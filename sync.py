#!/usr/bin/env python3
"""Собирает статический Site/data.json из SQL-файла, архива или stdin."""
import argparse
import bz2
import functools
import hashlib
import html
import gzip
import http.server
import json
import lzma
import os
import re
import shutil
import subprocess
import sys
import tarfile
import threading
import time
from datetime import datetime, timezone

SQL_IDENT = r'(?:[A-Za-z_][A-Za-z_0-9$]*|"(?:[^"]|"")+")'
TABLE_REF = rf'{SQL_IDENT}(?:\s*\.\s*{SQL_IDENT})*'
COPY_RE = re.compile(
    rf'^\s*COPY\s+(?P<table>{TABLE_REF})\s*'
    r'(?:\((?P<columns>.*?)\))?\s+FROM\s+stdin\s*;\s*$', re.I)
CREATE_RE = re.compile(
    rf'^\s*CREATE\s+TABLE\s+(?:IF\s+NOT\s+EXISTS\s+)?'
    rf'(?P<table>{TABLE_REF})\s*\((?P<definitions>.*)\)\s*$', re.I | re.S)
INSERT_RE = re.compile(
    rf'^\s*INSERT\s+INTO\s+(?:ONLY\s+)?(?P<table>{TABLE_REF})\s*'
    r'(?:\((?P<columns>.*?)\)\s*)?'
    r'(?:OVERRIDING\s+(?:SYSTEM|USER)\s+VALUE\s*)?'
    r'(?:(?P<default>DEFAULT\s+VALUES)|VALUES\s*(?P<values>.*))\s*$', re.I | re.S)
NUM_RE = re.compile(r'[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?')
COPY_ESC = {'b': '\b', 'f': '\f', 'n': '\n', 'r': '\r', 't': '\t',
            'v': '\v', '\\': '\\'}


def tname(s):
    parts, start, quoted, i = [], 0, False, 0
    while i < len(s):
        if s[i] == '"':
            if quoted and i + 1 < len(s) and s[i + 1] == '"':
                i += 2
                continue
            quoted = not quoted
        elif s[i] == '.' and not quoted:
            parts.append(s[start:i].strip())
            start = i + 1
        i += 1
    parts.append(s[start:].strip())
    return identifier_name(parts[-1])


def identifier_name(value):
    value = value.strip()
    if value.startswith('"') and value.endswith('"'):
        return value[1:-1].replace('""', '"')
    return value.lower()


def split_top_level(text, delimiter=','):
    parts, start, depth, brackets, quote, dollar, i = [], 0, 0, 0, None, None, 0
    while i < len(text):
        char = text[i]
        if dollar:
            if text.startswith(dollar, i):
                i += len(dollar)
                dollar = None
                continue
        elif quote:
            if quote == "'" and char == '\\' and i + 1 < len(text):
                i += 2
                continue
            if char == quote:
                if i + 1 < len(text) and text[i + 1] == quote:
                    i += 2
                    continue
                quote = None
        elif char in ("'", '"'):
            quote = char
        elif char == '$':
            match = re.match(r'\$(?:[A-Za-z_][A-Za-z_0-9]*)?\$', text[i:])
            if match:
                dollar = match.group()
                i += len(dollar)
                continue
        elif char == '(':
            depth += 1
        elif char == ')':
            depth -= 1
        elif char == '[':
            brackets += 1
        elif char == ']':
            brackets -= 1
        elif char == delimiter and depth == 0 and brackets == 0:
            parts.append(text[start:i].strip())
            start = i + 1
        i += 1
    parts.append(text[start:].strip())
    return parts


def cols_of(s):
    return [identifier_name(c) for c in split_top_level(s) if c]


def num(v):
    if NUM_RE.fullmatch(v):
        return float(v) if any(c in v for c in '.eE') else int(v)
    return v


def copy_val(v):
    if v == r'\N':
        return None
    def unescape(match):
        escaped = match[1]
        if escaped in COPY_ESC:
            return COPY_ESC[escaped]
        if escaped.startswith('x'):
            return chr(int(escaped[1:], 16))
        if escaped[0] in '01234567':
            return chr(int(escaped, 8))
        return escaped
    value = re.sub(r'\\(\\|[bfnrtv]|[0-7]{1,3}|x[0-9A-Fa-f]{1,2}|.)', unescape, v)
    return num(value)


def ins_val(v):
    v = v.strip()
    if v.upper() == 'DEFAULT':
        return None
    if v.startswith(('E\'', 'e\'')) and v.endswith("'"):
        value = v[2:-1].replace("''", "'")
        escapes = {'\\': '\\', "'": "'", 'b': '\b', 'f': '\f',
                   'n': '\n', 'r': '\r', 't': '\t'}
        return re.sub(r'\\(.)', lambda m: escapes.get(m[1], m[1]), value)
    if v.startswith("'") and v.endswith("'"):
        return v[1:-1].replace("''", "'")
    if v.startswith('$'):
        match = re.match(r'\$(?:[A-Za-z_][A-Za-z_0-9]*)?\$', v)
        if match and v.endswith(match.group()):
            return v[len(match.group()):-len(match.group())]
    if v.upper() == 'NULL':
        return None
    if v.lower() in ('true', 'false'):
        return v.lower() == 'true'
    return num(v)


def insert_rows(values):
    rows, i = [], 0
    while i < len(values):
        while i < len(values) and (values[i].isspace() or values[i] == ','):
            i += 1
        if i == len(values):
            break
        if values[i] != '(':
            raise ValueError(f'Ожидалась строка INSERT около: {values[i:i + 30]!r}')
        start, depth, quote, dollar = i + 1, 1, None, None
        i += 1
        while i < len(values):
            char = values[i]
            if dollar:
                if values.startswith(dollar, i):
                    i += len(dollar)
                    dollar = None
                    continue
            elif quote:
                if quote == "'" and char == '\\' and i + 1 < len(values):
                    i += 2
                    continue
                if char == quote:
                    if i + 1 < len(values) and values[i + 1] == quote:
                        i += 2
                        continue
                    quote = None
            elif char in ("'", '"'):
                quote = char
            elif char == '$':
                match = re.match(r'\$(?:[A-Za-z_][A-Za-z_0-9]*)?\$', values[i:])
                if match:
                    dollar = match.group()
                    i += len(dollar)
                    continue
            elif char == '(':
                depth += 1
            elif char == ')':
                depth -= 1
                if depth == 0:
                    rows.append([ins_val(value) for value in split_top_level(values[start:i])])
                    i += 1
                    break
            i += 1
        else:
            raise ValueError('Незакрытая строка значений в INSERT')
    return rows


def sql_statements(text):
    statement, i, quote, dollar, block_comment = [], 0, None, None, 0
    while i < len(text):
        char = text[i]
        if block_comment:
            if text.startswith('/*', i):
                block_comment += 1
                i += 2
            elif text.startswith('*/', i):
                block_comment -= 1
                i += 2
            else:
                i += 1
            continue
        if quote:
            statement.append(char)
            if quote == "'" and char == '\\' and i + 1 < len(text):
                statement.append(text[i + 1])
                i += 2
                continue
            if char == quote:
                if i + 1 < len(text) and text[i + 1] == quote:
                    statement.append(text[i + 1])
                    i += 2
                    continue
                quote = None
            i += 1
            continue
        if dollar:
            if text.startswith(dollar, i):
                statement.append(dollar)
                i += len(dollar)
                dollar = None
            else:
                statement.append(char)
                i += 1
            continue
        if text.startswith('--', i):
            statement.append(' ')
            i = text.find('\n', i)
            if i < 0:
                break
            statement.append('\n')
            i += 1
            continue
        if text.startswith('/*', i):
            statement.append(' ')
            block_comment = 1
            i += 2
            continue
        if char in ("'", '"'):
            quote = char
            statement.append(char)
        elif char == '$':
            match = re.match(r'\$(?:[A-Za-z_][A-Za-z_0-9]*)?\$', text[i:])
            if match:
                dollar = match.group()
                statement.append(dollar)
                i += len(dollar)
                continue
            statement.append(char)
        elif char == ';':
            value = ''.join(statement).strip()
            if value:
                yield value
            statement = []
        else:
            statement.append(char)
        i += 1
    if block_comment or quote or dollar:
        raise ValueError('SQL обрывается внутри строки или комментария')
    value = ''.join(statement).strip()
    if value:
        yield value


def read_dump(source, encoding):
    if source == '-':
        return sys.stdin.read()
    if os.path.isdir(source) or tarfile.is_tarfile(source):
        return restore_dump(source, encoding)

    with open(source, 'rb') as f:
        signature = f.read(5)
    if signature == b'PGDMP':
        return restore_dump(source, encoding)

    opener = {'.gz': gzip.open, '.bz2': bz2.open, '.xz': lzma.open}.get(
        os.path.splitext(source.lower())[1], open)
    with opener(source, 'rt', encoding=encoding) as f:
        return f.read()


def restore_dump(source, encoding):
    pg_restore = shutil.which('pg_restore')
    if not pg_restore:
        raise ValueError('Это архив PostgreSQL. Установите pg_restore или преобразуйте его в обычный .sql-файл.')
    result = subprocess.run(
        [pg_restore, '--no-owner', '--no-privileges', '--file=-', source],
        capture_output=True, text=True, encoding=encoding, errors='replace')
    if result.returncode:
        raise ValueError(f'pg_restore завершился с ошибкой: {result.stderr.strip()}')
    return result.stdout


def parse_column_overrides(values):
    result = {}
    for value in values:
        if '=' not in value:
            raise ValueError(f'Неверный формат --columns: {value!r}; ожидается table=col1,col2')
        table, columns = value.split('=', 1)
        result[tname(table)] = cols_of(columns)
    return result


def extract_copy(text):
    lines, remaining, blocks, i = text.splitlines(), [], [], 0
    while i < len(lines):
        match = COPY_RE.match(lines[i])
        if not match:
            remaining.append(lines[i])
            i += 1
            continue
        table = tname(match['table'])
        columns = cols_of(match['columns']) if match['columns'] else None
        rows, i = [], i + 1
        while i < len(lines) and lines[i].strip() != r'\.':
            rows.append(lines[i].split('\t'))
            i += 1
        if i == len(lines):
            raise ValueError(f'В COPY для {table} отсутствует строка \\.' )
        blocks.append((table, columns, rows))
        remaining.append('')
        i += 1
    return '\n'.join(remaining), blocks


def parse(text, column_overrides=None):
    tables, schemas, blocks = {}, {}, []
    column_overrides = column_overrides or {}
    text, blocks = extract_copy(text.lstrip('\ufeff'))
    statements = list(sql_statements(text))
    for statement in statements:
        match = CREATE_RE.match(statement)
        if not match:
            continue
        table = tname(match['table'])
        columns = []
        for definition in split_top_level(match['definitions']):
            if re.match(r'(?i)\s*(?:CONSTRAINT|PRIMARY|UNIQUE|CHECK|FOREIGN|EXCLUDE)\b', definition):
                continue
            column = re.match(r'\s*("(?:[^"]|"")+"|[^\s]+)', definition)
            if column:
                columns.append(identifier_name(column.group(1)))
        schemas[table] = columns
        tables.setdefault(table, [])

    for table, declared, raw_rows in blocks:
        columns = declared or column_overrides.get(table) or schemas.get(table)
        if not columns:
            raise ValueError(f'Не удалось определить колонки COPY для {table}; добавьте CREATE TABLE или --columns')
        rows = tables.setdefault(table, [])
        for raw_values in raw_rows:
            if len(raw_values) != len(columns):
                raise ValueError(f'В COPY для {table} ожидалось {len(columns)} значений, получено {len(raw_values)}')
            rows.append(dict(zip(columns, map(copy_val, raw_values))))

    for statement in statements:
        match = INSERT_RE.match(statement)
        if not match:
            continue
        table = tname(match['table'])
        columns = cols_of(match['columns']) if match['columns'] else (
            column_overrides.get(table) or schemas.get(table))
        if not columns:
            raise ValueError(f'У INSERT для {table} нет списка колонок и схемы; добавьте CREATE TABLE или --columns')
        rows = [[None] * len(columns)] if match['default'] else insert_rows(match['values'])
        for values in rows:
            if len(values) != len(columns):
                raise ValueError(f'В INSERT для {table} ожидалось {len(columns)} значений, получено {len(values)}')
            tables.setdefault(table, []).append(dict(zip(columns, values)))
    if not tables:
        raise ValueError('Не найдено таблиц. Нужен текстовый SQL-дамп или SQL-скрипт с CREATE TABLE, INSERT либо COPY.')
    return tables


PRODUCT_KEYS = {
    'name': ('name', 'title', 'model', 'product_name'),
    'brand': ('brand', 'brand_name', 'manufacturer'),
    'price': ('price', 'cost', 'price_eur'),
    'image': ('image', 'image_url', 'photo', 'img', 'picture'),
    'size': ('size', 'sizes'),
    'color': ('color', 'colour'),
    'stock': ('in_stock', 'stock', 'available', 'quantity'),
}


def product_field(row, field):
    return next((row[key] for key in PRODUCT_KEYS[field] if key in row), None)


def product_table(tables):
    for name, rows in tables.items():
        if rows and any(key in rows[0] for key in PRODUCT_KEYS['price']):
            return name
    return next(iter(tables), None)


def product_identity(row):
    image = display_value(product_field(row, 'image')).strip().replace('\\', '/').casefold()
    brand = display_value(product_field(row, 'brand')).strip().casefold()
    sex = next((row[key] for key in ('sex', 'gender') if key in row), None)
    if not image or not brand or sex is None:
        return None
    if isinstance(sex, bool):
        sex = str(sex).lower()
    else:
        sex = display_value(sex).strip().casefold()
        if sex in ('t', '1', 'yes'):
            sex = 'true'
        elif sex in ('f', '0', 'no'):
            sex = 'false'
    return image, sex, brand


def merge_product_rows(previous_rows, incoming_rows):
    merged, positions = [], {}
    for row in [*previous_rows, *incoming_rows]:
        identity = product_identity(row)
        if identity is not None and identity in positions:
            index = positions[identity]
            merged[index] = {**merged[index], **row}
        else:
            if identity is not None:
                positions[identity] = len(merged)
            merged.append(row)
    return merged


def display_value(value):
    if isinstance(value, (list, tuple)):
        return ', '.join(map(str, value))
    return '' if value is None else str(value)


def product_filename(row, index, used):
    name = display_value(product_field(row, 'name'))
    slug = re.sub(r'[^a-z0-9]+', '-', name.lower()).strip('-') or 'product'
    id_field = next((key for key in ('id', 'product_id', 'item_id', 'sku', 'code') if key in row), None)
    identity = f'{id_field}:{row[id_field]}' if id_field else f'{name}\0{display_value(product_field(row, "brand"))}'
    digest = hashlib.sha256(identity.encode('utf-8')).hexdigest()[:10]
    filename = f'{slug[:60]}-{digest}.html'
    if filename in used:
        filename = f'{slug[:55]}-{digest}-{index + 1}.html'
    used.add(filename)
    return filename


def product_page(row, return_url='../index.html'):
    name = display_value(product_field(row, 'name'))
    if not name:
        values = list(row.values())
        name = display_value(values[1] if len(values) > 1 else (values[0] if values else 'Produkt'))
    brand = display_value(product_field(row, 'brand'))
    price = display_value(product_field(row, 'price'))
    image = display_value(product_field(row, 'image')).replace('\\', '/')
    if image and not re.match(r'^(?:https?:)?//|^data:', image, re.I) and not image.startswith('/'):
        image = '../' + image.lstrip('./')
    size = display_value(product_field(row, 'size'))
    color = display_value(product_field(row, 'color'))
    stock = product_field(row, 'stock')
    unavailable = stock is False or stock == 0 or str(stock).lower() in ('0', 'f', 'false', 'no', 'off')
    title = f'{name} | Bringy'
    safe = lambda value: html.escape(str(value), quote=True)
    photo = (f'<img src="{safe(image)}" alt="{safe(name)}">' if image
             else f'<div class="placeholder">{safe(name[:1] or "B")}</div>')
    price_html = f'<p class="price">{safe(price)} €</p>' if price else ''
    stock_html = ('<span class="stock out">Vypredané</span>' if unavailable
                  else '<span class="stock">Na sklade</span>' if stock is not None else '')
    details = ''.join(
        f'<div><dt>{label}</dt><dd>{safe(value)}</dd></div>'
        for label, value in (('Farba', color), ('Veľkosti', size)) if value)
    return f'''<!doctype html>
<html lang="sk">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{safe(title)}</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Archivo+Black&family=Space+Grotesk:wght@400;500;700&display=swap" rel="stylesheet">
<style>
:root{{--ink:#111014;--panel:#f5f4ee;--paper:#fff;--steel:#6b6e76;--flare:#ff2f6e;--line:rgba(17,16,20,.14)}}
*{{box-sizing:border-box}}
body{{margin:0;background:var(--paper);color:var(--ink);font:16px/1.5 'Space Grotesk',system-ui,sans-serif;background-image:repeating-linear-gradient(0deg,rgba(17,16,20,.025) 0 1px,transparent 1px 3px)}}
.wrap{{max-width:1080px;margin:auto;padding:24px 20px 64px}}
.top{{display:flex;align-items:center;justify-content:space-between;border-bottom:2px solid var(--ink);padding:12px 0 20px}}
.logo{{font:2rem 'Archivo Black',system-ui,sans-serif;text-decoration:none;color:var(--ink);text-transform:uppercase}}
.logo span{{color:var(--flare)}}
.back{{color:var(--ink);font-weight:700;text-decoration:none}}
.back:hover{{color:var(--flare)}}
.product{{display:grid;grid-template-columns:minmax(0,1.15fr) minmax(280px,.85fr);gap:clamp(28px,6vw,76px);align-items:center;padding:44px 0}}
.photo{{position:relative;background:var(--panel);border:1px solid var(--line);aspect-ratio:1;display:grid;place-items:center;overflow:hidden}}
.photo:before{{content:"";position:absolute;z-index:1;top:12px;left:22px;width:64px;height:18px;background:repeating-linear-gradient(45deg,rgba(17,16,20,.16) 0 2px,rgba(17,16,20,.05) 2px 6px);transform:rotate(-4deg)}}
.photo img{{width:100%;height:100%;object-fit:cover}}
.placeholder{{font:7rem 'Archivo Black',sans-serif;color:rgba(17,16,20,.25)}}
.brand{{margin:0 0 10px;color:var(--steel);font-size:.8rem;text-transform:uppercase;letter-spacing:.08em}}
h1{{margin:0;font:clamp(2.2rem,5vw,4.5rem)/.98 'Archivo Black',system-ui,sans-serif;text-transform:uppercase;overflow-wrap:anywhere}}
.price{{display:inline-block;margin:24px 0 12px;padding:6px 14px;background:var(--flare);color:#fff;font-size:1.4rem;font-weight:700;transform:rotate(-1deg)}}
.stock{{display:table;border:1px solid #27845e;color:#176441;padding:4px 10px;font-size:.8rem;text-transform:uppercase}}
.stock.out{{border-color:var(--steel);color:var(--steel)}}
dl{{margin:28px 0 0;border-top:1px solid var(--line)}}
dl div{{display:grid;grid-template-columns:100px 1fr;gap:12px;padding:12px 0;border-bottom:1px solid var(--line)}}
dt{{color:var(--steel)}} dd{{margin:0;font-weight:700;overflow-wrap:anywhere}}
@media(max-width:700px){{.wrap{{padding-top:12px}}.product{{grid-template-columns:1fr;gap:28px;padding-top:28px}}.photo{{max-height:70vh}}.top{{align-items:flex-start;gap:16px;flex-wrap:wrap}}}}
</style>
</head>
<body><div class="wrap">
<nav class="top"><a class="logo" href="{safe(return_url)}">Bring<span>y</span></a><a class="back" href="{safe(return_url)}">← Všetky modely</a></nav>
<main class="product"><div class="photo">{photo}</div><section>
{f'<p class="brand">{safe(brand)}</p>' if brand else ''}<h1>{safe(name)}</h1>
{price_html}{stock_html}<dl>{details}</dl>
</section></main></div></body></html>'''


def write_text_atomic(path, content):
    tmp = path + '.tmp'
    with open(tmp, 'w', encoding='utf-8') as f:
        f.write(content)
    os.replace(tmp, path)


def build(dump, out, encoding='utf-8-sig', column_overrides=None):
    tables = parse(read_dump(dump, encoding), column_overrides)
    site_dir = os.path.dirname(os.path.abspath(out))
    products_dir = os.path.join(site_dir, 'products')
    os.makedirs(products_dir, exist_ok=True)
    manifest_path = os.path.join(products_dir, 'manifest.json')
    try:
        with open(manifest_path, encoding='utf-8') as f:
            old_pages = set(json.load(f))
    except (OSError, ValueError, TypeError):
        old_pages = set()
    try:
        with open(out, encoding='utf-8') as f:
            old_payload = json.load(f)
        old_tables = old_payload.get('tables', {})
    except (OSError, ValueError, TypeError, AttributeError):
        old_tables = {}

    pages, used = {}, set()
    table = product_table(tables)
    generated_pages = []
    if table:
        previous_rows = old_tables.get(table, [])
        if not isinstance(previous_rows, list):
            previous_rows = []
        tables[table] = merge_product_rows(previous_rows, tables[table])
        pages[table] = []
        for index, row in enumerate(tables[table]):
            filename = product_filename(row, index, used)
            page_path = os.path.join(products_dir, filename)
            write_text_atomic(page_path, product_page(row))
            generated_pages.append(filename)
            pages[table].append(f'products/{filename}')

    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    payload = {'generated': datetime.now(timezone.utc).isoformat(),
               'tables': tables, 'productPages': pages}
    write_text_atomic(out, json.dumps(payload, ensure_ascii=False, default=str))
    for filename in old_pages - set(generated_pages):
        if isinstance(filename, str) and os.path.basename(filename) == filename and filename.endswith('.html'):
            try:
                os.remove(os.path.join(products_dir, filename))
            except FileNotFoundError:
                pass
    write_text_atomic(manifest_path, json.dumps(generated_pages, ensure_ascii=False))
    source = 'stdin' if dump == '-' else dump
    print(f'[{time.strftime("%H:%M:%S")}] {source} -> {out}: '
          + ', '.join(f'{t}={len(r)}' for t, r in tables.items())
          + f'; product pages={len(generated_pages)}')


def main():
    p = argparse.ArgumentParser()
    root = os.path.dirname(os.path.abspath(__file__))
    p.add_argument('dump', nargs='?', help='SQL-файл, архив PostgreSQL или - для stdin')
    p.add_argument('-i', '--input', '--dump', dest='input_file', help='входной SQL-файл или архив')
    p.add_argument('--out', default=os.path.join(root, 'Site', 'data.json'))
    p.add_argument('--stdin', action='store_true', help='прочитать SQL из stdin')
    p.add_argument('--encoding', default='utf-8-sig', help='кодировка входного SQL')
    p.add_argument('--columns', action='append', default=[], metavar='TABLE=COL1,COL2',
                   help='задать колонки для INSERT без списка колонок; можно повторять')
    p.add_argument('--watch', action='store_true')
    p.add_argument('--serve', type=int, metavar='PORT')
    a = p.parse_args()

    if a.input_file and a.dump:
        p.error('укажите входной файл либо позиционно, либо через --input/--dump')
    if a.stdin and (a.input_file or a.dump):
        p.error('--stdin нельзя совмещать с путём к файлу')
    source = '-' if a.stdin else (a.input_file or a.dump or os.path.join(root, 'data.sql'))
    if source == '-' and a.watch:
        p.error('--watch нельзя использовать со stdin')
    try:
        columns = parse_column_overrides(a.columns)
        build(source, a.out, a.encoding, columns)
    except (OSError, ValueError, UnicodeError) as e:
        p.exit(1, f'Ошибка: {e}\n')

    if a.serve:
        handler = functools.partial(http.server.SimpleHTTPRequestHandler,
                                    directory=os.path.dirname(os.path.abspath(a.out)))
        srv = http.server.ThreadingHTTPServer(('127.0.0.1', a.serve), handler)
        threading.Thread(target=srv.serve_forever, daemon=True).start()
        print(f'Сайт: http://127.0.0.1:{a.serve}')
        if source == '-':
            srv.serve_forever()

    if a.watch or a.serve:
        last = os.stat(source).st_mtime
        while True:
            time.sleep(1)
            try:
                mtime = os.stat(source).st_mtime
            except FileNotFoundError:
                continue
            if mtime != last:
                time.sleep(0.5)  # дать дампу дописаться
                last = mtime
                try:
                    build(source, a.out, a.encoding, columns)
                except Exception as e:
                    print('Ошибка парсинга, оставляю старый JSON:', e)


if __name__ == '__main__':
    main()
