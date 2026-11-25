"""Decode PR12203 Packing data and estimate its already-supported flat format.

This script does not edit Lean sources. Every flattened node/hint pair is decoded
again through an independent flat-layout reader and compared exactly.
"""
import hashlib
import json
import re
from pathlib import Path

BASE = Path('/tmp/oec/pequalnp-pilot-61')
SOURCE = BASE / 'PR12203_L_meta_670.lean'
text = SOURCE.read_text()
starts = list(re.finditer(r'(?m)^(?:private )?(?:def|theorem|lemma|abbrev|structure|inductive|set_option)\s+([^\s:(]+)', text))
decls = {m[1]: text[m.start():starts[i+1].start() if i+1 < len(starts) else len(text)].strip()
         for i, m in enumerate(starts) if not m[0].startswith('set_option')}

def mask(width):
    return (1 << width) - 1

def data_words(name):
    body = decls[name].split(':=', 1)[1].strip()
    tokens = re.findall(r'0x[0-9a-fA-F]+|[0-9]+|[A-Za-z_][A-Za-z_0-9]*|[()<]', body)
    residue = re.sub(r'0x[0-9a-fA-F]+|[0-9]+|[A-Za-z_][A-Za-z_0-9]*|[()<]|\s', '', body)
    assert not residue, (name, residue)
    pos = 0
    def parse():
        nonlocal pos
        t = tokens[pos]
        pos += 1
        if t == '(':
            out = parse()
            assert tokens[pos] == ')'
            pos += 1
            return out
        if t == 'if':
            var, op, limit, then = tokens[pos:pos+4]
            assert var in ['i', 'j'] and op == '<' and then == 'then'
            pos += 4
            yes = parse()
            assert tokens[pos] == 'else'
            pos += 1
            no = parse()
            return (int(limit), yes, no)
        return int(t, 0)
    tree = parse()
    assert pos == len(tokens), (name, tokens[pos:])
    def word(i, tree=tree):
        while isinstance(tree, tuple):
            boundary, yes, no = tree
            tree = yes if i < boundary else no
        return tree
    return word, body

def packed(word, pos, width):
    i, shift = divmod(pos, 8192)
    lo = word(i) >> shift
    if shift + width > 8192:
        lo |= word(i + 1) << (8192 - shift)
    return lo & mask(width)

def decode(fields, word, raw, i):
    num, depth, cw, dictionary, flags, ow, marker = fields
    width = 10*depth + raw + depth
    if marker < 1024:
        record = packed(word, i*width, width)
        start = num*width
        pos = start + num*ow + packed(word, start + i*ow, ow)
        count = packed(word, pos, 5)
        pairs = []
        for j in range(count):
            val = packed(word, pos + 5 + marker + j*(cw + depth), cw + depth)
            pairs.append([val & mask(cw), val >> cw])
        return record, pairs
    prefix_width = 10*max(0, depth - 1)
    row_width = flags % 16 + (0 if depth == 0 else 10) + flags//16
    start = (dictionary % 65536)*prefix_width + (dictionary//65536)*(raw + depth)
    off = start + i*row_width
    pre = packed(word, off, flags % 16)
    last_width = 0 if depth == 0 else 10
    last = packed(word, off + flags % 16, last_width)
    live_index = packed(word, off + flags % 16 + last_width, flags//16)
    record = packed(word, pre*prefix_width, prefix_width)
    record |= last << prefix_width
    record |= packed(word, (dictionary % 65536)*prefix_width + live_index*(raw + depth), raw + depth) << (10*depth)
    off = start + num*row_width
    pairs_base = off + num*ow
    priority = marker >= 4096
    pos = pairs_base + (marker - (4096 if priority else 1024))*(cw + depth) + packed(word, off + i*ow, ow)
    count = packed(word, pos, 5)
    gap = packed(word, pos + 5, 3)
    pos += 8
    a = b = None
    if priority and count > 1:
        order_width = (count - 1).bit_length()
        a = packed(word, pos, order_width)
        b = max(0, 1 - a) if count == 2 else packed(word, pos + order_width, order_width)
        pos += order_width if count == 2 else 2*order_width
    pairs = []
    first = 0
    for _ in range(count):
        head = packed(word, pos, 32)
        ones = (head ^ (head + 1)).bit_length() - 1
        key = first + (ones << gap) + packed(word, pos + ones + 1, gap)
        pair = packed(word, pairs_base + key*(cw + depth), cw + depth)
        pairs.append([pair & mask(cw), pair >> cw])
        pos += ones + 1 + gap
        first = key + 1
    if a is not None:
        firsts = [v for j, v in enumerate(pairs) if j == a]
        seconds = [v for j, v in enumerate(pairs) if j != a and j == b]
        others = [v for j, v in enumerate(pairs) if j != a and j != b]
        pairs = firsts + seconds + others
    assert record <= mask(width)
    return record, pairs

def flattened(fields, decoded, raw):
    num, depth, cw, *_ = fields
    width = 10*depth + raw + depth
    payload = 0
    payload_bits = 0
    offsets = []
    for _, pairs in decoded:
        offsets.append(payload_bits)
        assert len(pairs) < 32
        value = len(pairs)
        at = 5
        for col, paid in pairs:
            assert col <= mask(cw) and paid <= mask(depth)
            value |= (col | (paid << cw)) << at
            at += cw + depth
        payload |= value << payload_bits
        payload_bits += at
    ow = max(offsets, default=0).bit_length()
    value = sum(record << (i*width) for i, (record, _) in enumerate(decoded))
    start = num*width
    value |= sum(off << (start + i*ow) for i, off in enumerate(offsets))
    value |= payload << (start + num*ow)
    total_bits = start + num*ow + payload_bits
    chunks = [(value >> i) & mask(8192) for i in range(0, max(1, total_bits), 8192)]
    new_fields = [num, depth, cw, 0, 0, ow, 0]
    word = lambda i: chunks[min(i, len(chunks) - 1)]
    assert [decode(new_fields, word, raw, i) for i in range(num)] == decoded
    return new_fields, chunks, total_bits

forests = []
for name, declaration in decls.items():
    m = re.fullmatch(r'def \w+ : Forest := ⟨(\d+),[^\n]*,(\w+),(\w+)⟩', declaration)
    if m:
        forests.append((name, int(m[1]), m[2]))

records = []
seen = set()
for forest, graph_mask, levels in forests:
    raw = (graph_mask & 511).bit_count()
    for match in re.finditer(r'(?m)^\s*\| (\d+) => ([^\n]+)', decls[levels]):
        level, term = int(match[1]), match[2].strip()
        named = None
        if re.fullmatch(r'\w+', term):
            named = term
            term = decls[named].split(':=', 1)[1].strip()
        m = re.fullmatch(r'\((\d+),(\d+),(\d+),(\d+),(\d+),(\d+),(\d+),(\w+)\)', term)
        assert m, (forest, level, term)
        fields = [int(m[i]) for i in range(1, 8)]
        data_name = m[8]
        key = (data_name, raw, *fields)
        if key in seen:
            continue
        seen.add(key)
        word, old_body = data_words(data_name)
        decoded = [decode(fields, word, raw, i) for i in range(fields[0])]
        new_fields, chunks, bits = flattened(fields, decoded, raw)
        old_hex_digits = sum(len(v) - 2 for v in re.findall(r'0x[0-9a-fA-F]+', old_body))
        new_hex_digits = sum(len(format(v, 'x')) for v in chunks)
        serial = json.dumps(decoded, separators=(',', ':')).encode()
        records.append({'forest': forest, 'level': level, 'packing_name': named,
            'data_name': data_name, 'raw': raw, 'fields': fields, 'new_fields': new_fields,
            'nodes': fields[0], 'hints': sum(len(v[1]) for v in decoded),
            'decoded_sha256': hashlib.sha256(serial).hexdigest(),
            'old_hex_digits': old_hex_digits, 'flat_hex_digits': new_hex_digits,
            'hex_growth': new_hex_digits - old_hex_digits,
            'old_function_body_bytes': len(old_body.encode()),
            'flat_bits': bits, 'flat_chunks': len(chunks),
            'compact': fields[6] >= 1024})
report = {'source_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
    'forest_count': len(forests), 'record_count': len(records),
    'nodes': sum(r['nodes'] for r in records), 'hints': sum(r['hints'] for r in records),
    'total_hex_growth': sum(r['hex_growth'] for r in records),
    'compact_hex_growth': sum(r['hex_growth'] for r in records if r['compact']),
    'records': records}
(BASE / 'flat12203-estimate.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k:v for k,v in report.items() if k != 'records'}, indent=2))
