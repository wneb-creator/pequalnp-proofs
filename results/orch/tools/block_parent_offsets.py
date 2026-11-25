from pathlib import Path
import copy
import json
import sys

BLOCK = 16
CHUNK = 8192

def chunks(value):
    result = []
    while value:
        result.append(hex(value & ((1 << CHUNK) - 1)))
        value >>= CHUNK
    return result or ['0x0']

def unpack_data(row):
    return sum(int(word, 16) << (CHUNK * i)
               for i, word in enumerate(row['dataHexchunks']))

def extract(data, pos, width):
    return (data >> pos) & ((1 << width) - 1)

def new_rules(row, i, blocked):
    data = unpack_data(row)
    start = row['prefixBits']
    ow = row['offsetWidth']
    if blocked:
        block_count = (row['count'] + BLOCK - 1) // BLOCK
        pos = start + block_count * ow + extract(data, start + (i // BLOCK) * ow, ow)
        for _ in range(i % BLOCK):
            pos += 5 + extract(data, pos, 5) * (row['columnWidth'] + row['depth'])
    else:
        pos = start + row['count'] * ow + extract(data, start + i * ow, ow)
    nr = extract(data, pos, 5)
    cw, depth = row['columnWidth'], row['depth']
    return tuple((extract(data, pos + 5 + j * (cw + depth), cw),
                  extract(data, pos + 5 + j * (cw + depth) + cw, depth))
                 for j in range(nr))

def decode_states(rows):
    indexed = {(r['forest'], r['level']): r for r in rows}
    data = {r['name']: unpack_data(r) for r in rows}
    cache = {}
    def decode(row, i):
        key = (row['forest'], row['level'], i)
        if key in cache:
            return cache[key]
        d, pw, iw = row['depth'], row['parentWidth'], row['indexWidth']
        rec = extract(data[row['name']], i * row['recordWidth'], row['recordWidth'])
        op_width = 0 if d == 0 else pw + 10
        live = rec >> op_width
        if d == 0:
            ops = 0
        else:
            parent = rec & ((1 << pw) - 1)
            if parent == row['parentCount']:
                ex = int(row['exceptionPacked'], 16)
                ops = None
                for j in range(row['exceptionCount']):
                    item = extract(ex, j * (iw + 10 * d), iw + 10 * d)
                    if item & ((1 << iw) - 1) == i:
                        ops = item >> iw
                        break
                assert ops is not None, (row['name'], i, 'exception')
            else:
                previous = indexed[row['forest'], row['level'] + 1]
                old_ops, _ = decode(previous, parent)
                ops = old_ops | (((rec >> pw) & 1023) << (10 * (d - 1)))
        cache[key] = (ops, live)
        return cache[key]
    return {(r['name'], i): decode(r, i) for r in rows for i in range(r['count'])}

def convert(path):
    original = json.loads(path.read_text())
    converted = []
    total_new_rules = 0
    for old in original:
        row = copy.deepcopy(old)
        prefix = unpack_data(old) & ((1 << old['prefixBits']) - 1)
        payload = 0
        payload_bits = 0
        anchors = []
        for i, node in enumerate(old['nodes']):
            if i % BLOCK == 0:
                anchors.append(payload_bits)
            rules = tuple(map(tuple, node['new_rules']))
            assert rules == new_rules(old, i, False), (old['name'], i, 'old rules')
            assert len(rules) < 32
            record = len(rules)
            cw, depth = old['columnWidth'], old['depth']
            for j, (column, paid) in enumerate(rules):
                assert column < (1 << cw) and paid < (1 << depth)
                record |= (column | (paid << cw)) << (5 + j * (cw + depth))
            payload |= record << payload_bits
            payload_bits += 5 + len(rules) * (cw + depth)
            total_new_rules += len(rules)
        ow = max(anchors, default=0).bit_length()
        anchor_data = sum(a << (j * ow) for j, a in enumerate(anchors))
        data = prefix | (anchor_data << old['prefixBits']) | (
            payload << (old['prefixBits'] + len(anchors) * ow))
        row['offsetWidth'] = ow
        row['payloadBits'] = payload_bits
        row['totalBits'] = old['prefixBits'] + len(anchors) * ow + payload_bits
        row['dataHexchunks'] = chunks(data)
        row['parentHexChars'] = old['newHexChars']
        row['newHexChars'] = sum(map(len, row['dataHexchunks'])) + (
            len(row['exceptionPacked']) if row['exceptionCount'] else 1)
        row['offsetBlockSize'] = BLOCK
        row['offsetBlockCount'] = len(anchors)
        assert (data & ((1 << old['prefixBits']) - 1)) == prefix
        for i, node in enumerate(old['nodes']):
            assert new_rules(row, i, True) == tuple(map(tuple, node['new_rules'])), (
                row['name'], i, 'blocked rules')
        converted.append(row)
    assert decode_states(original) == decode_states(converted), 'ops/live roundtrip'
    output = path.with_name(path.stem + '-block16.json')
    output.write_text(json.dumps(converted, separators=(',', ':')))
    print(json.dumps({'module': path.stem, 'levels': len(converted),
                      'nodes': sum(r['count'] for r in original),
                      'newRules': total_new_rules,
                      'parentHexChars': sum(r['newHexChars'] for r in original),
                      'blockHexChars': sum(r['newHexChars'] for r in converted),
                      'savedHexChars': sum(r['newHexChars'] for r in original) -
                          sum(r['newHexChars'] for r in converted),
                      'roundtrip': 'all ops, live masks, and new rule lists exact',
                      'output': str(output)}))

if __name__ == '__main__':
    for arg in sys.argv[1:]:
        convert(Path(arg))
