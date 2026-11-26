#!/usr/bin/env python3
"""Independent factor-leaf replay; this program is not a Lean certificate."""
import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import struct
import time

from factor_cut import factor_cut

if not __debug__:
    raise RuntimeError('Run this auditor without Python optimization; assertions are required.')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--wire-file', type=Path, required=True)
    parser.add_argument('--factor-dir', type=Path, required=True)
    parser.add_argument('--manifest', type=Path,
                        default=Path(__file__).with_name('snapshots.json'))
    parser.add_argument('--out-dir', type=Path, required=True)
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    spec = json.loads(args.manifest.read_text())
    start = time.monotonic()
    data = args.wire_file.read_bytes()
    assert digest(data) == spec['wire_sha256'], 'wire hash mismatch'
    assert len(data) == spec['wire_records'] * 144, 'partial wire record'
    inputs = [sum(1 << r for r in range(1024) if r & (1 << i)) for i in range(10)]
    edges = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
             (5,7),(7,9),(9,6),(6,8),(8,5)]
    target = 0
    for a, b in edges:
        target |= inputs[a] & inputs[b]
    positive = sorted({(1 << a) | (1 << b) for a, b in edges})
    negative = [r for r in range(1024) if not(target >> r & 1) and
                all(target >> (r | (1 << i)) & 1 for i in range(10) if not(r & (1 << i)))]
    assert len(positive) == len(negative) == 15
    assert all(target >> p & 1 for p in positive)
    assert all(not(target >> n & 1) for n in negative)
    pairs = list(itertools.product(positive, negative))
    full = (1 << 1024) - 1
    wires, seen, origins = [], set(), Counter()
    for index in range(spec['wire_records']):
        offset = 144 * index
        word = int.from_bytes(data[offset:offset+128], 'little')
        op, a, b, var = struct.unpack_from('<iiii', data, offset+128)
        assert word not in seen, ('duplicate wire', index)
        seen.add(word)
        if var >= 0:
            assert index == var and 0 <= var < 10 and op == a == b == -1
            assert word == inputs[var], ('wrong input', index)
            origins['input'] += 1
        else:
            assert var == -1 and op in (0,1) and 0 <= a < index and 0 <= b < index
            assert word == (wires[a] & wires[b] if op == 0 else wires[a] | wires[b])
            origins['and' if op == 0 else 'or'] += 1
        wires.append(word)
    del data, seen
    print('WIRE_DAG_PASS', len(wires), dict(origins), flush=True)
    results = []
    for entry in spec['factor_files']:
        assert Path(entry['file']).name == entry['file'], 'manifest needs basenames'
        data = (args.factor_dir / entry['file']).read_bytes()
        assert digest(data) == entry['sha256'], ('factor hash mismatch', entry['file'])
        offset = count = 0
        caps, kinds = Counter(), Counter()
        while offset < len(data):
            assert len(data)-offset >= 8, ('partial factor header', offset)
            cap, width = struct.unpack_from('<II', data, offset)
            offset += 8
            assert 0 <= cap <= 19 and 1 <= width <= 31
            assert len(data)-offset >= 4*width, ('partial factor IDs', offset)
            ids = struct.unpack_from('<' + 'I'*width, data, offset)
            offset += 4*width
            assert tuple(sorted(set(ids))) == ids and max(ids) < len(wires)
            values = [wires[i] for i in ids]
            assert len(set(values)) == width and all(w not in (0, full, target) for w in values)
            assert all(any((w >> p & 1) and not(w >> n & 1) for w in values) for p,n in pairs)
            answer = factor_cut(values, pairs, cap)
            assert answer is not None, ('factor leaf not excluded', entry['file'], count)
            count += 1
            caps[cap] += 1
            kinds[answer['kind']] += 1
            if count % 10000 == 0:
                print('FACTOR_PROGRESS', entry['file'], count, flush=True)
        assert count == entry['records'] and offset == len(data)
        assert dict(caps) == {int(k): v for k,v in entry['counts_by_cap'].items()}
        item = dict(file=entry['file'], records=count, counts_by_cap=dict(caps),
                    kinds=dict(kinds), sha256=entry['sha256'], verdict='PASS')
        results.append(item)
        print('FACTOR_FILE_PASS', json.dumps(item), flush=True)
    total = sum(x['records'] for x in results)
    assert total == spec['factor_records']
    assert digest(args.wire_file.read_bytes()) == spec['wire_sha256'], 'wire input changed'
    report = dict(verdict='PASS', factor_records=total, factor_files=results,
                  wire_records=len(wires), wire_sha256=spec['wire_sha256'],
                  seconds=time.monotonic()-start,
                  scope='Factor leaves only; not frontier completeness, other cuts, a Lean proof, or the posted gap.')
    (args.out_dir/'result.json').write_text(json.dumps(report, indent=2)+'\n')
    print('ALL_FACTOR_LEAVES_PASS', json.dumps(report), flush=True)


if __name__ == '__main__':
    main()
