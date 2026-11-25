import argparse
import json
from pathlib import Path

from live_search import INPUTS, binop, source_data


MODULUS = 2305843009213693951


def key_word(value):
    value %= MODULUS
    return value * (value + 971) % MODULUS


def bank_for(prefix, inputs=INPUTS):
    bank = list(inputs)
    for op, a, b in prefix:
        bank.append(binop(op, bank[a], bank[b]))
    return bank


def chunks_definition(name, value):
    words = []
    while value:
        words.append(value & ((1 << 8192) - 1))
        value >>= 8192
    if not words:
        return f'def {name} (_ : Nat) : Nat := 0\n'
    terms = [f'if i = {i} then 0x{word:x} else ' for i, word in enumerate(words)]
    return f'def {name} (i : Nat) : Nat := ' + ''.join(terms) + '0\n'


def displaced_table(mapping):
    if not mapping:
        return None
    size = len(mapping)
    buckets_count = max(1, (size + 3) // 4)
    node_bits = max(1, max(v[0] for v in mapping.values()).bit_length())
    auto_bits = max(1, max(v[1] for v in mapping.values()).bit_length())
    for scale in (14, 17, 21, 27, 35, 50):
        slots = max(size + 1, (size * scale + 9) // 10)
        while slots % 2 == 0 or slots % 3 == 0 or slots % 5 == 0:
            slots += 1
        buckets = [[] for _ in range(buckets_count)]
        for key, pair in mapping.items():
            buckets[key % buckets_count].append((key, pair))
        occupied = set()
        shifts = [0] * buckets_count
        rows = [0] * slots
        ok = True
        for bucket in sorted(range(buckets_count), key=lambda i: -len(buckets[i])):
            entries = buckets[bucket]
            residues = [(key // buckets_count) % slots for key, pair in entries]
            if len(set(residues)) != len(residues):
                ok = False
                break
            for shift in range(slots):
                positions = [(r + shift) % slots for r in residues]
                if all(pos not in occupied for pos in positions):
                    shifts[bucket] = shift
                    for (key, (node, auto)), pos in zip(entries, positions):
                        tag = key // (buckets_count * slots) % 16
                        rows[pos] = node | (auto << node_bits) | (tag << (node_bits + auto_bits))
                        occupied.add(pos)
                    break
            else:
                ok = False
                break
        if ok:
            shift_bits = max(1, max(shifts).bit_length())
            value_bits = node_bits + auto_bits + 4
            packed = sum(v << (i * shift_bits) for i, v in enumerate(shifts))
            packed |= sum(v << (buckets_count * shift_bits + i * value_bits)
                          for i, v in enumerate(rows))
            for key, expected in mapping.items():
                shift = shifts[key % buckets_count]
                row = rows[(key // buckets_count + shift) % slots]
                got = (row & ((1 << node_bits) - 1),
                       (row >> node_bits) & ((1 << auto_bits) - 1))
                assert got == expected
                assert row >> (node_bits + auto_bits) == key // (buckets_count * slots) % 16
            return (buckets_count, slots, shift_bits, value_bits, node_bits, auto_bits, packed)
    raise RuntimeError(f'Unable to construct displacement table for {size} keys')


def pack_nodes(records, column_bits):
    depth = max((len(rec['prefix']) for rec in records), default=0)
    assert all(len(rec['prefix']) == depth for rec in records)
    width = 10 * depth + 9 + depth
    nodes, payloads = [], []
    offset = 0
    offsets = []
    for rec in records:
        assert all(a < 16 and b < 16 for op, a, b in rec['prefix']), 'Needs wider prefix decoder'
        ops = sum((a | (b << 4) | (op << 8)) << (10 * i)
                  for i, (op, a, b) in enumerate(rec['prefix']))
        live = sum(1 << i for i in rec['live'])
        assert len(rec['live']) == len(set(rec['live']))
        nodes.append(ops | (live << (10 * depth)))
        rules = rec['rules']
        assert len(rules) < 32, 'Needs wider rule-count field'
        data = len(rules)
        for i, (column, paid) in enumerate(rules):
            assert column < 1 << column_bits and paid < 1 << depth
            data |= (column | (paid << column_bits)) << (5 + i * (column_bits + depth))
        payload_width = 5 + len(rules) * (column_bits + depth)
        offsets.append(offset)
        payloads.append((offset, data))
        offset += payload_width
    offset_bits = max(1, max(offsets, default=0).bit_length())
    start = len(records) * width
    payload_start = start + len(records) * offset_bits
    value = sum(node << (i * width) for i, node in enumerate(nodes))
    value |= sum(pos << (start + i * offset_bits) for i, pos in enumerate(offsets))
    value |= sum(data << (payload_start + pos) for pos, data in payloads)
    return (len(records), depth, column_bits, 0, 0, offset_bits, 0, value)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('records')
    parser.add_argument('output')
    parser.add_argument('--name', default='generatedNine')
    parser.add_argument('--blocks', type=int, default=16)
    args = parser.parse_args()
    report = json.loads(Path(args.records).read_text())
    assert report['verdict'] == 'UNSAT'
    columns, samples, swaps, permutations, domains = source_data()
    levels = {k: [] for k in range(report['cap'] + 1)}
    for record in report['records']:
        levels[record['k']].append(record)
    inverse_perms = []
    for sequence in swaps:
        p = list(range(9))
        for step in sequence:
            a, b = step & 15, step >> 4
            p = [b if v == a else a if v == b else v for v in p]
        inverse_perms.append(p)
    sources = ['import Structural16\n\nnamespace PEqualNP.Outside.L_meta_2592_aux.SignedFloor\n']
    name = args.name
    packed_levels, packed_indices, stats = {}, {}, {}
    for k, records in levels.items():
        if not records:
            continue
        packed_levels[k] = pack_nodes(records, max(1, (len(columns) - 1).bit_length()))
        sources.append(chunks_definition(f'{name}Data{k}', packed_levels[k][-1]))
        mapping, hash_states = {}, {}
        for i, rec in enumerate(records):
            for a, p in enumerate(inverse_perms):
                bank = bank_for(rec['prefix'], [INPUTS[j] for j in p])
                state = tuple(sorted(bank[j] for j in rec['live']))
                key = sum(map(key_word, state))
                if key in hash_states:
                    assert hash_states[key] == state, 'Real keySet collision'
                else:
                    mapping[key] = (i, a)
                    hash_states[key] = state
        packed_indices[k + 1] = displaced_table(mapping)
        sources.append(chunks_definition(f'{name}Hash{k+1}', packed_indices[k + 1][-1]))
        stats[k] = dict(nodes=len(records), depth=packed_levels[k][1], links=len(mapping),
                        bits=packed_levels[k][-1].bit_length(), max_rules=max(len(r['rules']) for r in records))
    sources.append(f'def {name}Level : Nat → Packing\n')
    for k, level in packed_levels.items():
        values = ','.join(map(str, level[:-1]))
        sources.append(f'  | {k} => ({values},{name}Data{k})\n')
    sources.append('  | _ => emptyPacking\n')
    sources.append(f'def {name}Index : Nat → Nat → Option (Nat × Nat)\n')
    for k, index in packed_indices.items():
        values = ' '.join(map(str, index[:-1]))
        sources.append(f'  | {k} => lookupWord {values} {name}Hash{k}\n')
    sources.append('  | _ => fun _ => none\n')
    sources.append(f'def {name} : Forest := ⟨511,{report["cap"]},'
                   f'fun j => rootSSamples[j]?.getD (0,0),rootSCols,rootSAutos,'
                   f'{name}Level,{name}Index⟩\n')
    for k, records in levels.items():
        for start in range(0, len(records), args.blocks):
            size = min(args.blocks, len(records) - start)
            sources.append('set_option maxRecDepth 32768 in\nset_option maxHeartbeats 0 in\n'
                           f'theorem {name}Block{k}_{start} : block {name} {k} {start} {size} = true := by\n'
                           '  decide +kernel\n')
    sources.append('\nend PEqualNP.Outside.L_meta_2592_aux.SignedFloor\n')
    Path(args.output).write_text(''.join(sources))
    Path(args.output + '.json').write_text(json.dumps(stats, indent=2))
    print(json.dumps(stats))


if __name__ == '__main__':
    main()
