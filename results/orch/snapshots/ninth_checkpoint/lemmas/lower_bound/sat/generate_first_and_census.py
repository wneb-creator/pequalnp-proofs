import json
from pathlib import Path


def generate(case, forced, dirty_pairs):
    edges = {tuple(sorted(e)) for e in case['edges']}
    allowed = edges | {tuple(sorted(e)) for e in dirty_pairs}
    adjacency = [0] * 16
    for a, b in allowed:
        adjacency[a] |= 1 << b
        adjacency[b] |= 1 << a
    negative = [m for m, y in case['raw_tests'] if not y]
    positive = [m for m, y in case['raw_tests'] if y]
    active = [entry['raw_mask'] for entry in forced]

    def columns(masks):
        return [sum(((mask >> i) & 1) << j for j, mask in enumerate(masks)) for i in range(16)]

    nc, pc, tc = columns(negative), columns(positive), columns(active)
    negative_or = [0] * (1 << 16)
    positive_or = [0] * (1 << 16)
    active_or = [0] * (1 << 16)
    common = [0] * (1 << 16)
    common[0] = (1 << 16) - 1
    for bits in range(1, 1 << 16):
        low = bits & -bits
        i, old = low.bit_length() - 1, bits ^ low
        negative_or[bits] = negative_or[old] | nc[i]
        positive_or[bits] = positive_or[old] | pc[i]
        active_or[bits] = active_or[old] | tc[i]
        common[bits] = common[old] & adjacency[i]
    all_negative, all_active = (1 << len(negative)) - 1, (1 << len(active)) - 1
    rows = []
    for a in range(1, 1 << 16):
        if active_or[a] != all_active:
            continue
        b = common[a]
        while b:
            if a < b and active_or[b] == all_active and positive_or[a] & positive_or[b]:
                equal = (all_negative ^ (negative_or[a] ^ negative_or[b])).bit_count()
                if equal <= 2:
                    left = [i for i in range(16) if a >> i & 1]
                    right = [i for i in range(16) if b >> i & 1]
                    rows.append(dict(left=left, right=right, equal_negatives=equal,
                                     positive_edges=(positive_or[a] & positive_or[b]).bit_count(),
                                     dirty_pairs=[sorted((i, j)) for i in left for j in right
                                                  if tuple(sorted((i, j))) not in edges]))
            b = (b - 1) & common[a]
    return rows


if __name__ == '__main__':
    root = Path(__file__).resolve().parents[2]
    case = json.loads((root / 'algebra_strategy/five-owner-raw-packet.json').read_text())[0]
    forced = json.loads((root / 'reduction_analysis/five_owner_forced_active_census.json').read_text())
    census = json.loads((root / 'reduction_analysis/five_owner_pair_extension_census.json').read_text())
    rows = generate(case, forced['assignments'], [r['local'] for r in census['five_and_dirty_pair_exceptions']])
    expected = json.loads(Path(__file__).with_name('five_first_and_census.json').read_text())
    assert rows == expected['possible_first_ANDs']
    print(json.dumps(dict(first_AND_candidates=len(rows), status='PASS reproducibility')))
