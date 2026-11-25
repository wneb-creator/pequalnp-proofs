import argparse
import json
import math
import zlib
from collections import defaultdict
from pathlib import Path


def rice(bits, values):
    values = sorted(values)
    if len(values) <= 1:
        return {'bits': bits * len(values), 'k': 0}
    deltas = [b - a for a, b in zip(values, values[1:])]
    k = min(range(bits + 1), key=lambda k: sum((d >> k) + 1 + k for d in deltas))
    return {'bits': bits + sum((d >> k) + 1 + k for d in deltas), 'k': k}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('census')
    args = ap.parse_args()
    root = Path(args.census)
    profiles = json.loads((root / 'maximal-profiles.json').read_text())
    weights = json.loads((root / 'weights.json').read_text())
    groups = defaultdict(list)
    for r in profiles:
        groups[r['weight'], r['cost']].append(r)
    dictionaries = {}
    for w in weights:
        shape = (w['rows'], w['cols'])
        dictionaries[shape] = (set(), set())
    for r in profiles:
        w = weights[r['weight']]
        p, n = dictionaries[w['rows'], w['cols']]
        p.add(r['positive_mask']); n.add(r['negative_false_mask'])
    dictionary_data = {}
    dictionary_bits = 0
    for shape, (p, n) in dictionaries.items():
        p, n = sorted(p), sorted(n)
        pbits, nbits = max(1, (len(p)-1).bit_length()), max(1, (len(n)-1).bit_length())
        dictionary_data[shape] = (dict(zip(p, range(len(p)))), dict(zip(n, range(len(n)))), pbits, nbits)
        dictionary_bits += rice(shape[0], p)['bits'] + rice(shape[1], n)['bits']
    raw_bits = direct_rice_bits = dictionary_raw_bits = dictionary_rice_bits = 0
    by_group = []
    for (wi, cap), rows in groups.items():
        w = weights[wi]; pbits, nbits = w['rows'], w['cols']
        width = pbits + nbits
        raw_bits += width * len(rows)
        codes0 = [r['positive_mask'] | (r['negative_false_mask'] << pbits) for r in rows]
        codes1 = [r['negative_false_mask'] | (r['positive_mask'] << nbits) for r in rows]
        r0, r1 = rice(width, codes0), rice(width, codes1)
        direct_rice_bits += min(r0['bits'], r1['bits'])
        pd, nd, pb, nb = dictionary_data[pbits, nbits]
        dc0 = [pd[r['positive_mask']] | (nd[r['negative_false_mask']] << pb) for r in rows]
        dc1 = [nd[r['negative_false_mask']] | (pd[r['positive_mask']] << nb) for r in rows]
        d0, d1 = rice(pb+nb, dc0), rice(pb+nb, dc1)
        dictionary_raw_bits += (pb+nb) * len(rows)
        dictionary_rice_bits += min(d0['bits'], d1['bits'])
        by_group.append({'weight': wi, 'cost': cap, 'count': len(rows),
                         'direct_rice': min([r0 | {'orientation': 0}, r1 | {'orientation': 1}], key=lambda r: r['bits']),
                         'dictionary_rice': min([d0 | {'orientation': 0}, d1 | {'orientation': 1}], key=lambda r: r['bits'])})
    summary = {'profiles': len(profiles), 'groups': len(groups),
               'raw_hex_digits': math.ceil(raw_bits / 4),
               'direct_rice_hex_digits': math.ceil(direct_rice_bits / 4),
               'dictionary_entries': {str(shape): [len(p), len(n)] for shape, (p, n) in dictionaries.items()},
               'dictionary_data_hex_digits': math.ceil(dictionary_bits / 4),
               'dictionary_index_raw_hex_digits': math.ceil(dictionary_raw_bits / 4),
               'dictionary_index_rice_hex_digits': math.ceil(dictionary_rice_bits / 4),
               'dictionary_total_rice_hex_digits': math.ceil((dictionary_rice_bits + dictionary_bits) / 4),
               'scope': 'Literal digit estimates exclude per-group proof declarations, metadata, decoder and semantic adapters.'}
    (root / 'encoding-estimate.json').write_text(json.dumps(summary, indent=2) + '\n')
    (root / 'encoding-groups.json').write_text(json.dumps(by_group, indent=2) + '\n')
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == '__main__':
    main()
