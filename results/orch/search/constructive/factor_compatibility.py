#!/usr/bin/env python3
"""Enumerate maximal compatible nonedge-factor pairs via support partitions."""
import argparse
from collections import Counter
import json
from pathlib import Path
import time

from factor_partition import EDGES, TARGET

EDGE_SET = {(u,v-7) for u,v in EDGES}
NONEDGES = [(u,v) for u in range(7) for v in range(7) if (u,v) not in EDGE_SET]
ALL = (1 << 28)-1
COMPAT = [sum(1 << j for j,(c,d) in enumerate(NONEDGES)
              if (a,d) in EDGE_SET or (c,b) in EDGE_SET) for a,b in NONEDGES]

def common_neighbors(vertices):
    result = ALL
    while vertices:
        bit = vertices & -vertices
        result &= COMPAT[bit.bit_length()-1]
        vertices ^= bit
    return result

def additions(vertices):
    return sum(1 << (7*u+v) for j,(u,v) in enumerate(NONEDGES) if vertices >> j & 1)

def enumerate_pairs(seconds):
    start = time.monotonic()
    pairs = set()
    closures = {}
    cuts = 0
    subsets = 0
    smaller_sizes = Counter()
    complete = True
    for a in range(128):
        for b in range(128):
            if (a,b) > (a^127,b^127):
                continue
            if time.monotonic()-start > seconds:
                complete = False
                break
            cuts += 1
            x = sum(1 << j for j,(u,v) in enumerate(NONEDGES) if a >> u & 1 and b >> v & 1)
            y = sum(1 << j for j,(u,v) in enumerate(NONEDGES) if not a >> u & 1 and not b >> v & 1)
            if x.bit_count() > y.bit_count():
                x,y = y,x
            smaller_sizes[x.bit_count()] += 1
            common = [y]
            vertices = x
            while vertices:
                bit = vertices & -vertices
                mask = COMPAT[bit.bit_length()-1]
                common += [old & mask for old in common]
                vertices ^= bit
            subsets += len(common)-1
            for candidate in set(common[1:]):
                if not candidate:
                    continue
                if candidate not in closures:
                    closed_x = common_neighbors(candidate)
                    closed_y = common_neighbors(closed_x)
                    assert closed_x and closed_y
                    assert common_neighbors(closed_y) == closed_x
                    closures[candidate] = tuple(sorted((closed_x,closed_y)))
                pairs.add(closures[candidate])
        if not complete:
            break
    result = []
    for x,y in sorted(pairs):
        assert x & y == 0
        assert common_neighbors(x) == y and common_neighbors(y) == x
        result.append({'x':x,'y':y,'sizes':[x.bit_count(),y.bit_count()],
                       'h':TARGET | additions(x),'k':TARGET | additions(y)})
    return {'complete':complete,'duration_seconds':time.monotonic()-start,
            'cuts':cuts,'nonempty_subsets_visited':subsets,
            'smaller_side_sizes':dict(smaller_sizes),'maximal_pairs':len(result),
            'pair_size_distribution':dict(Counter(str(sorted(p['sizes'])) for p in result)),
            'nonedges':NONEDGES,'pairs':result}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seconds',type=float,default=10)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    assert all(c.bit_count() == 18 for c in COMPAT)
    result = enumerate_pairs(args.seconds)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:value for key,value in result.items() if key not in {'pairs','nonedges'}},sort_keys=True))

if __name__ == '__main__':
    main()
