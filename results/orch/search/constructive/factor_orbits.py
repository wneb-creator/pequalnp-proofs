#!/usr/bin/env python3
import argparse
from collections import Counter
import itertools
import json
from pathlib import Path
import time

from factor_compatibility import EDGE_SET, NONEDGES, additions
from factor_partition import TARGET

def graph_automorphisms():
    columns = [frozenset(u for u in range(7) if (u,v) in EDGE_SET) for v in range(7)]
    column_index = {column:v for v,column in enumerate(columns)}
    nonedge_index = {edge:i for i,edge in enumerate(NONEDGES)}
    maps = []
    for p in itertools.permutations(range(7)):
        images = [frozenset(p[u] for u in column) for column in columns]
        if all(image in column_index for image in images):
            q = [column_index[image] for image in images]
            maps.append([nonedge_index[p[u],q[v]] for u,v in NONEDGES])
    assert len(maps) == 168
    return maps

def map_bits(vertices,mapping):
    result = 0
    while vertices:
        bit = vertices & -vertices
        result |= 1 << mapping[bit.bit_length()-1]
        vertices ^= bit
    return result

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--input',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    started = time.monotonic()
    data = json.loads(args.input.read_text())
    assert data['complete']
    unseen = {tuple(sorted((item['x'],item['y']))) for item in data['pairs']}
    all_pairs = set(unseen)
    maps = graph_automorphisms()
    result = []
    while unseen:
        x,y = min(unseen)
        orbit = {tuple(sorted((map_bits(x,p),map_bits(y,p)))) for p in maps}
        assert orbit <= all_pairs
        unseen.difference_update(orbit)
        result.append({'x':x,'y':y,'sizes':sorted([x.bit_count(),y.bit_count()]),
                       'h':TARGET | additions(x),'k':TARGET | additions(y),
                       'orbit_size':len(orbit)})
    output = {'duration_seconds':time.monotonic()-started,'automorphisms':len(maps),
              'orbits':len(result),'total_pairs':sum(p['orbit_size'] for p in result),
              'orbit_size_distribution':dict(Counter(p['orbit_size'] for p in result)),
              'representatives':result}
    args.output.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({key:value for key,value in output.items() if key!='representatives'}))

if __name__ == '__main__':
    main()
