"""Prepare and calibrate the four-point K4-plus-private incidence core."""
import argparse
import itertools
import json
from pathlib import Path
from SearchCalibrate import check, serialize


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--cnf',type=Path,required=True)
    parser.add_argument('--output-dir',type=Path,required=True)
    args=parser.parse_args()
    data=json.loads(args.cnf.with_suffix('.map.json').read_text())
    n=data['n'];edges={tuple(e) for e in data['edges']}
    assert n==14 and data['k']==19 and len(edges)==16 and len(data['tests'])==32
    assert data['metadata']['points']==[2,3,8,15] and data['metadata']['outside_or_cost']==4
    columns={v:frozenset(u for u,w in edges if w==v) for v in range(4,n)}
    assert sorted(len(v) for v in columns.values())==[1]*4+[2]*6
    assert {v for v in columns.values() if len(v)==2}=={frozenset(q) for q in itertools.combinations(range(4),2)}
    inverse={mask:v for v,mask in columns.items()}
    automorphisms=[]
    for perm in itertools.permutations(range(4)):
        mapping=list(perm)+[inverse[frozenset(perm[u] for u in columns[v])] for v in range(4,n)]
        assert {(mapping[u],mapping[v]) for u,v in edges}==edges
        automorphisms.append(mapping)
    remaining=set(itertools.combinations(range(n),2));orbits=[]
    while remaining:
        a,b=min(remaining)
        orbit={tuple(sorted((perm[a],perm[b]))) for perm in automorphisms}
        assert orbit<=remaining
        remaining-=orbit
        orbits.append({'representative':[a,b],'size':len(orbit)})
    gates=[];roots=[]
    def add(op,a,b):
        gates.append((op,(a,b)))
        return n+len(gates)-1
    for u in range(4):
        neighbors=sorted(v for a,v in edges if a==u)
        assert len(neighbors)==4
        value=neighbors[0]
        for v in neighbors[1:]:value=add('or',value,v)
        roots.append(add('and',u,value))
    value=roots[0]
    for v in roots[1:]:value=add('or',value,v)
    assert len(gates)==19
    canonical=min((serialize(n,gates,perm) for perm in automorphisms),key=lambda gs:tuple((pair,op) for op,pair in gs))
    check(args.cnf,canonical)
    for x in range(1<<n):
        values=[bool(x>>i&1) for i in range(n)]
        for op,(a,b) in canonical:
            values.append(values[a] and values[b] if op=='and' else values[a] or values[b])
        assert values[-1]==any(x>>u&1 and x>>v&1 for u,v in edges)
    positives={(1<<u)|(1<<v) for u,v in edges}
    negatives=set()
    for mask in range(16):
        negatives.add(mask|sum(1<<v for v,points in columns.items() if all(not(mask>>u&1) for u in points)))
    assert set(data['tests'])==positives|negatives and len(negatives)==16
    args.output_dir.mkdir(parents=True,exist_ok=True)
    (args.output_dir/'k4private-automorphisms.json').write_text(json.dumps({'automorphisms':automorphisms,'unordered_first_gate_orbits':orbits},indent=2)+'\n')
    (args.output_dir/'k4private-core.json').write_text(json.dumps({'inputs':n,'edges':sorted(edges),'positive_tests':sorted(positives),'negative_tests':sorted(negatives),'metadata':data['metadata'],'lift_overhead':106,'baseline':19,'target':18},indent=2)+'\n')
    (args.output_dir/'k4private-baseline19.json').write_text(json.dumps({'inputs':n,'gates':canonical,'size':19,'output':n+18,'verified_exhaustive_inputs':1<<n,'proof_status':'computational baseline; requires Lean verification'},indent=2)+'\n')
    print(json.dumps({'verdict':'PASS','automorphisms':len(automorphisms),'first_pair_orbits':len(orbits),'baseline_size':19,'exhaustive_cases':1<<n,'tests':len(data['tests']),'lift_overhead':106}),flush=True)


if __name__=='__main__':
    main()
