import itertools
import json
import pathlib
import runpy
from prune import prune_once

HERE=pathlib.Path(__file__).resolve().parent
Builder=runpy.run_path(str(HERE/'generate_full_guard_seeds.py'))['Builder']
case=json.loads((HERE/'subsets/k6_p3.json').read_text())
neighbors=[{l for p,l in case['edges'] if p==i} for i in range(6)]
seeds=[]
for size in (4,5,6):
    for group in itertools.combinations(range(6),size):
        choices=itertools.chain.from_iterable(itertools.combinations(group,k) for k in (2,3,4) if k<len(group))
        for guarded in choices:
            builder=Builder(17)
            builder.union(set(group)-set(guarded))
            guards=[]
            for p in guarded:
                guards.append(builder.gate(1,builder.union(set(group)-{p}),builder.union(neighbors[p])))
            merged=builder.gate(0,builder.union(group),builder.union(set().union(*(neighbors[p] for p in group))))
            for guard in guards:merged=builder.gate(0,merged,guard)
            output=merged
            for p in range(6):
                if p not in group:output=builder.gate(1,output,builder.gate(0,p,builder.union(neighbors[p])))
            gates=builder.compact(output)
            if len(gates)>28:
                while True:
                    reduced=prune_once(17,gates,case['tests'])
                    if reduced==gates:break
                    gates=reduced
            if len(gates)>28:continue
            a,b=guarded[:2];cubic_lines=set().union(*(neighbors[p] for p in group))-neighbors[a]-neighbors[b]
            if not cubic_lines:continue
            errors=0
            for x,y in case['tests']:
                values=[x>>i&1 for i in range(17)]
                for op,u,v in gates:values.append(values[u]|values[v] if op else values[u]&values[v])
                assert not y or values[-1]
                errors+=not y and values[-1]
            surviving_cubics=[]
            for l in cubic_lines:
                actual=[]
                for selected,expected in [({a,b,l},1),({a,l},0),({b,l},0)]:
                    values=[int(i in selected) for i in range(17)]
                    for op,u,v in gates:values.append(values[u]|values[v] if op else values[u]&values[v])
                    actual.append(values[-1])
                if actual==[1,0,0]:surviving_cubics.append([a,b,l])
            if not surviving_cubics and errors:continue
            seeds.append(dict(group=group,guarded=guarded,gates=gates,output=16+len(gates),size=len(gates),
                              false=errors,genuine_cubics=surviving_cubics))
(HERE/'k6-multiguard-seeds.json').write_text(json.dumps(seeds))
summary=dict(seeds=len(seeds),minimum_size=min((s['size'] for s in seeds),default=None),
             minimum_false=min((s['false'] for s in seeds),default=None))
print(summary)
