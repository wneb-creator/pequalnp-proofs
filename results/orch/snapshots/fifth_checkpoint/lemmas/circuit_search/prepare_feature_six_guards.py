import itertools
import json
import pathlib
import runpy
from prune import prune_once,signatures

HERE=pathlib.Path(__file__).resolve().parent
Builder=runpy.run_path(str(HERE/'generate_full_guard_seeds.py'))['Builder']
case=json.loads((HERE/'six-owner-gadgets.json').read_text())[1]
neighbors=[{l for p,l in case['edges'] if p==i} for i in range(6)]
tests=case['tests'].copy()
for raw in (1<<i for i in range(17)):
    available=raw
    for i,feature in enumerate(case['features']):
        if any(raw>>v&1 for v in feature['raw_indices']):available|=1<<(17+i)
    tests.append([available,0])
target=sum(y<<i for i,(_,y) in enumerate(tests))
input_sigs=signatures(30,[],tests)
seeds=[]
for size in range(2,7):
    for group in itertools.combinations(range(6),size):
        for count in range(2,min(size,4)+1):
            for guarded in itertools.combinations(group,count):
                builder=Builder(30);builder.unions={1<<i:i for i in range(17)}
                for i,f in enumerate(case['features']):builder.unions[sum(1<<v for v in f['raw_indices'])]=17+i
                common=set(group)-set(guarded)
                if common:builder.union(common)
                guards=[builder.gate(1,builder.union(set(group)-{p}),builder.union(neighbors[p])) for p in guarded]
                output=builder.gate(0,builder.union(group),builder.union(set.union(*(neighbors[p] for p in group))))
                for guard in guards:output=builder.gate(0,output,guard)
                for p in range(6):
                    if p not in group:output=builder.gate(1,output,builder.gate(0,p,builder.union(neighbors[p])))
                gates=builder.compact(output)
                if len(gates)>28:
                    while True:
                        reduced=prune_once(30,gates,tests)
                        if reduced==gates:break
                        gates=reduced
                if len(gates)>28:continue
                values=input_sigs.copy()
                for op,a,b in gates:values.append(values[a]|values[b] if op else values[a]&values[b])
                assert values[-1]&target==target
                false=(values[-1]&~target).bit_count()
                seeds.append(dict(group=list(group),guarded=list(guarded),gates=gates,output=29+len(gates),size=len(gates),false=false))
(HERE/'feature6-guard-seeds.json').write_text(json.dumps(seeds))
print(dict(seeds=len(seeds),minimum_size=min((s['size'] for s in seeds),default=None),
           minimum_false=min((s['false'] for s in seeds),default=None),
           three_or_more_guard_seeds=sum(len(s['guarded'])>=3 for s in seeds)))
