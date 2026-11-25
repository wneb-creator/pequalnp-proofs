import itertools
import json
import pathlib
import runpy

HERE=pathlib.Path(__file__).resolve().parent
Builder=runpy.run_path(str(HERE/'generate_full_guard_seeds.py'))['Builder']
case=json.loads((HERE/'six-owner-gadgets.json').read_text())[1]
assert case['name']=='core6_02' and case['inputs']==30
neighbors=[{l for p,l in case['edges'] if p==i} for i in range(6)]
tests=case['tests'].copy()
for raw in (1<<i for i in range(17)):
    value=raw
    for i,f in enumerate(case['features']):
        if any(raw>>j&1 for j in f['raw_indices']):value|=1<<(17+i)
    tests.append([value,0])
with (HERE/'feature6-tests.txt').open('w') as f:
    f.write(f'{len(tests)}\n')
    for x,y in tests:f.write(f'{x} {y}\n')
seeds=[]
groups=[(0,2)]+[s for k in range(2,7) for s in itertools.combinations(range(6),k) if s!=(0,2)]
for group in groups:
    builder=Builder(30)
    builder.unions={1<<i:i for i in range(17)}
    for i,feature in enumerate(case['features']):
        builder.unions[sum(1<<v for v in feature['raw_indices'])]=17+i
    output=builder.gate(0,builder.union(group),builder.union(set.union(*(neighbors[p] for p in group))))
    for p in range(6):
        if p not in group:output=builder.gate(1,output,builder.gate(0,p,builder.union(neighbors[p])))
    gates=builder.compact(output)
    if len(gates)>28:continue
    bad=0
    for x,y in tests:
        values=[x>>i&1 for i in range(30)]
        for op,a,b in gates:values.append(values[a]|values[b] if op else values[a]&values[b])
        assert not y or values[-1]
        bad+=not y and values[-1]
    seeds.append(dict(group=list(group),gates=gates,output=29+len(gates),size=len(gates),false=bad))
(HERE/'feature6-seeds.json').write_text(json.dumps(seeds))
lines=[str(len(seeds))]
for seed in seeds:
    lines.append(str(len(seed['gates'])));lines.extend(' '.join(map(str,g)) for g in seed['gates'])
(HERE/'feature6-seeds.txt').write_text('\n'.join(lines)+'\n')
print(dict(case=case['name'],seeds=len(seeds),first_size=seeds[0]['size'],first_false=seeds[0]['false']))
