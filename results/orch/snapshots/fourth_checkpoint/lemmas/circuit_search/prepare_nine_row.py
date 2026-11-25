import json
import pathlib
from prune import prune_once, signatures

HERE=pathlib.Path(__file__).resolve().parent
case=json.loads((HERE.parent/'algebra_strategy/k9_arc_4_8_10_12.json').read_text())
small=json.loads((HERE/'subsets/k6_p3.json').read_text())
tests=case['tests']+[[1<<i,0] for i in range(22)]
assert len(tests)==286
ren={i:case['input_original'].index(orig) for i,orig in enumerate(small['input_original'])}
small_seeds=[json.loads((HERE/'k6-algebra-17-normalized.json').read_text())]
small_seeds += [s['gates'] for s in json.loads((HERE/'k6-rectangle-pool.json').read_text())]
small_seeds += [json.loads((HERE.parent/'algebra_strategy'/name).read_text()) for name in
                ('k6-cover17-sharing-lines.json','k6-cover17-sharing-redundant.json')]
small_seeds += [s['gates'] for s in json.loads((HERE/'k6-multiguard-seeds.json').read_text())]
seeds=[]
for g in small_seeds:
    mapping=ren|{17+i:22+i for i in range(len(g))}
    lifted=[[op,mapping[a],mapping[b]] for op,a,b in g]
    output=21+len(lifted)
    for original in case['original_rows']:
        if original in small['original_rows']:continue
        owner=case['input_original'].index(original)
        neighbors=[l for p,l in case['edges'] if p==owner]
        union=neighbors[0]
        for l in neighbors[1:]:
            lifted.append([1,union,l]);union=21+len(lifted)
        lifted.append([0,owner,union]);term=21+len(lifted)
        lifted.append([1,output,term]);output=21+len(lifted)
    assert len(lifted)<=43
    while True:
        reduced=prune_once(22,lifted,tests)
        if reduced==lifted:break
        lifted=reduced
    values=signatures(22,lifted,tests)
    out=values[-1]
    assert all(not y or out>>i&1 for i,(_,y) in enumerate(tests))
    assert all(not(out>>i&1) for i,(x,_) in enumerate(tests)
               if x.bit_count()==1 or x in ((1<<9)-1,((1<<13)-1)<<9))
    seeds.append(dict(gates=lifted,size=len(lifted),false=sum(not y and out>>i&1 for i,(_,y) in enumerate(tests))))
exact=case['seed']['gates'] if isinstance(case['seed'],dict) else case['seed']
seeds.append(dict(gates=exact,size=len(exact),false=0))
(HERE/'k9-lifted-seeds.json').write_text(json.dumps(seeds))
rows=[str(len(seeds))]
for s in seeds:
    g=[x.copy() for x in s['gates']]
    while len(g)<43:
        out=21+len(g);g.append([0,out,out])
    rows.append(str(len(g)));rows.extend(' '.join(map(str,x)) for x in g)
temporary=HERE/'k9-live-seeds.next'
temporary.write_text('\n'.join(rows)+'\n');temporary.replace(HERE/'k9-live-seeds.txt')
with (HERE/'k9-singleton-tests.txt').open('w') as f:
    f.write(f'{len(tests)}\n')
    for x,y in tests:f.write(f'{x} {y}\n')
print(dict(seeds=len(seeds),minimum_size=min(s['size'] for s in seeds),
           minimum_false_within43=min(s['false'] for s in seeds if s['size']<=43)))
