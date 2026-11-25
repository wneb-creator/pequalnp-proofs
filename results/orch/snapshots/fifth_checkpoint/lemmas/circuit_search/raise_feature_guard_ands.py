import json
import pathlib
import random
from prune import signatures

HERE=pathlib.Path(__file__).resolve().parent
source=json.loads((HERE/'feature6-guard-seeds.json').read_text())
tests=json.loads((HERE/'six-owner-gadgets.json').read_text())[1]['tests']
rng=random.Random(65066)

def compact(gates):
    used={30+len(gates)-1}
    for i in range(len(gates)-1,-1,-1):
        if 30+i in used:used.update(gates[i][1:])
    ren={i:i for i in range(30)};result=[]
    for i,(op,a,b) in enumerate(gates):
        if 30+i in used:ren[30+i]=30+len(result);result.append([op,ren[a],ren[b]])
    return result

def expand(gates,index,child,other):
    ren={i:i for i in range(30)};result=[]
    for i,(op,a,b) in enumerate(gates):
        if i==index:
            _,u,v=gates[child-30]
            result.append([0,ren[u],ren[other]]);left=29+len(result)
            result.append([0,ren[v],ren[other]]);right=29+len(result)
            result.append([1,left,right])
        else:result.append([op,ren[a],ren[b]])
        ren[30+i]=29+len(result)
    return compact(result)

results=[];seen=set()
for item in source:
    if item['size']>25:continue
    for trial in range(20):
        gates=[g.copy() for g in item['gates']]
        for step in range(5):
            count=sum(op==0 for op,_,_ in gates)
            if count>=6:
                key=tuple(map(tuple,gates))
                if key not in seen:
                    assert signatures(30,gates,tests)[-1]==signatures(30,item['gates'],tests)[-1]
                    seen.add(key);results.append(dict(group=item['group'],guarded=item['guarded'],gates=gates,
                                                     output=29+len(gates),size=len(gates),ands=count,false=item['false']))
            if count>=7:break
            pure=[i<6 for i in range(30)]
            for _,a,b in gates:pure.append(pure[a] and pure[b])
            choices=[]
            for i,(op,a,b) in enumerate(gates):
                if op!=0:continue
                for child,other in [(a,b),(b,a)]:
                    if child>=30 and gates[child-30][0]==1 and pure[child]:
                        expanded=expand(gates,i,child,other)
                        if len(expanded)<=28:choices.append(expanded)
            if not choices:break
            gates=rng.choice(choices)
results.sort(key=lambda s:(s['ands'],s['false'],s['size']))
(HERE/'feature6-wide-validands.json').write_text(json.dumps(results))
lines=[str(len(results))]
for item in results:
    lines.append(str(len(item['gates'])));lines.extend(' '.join(map(str,g)) for g in item['gates'])
(HERE/'feature6-wide-validands.txt').write_text('\n'.join(lines)+'\n')
print(dict(seeds=len(results),ands=sorted({s['ands'] for s in results}),minimum_size=min((s['size'] for s in results),default=None)))
