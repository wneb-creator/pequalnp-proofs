import itertools
import json
from pathlib import Path

P=Path(__file__).resolve().parent
p=l=3;n=p+l
edges={(0,0),(0,2),(1,0),(1,1),(2,1),(2,2)}
gates=[(1,3,5),(0,0,6),(1,3,4),(0,1,8),(1,4,5),(0,2,10),(1,7,9),(1,12,11),(1,0,1),(1,1,2),(1,0,2)]
output=13
target=lambda r:any(r>>a&1 and r>>(p+b)&1 for a,b in edges)
assert all(not all(e in edges for e in ((a,b),(a,c),(d,b),(d,c))) for a,d in itertools.combinations(range(p),2) for b,c in itertools.combinations(range(l),2))
truth=[[bool(r>>i&1) for r in range(1<<n)] for i in range(n)]
reach=[{i} for i in range(n)];mixed=[]
for j,(op,a,b) in enumerate(gates):
    assert 0<=a<n+j and 0<=b<n+j
    truth.append([(x or y) if op else (x and y) for x,y in zip(truth[a],truth[b])])
    reach.append(reach[a]|reach[b] if op else set())
    if op and any(i<p for i in reach[-1]) and any(i>=p for i in reach[-1]):mixed.append(j)
assert not mixed and all(truth[output][r]==target(r) for r in range(1<<n))
stars=[]
for j,(op,a,b) in enumerate(gates):
    if not op:continue
    support={i for i in range(n) if truth[n+j][1<<i]}
    if len(support)<2 or not all(truth[n+j][r]==any(r>>i&1 for i in support) for r in range(1<<n)):continue
    centers=[]
    for v in range(n):
        if v<p and all(i>=p and (v,i-p) in edges for i in support):centers.append(v)
        if v>=p and all(i<p and (i,v-p) in edges for i in support):centers.append(v)
    if centers:
        assert len(centers)==1
        stars.append({'gate':j,'center':centers[0],'support':sorted(support)})
assert all(any((s['center']==a and p+b in s['support']) or (s['center']==p+b and a in s['support']) for s in stars) for a,b in edges)
components=[]
for center in range(n):
    todo=[set(s['support']) for s in stars if s['center']==center]
    while todo:
        comp=todo.pop();changed=True
        while changed:
            changed=False
            for s in todo[:]:
                if comp&s:comp|=s;todo.remove(s);changed=True
        components.append({'center':center,'support':sorted(comp)})
tau=min(r.bit_count() for r in range(1<<n) if all(r>>a&1 or r>>(p+b)&1 for a,b in edges))
k=len(components);d=sum(len(c['support']) for c in components);rest=len(gates)-len(stars)
assert k==6 and d==12 and len(stars)==6 and tau==3 and rest==5
assert rest<k+tau-1
assert len(edges)+tau<=len(gates)+1
result={'p':p,'l':l,'edges':sorted(edges),'gates':gates,'output':output,'AO2':True,'truth_rows_checked':1<<n,'tCount':len(mixed),'star_witnesses':stars,'components':components,'K':k,'d':d,'tau':tau,'pure_star_OR_gates':len(stars),'remaining_gates':rest,'proposed_remaining_lower_bound':k+tau-1,'posted_conclusion_holds':True,'note':'Counterexample to the proposed stronger component ledger only; not a refutation of L-meta-4970.'}
(P/'dead_star_ledger.json').write_text(json.dumps(result,indent=2)+'\n')
print('Verified all posted premises on64 inputs. K=6,d=12,tau=3,pure-star ORs=6,remaining=5<8. Posted conclusion holds.')
