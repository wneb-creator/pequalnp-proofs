import itertools,json,sys
from pathlib import Path
BASE=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(BASE/'counterexample'))
from common1342 import EDGES,N,audit
E={frozenset(e) for e in EDGES};records=[];seen=set()
for a,c in EDGES:
 for e in range(N):
  if e in [a,c] or frozenset([e,a]) not in E or frozenset([e,c]) not in E:continue
  for b in range(N):
   for d in range(N):
    if len({a,b,c,d})<4 or e in [b,d]:continue
    H={frozenset([a,c]),frozenset([a,d]),frozenset([b,c])}
    if not H<=E or frozenset([b,d]) in E:continue
    unit=tuple(sorted([tuple(sorted([a,b])),tuple(sorted([c,d]))]))
    if unit in seen:continue
    residual=[uv for uv in EDGES if frozenset(uv) not in H]
    covers=[C for C in itertools.combinations(range(N),5) if e in C and all(u in C or v in C for u,v in residual)]
    if not covers:continue
    C=covers[0];gs=[]
    def add(op,u,v):gs.append((op,u,v));return N+len(gs)-1
    def join(vs):
     out=vs[0]
     for v in vs[1:]:out=add('or',out,v)
     return out
    p=add('or',a,b);q=add('or',c,d);t=add('and',p,q)
    ctx=add('or',a,c);block=add('and',t,ctx);terms=[block]
    assigned={v:[] for v in C}
    for u,v in residual:
     owner=e if e in [u,v] and (a in [u,v] or c in [u,v]) else u if u in C else v
     assigned[owner].append(v if u==owner else u)
    for v,ls in assigned.items():
     if not ls:continue
     if v==e:
      assert a in ls and c in ls
      ors=join([ctx]+[u for u in ls if u not in [a,c]])
     else:ors=join(ls)
     terms.append(add('and',v,ors))
    out=join(terms);check=audit(gs,out)
    assert len(gs)==22 and not check['false_positives'] and not check['false_negatives']
    seen.add(unit);records.append({'unit':unit,'center_triangle':[a,c,e],'cover':C,'gates':gs,'output':out,'audit':check})
(BASE/'direct/neutral-units22.json').write_text(json.dumps(records,indent=2))
print('units',len(records))
for r in records:print(r['unit'],'triangle',r['center_triangle'],'cover',r['cover'],'junk',r['audit']['junk_ands'])
