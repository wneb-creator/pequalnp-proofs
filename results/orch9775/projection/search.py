import json,time,itertools
from pathlib import Path
start=time.monotonic();out=Path('results/orch9775/projection');d=json.loads((out/'graph.json').read_text());N=d['neighbors'];inds=d['independent'];maxs=d['maximal'];nb={m:sum(1<<v for v in range(14) if N[v]&m) for m in inds};bits={m:[v for v in range(14) if m>>v&1] for m in inds};subsets={m:[s for s in inds if s&m==s] for m in inds};data={};rows=[]
for P in inds:
 if not P:continue
 opts={f:[A for A in maxs if (P^(1<<f))&A==P^(1<<f) and N[f]&A] for f in bits[P]}
 q={J:sum(1<<f for f in bits[P] if any(nb[A]&J==J for A in opts[f])) for J in inds}
 bestJ={R:max(((J.bit_count()+q[J].bit_count(),J,q[J]) for J in subsets[R]),default=(0,0,0)) for R in inds}
 for I in inds:
  U=sum(1<<v for v in bits[I] if (P&N[v]).bit_count()==3);W=sum(1<<v for v in bits[I] if (P&N[v]).bit_count()==2)
  score,J,Q=bestJ[I&nb[P]]
  bound=score+2*U.bit_count()+W.bit_count()+14-I.bit_count()-P.bit_count()-(P&~I).bit_count()
  if I not in data or data[I]['bound']<bound:
   A={f:next(A for A in opts[f] if nb[A]&J==J) for f in bits[P] if Q>>f&1}
   data[I]={'I':I,'P':P,'U':U,'W':W,'J':J,'Q':Q,'A':A,'bound':bound}
rows=sorted(data.values(),key=lambda x:x['I']);(out/'private-bounds.json').write_text(json.dumps({'scope':'Finite witnesses for L9774 private_bound, conditional Bzero=0; no Lean check yet','elapsed':time.monotonic()-start,'rows':rows},indent=2)+'\n')
from collections import Counter
print('elapsed',time.monotonic()-start,'histogram',dict(sorted(Counter(r['bound'] for r in rows).items())))
print('survivorsBplus11',[r['I'] for r in rows if r['bound']<=11 and r['I'].bit_count()>=3])
