import json,random
from pathlib import Path
b=Path('/tmp/oec/pequalnp-pilot-81');rng=random.Random(28871937);allseeds=[]
truth=[sum(1<<x for x in range(16384) if x>>i&1) for i in range(14)];want=0
for l in range(7):
 for p in [l,(l+1)%7,(l+3)%7]:want|=truth[p]&truth[7+l]
for orientation in [0,1]:
 for seed in range(64):
  gates=[]
  def gate(op,a,c):gates.append([op,a,c]);return 13+len(gates)
  def ors(xs):
   xs=xs[:]
   while len(xs)>1:
    a=xs.pop(rng.randrange(len(xs)));c=xs.pop(rng.randrange(len(xs)));xs.append(gate('or',a,c))
   return xs[0]
  stars=[];centers=list(range(7));rng.shuffle(centers)
  for x in centers:
   if orientation:neighbors=[x,(x+1)%7,(x+3)%7];center=7+x
   else:neighbors=[7+x,7+(x-1)%7,7+(x-3)%7];center=x
   stars.append(gate('and',center,ors(neighbors)))
  out=ors(stars);assert len(gates)==27
  v=list(truth)
  for op,a,c in gates:v.append(v[a]&v[c] if op=='and' else v[a]|v[c])
  assert v[out]==want
  ds=[]
  for bv,dv in [(0,7),(7,0)]:
   vals=[i==bv for i in range(14)];der=[i==dv for i in range(14)]
   for op,a,c in gates:
    der.append((der[a] and vals[c]) or (vals[a] and der[c]) if op=='and' else der[a] or der[c]);vals.append(vals[a] and vals[c] if op=='and' else vals[a] or vals[c])
   ds.append(der[out])
  assert ds==[True,True]
  allseeds.append({'inputs':14,'size':27,'output':out,'marked_inputs':[0,7],'gates':gates,'derivatives':ds})
(b/'stochastic-ordinary27-seeds.json').write_text(json.dumps(allseeds)+'\n')
lines=(b/'stochastic-global-diverse.cfg').read_text().splitlines();head=list(map(int,lines[0].split()));head[5]+=len(allseeds);lines[0]=' '.join(map(str,head))
for d in allseeds:
 lines.append(f"27 {d['output']}");lines+=[' '.join(map(str,[int(op=='and'),a,c])) for op,a,c in d['gates']]
(b/'stochastic-global-trace-phase.cfg').write_text('\n'.join(lines)+'\n')
print('Verified128 ordinary27 seeds on all16384rows; both marked derivatives true. Combined next-phase config seeds768.')
