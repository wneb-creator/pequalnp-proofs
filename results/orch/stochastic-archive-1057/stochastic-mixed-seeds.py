import json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-81')
seedrows=(base/'stochastic-global-dual.cfg').read_text().splitlines();permutation=[7+(-i)%7 for i in range(7)]+[(-i)%7 for i in range(7)]
truth=[sum(1<<x for x in range(16384) if x>>i&1) for i in range(14)]
wanted=0
for l in range(7):
 for p in [l,(l+1)%7,(l+3)%7]:wanted|=truth[p]&truth[7+l]
seeds=[]
for center in [2,4,5,6]:
 for subset in range(1,128,2):
  g=[]
  def gate(op,a,b):
   assert a!=b
   g.append([op,a,b]);return 13+len(g)
  def reduce_or(xs):
   v=xs[0]
   for x in xs[1:]:v=gate('or',v,x)
   return v
  stars=[]
  for l in range(7):
   ps=[p for p in [l,(l+1)%7,(l+3)%7] if p!=center]
   stars.append(gate('and',7+l,reduce_or(ps)))
  h=reduce_or([stars[l] for l in range(7) if subset>>l&1])
  n=reduce_or([7+l for l in range(7) if center in [l,(l+1)%7,(l+3)%7]])
  out=gate('and',gate('or',h,center),gate('or',h,n))
  out=reduce_or([out]+[stars[l] for l in range(7) if not(subset>>l&1)])
  assert len(g)==29
  for dual in [False,True]:
   gg=[[op,permutation[a] if dual and a<14 else a,permutation[b] if dual and b<14 else b] for op,a,b in g]
   v=list(truth)
   for op,a,b in gg:v.append(v[a]&v[b] if op=='and' else v[a]|v[b])
   assert v[out]==wanted
   for bv,dv in [(0,7),(7,0)]:
    vv=[i==bv for i in range(14)];dd=[i==dv for i in range(14)]
    for op,a,b in gg:
     dd.append((dd[a] and vv[b]) or (vv[a] and dd[b]) if op=='and' else dd[a] or dd[b]);vv.append(vv[a] and vv[b] if op=='and' else vv[a] or vv[b])
    assert not dd[out]
   fan=[0]*43;sup=[1<<i for i in range(14)]
   for op,a,b in gg:fan[a]+=1;fan[b]+=1;sup.append(sup[a]&sup[b] if op=='and' else sup[a]|sup[b])
   elig=bp=bz=0
   for i in range(42):
    if fan[i]>1:
     if sup[i]:elig|=sup[i];bp+=fan[i]-1
     else:bz+=fan[i]-1
   assert elig.bit_count()==9 and bp==15 and bz==1
   seeds.append({'inputs':14,'size':29,'output':out,'marked_inputs':[0,7],'center':center,'H_line_subset':subset,'dual':dual,'eligible_inputs':[i for i in range(14) if elig>>i&1],'Bplus':bp,'Bzero':bz,'gates':gg})
(base/'stochastic-mixed29-seeds.json').write_text(json.dumps(seeds)+'\n')
head=list(map(int,seedrows[0].split()));head[5]+=len(seeds);lines=[' '.join(map(str,head))]+seedrows[1:]
for s in seeds:
 lines.append(f"29 {s['output']}")
 lines+=[' '.join(map(str,[int(op=='and'),a,b])) for op,a,b in s['gates']]
(base/'stochastic-global-mixed.cfg').write_text('\n'.join(lines)+'\n')
print('Verified',len(seeds),'mixed29 seeds on all16384 inputs and two derivatives. All p9 Bplus15 Bzero1. Combined config seeds=',head[5])
