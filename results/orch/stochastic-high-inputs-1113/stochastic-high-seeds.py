from pathlib import Path
import collections,itertools,json,random
b=Path('/tmp/oec/pequalnp-pilot-81');centers=list(range(1,7))+[7,11,13];edges=[(p,7+l) for l in range(7) for p in [l,(l+1)%7,(l+3)%7]];overlap=[e for e in edges if e[0] in centers and e[1] in centers];assert len(overlap)==6
best={};recipes=collections.defaultdict(list)
for orientation in range(64):
 stars={c:[] for c in centers}
 for p,l in edges:
  if (p,l) in overlap:c=l if orientation>>overlap.index((p,l))&1 else p
  else:c=p if p in centers else l
  stars[c].append(l if c==p else p)
 fan=[0]*14
 for c,ns in stars.items():
  fan[c]+=1
  for n in ns:fan[n]+=1
 base=sum(1<<i for i in range(14) if fan[i]>1)
 for square_mask in range(1<<9):
  if not(square_mask>>6&1):continue
  eligible=base
  for i,c in enumerate(centers):
   if square_mask>>i&1:
    for v in [c]+stars[c]:eligible|=1<<v
  p=eligible.bit_count();size=29+2*square_mask.bit_count()
  if p not in [12,13,14]:continue
  if p not in best or size<best[p]:best[p]=size;recipes[p]=[]
  if size==best[p]:recipes[p].append((orientation,square_mask,stars,eligible))
truth=[sum(1<<x for x in range(16384) if x>>i&1) for i in range(14)];want=0
for p,l in edges:want|=truth[p]&truth[l]
rng=random.Random(9187642);output=[];report=[]
for p in [12,13,14]:
 rr=recipes[p];rng.shuffle(rr);chosen=rr[:64];report.append({'eligible_count':p,'best_gate_cost':best[p],'minimum_recipes':len(rr),'selected':len(chosen)})
 for orientation,mask,stars,eligible in chosen:
  for dual in [False,True]:
   gates=[]
   def gate(op,a,c):gates.append([op,a,c]);return 13+len(gates)
   def ors(xs):
    vv=xs[0]
    for x in xs[1:]:vv=gate('or',vv,x)
    return vv
   outputs=[]
   for i,c in enumerate(centers):
    nn=ors(stars[c]);a=gate('and',c,nn)
    if mask>>i&1:a=gate('and',a,gate('and',c,nn))
    outputs.append(a)
   out=ors(outputs)
   if dual:
    perm=[7+(-i)%7 for i in range(7)]+[(-i)%7 for i in range(7)]
    gates=[[op,perm[a] if a<14 else a,perm[c] if c<14 else c] for op,a,c in gates]
   v=list(truth);supp=[1<<i for i in range(14)];ff=[0]*(14+len(gates))
   for j,(op,a,c) in enumerate(gates):
    assert a!=c and a<14+j and c<14+j
    v.append(v[a]&v[c] if op=='and' else v[a]|v[c]);supp.append(supp[a]&supp[c] if op=='and' else supp[a]|supp[c]);ff[a]+=1;ff[c]+=1
   assert v[out]==want
   for bv,dv in [(0,7),(7,0)]:
    vv=[i==bv for i in range(14)];dd=[i==dv for i in range(14)]
    for op,a,c in gates:
     dd.append((dd[a] and vv[c]) or (vv[a] and dd[c]) if op=='and' else dd[a] or dd[c]);vv.append(vv[a] and vv[c] if op=='and' else vv[a] or vv[c])
    assert not vv[out] and not dd[out]
   elig=bp=bz=0
   for w,n in enumerate(ff):
    if n>1:
     if supp[w]:elig|=supp[w];bp+=n-1
     else:bz+=n-1
   assert elig.bit_count()==p and bz==0 and bp==len(gates)+1-14 and len(gates)==best[p]
   output.append({'inputs':14,'size':len(gates),'output':out,'marked_inputs':[0,7],'eligible_count':p,'eligible_inputs':[i for i in range(14) if elig>>i&1],'Bplus':bp,'Bzero':bz,'orientation':orientation,'squared_stars_mask':mask,'dual':dual,'gates':gates})
(b/'stochastic-high-seeds.json').write_text(json.dumps(output)+'\n')
(b/'stochastic-high-seeds-verification.json').write_text(json.dumps({'seeds':len(output),'full_truth_rows_per_seed':16384,'both_derivatives_false_at':[0,7],'best_within_this_star_squaring_family_only':report,'verdict':'PASS'},indent=2)+'\n')
print(json.dumps({'seeds':len(output),'family_bounds_only':report,'all_truth_and_trace_checks':'PASS'},indent=2))
