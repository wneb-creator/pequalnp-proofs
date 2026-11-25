import functools,itertools,json
from pathlib import Path

def analyze(name,p,l,E,gates):
 n=p+l;E=list(map(tuple,E));N=1<<n
 assert len(set(E))==len(E)
 assert all(not all((a,b) in E for a in aa for b in bb) for aa in itertools.combinations(range(p),2) for bb in itertools.combinations(range(l),2))
 values=[sum(1<<x for x in range(N) if x>>a&1) for a in range(n)]
 reach=[1<<a for a in range(n)]
 F=sum(1<<x for x in range(N) if any((x>>a&1) and (x>>(p+b)&1) for a,b in E))
 for i,(op,a,b) in enumerate(gates):
  assert 0<=a<n+i and 0<=b<n+i and op in ['and','or']
  values.append(values[a]&values[b] if op=='and' else values[a]|values[b])
  reach.append(0 if op=='and' else reach[a]|reach[b])
  assert not ((reach[n+i]&((1<<p)-1)) and (reach[n+i]>>p))
  if op=='and':assert values[n+i]&~F, 'AND must be dirty'
 tau=min(s.bit_count() for s in range(1<<n) if all((s>>a&1) or (s>>(p+b)&1) for a,b in E))
 neigh=[0]*n
 for a,b in E:neigh[a]|=1<<(p+b);neigh[p+b]|=1<<a
 def ortt(S):
  r=0
  for a in range(n):
   if S>>a&1:r|=values[a]
  return r
 pure={};expanded={};pureCovered=set()
 for i,(op,a,b) in enumerate(gates):
  if op!='or':continue
  f=values[n+i];supp=sum(1<<v for v in range(n) if f>>(1<<v)&1)
  if supp.bit_count()<2:continue
  for c,Nc in enumerate(neigh):
   if supp&~Nc or f&~ortt(Nc):continue
   expanded[i]=c
   if f==ortt(supp):
    pure[i]=c
    for v in range(n):
     if supp>>v&1:pureCovered.add((c,v-p) if c<p else (v,c-p))
 assert pureCovered==set(E), 'posted star coverage required'
 coverage={}
 for a in range(len(values)):
  for b in range(a,len(values)):
   f=values[a]&values[b]
   if f&~F:continue
   S=sum(1<<j for j,(u,v) in enumerate(E) if f>>((1<<u)|(1<<(p+v)))&1)
   if S:coverage[S]=(a,b)
 masks=[S for S in coverage if not any(S!=T and S&~T==0 for T in coverage)]
 @functools.lru_cache(None)
 def solve(missing):
  if missing==0:return ()
  bits=[1<<j for j in range(len(E)) if missing>>j&1]
  bit=min(bits,key=lambda b:sum(bool(S&b) for S in masks))
  choices=[]
  for S in masks:
   if S&bit:
    rest=solve(missing&~S)
    if rest is not None:choices.append((S,)+rest)
  return min(choices,key=len) if choices else None
 answer=solve((1<<len(E))-1)
 assert answer is not None,'no sound-pair cover'
 U=[coverage[S] for S in answer]
 joined=0
 for a,b in U:joined|=values[a]&values[b]
 assert joined==F
 J=sum(op=='and' for op,a,b in gates);O=len(gates)-J
 result={'name':name,'p':p,'l':l,'E':E,'gates':gates,'tau':tau,'U':U,'pair_count':len(U),'A_pure':len(pure),'A_expanded':len(expanded),'J':J}
 for family,A in [('pure',len(pure)),('expanded',len(expanded))]:
  B=O-A
  result['B_'+family]=B
  result['first_slack_'+family]=A+J+len(U)-len(E)
  result['second_slack_'+family]=B+len(U)-tau
 print(name,'E',len(E),'tau',tau,'gates',len(gates),'J',J,'minimum_U',len(U),'A_pure',len(pure),'A_expanded',len(expanded),'first_slack',result['first_slack_expanded'],'second_slack',result['second_slack_expanded'])
 return result

root=Path(__file__).resolve().parent
examples=[]
examples.append(analyze('path_with_dirty_rectangle',2,2,[(0,0),(0,1),(1,0)],
 [('or',0,1),('or',2,3),('and',4,5),('and',0,0),('or',2,7)]))
examples.append(analyze('split_star',1,4,[(0,b) for b in range(4)],
 [('or',1,2),('or',3,4)]))
examples.append(analyze('expanded_only_star_gate',3,2,[(0,0),(1,0),(2,0)],
 [('or',0,1),('and',2,4),('or',5,6),('or',1,2)]))
E6=[(0,0),(0,1),(1,1),(1,2),(2,2),(2,0)]
examples.append(analyze('C6_standard_residual',3,3,E6,[('or',4,5),('or',3,4),('or',3,5)]))
examples.append(analyze('C6_with_dead_opposite_stars',3,3,E6,[('or',4,5),('or',3,4),('or',3,5),('or',0,2),('or',0,1),('or',1,2)]))
fano=json.loads((root/'fano-row-count.json').read_text());control=json.loads((root/'fano27-control-gates.json').read_text())
examples.append(analyze('Fano_standard_residual',7,7,fano['E'],control[:14]))
(root/'normalized-bounds-models.json').write_text(json.dumps(examples,indent=1)+'\n')
