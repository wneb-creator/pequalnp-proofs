import itertools,json,time
from pathlib import Path

def run(n,maxdepth):
 t0=time.monotonic(); allmask=(1<<(1<<n))-1
 inputs=tuple(sum(1<<a for a in range(1<<n) if a>>i&1) for i in range(n))
 pairs=list(itertools.combinations(range(n),2))
 targets={}
 for em in range(1<<len(pairs)):
  edges=tuple(e for j,e in enumerate(pairs) if em>>j&1)
  E={frozenset(e) for e in edges}
  tri=any(all(frozenset(e) in E for e in itertools.combinations(t,2)) for t in itertools.combinations(range(n),3))
  sq=any(all(frozenset((c[j],c[(j+1)%4])) in E for j in range(4)) for c in itertools.permutations(range(n),4))
  if tri or sq: continue
  f=sum(1<<a for a in range(1<<n) if any((a>>u&1) and (a>>v&1) for u,v in edges))
  targets[f]=edges
 def good(gates,edges):
  vals=list(inputs); anc=[set() for _ in inputs]; owned=[]
  for j,(op,a,b) in enumerate(gates):
   v=vals[a]&vals[b] if op=='and' else vals[a]|vals[b]
   aa=anc[a]|anc[b]
   edgeowns=[e for e in edges if v>>( (1<<e[0])|(1<<e[1]) )&1 and not any(vals[k]>>( (1<<e[0])|(1<<e[1]) )&1 for k in aa)]
   if op=='and':
    if not edgeowns or not set.intersection(*(set(e) for e in edgeowns)): return False,owned+[edgeowns]
    aa=aa|{n+j}
   vals.append(v);anc.append(aa);owned.append(edgeowns if op=='and' else [])
  return True,owned
 solved={0:{'size':0,'gates':[],'edges':[],'good':True}}
 states={():()};sizes=[]
 for depth in range(1,maxdepth+1):
  nxt={};created=0
  for fs,gates in states.items():
   vals=inputs+tuple((inputs+fs)[0:0])
   actual=list(inputs)
   for op,a,b in gates: actual.append(actual[a]&actual[b] if op=='and' else actual[a]|actual[b])
   existing=set(actual)
   for a,b in itertools.combinations(range(len(actual)),2):
    for op,f in [('and',actual[a]&actual[b]),('or',actual[a]|actual[b])]:
     if f in existing:continue
     ng=gates+((op,a,b),)
     if f in targets and f not in solved:
      ok,owns=good(ng,targets[f])
      solved[f]={'size':depth,'gates':ng,'edges':targets[f],'good':ok,'owned':owns}
     nf=tuple(sorted((*fs,f)))
     if nf not in nxt:nxt[nf]=ng
  sizes.append(len(nxt))
  print(json.dumps({'n':n,'depth':depth,'states':len(nxt),'solved':len(solved),'targets':len(targets),'elapsed':time.monotonic()-t0}),flush=True)
  states=nxt
  if len(solved)==len(targets):break
 result={'n':n,'targets':len(targets),'solved':len(solved),'state_counts':sizes,'solutions':list(solved.values()),'seconds':time.monotonic()-t0}
 return result
if __name__=='__main__':
 result=[run(n,4) for n in range(1,5)]
 Path('/tmp/oec/pequalnp-pilot-55/counterexample-small-results.json').write_text(json.dumps(result,indent=2))
 print(json.dumps({'bad_first_witnesses':[(r['n'],s) for r in result for s in r['solutions'] if not s['good']]}))
