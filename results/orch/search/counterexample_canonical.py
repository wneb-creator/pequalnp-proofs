from counterexample_sparse_sat import synth,PETER,FANO
import z3,json,itertools
from pathlib import Path

def pair_reps(n,edges):
 E={frozenset(e) for e in edges};deg=[sum(i in e for e in edges) for i in range(n)];maps=[]
 def visit(p,unused):
  i=len(p)
  if i==n:maps.append(p);return
  for v in unused:
   if deg[i]!=deg[v]:continue
   if any((frozenset((i,j)) in E)!=(frozenset((v,p[j])) in E) for j in range(i)):continue
   visit(p+[v],unused-{v})
 visit([],set(range(n)));pairs=sorted(itertools.combinations(range(n),2),key=lambda p:(p[1],p[0]));reps=[];seen=set()
 for pair in pairs:
  if pair in seen:continue
  reps.append(pair)
  for perm in maps:seen.add(tuple(sorted((perm[pair[0]],perm[pair[1]]))))
 return reps,len(maps)

if __name__=='__main__':
 z3.set_param('memory_max_size',256)
 e=[(0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1)]
 for name,n,es,s,mode in [('theta233',7,e,10,'general'),('theta233',7,e,11,'unsound'),('Petersen',10,PETER,19,'general')]:
  reps,count=pair_reps(n,es);print(json.dumps({'name':name,'first_pair_reps':reps,'automorphisms':count}),flush=True)
  r=synth(n,es,s,mode,timeout=300000,dominance=True,maxorder=True,firstpairs=reps);r.update(name=name,dominance=True,maxorder=True,automorphisms=count,first_pair_reps=reps)
  with Path('/tmp/oec/pequalnp-pilot-55/counterexample-canonical-results.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(json.dumps(r),flush=True)
