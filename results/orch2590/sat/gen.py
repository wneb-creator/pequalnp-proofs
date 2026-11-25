#!/usr/bin/env python3
"""Finite AO2 synthesis on explicitly supplied truth-table rows.

Search artifact only: no unproved normalization is advertised as a Lean result.
Leading padding gates are OR(0,0); active gates have ordered distinct sources.
Optional boundary-row incomparability is justified for monotone target boundary
sets by choosing a minimum correct AO2 circuit before adding the leading pads.
"""
import argparse
import json
from pathlib import Path

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('data',type=Path)
p.add_argument('size',type=int)
p.add_argument('output',type=Path)
p.add_argument('--incomparable',action='store_true')
p.add_argument('--lex',action='store_true')
p.add_argument('--first-symmetry',choices=['petersen','fano'])
p.add_argument('--first-op',choices=['and','or'])
p.add_argument('--first-second',type=int)
p.add_argument('--essential-boundaries',action='store_true')
p.add_argument('--formula-read2',action='store_true')
p.add_argument('--require-nonread1',action='store_true')
p.add_argument('--min-active',type=int,default=0)
a=p.parse_args()
d=json.loads(a.data.read_text()); n=d['n']; s=a.size; rows=d['rows']; edges=d['edges']
F=[]; nv=0
def new():
 global nv
 nv+=1;return nv
def clause(*x):F.append(list(x))
def alo(v):F.append(v)
def onehot(v):
 alo(v)
 for i,x in enumerate(v):
  for y in v[:i]:clause(-x,-y)
op=[new() for j in range(s)]
pad=[new() for j in range(s)]
src=[[[new() for k in range(n+j)] for side in range(2)] for j in range(s)]
val=[[new() for r in rows] for j in range(s)]
arg=[[[new() for r in rows] for side in range(2)] for j in range(s)]
for j in range(s):
 for side in range(2):
  onehot(src[j][side])
  clause(-pad[j],src[j][side][0])
  for k in range(n+j):
   sel=src[j][side][k]
   for ri,r in enumerate(rows):
    v=arg[j][side][ri]
    if k<n:clause(-sel,v if r>>k&1 else -v)
    else:
     w=val[k-n][ri]
     clause(-sel,-v,w);clause(-sel,v,-w)
 clause(-pad[j],op[j])
 for u in range(n+j):
  for v in range(u+1):clause(pad[j],-src[j][0][u],-src[j][1][v])
 if j:clause(-pad[j],pad[j-1])
 for i in range(j):
  for side in range(2):clause(-pad[i],-src[j][side][n+i])
 for ri,r in enumerate(rows):
  w=val[j][ri];x=arg[j][0][ri];y=arg[j][1][ri];o=op[j]
  clause(o,-w,x);clause(o,-w,y);clause(o,w,-x,-y)
  clause(-o,w,-x);clause(-o,w,-y);clause(-o,-w,x,y)
 if j+1<s:
  alo([pad[j]]+[src[k][side][n+j] for k in range(j+1,s) for side in range(2)])
 if a.incomparable:
  for pos in (0,1):
   ws=[]
   for ri in range(len(rows)):
    w=new();ws.append(w);x=arg[j][0][ri];y=arg[j][1][ri]
    clause(-w,x if pos==0 else -x)
    clause(-w,-y if pos==0 else y)
   alo([pad[j]]+ws)
 if a.essential_boundaries:
  # A minimum monotone circuit cannot have a wire false at all minimal-true
  # rows or true at all maximal-false rows: clamp it and propagate constants.
  pos=[ri for ri,r in enumerate(rows) if any(r>>u&1 and r>>v&1 for u,v in edges)]
  neg=[ri for ri in range(len(rows)) if ri not in pos]
  alo([pad[j]]+[val[j][ri] for ri in pos])
  alo([pad[j]]+[-val[j][ri] for ri in neg])
 if a.first_symmetry:
  # Petersen has two unordered pair orbits: edge {0,1}, nonedge {0,2}.
  # Fano incidence has representatives {0,1}, {0,7}, {0,8}.
  first=[pad[j]]+([-pad[j-1]] if j else [])
  clause(*first,src[j][0][0])
  reps=(1,2) if a.first_symmetry=='petersen' else (1,7,8)
  alo(first+[src[j][1][k] for k in reps])
  if a.first_op:clause(*first,op[j] if a.first_op=='or' else -op[j])
  if a.first_second is not None:clause(*first,src[j][1][a.first_second])
 if a.lex and j:
  escape=[pad[j-1],src[j][0][n+j-1],src[j][1][n+j-1]]
  for u in range(n+j-1):
   for v in range(u):clause(*escape,-src[j-1][0][u],-src[j][0][v])
   for v in range(u+1,n+j-1):
    for w in range(u+1,v):clause(*escape,-src[j-1][0][u],-src[j][0][u],-src[j-1][1][v],-src[j][1][w])
    clause(*escape,-src[j-1][0][u],-src[j][0][u],-src[j-1][1][v],-src[j][1][v],op[j-1],-op[j])
clause(-pad[-1])
if a.min_active:
 assert 0<a.min_active<=s
 clause(-pad[s-a.min_active])
if a.require_nonread1:
 # Degree-one flags are OR-reachable leaves, NOT singleton evaluations.
 # Degree-two flags are exact clean two-leaf proof monomials for graph edges.
 nf=n+len(edges)
 feat=[[new() for k in range(nf)] for j in range(s)]
 inp=[[[new() for k in range(nf)] for side in range(2)] for j in range(s)]
 for j in range(s):
  for side in range(2):
   for k in range(n+j):
    sel=src[j][side][k]
    for f in range(nf):
     x=inp[j][side][f]
     if k<n:clause(-sel,x if f==k else -x)
     else:
      y=feat[k-n][f]
      clause(-sel,-x,y);clause(-sel,x,-y)
  for f in range(nf):
   z=feat[j][f];x=inp[j][0][f];y=inp[j][1][f];o=op[j]
   clause(-o,-x,z);clause(-o,-y,z);clause(-o,x,y,-z)
   if f<n:clause(o,-z)
   else:
    u,v=edges[f-n];t1,t2=new(),new()
    for t,aa,bb in [(t1,inp[j][0][u],inp[j][1][v]),(t2,inp[j][0][v],inp[j][1][u])]:
     clause(-t,aa);clause(-t,bb);clause(t,-aa,-bb)
    clause(o,-t1,z);clause(o,-t2,z);clause(o,t1,t2,-z)
 alo([-feat[-1][n+k] for k in range(len(edges))])
if a.formula_read2:
 for v in pad:clause(-v)
 for k in range(n):
  # Exact-two sequential cardinality counter: p1/p2 are exact thresholds.
  p1,p2=new(),new();clause(-p1);clause(-p2)
  for x in [src[j][side][k] for j in range(s) for side in range(2)]:
   q1,q2=new(),new()
   clause(-p1,q1);clause(-x,q1);clause(-q1,p1,x)
   clause(-p2,q2);clause(-x,-p1,q2)
   clause(-q2,p2,x);clause(-q2,p2,p1)
   clause(-x,-p2)
   p1,p2=q1,q2
  clause(p2)
 for i in range(s-1):
  onehot([src[j][side][n+i] for j in range(i+1,s) for side in range(2)])
for ri,r in enumerate(rows):
 target=any(r>>u&1 and r>>v&1 for u,v in edges)
 clause(val[-1][ri] if target else -val[-1][ri])
a.output.write_text(f'p cnf {nv} {len(F)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in F))
meta={'data':str(a.data),'size':s,'variables':nv,'clauses':len(F),'op':op,'pad':pad,'src':src,'val':val,'arg':arg,'options':vars(a)|{'data':str(a.data),'output':str(a.output)}}
a.output.with_suffix('.json').write_text(json.dumps(meta)+'\n')
print(json.dumps({'variables':nv,'clauses':len(F),'rows':len(rows),'size':s,'output':str(a.output)}))
