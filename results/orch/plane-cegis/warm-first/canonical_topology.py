import argparse,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--data',required=True);p.add_argument('--gates',required=True);p.add_argument('--output',required=True);a=p.parse_args()
d=json.loads(Path(a.data).read_text());g=json.loads(Path(a.gates).read_text());n=d['n'];size=len(g)
assert size>0
for j,(op,u,v) in enumerate(g):assert op in (0,1) and 0<=u<n+j and 0<=v<n+j
live={n+size-1}
for j in reversed(range(size)):
 if n+j in live:live.update(g[j][1:])
assert all(n+j in live for j in range(size))
renaming={i:i for i in range(n)};todo=set(range(size));out=[]
while todo:
 choices=[]
 for j in todo:
  op,u,v=g[j]
  if u in renaming and v in renaming:
   u,v=sorted((renaming[u],renaming[v]));op=1 if u==v else op
   choices.append(((u,v,op,j),[op,u,v]))
 assert choices
 key,gate=min(choices);old=key[-1];renaming[n+old]=n+len(out);out.append(gate);todo.remove(old)
assert renaming[n+size-1]==n+size-1
for j in range(size-1):
 if n+j not in out[j+1][1:]:
  op,u,v=out[j];oo,uu,vv=out[j+1];assert (u,v,op)<=(uu,vv,oo)
def evaluate(gs,r):
 v=[bool(r&(1<<i)) for i in range(n)]
 for op,x,y in gs:v.append(v[x] or v[y] if op else v[x] and v[y])
 return v[-1]
assert all(evaluate(g,r)==evaluate(out,r) for r in d['rows'])
Path(a.output).write_text(json.dumps(out)+'\n')
print(json.dumps({'gates':size,'rows_checked':len(d['rows']),'status':'topological relabeling preserves all checked rows; every adjacent independent pair sorted'}))
