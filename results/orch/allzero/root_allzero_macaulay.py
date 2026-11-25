from pathlib import Path
import importlib.util,json,sys,itertools
job=Path('/tmp/oec/pequalnp-pilot-79');degree=int(sys.argv[1]);assert 4<=degree<=10
spec=importlib.util.spec_from_file_location('ng',job/'neogb-run-rational.py');ng=importlib.util.module_from_spec(spec);spec.loader.exec_module(ng)
names,prime,polys=ng.parse_input(job/'fresh_top_allzero_0.msolve');assert prime==0 and names[-1]=='h' and len(names)==7
n=6
def exact(total,k):
 if k==1:
  yield (total,);return
 for a in range(total+1):
  for rest in exact(total-a,k-1):yield(a,)+rest
def reduce(poly):
 out={}
 for ex,co in poly.items():
  e=ex[:-1]+(ex[-1]%2,);out[e]=out.get(e,0)+co*24**(ex[-1]//2)
 return {e:int(c) for e,c in out.items() if c}
polys=[reduce(p) for p in polys]
mons=[m+(h,) for d in range(degree,-1,-1) for m in exact(d,n) for h in (1,0)]
index={m:k for k,m in enumerate(mons)};origin=[]
for i,p in enumerate(polys):
 if not p:continue
 dp=max(sum(m[:-1]) for m in p)
 for d in range(degree-dp+1):
  for m in exact(d,n):
   for h in (0,1):origin.append((dp+d,i,m+(h,)))
origin.sort(key=lambda q:(q[0],sum(q[2][:-1]),q[1],q[2]))
rows=[]
for _,i,m in origin:
 shifted=reduce({tuple(a+b for a,b in zip(e,m)):c for e,c in polys[i].items()})
 rows.append(sorted((index[e],c) for e,c in shifted.items()))
base='root-allzero-d'+str(degree)
with (job/(base+'.matrix')).open('w') as f:
 f.write(f'{len(mons)} {len(rows)}\n')
 for row in rows:f.write(str(len(row))+' '+' '.join(str(j)+' '+str(c) for j,c in row)+'\n')
(job/(base+'-metadata.json')).write_text(json.dumps({'classification':'Macaulay identity search modulo h^2=24; not Lean checked','variables':names,'columns':mons,'row_origins':[[i,m] for _,i,m in origin],'degree':degree,'original_input':'fresh_top_allzero_0.msolve'},separators=(',',':'))+'\n')
print(json.dumps({'degree':degree,'rows':len(rows),'columns':len(mons),'nnz':sum(map(len,rows))}),flush=True)
