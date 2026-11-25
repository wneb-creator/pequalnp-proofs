from pathlib import Path
import importlib.util,itertools,json,sys
job=Path('/tmp/oec/pequalnp-pilot-79');chart=int(sys.argv[1]);degree=int(sys.argv[2]);assert chart in [2,3] and 4<=degree<=10
spec=importlib.util.spec_from_file_location('ng',job/'neogb-run-rational.py');ng=importlib.util.module_from_spec(spec);spec.loader.exec_module(ng)
names,prime,polys=ng.parse_input(job/('centered-two-coordinate-'+str(chart)+'-rational.msolve'));assert prime==0
assert all(c.denominator==1 for poly in polys for c in poly.values())
n=len(names)
def exact_mons(total,k):
 if k==1:yield(total,);return
 for a in range(total+1):
  for rest in exact_mons(total-a,k-1):yield(a,)+rest
mons=[m for d in range(degree,-1,-1) for m in exact_mons(d,n)];index={m:k for k,m in enumerate(mons)};rows=[];origins=[]
for i,p in enumerate(polys):
 dp=max(map(sum,p));multipliers=[m for d in range(degree-dp+1) for m in exact_mons(d,n)]
 for mult in multipliers:
  row=sorted((index[tuple(a+b for a,b in zip(m,mult))],int(c)) for m,c in p.items());rows.append(row);origins.append([i,list(mult)])
base='centered-two-macaulay-'+str(chart)+'-d'+str(degree)
with (job/(base+'.matrix')).open('w') as f:
 f.write(str(len(mons))+' '+str(len(rows))+'\n')
 for row in rows:f.write(str(len(row))+' '+' '.join(str(j)+' '+str(c) for j,c in row)+'\n')
(job/(base+'-metadata.json')).write_text(json.dumps({'classification':'CAS certificate search, not Lean checked','variables':names,'columns':mons,'row_origins':origins,'chart':chart,'degree':degree},separators=(',',':'))+'\n')
print(json.dumps({'chart':chart,'degree':degree,'rows':len(rows),'columns':len(mons),'nonzeros':sum(map(len,rows))}),flush=True)
