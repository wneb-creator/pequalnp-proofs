#!/usr/bin/env python3
import argparse,json,itertools,subprocess,sys,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('directory');p.add_argument('--case',default='not');p.add_argument('--limit',type=int,default=240);p.add_argument('--rounds',type=int,default=8);a=p.parse_args()
base=Path(a.directory);base.mkdir(parents=True,exist_ok=True)
n,s=10,19;R=1<<n;A=R+n+s+2
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
solver='/tmp/oec/pequalnp-pilot-101/toolchain/lean-4.36.0-linux/bin/cadical'
def g(r):return any(r>>u&1 and r>>v&1 for u,v in edges)
def ix(kd,j,k):return (kd*(s+1)+j)*A+k+1
def lit(v,b):return v if b else -v
def truth_clauses(rows):
 F=[]
 for sd in (1,2):
  for j in range(s):
   for r in rows:
    for k in range(n+j+1):
     if k<n:F.append([-ix(sd,j,k),lit(ix(sd+3,j,r),r>>k&1)])
     elif k<n+j:
      F.extend([[-ix(sd,j,k),-ix(sd+3,j,r),ix(3,k-n,r)],[-ix(sd,j,k),ix(sd+3,j,r),-ix(3,k-n,r)]])
     else:F.append([-ix(sd,j,k),-ix(sd+3,j,r)])
 for j in range(s):
  for r in rows:
   o0,o1,o2,o3=(ix(0,j,k) for k in range(4));w,u,v=(ix(k,j,r) for k in (3,4,5))
   F.extend([[-o0,-w,u],[-o0,-w,v],[-o0,w,-u,-v],[-o1,w,-u],[-o1,w,-v],[-o1,-w,u,v],[-o2,w],[-o3,w,u],[-o3,-w,-u]])
 for r in rows:
  for k in range(n+s+1):
   if k<n:
    if bool(r>>k&1)!=g(r):F.append([-ix(6,0,k)])
   elif k<n+s:F.append([-ix(6,0,k),lit(ix(3,k-n,r),g(r))])
   elif g(r):F.append([-ix(6,0,k)])
 return F
reference=Path('/tmp/oec/pequalnp-pilot-101/counterexample/petersen19rows.cnf')
clauses=[]
for line in reference.read_text().splitlines():
 if line and line[0] not in 'cp':clauses.append([int(v) for v in line.split()[:-1]])
ops={'not':3,'and_edge':0,'and_nonedge':0,'or_edge':1,'or_nonedge':1}
second=0 if a.case=='not' else 2 if a.case.endswith('nonedge') else 1
clauses.extend([[ix(0,0,ops[a.case])],[ix(1,0,0)],[ix(2,0,second)],[ix(0,j,3) for j in range(s)]])
for j in range(s):
 for kd,count in [(0,4),(1,n+j+1),(2,n+j+1)]:
  clauses.extend([[-ix(kd,j,k),-ix(kd,j,l)] for k in range(count) for l in range(k)])
clauses.extend([[-ix(0,j,3) for j in js] for js in itertools.combinations(range(s),5)])
rows={r for r in range(R) if r.bit_count()<=3 or r.bit_count()>=9}
rows.update(r for r in range(R) if not g(r) and all(g(r|(1<<i)) for i in range(n) if not (r>>i&1)))
summary=[]
for round in range(a.rounds):
 cnf=base/f'{a.case}-{round}.cnf';log=base/f'{a.case}-{round}.log';sol=base/f'{a.case}-{round}.sol'
 F=clauses+truth_clauses(sorted(rows))
 with cnf.open('w') as f:
  f.write(f'p cnf {10*(s+1)*A} {len(F)}\n')
  for c in F:f.write(' '.join(map(str,c))+' 0\n')
 print('round',round,'rows',len(rows),'clauses',len(F),flush=True)
 started=time.monotonic()
 with log.open('w') as f:r=subprocess.run([solver,'-t',str(a.limit),'-w',str(sol),str(cnf)],stdout=f,stderr=subprocess.STDOUT)
 entry={'round':round,'rows':len(rows),'clauses':len(F),'exit':r.returncode,'seconds':time.monotonic()-started}
 if r.returncode!=10:
  summary.append(entry);print(entry,flush=True);break
 out=base/f'{a.case}-{round}.json'
 with (base/f'{a.case}-{round}-validation.log').open('w') as f:
  subprocess.run([sys.executable,'results/orch/lemmas/sat_validate.py',str(sol),'--output',str(out)],stdout=f,stderr=subprocess.STDOUT,check=True)
 decoded=json.loads(out.read_text());bad=decoded['bad_rows'];entry['bad_count']=len(bad);entry['not_count']=decoded['not_count'];summary.append(entry);print(entry,flush=True)
 if not bad:print('VALID COUNTEREXAMPLE',out,flush=True);break
 assert not(rows&set(bad)), 'encoding/decoding disagreement'
 rows.update(bad)
(base/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
