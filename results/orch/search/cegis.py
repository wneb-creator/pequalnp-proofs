import sys,json,subprocess,time,random
from pathlib import Path
solver,base,seconds,outdir=sys.argv[1:]
outdir=Path(outdir)
seconds=int(seconds)
n=10;s=19;R=1024;A=1055
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def truth(r):return any(r>>u&1 and r>>v&1 for u,v in E)
def ix(k,j,a):return (k*20+j)*A+a+1
def lit(v,b):return v if b else -v
def row_clauses(r):
 F=[]
 for sd in [1,2]:
  for j in range(s):
   for k in range(n+j+1):
    if k<n:F.append([-ix(sd,j,k),lit(ix(sd+3,j,r),bool(r>>k&1))])
    elif k<n+j:
     F.append([-ix(sd,j,k),-ix(sd+3,j,r),ix(3,k-n,r)])
     F.append([-ix(sd,j,k),ix(sd+3,j,r),-ix(3,k-n,r)])
    else:F.append([-ix(sd,j,k),-ix(sd+3,j,r)])
 for j in range(s):
  o0,o1,o2,o3=[ix(0,j,t) for t in range(4)]
  w,u,v=ix(3,j,r),ix(4,j,r),ix(5,j,r)
  F.extend([[-o0,-w,u],[-o0,-w,v],[-o0,w,-u,-v],[-o1,w,-u],[-o1,w,-v],[-o1,-w,u,v],[-o2,w],[-o3,w,u],[-o3,-w,-u]])
 for k in range(n+s+1):
  if k<n:
   if bool(r>>k&1)!=truth(r):F.append([-ix(6,0,k)])
  elif k<n+s:F.append([-ix(6,0,k),lit(ix(3,k-n,r),truth(r))])
  elif truth(r):F.append([-ix(6,0,k)])
 return F
def decode(log):
 vals=set()
 for l in log.read_text().splitlines():
  if l.startswith('v '):vals.update(int(x) for x in l.split()[1:] if int(x)>0)
 gates=[]
 for j in range(s):
  op=next(t for t in range(4) if ix(0,j,t) in vals)
  a=next(t for t in range(n+j+1) if ix(1,j,t) in vals)
  b=next(t for t in range(n+j+1) if ix(2,j,t) in vals)
  gates.append([op,a,b])
 out=next(t for t in range(n+s+1) if ix(6,0,t) in vals)
 bad=[]
 for r in range(R):
  w=[bool(r>>i&1) for i in range(n)]
  for op,a,b in gates:
   u=w[a] if a<len(w) else False;v=w[b] if b<len(w) else False
   w.append(u and v if op==0 else u or v if op==1 else True if op==2 else not u)
  if (w[out] if out<len(w) else False)!=truth(r):bad.append(r)
 return {'gates':gates,'output':out,'bad_rows':bad}
start=time.monotonic();lines=Path(base).read_text().splitlines();nv=int(lines[0].split()[2]);clause_lines=lines[1:]
added=set()
extra=[]
for r in [0,1023]+[1<<i for i in range(10)]+[1023^(1<<i) for i in range(10)]:
 added.add(r);extra.extend(row_clauses(r))
for run in range(100):
 remaining=int(seconds-(time.monotonic()-start))
 if remaining<1:break
 cnf=outdir/f'cegis-{run}.cnf';log=outdir/f'cegis-{run}.log'
 with cnf.open('w') as f:
  f.write(f'p cnf {nv} {len(clause_lines)+len(extra)}\n')
  f.write('\n'.join(clause_lines)+'\n')
  for c in extra:f.write(' '.join(map(str,c))+' 0\n')
 with log.open('w') as f:
  p=subprocess.run([solver,'-t',str(min(120,remaining)),'--sat','--seed=99',str(cnf)],stdout=f,stderr=subprocess.STDOUT)
 print('iteration',run,'extra rows',len(added),'exit',p.returncode,'elapsed',time.monotonic()-start,flush=True)
 if p.returncode!=10:break
 d=decode(log)
 (outdir/f'cegis-{run}-model.json').write_text(json.dumps(d,indent=2))
 print('errors',len(d['bad_rows']),flush=True)
 if not d['bad_rows']:
  print('FOUND',json.dumps(d),flush=True);break
 assert not (added&set(d['bad_rows']))
 bad=sorted(d['bad_rows'],key=lambda r:(r.bit_count(),r))
 for r in bad[:10]+bad[-10:]:
  if r not in added:added.add(r);extra.extend(row_clauses(r))
