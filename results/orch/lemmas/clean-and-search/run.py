from pathlib import Path
import subprocess,json,time
root=Path('/tmp/oec/pequalnp-pilot-184/clean-and-search');cases=json.loads((root/'cases.json').read_text());results=[]
def solve(c,s,mode):
 name=c['name']+'-'+str(s)+'-'+mode;cnf=root/(name+'.cnf');out=root/(name+'.stdout');err=root/(name+'.stderr')
 with (root/(name+'.gen.stdout')).open('w') as o,(root/(name+'.gen.stderr')).open('w') as e:
  subprocess.run(['python3',str(root/'gen.py'),str(c['n']),str(s),str(root/(c['name']+'.edges.json')),str(cnf),mode],stdout=o,stderr=e,check=True)
 start=time.monotonic();peak=0;stopped=False
 with out.open('w') as o,err.open('w') as e:
  p=subprocess.Popen(['/tmp/oec/pequalnp-pilot-184/replacement/cadical/build/cadical','--unsat','-t','45',str(cnf)],stdout=o,stderr=e)
  while p.poll() is None:
   q=subprocess.run(['ps','-o','rss=','-p',str(p.pid)],text=True,capture_output=True)
   rss=int(q.stdout.strip() or 0);peak=max(peak,rss)
   if rss>300*1024:p.terminate();stopped=True
   time.sleep(.25)
 text=out.read_text();status=[l for l in text.splitlines() if l.startswith('s ') or l=='c UNKNOWN']
 r={'graph':c['name'],'gates':s,'mode':mode,'exit':p.returncode,'status':status,'seconds':time.monotonic()-start,'peak_KiB':peak,'memory_stopped':stopped}
 if p.returncode==10:
  M={int(v) for l in text.splitlines() if l.startswith('v ') for v in l.split()[1:] if int(v)>0}
  n=c['n'];A=(1<<n)+n+s+2;ix=lambda kd,j,a:(kd*(s+1)+j)*A+a+1
  gates=[]
  for j in range(s):
   op=next(d for d in range(3) if ix(0,j,d) in M)
   a=next(k for k in range(n+j+1) if ix(1,j,k) in M);b=next(k for k in range(n+j+1) if ix(2,j,k) in M)
   gates.append((op,a,b))
  errors=[];unsafe=[]
  for x in range(1<<n):
   f=any((x>>a&1) and (x>>b&1) for a,b in c['edges']);w=[bool(x>>i&1) for i in range(n)]
   for j,(op,a,b) in enumerate(gates):
    va=w[a] if a<len(w) else False;vb=w[b] if b<len(w) else False
    w.append((va and vb) if op==0 else (va or vb) if op==1 else True)
    if op in (0,2) and w[-1] and not f:unsafe.append((x,j))
   if w[-1]!=bool(f):errors.append(x)
  r.update({'witness':gates,'truth_errors':errors,'unsafe_ANDs':unsafe})
  assert not errors
  if mode=='safe':assert not unsafe
 results.append(r);(root/'results.json').write_text(json.dumps(results,indent=2));print(r,flush=True)
 return r
for c in cases:
 s=c['upper_bound']-1
 ordinary=solve(c,s,'ordinary')
 if ordinary['exit']==20:continue
 safe=solve(c,s,'safe')
 if ordinary['exit']==10 and safe['exit']==20:
  print('NUMERICAL_COUNTEREXAMPLE_CANDIDATE',c['name'],s,flush=True);break
