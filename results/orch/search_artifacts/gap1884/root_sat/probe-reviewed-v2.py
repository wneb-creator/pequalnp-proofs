import argparse, itertools, json, pathlib, subprocess, time, datetime, signal
BASE=pathlib.Path(__file__).resolve().parent
SOLVER='/tmp/oec/pequalnp-pilot-99/lean-4.36.0-linux/bin/cadical'
STOP=BASE.parent/'STOP'
EDGES=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(r): return any((r>>a&1) and (r>>b&1) for a,b in EDGES)
def pin(r,i): return bool(r>>i&1) if i<10 else not bool(r&1)
def make(s,rows,limit=True):
 wd=1024+11+s+1
 def ix(k,j,a): return (k*(s+1)+j)*wd+a+1
 cs=[]
 for j in range(s):
  cs.append([ix(0,j,k) for k in range(4)])
  for e in (1,2):cs.append([ix(e,j,k) for k in range(11+j+1)])
 for j in range(s):
  for r in rows:
   for e in (1,2):
    val=ix(e+3,j,r)
    for k in range(11+j+1):
     sel=ix(e,j,k)
     if k<11:cs.append([-sel,val if pin(r,k) else -val])
     elif k<11+j:
      w=ix(3,k-11,r);cs.extend([[-sel,-val,w],[-sel,val,-w]])
     else:cs.append([-sel,-val])
   o=[ix(0,j,k) for k in range(4)];v=ix(3,j,r);a=ix(4,j,r);b=ix(5,j,r)
   cs.extend([[-o[0],-v,a],[-o[0],-v,b],[-o[0],v,-a,-b],[-o[1],v,-a],[-o[1],v,-b],[-o[1],-v,a,b],[-o[2],v],[-o[3],-v,-a],[-o[3],v,a]])
 cs.append([ix(6,0,k) for k in range(11+s+1)])
 for r in rows:
  for k in range(11+s+1):
   o=ix(6,0,k)
   if k<11:
    if pin(r,k)!=target(r):cs.append([-o])
   elif k<11+s:cs.append([-o,ix(3,k-11,r) if target(r) else -ix(3,k-11,r)])
   elif target(r):cs.append([-o])
 if limit:
  for j in range(s):
   for k in range(j):cs.append([-ix(0,j,3),-ix(0,k,3)])
 return cs,ix

def evaluate(gs,out,r):
 w=[pin(r,i) for i in range(11)]
 for op,a,b in gs:
  av=w[a] if a<len(w) else False; bv=w[b] if b<len(w) else False
  w.append(av and bv if op==0 else av or bv if op==1 else True if op==2 else not av)
 return w[out] if out<len(w) else False

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--gates',type=int,default=18);ap.add_argument('--name',required=True);ap.add_argument('--seconds',type=int,default=300);ap.add_argument('--full',action='store_true');ap.add_argument('--fix');ap.add_argument('--no-limit',action='store_true');ap.add_argument('--proof',action='store_true');ap.add_argument('--zero-not',action='store_true');ar=ap.parse_args()
 deadline=time.monotonic()+ar.seconds
 rows=list(range(1024)) if ar.full else sorted(set([r for r in range(1024) if not target(r)]+[(1<<a)|(1<<b) for a,b in EDGES]))
 if ar.zero_not and not ar.full:
  rows=[r for r in range(1024) if (target(r) and all(not target(r & ~(1<<i)) for i in range(1,10) if r>>i&1)) or (not target(r) and all(target(r | (1<<i)) for i in range(1,10) if not r>>i&1))]
 for iteration in range(5):
  if STOP.exists():return 75
  s=ar.gates;cs,ix=make(s,rows,not ar.no_limit)
  if ar.zero_not:
   cs.extend([[-ix(0,j,3)] for j in range(s)])
  if ar.fix:
   f=json.loads(pathlib.Path(ar.fix).read_text()); assert len(f['gates'])==s
   for j,(op,a,b) in enumerate(f['gates']):
    assert op in range(5) and a>=0 and b>=0
    a=min(a,11+j);b=min(b,11+j)
    if op==3: kind=2
    elif op==4:kind=1;a=b=11+j
    else:kind=3 if op==2 else op
    cs.extend([[ix(0,j,kind)],[ix(1,j,a)],[ix(2,j,b)]])
   assert f['output']>=0
   cs.append([ix(6,0,min(f['output'],11+s))])
  base=BASE/(ar.name+f'-{iteration}'); cnf=base.with_suffix('.cnf'); maximum=max(abs(v) for c in cs for v in c)
  with cnf.open('w') as f:
   f.write(f'p cnf {maximum} {len(cs)}\n')
   for c in cs:f.write(' '.join(map(str,c))+' 0\n')
  remaining=max(1,int(deadline-time.monotonic()))
  if time.monotonic()>=deadline:return 0
  cmd=[SOLVER,'-t',str(remaining),str(cnf)]
  if ar.proof:cmd=[SOLVER,'--lrat','--binary','-t',str(remaining),str(cnf),str(base.with_suffix('.lrat'))]
  record={'start':datetime.datetime.now(datetime.timezone.utc).isoformat(),'cmd':cmd,'rows':rows,'gates':s,'at_most_one_not':not ar.no_limit,'zero_not':ar.zero_not,'global_seconds':ar.seconds,'variables':maximum,'clauses':len(cs)}
  print(json.dumps({k:v for k,v in record.items() if k!='rows'}),flush=True)
  with base.with_suffix('.stdout').open('w') as o,base.with_suffix('.stderr').open('w') as e:
   p=subprocess.Popen(cmd,stdout=o,stderr=e)
   while p.poll() is None:
    if time.monotonic()>=deadline:p.send_signal(signal.SIGINT);record['global_timeout']=True;p.wait();break
    if STOP.exists():p.send_signal(signal.SIGINT);record['cancelled_by_stop']=True;p.wait();break
    time.sleep(0.5)
  record['exit_code']=p.returncode;record['end']=datetime.datetime.now(datetime.timezone.utc).isoformat();base.with_suffix('.record.json').write_text(json.dumps(record,indent=2)+'\n');print('SOLVER_EXIT',p.returncode,flush=True)
  if p.returncode!=10:return p.returncode
  m={int(v) for line in base.with_suffix('.stdout').read_text().splitlines() if line.startswith('v ') for v in line[2:].split() if int(v)>0}
  gs=[]
  for j in range(s):
   ks=[k for k in range(4) if ix(0,j,k) in m];op=3 if 3 in ks else ks[0]
   a=next(k for k in range(11+j+1) if ix(1,j,k) in m);b=next(k for k in range(11+j+1) if ix(2,j,k) in m);gs.append([op,a,b])
  out=next(k for k in range(11+s+1) if ix(6,0,k) in m)
  bad=[r for r in range(1024) if evaluate(gs,out,r)!=target(r)]
  result={'gates':gs,'output':out,'op_map':['and','or','true','not'],'bad':bad};base.with_suffix('.circuit.json').write_text(json.dumps(result,indent=2)+'\n');print('FULL_TRUTH_MISMATCHES',len(bad),flush=True)
  if not bad:return 10
  rows=sorted(set(rows+bad))
 return 0
if __name__=='__main__':raise SystemExit(main())
