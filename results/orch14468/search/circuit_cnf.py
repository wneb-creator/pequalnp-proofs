#!/usr/bin/env python3
"""Exact finite strict circuit synthesis; every SAT model checked on all256 rows."""
import argparse,hashlib,itertools,json,pathlib,subprocess,time
from datetime import datetime,timezone
E=[(0,4),(1,5),(0,6),(2,6),(0,7),(1,7),(2,7),(3,7),(5,7)]
SOLVER='/tmp/oec/pequalnp-pilot-103/setup/lean-4.36.0-linux/bin/cadical'
class CNF:
 def __init__(self):self.n=0;self.cs=[]
 def var(self):self.n+=1;return self.n
 def add(self,*c):self.cs.append(c)
 def one(self,vs):
  self.add(*vs)
  for a,b in itertools.combinations(vs,2):self.add(-a,-b)
 def write(self,p):p.write_text(f'p cnf {self.n} {len(self.cs)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in self.cs))
def target(x):return any(x>>u&1 and x>>v&1 for u,v in E)
def evaluate(gates,x):
 w=[bool(x>>v&1)for v in range(8)]
 for op,a,b in gates:w.append((w[a]and w[b])if op==0 else(w[a]or w[b])if op==1 else not w[a])
 return w[-1]
def build(N,rows,nots,pin=None,not_position=None,first=None,allow_unused=False):
 c=CNF();A=[];B=[];O=[];vals=[]
 for i in range(N):
  A.append([c.var()for _ in range(8+i)]);B.append([c.var()for _ in range(8+i)]);O.append([c.var()for _ in range(3)])
  c.one(A[-1]);c.one(B[-1]);c.one(O[-1])
  for a in range(8+i):
   for b in range(a):c.add(-A[i][a],-B[i][b])
   c.add(-O[i][2],-A[i][a],B[i][a]);c.add(-O[i][2],A[i][a],-B[i][a])
 if nots==0:
  for os in O:c.add(-os[2])
 elif nots==1:c.one([os[2]for os in O])
 else:raise ValueError('nots must be0or1')
 if not_position is not None:c.add(O[not_position][2])
 if not allow_unused:
  for i in range(N-1):c.add(*(v for j in range(i+1,N)for v in(A[j][8+i],B[j][8+i])))
 for src in range(8):c.add(*(v for i in range(N)for v in(A[i][src],B[i][src])))
 if first is not None:
  op,a,b=first
  if op==2:b=a
  a,b=sorted((a,b));c.add(O[0][op]);c.add(A[0][a]);c.add(B[0][b])
 if pin:
  assert len(pin)==N
  for i,(op,a,b)in enumerate(pin):
   if op==2:b=a
   a,b=sorted((a,b));assert b<8+i
   c.add(O[i][op]);c.add(A[i][a]);c.add(B[i][b])
 for x in rows:
  values=[]
  for i in range(N):
   u,v,w=c.var(),c.var(),c.var()
   for src in range(8+i):
    for sels,d in[(A[i],u),(B[i],v)]:
     if src<8:c.add(-sels[src],d if x>>src&1 else-d)
     else:r=values[src-8];c.add(-sels[src],-d,r);c.add(-sels[src],d,-r)
   aa,oo,nn=O[i]
   c.add(-aa,-u,-v,w);c.add(-aa,u,-w);c.add(-aa,v,-w)
   c.add(-oo,u,v,-w);c.add(-oo,-u,w);c.add(-oo,-v,w)
   c.add(-nn,u,w);c.add(-nn,-u,-w)
   values.append(w)
  c.add(values[-1]if target(x)else-values[-1])
  vals.append(values)
 return c,A,B,O
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--gates',type=int,default=10);ap.add_argument('--nots',type=int,default=1);ap.add_argument('--seconds',type=int,default=120);ap.add_argument('--output',required=True);ap.add_argument('--pin');ap.add_argument('--not-position',type=int);ap.add_argument('--first');ap.add_argument('--cegis',action='store_true');ap.add_argument('--allow-unused',action='store_true');ap.add_argument('--encode-only',action='store_true');a=ap.parse_args()
 out=pathlib.Path(a.output);out.parent.mkdir(parents=True,exist_ok=True)
 pin=json.loads(pathlib.Path(a.pin).read_text())if a.pin else None
 if isinstance(pin,dict):pin=pin['gates']
 first=tuple(map(int,a.first.split(',')))if a.first else None
 rows=set(range(256))
 if a.cegis:rows={x for x in range(256)if x.bit_count()<=2 or x.bit_count()>=7 or(not target(x)and all(target(x|(1<<v))for v in range(8)if not x>>v&1))}
 started=time.time();deadline=started+a.seconds;records=[]
 for stage in range(256):
  stem=out.with_name(out.name+f'-stage{stage}');c,A,B,O=build(a.gates,sorted(rows),a.nots,pin,a.not_position,first,a.allow_unused);cnf=stem.with_suffix('.cnf');c.write(cnf)
  metadata={'n':8,'edges':E,'gates':a.gates,'nots':a.nots,'rows':sorted(rows),'first':first,'not_position':a.not_position,'strict_earlier_wires':True,'all_internal_used':not a.allow_unused,'all_primary_used':True,'constant_sources':False,'A':A,'B':B,'O':O,'cnf_sha256':hashlib.sha256(cnf.read_bytes()).hexdigest()}
  stem.with_suffix('.json').write_text(json.dumps(metadata,separators=(',',':'))+'\n')
  record={'stage':stage,'variables':c.n,'clauses':len(c.cs),'rows':len(rows),'cnf_sha256':metadata['cnf_sha256'],'started_utc':datetime.now(timezone.utc).isoformat()};print(json.dumps(record),flush=True)
  if a.encode_only:break
  remaining=max(1,int(deadline-time.time()))
  with stem.with_suffix('.stdout').open('w')as stdout,stem.with_suffix('.stderr').open('w')as stderr:
   run=subprocess.run([SOLVER,'--lrat','--no-binary','-t',str(remaining),str(cnf),str(stem.with_suffix('.lrat'))],stdout=stdout,stderr=stderr)
  record['exit_code']=run.returncode;record['verdict']={10:'SAT',20:'UNSAT',0:'UNKNOWN'}.get(run.returncode,'ERROR');records.append(record)
  if run.returncode==10:
   text=stem.with_suffix('.stdout').read_text();model={int(v)for l in text.splitlines()if l.startswith('v ')for v in l.split()[1:]if int(v)>0}
   gates=[(next(j for j,v in enumerate(O[i])if v in model),next(j for j,v in enumerate(A[i])if v in model),next(j for j,v in enumerate(B[i])if v in model))for i in range(a.gates)]
   bad=[x for x in range(256)if evaluate(gates,x)!=bool(target(x))];record['gates_model']=gates;record['bad_rows']=bad
   if not bad:
    out.with_suffix('.witness.json').write_text(json.dumps({'n':8,'gates':gates,'output':8+a.gates-1,'all256_checked':True},indent=2)+'\n');record['verdict']='VERIFIED_SAT'
   elif not a.cegis:raise AssertionError('complete truth encoding failed')
   else:rows.update(bad[:32])
  out.with_suffix('.results.json').write_text(json.dumps({'arguments':vars(a),'records':records,'elapsed_seconds':time.time()-started},indent=2)+'\n');print(json.dumps(record),flush=True)
  if run.returncode!=10 or not record.get('bad_rows')or time.time()>=deadline:break
if __name__=='__main__':main()
