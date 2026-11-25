from pathlib import Path
from itertools import combinations
import runpy,subprocess,json,time,argparse
BASE=Path('/tmp/oec/pequalnp-pilot-74');CNF=runpy.run_path(str(BASE/'star-sat.py'))['CNF']
SOLVER=str(BASE/'toolchain/bin/cadical')
def and_synth(n,edges,k,label,seconds=60):
 cn=CNF()
 samples=set((1<<a)|(1<<b) for a,b in edges)
 for x in range(1<<n):
  if any(x>>a&1 and x>>b&1 for a,b in edges):continue
  if all(any(((x|(1<<j))>>a&1) and ((x|(1<<j))>>b&1) for a,b in edges) for j in range(n) if not x>>j&1):samples.add(x)
 samples=sorted(samples)
 sels=[[[cn.var() for _ in range(n+i)] for _ in range(2)] for i in range(k)]
 val=[{x:cn.var() for x in samples} for _ in range(k)]
 outs=[cn.var() for _ in range(k)]
 def make_or(inputs):
  if not inputs:return False
  if len(inputs)==1:return inputs[0]
  z=cn.var()
  for t in inputs:cn.clause(-t,z)
  cn.clause(-z,*inputs)
  return z
 def make_and(a,b):
  if a is False or b is False:return False
  if a is True:return b
  if b is True:return a
  z=cn.var();cn.clause(-z,a);cn.clause(-z,b);cn.clause(z,-a,-b);return z
 for i in range(k):
  for side in range(2):cn.clause(*sels[i][side])
  for x in samples:
   sidevals=[]
   for side in range(2):
    ts=[]
    for w,sel in enumerate(sels[i][side]):
     if w<n:
      if x>>w&1:ts.append(sel)
     else:ts.append(make_and(sel,val[w-n][x]))
    sidevals.append(make_or(ts))
   a,b=sidevals;z=val[i][x]
   cn.clause(-z,a);cn.clause(-z,b);cn.clause(z,cn.neg(a),cn.neg(b))
 for x in samples:
  o=make_or([make_and(sel,val[i][x]) for i,sel in enumerate(outs)])
  if any(x>>a&1 and x>>b&1 for a,b in edges):cn.clause(o)
  else:cn.clause(cn.neg(o))
 p=BASE/(label+'.cnf');cn.emit(p)
 start=time.monotonic()
 with (BASE/(label+'.stdout')).open('w') as f,(BASE/(label+'.stderr')).open('w') as e:r=subprocess.run([SOLVER,'-q','-t',str(seconds),str(p)],stdout=f,stderr=e)
 result={'n':n,'edges':edges,'and_budget':k,'status':{10:'SAT',20:'UNSAT'}.get(r.returncode,'UNKNOWN'),'seconds':round(time.monotonic()-start,3),'variables':cn.nv,'clauses':len(cn.cls),'samples':len(samples)}
 if r.returncode==10:
  model={int(x) for line in (BASE/(label+'.stdout')).read_text().splitlines() if line.startswith('v ') for x in line.split()[1:] if int(x)>0}
  sets=[[[w for w,sel in enumerate(side) if sel in model] for side in ss] for ss in sels]
  output=[i for i,sel in enumerate(outs) if sel in model]
  result['and_operands']=sets;result['output_ands']=output
  for x in range(1<<n):
   wires=[bool(x>>j&1) for j in range(n)]
   for a,b in sets:wires.append(any(wires[w] for w in a) and any(wires[w] for w in b))
   got=any(wires[n+i] for i in output)
   assert got==any(x>>a&1 and x>>b&1 for a,b in edges),(x,got)
 return result
if __name__=='__main__':
 pa=argparse.ArgumentParser();pa.add_argument('--seconds',type=int,default=60);args=pa.parse_args()
 examples=[(5,[(i,(i+1)%5) for i in range(5)],2,'cycle5'),(6,[(i,(i+1)%6) for i in range(6)],2,'cycle6'),(11,[(i,(i+1)%11) for i in range(11)],5,'cycle11'),(10,[(i,(i+1)%5) for i in range(5)]+[(i,i+5) for i in range(5)]+[(i+5,5+(i+2)%5) for i in range(5)],5,'petersen')]
 results=[]
 for n,es,k,name in examples:
  r=and_synth(n,es,k,'star-and-'+name,seconds=args.seconds);results.append(r)
  print(json.dumps(r),flush=True)
  (BASE/'star-and-results.json').write_text(json.dumps(results,indent=2))
