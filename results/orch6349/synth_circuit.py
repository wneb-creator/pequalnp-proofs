from pathlib import Path
import json,subprocess,time,os,sys
BASE=Path(__file__).resolve().parent
class CNF:
 def __init__(self):self.n=0;self.cs=[]
 def var(self):self.n+=1;return self.n
 def clause(self,*xs):
  if True in [x for x in xs if type(x)is bool]:return
  ys=[x for x in xs if type(x)is not bool]
  if any(-x in ys for x in ys):return
  self.cs.append(ys)
 def exactly(self,xs):
  self.clause(*xs)
  for i,x in enumerate(xs):
   for y in xs[:i]:self.clause(-x,-y)
def neg(x):return not x if type(x)is bool else -x
def encode(count,target):
 c=CNF();vals=[[bool((i<4 and row//4==i)or(i>=4 and row%4==i-4))for row in range(16)]for i in range(8)];gates=[]
 for j in range(count):
  width=8+j;sa=[c.var()for _ in range(width)];sb=[c.var()for _ in range(width)];c.exactly(sa);c.exactly(sb)
  for a in range(width):
   for b in range(a):c.clause(-sa[a],-sb[b])
  a=[c.var()for _ in range(16)];b=[c.var()for _ in range(16)];z=[c.var()for _ in range(16)];op=c.var()
  for selectors,vs in [(sa,a),(sb,b)]:
   for k,s in enumerate(selectors):
    for r in range(16):
     v=vals[k][r];c.clause(-s,-vs[r],v);c.clause(-s,vs[r],neg(v))
  for r in range(16):
   # op=false meansAND; op=true meansOR.
   c.clause(op,-z[r],a[r]);c.clause(op,-z[r],b[r]);c.clause(op,z[r],-a[r],-b[r])
   c.clause(-op,z[r],-a[r]);c.clause(-op,z[r],-b[r]);c.clause(-op,-z[r],a[r],b[r])
  vals.append(z);gates.append((sa,sb,op))
 for r in range(16):c.clause(vals[-1][r]if(target>>r)&1 else -vals[-1][r])
 # Each intermediate gate is used; any minimal circuit satisfies this restriction.
 for j in range(count-1):c.clause(*(s[8+j]for a,b,_ in gates[j+1:]for s in [a,b]))
 return c,gates
if __name__=='__main__':
 count=int(sys.argv[1]);target=5805;c,gates=encode(count,target);cnf=BASE/f'synth-{count}.cnf';log=BASE/f'synth-{count}.log'
 cnf.write_text(f'p cnf {c.n} {len(c.cs)}\n'+''.join(' '.join(map(str,row))+' 0\n'for row in c.cs))
 start=time.monotonic()
 with log.open('w')as out:
  p=subprocess.run(['/tmp/oec/pequalnp-pilot-61/lean-4.36.0-linux/bin/cadical',str(cnf)],stdout=out,stderr=subprocess.STDOUT)
 result={'gates':count,'target':target,'variables':c.n,'clauses':len(c.cs),'exitCode':p.returncode,'seconds':time.monotonic()-start,'interpretation':'Search encoding only; UNSAT is not a Lean lower-bound proof.'}
 if p.returncode==10:
  model={int(w)for line in log.read_text().splitlines()if line.startswith('v ')for w in line.split()[1:]if int(w)>0};decoded=[];values=[15,240,3840,61440,4369,8738,17476,34952]
  for sa,sb,op in gates:
   a=next(i for i,v in enumerate(sa)if v in model);b=next(i for i,v in enumerate(sb)if v in model);o='or'if op in model else'and';v=values[a]|values[b]if o=='or'else values[a]&values[b];values.append(v);decoded.append([o,a,b,v])
  assert values[-1]==target
  result['circuit']=decoded;result['output']=7+count
 (BASE/f'synth-{count}.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
