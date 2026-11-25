import sys,json,argparse
from pathlib import Path
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-109/counterexample/z3-5.3.3-x64-glibc-2.39/bin/python')
import z3
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
MASK=(1<<1024)-1
INPUT=[sum(((x>>j)&1)<<x for x in range(1024)) for j in range(10)]
TARGET=sum(int(any((x>>i)&1 and (x>>j)&1 for i,j in E))<<x for x in range(1024))
def read_aig(path):
 data=Path(path).read_bytes(); p=data.index(b'\n'); head=data[:p].decode().split();p+=1
 assert head[0]=='aig',head
 M,I,L,O,A=map(int,head[1:6]);assert I==10 and L==0 and O==1,(M,I,L,O,A)
 end=data.index(b'\n',p);out=int(data[p:end]);p=end+1
 def number():
  nonlocal p
  value=0;shift=0
  while True:
   b=data[p];p+=1;value|=(b&127)<<shift
   if b<128:return value
   shift+=7
 gates=[]
 for i in range(A):
  lhs=2*(I+i+1);a=lhs-number();b=a-number();gates.append((a,b))
 assert M==I+A
 return I,gates,out

def optimize(path):
 I,aig,out=read_aig(path);n=I+len(aig)
 phases=[z3.BoolVal(False) for i in range(I+1)]+[z3.Bool('p%d'%i) for i in range(I+1,n+1)]
 needs=[[] for _ in range(n+1)]
 for i,(a,b) in enumerate(aig,I+1):
  for lit in (a,b):needs[lit//2].append(z3.Xor(z3.Xor(z3.BoolVal(bool(lit&1)),phases[i]),phases[lit//2]))
 needs[out//2].append(z3.Xor(z3.BoolVal(bool(out&1)),phases[out//2]))
 s=z3.Optimize();count=z3.Sum([z3.If(z3.Or(*v),1,0) for v in needs if v]);s.minimize(count)
 assert s.check()==z3.sat
 model=s.model();p=[z3.is_true(model.eval(t,model_completion=True)) for t in phases]
 gs=[];wire={i:i-1 for i in range(1,I+1)};wire[0]=99999;neg={}
 def value(source,phase):
  if bool(phase)==p[source]:return wire[source]
  if source not in neg:
   neg[source]=I+len(gs);gs.append([2,wire[source],wire[source]])
  return neg[source]
 for i,(a,b) in enumerate(aig,I+1):
  va=value(a//2,(a&1)^p[i]);vb=value(b//2,(b&1)^p[i]);wire[i]=I+len(gs)
  gs.append([1 if p[i] else 0,va,vb])
 output=value(out//2,out&1)
 w=INPUT.copy()
 for op,a,b in gs:
  va=w[a] if a<len(w) else 0;vb=w[b] if b<len(w) else 0
  w.append(va&vb if op==0 else va|vb if op==1 else MASK^va)
 actual=w[output] if output<len(w) else 0
 assert actual==TARGET,('mismatch',path,(actual^TARGET).bit_count())
 return {'binary':len(aig),'nots':sum(op==2 for op,a,b in gs),'size':len(gs),'output':output,'gates':gs,'phase':p,'errors':0}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('aig');p.add_argument('--save');a=p.parse_args()
 d=optimize(a.aig);print(json.dumps(d))
 if a.save:Path(a.save).write_text(json.dumps(d)+'\n')
