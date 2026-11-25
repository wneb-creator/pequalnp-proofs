import argparse,itertools,json,subprocess,time
from pathlib import Path
N=14
E=[(0,8),(0,10),(1,7),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
NEI=[sum(1<<(b if a==v else a) for a,b in E if v in (a,b)) for v in range(N)]
MAX=(1<<N)-1
class CNF:
 def __init__(self):self.n=0;self.clauses=[]
 def var(self):self.n+=1;return self.n
 def add(self,*ls):self.clauses.append(tuple(ls))
 def conj(self,a,b):
  t=self.var();self.add(-t,a);self.add(-t,b);self.add(t,-a,-b);return t
 def union(self,ls):
  z=self.var();self.add(-z,*ls)
  for t in ls:self.add(-t,z)
  return z
 def write(self,p):
  with p.open('w') as f:
   f.write(f'p cnf {self.n} {len(self.clauses)}\n')
   for c in self.clauses:f.write(' '.join(map(str,c))+' 0\n')
def make(k,rows,strip=False):
 c=CNF();left=[];right=[]
 for j in range(k):
  left.append([c.var() for _ in range(N+j)])
  right.append([c.var() for _ in range(N+j)])
 if strip:
  for aa,bb in zip(left,right):
   for a,b in zip(aa[:N],bb[:N]):c.add(-a,-b)
 out=[c.var() for _ in range(k)]
 for x,target in rows:
  ws=[bool(x>>i&1) for i in range(N)]
  for j in range(k):
   sides=[]
   for sels in [left[j],right[j]]:
    terms=[]
    for sel,w in zip(sels,ws):
     if isinstance(w,bool):
      if w:terms.append(sel)
     else:terms.append(c.conj(sel,w))
    sides.append(c.union(terms))
   ws.append(c.conj(*sides))
  output=c.union([c.conj(sel,w) for sel,w in zip(out,ws[N:])])
  c.add(output if target else -output)
 return c,(left,right,out)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--gates',type=int,default=6);ap.add_argument('--seconds',type=int,default=300);ap.add_argument('--out',required=True);ap.add_argument('--solver',required=True);ap.add_argument('--strip',action='store_true');args=ap.parse_args()
 out=Path(args.out);out.mkdir(parents=True,exist_ok=True)
 mis=[x for x in range(1<<N) if all(not(x>>a&1 and x>>b&1) for a,b in E) and all(x>>v&1 or NEI[v]&x for v in range(N))]
 rows=[(x,False) for x in mis]+[((1<<a)|(1<<b),True) for a,b in E]
 print('maximal false rows',len(mis),'minimal true rows',len(E),flush=True)
 cnf,schema=make(args.gates,rows,args.strip)
 cnf.write(out/'model.cnf');(out/'schema.json').write_text(json.dumps(schema));(out/'rows.json').write_text(json.dumps(rows))
 print('CNF',cnf.n,'vars',len(cnf.clauses),'clauses',flush=True)
 with (out/'solver.log').open('w') as f:p=subprocess.run([args.solver,'-t',str(args.seconds),str(out/'model.cnf')],stdout=f,stderr=subprocess.STDOUT)
 print('solver exit',p.returncode,flush=True)
 if p.returncode!=10:return
 model={int(v) for l in (out/'solver.log').read_text().splitlines() if l.startswith('v ') for v in l[2:].split() if int(v)>0}
 left,right,outputs=schema
 gates=[([i for i,s in enumerate(a) if s in model],[i for i,s in enumerate(b) if s in model]) for a,b in zip(left,right)]
 og=[j for j,s in enumerate(outputs) if s in model]
 errors=[]
 for x in range(1<<N):
  vals=[bool(x>>i&1) for i in range(N)]
  for a,b in gates:vals.append(any(vals[i] for i in a) and any(vals[i] for i in b))
  actual=any(vals[N+j] for j in og);wanted=any(x>>a&1 and x>>b&1 for a,b in E)
  if actual!=wanted:errors.append(x)
 result={'gates':gates,'out':og,'errors':errors}
 (out/'candidate.json').write_text(json.dumps(result,indent=2))
 print(json.dumps(result),flush=True)
 assert not errors
if __name__=='__main__':main()
