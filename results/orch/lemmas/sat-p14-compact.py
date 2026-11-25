import argparse,itertools,json,subprocess,time
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-81')
CADICAL=str(BASE/'lean-4.36.0-linux/bin/cadical')
def neg(x):return not x if type(x)==bool else -x
class CNF:
 def __init__(self):self.n=0;self.cs=[]
 def var(self):self.n+=1;return self.n
 def add(self,*args):
  if any(x is True for x in args):return
  row=list(dict.fromkeys(x for x in args if x is not False))
  if any(-x in row for x in row):return
  self.cs.append(row)
 def conj(self,y,a,b):
  self.add(neg(a),neg(b),y);self.add(a,-y);self.add(b,-y)
 def disjunction(self,y,lits):
  self.add(-y,*lits)
  for x in lits:self.add(neg(x),y)
 def threshold(self,lits,k):
  if k<=0:return dict(literals=lits,threshold=k,cells=[],root=True)
  if k>len(lits):return dict(literals=lits,threshold=k,cells=[],root=False)
  previous=[True]+[False]*k;cells=[]
  for i,x in enumerate(lits,1):
   current=[True]+[False]*k
   for j in range(1,min(i,k)+1):
    a=previous[j];b=previous[j-1];z=self.var()
    self.add(neg(a),z);self.add(neg(b),neg(x),z);self.add(-z,a,b);self.add(-z,a,x)
    current[j]=z;cells.append(dict(prefix=i,threshold=j,var=z))
   previous=current
  return dict(literals=lits,threshold=k,cells=cells,root=previous[k])
 def write(self,path):
  with path.open('w') as f:
   f.write(f'p cnf {self.n} {len(self.cs)}\n')
   for row in self.cs:f.write(' '.join(map(str,row))+' 0\n')
def specification(graph):
 edges=[(p,7+l) for p in range(7) for l in range(7) if ((p-l)%7 in (0,1,3) if graph=='fano' else p==l)]
 hit=lambda m:any(m>>a&1 and m>>b&1 for a,b in edges)
 positive=[(1<<a)|(1<<b) for a,b in edges]
 negative=[m for m in range(1<<14) if not hit(m) and all(hit(m|1<<x) for x in range(14) if not m>>x&1)]
 return edges,positive,negative

def build(cap,equality=True,negative_proxy=False,graph='fano'):
 edges,pos,negs=specification(graph);tests=pos+negs;c=CNF();active=[c.var() for _ in range(cap)];c.add(active[0])
 for j in range(1,cap):c.add(-active[j],active[j-1])
 atoms=[]
 for j in range(cap):
  slots=[]
  for side in range(2):
   ss=[c.var() for _ in range(14)];tt=[c.var() for _ in range(j)]
   for z in ss+tt:c.add(-z,active[j])
   c.add(-active[j],*ss,*tt)
   slots.append(dict(primary=ss,prior=tt,values=[],terms=[]))
  for x in range(14):c.add(-slots[0]['primary'][x],-slots[1]['primary'][x])
  atoms.append(dict(active=active[j],slots=slots,values=[],modes=[],use_dp=None))
 final=[c.var() for _ in range(cap)];c.add(*final)
 for j,z in enumerate(final):c.add(-z,active[j])
 primary_counts=[]
 if equality:
  for x in range(14):
   uses=[s['primary'][x] for a in atoms for s in a['slots']];dp=c.threshold(uses,3)
   root2=next(z['var'] for z in dp['cells'] if z['prefix']==len(uses) and z['threshold']==2)
   c.add(root2);c.add(neg(dp['root']));primary_counts.append(dict(label=x,dp=dp,at_least_two=root2))
 for k,a in enumerate(atoms):
  consumers=[dict(atom=j,side=side,var=atoms[j]['slots'][side]['prior'][k]) for j in range(k+1,cap) for side in range(2)]
  uses=[z['var'] for z in consumers]+[final[k]];a['consumers']=consumers;c.add(-active[k],*uses)
  for z in uses:c.add(-z,active[k])
  if equality:
   modes=[c.var() for _ in range(15)];a['modes']=modes;c.add(-active[k],*modes)
   for z in modes:c.add(-z,active[k])
   for u,v in itertools.combinations(modes,2):c.add(-u,-v)
   dp=c.threshold(uses,2);a['use_dp']=dp;c.add(-modes[0],neg(dp['root']))
   for x in range(14):
    c.add(-modes[1+x],-final[k])
    for z in consumers:c.add(-modes[1+x],-z['var'],atoms[z['atom']]['slots'][z['side']]['primary'][x])
 for j,a in enumerate(atoms):
  for s in a['slots']:
   for row,mask in enumerate(tests):
    terms=[]
    for k,t in enumerate(s['prior']):
     q=c.var();c.conj(q,t,atoms[k]['values'][row]);terms.append(q)
    v=c.var();c.disjunction(v,[s['primary'][x] for x in range(14) if mask>>x&1]+terms)
    s['values'].append(v);s['terms'].append(terms)
  for row in range(len(tests)):
   v=c.var();c.conj(v,a['slots'][0]['values'][row],a['slots'][1]['values'][row]);a['values'].append(v)
  if negative_proxy:
   assert equality
   for row,mask in enumerate(tests):
    if mask in negs:
     for x in range(14):
      if not mask>>x&1:c.add(-a['modes'][1+x],-a['values'][row])
 final_values=[];final_terms=[]
 for row,mask in enumerate(tests):
  terms=[]
  for j,z in enumerate(final):
   q=c.var();c.conj(q,z,atoms[j]['values'][row]);terms.append(q)
  v=c.var();c.disjunction(v,terms);c.add(v if mask in pos else -v);final_values.append(v);final_terms.append(terms)
 meta=dict(cap=cap,equality=equality,negative_proxy=negative_proxy,graph=graph,edges=edges,positive=pos,negative=negs,tests=tests,active=active,atoms=atoms,final=final,primary_counts=primary_counts,final_values=final_values,final_terms=final_terms,variables=c.n,clauses=len(c.cs))
 return c,meta

def decode(meta,model):
 on=lambda z:z in model
 atoms=[]
 for a in meta['atoms']:
  if not on(a['active']):break
  slots=[dict(primary=[x for x,z in enumerate(s['primary']) if on(z)],prior=[k for k,z in enumerate(s['prior']) if on(z)]) for s in a['slots']]
  modes=[k for k,z in enumerate(a['modes']) if on(z)]
  atoms.append(dict(slots=slots,mode=None if not modes else modes[0]))
 return dict(atoms=atoms,final=[j for j,z in enumerate(meta['final']) if on(z)],graph=meta['graph'],equality=meta['equality'],negative_proxy=meta['negative_proxy'])
def evaluate(compact,mask):
 vals=[]
 for a in compact['atoms']:
  sv=[any(mask>>x&1 for x in s['primary']) or any(vals[k] for k in s['prior']) for s in a['slots']]
  vals.append(sv[0] and sv[1])
 return any(vals[k] for k in compact['final'])
def validate(compact):
 a=compact['atoms'];n=len(a);edges,pos,negs=specification(compact['graph']);assert n>0 and compact['final']
 slots=[s for z in a for s in z['slots']]
 for j,z in enumerate(a):
  assert not(set(z['slots'][0]['primary'])&set(z['slots'][1]['primary']))
  for s in z['slots']:assert s['primary'] or s['prior'];assert all(k<j for k in s['prior'])
 if compact['equality']:
  assert all(sum(x in s['primary'] for s in slots)==2 for x in range(14))
 for j,z in enumerate(a):
  uses=[s for k,b in enumerate(a) if k>j for s in b['slots'] if j in s['prior']];total=len(uses)+(j in compact['final']);assert total>=1
  if compact['equality']:
   assert total<=2
   if z['mode']==0:assert total==1
   else:
    x=z['mode']-1;assert j not in compact['final'] and all(x in s['primary'] for s in uses)
 for mask in range(1<<14):assert evaluate(compact,mask)==any(mask>>x&1 and mask>>y&1 for x,y in edges)
 return True

def main():
 p=argparse.ArgumentParser();p.add_argument('--cap',type=int,default=18);p.add_argument('--tag',required=True);p.add_argument('--no-equality',action='store_true');p.add_argument('--negative-proxy',action='store_true');p.add_argument('--graph',choices=['fano','matching'],default='fano');p.add_argument('--solve',type=int)
 args=p.parse_args();c,meta=build(args.cap,not args.no_equality,args.negative_proxy,args.graph);cnf=BASE/(args.tag+'.cnf');c.write(cnf);(BASE/(args.tag+'.metadata.json')).write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps({k:meta[k] for k in ['cap','graph','equality','negative_proxy','variables','clauses']}),flush=True)
 if args.solve is None:return
 start=time.time()
 with (BASE/(args.tag+'.stdout')).open('w') as out,(BASE/(args.tag+'.stderr')).open('w') as err:r=subprocess.run([CADICAL,'-t',str(args.solve),str(cnf)],stdout=out,stderr=err)
 text=(BASE/(args.tag+'.stdout')).read_text();status=next((line for line in text.splitlines() if line.startswith('s ')),'s UNKNOWN');print(json.dumps(dict(status=status,exit=r.returncode,elapsed=time.time()-start)),flush=True)
 if status=='s SATISFIABLE':
  model={int(x) for line in text.splitlines() if line.startswith('v ') for x in line.split()[1:] if x!='0'};candidate=decode(meta,model);validate(candidate);path=BASE/(args.tag+'.compact.json');path.write_text(json.dumps(candidate,indent=2)+'\n');print(json.dumps(dict(candidate=str(path),validated_truth_rows=1<<14)),flush=True)
if __name__=='__main__':main()
