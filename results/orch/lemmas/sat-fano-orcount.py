import argparse, itertools, json, subprocess, time
from pathlib import Path

BASE=Path('/tmp/oec/pequalnp-pilot-81')
CADICAL=str(BASE/'lean-4.36.0-linux/bin/cadical')
def neg(x): return not x if isinstance(x,bool) else -x
class CNF:
 def __init__(self): self.n=0;self.cs=[]
 def var(self): self.n+=1;return self.n
 def add(self,*args):
  if any(x is True for x in args): return
  row=list(dict.fromkeys(x for x in args if x is not False))
  if any(-x in row for x in row): return
  self.cs.append(row)
 def eq(self,a,b,cond=True):
  self.add(neg(cond),neg(a),b);self.add(neg(cond),a,neg(b))
 def conj(self,y,a,b,cond=True):
  self.add(neg(cond),neg(a),neg(b),y);self.add(neg(cond),a,neg(y));self.add(neg(cond),b,neg(y))
 def disj(self,y,a,b,cond=True):
  self.add(neg(cond),a,b,neg(y));self.add(neg(cond),neg(a),y);self.add(neg(cond),neg(b),y)
 def onehot(self,v):
  self.add(*v)
  for a,b in itertools.combinations(v,2): self.add(-a,-b)
 def select(self,s,v):
  y=self.var()
  for z,x in zip(s,v): self.eq(y,x,z)
  return y
 def write(self,p):
  with p.open('w') as f:
   f.write(f'p cnf {self.n} {len(self.cs)}\n')
   for c in self.cs:f.write(' '.join(map(str,c))+' 0\n')

def at_least(c,lits,threshold):
 # Cell(i,j) is exactly: at least j of the first i literals hold.
 # z <-> a OR (b AND x), where a=Cell(i-1,j), b=Cell(i-1,j-1).
 cells=[]
 if threshold<=0:return dict(threshold=threshold,literals=lits,cells=cells,root=True)
 if threshold>len(lits):
  c.add(False)
  return dict(threshold=threshold,literals=lits,cells=cells,root=False)
 previous=[True]+[False]*threshold
 for i,x in enumerate(lits,1):
  current=[True]+[False]*threshold
  for j in range(1,min(i,threshold)+1):
   a=previous[j];b=previous[j-1];z=c.var()
   c.add(neg(a),z)
   c.add(neg(b),neg(x),z)
   c.add(-z,a,b)
   c.add(-z,a,x)
   current[j]=z
   cells.append(dict(prefix=i,threshold=j,var=z))
  previous=current
 c.add(previous[threshold])
 return dict(threshold=threshold,literals=lits,cells=cells,root=previous[threshold])

def get_spec(points):
 lines=sorted({(p-d)%7 for p in points for d in (0,1,3)})
 original=list(points)+[7+l for l in lines]
 edges=[(points.index(p),len(points)+lines.index(l)) for p in points for l in lines if (p-l)%7 in (0,1,3)]
 n=len(original)
 def fun(mask):return any((mask>>a)&1 and (mask>>b)&1 for a,b in edges)
 pos=[(1<<a)|(1<<b) for a,b in edges]
 negs=[m for m in range(1<<n) if not fun(m) and all(fun(m|(1<<i)) for i in range(n) if not(m>>i&1))]
 return original,edges,pos,negs,fun

def synth(points,size,limit,double=True,tag=None,selected_edge=None,ordered=False,edge_support=False,op_order=False,no_solve=False,boundary_essential=False,false_or_count=False):
 original,edges,pos,negs,fun=get_spec(points); n=len(original)
 edge=edges[0] if selected_edge is None else (original.index(selected_edge[0]),original.index(7+selected_edge[1])); assert edge in edges
 bases=[1<<edge[0],1<<edge[1]]
 tests=list(dict.fromkeys(pos+negs+bases))
 c=CNF();vals=[[bool(m>>i&1) for m in tests] for i in range(n)]
 ders=[[bool(i==edge[1]),bool(i==edge[0])] for i in range(n)]
 ops=[]; sels=[]; gate_meta=[]
 for j in range(size):
  width=n+j
  op=c.var();ops.append(op)
  sa=[c.var() for _ in range(width)]; sb=[c.var() for _ in range(width)]
  c.onehot(sa);c.onehot(sb)
  for a in range(width):
   for b in range(a+1):c.add(-sa[a],-sb[b])
  sels.append((sa,sb))
  va=[];vb=[];vy=[]
  for r in range(len(tests)):
   a=c.select(sa,[v[r] for v in vals]); b=c.select(sb,[v[r] for v in vals]); y=c.var()
   c.conj(y,a,b,op);c.disj(y,a,b,-op)
   va.append(a);vb.append(b);vy.append(y)
  dy=[];trace_meta=[]
  for r in range(2):
   da=c.select(sa,[d[r] for d in ders]); db=c.select(sb,[d[r] for d in ders]); y=c.var()
   ta=c.var();tb=c.var();both=c.var()
   baseidx=tests.index(bases[r])
   c.conj(ta,va[baseidx],db);c.conj(tb,da,vb[baseidx]);c.disj(both,ta,tb)
   c.eq(y,both,op);c.disj(y,da,db,-op);dy.append(y)
   trace_meta.append(dict(selected_a=da,selected_b=db,term_a=ta,term_b=tb,both=both,out=y))
  vals.append(vy);ders.append(dy)
  gate_meta.append(dict(op=op,select_a=sa,select_b=sb,selected_a=va,selected_b=vb,outputs=vy,traces=trace_meta))
 if ordered:
  for (sa,sb),(ta,tb) in zip(sels,sels[1:]):
   for i,x in enumerate(sb):c.add(-x,*tb[i:])
   for b in range(len(sb)):
    for a in range(b):c.add(-sb[b],-tb[b],-sa[a],*ta[a:])
 if op_order:
  for j,((sa,sb),(ta,tb)) in enumerate(zip(sels,sels[1:])):
   for b in range(len(sb)):
    for a in range(b):c.add(-sa[a],-ta[a],-sb[b],-tb[b],ops[j],-ops[j+1])
 if edge_support:
  for v in vals[n:]:c.add(*[v[tests.index(m)] for m in pos])
 boundary_meta=[]
 if boundary_essential:
  for v in vals[n:]:c.add(*[-v[tests.index(m)] for m in negs])
  # At the optimal Fano size27, a removable boundary-comparable gate
  # contradicts the accepted ordinary lower bound. Positive controls at28
  # are checked explicitly; this is not a WLOG claim for arbitrary size28.
  for j,g in enumerate(gate_meta):
   signs={True:[[],[]],False:[[],[]]}
   for r,m in enumerate(tests):
    if m not in pos and m not in negs:continue
    ab=c.var();ba=c.var()
    c.conj(ab,g['selected_a'][r],-g['selected_b'][r])
    c.conj(ba,g['selected_b'][r],-g['selected_a'][r])
    signs[m in pos][0].append(ab);signs[m in pos][1].append(ba)
    boundary_meta.append(dict(gate=j,row=r,a_not_b=ab,b_not_a=ba))
   for ds in signs[True]:c.add(ops[j],*ds)
   for ds in signs[False]:c.add(-ops[j],*ds)
 row_card_meta=[]
 if false_or_count:
  for mask in negs:
   row=tests.index(mask)
   required=n-mask.bit_count()-1
   eligible=[]
   for j,g in enumerate(gate_meta):
    q=c.var();c.conj(q,-ops[j],-g['outputs'][row]);eligible.append(q)
   dp=at_least(c,eligible,required)
   row_card_meta.append(dict(row=row,mask=mask,required=required,gate_literals=eligible,dp=dp))
 for r,m in enumerate(tests):c.add(vals[-1][r] if fun(m) else -vals[-1][r])
 if double:
  for d in ders[-1]:c.add(-d)
 for i in range(n):c.add(*[sel[i] for sa,sb in sels for sel in (sa,sb)])
 # Retain only useful gates; output-operator padding covers smaller witnesses.
 for j in range(size-1):
  c.add(*[s[n+j] for sa,sb in sels[j+1:] for s in (sa,sb)])
 tag=tag or 'sat-'+''.join(map(str,points))+'-'+str(size)+('-double' if double else '')
 cnf=BASE/(tag+'.cnf');out=BASE/(tag+'.stdout');err=BASE/(tag+'.stderr')
 c.write(cnf)
 (BASE/(tag+'.metadata.json')).write_text(json.dumps(dict(inputs=n,original=original,tests=tests,positive=pos,negative=negs,edge=edge,bases=bases,gates=gate_meta,boundary_essential=boundary_meta,false_or_count=row_card_meta,variables=c.n,clauses=len(c.cs)),indent=2)+'\n')
 start=time.time()
 print(json.dumps(dict(tag=tag,inputs=n,tests=len(tests),vars=c.n,clauses=len(c.cs))),flush=True)
 if no_solve:return None
 with out.open('w') as f,err.open('w') as e:
  run=subprocess.run([CADICAL,'-t',str(limit),str(cnf)],stdout=f,stderr=e)
 text=out.read_text();status=next((x for x in text.splitlines() if x.startswith('s ')),'s UNKNOWN')
 print(json.dumps(dict(tag=tag,status=status,exit=run.returncode,elapsed=round(time.time()-start,3))),flush=True)
 if status!='s SATISFIABLE':return None
 model={int(s) for line in text.splitlines() if line.startswith('v ') for s in line.split()[1:] if s!='0'}
 gates=[]
 for op,(sa,sb) in zip(ops,sels):
  gates.append(('and' if op in model else 'or',next(i for i,x in enumerate(sa) if x in model),next(i for i,x in enumerate(sb) if x in model)))
 def eval_all(mask):
  v=[bool(mask>>i&1) for i in range(n)]
  for op,a,b in gates:v.append(v[a] and v[b] if op=='and' else v[a] or v[b])
  return v
 def deriv(r):
  v=eval_all(bases[r]);d=[bool(i==edge[1-r]) for i in range(n)]
  for op,a,b in gates:d.append((v[a] and d[b])or(d[a] and v[b]) if op=='and' else d[a] or d[b])
  return d[-1]
 assert all(eval_all(m)[-1]==fun(m) for m in range(1<<n))
 assert not double or not(deriv(0) or deriv(1))
 witness=dict(original=original,edge=[original[i] for i in edge],gates=gates,derivatives=[deriv(0),deriv(1)],size=size)
 (BASE/(tag+'.witness.json')).write_text(json.dumps(witness,indent=2)+'\n')
 print(json.dumps(witness),flush=True)
 return witness

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--points',required=True);p.add_argument('--size',type=int,required=True);p.add_argument('--limit',type=int,default=60);p.add_argument('--no-double',action='store_true');p.add_argument('--tag');p.add_argument('--edge');p.add_argument('--ordered',action='store_true');p.add_argument('--edge-support',action='store_true');p.add_argument('--op-order',action='store_true');p.add_argument('--no-solve',action='store_true');p.add_argument('--boundary-essential',action='store_true');p.add_argument('--false-or-count',action='store_true')
 a=p.parse_args();synth([int(x) for x in a.points.split(',')],a.size,a.limit,not a.no_double,a.tag,None if a.edge is None else tuple(map(int,a.edge.split(','))),a.ordered,a.edge_support,a.op_order,a.no_solve,a.boundary_essential,a.false_or_count)
