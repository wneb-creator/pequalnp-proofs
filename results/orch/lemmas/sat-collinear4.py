import argparse,importlib.util,json,subprocess,time
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-81')
spec=importlib.util.spec_from_file_location('broad',BASE/'sat-fano-full.py');broad=importlib.util.module_from_spec(spec);spec.loader.exec_module(broad)
POINTS=[3,4,5,6]
ORIGINAL=POINTS+list(range(7,14))
EDGES=[(i,4+l) for i,p in enumerate(POINTS) for l in range(7) if (p+l)%7 in (0,1,3)]
def target(mask):return any(mask>>a&1 and mask>>b&1 for a,b in EDGES)
def build(size,double=True):
 n=11;positive=[(1<<a)|(1<<b) for a,b in EDGES];negative=[m for m in range(1<<n) if not target(m) and all(target(m|(1<<i)) for i in range(n) if not m>>i&1)];tests=positive+negative
 c=broad.CNF();flags=[c.var() for _ in EDGES];c.onehot(flags);bases=[]
 for direction in range(2):
  row=[]
  for i in range(n):
   d=c.var();terms=[z for z,e in zip(flags,EDGES) if e[direction]==i];c.add(-d,*terms)
   for z in terms:c.add(-z,d)
   row.append(d)
  bases.append(row)
 vals=[[bool(mask>>i&1) for mask in tests]+[bases[0][i],bases[1][i]] for i in range(n)]
 ders=[[bases[1][i],bases[0][i]] for i in range(n)];gates=[]
 for j in range(size):
  width=n+j;op=c.var();sa=[c.var() for _ in range(width)];sb=[c.var() for _ in range(width)];c.onehot(sa);c.onehot(sb)
  for a in range(width):
   for b in range(a+1):c.add(-sa[a],-sb[b])
  va=[];vb=[];vy=[]
  for row in range(len(tests)+2):
   a=c.select(sa,[v[row] for v in vals]);b=c.select(sb,[v[row] for v in vals]);y=c.var();c.conj(y,a,b,op);c.disj(y,a,b,-op);va.append(a);vb.append(b);vy.append(y)
  traces=[];dy=[]
  for direction in range(2):
   da=c.select(sa,[v[direction] for v in ders]);db=c.select(sb,[v[direction] for v in ders]);ta=c.var();tb=c.var();both=c.var();y=c.var()
   c.conj(ta,va[len(tests)+direction],db);c.conj(tb,da,vb[len(tests)+direction]);c.disj(both,ta,tb);c.eq(y,both,op);c.disj(y,da,db,-op);dy.append(y)
   traces.append(dict(selected_a=da,selected_b=db,term_a=ta,term_b=tb,both=both,out=y))
  gates.append(dict(op=op,select_a=sa,select_b=sb,selected_a=va,selected_b=vb,outputs=vy,traces=traces));vals.append(vy);ders.append(dy)
  c.add(*vy[:len(positive)])
 for first,second in zip(gates,gates[1:]):
  sa,sb=first['select_a'],first['select_b'];ta,tb=second['select_a'],second['select_b']
  for i,x in enumerate(sb):c.add(-x,*tb[i:])
  for b in range(len(sb)):
   for a in range(b):c.add(-sb[b],-tb[b],-sa[a],*ta[a:])
 for i in range(n):c.add(*[g[s][i] for g in gates for s in ['select_a','select_b']])
 for j in range(size-1):c.add(*[g[s][n+j] for g in gates[j+1:] for s in ['select_a','select_b']])
 for row in range(len(tests)+2):c.add(vals[-1][row] if row<len(positive) else -vals[-1][row])
 if double:
  for d in ders[-1]:c.add(-d)
 m=dict(inputs=n,size=size,original=ORIGINAL,edges=EDGES,positive=positive,negative=negative,tests=tests,flags=flags,bases=bases,gates=gates,double=double,ordered=True,edge_support=True,variables=c.n,clauses=len(c.cs));return c,m

def canonicalize(gates,n=11):
 pending=set(range(len(gates)));mapped={i:i for i in range(n)};out=[]
 while pending:
  ready=[j for j in pending if gates[j][1] in mapped and gates[j][2] in mapped];assert ready
  def key(j):
   a,b=sorted([mapped[gates[j][1]],mapped[gates[j][2]]]);return b,a,j
  j=min(ready,key=key);op,a,b=gates[j];a,b=sorted([mapped[a],mapped[b]]);out.append([op,a,b]);mapped[n+j]=n+len(out)-1;pending.remove(j)
 assert mapped[n+len(gates)-1]==n+len(gates)-1;return out

def evaluate(gates,n,mask):
 vals=[bool(mask>>i&1) for i in range(n)]
 for op,a,b in gates:vals.append(vals[a] and vals[b] if op=='and' else vals[a] or vals[b])
 return vals

def derivative(gates,n,base,seed):
 vals=evaluate(gates,n,1<<base);ds=[i==seed for i in range(n)]
 for op,a,b in gates:ds.append((vals[a] and ds[b]) or (ds[a] and vals[b]) if op=='and' else ds[a] or ds[b])
 return ds[-1]

def validate_local(gates,edge,double=True):
 assert edge in EDGES
 for j,(op,a,b) in enumerate(gates):assert op in ('and','or') and 0<=a<b<11+j
 assert all(evaluate(gates,11,m)[-1]==target(m) for m in range(2048))
 ds=[derivative(gates,11,edge[0],edge[1]),derivative(gates,11,edge[1],edge[0])]
 assert not double or ds==[False,False];return ds

def splice(gates,edge):
 mapping=POINTS+[7+(-l)%7 for l in range(7)];full=[]
 for j,(op,a,b) in enumerate(gates):
  full.append([op,mapping[a],mapping[b]]);mapping.append(14+j)
 outputs=[14+len(gates)-1]
 for p in [0,1,2]:
  lines=[7+(p-d)%7 for d in [0,1,3]]
  full.append(['or',lines[0],lines[1]]);u=14+len(full)-1
  full.append(['or',u,lines[2]]);u=14+len(full)-1
  full.append(['and',p,u]);outputs.append(14+len(full)-1)
 out=outputs[0]
 for v in outputs[1:]:full.append(['or',out,v]);out=14+len(full)-1
 assert len(full)==len(gates)+12
 for j,(op,a,b) in enumerate(full):assert a!=b and 0<=a<14+j and 0<=b<14+j
 edges=[(p,7+l) for p in range(7) for l in range(7) if (p-l)%7 in (0,1,3)]
 assert all(evaluate(full,14,m)[-1]==any(m>>a&1 and m>>b&1 for a,b in edges) for m in range(16384))
 flag=[mapping[edge[0]],mapping[edge[1]]];ds=[derivative(full,14,flag[0],flag[1]),derivative(full,14,flag[1],flag[0])]
 assert ds==[derivative(gates,11,edge[0],edge[1]),derivative(gates,11,edge[1],edge[0])]
 return dict(n_inputs=14,gates=full,output=out,size=len(full),target_edge=[flag[0],flag[1]-7],derivatives=ds,verified_truth_rows=16384)

def main():
 p=argparse.ArgumentParser();p.add_argument('--size',type=int,default=15);p.add_argument('--ordinary',action='store_true');p.add_argument('--tag',required=True);p.add_argument('--solve',type=int);a=p.parse_args();c,m=build(a.size,not a.ordinary);cnf=BASE/(a.tag+'.cnf');c.write(cnf);(BASE/(a.tag+'.metadata.json')).write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({k:m[k] for k in ['inputs','size','variables','clauses','double']}),flush=True)
 if a.solve is None:return
 start=time.time()
 with (BASE/(a.tag+'.stdout')).open('w') as out,(BASE/(a.tag+'.stderr')).open('w') as err:r=subprocess.run([broad.CADICAL,'-t',str(a.solve),str(cnf)],stdout=out,stderr=err)
 text=(BASE/(a.tag+'.stdout')).read_text();status=next((line for line in text.splitlines() if line.startswith('s ')),'s UNKNOWN');print(json.dumps(dict(status=status,exit=r.returncode,elapsed=time.time()-start)),flush=True)
 if status=='s SATISFIABLE':
  model={int(z) for line in text.splitlines() if line.startswith('v ') for z in line.split()[1:] if z!='0'};edge=next(e for e,z in zip(EDGES,m['flags']) if z in model)
  gates=[['and' if g['op'] in model else 'or',next(i for i,z in enumerate(g['select_a']) if z in model),next(i for i,z in enumerate(g['select_b']) if z in model)] for g in m['gates']]
  ds=validate_local(gates,edge,not a.ordinary);witness=dict(original=ORIGINAL,gates=gates,edge=edge,derivatives=ds,size=a.size);(BASE/(a.tag+'.witness.json')).write_text(json.dumps(witness,indent=2)+'\n');full=splice(gates,edge);(BASE/(a.tag+'.full-fano.json')).write_text(json.dumps(full,indent=2)+'\n');print(json.dumps(dict(local_witness=str(BASE/(a.tag+'.witness.json')),full_witness=str(BASE/(a.tag+'.full-fano.json')),full_size=full['size'],derivatives=ds)),flush=True)
if __name__=='__main__':main()
