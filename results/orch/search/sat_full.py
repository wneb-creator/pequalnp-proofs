import argparse,json
from pathlib import Path
from itertools import combinations

class CNF:
 def __init__(self):self.n=0;self.cs=[]
 def v(self):self.n+=1;return self.n
 def c(self,*xs):self.cs.append(list(xs))
 def exactly1(self,ss):
  self.c(*ss)
  for a,b in combinations(ss,2):self.c(-a,-b)
 def mux(self,q,ss,vs):
  for s,v in zip(ss,vs):
   if isinstance(v,bool):self.c(-s,q if v else -q)
   else:self.c(-s,-q,v);self.c(-s,q,-v)

def data(name):
 if name=='subK4':
  p,l=4,6;edges=[(a,j) for j,e in enumerate(combinations(range(4),2)) for a in e]
 else:
  p=l=7;edges=[(a,b) for a in range(7) for b in range(7) if ((a+1)&(b+1)).bit_count()%2==0]
 n=p+l;edge_masks=[(1<<a)|(1<<(p+b)) for a,b in edges]
 neg=[]
 for x in range(1<<n):
  if any((x&e)==e for e in edge_masks):continue
  if all((x>>i)&1 or any(((x|(1<<i))&e)==e for e in edge_masks) for i in range(n)):neg.append(x)
 stars=[]
 for a in range(p):
  nb=[p+b for aa,b in edges if aa==a]
  for s in range(2,len(nb)+1):
   for q in combinations(nb,s):stars.append(dict(side='left',centre=a,q=list(q),covers=[[a,i-p] for i in q]))
 for b in range(l):
  nb=[a for a,bb in edges if bb==b]
  for s in range(2,len(nb)+1):
   for q in combinations(nb,s):stars.append(dict(side='right',centre=b,q=list(q),covers=[[i,b] for i in q]))
 tests=list(dict.fromkeys(edge_masks+neg+[1<<i for i in range(n)]+[((1<<n)-1)^sum(1<<i for i in star['q']) for star in stars]+[0,(1<<n)-1]+[(1<<a)|(1<<b) for a,b in combinations(range(n),2)]))
 return dict(name=name,p=p,l=l,edges=edges,stars=stars,tests=tests,target=[any((x&e)==e for e in edge_masks) for x in tests])

def build(name,k,prefix):
 d=data(name);p=d['p'];n=p+d['l'];tests=d['tests'];C=CNF();sel=[];ops=[];vals=[];flags=[]
 for j in range(k):
  op=C.v();ss=[[C.v() for _ in range(n+j)] for _ in range(2)]
  for side in ss:C.exactly1(side)
  for a in range(n+j):
   for b in range(a):C.c(-ss[0][a],-ss[1][b])
  zz=[C.v() for _ in tests]
  for t,x in enumerate(tests):
   vs=[bool((x>>i)&1) for i in range(n)]+[vals[h][t] for h in range(j)]
   a,b=C.v(),C.v();C.mux(a,ss[0],vs);C.mux(b,ss[1],vs);z=zz[t]
   C.c(-op,-a,z);C.c(-op,-b,z);C.c(-op,a,b,-z)
   C.c(op,a,-z);C.c(op,b,-z);C.c(op,-a,-b,z)
  ff=[]
  for colour in range(2):
   vs=[(i<p) if colour==0 else (i>=p) for i in range(n)]+[flags[h][colour] for h in range(j)]
   a,b,z=C.v(),C.v(),C.v();C.mux(a,ss[0],vs);C.mux(b,ss[1],vs)
   C.c(op,-z);C.c(-op,-a,z);C.c(-op,-b,z);C.c(-op,a,b,-z);ff.append(z)
  C.c(-ff[0],-ff[1]);sel.append(ss);ops.append(op);vals.append(zz);flags.append(ff)
 out=[C.v() for _ in range(k)];C.exactly1(out)
 for j in range(k):
  for t,want in enumerate(d['target']):C.c(-out[j],vals[j][t] if want else -vals[j][t])
 wi=[];idx={x:t for t,x in enumerate(tests)}
 for star in d['stars']:
  ws=[];comp=((1<<n)-1)^sum(1<<i for i in star['q'])
  for j in range(k):
   w=C.v();ws.append(w);C.c(-w,ops[j]);C.c(-w,-vals[j][idx[comp]])
   for q in star['q']:C.c(-w,vals[j][idx[1<<q]])
  wi.append(ws)
 for edge in d['edges']:C.c(*[wi[c][j] for c,star in enumerate(d['stars']) if edge in [tuple(e) for e in star['covers']] for j in range(k)])
 d.update(k=k,sel=sel,ops=ops,vals=vals,flags=flags,out=out,wi=wi,variables=C.n,clauses=len(C.cs))
 Path(prefix+'.map.json').write_text(json.dumps(d))
 with Path(prefix+'.cnf').open('w') as f:
  f.write(f'p cnf {C.n} {len(C.cs)}\n')
  for c in C.cs:f.write(' '.join(map(str,c))+' 0\n')
 print(json.dumps({x:d[x] for x in ('name','k','variables','clauses')}|dict(patterns=len(tests),stars=len(d['stars']))))

def pin(prefix):
 d=json.loads(Path(prefix+'.map.json').read_text());p=d['p'];n=p+d['l'];gates=[];terms=[]
 for a in range(p):
  nb=[p+b for aa,b in d['edges'] if aa==a];r=nb[0]
  for b in nb[1:]:gates.append(['or',*sorted((r,b))]);r=n+len(gates)-1
  gates.append(['and',*sorted((a,r))]);terms.append(n+len(gates)-1)
 r=terms[0]
 for t in terms[1:]:gates.append(['or',*sorted((r,t))]);r=n+len(gates)-1
 assert len(gates)==d['k'];units=[]
 for j,(op,a,b) in enumerate(gates):
  units.append(d['ops'][j] if op=='or' else -d['ops'][j])
  for side,wire in enumerate((a,b)):
   units.extend(v if i==wire else -v for i,v in enumerate(d['sel'][j][side]))
 units.extend(v if n+j==r else -v for j,v in enumerate(d['out']))
 lines=Path(prefix+'.cnf').read_text().splitlines();head=lines[0].split();head[3]=str(int(head[3])+len(units))
 Path(prefix+'.pinned.cnf').write_text(' '.join(head)+'\n'+'\n'.join(lines[1:])+'\n'+''.join(str(x)+' 0\n' for x in units))
 print('Canonical pinned gate count:',len(gates))

def verify(prefix,model):
 d=json.loads(Path(prefix+'.map.json').read_text());p=d['p'];l=d['l'];n=p+l;s=Path(model).read_text()
 if 's SATISFIABLE' not in s:print('No SAT witness');return
 true={int(x) for ln in s.splitlines() if ln.startswith('v ') for x in ln[2:].split() if int(x)>0}
 gates=[]
 for j in range(d['k']):
  a,b=[[i for i,v in enumerate(side) if v in true] for side in d['sel'][j]]
  assert len(a)==len(b)==1;gates.append(['or' if d['ops'][j] in true else 'and',a[0],b[0]])
 os=[j for j,v in enumerate(d['out']) if v in true];assert len(os)==1;out=n+os[0]
 iv=[sum(1<<x for x in range(1<<n) if (x>>i)&1) for i in range(n)];target=0
 for a,b in d['edges']:target|=iv[a]&iv[p+b]
 vals=iv.copy();reach=[1<<i for i in range(n)];covered=set();witnesses=[];mixed=0
 for j,(op,a,b) in enumerate(gates):
  assert a<n+j and b<n+j;vals.append((vals[a]|vals[b]) if op=='or' else (vals[a]&vals[b]));reach.append((reach[a]|reach[b]) if op=='or' else 0)
  if op=='or' and reach[-1]&((1<<p)-1) and reach[-1]&(((1<<l)-1)<<p):mixed+=1
  if op!='or':continue
  support=[i for i in range(n) if (vals[-1]>>(1<<i))&1];st=0
  for i in support:st|=iv[i]
  if len(support)<2 or st!=vals[-1]:continue
  for c,star in enumerate(d['stars']):
   if support==star['q']:covered.update(map(tuple,star['covers']));witnesses.append([j,c])
 es=[(1<<a)|(1<<(p+b)) for a,b in d['edges']]
 tau=min(x.bit_count() for x in range(1<<n) if all(x&e for e in es))
 c4free=all(len({b for aa,b in d['edges'] if aa==a}&{b for aa,b in d['edges'] if aa==aa2})<=1 for a,aa2 in combinations(range(p),2))
 report=dict(full_truth=vals[out]==target,T=mixed,star_covered=len(covered),edges=len(es),tau=tau,gates=len(gates),claimed_bound=len(es)+tau-1,violates_bound=len(gates)<len(es)+tau-1,C4free=c4free,AND=sum(g[0]=='and' for g in gates),OR=sum(g[0]=='or' for g in gates),uncovered=sorted(set(map(tuple,d['edges']))-covered))
 witness=dict(graph=d['name'],p=p,l=l,edges=d['edges'],gates=gates,output=out,stars=d['stars'],star_witnesses=witnesses,report=report)
 Path(prefix+'.witness.json').write_text(json.dumps(witness));print(json.dumps(report));print(prefix+'.witness.json')

ap=argparse.ArgumentParser();s=ap.add_subparsers(dest='mode',required=True)
a=s.add_parser('build');a.add_argument('graph',choices=['subK4','Fano']);a.add_argument('gates',type=int);a.add_argument('prefix')
a=s.add_parser('pin');a.add_argument('prefix')
a=s.add_parser('verify');a.add_argument('prefix');a.add_argument('model')
a=ap.parse_args()
if a.mode=='build':build(a.graph,a.gates,a.prefix)
elif a.mode=='pin':pin(a.prefix)
else:verify(a.prefix,a.model)
