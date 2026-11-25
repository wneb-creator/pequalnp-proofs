import argparse,itertools,json
from pathlib import Path
T=3892346880*2**32+2147483648
class CNF:
 def __init__(self):self.n=0;self.cs=[]
 def v(self):self.n+=1;return self.n
 def c(self,*xs):self.cs.append(list(xs))
 def one(self,xs):
  self.c(*xs)
  for a,b in itertools.combinations(xs,2):self.c(-a,-b)
 def mux(self,z,ss,vs):
  for s,v in zip(ss,vs):
   if isinstance(v,bool):self.c(-s,z if v else -z)
   else:self.c(-s,-z,v);self.c(-s,z,-v)
def build(k,general,prefix,sym=True):
 C=CNF();opnames=['and','or']+(['not'] if general else [])+['true','false'];sels=[];ops=[];vals=[]
 for j in range(k):
  oo=[C.v() for _ in opnames];C.one(oo);ss=[[C.v() for _ in range(7+j)] for _ in range(2)]
  for s in ss:C.one(s)
  for oi,op in enumerate(opnames):
   ov=oo[oi]
   if op in ['true','false']:
    C.c(-ov,ss[0][6]);C.c(-ov,ss[1][6])
   elif op=='not':
    for a in range(7+j):C.c(-ov,-ss[0][a],ss[1][a])
   else:
    for a in range(7+j):
     for b in range(a):C.c(-ov,-ss[0][a],-ss[1][b])
  zz=[]
  for x in range(64):
   a,b,z=C.v(),C.v(),C.v();zz.append(z);vs=[bool(x>>i&1) for i in range(6)]+[False]+[vals[h][x] for h in range(j)]
   C.mux(a,ss[0],vs);C.mux(b,ss[1],vs)
   for oi,op in enumerate(opnames):
    v=oo[oi]
    if op=='and':C.c(-v,a,-z);C.c(-v,b,-z);C.c(-v,-a,-b,z)
    elif op=='or':C.c(-v,-a,z);C.c(-v,-b,z);C.c(-v,a,b,-z)
    elif op=='not':C.c(-v,a,z);C.c(-v,-a,-z)
    elif op=='true':C.c(-v,z)
    else:C.c(-v,-z)
  sels.append(ss);ops.append(oo);vals.append(zz)
 for j in range(k-1):C.c(*[sels[h][b][7+j] for h in range(j+1,k) for b in range(2)])
 for x in range(64):C.c(vals[-1][x] if T>>x&1 else -vals[-1][x])
 if sym:
  for j in range(1,k):
   guard=[sels[j][0][-1],sels[j][1][-1]]
   for a in range(len(opnames)):
    for b in range(a):C.c(*guard,-ops[j-1][a],-ops[j][b])
   aa=sels[j-1][0];bb=sels[j][0];eq=C.v()
   for a,b in zip(aa,bb):C.c(-a,-b,eq);C.c(-eq,-a,b);C.c(-eq,-b,a)
   C.c(-eq,-bb[-1])
   for op in range(len(opnames)):
    g=guard+[-ops[j-1][op],-ops[j][op]]
    for a in range(7+j-1):
     for b in range(a):
      C.c(*g,-aa[a],-bb[b]);C.c(*g,-eq,-sels[j-1][1][a],-sels[j][1][b])
  others=[0,1,2,4,5];perms=[]
  for pp in itertools.permutations(others):
   perm=list(range(7))
   for a,b in zip(others,pp):perm[a]=b
   assert all((T>>x&1)==(T>>sum(1<<perm[i] for i in range(6) if x>>i&1)&1) for x in range(64));perms.append(perm)
  seen=set();reps=[]
  for a in range(7):
   for b in range(a,7):
    if (a,b) in seen:continue
    orb={tuple(sorted((p[a],p[b]))) for p in perms};seen|=orb;reps.append(min(orb))
  choices=[]
  for a,b in reps:
   z=C.v();choices.append(z);C.c(-z,sels[0][0][a]);C.c(-z,sels[0][1][b])
  C.c(*choices)
 d=dict(k=k,general=general,T=T,sels=sels,ops=ops,vals=vals,opnames=opnames,variables=C.n,clauses=len(C.cs),symmetry=sym)
 Path(prefix+'.json').write_text(json.dumps(d))
 with Path(prefix+'.cnf').open('w') as f:
  f.write(f'p cnf {C.n} {len(C.cs)}\n')
  for c in C.cs:f.write(' '.join(map(str,c))+' 0\n')
 print('BUILT',prefix,'variables',C.n,'clauses',len(C.cs),'general',general,'symmetry',sym)
def decode(prefix,log):
 d=json.loads(Path(prefix+'.json').read_text());txt=Path(log).read_text()
 if 's SATISFIABLE' not in txt:print('No SAT model');return
 tr={int(x) for ln in txt.splitlines() if ln.startswith('v ') for x in ln[2:].split() if int(x)>0}
 vv=[sum(1<<x for x in range(64) if x>>i&1) for i in range(6)]+[0];gates=[];full=(1<<64)-1
 for j in range(d['k']):
  oo=[op for op,v in zip(d['opnames'],d['ops'][j]) if v in tr];aa=[[i for i,v in enumerate(s) if v in tr] for s in d['sels'][j]];assert len(oo)==1 and all(len(a)==1 for a in aa);op=oo[0];a,b=aa[0][0],aa[1][0]
  z=(vv[a]&vv[b]) if op=='and' else (vv[a]|vv[b]) if op=='or' else (full^vv[a]) if op=='not' else full if op=='true' else 0
  vv.append(z);gates.append([op,a,b])
 assert vv[-1]==T
 original=[]
 for j,(op,a,b) in enumerate(gates):
  conv=lambda i:i if i<6 else (6+j if i==6 else i-1)
  original.append(dict(op='and' if op=='true' else 'or' if op=='false' else op,inputs=[] if op in ['true','false'] else [conv(a)] if op=='not' else [conv(a),conv(b)]))
 report=dict(gates=d['k'],truth=hex(vv[-1]),NOT=sum(g[0]=='not' for g in gates),all64verified=True,output=5+d['k'])
 witness=dict(report=report,normalized=gates,circuit=original,output=5+d['k'])
 Path(prefix+'.witness.json').write_text(json.dumps(witness,indent=2)+'\n');print(json.dumps(report));print(json.dumps(witness))
p=argparse.ArgumentParser();s=p.add_subparsers(dest='cmd',required=True);a=s.add_parser('build');a.add_argument('k',type=int);a.add_argument('basis',choices=['general','monotone']);a.add_argument('prefix');a.add_argument('--no-sym',action='store_true');a=s.add_parser('decode');a.add_argument('prefix');a.add_argument('log');a=p.parse_args()
if a.cmd=='build':build(a.k,a.basis=='general',a.prefix,not a.no_sym)
else:decode(a.prefix,a.log)
