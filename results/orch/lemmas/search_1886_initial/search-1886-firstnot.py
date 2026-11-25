import argparse,itertools,json,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--edge-op',choices=['and','or'],required=True);p.add_argument('--not-input',type=int,required=True);p.add_argument('--gates',type=int,default=17);p.add_argument('--seedfile',default='');p.add_argument('--final-or-edge',action='store_true');p.add_argument('--ordered',action='store_true');p.add_argument('--live',action='store_true');p.add_argument('--output',required=True);a=p.parse_args()
assert -1<=a.not_input<=10
assert not a.final_or_edge or (a.edge_op=='and' and a.not_input==-1)
fixed_not=a.not_input>=0
fixed_inputs=set() if not fixed_not else {a.not_input} if a.not_input<10 else {0,1}
bank_count=11+int(fixed_not)
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(x):return any((x>>u&1) and (x>>v&1) for u,v in edges)
rows=[]
for x in range(1024):
 value=target(x)
 if value:
  critical=all(not target(x^(1<<j)) for j in range(10) if j not in fixed_inputs and x>>j&1)
 else:
  critical=all(target(x^(1<<j)) for j in range(10) if j not in fixed_inputs and not x>>j&1)
 if critical and not (a.final_or_edge and x==3):rows.append(x)
n=0;clauses=[]
def fresh():
 global n
 n+=1;return n
def put(*xs):clauses.append(list(xs))
def exactly(xs):
 put(*xs)
 for x,y in itertools.combinations(xs,2):put(-x,-y)
ops=[];sa=[];sb=[]
for i in range(a.gates):
 o=fresh();aa=[fresh() for _ in range(bank_count+i)];bb=[fresh() for _ in range(bank_count+i)]
 ops.append(o);sa.append(aa);sb.append(bb);exactly(aa);exactly(bb)
 for k in range(bank_count+i):put(-aa[k],*bb[k:])
if a.ordered:
 for i in range(a.gates-1):
  for b in range(bank_count+i):
   put(-sb[i][b],*sb[i+1][b:])
   for u in range(b+1):
    put(-sb[i][b],-sb[i+1][b],-sa[i][u],*sa[i+1][u:])
    put(-sb[i][b],-sb[i+1][b],-sa[i][u],-sa[i+1][u],-ops[i],ops[i+1])
if a.live:
 for i in range(a.gates-1):
  put(*[selector[j][bank_count+i] for j in range(i+1,a.gates) for selector in (sa,sb)])
if a.seedfile:
 seed=json.loads(Path(a.seedfile).read_text())
 for i,(op,x,y) in enumerate(seed['gates'][-a.gates:]):
  assert op in (0,1)
  x,y=sorted((x,y));put(ops[i] if op==1 else -ops[i]);put(sa[i][x]);put(sb[i][y])
for x in rows:
 base=[bool(x>>j&1) for j in range(10)]
 base.append(base[0] and base[1] if a.edge_op=='and' else base[0] or base[1])
 if fixed_not:base.append(not base[a.not_input])
 wires=[('constant',b) for b in base]
 for i in range(a.gates):
  va,vb,v=fresh(),fresh(),fresh()
  for sels,u in ((sa[i],va),(sb[i],vb)):
   for sel,(kind,w) in zip(sels,wires):
    if kind=='constant':put(-sel,u if w else -u)
    else:put(-sel,-u,w);put(-sel,u,-w)
  o=ops[i]
  put(o,-v,va);put(o,-v,vb);put(o,v,-va,-vb)
  put(-o,v,-va);put(-o,v,-vb);put(-o,-v,va,vb)
  wires.append(('variable',v))
 put(wires[-1][1] if target(x) else -wires[-1][1])
out=Path(a.output)
with out.open('w') as f:
 f.write('p cnf '+str(n)+' '+str(len(clauses))+'\n')
 for row in clauses:f.write(' '.join(map(str,row))+' 0\n')
meta={'variables':n,'clauses':len(clauses),'ops':ops,'a':sa,'b':sb,'rows':rows,'edge_op':a.edge_op,'not_input':a.not_input,'gates':a.gates,'fixed_not':fixed_not,'final_or_edge':a.final_or_edge,'ordered':a.ordered,'live':a.live}
out.with_suffix('.json').write_text(json.dumps(meta))
print(json.dumps({k:v for k,v in meta.items() if k not in ('ops','a','b')}))
