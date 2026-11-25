import argparse,ctypes,itertools,json,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--edge-op',choices=['and','or'],required=True);p.add_argument('--gates',type=int,default=18);p.add_argument('--min-not',type=int,default=0);p.add_argument('--max-not',type=int,default=2);p.add_argument('--seconds',type=float,default=600);p.add_argument('--seedfile',default='');p.add_argument('--output-prefix',required=True);a=p.parse_args()
ptr=ctypes.c_void_p;c=ctypes.CDLL('/tmp/oec/pequalnp-pilot-92/search-libcadical.so')
for name,restype,args in [('init',ptr,[]),('release',None,[ptr]),('add',None,[ptr,ctypes.c_int]),('solve',ctypes.c_int,[ptr]),('val',ctypes.c_int,[ptr,ctypes.c_int]),('freeze',None,[ptr,ctypes.c_int]),('set_option',None,[ptr,ctypes.c_char_p,ctypes.c_int])]:
 fn=getattr(c,'search_'+name);fn.restype=restype;fn.argtypes=args
callback_type=ctypes.CFUNCTYPE(ctypes.c_int,ptr);c.search_set_terminate.restype=None;c.search_set_terminate.argtypes=[ptr,ptr,callback_type]
start=time.monotonic();deadline=start+a.seconds
@callback_type
def terminate(_):return int(time.monotonic()>=deadline)
s=c.search_init();c.search_set_option(s,b'quiet',1);c.search_set_terminate(s,None,terminate)
n=0;clauses=[]
def fresh():
 global n
 n+=1;return n
def put(*xs):
 clauses.append(list(xs))
 for x in xs:c.search_add(s,x)
 c.search_add(s,0)
def exactly(xs):
 put(*xs)
 for x,y in itertools.combinations(xs,2):put(-x,-y)
ops=[];sa=[];sb=[]
for i in range(a.gates):
 o=[fresh() for _ in range(3)];aa=[fresh() for _ in range(11+i)];bb=[fresh() for _ in range(11+i)]
 ops.append(o);sa.append(aa);sb.append(bb);exactly(o);exactly(aa);exactly(bb);put(-o[2],bb[0])
 for k in range(11+i):put(o[2],-aa[k],*bb[k:])
notvars=[o[2] for o in ops]
if a.min_not:
 for xs in itertools.combinations(notvars,len(notvars)-a.min_not+1):put(*xs)
for xs in itertools.combinations(notvars,a.max_not+1):put(*[-x for x in xs])
for i in range(a.gates-1):
 put(*[selector[j][11+i] for j in range(i+1,a.gates) for selector in (sa,sb)])
 oi,oj=ops[i][2],ops[i+1][2]
 for k in range(11+i):
  put(-oi,-oj,-sa[i][k],*sa[i+1][k:])
  put(-oi,oj,-sa[i][k],*sb[i+1][k:])
  put(oi,-oj,-sb[i][k],*sa[i+1][k:])
  put(oi,oj,-sb[i][k],*sb[i+1][k:])
if a.seedfile:
 seed=json.loads(Path(a.seedfile).read_text())
 assert len(seed['gates'])==a.gates
 for i,(op,x,y) in enumerate(seed['gates']):
  if op==2:y=0
  else:x,y=sorted((x,y))
  put(ops[i][op]);put(sa[i][x]);put(sb[i][y])
for v in range(1,n+1):c.search_freeze(s,v)
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(x):return any((x>>u&1) and (x>>v&1) for u,v in edges)
rows=set()
def add_row(x):
 assert x not in rows;rows.add(x)
 base=[bool(x>>j&1) for j in range(10)];base.append(base[0] and base[1] if a.edge_op=='and' else base[0] or base[1]);wires=[('constant',v) for v in base]
 for i in range(a.gates):
  va,vb,v=fresh(),fresh(),fresh()
  for sels,u in ((sa[i],va),(sb[i],vb)):
   for sel,(kind,w) in zip(sels,wires):
    if kind=='constant':put(-sel,u if w else -u)
    else:put(-sel,-u,w);put(-sel,u,-w)
  oa,oo,on=ops[i]
  put(-oa,-v,va);put(-oa,-v,vb);put(-oa,v,-va,-vb)
  put(-oo,v,-va);put(-oo,v,-vb);put(-oo,-v,va,vb)
  put(-on,-v,-va);put(-on,v,va)
  wires.append(('variable',v))
 put(wires[-1][1] if target(x) else -wires[-1][1])
for x in range(1024):
 t=target(x)
 critical=all(not target(x^(1<<j)) for j in range(10) if x>>j&1) if t else all(target(x^(1<<j)) for j in range(10) if not x>>j&1)
 if critical:add_row(x)
def pick(vs):
 found=[i for i,v in enumerate(vs) if c.search_val(s,v)>0];assert len(found)==1,found;return found[0]
round_no=0;prefix=Path(a.output_prefix)
try:
 while True:
  round_no+=1;print(json.dumps({'round':round_no,'rows':len(rows),'variables':n,'clauses':len(clauses),'elapsed':time.monotonic()-start}),flush=True)
  verdict=c.search_solve(s);print(json.dumps({'verdict':{0:'UNKNOWN',10:'SAT',20:'UNSAT'}[verdict],'elapsed':time.monotonic()-start}),flush=True)
  if verdict!=10:break
  gates=[(pick(o),pick(x),pick(y)) for o,x,y in zip(ops,sa,sb)];errors=[]
  for x in range(1024):
   w=[bool(x>>j&1) for j in range(10)];w.append(w[0] and w[1] if a.edge_op=='and' else w[0] or w[1])
   for op,u,v in gates:w.append(w[u] and w[v] if op==0 else w[u] or w[v] if op==1 else not w[u])
   if w[-1]!=target(x):errors.append(x)
  result={'gates':gates,'output':10+len(gates),'edge_op':a.edge_op,'truth_table_errors':errors,'size':len(gates),'not_count':sum(op==2 for op,_,_ in gates),'qualifies_for_L_meta_1886_counterexample':not errors and len(gates)<=18}
  prefix.with_name(prefix.name+'-candidate'+str(round_no)+'.json').write_text(json.dumps(result,indent=2));print(json.dumps({'errors':len(errors),'not_count':result['not_count'],'qualifies':result['qualifies_for_L_meta_1886_counterexample']}),flush=True)
  if not errors:break
  for x in sorted(errors,key=lambda x:(x.bit_count(),x))[:64]:add_row(x)
finally:
 with prefix.with_suffix('.cnf').open('w') as f:
  f.write('p cnf '+str(n)+' '+str(len(clauses))+'\n')
  for row in clauses:f.write(' '.join(map(str,row))+' 0\n')
 prefix.with_suffix('.json').write_text(json.dumps({'gates':a.gates,'edge_op':a.edge_op,'min_not':a.min_not,'max_not':a.max_not,'rows':sorted(rows),'variables':n,'clauses':len(clauses),'ops':ops,'a':sa,'b':sb,'ordered_max_parent':True,'live':True,'seconds':time.monotonic()-start},indent=2))
 c.search_release(s)
