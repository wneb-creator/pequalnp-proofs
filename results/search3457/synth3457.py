import argparse,itertools,json,resource,subprocess,time,gc
from pathlib import Path

ap=argparse.ArgumentParser();ap.add_argument('--N',type=int,default=3);ap.add_argument('--gates',type=int,default=7);ap.add_argument('--mask',type=int,default=238);ap.add_argument('--seconds',type=int,default=60);ap.add_argument('--clean',action='store_true');ap.add_argument('--sym-c6',action='store_true');ap.add_argument('--sym-auto',action='store_true');ap.add_argument('--critical',action='store_true');ap.add_argument('--and-count',type=int);ap.add_argument('--colex',action='store_true');ap.add_argument('--edge-useful',action='store_true');args=ap.parse_args()
N=args.N;n=N*2;k=args.gates;mask=args.mask
edges=[(p,N+l) for p in range(N) for l in range(N) if mask>>(p*N+l)&1]
def expected(r):return any(r>>p&1 and r>>l&1 for p,l in edges)
if args.critical:
 aset={1<<i for i in range(n)}|{(1<<p)|(1<<l) for p,l in edges}
 aset|={r for r in range(1<<n) if not expected(r) and all(expected(r|(1<<i)) for i in range(n) if not r>>i&1)}
 if args.clean:aset|={(1<<p)|(1<<(N+l)) for p in range(N) for l in range(N)}
 assignments=sorted(aset)
else:assignments=list(range(1<<n))
rows=len(assignments)
folder=Path('/tmp/oec/pequalnp-pilot-53/search');stem=f'n{N}-m{mask}-k{k}-'+('clean' if args.clean else 'dirty')+('-critical' if args.critical else '')+(f'-ands{args.and_count}' if args.and_count is not None else '')+('-colex' if args.colex else '')+('-useful' if args.edge_useful else '')
clauses=[];nv=0
def var():
 global nv
 nv+=1;return nv
def clause(*xs):
 if True in [x for x in xs if isinstance(x,bool)]:return
 c=[x for x in xs if not isinstance(x,bool)]
 clauses.append(c)
def neg(x):return not x if isinstance(x,bool) else -x
def implies_eq(cond,a,b):
 clause(-cond,neg(a),b);clause(-cond,a,neg(b))
def exactly_one(xs):
 clause(*xs)
 for a,b in itertools.combinations(xs,2):clause(-a,-b)
truth=[[bool(r>>i&1) for r in assignments] for i in range(n)]
target=[expected(r) for r in assignments]
gates=[]
for i in range(k):
 selectors=[[var() for _ in range(n+i)] for _ in range(2)]
 for ss in selectors:exactly_one(ss)
 for a in range(n+i):
  for b in range(a+1):clause(-selectors[0][a],-selectors[1][b])
 op=var();av=[var() for _ in range(rows)];bv=[var() for _ in range(rows)];gv=[var() for _ in range(rows)]
 for s,outs in zip(selectors,[av,bv]):
  for j,sel in enumerate(s):
   for r in range(rows):implies_eq(sel,outs[r],truth[j][r])
 for r,(a,b,g) in zip(assignments,zip(av,bv,gv)):
  clause(-op,-g,a);clause(-op,-g,b);clause(-op,g,-a,-b)
  clause(op,g,-a);clause(op,g,-b);clause(op,-g,a,b)
  if r.bit_count()==1:clause(-op,-g)
  if args.clean and r.bit_count()==2:
   ps=[p for p in range(N) if r>>p&1];ls=[l for l in range(N) if r>>(N+l)&1]
   if ps and ls and not(mask>>(ps[0]*N+ls[0])&1):clause(-op,-g)
 truth.append(gv);gates.append((selectors,op,gv))
 if args.edge_useful:clause(-op,*(gv[j] for j,r in enumerate(assignments) if r.bit_count()==2 and expected(r)))
for r,v in enumerate(gates[-1][2]):clause(v if target[r] else -v)
for i in range(k-1):clause(*(gates[j][0][s][n+i] for j in range(i+1,k) for s in range(2)))
if args.colex:
 for i in range(k-1):
  sa,sb=gates[i][0];ta,tb=gates[i+1][0]
  for b in range(len(sb)):
   for d in range(b):clause(-sb[b],-tb[d])
   for a in range(b):
    for c in range(a):clause(-sb[b],-tb[b],-sa[a],-ta[c])
if args.and_count is not None:
 ops=[g[1] for g in gates]
 for xs in itertools.combinations(ops,args.and_count+1):clause(*(-v for v in xs))
 for xs in itertools.combinations(ops,k-args.and_count+1):clause(*xs)
if args.sym_c6:
 assert N==3 and mask==238
 clause(gates[0][0][0][0]);clause(*(gates[0][0][1][j] for j in [1,3,4]))
if args.sym_auto:
 perms=list(itertools.permutations(range(N)));edge_set=set(edges);auts=[]
 for pr in perms:
  for pc in perms:
   p=list(pr)+[N+x for x in pc]
   if {(p[a],p[b]) for a,b in edges}==edge_set:auts.append(p)
   p=[N+x for x in pr]+list(pc)
   if {(p[b],p[a]) for a,b in edges}==edge_set:auts.append(p)
 reps=set()
 for a,b in itertools.combinations(range(n),2):
  rep=min((tuple(sorted((p[a],p[b]))) for p in auts),key=(lambda x:(x[1],x[0])) if args.colex else (lambda x:x))
  reps.add(rep)
  if (a,b)!=rep:clause(-gates[0][0][0][a],-gates[0][0][1][b])
 print('graph automorphisms',len(auts),'first pair reps',sorted(reps),flush=True)
cnf=folder/(stem+'.cnf')
with cnf.open('w') as f:
 f.write(f'p cnf {nv} {len(clauses)}\n')
 for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
(folder/(stem+'.mapping.json')).write_text(json.dumps({'N':N,'k':k,'mask':mask,'gates':gates,'target':target,'assignments':assignments}))
print('CNF',stem,'rows',rows,'vars',nv,'clauses',len(clauses),flush=True)
clauses.clear();gc.collect()
(folder/(stem+'.sol')).unlink(missing_ok=True)
def limit():resource.setrlimit(resource.RLIMIT_AS,(256*1024*1024,256*1024*1024))
with (folder/(stem+'.solver.stdout')).open('w') as out,(folder/(stem+'.solver.stderr')).open('w') as err:
 try:
  run=subprocess.run(['/tmp/oec/pequalnp-pilot-53/elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical','-t',str(args.seconds),'-w',str(folder/(stem+'.sol')),str(cnf)],stdout=out,stderr=err,preexec_fn=limit,timeout=args.seconds+5)
  returncode=run.returncode
 except subprocess.TimeoutExpired:
  returncode='wall_timeout'
  print('External wall timeout; no solver verdict implied',flush=True)
print('exit',returncode,flush=True)
sol=(folder/(stem+'.sol')).read_text() if (folder/(stem+'.sol')).exists() else ''
print(sol[:100],flush=True)
if sol.startswith('s SATISFIABLE'):
 vals={int(x) for line in sol.splitlines() if line.startswith('v ') for x in line[2:].split() if int(x)>0}
 chosen=[];tables=truth[:n]
 for i,(ss,op,_) in enumerate(gates):
  a=next(j for j,v in enumerate(ss[0]) if v in vals);b=next(j for j,v in enumerate(ss[1]) if v in vals);isand=op in vals
  table=[(x and y) if isand else (x or y) for x,y in zip(tables[a],tables[b])]
  assert not isand or all(not table[assignments.index(1<<j)] for j in range(n))
  tables.append(table);chosen.append(['and' if isand else 'or',a,b])
 assert tables[-1]==target
 for r in range(1<<n):
  ws=[bool(r>>i&1) for i in range(n)]
  for op,a,b in chosen:ws.append(ws[a] and ws[b] if op=='and' else ws[a] or ws[b])
  assert ws[-1]==expected(r)
 (folder/(stem+'.witness.json')).write_text(json.dumps(chosen,indent=2)+'\n')
 print(json.dumps(chosen),flush=True)
