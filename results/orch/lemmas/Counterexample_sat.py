import itertools,json,sys,subprocess,time
from pathlib import Path
n=int(sys.argv[1]);k=int(sys.argv[2]);mode=sys.argv[3]
root=Path('/tmp/oec/pequalnp-pilot-63')
edges=json.loads(Path(sys.argv[4]).read_text()) if len(sys.argv)>4 else [(i,(i+1)%n) for i in range(n)]
truth=[any(x>>u&1 and x>>v&1 for u,v in edges) for x in range(1<<n)]
clauses=[];names={};counter=0
def var(name):
 global counter
 counter+=1;names[counter]=name;return counter
def add(*lits):
 if True in [type(x)==bool and x for x in lits]:return
 lits=tuple(x for x in lits if type(x)!=bool)
 if any(-x in lits for x in lits):return
 clauses.append(lits)
def neg(x):return not x if type(x)==bool else -x
def eq_under(s,z,a):
 add(-s,-z,a);add(-s,z,neg(a))
def or_under(s,z,a,b):
 add(-s,-z,a,b);add(-s,z,neg(a));add(-s,z,neg(b))
def and_under(s,z,a,b):
 add(-s,z,neg(a),neg(b));add(-s,-z,a);add(-s,-z,b)
def iff_or(z,xs):
 add(-z,*xs)
 for x in xs:add(z,neg(x))
def iff_and(z,xs):
 add(z,*(neg(x) for x in xs))
 for x in xs:add(-z,x)
vs=[[var(('value',j,x)) for x in range(1<<n)] for j in range(k)]
andop=[var(('and',j)) for j in range(k)]
dirty=[var(('dirty',j)) for j in range(k)]
anc={(i,j):var(('ancestor',i,j)) for i in range(k) for j in range(i+1,k)}
options=[]
def value(w,x):return bool(x>>w&1) if w<n else vs[w-n][x]
def ancestor(i,w):return False if w<n or w-n<i else True if w-n==i else anc[i,w-n]
for j in range(k):
 opts=[]
 for op in ['and','or']:
  for a,b in itertools.combinations(range(n+j),2):
   s=var(('select',j,op,a,b));opts.append((s,op,a,b))
   for x,z in enumerate(vs[j]):
    (and_under if op=='and' else or_under)(s,z,value(a,x),value(b,x))
   eq_under(s,andop[j],op=='and')
   for i in range(j):or_under(s,anc[i,j],ancestor(i,a),ancestor(i,b))
 add(*(s for s,op,a,b in opts))
 for lhs,rhs in itertools.combinations(opts,2):add(-lhs[0],-rhs[0])
 options.append(opts)
 bad=var(('bad',j));iff_or(bad,[vs[j][x] for x in range(1<<n) if not truth[x]])
 iff_and(dirty[j],[andop[j],bad])
for x,t in enumerate(truth):add(vs[-1][x] if t else -vs[-1][x])
# Every gate must be used downstream (least circuits have this property).
for i in range(k-1):
 add(*(s for j,opts in enumerate(options) if j>i for s,op,a,b in opts if a==n+i or b==n+i))
if mode in ['deep','junk','double']:
 for (i,j),a in anc.items():add(-a,-andop[i],-andop[j],dirty[i])
if mode=='deep':
 witnesses=[]
 for (i,j),a in anc.items():
  w=var(('deep',i,j));iff_and(w,[a,dirty[i],dirty[j]]);witnesses.append(w)
 add(*witnesses)
if mode=='junk':add(*dirty)
tag=Path(sys.argv[4]).stem if len(sys.argv)>4 else str(n)
prefix=root/f'Counterexample_sat_{tag}_{k}_{mode}'
with prefix.with_suffix('.cnf').open('w') as out:
 out.write(f'p cnf {counter} {len(clauses)}\n')
 for c in clauses:out.write(' '.join(map(str,c))+' 0\n')
print('variables',counter,'clauses',len(clauses),flush=True)
with prefix.with_suffix('.solver').open('w') as out:
 result=subprocess.run(['/tmp/oec/pequalnp-pilot-63/toolchain/lean-4.36.0-linux/bin/cadical','-t','180',str(prefix.with_suffix('.cnf'))],stdout=out,stderr=subprocess.STDOUT)
s=prefix.with_suffix('.solver').read_text()
print('exit',result.returncode,flush=True)
model={int(v) for line in s.splitlines() if line.startswith('v ') for v in line[2:].split() if int(v)>0}
if model:
 selected=[dict(j=j,op=op,a=a,b=b) for j,opts in enumerate(options) for sv,op,a,b in opts if sv in model]
 print(json.dumps(selected),flush=True)
 print('dirty',[j for j,d in enumerate(dirty) if d in model],flush=True)
 prefix.with_suffix('.json').write_text(json.dumps(dict(n=n,k=k,mode=mode,edges=edges,circuit=selected,dirty=[j for j,d in enumerate(dirty) if d in model]),indent=2))
