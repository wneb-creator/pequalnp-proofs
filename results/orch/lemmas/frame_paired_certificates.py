from pathlib import Path
import sympy as s,json,itertools,resource,time
from sympy.polys.matrices import DomainMatrix
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120))
job=Path('/tmp/oec/pequalnp-pilot-79');cases=json.loads((job/'frame-paired-cases.json').read_text());r=s.Symbol('r');started=time.monotonic();results=[]
def mons(n,d):
 if n==1:yield(d,);return
 for i in range(d+1):
  for m in mons(n-1,d-i):yield(i,)+m
for case in cases:
 variables=s.symbols(' '.join(case['variables']));scope=dict(zip(case['variables'],variables));scope['r']=r;qs=[s.sympify(q,locals=scope) for q in case['quadratics']];found=False
 for degree in [2,3,4]:
  allmons=[m for d in range(degree+1) for m in mons(len(variables),d)];columns=[(m,j) for m in allmons for j in [0,1]];ci={m:i for i,m in enumerate(columns)};origins=[];rows=[]
  for qi,q in enumerate(qs):
   qdegree=s.Poly(q,*variables).total_degree()
   for d in range(degree-qdegree+1):
    for mult in mons(len(variables),d):
     for parity in [0,1]:
      expr=s.rem(s.expand(q*s.prod(v**e for v,e in zip(variables,mult))*r**parity),r*r-2,r);terms=s.Poly(expr,*variables,r).terms();row={ci[(tuple(m[:-1]),m[-1])]:c for m,c in terms if c};rows.append(row);origins.append([qi,list(mult),parity])
  target=[s.Integer(1) if m==(0,)*len(variables) and j==0 else s.Integer(0) for m,j in columns]
  matrix=[[row.get(i,s.Integer(0)) for row in rows]+[target[i]] for i in range(len(columns))];before=time.monotonic();dm=DomainMatrix.from_list_sympy(len(matrix),len(matrix[0]),matrix).convert_to(s.QQ);rr,pivots=dm.rref();ok=len(rows) not in pivots;summary={'signs':case['signs'],'degree':degree,'rows':len(rows),'columns':len(columns),'rank':len(pivots),'constant_member':ok,'seconds':time.monotonic()-before};print(json.dumps(summary),flush=True)
  if not ok:continue
  reduced=rr.to_Matrix();weights=[s.Integer(0)]*len(rows)
  for index,pivot in enumerate(pivots):weights[pivot]=reduced[index,len(rows)]
  check=[sum(w*row.get(i,0) for w,row in zip(weights,rows) if w) for i in range(len(columns))];assert check==target
  cert=[{'origin':origin,'numerator':int(w.p),'denominator':int(w.q)} for w,origin in zip(weights,origins) if w];summary['support']=len(cert);summary['max_bits']=max(max(abs(z['numerator']).bit_length(),z['denominator'].bit_length()) for z in cert);results.append({'case':case,'status':summary,'certificate':cert});found=True;break
 if not found:results.append({'case':case,'status':{'constant_member':False}})
 (job/'frame-paired-exact-certificates.json').write_text(json.dumps({'classification':'exact rational identities modulo r^2-2 for conditional paired-root cases; base cubic implications remain unproved','cases':results,'seconds':time.monotonic()-started},indent=2)+'\n')
