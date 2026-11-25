from pathlib import Path
from itertools import combinations
import sympy as S
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
import json,time,resource,random,sys
resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(60,65))
start=time.monotonic()
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
data=json.loads(Path('/tmp/oec/pequalnp-pilot-78/geometry_search/tracezero_rankdrop/matrix.json').read_text())
shifted='--shifted' in sys.argv
variables=[x.replace('p','r') if x.startswith('p') else x for x in data['variables']] if shifted else data['variables']
R,*gens=ring(','.join(variables),QQ)
shift={S.Symbol('p'+str(i)):S.Symbol('r'+str(i)) for i in range(6)} if shifted else {}
if shifted:
 shift[S.Symbol('p0')]+=3;shift[S.Symbol('p3')]+=3
 shift[S.Symbol('p4')]+=3*S.Symbol('k');shift[S.Symbol('p5')]+=3*S.Symbol('l')
original=[[R.from_expr(S.sympify(x).subs(shift,simultaneous=True)) for x in row] for row in data['matrix'][:5]]
N=[[row[0],row[1],row[2],row[3]-row[5],row[4]-row[5],row[6]] for row in original]
if shifted:
 for row in N:row[5]+=3*row[2]
for i in (2,4):N[i]=[x*QQ(1,2) for x in N[i]]
dp={():R.one}
for row in range(5):
 new={}
 for cols in combinations(range(6),row+1):
  value=R.zero
  for j,col in enumerate(cols):
   value+=(-1)**(row+j)*N[row][col]*dp[cols[:j]+cols[j+1:]]
  new[cols]=value
 dp=new
 print('DP_LAYER',row+1,'polynomials',len(dp),'total_terms',sum(len(x) for x in dp.values()),flush=True)

def evalmod(poly,values,p):
 total=0
 for mon,coeff in poly.items():
  c=int(coeff.numerator)*pow(int(coeff.denominator),-1,p)
  for x,n in zip(values,mon): c=c*pow(x,n,p)%p
  total=(total+c)%p
 return total
def detmod(a,p):
 a=[row[:] for row in a];det=1
 for i in range(len(a)):
  pivot=next((j for j in range(i,len(a)) if a[j][i]%p),None)
  if pivot is None:return 0
  if pivot!=i:a[i],a[pivot]=a[pivot],a[i];det=-det
  v=a[i][i]%p;det=det*v%p
  inv=pow(v,-1,p)
  for j in range(i+1,len(a)):
   c=a[j][i]*inv%p
   a[j]=[(x-c*y)%p for x,y in zip(a[j],a[i])]
 return det%p
rng=random.Random(78231)
for p in (101,103):
 for _ in range(10):
  point=[rng.randrange(p) for _ in gens]
  numerical=[[evalmod(x,point,p) for x in row] for row in N]
  for cols,poly in dp.items():
   assert evalmod(poly,point,p)==detmod([[row[j] for j in cols] for row in numerical],p)
results=[]
for cols,poly in sorted(dp.items(),key=lambda item:len(item[1])):
 results.append({'columns':cols,'omitted_column':next(i for i in range(6) if i not in cols),'term_count':len(poly),'total_degree':max(sum(m) for m in poly),'polynomial':str(poly.as_expr())})
report={'status':'PASS','coordinate_change':'B_W=(R0+tau,R1+tau,-R0-R1+tau), trace=3tau','trace_zero_coordinates':['P_W0','P_W1','P_W2','R0','R1','D_W2'],'matrix':[[str(x.as_expr()) for x in row] for row in N],'row_divisors':[1,1,2,1,2],'minors':results,'independent_modular_determinant_checks':120,'shifted':shifted,'shifted_base_variables':variables,'extra_shift':'p0=r0+3,p3=r3+3,p4=r4+3k,p5=r5+3l,p1=r1,p2=r2; P_W2=R_W2+3D_W2' if shifted else None,'scope':'The six minors cover rank5 of the trace-zero restriction. Their non-simultaneous vanishing on the valid-plane scheme remains to be proved; no global pivot assumption is made.','seconds':time.monotonic()-start}
name='trace-rankdrop-shifted-pivots.json' if shifted else 'trace-rankdrop-small-pivots.json'
(base/name).write_text(json.dumps(report,indent=2)+'\n')
print('MINOR_SUMMARY',json.dumps([{k:v for k,v in x.items() if k!='polynomial'} for x in results]),flush=True)
print('SECONDS',time.monotonic()-start,flush=True)
