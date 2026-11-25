from pathlib import Path
from fractions import Fraction as F
import json,itertools,random,math
base=Path('/tmp/oec/pequalnp-pilot-78/construct_search');data=json.loads(Path('/tmp/oec/pequalnp-pilot-78/numeric/s4-hadamard/chart.json').read_text())
assert data['variables']==[f'p{i}' for i in range(9)]+[f'b{i}' for i in range(9)]
assert data['matrix_scale']==8 and len(data['polynomials'])==31
Q=[[F(x,2) for x in row] for row in [[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]]
zero=(0,0,0);rng=random.Random(23178)
def mul(A,B):
 C={}
 for a,c in A.items():
  for b,d in B.items():
   m=tuple(x+y for x,y in zip(a,b));C[m]=C.get(m,0)+c*d
 return {m:c for m,c in C.items() if c}
def eval_poly(poly,vals):return sum(c*math.prod(vals[k] for k in mon) for mon,c in poly)
checks=0
for case in range(32):
 vals=[rng.randint(-5,5) for _ in range(18)];P=[vals[i:i+3] for i in [0,3,6]];B=[vals[i:i+3] for i in [9,12,15]]
 mats=[]
 for k in range(3):
  vp=[F(P[i][k]-int(i==k),2) for i in range(3)];op=[F(3*int(i==k)-P[i][k],2) for i in range(3)]
  Tp=[[0,vp[0],vp[1],vp[2]],[vp[0],B[0][k],op[2],op[1]],[vp[1],op[2],B[1][k],op[0]],[vp[2],op[1],op[0],B[2][k]]]
  M=[[8*sum(Q[i][r]*Tp[r][t]*Q[j][t] for r,t in itertools.product(range(4),repeat=2)) for j in range(4)] for i in range(4)]
  assert all(x.denominator==1 for row in M for x in row)
  assert sum(map(sum,M))==0
  mats.append(M)
 entries=[[{zero:F(1)}|{tuple(int(r==k) for r in range(3)):mats[k][i][j] for k in range(3) if mats[k][i][j]} for j in range(4)] for i in range(4)]
 direct={}
 for pm in itertools.permutations(range(4)):
  prod={zero:F(1)}
  for i,j in enumerate(pm):prod=mul(prod,entries[i][j])
  for m,c in prod.items():direct[m]=direct.get(m,0)+c
 assert direct.pop(zero)==24
 assert all(sum(m)>=2 or c==0 for m,c in direct.items())
 for mon,poly in zip(data['parameter_exponents'],data['polynomials']):
  expected=eval_poly(poly,vals)*data['degree_divisors'][str(sum(mon))]
  actual=direct.get(tuple(mon),0)
  assert actual==expected,(case,mon,actual,expected)
  checks+=1
 print('CASE',case,'COEFFICIENT_CHECKS',31)
print('PASS',checks,'EXACT_COEFFICIENT_COMPARISONS','CASES',32)
