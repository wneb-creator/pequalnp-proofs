from datetime import datetime,timezone
from itertools import combinations
import json
from pathlib import Path
import sympy as s

base=Path(__file__).resolve().parent
x,y=s.symbols('x y');r=s.sqrt(2)
def ryser(M):
 n=M.rows
 return s.expand(sum((-1)**(n-mask.bit_count())*s.prod(sum(M[i,j] for j in range(n) if mask>>j&1) for i in range(n)) for mask in range(1,1<<n)))
def polar(A,B):
 M=s.ones(4)+x*A+y*B
 columns=[]
 mons=[(i,d-i) for d in range(4) for i in range(d+1)]
 for i in range(4):
  for j in range(i,4):
   minor=M.minor_submatrix(i,j)
   p=s.Poly((1 if i==j else 2)*ryser(minor),x,y)
   columns.append(s.Matrix([p.coeff_monomial(x**a*y**b) for a,b in mons]))
 return s.Matrix.hstack(*columns)
def matrix_edges(values):
 A=s.zeros(4)
 for (i,j),v in zip(combinations(range(4),2),values):A[i,j]=A[j,i]=v
 return A
def stable_transpositions(A,B):
 V=s.Matrix.hstack(s.Matrix(list(A)),s.Matrix(list(B)))
 result=[]
 for i,j in combinations(range(4),2):
  p=list(range(4));p[i],p[j]=p[j],p[i]
  AT=s.Matrix(4,4,lambda a,b:A[p[a],p[b]])
  BT=s.Matrix(4,4,lambda a,b:B[p[a],p[b]])
  if V.row_join(s.Matrix(list(AT))).row_join(s.Matrix(list(BT))).rank()==2:result.append((i,j))
 return result
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
aa,bb=s.symbols('a b')
Ag=matrix_edges([1,0,0,-2,1,0])
Bg=s.Matrix([[aa,0,0,1],[0,0,0,0],[0,0,0,0],[1,0,0,bb]])
general=ryser(s.ones(4)+x*Ag+y*Bg)-24
assert s.expand(general-((aa+bb+2)*(x*x-4*x+6)*y+(aa*bb+1)*(4*x*x-4*x+2)*y*y))==0
print('GENERAL_IDENTITY (a+b+2)(x^2-4x+6)y+(ab+1)(4x^2-4x+2)y^2',flush=True)
B=s.Matrix([[-1-r,0,0,1],[0,0,0,0],[0,0,0,0],[1,0,0,-1+r]])
cases={
 'center0_difference':(matrix_edges([-1,1,0,0,0,0]),B),
 'center3_difference':(matrix_edges([0,0,0,0,-1,1]),B),
 'center1_triple':(matrix_edges([1,0,0,-2,1,0]),B),
 'center2_triple':(matrix_edges([0,1,0,-2,0,1]),B),
}
D=s.Matrix([[r-1,1],[1,-r-1]])
cases['two_block_diagonal_rank2']=(s.diag(D,s.zeros(2)),s.diag(s.zeros(2),D))
results={}
for name,(A,B) in cases.items():
 assert ryser(s.ones(4)+x*A+y*B)==24
 assert s.Matrix.hstack(s.Matrix(list(A)),s.Matrix(list(B))).rank()==2
 K=polar(A,B)
 rank=K.rank();stable=stable_transpositions(A,B)
 diag_rank=s.Matrix.hstack(A.diagonal().T,B.diagonal().T).rank()
 print(name,'polar_rank',rank,'diagonal_rank',diag_rank,'stable_transpositions',stable,flush=True)
 results[name]={'A':[[str(v) for v in A.row(i)] for i in range(4)],
                'B':[[str(v) for v in B.row(i)] for i in range(4)],
                'polar_matrix':[[str(v) for v in K.row(i)] for i in range(10)],
                'polar_rank':rank,'diagonal_rank':diag_rank,'stable_transpositions':stable}
(base/'rank-check-results.json').write_text(json.dumps(results,indent=2)+'\n')
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
