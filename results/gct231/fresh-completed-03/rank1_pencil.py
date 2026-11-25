import sympy as s,itertools
x,y=s.symbols('x y');r=s.sqrt(2)
A=s.Matrix([[0,1,-1,0],[1,0,0,0],[-1,0,0,0],[0,0,0,0]])
B=s.Matrix([[-1-r,0,0,1],[0,0,0,0],[0,0,0,0],[1,0,0,-1+r]])
M=s.ones(4)+x*A+y*B
P=s.expand(sum(s.prod(M[i,p[i]] for i in range(4)) for p in itertools.permutations(range(4)))-24)
assert P==0
assert s.Matrix.hstack(s.Matrix(list(A)),s.Matrix(list(B))).rank()==2
assert s.Matrix.hstack(A.diagonal().T,B.diagonal().T).rank()==1
print('A',A,'B',B,flush=True)
print('PERMANENT_IDENTITY_24; BASIS_RANK_2; DIAGONAL_PROJECTION_RANK_1',flush=True)
