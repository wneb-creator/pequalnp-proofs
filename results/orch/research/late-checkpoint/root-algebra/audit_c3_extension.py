from pathlib import Path
import json
import sympy as s

root = Path('/tmp/oec/pequalnp-pilot-78')
w,a,B,c,D,X,Y = s.symbols('w a B c D X Y')
env = {str(v):v for v in (w,a,B,c,D)}
relation = s.Poly(w*w+w+1,w)
def red(expression):
    return s.Poly(s.expand(expression),w).rem(relation).as_expr().expand()
def plus(u,v,b):
    return s.Matrix([[0,u,w*w*u,w*u],[u,v,w*b,w*w*b],
                     [w*w*u,w*b,w*w*v,b],[w*u,w*w*b,b,w*v]])
def minus(u,v,b):
    return plus(u,v,b).subs(w,w*w).applyfunc(red)
U,V = plus(1,a,B),minus(1,c,D)
trivial = [s.diag(1,0,0,0),s.diag(0,1,1,1),
           s.Matrix([[0,1,1,1],[1,0,0,0],[1,0,0,0],[1,0,0,0]]),
           s.Matrix([[0,0,0,0],[0,0,1,1],[0,1,0,1],[0,1,1,0]])]
bases = {'trivial':trivial,'plus':[plus(1,0,0),plus(0,1,0),plus(0,0,1)],
         'minus':[minus(1,0,0),minus(0,1,0),minus(0,0,1)]}
monomials = {'trivial':[(0,0),(1,1),(3,0),(0,3)],
             'plus':[(0,1),(2,0),(1,2)],'minus':[(1,0),(0,2),(2,1)]}
M = s.ones(4)+X*U+Y*V
data = json.loads((root/'construct_search/net_normal_form/c3-extension-blocks.json').read_text())
checked = 0
for name,basis in bases.items():
    for column,W in enumerate(basis):
        derivative = 0
        for mask in range(16):
            selected = [j for j in range(4) if mask & (1<<j)]
            rows = [sum(M[i,j] for j in selected) for i in range(4)]
            wr = [sum(W[i,j] for j in selected) for i in range(4)]
            derivative += (-1)**(4-len(selected))*sum(wr[i]*s.prod(rows[k] for k in range(4) if k!=i) for i in range(4))
        polynomial = s.Poly(red(derivative),X,Y)
        assert set(polynomial.monoms()).issubset(set(monomials[name]))
        for row,(i,j) in enumerate(monomials[name]):
            target = s.sympify(data['blocks'][name][row][column],locals=env)
            assert red(polynomial.coeff_monomial(X**i*Y**j)-target)==0
            checked += 1
slots = [(i,j) for i in range(4) for j in range(i,4)]
all_basis = [W for basis in bases.values() for W in basis]
change = s.Matrix([[W[i,j] for W in all_basis] for i,j in slots])
determinant = red(change.det())
assert determinant != 0 and red(determinant*determinant) != 0
result = {'status':'PASS','method':'Independent differentiated sixteen-subset Ryser formula',
          'block_entries_checked':checked,'all_other_character_coefficients_zero':True,
          'full_symmetric_space_basis_determinant':str(determinant),
          'scope':'Exact unrestricted first-variation blocks; rank nonvanishing requires separate certificates.'}
(root/'root-algebra/c3-extension-independent-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
