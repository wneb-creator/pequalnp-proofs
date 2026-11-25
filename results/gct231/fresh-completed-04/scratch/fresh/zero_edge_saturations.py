import hashlib,itertools,json,sympy as s
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-75/gct231/fresh')
source=base/'zero-edge-pencil.json';data=json.loads(source.read_text())
v=s.symbols(' '.join(data['variables']));x,y=s.symbols('x y');sat=s.Symbol('sat')
T=s.Matrix([[s.sympify(e) for e in row] for row in data['matrix']])
D=s.Matrix([[s.expand(T[i,i]).coeff(x),s.expand(T[i,i]).coeff(y)] for i in range(4)])
eq=list(map(s.sympify,data['equations']))
for i,j in itertools.combinations(range(4),2):
    minor=s.expand(D.extract([i,j],[0,1]).det())
    equations=eq+[s.expand(sat*minor-1)]
    out={'variables':data['variables']+['sat'],'equations':list(map(str,equations)),
         'base_source':str(source),'base_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
         'diagonal_rows':[i,j],'diagonal_minor':str(minor),'scope':'Saturation diagnostic for rank-two diagonal image in the normalized zero-edge pencil chart; no unit-ideal claim.'}
    target=base/f'zero-edge-saturated-minor-{i}{j}.json';target.write_text(json.dumps(out,indent=2))
    print('EXPORTED',target.name,'VARS',len(out['variables']),'EQUATIONS',len(equations),'TERMS',sum(len(s.Poly(e,*v,sat).terms()) for e in equations),'MINOR',minor,'SHA256',hashlib.sha256(target.read_bytes()).hexdigest(),flush=True)
print('DIAGONAL_COEFFICIENT_MATRIX',D,flush=True)
