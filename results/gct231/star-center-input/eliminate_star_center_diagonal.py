"""Invertibly reparametrize full-star constraints by eliminating diagonal00."""
from pathlib import Path
import hashlib,json
import sympy as s
root=Path('/tmp/oec/pequalnp-pilot-75/gct231')
source=root/'star-full-grouped-equations.json'
data=json.loads(source.read_text())
old_names=data['unknowns']
old_vars={name:s.Symbol(name) for name in old_names}
n=s.symbols('n0:3');x,y,z=s.symbols('x y z')
namespace={**old_vars,**{str(v):v for v in n},'x':x,'y':y,'z':z}
sub={old_vars[f'd{i}']:-(n[i]+old_vars[f'd{i+3}']+old_vars[f'd{i+6}']+
        2*(1+old_vars[f'o{i}']+old_vars[f'o{i+3}']+old_vars[f'o{i+6}']))
     for i in range(3)}
groups=[[f'd{i+3}',f'd{i+6}',f'n{i}',f'o{i}',f'o{i+3}',f'o{i+6}'] for i in range(3)]
names=sum(groups,[]);variables=[namespace[name] for name in names]
assert len(names)==len(set(names))==18
inverse={n[i]:-(old_vars[f'd{i}']+old_vars[f'd{i+3}']+old_vars[f'd{i+6}']+
         2*(1+old_vars[f'o{i}']+old_vars[f'o{i+3}']+old_vars[f'o{i+6}']))
         for i in range(3)}
for key,value in sub.items():assert s.expand(value.subs(inverse,simultaneous=True)-key)==0
matrix=[[s.expand(s.sympify(entry,locals=namespace).subs(sub,simultaneous=True))
         for entry in row] for row in data['matrix']]
assert s.expand(matrix[3][3]-(n[0]*x+n[1]*y+n[2]*z))==0
assert s.expand(sum(sum(row) for row in matrix))==0
for i in range(4):
    for j in range(4):assert matrix[i][j]==matrix[j][i]
equations=[];term_count=0
for entry in data['equations']:
    old=s.sympify(entry['coefficient'],locals=namespace)
    new=s.Poly(s.expand(old.subs(sub,simultaneous=True)),*variables,domain=s.QQ)
    assert not new.is_zero
    assert s.expand(new.as_expr().subs(inverse,simultaneous=True)-old)==0
    term_count+=len(new.terms())
    equations.append({'monomial':entry['monomial'],'coefficient':str(new.as_expr())})
output={'pivots':data['pivots'],'remaining':data['remaining'],'unknowns':names,
        'matrix':[[str(entry) for entry in row] for row in matrix],
        'equations':equations,'basis_direction_groups':groups,
        'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'forward_substitution':{str(k):str(v) for k,v in sub.items()},
        'inverse_substitution':{str(k):str(v) for k,v in inverse.items()},
        'scope':'Same31 full-star constraints under an invertible affine18-parameter substitution; diagonal00 eliminated and diagonal33 free. OrdinaryDRL grouped by basis direction. No solver verdict.'}
target=root/'star-full-center-eliminated-equations.json'
target.write_text(json.dumps(output,indent=2)+'\n')
print('PASS invertible affine substitution, all16 matrix entries and all31 reverse polynomial identities.',flush=True)
print('VARIABLES',names,'TOTAL_TERMS',term_count,flush=True)
print('SOURCE_SHA256',output['source_sha256'],flush=True)
print('OUTPUT_SHA256',hashlib.sha256(target.read_bytes()).hexdigest(),flush=True)
