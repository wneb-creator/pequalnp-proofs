from pathlib import Path
import ast,hashlib,json,re
import sympy as s
b=Path('/tmp/oec/pequalnp-pilot-75/gct231');out=Path(__file__).parent
src=b/'C4Case2ModularCoprimeList11.lean';raw=src.read_bytes();text=raw.decode();digest=hashlib.sha256(raw).hexdigest()
assert digest=='548488ed6cdac516542dbe0e73e2a1661d1c3d5e1503b8f10dfe77369402f767'
data=json.loads((b/'c4-case2-modular-coprime-p11.json').read_text());P=s.Symbol('P')
def coeffs(t):return [int(c) for c in reversed(s.Poly(s.sympify(t,locals={'P':P}),P,domain=s.ZZ).all_coeffs())]
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def mul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]+=x*y
 return trim(z)
def add(a,b):
 z=[0]*max(len(a),len(b))
 for i,c in enumerate(a):z[i]+=c
 for i,c in enumerate(b):z[i]+=c
 return trim(z)
lists=[ast.literal_eval('['+m+']') for m in re.findall(r'polynomialOfCoeffs \(\[([-0-9, ]+)\]',text)]
assert len(lists)==7 and all(all(type(v)==int for v in a) for a in lists)
keys=['original_f','original_g','mod_f','mod_g','mod_a','mod_b','integer_quotient']
assert lists==[coeffs(data[k]) for k in keys]
f,g,fm,gm,a,c,h=lists
assert data['prime']==11 and [len(f)-1,len(g)-1]==data['degrees']==[54,82]
assert fm==[v%11 for v in f] and gm==[v%11 for v in g]
assert [fm[-1],gm[-1]]==data['modular_leading_coefficients']==[1,6]
assert add(mul(a,fm),mul(c,gm))==add([1],[11*x for x in h])
old=json.loads((b/'c4-case2-projective-cofactors.json').read_text())
assert [f,g]==[coeffs(t) for t in old['cofactors']]
assert not re.search(r'_root_|"|\bsorry\b|\baxiom\b|native_decide|\binitialize\b|\belab\b|\bunsafe\b|@\[|#',text)
assert 'case2_cofactor_degree_bounds' in text and 'case2_modular_degrees' in text and 'case2_modular_coprime' in text
result={'status':'PASS_ACTUAL_LEAN_LISTS_AND_EXACT_INTEGER_BEZOUT_IDENTITY','source_sha256':digest,'source_bytes':len(raw),'data_sha256':hashlib.sha256((b/'c4-case2-modular-coprime-p11.json').read_bytes()).hexdigest(),'degrees':[54,82],'modular_leading_coefficients':[1,6],'coefficient_lists':7,'scope':'The actual119-line file proves coefficient maps, degree bounds/preservation, and coprimality of two explicit cofactor polynomials modulo11. It does not itself contain the norm-implication wrapper or original-chart bridge. Source review only; compile/audit separate. Two outer namespaces make it a scratch component requiring namespace integration before any PR use.'}
(out/'verdict.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
