from pathlib import Path
import re,json,hashlib,sympy as s
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
base=Path('/tmp/oec/pequalnp-pilot-78');p=base/'numeric/incidence-module/probe.sing';text=p.read_text();source=base/'geometry_search/tracezero_rankdrop/shifted-matrix.json';data=json.loads(source.read_text());R,*vs=ring(','.join(data['variables']),QQ)
parse=lambda x:R.from_expr(s.sympify(x.replace('^','**')))
assert 'matrix A[7][93];' in text
actual={}
for i,j,expr in re.findall(r'A\[(\d+),(\d+)\]=([^;]+);',text):
 key=(int(i),int(j));assert key not in actual;actual[key]=parse(expr)
expected={}
for col,row in enumerate(data['matrix'],1):
 for i,x in enumerate(row,1):expected[(i,col)]=parse(x)
for gi,g in enumerate(data['flat_generators']):
 for i in range(7):expected[(i+1,10+7*gi+i)]=parse(g)
assert all(actual.get((i,j),R.zero)==expected.get((i,j),R.zero) for i in range(1,8) for j in range(1,94))
assert 'module M=module(A);' in text and 'module E=[0,0,0,0,0,0,1];' in text
assert 'matrix C=lift(M,E);' in text and 'matrix residual=matrix(M)*C-matrix(E);' in text
report={'status':'PASS','source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'probe_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'matrix_shape':[7,93],'all651_entries_verified':True,'first9_columns':'Transpose of audited shifted9x7 incidence matrix','last84_columns':'Each of12flat generators times each of7basis vectors, correct column10+7*generator_index+coordinate_index','target':'e7, the constant-coordinate vector','scope':'Encoding and exact-lift residual formula audit only. Modular candidate or zero remainder is not itself an exact polynomial certificate; raw lifted identity must be independently multiplied.'}
(base/'geometry_search/incidence-module-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
