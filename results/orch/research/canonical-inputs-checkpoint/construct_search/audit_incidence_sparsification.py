from pathlib import Path
import sympy as S, json, hashlib, resource, time
resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(30,35))
b=Path('/tmp/oec/pequalnp-pilot-78');root=b/'geometry_search';job=root/'tracezero_rankdrop';start=time.monotonic()
source=json.loads((job/'shifted-matrix.json').read_text());old=json.loads((job/'matrix.json').read_text());full=json.loads((job/'full31-shifted.json').read_text());data=json.loads((root/'incidence-row-sparsification.json').read_text())
v=S.symbols(' '.join(source['variables']));loc=dict(zip(source['variables'],v));parse=lambda z:S.sympify(z,locals=loc);M=S.Matrix([[parse(z) for z in row] for row in source['matrix']]);p0,p1,p2,p3,p4,p5,b0,b1,b2,b3,k,l=v
s,t=S.symbols('s t');D=S.Matrix([s,t,k*s+l*t]);R=S.Matrix([p0*s+p1*t,p2*s+p3*t,p4*s+p5*t]);F=S.Poly(S.expand(D.dot(R)/2+3*D.dot(D)/4),s,t);fc=[F.coeff_monomial(s**(2-i)*t**i) for i in range(3)]
w=S.symbols('w0:7');dw=S.Matrix([0,0,w[6]]);rw=S.Matrix(w[:3]);derivative=S.expand((dw.dot(R)+D.dot(rw))/2+3*D.dot(dw)/2);dF=S.Matrix([[S.expand(derivative).coeff(z).coeff(s),S.expand(derivative).coeff(z).coeff(t)] for z in w])
assert dF==S.Matrix([[parse(z) for z in row] for row in data['F_derivative_coefficients']])
actual={tuple(e):parse(g)*parse(scale) for e,g,scale in zip(full['parameter_exponents'],full['generators'],full['scales_to_actual_permanent_coefficients'])}
Q=[actual[2-i,i,0] for i in range(3)];C=[actual[3-i,i,0] for i in range(4)]
for expected,reported in zip(Q,data['Q_binary_coefficients']):assert S.expand(expected-parse(reported))==0
for expected,reported in zip(C,data['C_binary_coefficients']):assert S.expand(expected-parse(reported))==0
flat=[S.Poly(parse(z),*v) for z in source['flat_generators']]
for n in (2,3,4):
 for i in range(n+1):
  f=S.Poly(S.expand(actual[n-i,i,0]),*v)
  assert any(S.expand(f.as_expr()-g.as_expr()*f.LC()/g.LC())==0 for g in flat)
for trial in data['trials']:
 N=S.Matrix([[parse(z) for z in row] for row in trial['matrix']]);assert N[:5,:]==M[:5,:]
 for i in range(4):
  scale=parse(trial['new_quartic_row_scales_to_actual'][i]);assert scale.is_Rational and scale!=0
  for j in range(7):
   expected=M[5+i,j]*parse(old['row_scale_to_actual_derivative'][5+i])
   for h in range(2):
    z=i-h
    if 0<=z<3:
     f=fc[z]+(Q[z]/8 if trial['label']!='subtract_Fq' else 0)
     expected-=f*M[h,j]*parse(old['row_scale_to_actual_derivative'][h])
     if trial['label']=='compact_mod_flat':expected-=Q[z]*dF[j,h]
   if trial['label']=='compact_mod_flat' and j in (3,4,5):expected-=C[i]/4
   assert S.expand(expected-scale*N[5+i,j])==0,(trial['label'],i,j)
report={'verdict':'PASS independent exact row-transformation audit','quartic_entry_identities':84,'flat_coefficient_equivalences':12,'first_five_rows_unchanged':True,'scope':'All three transformed matrices have identical ranks on the permanent-flat locus; first two are equivalent for every parameter value. No rank or infeasibility conclusion.','source_sha256':hashlib.sha256((root/'incidence-row-sparsification.json').read_bytes()).hexdigest(),'seconds':time.monotonic()-start}
(b/'construct_search/incidence-sparsification-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
