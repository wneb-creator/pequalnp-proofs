from pathlib import Path
import json,sys,sympy as s,time
job=Path('/tmp/oec/pequalnp-pilot-79');chart=int(sys.argv[1]);assert chart in [2,3];base='centered-two-macaulay-'+str(chart)+'-d9';start=time.monotonic()
certificate=json.loads((job/(base+'-exact-certificate.json')).read_text());metadata=json.loads((job/(base+'-metadata.json')).read_text());source=(job/('centered-two-coordinate-'+str(chart)+'-rational.msolve')).read_text().splitlines()
names=source[0].split(',');assert names==metadata['variables'] and source[1]=='0';variables=s.symbols(' '.join(names));local=dict(zip(names,variables));body='\n'.join(source[2:]);assert all(c.isalnum() or c in ' _+-*^,()\n' for c in body)
polys=[s.Poly(s.sympify(expr.strip().replace('^','**'),locals=local),*variables,domain=s.ZZ) for expr in body.split(',') if expr.strip()];assert len(polys)==12
coefficients=certificate['coefficients'];origins=metadata['row_origins'];assert len(coefficients)==len(origins);constant=certificate['denominator'];assert isinstance(constant,int) and constant>0
out={}
for coefficient,origin in zip(coefficients,origins):
 assert isinstance(coefficient,int)
 if coefficient==0:continue
 index,mult=origin;assert 0<=index<len(polys) and len(mult)==len(variables) and all(isinstance(e,int) and e>=0 for e in mult)
 for monomial,value in polys[index].terms():
  key=tuple(a+b for a,b in zip(monomial,mult));out[key]=out.get(key,0)+coefficient*int(value)
out={key:value for key,value in out.items() if value}
assert out=={(0,)*len(variables):constant},'original-polynomial identity failed'
# Recompute the chart equations from the symmetric matrix, independently of the matrix file.
x,y=s.symbols('x y');a,b,c,f,e,d=s.symbols('a b c f e d');coords=[a,b,c,f,e,d];pivots=(0,3) if chart==2 else (0,4);substitutions={coords[pivots[0]]:x,coords[pivots[1]]:y};other=[i for i in range(6) if i not in pivots]
for j,index in enumerate(other):substitutions[coords[index]]=variables[2*j]*x+variables[2*j+1]*y
B=s.Matrix([[a,d,e],[d,b,f],[e,f,c]]).subs(substitutions,simultaneous=True);H=s.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]);Z=s.zeros(4);Z[1:4,1:4]=B;T=H*Z*H/4
recomputed=[]
for invariant in [s.trace(B*B),B.per(),T.per()]:
 for coefficient in s.Poly(s.expand(invariant),x,y).coeffs():recomputed.append(s.Poly(coefficient,*variables).clear_denoms()[1].primitive()[1])
assert len(recomputed)==len(polys)
assert all(a.set_domain(s.QQ)==b.set_domain(s.QQ) for a,b in zip(recomputed,polys)), 'chart invariants differ from input equations'
result={'classification':'Exact standalone integer-polynomial verification; not Lean checked','chart':chart,'identity_verified':True,'chart_invariants_verified':True,'certificate_support':sum(c!=0 for c in coefficients),'constant_bits':constant.bit_length(),'seconds':time.monotonic()-start};(job/(base+'-exact-verification.json')).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
