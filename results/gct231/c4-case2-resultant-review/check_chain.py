from pathlib import Path
import hashlib,json,resource,time,sys
import sympy as s
resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,768*1024**2))
base=Path('/workspace/pequalnp-proofs/results/gct231/c4-case2-resultants')
start=time.monotonic()
def say(*x):print(round(time.monotonic()-start,3),*x,flush=True)
entries={}
for line in (base/'SHA256SUMS').read_text().splitlines():
 h,n=line.split('  ',1);entries[n]=h
 assert hashlib.sha256((base/n).read_bytes()).hexdigest()==h
assert {str(p.relative_to(base)) for p in base.rglob('*') if p.is_file()}==set(entries)|{'SHA256SUMS'}
say('ARCHIVE EXACT COVERAGE AND HASHES PASS',len(entries),hashlib.sha256((base/'SHA256SUMS').read_bytes()).hexdigest())
P,B,U,V,sat=s.symbols('P B U V sat');env={str(x):x for x in (P,B,U,V,sat)}
def parse(x):return s.sympify(x,locals=env)
source=json.loads((base/'original-six-equations.json').read_text());eq=list(map(parse,source['equations']))
F=eq[2];K=P**2+P-1;W=9*B**2-6*B*P**2-12*B+10*P**2
assert s.expand(eq[5]-(B*P*sat*W-1))==0
assert s.expand(F-(K*(-6*B**2+(5*P**2-P+10)*B-8*P**2)-3*P*B))==0
say('SATURATION AND K IDENTITY PASS')
datasets=[]
for filename in ['c4-case2-resultants.json','c4-case2-reverse-resultants.json']:
 d=json.loads((base/filename).read_text());assert d['source']==source
 rows={r['label']:r for r in d['reductions']};polys={k:parse(r['polynomial']) for k,r in rows.items()}
 for label,r in rows.items():
  den=s.Poly(parse(r['denominator']),P,domain=s.QQ)
  while den.degree()>0:
   den,rem=den.div(s.Poly(K,P));assert rem.is_zero,(label,r['denominator'])
  assert den.as_expr()!=0 and r['removed_nonzero_factors']==[]
 say('ALL DENOMINATORS CONSTANT TIMES POWERS OF K; NO FACTORS REMOVED',filename)
 datasets.append((rows,polys))

# Work in the polynomial ring, using pseudo-remainders.  Multiplication by
# the nonzero leading coefficient of F only changes a nonzero scalar power.
# Compare the primitive polynomial remainder with the archived primitive row.
domain=s.QQ.poly_ring(P,U,V)
mod=s.Poly(F,B,domain=domain)
def primitive(x):
 p=s.Poly(x,P,B,U,V,domain=s.QQ)
 return p.clear_denoms()[1].primitive()[1].monic()
def verify_reduction(expression,target,label):
 rem=s.Poly(expression,B,domain=domain).prem(mod)
 # Remove the powers of K introduced by pseudo-division, then compare
 # coefficient ratios over QQ(P), since the archived denominator may cancel.
 expected=s.Poly(target,B,U,V,domain=s.QQ.frac_field(P))
 actual=s.Poly(rem.as_expr(),B,U,V,domain=s.QQ.frac_field(P))
 ratio=actual.LC()/expected.LC()
 assert actual==expected.mul_ground(ratio),label
 num,den=s.fraction(s.cancel(ratio))
 for value in [num,den]:
  p=s.Poly(value,P,domain=s.QQ)
  while p.degree()>0:
   p,r=p.div(s.Poly(K,P));assert r.is_zero,(label,s.factor(value))
  assert p.as_expr()!=0
 say('EXACT REDUCTION PASS',label)

for direction,(rows,polys) in ([] if '--tail-only' in sys.argv else enumerate(datasets)):
 first,second=(U,V) if direction==0 else (V,U)
 for label,index in [('q',0),('c',1),('linear_r',3),('quadratic_l',4)]:
  verify_reduction(eq[index],polys[label],str(direction)+':'+label)
 r=s.Poly(polys['linear_r'],first);assert r.degree()==1
 a,b=r.all_coeffs();outs=[]
 for label,name in [('q','q'),('c','c'),('quadratic_l','l')]:
  f=s.Poly(polys[label],first);n=f.degree()
  # Direct homogeneous evaluation of a linear resultant: no division by a.
  resultant=sum(coef*(-b)**i*a**(n-i) for (i,),coef in f.terms())
  key='eliminate_'+str(first)+'_'+name
  verify_reduction(s.expand(resultant),polys[key],str(direction)+':'+key)
  outs.append(polys[key])
 for i,j in [(0,1),(0,2),(1,2)]:
  key='eliminate_'+str(second)+'_'+str(i)+str(j)
  # A Sylvester determinant (fraction-free polynomial arithmetic) independently
  # reconstructs this necessary resultant. No root or leading coefficient division.
  f=s.Poly(outs[i],second);g=s.Poly(outs[j],second);m=f.degree();n=g.degree()
  coeff_f=f.all_coeffs();coeff_g=g.all_coeffs()
  matrix=s.zeros(m+n)
  for k in range(n):
   for z,c in enumerate(coeff_f):matrix[k,k+z]=c
  for k in range(m):
   for z,c in enumerate(coeff_g):matrix[n+k,k+z]=c
  result=matrix.det(method='domain-ge')
  verify_reduction(result,polys[key],str(direction)+':'+key)
say('NECESSARY RESULTANT PHASE '+('SKIPPED: USE PRIOR FULL PHASE LOG' if '--tail-only' in sys.argv else 'PASS'))

norm_rows=json.loads((base/'c4-case2-norm-gcd.json').read_text())+json.loads((base/'c4-case2-combined-norm-gcd.json').read_text())
fa,fb,fc=[s.Poly(c,P,domain=s.QQ) for c in s.Poly(F,B).all_coeffs()]
Q=s.Poly(P**4-2*P**3+4*P+2,P,domain=s.QQ);G=s.Poly((P+2)**2,P)*Q**22
cofactors=[]
for k,row in enumerate(norm_rows):
 target=datasets[0 if k<3 else 1][1][row['label']]
 p=s.Poly(target,B);assert p.degree()==1
 a,b=[s.Poly(v,P,domain=s.QQ) for v in p.all_coeffs()]
 norm=(fa*b*b-fb*a*b+fc*a*a).primitive()[1]
 for factor in row['removed_nonzero_factors']:
  fac=s.Poly(parse(factor),P,domain=s.QQ);assert fac.as_expr() in [P,K]
  norm,rem=norm.div(fac);assert rem.is_zero
 assert norm==s.Poly(parse(row['norm']),P,domain=s.QQ)
 co,rem=norm.div(G);assert rem.is_zero
 cofactors.append(co.clear_denoms()[1].primitive()[1])
 say('EXACT NORM AND COMMON FACTOR PASS',row['label'],norm.degree(),co.degree())
prime=1009
reduced=[]
for co in cofactors:
 assert int(co.LC())%prime!=0
 reduced.append(s.Poly(co.as_expr(),P,modulus=prime))
common=reduced[0]
for co in reduced[1:]:common=common.gcd(co)
assert common.degree()==0
say('GCD EXACT OVER QQ: G divides all four norms and primitive cofactors are coprime mod1009 with nonvanishing leading coefficients')

finish=json.loads((base/'c4-case2-finish.json').read_text())
e=parse(finish['necessary_remainder_primitive']);a=parse(finish['multiplier_a']);L=3*B+P**3-2*P**2
raw=datasets[0][1]['eliminate_V_01']
rem=s.Poly(raw,P,domain=s.QQ.poly_ring(B)).rem(s.Poly(Q.as_expr(),P,domain=s.QQ.poly_ring(B))).as_expr()
assert primitive(rem)==primitive(e)
assert s.expand(e-a*L-Q.as_expr()*parse(finish['remainder_quotient']))==0
assert s.expand(a*parse(finish['a_inverse_mod_Q'])+Q.as_expr()*parse(finish['a_bezout_Q'])-1)==0
assert s.expand(W.subs(B,(2*P**2-P**3)/3)-P**2*Q.as_expr())==0
assert s.expand(F.subs(P,-2)+2*(B-1)*(3*B-16))==0
for branch in finish['point_branches']:
 val=parse(branch['B'])
 expected=[parse(x) for x in branch['equations']]
 actual=[f.subs({P:-2,B:val}) for i,f in enumerate(eq) if i!=2]
 assert all(s.expand(x-y)==0 for x,y in zip(actual,expected))
assert all(s.expand(f.subs({P:-2,B:1,U:0,V:6,sat:-s.Rational(1,26)}))==0 for f in eq)
say('QUARTIC BEZOUT BRANCH, W IDENTITY, ENDPOINT SPECIALIZATIONS AND UNIQUE SURVIVING POINT PASS')
aug=json.loads((base.parent/'c4-augmented-qq/c4-nonzero-augmented-2.json').read_text())
assert aug['equations'][:6]==source['equations']
last=parse(aug['equations'][6]);assert last.subs({P:-2,B:1,U:0,V:6,sat:-s.Rational(1,26)})==-216
say('PREVIOUSLY REVIEWED AUGMENTED SQUARE CONDITION EXCLUDES UNIQUE POINT: -216')
say('PASS: exact CAS necessary chain; endpoint necessity uses separately independently checked scalar Lean certificates. Not a Lean theorem for the resultant chain or chart geometry.')
