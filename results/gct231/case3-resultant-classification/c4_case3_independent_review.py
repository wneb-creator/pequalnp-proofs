from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,time,signal
import sympy as S
from sympy.polys.matrices import DomainMatrix
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True);start=time.monotonic()
A,b,U,V,sat=S.symbols('A beta U V sat');loc={str(x):x for x in (A,b,U,V,sat)}
parse=lambda t:S.sympify(t,locals=loc)
source=root/'fresh/c4-nonzero-reduced-3.json';assert sha(source)=='72b12e2f543766e57aec78a88717f5133442553a207566956022363aa89a867f'
eq=[parse(t) for t in json.loads(source.read_text())['equations']]
fd=json.loads((root/'c4-case3-resultants.json').read_text());nd=json.loads((root/'c4-case3-norm-gcd.json').read_text());rd=json.loads((root/'c4-case3-reverse-firstnorm.json').read_text());branches=json.loads((root/'c4-case3-scalar-branches.json').read_text())
for name in ['c4-case3-resultants.json','c4-case3-norm-gcd.json','c4-case3-reverse-firstnorm.json','c4-case3-scalar-branches.json']:print('SHA256',name,sha(root/name),flush=True)
assert fd['source']==json.loads(source.read_text())
F=eq[2];H=b*b+b-1;det=-4*A*b*b-4*A*b+5*A+6*b*b+6*b-6;safe=A*b*H*det
assert S.expand(eq[5]-(A*b*sat*det-1))==0
assert S.expand(F-H*((8*A*A-10*A)*b*b+2*A*b+6-8*A)-3*A*(2*b-1))==0
assert S.expand((2*b+3)*(2*b-1)-4*H-1)==0
assert S.Poly(F,A).LC()==8*b**2*H or S.expand(S.Poly(F,A).LC()-8*b*b*H)==0
print('Saturation A*beta*det nonzero; exact identities force H nonzero; curve leading coefficient8beta^2H nonzero: PASS',flush=True)
field=S.QQ.frac_field(b,U,V);modulus=S.Poly(F,A,domain=field)
def allowed_denominator(expression):
 p=S.Poly(expression,b,domain=S.QQ)
 assert p!=0
 for divisor in [S.Poly(b,b,domain=S.QQ),S.Poly(H,b,domain=S.QQ)]:
  while p.degree()>0:
   q,r=p.div(divisor)
   if not r.is_zero:break
   p=q
 assert p.degree()==0 and p.LC()!=0

def validate_record(expression,row):
 den_saved=parse(row['denominator']);allowed_denominator(den_saved)
 removed=S.Integer(1)
 for value in row['removed_nonzero_factors']:
  factor=parse(value);assert factor!=0
  assert S.Poly(safe,A,b,U,V).rem(S.Poly(factor,A,b,U,V)).is_zero
  removed*=factor
 rational=S.cancel(S.Poly(expression,A,domain=field).rem(modulus).as_expr())
 numerator,denominator=S.fraction(rational);allowed_denominator(denominator)
 assert S.expand(denominator-den_saved)==0
 got=S.Poly(numerator,A,b,U,V,domain=S.QQ)
 want=S.Poly(parse(row['polynomial'])*removed,A,b,U,V,domain=S.QQ)
 assert not got.is_zero and not want.is_zero and got.monoms()==want.monoms()
 scale=got.LC()/want.LC();assert scale!=0 and got==want.mul_ground(scale)
 print('Exact reduced identity',row['label'],'nonzero rational scale',scale,'seconds',round(time.monotonic()-start,3),flush=True)
 return parse(row['polynomial'])

# Independent determinant algorithms: linear-root formula and Sylvester determinant.
def linear_resultant(f,g,var,other):
 fp=S.Poly(f,var);gp=S.Poly(g,var);assert fp.degree()==1
 aa,bb=fp.all_coeffs();pa=S.Poly(aa,*other,domain=S.QQ);pb=S.Poly(bb,*other,domain=S.QQ)
 ans=S.Poly(0,*other,domain=S.QQ);degree=gp.degree()
 for (power,),coefficient in gp.terms():ans+=S.Poly(coefficient,*other,domain=S.QQ)*(-pb)**power*pa**(degree-power)
 return ans.as_expr()
def sylvester_resultant(f,g,var):
 domain=S.QQ.poly_ring(A,b);fp=S.Poly(f,var,domain=domain);gp=S.Poly(g,var,domain=domain)
 fc=fp.rep.to_list();gc=gp.rep.to_list();m=fp.degree();n=gp.degree();size=m+n;rows=[]
 for shift in range(n):rows.append([domain.zero]*shift+fc+[domain.zero]*(size-shift-len(fc)))
 for shift in range(m):rows.append([domain.zero]*shift+gc+[domain.zero]*(size-shift-len(gc)))
 return domain.to_sympy(DomainMatrix.from_list(rows,domain).det())

def stop(*args):raise TimeoutError('Independent exact polynomial check180-second cap')
signal.signal(signal.SIGALRM,stop);signal.alarm(180)
rows={r['label']:r for r in fd['reductions']}
pol={label:validate_record(eq[i],rows[label]) for label,i in [('q',0),('c',1),('linear_r',3),('quadratic_l',4)]}
for label,key in [('q','q'),('c','c'),('l','quadratic_l')]:
 name='eliminate_U_'+label
 pol[name]=validate_record(linear_resultant(pol['linear_r'],pol[key],U,(A,b,V)),rows[name])
outputs=[pol['eliminate_U_'+v] for v in ['q','c','l']]
for i,j in [(0,1),(0,2),(1,2)]:
 name='eliminate_V_'+str(i)+str(j)
 pol[name]=validate_record(sylvester_resultant(outputs[i],outputs[j],V),rows[name])
print('All forward resultants independently reconstructed by linear formula/Sylvester determinant: PASS',flush=True)
# Norms are univariate polynomial products, avoiding giant expression expansion.
fa,fb,fc=[S.Poly(t,b,domain=S.QQ) for t in S.Poly(F,A).all_coeffs()]
def check_norm(poly,normtext,removed):
 pp=S.Poly(poly,A);assert pp.degree()==1
 aa,cc=[S.Poly(t,b,domain=S.QQ) for t in pp.all_coeffs()]
 norm=(fa*cc*cc-fb*aa*cc+fc*aa*aa).primitive()[1]
 for value in removed:
  divisor=S.Poly(parse(value),b,domain=S.QQ)
  assert divisor in [S.Poly(b,b,domain=S.QQ),S.Poly(H,b,domain=S.QQ)]
  norm=norm.exquo(divisor)
 assert norm==S.Poly(parse(normtext),b,domain=S.QQ)
 return norm
common=None
for row in nd:
 norm=check_norm(pol[row['label']],row['norm'],row['removed_nonzero_factors'])
 common=norm if common is None else common.gcd(norm)
 assert common==S.Poly(parse(row['gcd_so_far']),b,domain=S.QQ)
 print('Forward norm/gcd',row['label'],norm.degree(),common.degree(),'PASS',flush=True)
reverse={r['label']:r for r in rd['reductions']}
for label in ['q','c','linear_r']:assert reverse[label]==rows[label]
rq=validate_record(linear_resultant(pol['linear_r'],pol['q'],V,(A,b,U)),reverse['eliminate_V_q'])
rc=validate_record(linear_resultant(pol['linear_r'],pol['c'],V,(A,b,U)),reverse['eliminate_V_c'])
last=validate_record(sylvester_resultant(rq,rc,U),reverse['eliminate_U_01'])
rnorm=check_norm(last,rd['norm'],rd['removed_nonzero_factors'])
gcd=common.gcd(rnorm);expected=S.Poly((b+2)**22*(2*b-1)**24/S.Integer(16777216),b,domain=S.QQ)
assert gcd==expected==S.Poly(parse(rd['combined_gcd']),b,domain=S.QQ)
assert S.Poly(parse(rd['combined_gcd_factored']),b,domain=S.QQ)==expected
print('Reverse norm and combined exact gcd=(beta+2)^22(2beta-1)^24/16777216: PASS',flush=True)
# Scalar endpoints without a Groebner rerun.
for value,roots in [(S.Integer(-2),[S.Integer(2),S.Rational(3,32)]),(S.Rational(1,2),[S.Integer(4),S.Rational(3,4)])]:
 fp=S.Poly(F.subs(b,value),A);assert fp.degree()==2
 assert S.expand(fp.as_expr()-fp.LC()*S.prod(A-t for t in roots))==0
for row in branches:
 av=S.Rational(row['A']);bv=S.Rational(row['beta']);es=[S.expand(e.subs({A:av,b:bv})) for e in eq]
 assert all(S.expand(e-parse(t))==0 for e,t in zip(es,row['equations']))
 if (av,bv) in [(S.Integer(2),S.Integer(-2)),(S.Rational(3,4),S.Rational(1,2))]:assert es[5]==-1
 elif av==S.Rational(3,32):
  line=-45*U+16*V-258
  assert S.expand(es[3]-S.Rational(11163,4096)*line)==0
  assert S.expand(es[4]-S.Rational(549,512)*V*(line-90))==0
  assert es[0].subs({V:0,U:-S.Rational(86,15)})==-S.Rational(4467,640)
 else:
  assert (av,bv)==(4,S.Rational(1,2))
  assert S.expand(es[3]-S.Rational(169,8)*(5*U+V+12))==0
  qq=S.factor(es[0].subs(V,-5*U-12));cc=S.factor(es[1].subs(V,-5*U-12))
  assert S.expand(qq+S.Rational(13,2)*U*(5*U+24))==0
  assert S.expand(cc-U*(299*U**2-902*U-1248)/2)==0
  assert cc.subs(U,-S.Rational(24,5))!=0
  assert all(e.subs({U:0,V:-12,sat:S.Rational(1,13)})==0 for e in es)
 print('Direct scalar branch A=',av,'beta=',bv,'PASS',flush=True)
full=json.loads((root/'fresh/c4-nonzero-square-3.json').read_text());alpha,beta,gamma,u,v=S.symbols('alpha beta gamma u v');sloc={str(t):t for t in [alpha,beta,gamma,u,v]};square=S.sympify(full['equations'][4],locals=sloc)
for sign in [-1,1]:assert S.expand(square.subs({alpha:2*sign,beta:S.Rational(1,2),gamma:sign,u:0,v:-6*sign}))==-1
print('Only original reduced point (A,beta,U,V,sat)=(4,1/2,0,-12,1/13); both scale lifts fail omitted square condition: PASS',flush=True)
signal.alarm(0)
print('Scope: exact necessary elimination and original scalar branches close reduced open case3, given the separately reviewed geometric reduction. No case2, fullchart, main-gap or Lean claim.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
