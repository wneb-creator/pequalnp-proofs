from pathlib import Path
from fractions import Fraction
import math,re,json,hashlib,time
import sympy as S
p=Path('/tmp/oec/pequalnp-pilot-78/construct_search/net_normal_form');start=time.monotonic();variables=['z','a','B','c','D'];zero=(0,)*5

def parse(text):
 text=text.replace(' ','');out={}
 for term in re.findall(r'[+-]?[^+-]+',text):
  coeff=Fraction(1);expo=[0]*5
  for factor in term.split('*'):
   sign=1
   if factor.startswith('-'):sign=-1;factor=factor[1:]
   elif factor.startswith('+'):factor=factor[1:]
   coeff*=sign
   if re.fullmatch(r'\d+(?:/\d+)?',factor):coeff*=Fraction(factor)
   else:
    m=re.fullmatch(r'([zaBcD])(?:\^(\d+))?',factor);assert m,(text,factor)
    expo[variables.index(m[1])]+=int(m[2] or 1)
  key=tuple(expo);out[key]=out.get(key,Fraction(0))+coeff
 return {m:c for m,c in out.items() if c}

def expected(text):return parse(str(S.expand(S.sympify(text))).replace('**','^'))
q='-a*c+2*a*D+2*B*c-2*a-2*c+2*B+2*D';ca='a^3+6*a^2+3*a*B^2-6*a*B+3*a+2*B^3+6*B';cc='c^3+6*c^2+3*c*D^2-6*c*D+3*c+2*D^3+6*D'
a,B,c,D=S.symbols('a B c D');pp=(a-c)**2+2*(a-c)*(B-D)+3*(B+D)**2
reduced=json.loads((p/'c3-reduced-trivial-block.json').read_text());env={str(v):v for v in [a,B,c,D]}
nt=S.sympify(reduced['determinant'],locals=env);minor=S.sympify(reduced['plus_minor_divided_minus36'],locals=env)
reports=[]
for stem,target,expected_last,guard in [('c3-certificate-trivial',{zero:1},nt,True),('c3-power-certificate-plus',{(0,1,0,1,0):1},minor,False)]:
 data=(p/(stem+'.stdout')).read_bytes();lines=data.decode().splitlines();assert lines[-1]=='DONE'
 gens=[parse(lines[i+1]) for i,v in enumerate(lines) if v=='GENERATOR'];certs=[parse(lines[i+1]) for i,v in enumerate(lines) if v=='COEFFICIENT'];assert len(gens)==len(certs)==(6 if guard else 5)
 for actual,want in zip(gens[:4],[parse(q),parse(ca),parse(cc),expected(str(pp))]):assert actual==want
 assert gens[-1]==expected(str(expected_last))
 if guard:assert gens[-2]==parse('z*a*c-1')
 common=1
 for poly in certs:
  for coefficient in poly.values():common=math.lcm(common,coefficient.denominator)
 result={}
 for gen,cert in zip(gens,certs):
  for gm,gc in gen.items():
   assert gc.denominator==1
   for cm,coef in cert.items():
    mon=tuple(x+y for x,y in zip(gm,cm));n=gc.numerator*coef.numerator*(common//coef.denominator);result[mon]=result.get(mon,0)+n
 result={m:c for m,c in result.items() if c};assert result=={m:common*c for m,c in target.items()}
 report={'file':stem+'.stdout','sha256':hashlib.sha256(data).hexdigest(),'verdict':'PASS','coefficient_terms':sum(map(len,certs)),'common_denominator_digits':len(str(common)),'target':str(target)};reports.append(report);print(report,flush=True)
# The smaller trivial block follows by tangent elimination and adding explicit multiples of q, C(a,B), C(c,D).
full=json.loads((p/'c3-extension-blocks.json').read_text())['blocks']['trivial'];T=S.Matrix([[S.sympify(x,locals=env) for x in row] for row in full]);N=S.Matrix([[S.sympify(x,locals=env) for x in row] for row in reduced['matrix']]);scales=[6,3,3];eqs=[S.sympify(q,locals=env),S.sympify(ca.replace('^','**'),locals=env),S.sympify(cc.replace('^','**'),locals=env)]
quotients=[]
for i in range(3):
 row=[]
 for j in range(3):
  difference=S.expand(T[i+1,j+1]/scales[i]-T[i+1,0]/scales[i]*(T[0,j+1]/6)-N[i,j]);quot,rem=S.div(difference,eqs[i],a,B,c,D);assert rem==0;row.append(str(quot))
 quotients.append(row)
assert S.expand(N.det()-nt)==0
out={'verdict':'PASS','certificates':reports,'trivial_row_reduction_multipliers':quotients,'seconds':time.monotonic()-start}
(p/'c3-certificates-independent-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
