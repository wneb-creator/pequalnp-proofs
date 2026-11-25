from pathlib import Path
import json,re,hashlib,sympy as s,time
base=Path(__file__).parent;p=base/'case2-necessity';text=(p/'Case2NecessaryResultants.lean').read_text()
P,B,U,V,sat=s.symbols('P B U V sat');loc={str(x):x for x in(P,B,U,V,sat)}
source=json.loads((base/'fresh/c4-nonzero-reduced-2.json').read_text()); eq=[s.sympify(x,locals=loc) for x in source['equations']]
def readdef(name):
 match=re.search(r'^def '+name+r' .*?:=\s*([^\n]+)',text,re.M);assert match,name
 return s.sympify(match.group(1).replace('^','**'),locals=loc)
for name,i in [('originalQ',0),('originalC',1),('scaleCurve',2),('originalR',3),('originalL',4),('originalSaturation',5)]:
 assert s.expand(readdef(name)-eq[i])==0;print('literal original',name,'PASS',flush=True)
ra,rb,rc=[readdef(x) for x in ['rA','rB','rC']];la,lb,lc,ld,le=[readdef(x) for x in ['l20','l11','l10','l02','l01']]
r=ra*U+rb*V+rc;l=la*U**2+(lb*V+lc)*U+ld*V**2+le*V
certs=json.loads((p/'reduction-certificates.json').read_text())
for name,actual,i in [('linear_r',r,3),('quadratic_l',l,4)]:
 cert=certs[name];factor=s.sympify(cert['factor'],locals=loc);cofactor=s.sympify(cert['cofactor'],locals=loc)
 assert s.expand(actual-factor*eq[i]-cofactor*eq[2])==0;print('reduction identity',name,'PASS',flush=True)
W=readdef('chartDet');K=readdef('curveLeading')
assert s.expand(eq[5]-(P*B*W*sat-1))==0
assert s.expand(eq[2]-(K*(-6*B**2+(5*P**2-P+10)*B-8*P**2)-3*P*B))==0
print('saturation and safe-factor domain identities PASS',flush=True)
t=rb*V+rc
qe=(4*P**2-6*B)*t**2-ra*(4*P*V)*t+ra**2*((3*B-4)*V**2+36*B)
lelim=la*t**2-ra*(lb*V+lc)*t+ra**2*(ld*V**2+le*V)
ce=-2*P**2*t**3+ra*(-28*P**2-4*P*V)*t**2-ra**2*(-2*P*V**2+20*P*V)*t+ra**3*(-V**3+(9*B-2)*V**2-36*B)
for label,pol,target,degree in [('q',eq[0],qe,2),('l',l,lelim,2),('c',eq[1],ce,3)]:
 a=s.Poly(pol,U); rootformula=sum(coefficient*(-t)**power[0]*ra**(degree-power[0]) for power,coefficient in a.terms())
 assert s.expand(rootformula-target)==0
 assert s.Poly(target,V).degree()<=degree
 print('linear-eliminant formula and V degree',label,degree,'PASS',flush=True)
helper=(base/'ResultantCommonRoot.lean').read_text();body=helper[helper.index('theorem resultant_zero_of_common_root'):helper.index('end PEqualNP')]
assert body in text
print('generic common-root helper exact frozen body PASS',flush=True)
assert '_root_' not in text and chr(34) not in text and 'sorry' not in text and 'native_decide' not in text
meta={'status':'PASS_INDEPENDENT_LITERAL_SOURCE_AND_POLYNOMIAL_IDENTITIES','source_sha256':hashlib.sha256(text.encode()).hexdigest(),'scope':'Six original equations imply nonzero P/B/K/W and two raw fixed-degree resultants. No divided-resultant or norm necessity assertion. Polynomial eliminant definitions checked by direct source inspection against the independently evaluated formulas.'}
(base/'case2-necessity-independent-review.json').write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(meta),flush=True)
