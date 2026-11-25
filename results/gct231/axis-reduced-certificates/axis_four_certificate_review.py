from pathlib import Path
from datetime import datetime,timezone
from fractions import Fraction
import json,hashlib,math,sympy as s
base=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
summary=[]
for case in ['equal','different']:
 prefix='axis-four-'+case;source=base/(prefix+'.json');certpath=base/(prefix+'-quotient-compressed-certificate.json');inputpath=base/(prefix+'.in');provpath=base/(prefix+'.provenance.json')
 d=json.loads(source.read_text());c=json.loads(certpath.read_text());pr=json.loads(provpath.read_text());assert c['variables']==d['unknowns']==pr['variables']==['o7','o8','o1','u'];vs=s.symbols(d['unknowns']);loc=dict(zip(d['unknowns'],vs))
 assert len(d['equations'])==len(c['generators'])==len(c['multipliers'])==pr['generator_count']==8
 assert pr['source_sha256']==sha(source) and pr['input_sha256']==sha(inputpath) and pr['characteristic']==0
 def readterms(terms):
  out={}
  for mon,coef in terms:
   assert len(mon)==4 and min(mon)>=0 and tuple(mon) not in out
   v=Fraction(coef);assert v;out[tuple(mon)]=v
  return out
 generators=list(map(readterms,c['generators']));multipliers=list(map(readterms,c['multipliers']))
 for i,(row,g) in enumerate(zip(d['equations'],generators)):
  poly=s.Poly(s.sympify(row['coefficient'],locals=loc),*vs,domain=s.QQ);den,ip=poly.clear_denoms();content,primitive=ip.primitive();assert g=={mon:Fraction(coef) for mon,coef in primitive.terms()}
  sc=pr['equation_scalings'][i];assert Fraction(sc['denominator'])/Fraction(sc['content'])==Fraction(den/content)
 vals=list(map(int,inputpath.read_text().split()));n,m,ch,total=vals[:4];lengths=vals[4:12];pos=12;assert (n,m,ch)==(4,8,0) and total==sum(lengths)==pr['term_count']
 for length,g in zip(lengths,generators):
  got={}
  for _ in range(length):
   num,den=vals[pos:pos+2];mon=tuple(vals[pos+2:pos+6]);pos+=6;assert den>0 and mon not in got;got[mon]=Fraction(num,den)
  assert got==g
 assert pos==len(vals)
 result={}
 for g,mult in zip(generators,multipliers):
  for mon,a in g.items():
   for powers,b in mult.items():
    key=tuple(x+y for x,y in zip(mon,powers));result[key]=result.get(key,Fraction(0))+a*b
 result={m:v for m,v in result.items() if v};assert result==readterms(c['target'])=={(0,0,0,0):Fraction(1)}
 D=math.lcm(*[v.denominator for m in multipliers for v in m.values()]);assert D==int(c['integer_denominator'])
 item={'case':case,'source_sha256':sha(source),'certificate_sha256':sha(certpath),'input_sha256':sha(inputpath),'provenance_sha256':sha(provpath),'generator_terms':sum(map(len,generators)),'multiplier_terms':sum(map(len,multipliers)),'integer_denominator':str(D),'source_indices':[row['source_index'] for row in d['equations']],'exact_identity':'sum multiplier_i*generator_i=1','review':'PASS'};summary.append(item);print(json.dumps(item),flush=True)
print('Both exact Fraction convolution identities equal1, all8 ordered primitive generators/source coefficients/actual rational sparse rows and conversion provenance verified. No quotient-only remainder or omitted relation is used.',flush=True)
print('Scope: the two displayed8-equation complex polynomial systems are inconsistent. Geometric/source reduction to these systems is not independently covered by this review. No solver or compiler rerun.',flush=True)
(base/'axis-four-certificate-review.json').write_text(json.dumps({'utc':datetime.now(timezone.utc).isoformat(),'cases':summary,'scope':'Explicit conditional polynomial contradiction certificates only.'},indent=2)+'\n')
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True);print('PASS',flush=True)
