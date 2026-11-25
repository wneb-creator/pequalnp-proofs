from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
import sympy as s
root=Path(__file__).resolve().parent.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
source=root/'triangle_generic/triangle-generic-eleven-equations.json'
assert sha(source)=='8ded9d5e1145761185086336d90b749165633b5bad27a9c8de1677e32617eb48'
d=json.loads(source.read_text());vs=s.symbols(d['unknowns']);loc=dict(zip(d['unknowns'],vs))
polys=[s.Poly(s.sympify(e['coefficient'],locals=loc),*vs,domain=s.QQ) for e in d['equations']]
inp=root/'triangle_generic/generic-p1009.in';provpath=root/'triangle_generic/generic-p1009.provenance.json';prov=json.loads(provpath.read_text())
assert prov['source_sha256']==sha(source) and prov['input_sha256']==sha(inp) and prov['variables']==d['unknowns']
assert prov['characteristic']==1009 and prov['generator_count']==20 and prov['term_count']==1050
vals=list(map(int,inp.read_text().split()));n,m,p,total=vals[:4];assert (n,m,p,total)==(11,20,1009,1050)
lengths=vals[4:24];assert sum(lengths)==total;pos=24
for i,(length,poly) in enumerate(zip(lengths,polys)):
 got={}
 for _ in range(length):
  num,den=vals[pos:pos+2];mon=tuple(vals[pos+2:pos+13]);pos+=13
  assert den>0 and den%1009 and all(e>=0 for e in mon) and mon not in got
  got[mon]=num*pow(den,-1,1009)%1009
 denominator,integral=poly.clear_denoms();content,primitive=integral.primitive()
 scale=prov['equation_scalings'][i]
 assert s.Rational(scale['denominator'])/s.Rational(scale['content'])==denominator/content
 assert int(denominator)%1009 and int(content)%1009
 want={mon:int(c.p)*pow(int(c.q),-1,1009)%1009 for mon,c in primitive.terms()};want={mon:c for mon,c in want.items() if c}
 assert got==want,i
assert pos==len(vals)
print('All 20 actual sparse F1009 rows, 11-variable order, primitive scaling, 1050 terms and source/input provenance: PASS',flush=True)
print('Input SHA256',sha(inp),'provenance SHA256',sha(provpath),flush=True)
print('No solver rerun; finite-field input validity only, no characteristic-zero verdict.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True)
print('PASS',flush=True)
