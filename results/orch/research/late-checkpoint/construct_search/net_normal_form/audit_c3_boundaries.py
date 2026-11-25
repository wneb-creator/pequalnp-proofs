from pathlib import Path
import json,sympy as s,time
p=Path('/tmp/oec/pequalnp-pilot-78/construct_search/net_normal_form');start=time.monotonic();data=json.loads((p/'c3-boundary-certificates.json').read_text());x=s.symbols('x')
for name in ['one_zero_off0','both_zero_off0']:
 item=data[name];f=s.sympify(item['f']);g=s.sympify(item['g']);a,b=map(s.sympify,item['coefficients']);assert s.expand(a*f+b*g)==1
item=data['trivial_direction'];a,b=map(s.sympify,item['coefficients']);assert s.expand(a*s.sympify(item['normalized_q'])+b*s.sympify(item['normalized_c']))==1
A,B,C,D=s.symbols('a B c D');env={str(v):v for v in [A,B,C,D]};blocks=json.loads((p/'c3-extension-blocks.json').read_text())['blocks'];plus=s.Matrix([[s.sympify(v,locals=env) for v in row] for row in blocks['plus']]);minus=s.Matrix([[s.sympify(v,locals=env) for v in row] for row in blocks['minus']]);swapped=plus.subs({A:C,B:D,C:A,D:B},simultaneous=True);assert (swapped-minus).applyfunc(s.expand)==s.zeros(3)
report={'verdict':'PASS','boundary_bezout_identities':3,'minus_equals_swapped_plus':True,'seconds':time.monotonic()-start};(p/'c3-boundaries-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
