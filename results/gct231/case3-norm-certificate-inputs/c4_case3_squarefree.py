from pathlib import Path
import json,sympy as s,time
r=Path(__file__).parent; b=s.symbols('beta'); d=json.loads((r/'c4-case3-bezout-inputs.json').read_text())
start=time.monotonic();out=[]
for key in ['first_norm','second_norm']:
 p=s.Poly(s.sympify(d[key],locals={'beta':b}),b,domain=s.QQ)
 c,fs=s.sqf_list(p);q=s.Poly(1,b,domain=s.QQ)
 for f,n in fs:q*=f
 q=q.primitive()[1]
 out.append({'key':key,'content':str(c),'factors':[{'polynomial':str(f.as_expr()),'multiplicity':n} for f,n in fs],'squarefree':str(q.as_expr())})
 print(key,'sqf',[(f.degree(),n) for f,n in fs],time.monotonic()-start,flush=True)
(r/'c4-case3-squarefree.json').write_text(json.dumps(out,indent=2)+'\n')
