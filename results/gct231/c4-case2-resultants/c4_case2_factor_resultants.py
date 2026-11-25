from pathlib import Path
import json,time
import sympy as S
p=Path(__file__).parent
P,B,U,V=S.symbols('P B U V'); loc={str(x):x for x in (P,B,U,V)}
d=json.loads((p/'c4-case2-resultants.json').read_text()); out=[]; start=time.monotonic()
for r in d['reductions']:
 if not r['label'].startswith('eliminate_V'): continue
 f=S.sympify(r['polynomial'],locals=loc)
 fac=S.factor_list(f, P,B)
 row={'label':r['label'],'scalar':str(fac[0]),'factors':[{'polynomial':str(x),'multiplicity':m,'degree':S.Poly(x,P,B).total_degree(),'terms':len(S.Poly(x,P,B).terms())} for x,m in fac[1]]}
 out.append(row)
 print(row['label'],[(a['degree'],a['multiplicity'],a['terms']) for a in row['factors']],time.monotonic()-start,flush=True)
 (p/'c4-case2-resultant-factors.json').write_text(json.dumps(out,indent=2)+'\n')
