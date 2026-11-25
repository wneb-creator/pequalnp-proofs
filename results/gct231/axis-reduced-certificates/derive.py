from pathlib import Path
import hashlib,json,resource
import sympy as S
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
base=Path(__file__).resolve().parents[1]
src=base/'triangle_concept/triangle-twelve-equations.json'
assert hashlib.sha256(src.read_bytes()).hexdigest()=='03a8aa61b2a83e2918457d922059fb481128cc02b3d1532c2cfcc11677ed0ce7'
data=json.loads(src.read_text());loc={n:S.Symbol(n) for n in data['unknowns']}
polys=[S.sympify(row['coefficient'],locals=loc) for row in data['equations']]
out=Path(__file__).parent
cases={
 'axis_x':{loc['o0']:0,loc['o3']:0,loc['d3']:-loc['d0']-2},
 'support_xy':{loc['o3']:0,loc['o7']:0},
}
for name,sub in cases.items():
 rows=[]
 print('CASE',name,'substitution',sub,flush=True)
 for index,poly in enumerate(polys):
  reduced=S.factor(poly.subs(sub,simultaneous=True))
  if reduced!=0:
   print(index,data['equations'][index]['monomial'],reduced,flush=True)
   rows.append({'source_index':index,'monomial':data['equations'][index]['monomial'],'coefficient':str(reduced)})
 unknowns=[str(x) for x in sorted(set().union(*(S.sympify(r['coefficient'],locals=loc).free_symbols for r in rows)),key=str)]
 result={'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'case':name,'substitution':{str(k):str(v) for k,v in sub.items()},'unknowns':unknowns,'equations':rows,'scope':'Necessary equations under displayed center-kernel stratum assumptions; no verdict.'}
 (out/(name+'.json')).write_text(json.dumps(result,indent=2)+'\n')
