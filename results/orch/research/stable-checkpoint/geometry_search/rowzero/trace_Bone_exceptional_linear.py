from pathlib import Path
import sympy as S
import json,resource,time
resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(30,35))
start=time.monotonic();base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
data=json.loads((base/'trace-Bone-systems.json').read_text())['cases']['other-index']
symbols={name:S.Symbol(name) for name in data['variables']}
alpha=(-7+S.I)/5
sub={symbols['tau']:0,symbols['d1']:0,symbols['d3']:0,symbols['p3']:alpha,symbols['p1']:-2*(alpha+1),symbols['p5']:0}
unknowns=[symbols[x] for x in ['p0','p2','p4','d0','d2']]
equations=[S.expand(S.sympify(g).subs(sub,simultaneous=True)) for g in data['generators']]
first_indices=[1,5,10]
A,b=S.linear_eq_to_matrix([equations[i] for i in first_indices],unknowns)
solution=list(S.linsolve((A,b),unknowns))[0]
sub2=dict(zip(unknowns,solution));free=sorted(set().union(*(x.free_symbols for x in solution)),key=str)
residuals=[S.expand(x.subs(sub2,simultaneous=True)) for x in equations]
assert all(residuals[i]==0 for i in first_indices)
nonzero=[]
for i,g in enumerate(residuals):
 if g:
  p=S.Poly(g,*free,extension=S.I)
  nonzero.append({'index':i,'degree':p.total_degree(),'terms':len(p.terms()),'polynomial':str(g)})
report={'status':'PASS','alpha':str(alpha),'unknowns':list(map(str,unknowns)),'first_variation_indices':first_indices,'linear_rank':A.rank(),'augmented_rank':A.row_join(b).rank(),'solution':{str(k):str(v) for k,v in sub2.items()},'free_variables':list(map(str,free)),'residuals':nonzero,'scope':'Exact linear elimination in the refined exceptional B-rank-one chart over Q(i); the conjugate field embedding covers the other alpha root. No infeasibility conclusion yet.','seconds':time.monotonic()-start}
(base/'trace-Bone-exceptional-linear.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
