from pathlib import Path
import json
import resource
import time
import sympy as S

resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(45,50))
start=time.monotonic()
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search/rowzero')
data=json.loads((base/'trace-Bone-systems.json').read_text())['cases']['same-index']
names={name:S.Symbol(name) for name in data['variables']}
alpha=(-7+S.I)/5
sub={names['d1']:0,names['d3']:0,names['p1']:alpha,
     names['p3']:-2*(alpha+1),names['p5']:0}
equations=[S.expand(S.sympify(g,locals=names).subs(sub,simultaneous=True))
           for g in data['generators']]
unknowns=[names[k] for k in ['p0','p2','p4']]
indices=[1,5,10]
M,rhs=S.linear_eq_to_matrix([equations[i] for i in indices],unknowns)
solution=list(S.linsolve((M,rhs),unknowns))
report={'scope':'Exact kernel-D-support-one specialization of the same-index '
                'B-rank-one chart; no generic rank-one conclusion.',
        'substitution':{str(k):str(v) for k,v in sub.items()},
        'matrix':[[str(x) for x in row] for row in M.tolist()],
        'rhs':list(map(str,rhs)),'rank':M.rank(),
        'determinant':str(S.expand(M.det())),'solution':None}
if solution:
    assert len(solution)==1
    solution=dict(zip(unknowns,solution[0]))
    report['solution']={str(k):str(v) for k,v in solution.items()}
    residuals=[S.expand(g.subs(solution,simultaneous=True)) for g in equations]
    assert all(residuals[i]==0 for i in indices)
    report['residuals']=[{'index':i,'polynomial':str(S.factor(g,extension=S.I))}
                         for i,g in enumerate(residuals) if g!=0]
report['seconds']=time.monotonic()-start
(base/'trace-Bone-single-D.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2),flush=True)
