from pathlib import Path
from functools import reduce
from math import gcd,lcm
import json,time
import sympy as S
from sympy.polys.rings import ring
from sympy.polys.domains import QQ

start=time.monotonic();base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search')
job=base/'tracezero_rankdrop'
source=json.loads((job/'shifted-matrix.json').read_text())
full=json.loads((job/'full31-shifted.json').read_text())
R,*v=ring(','.join(source['variables']),QQ)
p0,p1,p2,p3,p4,p5,b0,b1,b2,b3,k,l=v
loc={str(x):S.Symbol(str(x)) for x in v}
parse=lambda s:R.from_expr(S.sympify(s,locals=loc))
M=[[parse(x) for x in row] for row in source['matrix']]
F=[p0/2+k*p4/2+3*(1+k*k)/4,
   (p1+p2+k*p5+l*p4)/2+3*k*l/2,
   p3/2+l*p5/2+3*(1+l*l)/4]
Q=[]
for power in [[2,0,0],[1,1,0],[0,2,0]]:
    i=full['parameter_exponents'].index(power)
    Q.append(parse(full['generators'][i])*QQ(full['scales_to_actual_permanent_coefficients'][i]))
C=[]
for power in [[3,0,0],[2,1,0],[1,2,0],[0,3,0]]:
    i=full['parameter_exponents'].index(power)
    C.append(parse(full['generators'][i])*QQ(full['scales_to_actual_permanent_coefficients'][i]))
dF=[[R.one/2,R.zero],[R.zero,R.one/2],[k/2,l/2],
    [R.zero,R.zero],[R.zero,R.zero],[R.zero,R.zero],[(p4+3*k)/2,(p5+3*l)/2]]
trials=[]
for label,f,modflat in [('subtract_Fq',F,False),('subtract_Fq_and_Qq',[F[i]+Q[i]/8 for i in range(3)],False),('compact_mod_flat',[F[i]+Q[i]/8 for i in range(3)],True)]:
    rows=[row[:] for row in M]
    primitive=[];scales=[]
    for i in range(4):
        new=[]
        for j in range(7):
            entry=M[5+i][j]/4
            if i<3:entry-=2*f[i]*M[0][j]
            if i>0:entry-=2*f[i-1]*M[1][j]
            if modflat:
                if i<3:entry-=Q[i]*dF[j][0]
                if i>0:entry-=Q[i-1]*dF[j][1]
                if j in [3,4,5]:entry-=C[i]/4
            new.append(entry)
        den=lcm(*(int(c.denominator) for g in new for c in g.values()))
        content=reduce(gcd,(abs(int(c*den)) for g in new for c in g.values()))
        scale=QQ(content,den)
        primitive.append([g/scale for g in new]);scales.append(str(scale))
    rows[5:]=primitive
    trials.append({'label':label,'matrix':[[str(x) for x in row] for row in rows],
                   'new_quartic_row_scales_to_actual':scales,
                   'term_count':sum(len(x) for row in rows for x in row),
                   'quartic_term_count':sum(len(x) for row in rows[5:] for x in row),
                   'row_operation_coefficients':list(map(str,f)),
                   'scope':('First five rows unchanged. Subtracts Q*dF and C*traceW/4 in addition to triangular q-row operations; preserves the row module modulo the twelve flat generators.' if modflat else 'Exact triangular row operations; first five rows unchanged. No use of flat equations, so matrix rank preserved for every parameter value.')})
report={'status':'PASS','original_terms':sum(len(x) for row in M for x in row),
        'Q_binary_coefficients':list(map(str,Q)),
        'C_binary_coefficients':list(map(str,C)),
        'F_derivative_coefficients':[[str(x) for x in row] for row in dF],
        'trials':trials,'seconds':time.monotonic()-start,
        'scope':'Algebraic row-equivalent first-variation matrices. No rank or infeasibility conclusion.'}
compact_flat=[parse(x) for x in source['flat_generators'][:7]]
compact_scales=[]
for j in range(5):
    idx=full['parameter_exponents'].index([4-j,j,0])
    g=parse(full['generators'][idx])*QQ(full['scales_to_actual_permanent_coefficients'][idx])
    for a in range(3):
        b=j-a
        if 0<=b<3:g-=Q[a]*(Q[b]/16+F[b])
    den=lcm(*(int(c.denominator) for c in g.values()))
    content=reduce(gcd,(abs(int(c*den)) for c in g.values()))
    scale=QQ(content,den)
    compact_scales.append(str(scale));compact_flat.append(g/scale)
report['compact_flat_generators']=list(map(str,compact_flat))
report['compact_flat_quartic_scales_to_actual']=compact_scales
report['compact_flat_term_counts']=list(map(len,compact_flat))
report['compact_flat_total_terms']=sum(map(len,compact_flat))
report['compact_flat_ideal_equivalence']='First7 generators unchanged; binary quartic replaced by P-Q*(Q/16+F). All Q binary coefficients are among first3 generators, so ideals are equal without a guard.'
(base/'incidence-row-sparsification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'original_terms':report['original_terms'],'trials':[{k:x[k] for k in ['label','term_count','quartic_term_count']} for x in trials],'compact_flat_terms':report['compact_flat_total_terms'],'seconds':report['seconds']}))
