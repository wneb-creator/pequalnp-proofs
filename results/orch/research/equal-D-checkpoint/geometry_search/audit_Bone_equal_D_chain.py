from pathlib import Path
from itertools import combinations
from fractions import Fraction
from math import lcm
import hashlib,json,resource,time
import sympy as S
from sympy.polys.rings import ring
from sympy.polys.domains import QQ

resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
resource.setrlimit(resource.RLIMIT_CPU,(120,125))
start=time.monotonic()
base=Path('/tmp/oec/pequalnp-pilot-78/geometry_search')
child=base/'rowzero'
systems=json.loads((child/'trace-Bone-systems.json').read_text())['cases']['same-index']
Original,*ov=ring(','.join(systems['variables']),QQ)
original=[Original.from_expr(S.sympify(g)) for g in systems['generators']]
H=[[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]
reports=[]
for branch in [7,9]:
    lp=child/f'trace-Bone-equal-D-linear-{branch}.json'
    np=child/f'trace-Bone-equal-D-{branch}-lift-input.json'
    cp=child/f'trace-Bone-equal-D-{branch}-certificate.json'
    linear=json.loads(lp.read_text());native=json.loads(np.read_text());cert=json.loads(cp.read_text())
    assert native['source_sha256']==hashlib.sha256(lp.read_bytes()).hexdigest()
    assert cert['source_input_sha256']==hashlib.sha256(np.read_bytes()).hexdigest()
    K,y,x,u,v,tau=ring('y,x,u,v,tau',QQ)
    parse=lambda text:K.from_expr(S.sympify(str(text)))
    fx,fy=map(parse,linear['field_relations'])
    red=lambda p:p.div([fy,fx])[1]
    assert red(parse(linear['first_variation_determinant'])*parse(linear['first_variation_determinant_inverse']))==1
    kernel=list(map(parse,linear['R_kernel']))
    comp=list(map(parse,linear['R_companion']))
    dc=list(map(parse,linear['D_companion']))
    bc=list(map(parse,linear['B_companion']))
    sub=[comp[0],kernel[0],comp[1],kernel[1],comp[2],kernel[2],u,K.one,v,K.one,tau]
    def hom(poly,images,zero,one,reducer):
        answer=zero
        for mon,c in poly.items():
            term=one*c
            for a,e in zip(images,mon):
                if e:term=reducer(term*(a**e))
            answer+=term
        return reducer(answer)
    evaluated=[hom(p,sub,K.zero,K.one,red) for p in original]
    assert all(evaluated[i]==0 for i in [1,2,5,6,10,11])
    residuals={entry['index']:parse(entry['polynomial']) for entry in linear['residuals']}
    assert set(residuals)=={0,3,4,7,8,9}
    for i,p in residuals.items():assert red(p-evaluated[i])==0
    # Check the claimed determinant against the original three first variations.
    mat=[[hom(original[i].diff(ov[j]),sub,K.zero,K.one,red) for j in [0,2,4]] for i in [1,5,10]]
    det=red(mat[0][0]*(mat[1][1]*mat[2][2]-mat[1][2]*mat[2][1])-mat[0][1]*(mat[1][0]*mat[2][2]-mat[1][2]*mat[2][0])+mat[0][2]*(mat[1][0]*mat[2][1]-mat[1][1]*mat[2][0]))
    assert red(det-parse(linear['first_variation_determinant']))==0
    # Independently construct physical A,K and evaluate their binary permanent by Ryser.
    def physical(B,rr,D):
        M=[[K.zero for j in range(4)] for i in range(4)]
        for i in range(3):
            M[i+1][i+1]=B[i];M[0][i+1]=M[i+1][0]=(rr[i]+2*D[i])/2
        for i,(j,k) in enumerate([(2,3),(1,3),(1,2)]):M[j][k]=M[k][j]=-rr[i]/2
        return [[red(sum(H[i][a]*H[j][b]*M[a][b] for a in range(4) for b in range(4))/4) for j in range(4)] for i in range(4)]
    A=physical(bc,comp,dc);B=physical([K.zero]*3,kernel,[K.one]*3)
    coeff={}
    for size in range(1,5):
        for cols in combinations(range(4),size):
            p={(0,0):K.one}
            for i in range(4):
                factors={(0,0):K.one*size,(1,0):sum(A[i][j] for j in cols),(0,1):sum(B[i][j] for j in cols)}
                nxt={}
                for aa,ca in p.items():
                    for bb,cb in factors.items():
                        key=(aa[0]+bb[0],aa[1]+bb[1])
                        nxt[key]=nxt.get(key,K.zero)+red(ca*cb)
                p={m:red(c) for m,c in nxt.items()}
            for m,c in p.items():coeff[m]=coeff.get(m,K.zero)+(-1)**(4-size)*c
    powers=[(d-j,j) for d in [2,3,4] for j in range(d+1)]
    for i,power in enumerate(powers):
        assert red(coeff[power]-QQ(systems['scales_to_actual_permanent_coefficients'][i])*evaluated[i])==0
    assert red(coeff[(0,0)])==24 and red(coeff[(1,0)])==red(coeff[(0,1)])==0
    # Check both directions of the primitive element coordinate map.
    T,a,uu,vv,tt=ring('a,u,v,tau',QQ)
    tp=lambda text:T.from_expr(S.sympify(str(text)))
    minpoly=tp(native['minpoly']);tr=lambda p:p.div([minpoly])[1]
    xx,yy=tp(native['x']),tp(native['y'])
    assert tr(xx+2*yy-a)==0
    assert hom(fx,[yy,xx,uu,vv,tt],T.zero,T.one,tr)==0
    assert hom(fy,[yy,xx,uu,vv,tt],T.zero,T.one,tr)==0
    prim=x+2*y
    assert hom(minpoly,[prim,u,v,tau],K.zero,K.one,red)==0
    assert hom(xx,[prim,u,v,tau],K.zero,K.one,red)==x
    assert hom(yy,[prim,u,v,tau],K.zero,K.one,red)==y
    ngens=list(map(tp,native['residuals']))
    for i,g in zip(native['residual_indices'],ngens):
        assert tr(g-hom(evaluated[i],[yy,xx,uu,vv,tt],T.zero,T.one,tr))==0
    assert tp(cert['field_relation'])==minpoly
    assert list(map(tp,cert['residual_generators']))==ngens
    # A second arithmetic route clears all denominators and multiplies integer
    # coefficient dictionaries; no native-CAS or quotient-field result is trusted.
    mult=list(map(tp,cert['multipliers']))+[tp(cert['field_multiplier'])]
    gens=ngens+[minpoly]
    dm=lcm(*(int(c.denominator) for p in mult for c in p.values()))
    dg=lcm(*(int(c.denominator) for p in gens for c in p.values()))
    total={}
    for mp,gp in zip(mult,gens):
        mi={m:int(c*dm) for m,c in mp.items()};gi={m:int(c*dg) for m,c in gp.items()}
        for m,c in mi.items():
            for n,d in gi.items():
                key=tuple(i+j for i,j in zip(m,n));total[key]=total.get(key,0)+c*d
    total={m:c for m,c in total.items() if c}
    assert total=={(0,0,0,0):dm*dg*cert['target']}
    report={'branch':branch,'status':'PASS','certificate_sha256':hashlib.sha256(cp.read_bytes()).hexdigest(),
            'original_first_variation_determinant_and_inverse':True,'all12_Ryser_coefficients':True,
            'all6_residual_correspondences':True,'both_field_maps':True,'integer_cleared_certificate_identity':True,
            'seconds_cumulative':time.monotonic()-start}
    reports.append(report);print(json.dumps(report),flush=True)
out={'status':'PASS','branches':reports,'seconds':time.monotonic()-start,
     'scope':'Independent complete algebraic chain audit for the two equal-D-square B-rank-one boundary branches only. Generic B-rank-one and full L-gct-231 remain open. No Lean theorem.'}
(base/'Bone-equal-D-chain-independent-audit.json').write_text(json.dumps(out,indent=2)+'\n')
