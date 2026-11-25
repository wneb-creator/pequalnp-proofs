"""Search disjoint-pair isotropic planes in all nine Hadamard tangent coordinates.

All 72 individual isotropic lines are checked exactly. Triples of disjoint
coordinate pairs are filtered numerically, then every survivor is checked
by exact polynomial expansion. A rejected numerical filter is not a theorem.
"""

import itertools
import json
from pathlib import Path
import time

import numpy as np
import sympy as sp


def permanent(matrix):
    return sp.expand(sum(sp.prod(matrix[i,p[i]] for i in range(4))
                         for p in itertools.permutations(range(4))))


def cubic(matrix):
    return sp.expand(sum(sp.prod(matrix[i,p[i]] for i in rows)
        for p in itertools.permutations(range(4))
        for rows in itertools.combinations(range(4),3)))


def main():
    start=time.monotonic()
    output=Path('/tmp/oec/pequalnp-pilot-75/gct231/coordinate-pairs.json')
    H=sp.Matrix([[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]])
    basis=[]
    names=[]
    signs=[]
    for i in range(1,4):
        S=sp.zeros(4); S[0,i]=S[i,0]=1/sp.sqrt(6)
        basis.append(H*S*H.T); names.append('b'+str(i)); signs.append(-1)
    for i in range(1,4):
        S=sp.zeros(4); S[i,i]=1
        basis.append(H*S*H.T); names.append('a'+str(i)); signs.append(1)
    for i,j in itertools.combinations(range(1,4),2):
        S=sp.zeros(4); S[i,j]=S[j,i]=1/sp.sqrt(2)
        basis.append(H*S*H.T); names.append('a'+str(i)+str(j)); signs.append(1)
    line_records=[]
    lines=[]
    for i,j in itertools.combinations(range(9),2):
        phase=1 if signs[i]!=signs[j] else sp.I
        for sign in [-1,1]:
            T=basis[i]+sign*phase*basis[j]
            rows=[sum(T[i,j] for j in range(4)) for i in range(4)]
            q=sp.expand(sum(T[i,j]**2 for i in range(4) for j in range(4))-2*sum(r*r for r in rows))
            assert q==0
            c=cubic(T); p=permanent(T)
            constant=c==0 and p==0
            record={'indices':[i,j],'coordinates':[names[i],names[j]],'sign':sign,
                    'phase':str(phase),'cubic':str(c),'quartic':str(p),'constant':constant}
            line_records.append(record)
            if constant:
                lines.append((record,T))
    print(json.dumps({'stage':'lines','checked':len(line_records),'constant':len(lines),
                      'seconds':time.monotonic()-start}),flush=True)
    points=np.array(list(itertools.product([-1.,0.,1.,2.],repeat=3)))
    tested=0; survivors=[]; best=float('inf'); best_record=None
    for triple in itertools.combinations(lines,3):
        if len(set(i for record,_ in triple for i in record['indices']))!=6:
            continue
        tested+=1
        B=np.array([np.array(T.evalf(),dtype=complex) for _,T in triple])
        matrices=1+np.einsum('pi,ijk->pjk',points,B)
        values=np.zeros(len(points),dtype=complex)
        for perm in itertools.permutations(range(4)):
            values+=np.prod(matrices[:,np.arange(4),perm],axis=1)
        error=float(np.max(np.abs(values-24)))
        if error<best:
            best=error; best_record=[record for record,_ in triple]
        if error<1e-7:
            x=sp.symbols('x y z')
            T=sum((value*matrix for value,(_,matrix) in zip(x,triple)),sp.zeros(4))
            polynomial=sp.Poly(permanent(sp.ones(4)+T)-24,*x)
            exact=polynomial.is_zero
            survivors.append({'lines':[record for record,_ in triple],
                'numerical_error':error,'exact_constant':exact,'polynomial':str(polynomial.as_expr()),
                'matrix':[[str(T[i,j]) for j in range(4)] for i in range(4)]})
            print(json.dumps({'stage':'survivor','exact_constant':exact,'error':error}),flush=True)
    result={'names':names,'lines':line_records,'triples_tested':tested,'best_numeric_error':best if tested else None,
        'best_lines':best_record,'survivors':survivors,'seconds':time.monotonic()-start,
        'scope':'Exact line checks; numeric triple rejection; exact survivor checks only.'}
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['lines','best_lines','survivors']}),flush=True)


if __name__=='__main__':main()
