from itertools import combinations
import json

def plane(q):
    points=[(a,b) for a in range(q) for b in range(q)]+[(m,) for m in range(q)]+[(q,)]
    lines=[]
    for m in range(q):
        for c in range(q):
            lines.append({points.index((a,(m*a+c)%q)) for a in range(q)}|{points.index((m,))})
    for a in range(q):
        lines.append({points.index((a,b)) for b in range(q)}|{points.index((q,))})
    lines.append(set(range(q*q,len(points))))
    return points,lines

report=[]
for q in (2,3,5,7):
    points,lines=plane(q); n=len(points)
    assert n==q*q+q+1==len(lines)
    assert all(len(L)==q+1 for L in lines)
    assert all(sum(a in L and b in L for L in lines)==1 for a,b in combinations(range(n),2))
    assert all(sum(p in L for L in lines)==q+1 for p in range(n))
    assert all(len(A&B)==1 for A,B in combinations(lines,2))
    tests=0
    # Every at-most-q selected lines leave a witness on each unselected line.
    # Enumerate all selections for q<=3, and all sizes <=2 for larger q.
    for r in range((q if q<=3 else 2)+1):
        for T in combinations(range(n),r):
            union=set().union(*(lines[t] for t in T))
            assert all(L-union for l,L in enumerate(lines) if l not in T)
            tests+=1
    report.append(dict(q=q,n=n,incidences=n*(q+1),line_subsets_tested=tests,minimum_input_sensitivity_floor=2*n-1,target=n*q/100))
print(json.dumps(report,indent=2))
