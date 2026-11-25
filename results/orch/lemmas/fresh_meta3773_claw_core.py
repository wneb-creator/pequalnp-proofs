from pathlib import Path
from itertools import combinations
p=Path(__file__).resolve().parent
X=set(range(3));Y=set(range(3,7));N=[{3,4+i} for i in range(3)];E=[(i,j)for i in X for j in sorted(N[i])]
tests=[{i,j} for i,j in E]; tests+=[set(P)|(Y-set.union(set(),*(N[i] for i in P)))for k in range(4) for P in combinations(X,k)]
def mask(S):return sum(1<<k for k,T in enumerate(tests) if S&T)
leaves={mask({v})for v in X|Y}|{mask(set(T))for k in [2,3]for T in combinations(range(4,7),k)}
(p/'fresh-meta3773-claw-cse-input.txt').write_text(' '.join(map(str,[1<<len(tests),7,(1<<len(E))-1,len(leaves),*sorted(leaves)]))+'\n')
print('six edges',E,'negative separators',tests[6:],'leaves',len(leaves))
