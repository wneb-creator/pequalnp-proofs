from pathlib import Path
from collections import Counter
N=13
D={0,1,3,9}
lines=[{(l+d)%N for d in D} for l in range(N)]
assert all(len(s)==4 for s in lines)
assert all(len(lines[a]&lines[b])==1 for a in range(N) for b in range(a))
assert all(sum(p in s and q in s for s in lines)==1 for p in range(N) for q in range(p))
edges=[(p,l) for l in range(N) for p in sorted(lines[l])]
positive=[(1<<p)|(1<<(N+l)) for p,l in edges]
negative=[]
for S in range(1<<N):
 T=sum(1<<l for l in range(N) if all(not(S>>p&1) for p in lines[l]))
 R=sum(1<<p for p in range(N) if all(not(T>>l&1) or p not in lines[l] for l in range(N)))
 if R==S:negative.append(S|(T<<N))
assert len(set(negative))==len(negative)
assert all(not(any((m>>p&1) and (m>>(N+l)&1) for p,l in edges)) for m in negative)
assert all(all(any(((m|(1<<v))>>p&1) and ((m|(1<<v))>>(N+l)&1) for p,l in edges) for v in range(2*N) if not(m>>v&1)) for m in negative)
Path('/tmp/oec/pequalnp-pilot-138/pg3/tests.txt').write_text('\n'.join(map(str,positive+negative))+'\n')
Path('/tmp/oec/pequalnp-pilot-138/pg3/edges.txt').write_text('\n'.join(f'{p} {l}' for p,l in edges)+'\n')
print('points=lines=',N,'edges=',len(edges),'maximal_independent_sets=',len(negative),'decisive_tests=',len(positive)+len(negative))
print('MIS sizes:',sorted(Counter(m.bit_count() for m in negative).items()))
print('line sets:',[sorted(s) for s in lines])
