from pathlib import Path
root=Path('/tmp/oec/pequalnp-pilot-138/pg3')
edges=[tuple(map(int,l.split())) for l in (root/'edges.txt').read_text().splitlines()]
cases=[tuple(map(int,l.split())) for l in (root/'matching-audit-cases.txt').read_text().splitlines()]
for case,(removed,claimed) in enumerate(cases):
 adj=[0]*13
 for e,(p,l) in enumerate(edges):
  if not(removed>>e&1):adj[p]|=1<<l
 unions=[0]*8192
 optimum=13
 for U in range(1,8192):
  v=U&-U
  unions[U]=unions[U^v]|adj[v.bit_length()-1]
  optimum=min(optimum,13-U.bit_count()+unions[U].bit_count())
 assert optimum==claimed,(case,removed,claimed,optimum)
print('PASS:',len(cases),'C++ bipartite matching results agree with exhaustive enumeration of all8192 point-side vertex-cover choices each.')
