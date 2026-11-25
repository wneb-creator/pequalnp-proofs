import json,sys,itertools
from pathlib import Path
p=Path(sys.argv[1]);d=json.loads(p.read_text());G=d['graph'];n=G['n'];gates=d['gates'];output=d['output'];E={tuple(sorted(e))for e in G['edges']};anc=[];tt=[]
for j,(op,a,b)in enumerate(gates):
 assert op in ['and','or']and 0<=a<n+j and 0<=b<n+j
 anc.append(({a-n}|anc[a-n]if a>=n else set())|({b-n}|anc[b-n]if b>=n else set()))
for x in range(1<<n):
 w=[bool(x>>i&1)for i in range(n)]
 for op,a,b in gates:w.append((w[a]and w[b])if op=='and'else(w[a]or w[b]))
 tt.append(w)
errors=[x for x in range(1<<n)if tt[x][output]!=any(tt[x][u]and tt[x][v]for u,v in E)]
adj=lambda u,v:tuple(sorted((u,v)))in E
triangles=[list(S)for S in itertools.combinations(range(n),3)if all(adj(u,v)for u,v in itertools.combinations(S,2))]
squares=[list(S)for S in itertools.combinations(range(n),4)if any(all(adj(P[i],P[(i+1)%4])for i in range(4))for P in itertools.permutations(S))]
cover=min(x.bit_count()for x in range(1<<n)if all((x>>u&1)or(x>>v&1)for u,v in E))
owners=[]
for j,(op,a,b)in enumerate(gates):
 if op!='and':continue
 es=[e for e in sorted(E)if tt[(1<<e[0])|(1<<e[1])][n+j]and all(not tt[(1<<e[0])|(1<<e[1])][n+i]for i in anc[j]if gates[i][0]=='and')]
 owners.append({'gate':j,'wire':n+j,'edges':es,'centers':sorted(set.intersection(*(set(e)for e in es)))if es else[]})
print(json.dumps({'file':p.name,'size':len(gates),'and_count':sum(g[0]=='and'for g in gates),'or_count':sum(g[0]=='or'for g in gates),'errors':errors,'triangles':triangles,'squares':squares,'vertex_cover':cover,'ownership':owners},indent=2))
