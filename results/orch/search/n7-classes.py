from itertools import combinations,permutations
from pathlib import Path
import json
n=7;ps=list(combinations(range(n),2));idx={p:i for i,p in enumerate(ps)};perms=list(permutations(range(n)));seen=set();classes=[]
for chosen in combinations(range(len(ps)),9):
 m=sum(1<<i for i in chosen)
 if m in seen:continue
 h=[0]*n;es=[ps[i]for i in chosen]
 for i,j in es:h[i]|=1<<j;h[j]|=1<<i
 if any((h[i]&h[j]).bit_count()>=2 for i,j in ps):continue
 alpha=max(x.bit_count()for x in range(1<<n)if all(not(h[i]&x)for i in range(n)if x>>i&1))
 for pm in perms:seen.add(sum(1<<idx[tuple(sorted((pm[i],pm[j])))]for i,j in es))
 d={'n':n,'edges':es,'tau':n-alpha};classes.append(d)
 name='n7-class'+str(len(classes));Path('/tmp/oec/pequalnp-pilot-31/search/'+name+'-graph.json').write_text(json.dumps(d))
 print(name,d)
print('classes',len(classes),'labeled',len(seen))
