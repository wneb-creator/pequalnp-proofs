import json,sys
from pathlib import Path
p=Path(sys.argv[1]);d=json.loads(p.read_text());n=d['graph']['n'];andcount=d['basis']=='and';free='or' if andcount else 'and';charged=d['basis'];gates=[];cache={};mapping={i:i for i in range(n)}
def gate(op,a,b):
 if a==b:return a
 key=(op,min(a,b),max(a,b))
 if key not in cache:cache[key]=n+len(gates);gates.append(key)
 return cache[key]
def cone(indices):
 assert indices
 vals=[mapping[i]for i in indices]
 while len(vals)>1:
  hit=next(((a,b)for a in vals for b in vals if a<b and(free,a,b)in cache),None)
  if hit is None:a,b=vals[:2]
  else:a,b=hit
  vals.remove(a);vals.remove(b);vals.append(gate(free,a,b))
 return vals[0]
for j in range(d['k']):mapping[n+2+j]=gate(charged,cone(d['subsets']['l'+str(j)]),cone(d['subsets']['r'+str(j)]))
output=cone(d['subsets']['out']);tt=[];anc=[]
for op,a,b in gates:
 anc.append(({a-n}|anc[a-n]if a>=n else set())|({b-n}|anc[b-n]if b>=n else set()))
for mask in range(1<<n):
 values=[bool(mask>>i&1)for i in range(n)]
 for op,a,b in gates:values.append((values[a]and values[b])if op=='and'else(values[a]or values[b]))
 tt.append(values)
errors=[mask for mask in range(1<<n)if tt[mask][output]!=any(tt[mask][u]and tt[mask][v]for u,v in d['graph']['edges'])]
owned=[]
for j,(op,a,b)in enumerate(gates):
 if op!='and':continue
 es=[]
 for u,v in d['graph']['edges']:
  vals=tt[(1<<u)|(1<<v)]
  if vals[n+j]and all(not vals[n+i]for i in anc[j]if gates[i][0]=='and'):es.append([u,v])
 centers=sorted(set.intersection(*(set(e)for e in es)))if es else []
 owned.append({'gate':j,'wire':n+j,'edges':es,'centers':centers})
r={'graph':d['graph'],'gates':gates,'output':output,'size':len(gates),'and_count':sum(g[0]=='and'for g in gates),'or_count':sum(g[0]=='or'for g in gates),'errors':errors,'ownership':owned}
p.with_name(p.stem+'_expanded.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
