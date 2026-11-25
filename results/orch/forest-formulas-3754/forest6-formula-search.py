import itertools,json,time
n=6
pairs=list(itertools.combinations(range(n),2))
perms=list(itertools.permutations(range(n)))
def canon(es):
 return min(tuple(sorted(tuple(sorted((p[a],p[b]))) for a,b in es)) for p in perms)
def forest(es):
 par=list(range(n))
 def root(v):
  while par[v]!=v:v=par[v]
  return v
 for a,b in es:
  a,b=root(a),root(b)
  if a==b:return False
  par[a]=b
 return True
from pathlib import Path
previous=[json.loads(line)["edges"] for line in Path('/tmp/oec/pequalnp-pilot-152/gap-3754/forest-formula-search.log').read_text().splitlines()]+[[]]
Gs={canon(es+[(i,5) for i in range(5) if m>>i&1]) for es in previous for m in range(32) if forest(es+[(i,5) for i in range(5) if m>>i&1])}
Gs.discard(())
jobStart=time.monotonic()
full=(1<<(1<<n))-1
inputs=[sum(1<<r for r in range(1<<n) if r>>i&1) for i in range(n)]
for es in sorted(Gs,key=lambda es:(len(es),es)):
 if time.monotonic()-jobStart>180:break
 t=time.monotonic();F=sum(1<<r for r in range(1<<n) if any((r>>a&1) and (r>>b&1) for a,b in es))
 tau=min(m.bit_count() for m in range(1<<n) if all(m>>a&1 or m>>b&1 for a,b in es))
 bound=len(es)+tau-1
 bycost=[{(f,False) for f in inputs}]; seen={k:0 for k in bycost[0]}; deriv={}
 dirty=None
 for cost in range(1,bound+1):
  new=set()
  for i in range((cost-1)//2+1):
   j=cost-1-i
   for (a,da),(b,db) in itertools.product(bycost[i],bycost[j]):
    if i==j and (a,da)>(b,db):continue
    for op,c in [(0,a&b),(1,a|b)]:
     if c==a or c==b:continue
     if op and bool(a&~F)!=bool(b&~F):continue
     d=da or db or (op==0 and bool(c&~F));key=(c,d)
     if key in seen or key in new:continue
     new.add(key);deriv[key]=(op,(a,da),(b,db))
  for key in new:seen[key]=cost
  bycost.append(new)
  if (F,True) in seen:
   dirty=cost;break
 def expr(k):
  if k not in deriv:return str(inputs.index(k[0]))
  op,a,b=deriv[k];return ["OR" if op else "AND",expr(a),expr(b)]
 result={"edges":es,"star_bound":bound,"dirty_fixed_formula_cost":dirty,"clean_cost":seen.get((F,False)),"states":len(seen),"seconds":round(time.monotonic()-t,3)}
 if dirty is not None:result["formula"]=expr((F,True))
 print(json.dumps(result),flush=True)
