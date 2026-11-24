import json,sys
from pathlib import Path
from itertools import combinations_with_replacement
base=Path(__file__).resolve().parent;path=Path(sys.argv[1]);d=json.loads(path.read_text());assert d['result']=='sat';N=len(d['rows']);n=2*N;R=1<<n;ALL=(1<<R)-1;edges=set(map(tuple,d['edges']));circ=d['circuit'];inp=[sum(1<<r for r in range(R)if r>>i&1)for i in range(n)];target=sum(1<<r for r in range(R)if any((r>>i&1)and(r>>(N+j)&1)for i,j in edges));forbidden=sum(1<<(1<<i)for i in range(n))|sum(1<<((1<<i)|(1<<(N+j)))for i in range(N)for j in range(N)if(i,j)not in edges)
def evaluate(replace=None):
 vals=inp.copy();ops=[]
 for j,(op,a,b)in enumerate(circ):
  args=[a,b]
  if replace and j==replace[0]:op,args=replace[1],replace[2]
  v=ALL if op=='and'else 0
  for k in args:v=(v&vals[k])if op=='and'else(v|vals[k])
  vals.append(v);ops.append(op)
 return vals,ops
vals,ops=evaluate();assert vals[-1]==target;bad=[j for j,op in enumerate(ops)if op=='and'and vals[n+j]&forbidden];unsafe=[j for j in range(len(circ))if vals[n+j]&(ALL^target)];out={'id':d['id'],'minimum_size':len(circ),'dirty_gates':bad,'latest_globally_unsafe_gate':{'index':unsafe[-1],'operation':ops[unsafe[-1]]}if unsafe else None,'replacements':{}}
for j in bad:
 options=[];k=n+j
 for op in ['and','or']:
  options.append((op,[]));options.extend((op,[a])for a in range(k));options.extend((op,[a,b])for a,b in combinations_with_replacement(range(k),2))
 matches=[]
 for op,args in options:
  vs,os=evaluate((j,op,args))
  if vs[-1]!=target or (op=='and'and vs[n+j]&forbidden):continue
  bad_after=[a for a,t in enumerate(os)if t=='and'and vs[n+a]&forbidden];matches.append({'op':op,'inputs':args,'dirty_after':bad_after})
 out['replacements'][str(j)]={'tested':len(options),'valid_cleanup_count':len(matches),'matches':matches}
(base/(d['id']+'_local_diagnosis.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
