from pathlib import Path
import json,sys
P=Path(__file__).parent
for t in map(int,sys.argv[1:]or['5','4']):
 d=json.loads((P/f'ExactDagT{t}.json').read_text());rs=d['records'];seen=set();todo=[0]
 while todo:
  a=todo.pop()
  if a in seen:continue
  seen.add(a);r=rs[a]
  if r['kind']==2:todo.extend(r['children'])
 assert all(rs[c]['k']==r['k']-1 for r in rs for c in r['children'])
 assert all(r['kind']in(1,2)for r in rs)
 kept=sorted(seen);ix={a:i for i,a in enumerate(kept)}
 for a in kept:
  r=rs[a];r['source_record']=a;r['children']=sorted(set(ix[c]for c in r['children']))if r['kind']==2 else[]
 d['records']=[rs[a]for a in kept];d['root']=ix[0];d['status']='Native diagnostic only; finite Lean replay not yet checked.'
 (P/f'PrunedDagT{t}.json').write_text(json.dumps(d,separators=(',',':'))+'\n')
