from pathlib import Path
from collections import Counter,defaultdict
import json,re,runpy
scope=runpy.run_path('/tmp/oec/pequalnp-pilot-184/search/pool-storage.py')
source,words,read,spans=scope['source'],scope['words'],scope['read'],scope['spans']
profiles=json.loads(Path('/tmp/oec/pequalnp-pilot-184/search/pool-order.json').read_text())['profiles']
bykey={(x['name'],x['k'],x['i']):x for x in profiles}
changed=[];totalold=totalnew=0
origwords={n:dict(w) for n,w in words.items()}
for span,keys in spans.items():
 table,start,width,n=span
 if n<2:continue
 ps=[bykey[k] for k in keys]
 ids=ps[0]['ids'];assert all(p['ids']==ids for p in ps)
 counts=Counter()
 for p in ps:counts.update({int(m):c for m,c in p['counts'].items()})
 def cost(order):return sum(c*next((r+1 for r,j in enumerate(order) if m>>j&1),n) for m,c in counts.items())
 old=cost(range(n));remaining=dict(counts);remaining.pop(0,None);order=[];unselected=list(range(n))
 while unselected:
  j=max(unselected,key=lambda j:sum(c for m,c in remaining.items() if m>>j&1))
  order.append(j);unselected.remove(j);remaining={m:c for m,c in remaining.items() if not m>>j&1}
 new=cost(order);totalold+=old
 if new>=old:totalnew+=old;continue
 totalnew+=new;newids=[ids[j] for j in order]
 assert Counter(ids)==Counter(newids)
 for j,value in enumerate(newids):
  assert value<1<<width
  pos=start+j*width
  for b in range(width):
   wi,bi=divmod(pos+b,4096);v=words[table].get(wi,0);bit=(value>>b)&1
   words[table][wi]=(v|(1<<bi)) if bit else (v&~(1<<bi))
 changed.append({'span':span,'nodes':keys,'old':ids,'new':newids,'old_scans':old,'new_scans':new})
for span,keys in spans.items():
 table,start,width,n=span
 ids=[read(table,start+j*width,width) for j in range(n)]
 assert Counter(ids)==Counter(bykey[keys[0]]['ids'])
# Copy changes in composite axN tables back to their wordN_j backing declarations.
for name in list(words):
 m=re.fullmatch(r'word(\d+)_(\d+)',name)
 if m:
  table='ax'+m[1]+'Words';base=int(m[2])*8
  for i in words[name]:words[name][i]=words[table][base+i]
changed_literals=[]
def rewrite_decl(m):
 name=m.group(1);body=m.group(2)
 if name not in words:return m.group(0)
 def replace_word(x):
  i=int(x.group(1));old=int(x.group(2),16);new=words[name][i]
  if old==new:return x.group(0)
  changed_literals.append((name,i))
  return x.group(0).replace('0x'+x.group(2),'0x'+format(new,'x').rjust(len(x.group(2)),'0'))
 newbody=re.sub(r'^  \| (\d+) => 0x([0-9a-f]+)',replace_word,body,flags=re.M)
 return m.group(0)[:len(m.group(0))-len(body)]+newbody
result=re.sub(r'^def ([A-Za-z0-9_]+)[^\n]*\n(.*?)(?=^(?:def|theorem|lemma|set_option|end) |\Z)',rewrite_decl,source,flags=re.M|re.S)
# Only natural numeral literals can differ: all code, theorem statements, and helpers identical.
strip=lambda s:re.sub(r'0x[0-9a-f]+','0xN',s)
assert strip(result)==strip(source)
dest=Path('results/orch/lemmas/search/PoolOrdered256.lean');dest.write_text(result)
report={'old_scans':totalold,'new_scans':totalnew,'saved_scans':totalold-totalnew,'spans_changed':len(changed),'nodes_changed':sum(len(c['nodes']) for c in changed),'literals_changed':changed_literals,'changes':changed,'output_bytes':dest.stat().st_size}
Path('/tmp/oec/pequalnp-pilot-184/search/pool-order-report.json').write_text(json.dumps(report,indent=2))
print({k:v for k,v in report.items() if k not in ('changes','literals_changed')})
print('literals_changed',len(changed_literals))
