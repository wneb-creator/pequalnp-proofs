from pathlib import Path
import json,time
root=Path('/tmp/oec/pequalnp-pilot-10/root984');out=Path(__file__).resolve().parent
start=time.monotonic();summaries=[]
for graph in range(26,31):
 prefix=f'compact{graph}';m=json.loads((root/(prefix+'.meta.json')).read_text());k=m['k']
 neg=list(dict.fromkeys(m['negative_rows']));pos=list(dict.fromkeys(m['positive_rows']));nn=len(neg);np=len(pos)
 assert m['negative_rows']==[n for n in neg for p in pos]
 assert m['positive_rows']==[p for n in neg for p in pos]
 coords=[i*np for i in range(nn)]+[k+j for j in range(np)];totalrows=nn+np
 compress_cache={}
 def compress(w):
  if w not in compress_cache:compress_cache[w]=sum(((w>>j)&1)<<i for i,j in enumerate(coords))
  return compress_cache[w]
 def canonical(ws):
  xs=tuple(sorted(ws));seen=set();steps=0
  while xs not in seen and steps<64:
   seen.add(xs);steps+=1
   sig=[sum(((w>>i)&1)<<j for j,w in enumerate(xs)) for i in range(totalrows)]
   perm=sorted(range(nn),key=lambda i:sig[i])+sorted(range(nn,totalrows),key=lambda i:sig[i])
   ys=tuple(sorted(sum(((w>>old)&1)<<new for new,old in enumerate(perm)) for w in xs))
   if ys==xs:return xs,steps
   xs=ys
  return xs,steps
 layers=[];maxsteps=0
 for s in range(m['budget'],-1,-1):
  states=[json.loads(line) for line in (root/f'{prefix}.layer{s}.jsonl').read_text().splitlines()]
  images=set()
  for ws in states:
   key,steps=canonical([compress(int(w,16)) for w in ws]);images.add(key);maxsteps=max(maxsteps,steps)
  layers.append({'layer':s,'original':len(states),'row_column_images':len(images)})
 report={'graph':graph,'negative_rows':nn,'positive_rows':np,'layers':layers,'total_original':sum(x['original'] for x in layers),'total_images':sum(x['row_column_images'] for x in layers),'max_sort_iterations':maxsteps,'elapsed_seconds':time.monotonic()-start,'claim':'Computational quotient experiment only; no Lean transport proof or complete isomorphism canonicalization.'}
 summaries.append(report);print(json.dumps(report),flush=True)
(out/'row_symmetry_measurement.json').write_text(json.dumps(summaries,indent=2)+'\n')
