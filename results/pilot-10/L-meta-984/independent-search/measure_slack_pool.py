from pathlib import Path
import json,collections
root=Path('/tmp/oec/pequalnp-pilot-10/root984');p=Path(__file__).resolve().parent
pool=json.loads((p/'score_pool.json').read_text())['pool'];cache={}
def score(w,coords):
 key=(w,tuple(coords))
 if key in cache:return cache[key]
 a,b,c,d,e,f=[(w>>v)&1 for v in coords];x=b+c;y=2-e-f
 r=(y if d else max(x,y,x+y-1)) if a else (0 if d else x)
 cache[key]=r;return r
summary=[]
for s in range(11,-1,-1):
 total=0;hits=0;examples=[];bywidth=collections.Counter();hitwidth=collections.Counter()
 for index,line in enumerate((root/f'shard28.layer{s}.jsonl').read_text().splitlines()):
  wires=[int(w,16) for w in json.loads(line)];slack=s+1-len(wires)
  if slack<=0:continue
  total+=1;bywidth[len(wires)]+=1;threshold=2 if slack==1 else 1
  if any(sum(score(w,c['coordinates']) for w in wires)<threshold for c in pool):
   hits+=1;hitwidth[len(wires)]+=1
   if len(examples)<3:examples.append(index)
 summary.append({'layer':s,'non_tight_states':total,'pruned_if_slack_lemma':hits,'bywidth':dict(bywidth),'hits_bywidth':dict(hitwidth),'examples':examples})
(p/'score_slack_measurement.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary))
