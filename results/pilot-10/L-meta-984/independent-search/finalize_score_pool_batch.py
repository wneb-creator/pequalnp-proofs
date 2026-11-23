from pathlib import Path
import json,hashlib,collections,sys,re
prefix=sys.argv[1]; p=Path(sys.argv[2]); source=Path(__file__).resolve().parent; root=Path('/tmp/oec/pequalnp-pilot-10/root984')
meta=json.loads((root/(prefix+'.meta.json')).read_text())
m=json.loads((p/'score_coordinate_map.json').read_text()); k=m['k']; goal=((1<<k)-1)<<k
pool=[]
for line in (p/'score_pool_indices.txt').read_text().splitlines():
 a,b,c,d,e,f=map(int,line.split())
 coords=[m['positive_coordinate_indices'][a],m['positive_coordinate_indices'][b],m['positive_coordinate_indices'][c],m['negative_coordinate_indices'][d],m['negative_coordinate_indices'][e],m['negative_coordinate_indices'][f]]
 code=sum(v<<(10*i) for i,v in enumerate(coords)); assert all(v<1024 for v in coords)
 pool.append({'coordinates':coords,'code':code})
cache={}
def value(w,coord):
 key=(w,tuple(coord))
 if key in cache:return cache[key]
 a,b,c,d,e,f=[bool((w>>j)&1) for j in coord]
 x=int(b)+int(c); y=int(not e)+int(not f)
 z=(y if d else max(x,y,x+y-1)) if a else (0 if d else x)
 cache[key]=z; return z
for c in pool: assert value(goal,c['coordinates'])==3
uncovered=[]; total=0; covered=0; layers=collections.Counter(); remaining=collections.Counter()
for s in range(meta['budget'],-1,-1):
 for index,line in enumerate((root/f'{prefix}.layer{s}.jsonl').read_text().splitlines()):
  wires=[int(w,16) for w in json.loads(line)]
  if len(wires)!=s+1:continue
  total+=1
  if any(sum(value(w,c['coordinates']) for w in wires)<3 for c in pool): covered+=1; layers[s]+=1
  else: uncovered.append({'layer':s,'index':index,'wires_hex':[hex(w) for w in wires]}); remaining[s]+=1
summary=re.search(r'DONE states=(\d+) pool=(\d+) covered=(\d+) remaining=(\d+) seeds=(\d+)',(p/'score_pool.log').read_text())
assert summary is not None
assert total==int(summary[1]) and len(pool)==int(summary[2]) and covered==int(summary[3]) and len(uncovered)==int(summary[4])
report={'graph':prefix,'k':k,'codes':[c['code'] for c in pool],'pool':pool,'tight_states':total,'covered':covered,'uncovered':len(uncovered),'covered_by_layer':dict(layers),'uncovered_by_layer':dict(remaining),'validation':'Independent scalar value6 evaluation of original raw wire Nats for every tight state; target score3 for every code; counts match complete C++ log.','source_sha256':{s:hashlib.sha256((source/s).read_bytes()).hexdigest() for s in ['prepare_score_states_batch.py','score_pool.cpp','finalize_score_pool_batch.py']}}
(p/'score_pool.json').write_text(json.dumps(report,indent=2)+'\n')
(p/'score_uncovered.json').write_text(json.dumps({'k':k,'goal_hex':hex(goal),'coordinate_map':m,'states':uncovered},indent=2)+'\n')
print(json.dumps({key:report[key] for key in ['k','tight_states','covered','uncovered','covered_by_layer','uncovered_by_layer']}))
