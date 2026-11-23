from pathlib import Path
import json,sys
root=Path('/tmp/oec/pequalnp-pilot-10/root984')
prefix=sys.argv[1]
out=Path(sys.argv[2]); out.mkdir(parents=True,exist_ok=True)
meta=json.loads((root/(prefix+'.meta.json')).read_text()); k=meta['k']
def representatives(rows):
 seen=set(); result=[]
 for i,x in enumerate(rows):
  if x not in seen: result.append(i); seen.add(x)
 return result
pos=representatives(meta['positive_rows']); neg=representatives(meta['negative_rows'])
coords=[k+i for i in pos]+neg
states=[]
for s in range(meta['budget'],-1,-1):
 for index,line in enumerate((root/f'{prefix}.layer{s}.jsonl').read_text().splitlines()):
  wires=[int(w,16) for w in json.loads(line)]
  if len(wires)!=s+1: continue
  masks=[sum(((w>>j)&1)<<i for i,w in enumerate(wires)) for j in coords]
  states.append((s,index,len(wires),masks))
with (out/'score_states.txt').open('w') as f:
 f.write(f'{len(states)} {len(pos)} {len(neg)}\n')
 for s,index,width,masks in states: f.write(' '.join(map(str,[s,index,width]+masks))+'\n')
(out/'score_coordinate_map.json').write_text(json.dumps({'k':k,'positive_coordinate_indices':[k+i for i in pos],'negative_coordinate_indices':neg,'positive_rows':[meta['positive_rows'][i] for i in pos],'negative_rows':[meta['negative_rows'][i] for i in neg],'tight_states':len(states)},indent=2)+'\n')
print(json.dumps({'tight_states':len(states),'positive_choices':len(pos),'negative_choices':len(neg)}))
