import argparse
import json
import re
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('model')
args=parser.parse_args()
base=Path('/tmp/oec/pequalnp-pilot-121/plane3-sat')
data=json.loads((base/'plane3-data.json').read_text())
record=json.loads(Path(args.model).read_text())
assert record['status']==1
model={name:int(value,16 if radix=='x' else 2) for name,radix,value in re.findall(r'([aob][0-9]+) -> #([xb])([0-9a-f]+)',record['result'])}
size=record['size']
gates=[(model[f'o{j}'],model[f'a{j}'],model[f'b{j}']) for j in range(size)]
assert all(op in [0,1] and 0<=a<b<26+j for j,(op,a,b) in enumerate(gates))
rows=data['rows']
values=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(26)]
target=0
for p,l in data['edges']:
    target|=values[p]&values[l]
for op,a,b in gates:
    values.append(values[a]&values[b] if op==0 else values[a]|values[b])
error=values[-1]^target
failures=[r for k,r in enumerate(rows) if (error>>k)&1]
read_counts=[]
for p,l in data['edges']:
    counts=[{(1,0)} if i==p else {(0,1)} if i==l else set() for i in range(26)]
    for op,a,b in gates:
        counts.append({(min(x+y,2),min(xx+yy,2)) for x,xx in counts[a] for y,yy in counts[b]} if op==0 else counts[a]|counts[b])
    read_counts.append({'edge':[p,l],'vectors':sorted(counts[-1]),'joint_read1':(1,1) in counts[-1]})
result={'size':size,'errors':len(failures),'failures':failures,'gates':gates,'output':26+size-1,'read_counts':read_counts}
path=base/f'verified-{record["seed"]}.json'
path.write_text(json.dumps(result,indent=2))
(base/f'gates-{record["seed"]}.txt').write_text(''.join(' '.join(map(str,g))+'\n' for g in gates))
print(json.dumps({'size':size,'errors':len(failures),'read1_edges':sum(x['joint_read1'] for x in read_counts),'canonical_vectors':next(x['vectors'] for x in read_counts if x['edge']==[0,13])}))
