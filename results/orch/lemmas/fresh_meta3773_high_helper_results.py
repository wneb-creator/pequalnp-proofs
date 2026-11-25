from pathlib import Path
import json,re
S=Path(__file__).resolve().parent;table={}
for mask in (63,126,127):
 vals=[]
 for d in range(9-mask.bit_count()):
  prefix=f'fresh-meta3773-five-1-{mask}-{d}-';j=json.loads((S/(prefix+'progress.json')).read_text());assert not j['hits'] and j['tested']==j['total'];ids=set()
  for fn in S.glob(prefix+'*.log'):
   data=fn.read_text();assert 'result True' not in data
   for n,t in re.findall(r'case (\d+) of (\d+) result False',data):assert int(t)==j['total'];ids.add(int(n))
  assert ids==set(range(1,j['total']+1));vals.append(j['total'])
 table[mask]=vals
print(json.dumps({'orbits':table,'total':sum(map(sum,table.values())),'tested_all':True,'hits':0,'scope':'one-triple patch with six or seven actually used helpers only'},indent=2))
