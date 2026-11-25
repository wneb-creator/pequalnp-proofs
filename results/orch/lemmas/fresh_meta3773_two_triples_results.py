from pathlib import Path
import json,re,collections
j=Path(__file__).resolve().parent;out={}; cases={0:8,1:7,3:6}
for used,n in cases.items():
 out[used]=[]
 for dup in range(n):
  prefix=f'fresh-meta3773-five-0-{used}-{dup}-';x=json.loads((j/(prefix+'progress.json')).read_text());assert not x['hits'] and x['total']==x['tested']
  seen=set()
  for log in j.glob(prefix+'*.log'):
   data=log.read_text();assert 'result True' not in data
   for idx,tot in re.findall(r'case (\d+) of (\d+) result False',data):
    assert int(tot)==x['total'];seen.add(int(idx))
  assert seen==set(range(1,x['total']+1));out[used].append(x['total'])
print(json.dumps({'orbits':out,'total':sum(map(sum,out.values())),'tested_all':True,'hits':0,'scope':'two-triple reduced patch exhaustive finite-search diagnostic only'},indent=2))
