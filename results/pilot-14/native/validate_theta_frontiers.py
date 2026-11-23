from pathlib import Path
import json,collections
base=json.loads(Path('Data414.json').read_text());ds=json.loads(Path('Domains12.json').read_text());top=(1<<414)-1;oldtop=(1<<252)-1;raw=[tuple(int(z,16) for z in r) for r in base['raw']]
def gate(op,a,b=None):return tuple(z^oldtop for z in a) if op==2 else tuple((x&y if op==0 else x|y) for x,y in zip(a,b))
def project(q,s):
 d=ds[q];return tuple(sum(((s[side]>>ix)&1)<<j for j,ix in enumerate(d['pos' if side==0 else 'neg'])) for side in range(2))
checks=0
for t in range(8):
 d=json.loads(Path(f'ThetaFrontier13t{t}.json').read_text());wires=[]
 for w in d['wires']:
  sig=tuple(int(w[k],16) for k in ['p','n']);st=[]
  for op in w['recipe']:
   if op<=9:st.append(raw[op-1])
   elif op==10:st.append(tuple(z^top for z in st.pop()))
   else:
    b=st.pop();a=st.pop();st.append(tuple((x&y if op==11 else x|y) for x,y in zip(a,b)))
  assert st==[sig];wires.append(sig)
 for r in d['records']:
  v=[wires[i] for i in r['v']];assert len(set(v))==len(v);assert (0,0) not in v and (top,top) not in v;excluded=False
  for q,p in enumerate(r['programs']):
   values=[tuple(s) for s in ds[q]['raw']]+[(0,0),(oldtop,oldtop)]
   for g in p['gates']:
    assert all(0<=i<len(values) for i in g[1:]);values.append(gate(g[0],values[g[1]],values[g[2]] if len(g)>2 else None))
   projs=[project(q,s) for s in v];assert [values[i] for i in p['outputs']]==projs
   c=sum(s in [(0,0),(oldtop,oldtop)] for s in projs);excluded|=len(p['gates'])+r['k']<ds[q]['bound']+c
  assert r['kind']!=1 or excluded;checks+=1
 print('verified',t,'records',len(d['records']),'wires',len(wires),'kinds',dict(collections.Counter(r['kind'] for r in d['records'])))
print('all',checks,'records valid')
