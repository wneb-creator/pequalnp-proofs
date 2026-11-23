from pathlib import Path
import json
root=Path('/tmp/oec/pequalnp-pilot-10/proof-strategy/meta984');out=Path(__file__).resolve().parent
with (out/'exact_symmetry_states.txt').open('w') as f:
 f.write('5\n')
 for graph in range(26,31):
  m=json.loads((root/f'quotient{graph}.meta.json').read_text());k=m['k'];neg=list(dict.fromkeys(m['negative_rows']));pos=list(dict.fromkeys(m['positive_rows']));nn=len(neg);np=len(pos)
  assert m['negative_rows']==[n for n in neg for p in pos] and m['positive_rows']==[p for n in neg for p in pos]
  coords=[j*np for j in range(nn)]+[k+j for j in range(np)];repeat=sum(1<<(np*j) for j in range(nn));cache={};states=[]
  for s in range(m['budget'],-1,-1):
   for line in (root/f'quotient{graph}.layer{s}.jsonl').read_text().splitlines():
    cols=[]
    for x in json.loads(line):
     if x not in cache:
      w=int(x,16);z=sum(((w>>j)&1)<<i for i,j in enumerate(coords))
      expanded=sum(((z>>i)&1)*((1<<np)-1)<<(np*i) for i in range(nn))|(((z>>nn)*repeat)<<k)
      assert expanded==w
      cache[x]=z
     cols.append(cache[x])
    states.append((s,cols))
  f.write(f'{graph} {nn} {np} {len(states)}\n')
  for s,cols in states:f.write(' '.join(map(str,[s,len(cols)]+cols))+'\n')
print('Prepared five exact quotient experiments; every compact wire round-trips to its original Nat.')
