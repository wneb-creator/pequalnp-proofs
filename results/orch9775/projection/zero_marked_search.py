from pathlib import Path
import json
p=Path('results/orch9775/projection');d=json.loads((p/'graph.json').read_text());N=d['neighbors'];inds=d['independent'];Is=json.loads(Path('results/orch9775/lemmas/notes/private_weights.json').read_text())['survivors']['11'];best={}
for P in inds:
 wide=sum(1<<i for i in range(14) if (N[i]&P).bit_count()==3);opts=[];O=wide
 while True:
  labs=0
  for i in range(14):
   if not O>>i&1:labs|=N[i]&P
  opts.append((O,2*O.bit_count()+labs.bit_count()))
  if not O:break
  O=(O-1)&wide
 for I in Is:
  need=wide&I;bc,O=min((value,O)for O,value in opts if O&need==need)
  bound=bc+need.bit_count()+14-I.bit_count()-P.bit_count()-(P&~I).bit_count()
  if I not in best or best[I]['bound']<bound:best[I]={'I':I,'P':P,'wide':wide,'minimumO':O,'bound':bound}
(p/'zero-marked-bounds.json').write_text(json.dumps({'scope':'projected_count underBzero0; allrequiredneighborhoodtriplesoccur; Leanpending','rows':list(best.values())},indent=2)+'\n');print('newexclude',[r for r in best.values()if r['bound']>=12]);print('wanted',[best[i]for i in[63,111,4757,4293,2213]])
