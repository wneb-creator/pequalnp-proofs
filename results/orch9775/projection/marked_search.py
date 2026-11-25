from pathlib import Path
import json,itertools
p=Path('results/orch9775/projection');d=json.loads((p/'graph.json').read_text());N=d['neighbors'];inds=d['independent'];best={}
for I in [127,1290,4757,8488,16256]:
 for P in inds:
  wide=sum(1<<i for i in range(14) if (N[i]&P).bit_count()==3)
  wideI=wide&I; choices=[]
  O=wide
  while True:
   if (wideI&~O).bit_count()<=1:
    labels=0
    for i in range(14):
     if not O>>i&1:labels|=N[i]&P
    bound=2*O.bit_count()+wideI.bit_count()+labels.bit_count()+14-I.bit_count()-P.bit_count()-(P&~I).bit_count()
    choices.append((bound,O,labels))
   if O==0:break
   O=(O-1)&wide
  bound,O,labels=min(choices)
  if I not in best or best[I]['bound']<bound:best[I]={'I':I,'P':P,'wide':wide,'minimumO':O,'labels':labels,'bound':bound,'choices':choices}
(p/'marked-bounds.json').write_text(json.dumps({'scope':'projected_count plus at-most-one missing wide inelig center under Bzero<=1; finite check only','rows':list(best.values())},indent=2)+'\n')
print(list(best.values()))
