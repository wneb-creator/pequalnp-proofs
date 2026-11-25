from pathlib import Path
import json,itertools
p=Path('results/orch9775/projection');d=json.loads((p/'graph.json').read_text());N=d['neighbors'];inds=d['independent'];rec={};nv=0;cs=[]
for P in inds:
 for i in range(14):
  if (P&N[i]).bit_count()==3:nv+=1;rec[P,i]=nv
for P in inds:
 for Q in inds:
  if P&Q==P:
   for i in range(14):
    if (P,i) in rec:cs.append([-rec[Q,i],rec[P,i]])
for I in [127,16256]:
 out=cs[:]
 for P in inds:
  wide=[i for i in range(14) if(P,i) in rec];Iw=[i for i in wide if I>>i&1]
  for i,j in itertools.combinations(Iw,2):out.append([rec[P,i],rec[P,j]])
  for choice in range(1<<len(wide)):
   O=sum(1<<i for k,i in enumerate(wide) if choice>>k&1); labels=0
   for i in range(14):
    if not O>>i&1:labels|=N[i]&P
   b=2*O.bit_count()+len(Iw)+labels.bit_count()+14-I.bit_count()-P.bit_count()-(P&~I).bit_count()
   if b>10:out.append([-rec[P,i] if O>>i&1 else rec[P,i] for i in wide])
 f=Path(f'/tmp/oec/pequalnp-pilot-103/9775-global-marks-{I}.cnf')
 f.write_text(f'p cnf {nv} {len(out)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in out));print(I,nv,len(out))
(p/'global-marks-map.json').write_text(json.dumps([[P,i,v]for(P,i),v in rec.items()])+'\n')
