from pathlib import Path
import json,itertools,subprocess
out=Path('results/orch9775/projection');data=json.loads((out/'graph.json').read_text());N=data['neighbors'];Ms=data['maximal'];Is=[111,4757,4293,2213]
for I in Is:
 k=I.bit_count()-3;rel=[]
 for x in range(14):
  if I>>x&1:continue
  for c in range(14):
   if x==c:continue
   # Exact geometry copied from checked two_exact/exposed_exact.
   wit=None
   for P in Ms:
    if not(P>>x&1 and P>>c&1):continue
    centers=[i for i in range(14) if I>>i&1 and N[i]>>x&1 and not N[i]>>c&1]
    for i,j in itertools.permutations(centers,2):
     ys=P&N[i]&~N[j]
     if ys:
      y=(ys&-ys).bit_length()-1;wit=['two',P,i,j,x,c,y];break
    if wit:break
    for i in centers:
     for A in Ms:
      ys=P&A&N[i]
      if A>>c&1 and N[x]&A and ys:
       y=(ys&-ys).bit_length()-1;wit=['exposed',P,A,i,x,c,y];break
     if wit:break
    if wit:break
   if wit:
    common=next((i for i in range(14) if I>>i&1 and N[i]>>x&1 and N[i]>>c&1),None)
    rel.append({'x':x,'c':c,'strict':common is not None,'common_center':common,'witness':wit})
 cs=[];nv=14*k
 def var(x,t):return 1+x*k+t
 for x in range(14):
  if I>>x&1:
   cs += [[-var(x,t)]for t in range(k)]
 for r in rel:
  x,c=r['x'],r['c'];diff=[]
  for t in range(k):
   nv+=1;v=nv;diff.append(v);cs += [[-v,var(x,t)],[-v,-var(c,t)],[v,-var(x,t),var(c,t)]]
  if r['strict']:cs.append(diff)
  else:
   for t in range(k):cs.append([-var(x,t)]+diff)
 cnf=Path(f'/tmp/oec/pequalnp-pilot-103/9775-code-{I}.cnf');cnf.write_text(f'p cnf {nv} {len(cs)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in cs))
 with(out/f'code-{I}.stdout').open('w')as f,(out/f'code-{I}.stderr').open('w')as g:cp=subprocess.run(['/tmp/oec/pequalnp-pilot-103/setup/lean-4.36.0-linux/bin/cadical','-t','5',str(cnf)],stdout=f,stderr=g)
 (out/f'code-{I}.json').write_text(json.dumps({'I':I,'k':k,'relations':rel,'exit_code':cp.returncode,'clauses':len(cs),'vars':nv,'scope':'Necessary residualsetrelations; noactualcircuit/noLeanproof yet'},indent=2)+'\n');print(I,k,len(rel),cp.returncode,flush=True)
