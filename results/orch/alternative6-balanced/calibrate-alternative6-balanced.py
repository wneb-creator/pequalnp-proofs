from pathlib import Path
import sys,random,hashlib
r=Path('/workspace/pequalnp-proofs/results/orch/lemmas');sys.path.insert(0,str(r));import SearchStochasticAlternative6Balanced as M
rng=random.Random(147729300);valid=invalid=cases=physical=0
for i in range(144):
 linear=[1,2,4,8][i%4];helpers=[1,2,3,4,8,12][i%6];mixed=[1,2,4][(i//4)%3]
 rows,out=M.baseline(rng,linear,helpers,mixed);ev=M.evaluate(rows,out);gates,output=M.expand_rows(M.N,rows,out,ev[3]);assert len(gates)==ev[0]
 for j,(op,refs) in enumerate(gates):assert len(refs)==2 and all(0<=v<M.N+j for v in refs)
 wp=wn=0
 for x in sorted(M.POSITIVES|M.RAW_NEGATIVES):
  vs=[bool(x>>j&1) for j in range(M.N)]
  for op,(a,b) in gates:vs.append(vs[a] and vs[b] if op=='and' else vs[a] or vs[b])
  expected=any(x>>a&1 and x>>b&1 for a,b in M.EDGES)
  wp+=expected and not vs[output];wn+=not expected and vs[output];cases+=1
 assert wp==0 and wn==ev[2]
 if wn:invalid+=1
 else:valid+=1
 for z in range(3):
  rows,out=M.mutate(rng,rows,out,linear);ev=M.evaluate(rows,out);gs,oo=M.expand_rows(M.N,rows,out,ev[3]);assert len(gs)==ev[0];vs=list(M.INPUT_MASKS)
  for op,(a,b) in gs:assert 0<=a<len(vs) and 0<=b<len(vs);vs.append(vs[a]&vs[b] if op=='and' else vs[a]|vs[b])
  assert vs[oo]==ev[4];physical+=1
print('PASS144 full88 baselines:',valid,'valid',invalid,'explicitly INVALID,',cases,'scalar cases,',physical,'physical mutants')
print('SOURCE_SHA',hashlib.sha256((r/'SearchStochasticAlternative6Balanced.py').read_bytes()).hexdigest())
print('NEGATIVE_SCALE',M.NEGATIVE_SCALE,'BICLIQUE_STARTS',M.INVALID_BICLIQUE_STARTS)
