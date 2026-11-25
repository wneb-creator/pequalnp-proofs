import sys,json,time,random,hashlib,argparse,subprocess
from pathlib import Path
from abc_phase import optimize,read_aig
P=Path('/tmp/oec/pequalnp-pilot-109/audit');ABC=P/'abc-tool/abc-master/abc'
p=argparse.ArgumentParser();p.add_argument('--seconds',type=int,default=600);p.add_argument('--seed',type=int,default=109);a=p.parse_args()
D=P/'abc-runs';D.mkdir(exist_ok=True);rng=random.Random(a.seed);start=time.time();best=999;bestbin=999;pool=[];seen=set();counter=0
resyn='balance; rewrite; refactor; balance; rewrite; rewrite -z; balance; refactor -z; rewrite -z; balance'
flows=[resyn,'balance; resub -K 10 -N 3; rewrite -z; refactor -z; balance','dc2; dc2; rewrite -z; dc2','dch; if -K 4 -a; mfs2 -a; strash; '+resyn,'if -K 6 -a; mfs2 -a -e; strash; refactor -z; resub -K 10 -N 3','if -K 10 -a -d; strash; '+resyn]
def run(source,flow):
 global best,bestbin,counter,pool
 k=counter;counter+=1;out=D/('r%05d.aig'%k);cmd=('read_blif ' if str(source).endswith('.blif') else 'read_aiger ')+str(source)+'; strash; '+flow+'; strash; print_stats; write_aiger '+str(out)
 (D/('r%05d.cmd'%k)).write_text(cmd+'\n')
 try:
  with (D/('r%05d.stdout'%k)).open('w') as fo,(D/('r%05d.stderr'%k)).open('w') as fe:r=subprocess.run([str(ABC),'-s','-c',cmd],cwd=P,stdout=fo,stderr=fe,timeout=25)
 except subprocess.TimeoutExpired:
  print('timeout',k,flush=True);return False
 if r.returncode!=0 or not out.exists():print('tool_failure',k,r.returncode,flush=True);return False
 try:d=optimize(out)
 except Exception as ex:print('validation_failure',k,str(ex),flush=True);return False
 if d['size']<best or d['binary']<bestbin:
  best=min(best,d['size']);bestbin=min(bestbin,d['binary']);print('improvement',k,'binary',d['binary'],'nots',d['nots'],'size',d['size'],'source',str(source),'flow',flow,flush=True)
  (D/('r%05d-circuit.json'%k)).write_text(json.dumps(d)+'\n')
 if (d['size']<=19 and d['nots']>=1) or d['size']<=18:
  (P/'abc-witness.json').write_text(json.dumps(d)+'\n');print('WITNESS',k,json.dumps(d),flush=True);return True
 I,g,o=read_aig(out);sig=repr((g,o))
 if sig not in seen and d['size']<=best+4 and d['binary']<=bestbin+2:
  seen.add(sig);pool.append((d['size'],d['binary'],str(out)));pool.sort();pool=pool[:150]
 if k%20==0:print('progress',k,'seconds',round(time.time()-start,1),'best',best,'best_binary',bestbin,'pool',len(pool),flush=True)
 return False
sources=[P/'seeds'/('seed-%02d.blif'%i) for i in range(40)]+[P/'petersen.blif']
for s in sources:
 if run(s,flows[rng.randrange(len(flows))]):sys.exit(0)
while time.time()-start<a.seconds:
 source=Path(rng.choice(pool)[2]) if pool and rng.random()<0.75 else rng.choice(sources)
 flow='; '.join(rng.choices(flows,k=rng.randrange(1,4)))
 if run(source,flow):sys.exit(0)
print('DONE seconds',time.time()-start,'candidates',counter,'best',best,'best_binary',bestbin,'pool',len(pool),flush=True)
(P/'abc-pool.json').write_text(json.dumps(pool)+'\n')
