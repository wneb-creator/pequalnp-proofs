import sys,json,time,subprocess,shutil,hashlib
from pathlib import Path
from datetime import datetime,timezone
cnf=Path(sys.argv[1]);stem=Path(sys.argv[2]);seconds=int(sys.argv[3]);cap=int(sys.argv[4])*1024*1024
exe=shutil.which('cadical');assert exe
proof=stem.with_suffix('.lrat');log=stem.with_suffix('.log');started_utc=datetime.now(timezone.utc).isoformat();start=time.monotonic();reason=None
no_proof=len(sys.argv)>5 and sys.argv[5]=='noproof'
cmd=[exe,'-t',str(seconds),str(cnf)] if no_proof else [exe,'-t',str(seconds),'--lrat=true','--binary=false',str(cnf),str(proof)]
print(datetime.now(timezone.utc).isoformat(),'START','seconds',seconds,'proofcap_bytes',cap,flush=True)
with log.open('w') as out:
 process=subprocess.Popen(cmd,stdout=out,stderr=subprocess.STDOUT)
 while process.poll() is None:
  time.sleep(1)
  proofbytes=proof.stat().st_size if proof.exists() else 0
  free=shutil.disk_usage(cnf.parent).free
  if proofbytes>cap:reason='proof_size_cap'
  elif free<200*1024*1024:reason='free_disk_floor'
  elif time.monotonic()-start>seconds+30:reason='wall_time_fallback'
  if reason:
   process.terminate()
   try:process.wait(timeout=10)
   except subprocess.TimeoutExpired:process.kill();process.wait()
   break
returncode=process.wait();text=log.read_text();statuses=[s for s in text.splitlines() if s.startswith('s ')]
summary=dict(started_utc=started_utc,finished_utc=datetime.now(timezone.utc).isoformat(),command=cmd,returncode=returncode,seconds=round(time.monotonic()-start,3),termination_reason=reason,status=statuses,proof_bytes=proof.stat().st_size if proof.exists() else 0,cnf_sha256=hashlib.sha256(cnf.read_bytes()).hexdigest())
if proof.exists():summary['proof_sha256']=hashlib.sha256(proof.read_bytes()).hexdigest()
if 's SATISFIABLE' in statuses:
 metadata=json.loads(cnf.with_suffix('.json').read_text());n=metadata['n'];m=metadata['s'];width=metadata['width']
 positive={int(z) for line in text.splitlines() if line.startswith('v ') for z in line[2:].split() if int(z)>0}
 def v(kd,j,a):return (kd*(m+1)+j)*width+a+1
 gates=[]
 for j in range(m):
  op=next(o for o in range(4) if v(0,j,o) in positive)
  a=next(k for k in range(n+j+1) if v(1,j,k) in positive)
  b=next(k for k in range(n+j+1) if v(2,j,k) in positive)
  a=999 if a==n+j else a;b=999 if b==n+j else b
  gates.append(dict(op=['and','or','and','not'][op],inputs=[] if op==2 else [a] if op==3 else [a,b]))
 output=next(k for k in range(n+m+1) if v(6,0,k) in positive)
 if output==n+m:output=999
 edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
 bad=[]
 for x in range(1024):
  vals=[bool(x>>i&1) for i in range(10)]+[not bool(x&1)]
  for g in gates:
   ins=[vals[w] if w<len(vals) else False for w in g['inputs']]
   vals.append(all(ins) if g['op']=='and' else any(ins) if g['op']=='or' else not(ins[0] if ins else False))
  actual=vals[output] if output<len(vals) else False;expected=any(x>>a&1 and x>>b&1 for a,b in edges)
  if actual!=expected:bad.append(x)
 data=dict(inputs=n,gates=gates,output=output,free_unary='not',bad_inputs=bad)
 modelpath=stem.with_name(stem.name+('-rejected-model.json' if bad else '-VERIFIED-model.json'));modelpath.write_text(json.dumps(data,indent=2))
 summary['full_truth_table_bad_inputs']=bad;summary['decoded_model']=str(modelpath)
 print('FULL_TRUTH_TABLE', 'REJECTED' if bad else 'VERIFIED', 'bad_count',len(bad),flush=True)
stem.with_name(stem.name+'-monitor.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary),flush=True)
