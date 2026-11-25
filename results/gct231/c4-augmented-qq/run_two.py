from pathlib import Path
import subprocess,json
b=Path(__file__).resolve().parent;g=b.parent
for case in(2,3):
 src=g/('neogb-c4-augmented'+str(case)+'-qq.in');prefix=b/('case'+str(case))
 with prefix.with_suffix('.driver.log').open('w')as out:
  r=subprocess.run(['python3',str(g/'sparse-engine/run_neogb_trace_compact.py'),str(src),str(prefix),'--seconds','120','--memory-mib','1024','--pairs','32','--output-mib','64'],stdout=out,stderr=subprocess.STDOUT)
 assert r.returncode==0
 status=json.loads(prefix.with_suffix('.run.json').read_text());print(case,status['status'],status['wall_seconds'],flush=True)
 if status['status']!='COMPLETED':continue
 sliced=b/('case'+str(case)+'-slice.trace')
 with(b/('case'+str(case)+'-slice.log')).open('w')as out:
  s=subprocess.run(['python3',str(g/'slice_neogb_trace.py'),str(prefix.with_suffix('.trace')),str(sliced)],stdout=out,stderr=subprocess.STDOUT)
 if s.returncode:print(case,'NO_CERTIFICATE_SLICE',flush=True);continue
 with(b/('case'+str(case)+'-replay.log')).open('w')as out:
  q=subprocess.run(['python3',str(g/'replay_neogb_compact.py'),str(prefix.with_suffix('.f4.in')),str(sliced),str(b/('case'+str(case)+'.certificate.json'))],stdout=out,stderr=subprocess.STDOUT)
 assert q.returncode==0
 data=json.loads((b/('case'+str(case)+'.certificate.json')).read_text());print(case,{'unit_replayed':data['proved_nonzero_constant'],'needed_steps':len(data['needed_steps'])},flush=True)
