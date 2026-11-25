from pathlib import Path
import subprocess,sys,time,json
base=Path(__file__).parent
chart,mode=sys.argv[1:3];seconds=int(sys.argv[3]);method=sys.argv[4] if len(sys.argv)>4 else 'f5b'
prefix=chart+'-'+mode+'-'+method
start=time.monotonic()
with (base/(prefix+'.log')).open('w') as out:
 try:
  r=subprocess.run(['python3',str(base/'chart_groebner.py'),chart,mode,method],stdout=out,stderr=subprocess.STDOUT,timeout=seconds)
  result={'returncode':r.returncode,'status':'completed' if r.returncode==0 else 'error'}
 except subprocess.TimeoutExpired:
  result={'status':'UNKNOWN_TIME_LIMIT','native_python_timeout_seconds':seconds}
result['wall_seconds']=time.monotonic()-start
(base/(prefix+'-run.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
