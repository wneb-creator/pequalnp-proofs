import subprocess,time,json,signal,resource,psutil,sys,hashlib,datetime
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-75/gct231/case2-necessity')
source=Path(sys.argv[1]) if len(sys.argv)>1 else base/'Case2NecessaryResultants.lean'
tag=sys.argv[2] if len(sys.argv)>2 else 'build01'
rootdir=Path('/workspace/pequalnp-proofs/lean')
packages=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib']
tool='/tmp/oec/pequalnp-pilot-75/lean-tools/lean-4.36.0-linux'
env={'LEAN_PATH':':'.join([str(rootdir/'.lake/packages'/n/'.lake/build/lib/lean') for n in packages]+[str(rootdir/'.lake/build/lib/lean'),tool+'/lib/lean'])}
start=time.monotonic();peak=0;reason=None;last_write=0
initial_hash=hashlib.sha256(source.read_bytes()).hexdigest()
with (base/(tag+'.log')).open('w') as log:
    proc=subprocess.Popen([tool+'/bin/lean','-j1',str(source)],stdout=log,stderr=subprocess.STDOUT,start_new_session=True,env=env)
    while proc.poll() is None:
        current=0
        try:
            parent=psutil.Process(proc.pid)
            current=sum(p.memory_info().rss for p in [parent]+parent.children(recursive=True) if p.is_running())//1024
            peak=max(peak,current)
        except psutil.Error:pass
        elapsed=time.monotonic()-start
        if elapsed-last_write>5:
            (base/(tag+'-progress.json')).write_text(json.dumps({'seconds':elapsed,'rss_kib':current,'peak_rss_kib':peak,'status':'RUNNING'},indent=2))
            last_write=elapsed
        if peak>4*1024**2:reason='RSS_LIMIT';proc.kill();break
        if elapsed>90:reason='TIME_LIMIT';proc.kill();break
        time.sleep(.2)
    code=proc.wait()
record={'source':str(source),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'source_unchanged':initial_hash==hashlib.sha256(source.read_bytes()).hexdigest(),
 'exit_code':code,'seconds':time.monotonic()-start,'peak_rss_kib':peak,
 'resource_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'reason':reason,
 'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
assert record['source_unchanged']
(base/(tag+'.json')).write_text(json.dumps(record,indent=2))
if code==0:
    source.chmod(0o444)
    (base/(tag+'.log')).chmod(0o444)
    (base/(tag+'-frozen.json')).write_text(json.dumps(record,indent=2))
print(json.dumps(record,indent=2),flush=True)
