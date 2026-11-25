from pathlib import Path
import hashlib,json,os,socket,stat,time
BASE=Path('/tmp/oec/pequalnp-pilot-78/toolchain')
PLAN=BASE/'memfd-disk-migration-plan.json'
assert hashlib.sha256(PLAN.read_bytes()).hexdigest()=='5c8a209e0d5480572bb1ecc6302f4a073e9c3383191b395f0a496916e6d248a6'
plan=json.loads(PLAN.read_text());reserve=100*2**20
def free():
    s=os.statvfs(BASE);return s.f_bavail*s.f_frsize
def command(op,paths=None):
    request={'op':op}
    if paths is not None:request['paths']=paths
    with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as s:
        s.connect(str(BASE/'memfd.sock'));s.sendall(json.dumps(request).encode()+b'\n')
        with s.makefile('rb') as stream:answer=json.loads(stream.readline())
    assert answer['ok'],answer
    return answer
def digest(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        while chunk:=f.read(2**20):h.update(chunk)
    return h.hexdigest()
initial=command('status');assert initial['pid']==4303 and initial['bytes']==plan['current_held_bytes']
assert free()-plan['allocated_disk_upper_bound']>=reserve+2**20
done=[];started=time.monotonic()
with(BASE/'private-migration-events.jsonl').open('w')as events:
    for row in plan['files']:
        p=Path(row['path']);amount=((row['bytes']+4095)//4096)*4096
        if free()-amount<reserve+2**18:raise RuntimeError('disk reserve changed; stopping before next intact artifact')
        assert p.is_symlink() and os.readlink(p)==f"/proc/4303/fd/{row['fd']}"
        assert digest(p)==row['sha256']
        reply=command('release',[str(p)])
        assert not p.is_symlink() and p.is_file()
        p.chmod(row['mode']);os.utime(p,ns=(row['atime_ns'],row['mtime_ns']))
        s=p.stat();assert s.st_size==row['bytes'] and stat.S_IMODE(s.st_mode)==row['mode'] and s.st_mtime_ns==row['mtime_ns'] and digest(p)==row['sha256']
        done.append(row);events.write(json.dumps({'path':str(p),'bytes':row['bytes'],'sha256':row['sha256'],'mode':row['mode'],'mtime_ns':row['mtime_ns'],'holder_bytes':reply['bytes'],'free_bytes':free()})+'\n');events.flush()
        if len(done)%25==0:print(json.dumps({'files':len(done),'bytes_recovered':sum(r['bytes']for r in done),'free':free()}),flush=True)
final=command('status');assert final['bytes']==initial['bytes']-sum(r['bytes']for r in done)
report={'pass':True,'files':len(done),'bytes_recovered_from_memfd':sum(r['bytes']for r in done),'holder_before':initial,'holder_after':final,'free_bytes':free(),'seconds':time.monotonic()-started,'plan_sha256':hashlib.sha256(PLAN.read_bytes()).hexdigest(),'rollback':'If required, existing memfd-control.py store accepts these regular .olean.private paths and authenticates bytes before atomic replacement; original holder4GiB cap has room for the entire pre-migration state. No rollback needed.'}
(BASE/'private-migration-result.json').write_text(json.dumps(report,indent=2));print(json.dumps(report),flush=True)
