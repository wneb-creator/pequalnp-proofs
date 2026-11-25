#!/usr/bin/env python3
"""Run unchanged official checker, scheduling exact compilation-only cache storage.

The verifier reads runtime facets, never .c/.ilean. Its Node parent is stopped while
those compilation facets are absent, and resumed only after exact restoration.
No proof, checker, source, configuration, or runtime facet is modified.
"""
import argparse, datetime, errno, hashlib, json, os, resource, signal, stat
import subprocess, sys, tarfile, time, traceback
from pathlib import Path
from watch_runtime_cache_eviction import ProofOpenWatch, prepare_eviction_plan, evict_after_proof_open, PROOF

TASK=Path('/tmp/oec/pequalnp-pilot-182')
REPO=Path('/workspace/pequalnp-proofs')
LEAN=REPO/'lean'
KEEPER=TASK/'ram_cache_keeper.py'
RESTORE=TASK/'restore_compilation_artifacts.py'
VERIFIER=LEAN/'.lake/build/bin/checklemma'
MANIFEST=TASK/'compilation-artifacts-manifest.json'
BACKUP=TASK/'compilation-artifacts.tar.gz'
STAGE='checker stage: verifier reading the built file'

def utc(): return datetime.datetime.now(datetime.timezone.utc).isoformat()

def process_info(pid):
    try:
        raw=Path('/proc')/str(pid)/'stat'
        text=raw.read_text();fields=text[text.rfind(')')+2:].split()
        return {'pid':pid,'state':fields[0],'start':int(fields[19])}
    except (FileNotFoundError,ProcessLookupError): return None

def same_process(identity, allow_zombie=False):
    now=process_info(identity['pid'])
    return bool(now and now['start']==identity['start'] and
                (allow_zombie or now['state'] not in ('Z','X')))

def send(identity,sig):
    if not same_process(identity): return False
    os.kill(identity['pid'],sig)
    return True

def descendants(pid):
    # This container exposes PPid but omits /proc/.../task/.../children.
    # Ask ps only for numeric process metadata: never request arguments or env.
    census=subprocess.run(['ps','-e','-o','pid=,ppid='],stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE,text=True,timeout=5,check=False)
    if census.returncode!=0:
        raise RuntimeError('Numeric process census failed with exit '+str(census.returncode))
    by_parent={}
    for line in census.stdout.splitlines():
        fields=line.split()
        if len(fields)!=2 or not all(value.isascii() and value.isdecimal() for value in fields):
            raise RuntimeError('Unexpected numeric process census shape')
        child,parent=map(int,fields)
        if child<=0 or parent<0:raise RuntimeError('Invalid process identifiers in numeric census')
        by_parent.setdefault(parent,[]).append(child)
    pending=[pid];seen={pid}
    while pending:
        parent=pending.pop()
        for child in by_parent.get(parent,[]):
            if child not in seen:
                seen.add(child);pending.append(child);yield child

def verified_child(node):
    expected=VERIFIER.stat()
    for pid in descendants(node['pid']):
        try:
            actual=(Path('/proc')/str(pid)/'exe').stat()
            if (actual.st_dev,actual.st_ino)!=(expected.st_dev,expected.st_ino): continue
            argv=(Path('/proc')/str(pid)/'cmdline').read_bytes().split(b'\0')
            if len(argv)<5 or argv[1]!=b'PEqualNP.Outside.L_meta_10760' or argv[3]!=b'check':
                raise RuntimeError('Unexpected arguments for official verifier descendant')
            identity=process_info(pid)
            if identity and same_process(identity): return identity
        except (FileNotFoundError,ProcessLookupError): continue
    return None

def keeper_identity():
    pid=int((TASK/'ram-cache-3.pid').read_text())
    identity=process_info(pid)
    if not identity or not same_process(identity): raise RuntimeError('Keeper3 is not alive')
    argv=(Path('/proc')/str(pid)/'cmdline').read_bytes().split(b'\0')
    args=[os.fsdecode(x) for x in argv if x]
    if len(args)!=3 or args[1]!=str(KEEPER) or args[2]!='3':
        raise RuntimeError('Keeper3 PID does not identify the expected cache keeper')
    return identity

def sha_file(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''): h.update(block)
    return h.hexdigest()

def load_items():
    items=json.loads(MANIFEST.read_text())
    if not isinstance(items,list) or len(items)!=5000: raise RuntimeError('Expected5000 compilation facets')
    paths=set();names=set()
    for e in items:
        path=Path(e['path'])
        if not path.is_relative_to(LEAN/'.lake/packages') or path.suffix not in ('.c','.ilean'):
            raise RuntimeError('Manifest contains a path outside compilation-only facets')
        if '..' in path.parts or e['archive_name']!=str(path.relative_to(LEAN)):
            raise RuntimeError('Unsafe or inconsistent compilation archive path')
        if str(path) in paths or e['archive_name'] in names: raise RuntimeError('Duplicate compilation artifact')
        paths.add(str(path));names.add(e['archive_name'])
    return items

def validate_links(items,keeper,hashes=False):
    prefix='/proc/'+str(keeper['pid'])+'/fd/'
    if not same_process(keeper): raise RuntimeError('Keeper identity changed')
    for e in items:
        path=Path(e['path'])
        if not path.is_symlink(): raise RuntimeError('Compilation artifact is not a keeper symlink: '+str(path))
        target=os.readlink(path)
        if not target.startswith(prefix) or not target[len(prefix):].isdigit():
            raise RuntimeError('Compilation artifact belongs to another keeper: '+str(path))
        st=path.stat()
        if not stat.S_ISREG(st.st_mode) or st.st_size!=e['bytes'] or stat.S_IMODE(st.st_mode)!=0o400:
            raise RuntimeError('Compilation artifact metadata changed: '+str(path))
        if hashes and sha_file(path)!=e['sha256']: raise RuntimeError('Compilation artifact hash mismatch: '+str(path))

def validate_backup(items):
    expected={e['archive_name']:e for e in items};seen=set()
    with tarfile.open(BACKUP,'r|gz') as archive:
        for member in archive:
            if not member.isfile() or member.name not in expected or member.name in seen:
                raise RuntimeError('Unexpected member in genuine compilation backup')
            e=expected[member.name];seen.add(member.name)
            if member.size!=e['bytes']: raise RuntimeError('Backup size mismatch')
            h=hashlib.sha256()
            with archive.extractfile(member) as inp:
                for block in iter(lambda:inp.read(1024*1024),b''): h.update(block)
            if h.hexdigest()!=e['sha256']: raise RuntimeError('Backup SHA mismatch')
    if len(seen)!=len(expected): raise RuntimeError('Incomplete compilation backup')

def wait_dead(identity,limit=10):
    deadline=time.monotonic()+limit
    while same_process(identity):
        if time.monotonic()>deadline: return False
        time.sleep(0.05)
    return True

def run(args):
    prefix=TASK/args.output_prefix
    outpath=Path(str(prefix)+'.stdout');errpath=Path(str(prefix)+'.stderr')
    tracepath=Path(str(prefix)+'.trace.jsonl');metricpath=Path(str(prefix)+'.metrics.json')
    started=utc();begin=time.monotonic();trace=tracepath.open('w',buffering=1)
    def event(name,**kwargs):
        record={'at':utc(),'elapsed':time.monotonic()-begin,'event':name,**kwargs}
        trace.write(json.dumps(record)+'\n');trace.flush()
        print(json.dumps(record),flush=True)
    eviction_plan=prepare_eviction_plan()
    event('runtime_eviction_preflight',files=len(eviction_plan['files']),source_bytes=eviction_plan['bytes_with_directory_entries_removed'],preserved_disk_files=eviction_plan['disk_backed_files_preserved'])
    items=load_items();keeper=keeper_identity()
    validate_backup(items);validate_links(items,keeper,hashes=True)
    backup_hash=sha_file(BACKUP)
    event('preflight_ok',count=len(items),bytes=sum(e['bytes'] for e in items),
          keeper=keeper['pid'],backup_sha256=backup_hash,success_stdout_bound=5980)
    nodeproc=None;node=None;child=None;paused=False;cache_absent=False;oldkeeper=keeper
    replacement=None;replacement_identity=None;result=3;failure=None;released=False;restored=False
    runtime_watch=None;runtime_evicted=False;runtime_eviction_result=None
    stop_requested=False
    def request_stop(signum,frame):
        nonlocal stop_requested
        stop_requested=True
        event('stop_requested',signal=signum)
    previous={sig:signal.signal(sig,request_stop) for sig in (signal.SIGTERM,signal.SIGINT)}

    def restore_cache():
        nonlocal cache_absent,replacement,replacement_identity,restored
        if not cache_absent:return
        # Remove only old keeper links left by an interrupted removal. Never replace
        # a path owned by another process or a regular file.
        permitted=[oldkeeper]
        if replacement_identity is not None:permitted.append(replacement_identity)
        prefixes=['/proc/'+str(k['pid'])+'/fd/' for k in permitted]
        remaining=[]
        for e in items:
            path=Path(e['path'])
            if path.is_symlink():
                target=os.readlink(path)
                if not any(target.startswith(prefix) and target[len(prefix):].isdigit() for prefix in prefixes):
                    raise RuntimeError('Recovery found a compilation path owned by another keeper')
                remaining.append(path)
            elif path.exists():raise RuntimeError('Recovery found an unexpected existing compilation file')
        for path in remaining:path.unlink()
        for owned_keeper in permitted:
            if same_process(owned_keeper):
                send(owned_keeper,signal.SIGTERM)
                if not wait_dead(owned_keeper):
                    send(owned_keeper,signal.SIGKILL)
                    if not wait_dead(owned_keeper):raise RuntimeError('Owned keeper3 did not exit')
        event('restore_start')
        kout=open(str(prefix)+'.keeper3.stdout','ab',buffering=0)
        kerr=open(str(prefix)+'.keeper3.stderr','ab',buffering=0)
        replacement=subprocess.Popen([sys.executable,str(KEEPER),'3'],cwd=REPO,stdout=kout,stderr=kerr,start_new_session=True)
        kout.close();kerr.close()
        replacement_identity=process_info(replacement.pid)
        deadline=time.monotonic()+10
        while True:
            if replacement.poll() is not None:raise RuntimeError('Replacement keeper3 exited')
            if (TASK/'ram-cache-3.sock').exists() and (TASK/'ram-cache-3.pid').read_text().strip()==str(replacement.pid):break
            if time.monotonic()>deadline:raise RuntimeError('Replacement keeper3 startup timed out')
            time.sleep(0.05)
        with open(str(prefix)+'.restore.stdout','ab') as sout,open(str(prefix)+'.restore.stderr','ab') as serr:
            proc=subprocess.run([sys.executable,str(RESTORE)],cwd=REPO,stdout=sout,stderr=serr)
        if proc.returncode!=0:
            raise RuntimeError('Exact compilation cache restoration failed; Node remains stopped for recovery')
        validate_links(items,replacement_identity,hashes=True)
        if sha_file(BACKUP)!=backup_hash:raise RuntimeError('Compilation backup changed')
        cache_absent=False;restored=True
        event('restore_complete',keeper=replacement.pid,files=len(items))

    try:
        with outpath.open('w') as out,errpath.open('w') as err:
            env=os.environ.copy()
            env.update({'MIMALLOC_PURGE_DELAY':'0','MIMALLOC_PURGE_DECOMMITS':'1','MIMALLOC_ALLOW_THP':'0'})
            nodeproc=subprocess.Popen(['node','tools/check-lean.mjs','lean/PEqualNP/Outside/L_meta_10760.lean',str(TASK/'statement.txt'),'check'],cwd=REPO,stdout=out,stderr=err,env=env)
            node=process_info(nodeproc.pid)
            event('checker_started',node=nodeproc.pid)
            while nodeproc.poll() is None:
                if stop_requested:raise RuntimeError('Scheduler was asked to stop')
                if STAGE in errpath.read_text():
                    child=verified_child(node)
                    if child:break
                time.sleep(0.05)
            if child:
                event('verifier_found',pid=child['pid'])
                runtime_watch=ProofOpenWatch(PROOF)
                event('proof_import_watch_armed',path=str(PROOF),verifier=child['pid'])
                if not send(node,signal.SIGSTOP):raise RuntimeError('Node exited before pause')
                paused=True
                deadline=time.monotonic()+5
                while (current:=process_info(node['pid'])) and current['state'] not in ('T','t'):
                    if time.monotonic()>deadline:raise RuntimeError('Node failed to stop')
                    time.sleep(0.01)
                if not same_process(node):raise RuntimeError('Node died while pausing')
                # The entire set is checked before the first removal.
                validate_links(items,oldkeeper,hashes=False)
                cache_absent=True
                for e in items:Path(e['path']).unlink()
                if not send(oldkeeper,signal.SIGTERM):raise RuntimeError('Keeper3 changed before release')
                if not wait_dead(oldkeeper):raise RuntimeError('Keeper3 did not release compilation storage')
                released=True
                event('compilation_storage_released',node=node['pid'],verifier=child['pid'])
                verifier_start=time.monotonic();blocked_since=None;last_heartbeat=0.0
                while same_process(child):
                    if not runtime_evicted and runtime_watch.poll(0):
                        event('proof_import_open_observed',verifier=child['pid'])
                        runtime_eviction_result=evict_after_proof_open(runtime_watch,eviction_plan,node,child,Path(str(prefix)+'.runtime-eviction.json'))
                        runtime_evicted=True
                        runtime_watch.close()
                        event('runtime_cache_evicted',**runtime_eviction_result)
                    if time.monotonic()-last_heartbeat>=30:
                        try:
                            status=(Path('/proc')/str(child['pid'])/'status').read_text().splitlines()
                            memory={line.split(':',1)[0]:line.split(':',1)[1].strip() for line in status if line.startswith(('VmRSS:','VmHWM:'))}
                            event('verifier_progress',pid=child['pid'],memory=memory)
                        except (FileNotFoundError,ProcessLookupError):pass
                        last_heartbeat=time.monotonic()
                    if stop_requested:
                        event('verifier_cancelled_for_requested_stop')
                        send(child,signal.SIGTERM)
                        if not wait_dead(child):send(child,signal.SIGKILL);wait_dead(child)
                        break
                    if time.monotonic()-verifier_start>args.verifier_timeout:
                        event('verifier_timeout_restore_before_resume')
                        break
                    try:
                        tasks=Path('/proc')/str(child['pid'])/'task'
                        wchans=[]
                        for task in tasks.iterdir():
                            try:wchans.append((task/'wchan').read_text().strip())
                            except (FileNotFoundError,ProcessLookupError):pass
                    except (FileNotFoundError,ProcessLookupError):break
                    blocked=[w for w in wchans if w in ('pipe_write','sock_alloc_send_pskb','unix_stream_sendmsg')]
                    if blocked:
                        blocked_since=blocked_since or time.monotonic()
                        if time.monotonic()-blocked_since>2:
                            event('possible_output_backpressure_restore_before_resume',wchans=blocked)
                            break
                    else:blocked_since=None
                    time.sleep(0.1)
                event('verifier_wait_finished',alive=same_process(child),state=process_info(child['pid']))
                restore_cache()
                if same_process(node):send(node,signal.SIGCONT);paused=False;event('checker_resumed')
            while nodeproc.poll() is None:
                if stop_requested:
                    send(node,signal.SIGTERM)
                    break
                time.sleep(0.2)
            result=nodeproc.wait()
            event('checker_finished',exit=result)
    except BaseException as exc:
        failure=repr(exc);event('scheduler_error',error=failure,traceback=traceback.format_exc())
    finally:
        if runtime_watch is not None:runtime_watch.close()
        # Any cache restoration must precede resuming the stopped official checker.
        if cache_absent:
            try:
                if child and same_process(child):
                    send(child,signal.SIGTERM)
                    if not wait_dead(child):send(child,signal.SIGKILL);wait_dead(child)
                restore_cache()
            except BaseException as exc:
                failure=(failure or '')+'; recovery: '+repr(exc)
                event('recovery_failed_node_left_stopped',error=repr(exc),node=None if node is None else node['pid'])
        if paused and not cache_absent and node and same_process(node):
            send(node,signal.SIGCONT);paused=False;event('checker_resumed_in_finally')
        if failure and node and same_process(node) and not paused:
            send(node,signal.SIGTERM)
            if not wait_dead(node):send(node,signal.SIGKILL)
        if nodeproc and not paused:
            try:nodeproc.wait(timeout=10)
            except subprocess.TimeoutExpired:pass
        for sig,handler in previous.items():signal.signal(sig,handler)
        usage=resource.getrusage(resource.RUSAGE_CHILDREN)
        metrics={'started_at':started,'finished_at':utc(),'exit':result if failure is None else 3,
                 'wall_seconds':time.monotonic()-begin,'user_seconds':usage.ru_utime,
                 'system_seconds':usage.ru_stime,'max_rss_kib':usage.ru_maxrss,
                 'node_pid':None if node is None else node['pid'],
                 'verifier_pid':None if child is None else child['pid'],
                 'compilation_cache_released':released,'compilation_cache_restored':restored,
                 'cache_absent':cache_absent,'node_left_stopped':paused,'error':failure,
                 'runtime_cache_evicted':runtime_evicted,'runtime_eviction_result':runtime_eviction_result,
                 'runtime_cache_recovery_required':runtime_evicted,
                 'allocator_environment':{'MIMALLOC_PURGE_DELAY':'0','MIMALLOC_PURGE_DECOMMITS':'1','MIMALLOC_ALLOW_THP':'0'}}
        metricpath.write_text(json.dumps(metrics,indent=2)+'\n');event('metrics',**metrics);trace.close()
    return 3 if failure is not None else result

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-prefix',default='final-checker-eviction')
    ap.add_argument('--verifier-timeout',type=float,default=1800,
                    help='Restore cache and resume output draining after this many verifier seconds.')
    args=ap.parse_args()
    if '/' in args.output_prefix or args.output_prefix in ('','.','..'):ap.error('output-prefix must be a filename stem')
    return run(args)

if __name__=='__main__':sys.exit(main())
