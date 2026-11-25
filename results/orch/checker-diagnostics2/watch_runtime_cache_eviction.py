#!/usr/bin/env python3
"""Observe proof import and evict only temporary runtime-cache directory entries.

No contents are modified or truncated. Live mappings retain the exact original
inodes. Only explicitly reviewed callers may invoke the eviction function;
the command-line interface supports an isolated inotify self-test only.
"""
import argparse, ctypes, errno, json, os, select, signal, stat, struct, time
from pathlib import Path

TASK=Path('/tmp/oec/pequalnp-pilot-182')
REPO=Path('/workspace/pequalnp-proofs')
PACKAGES=REPO/'lean/.lake/packages'
PROOF=REPO/'lean/.lake/build/lib/lean/PEqualNP/Outside/L_meta_10760.olean'
VERIFIER=REPO/'lean/.lake/build/bin/checklemma'
KEEPER_SCRIPT=TASK/'ram_cache_keeper.py'
IN_OPEN=0x20
IN_DELETE_SELF=0x400
IN_MOVE_SELF=0x800
IN_IGNORED=0x8000
IN_Q_OVERFLOW=0x4000

class ProofOpenWatch:
    def __init__(self,path):
        self.path=Path(path)
        st=self.path.stat()
        if not stat.S_ISREG(st.st_mode):raise RuntimeError('Watch target must be a regular file')
        self.inode=(st.st_dev,st.st_ino)
        self.seen_open=False
        libc=ctypes.CDLL(None,use_errno=True)
        libc.inotify_init1.argtypes=[ctypes.c_int]
        libc.inotify_init1.restype=ctypes.c_int
        libc.inotify_add_watch.argtypes=[ctypes.c_int,ctypes.c_char_p,ctypes.c_uint32]
        libc.inotify_add_watch.restype=ctypes.c_int
        self.fd=libc.inotify_init1(os.O_CLOEXEC|os.O_NONBLOCK)
        if self.fd<0:raise OSError(ctypes.get_errno(),'inotify_init1')
        self.wd=libc.inotify_add_watch(self.fd,os.fsencode(self.path),IN_OPEN|IN_DELETE_SELF|IN_MOVE_SELF)
        if self.wd<0:
            number=ctypes.get_errno();os.close(self.fd);self.fd=-1
            raise OSError(number,'inotify_add_watch')
        self.armed_at=time.monotonic()

    def poll(self,timeout=0.0):
        if self.fd<0:raise RuntimeError('Watch is closed')
        if not select.select([self.fd],[],[],timeout)[0]:return self.seen_open
        while True:
            try:data=os.read(self.fd,65536)
            except BlockingIOError:break
            if not data:break
            pos=0
            while pos<len(data):
                if len(data)-pos<16:raise RuntimeError('Truncated inotify event')
                wd,mask,cookie,length=struct.unpack_from('iIII',data,pos)
                pos+=16+length
                if pos>len(data):raise RuntimeError('Truncated inotify filename')
                if mask&IN_Q_OVERFLOW:raise RuntimeError('Inotify queue overflow')
                if wd!=self.wd:raise RuntimeError('Unexpected inotify watch descriptor')
                if mask&(IN_DELETE_SELF|IN_MOVE_SELF|IN_IGNORED):raise RuntimeError('Watched proof inode changed')
                if mask&IN_OPEN:self.seen_open=True
        if self.seen_open:
            st=self.path.stat()
            if (st.st_dev,st.st_ino)!=self.inode:raise RuntimeError('Proof path no longer identifies watched inode')
        return self.seen_open

    def close(self):
        if self.fd>=0:os.close(self.fd);self.fd=-1


def process_identity(pid):
    try:
        raw=(Path('/proc')/str(pid)/'stat').read_text()
        fields=raw[raw.rfind(')')+2:].split()
        return {'pid':pid,'start':int(fields[19]),'state':fields[0]}
    except (FileNotFoundError,ProcessLookupError):return None


def live(identity):
    actual=process_identity(identity['pid'])
    return bool(actual and actual['start']==identity['start'] and actual['state'] not in ('Z','X'))


def runtime_keeper(slot):
    if slot not in (0,1,2):raise RuntimeError('Only runtime keepers0/1/2 are permitted')
    pid=int((TASK/f'ram-cache-{slot}.pid').read_text())
    identity=process_identity(pid)
    if not identity or not live(identity):raise RuntimeError('Expected runtime keeper is not alive')
    args=[os.fsdecode(x) for x in (Path('/proc')/str(pid)/'cmdline').read_bytes().split(b'\0') if x]
    if len(args)!=3 or args[1]!=str(KEEPER_SCRIPT) or args[2]!=str(slot):
        raise RuntimeError('Runtime keeper identity does not match its dedicated slot')
    return {**identity,'slot':slot}


def prepare_eviction_plan():
    """Read-only metadata validation. Run before the checker to avoid peak overhead."""
    keepers=[runtime_keeper(i) for i in (0,1,2)]
    prefixes={f"/proc/{k['pid']}/fd/":k for k in keepers}
    selected=[];seen=set();modules=set();disk_count=0
    with (TASK/'runtime-cache-installed.jsonl').open() as source:
        for line in source:
            row=json.loads(line);module=row['module']
            if module in modules:raise RuntimeError('Duplicate module in genuine-cache manifest')
            modules.add(module)
            for e in row['files']:
                path=Path(e['path'])
                if not path.is_relative_to(PACKAGES) or '..' in path.parts:
                    raise RuntimeError('Cache path is outside pinned dependency artifact scope')
                if not path.name.endswith(('.olean','.olean.server','.olean.private','.ir','.ir.sig')):
                    raise RuntimeError('Cache manifest contains a non-runtime facet')
                if str(path) in seen:raise RuntimeError('Duplicate cache destination')
                seen.add(str(path))
                st=path.stat()
                if not stat.S_ISREG(st.st_mode) or st.st_size!=e['bytes']:
                    raise RuntimeError('Runtime artifact metadata differs from genuine manifest')
                if path.is_symlink():
                    target=os.readlink(path)
                    matches=[(prefix,k) for prefix,k in prefixes.items() if target.startswith(prefix) and target[len(prefix):].isdigit()]
                    if len(matches)!=1:raise RuntimeError('Runtime symlink is not owned by keepers0/1/2')
                    selected.append({'path':str(path),'target':target,'bytes':e['bytes'],'sha256':e['sha256'],
                                     'module':module,'archive':row['archive'],'archive_sha256':row['archive_sha256'],
                                     'keeper_slot':matches[0][1]['slot']})
                else:disk_count+=1
    if len(modules)!=6635 or len(seen)!=33175:
        raise RuntimeError('Unexpected new-runtime cache manifest census')
    return {'keepers':keepers,'files':selected,'disk_backed_files_preserved':disk_count,
            'bytes_with_directory_entries_removed':sum(e['bytes'] for e in selected),
            'prepared_at':time.time(),'proof_path':str(PROOF)}


def evict_after_proof_open(watch,plan,node_identity,verifier_identity,record_path):
    """Unlink validated new-runtime symlinks, then stop only their keeper daemons.

    Caller must have observed the genuine verifier and stopped only its Node
    parent. Inotify has no reader PID: caller must exclude unrelated proof reads.
    Returns after daemon termination requests, without altering mapped file data.
    """
    if Path(watch.path)!=PROOF or not watch.poll(0):raise RuntimeError('Exact proof import has not been observed')
    node=process_identity(node_identity['pid'])
    if not node or node['start']!=node_identity['start'] or node['state'] not in ('T','t'):
        raise RuntimeError('Official checker Node parent is not paused')
    if not live(verifier_identity):raise RuntimeError('Official verifier is not alive')
    expected=VERIFIER.stat();actual=(Path('/proc')/str(verifier_identity['pid'])/'exe').stat()
    if (actual.st_dev,actual.st_ino)!=(expected.st_dev,expected.st_ino):raise RuntimeError('Verifier executable changed')
    for keeper in plan['keepers']:
        verified=runtime_keeper(keeper['slot'])
        if verified['pid']!=keeper['pid'] or verified['start']!=keeper['start']:
            raise RuntimeError('Runtime keeper changed since preflight')
    # Validate the entire unlink set before removing its first path.
    for e in plan['files']:
        path=Path(e['path'])
        if not path.is_symlink() or os.readlink(path)!=e['target'] or path.stat().st_size!=e['bytes']:
            raise RuntimeError('Eviction path changed since preflight')
    record=Path(record_path)
    if not record.is_relative_to(TASK) or record.exists():raise RuntimeError('Eviction log must be a new task-scratch file')
    record.write_text(json.dumps({**plan,'node':node_identity,'verifier':verifier_identity,
                                 'operation':'unlink directory entries then close keeper FDs; never truncate',
                                 'started_at':time.time()},separators=(',',':'))+'\n')
    removed=[]
    try:
        for e in plan['files']:
            Path(e['path']).unlink();removed.append(e)
    except BaseException:
        # All keepers remain alive until the entire unlink pass succeeds.
        # Re-create only the exact missing links already removed by this call.
        for e in removed:
            path=Path(e['path'])
            if path.exists() or path.is_symlink():raise RuntimeError('Cannot roll back externally changed cache path')
            os.symlink(e['target'],path)
        raise
    for keeper in plan['keepers']:
        if not live(keeper):raise RuntimeError('Runtime keeper unexpectedly exited during eviction')
    for keeper in plan['keepers']:
        if not live(keeper):raise RuntimeError('Runtime keeper identity changed before close')
        os.kill(keeper['pid'],signal.SIGTERM)
    return {'evicted_files':len(plan['files']),'preserved_disk_files':plan['disk_backed_files_preserved'],
            'source_bytes':plan['bytes_with_directory_entries_removed'],'record':str(record),
            'actual_memory_saved':'Not assumed; live mmaps retain their original inodes.'}


def self_test():
    target=TASK/'inotify-isolated-probe.txt'
    if target.exists():raise RuntimeError('Isolated test file already exists')
    target.write_bytes(b'isolated inotify regular-file capability test\n')
    watch=ProofOpenWatch(target)
    try:
        assert not watch.poll(0)
        with target.open('rb') as source:assert source.read()==b'isolated inotify regular-file capability test\n'
        assert watch.poll(1)
        print(json.dumps({'inotify_regular_file_IN_OPEN':'PASS','eviction_performed':False,'actual_cache_changes':False}))
    finally:watch.close();target.unlink()

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--self-test',action='store_true',required=True)
    parser.parse_args();self_test()
