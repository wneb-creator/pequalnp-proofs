from pathlib import Path
from collections import Counter
import gzip
import hashlib
import json
import re
import sys

root=Path(sys.argv[1])
manifest=json.loads((root/'manifest.json').read_text())
assert hashlib.sha256((root/'manifest.json').read_bytes()).hexdigest()=='51c3386b2fe63e1ccfc32721b04729c2cdf309d5e5ac98f3584c8dedf1678faf'
def stream_digest(stream):
    count=0;digest=hashlib.sha256()
    while True:
        block=stream.read(1024*1024)
        if not block:break
        count+=len(block);digest.update(block)
    return count,digest.hexdigest()
for name,item in manifest.items():
    if 'gzip_bytes'in item:
        path=root/(name+'.gz')
        with path.open('rb')as f:assert stream_digest(f)==(item['gzip_bytes'],item['gzip_sha256'])
        with gzip.open(path,'rb')as f:assert stream_digest(f)==(item['original_bytes'],item['original_sha256'])
    else:
        with(root/name).open('rb')as f:assert stream_digest(f)==(item['bytes'],item['sha256'])

full=(1<<1024)-1
inputs=[sum(((r>>j)&1)<<r for r in range(1024))for j in range(10)]
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
target=0
for a,b in edges:target|=inputs[a]&inputs[b]
root_orbits={tuple(sorted(inputs+[inputs[a]|inputs[b]]))for a,b in edges}
memo_results={}
for name,expected in [('input-weak15.memo',61991),('completed-weak15.memo',76286)]:
    seen=set();counts=Counter();roots_found=0
    with gzip.open(root/(name+'.gz'),'rt')as stream:
        assert stream.readline().strip()=='PNP_COPY_MEMO_V1 0 19 oredge 1'
        for line in stream:
            fields=line.split();assert fields[0]=='S'
            k,n=map(int,fields[1:3]);assert 0<=k<=19 and 1<=n<=k+1 and len(fields)==n+3
            assert all(re.fullmatch('0x[0-9a-f]{256}',v)for v in fields[3:])
            words=[int(v,16)for v in fields[3:]]
            assert all(0<v<full and not(v&1)for v in words)
            key=hashlib.sha256(' '.join(fields).encode()).digest();assert key not in seen;seen.add(key)
            counts[k]+=1
            roots_found+=k==18 and tuple(sorted(words))in root_orbits
    assert len(seen)==expected and roots_found==0
    memo_results[name]=dict(states=len(seen),remaining=dict(counts),root_orbits_found=roots_found)

event_counts=Counter();ids=set();signals={};trailer=None;matrices={};hits=Counter()
with gzip.open(root/'rectangles.jsonl.gz','rb')as stream:
    for line in stream:
        try:event=json.loads(line)
        except json.JSONDecodeError:
            assert stream.read()==b''
            trailer=dict(bytes=len(line),sha256=hashlib.sha256(line).hexdigest(),literal=line.decode())
            break
        kind=event['event'];event_counts[kind]+=1
        if kind=='header':
            assert not event['signed']and event['cap']==19 and event['first']=='oredge'
            assert int(event['target'],16)==target
        elif kind=='matrix_loaded':
            assert event['matrix']not in matrices
            w=event['weights'];P=event['positive_rows'];N=event['negative_rows']
            assert len(w)==len(P)and all(len(row)==len(N)for row in w)
            assert sum(map(sum,w))==event['total']
            assert all((target>>r)&1 for r in P)and all(not((target>>r)&1)for r in N)
            matrices[event['matrix']]=event['total']
        elif kind=='rectangle':
            state=event['state'];costs=event['root_costs']
            assert len(state)==len(costs)==event['remaining']+1
            assert all(c>=0 for c in costs)
            assert sum(costs)==event['cost_sum']<event['total']
            if event['matrix']>=13:assert event['total']==matrices[event['matrix']]
            ids.update(state);hits[event['matrix']]+=1
        elif kind=='signal':signals[event['id']]=int(event['hex'],16)
        else:raise AssertionError(kind)
assert event_counts==Counter(header=1,matrix_loaded=49,rectangle=403936)
assert not signals and len(ids)==47199
assert trailer['bytes']==28 and trailer['sha256']=='9833c8e223bbc5d9089853d7c0b5e7346fdd392fdd4f03b125181f7791b3deaa'
bank_count=0
with gzip.open(root/'banks.jsonl.gz','rt')as stream:
    for line in stream:
        event=json.loads(line);available=set(inputs)
        for d,a,b in event['history']:
            a=int(a,16);b=int(b,16);assert d in(0,1)and a in available and b in available
            available.add((a&b)if d==0 else(a|b))
        assert all(int(x,16)in available for x in event['state'])
        assert len(event['state'])==event['remaining']+1
        bank_count+=1
assert bank_count==109
meta=json.loads((root/'run-metadata.json').read_text())
assert meta['exit_code']==-6 and meta['address_space_limit_bytes']==1000000000
assert meta['mono_nine_bound']==15 and '--mono-nine15'in meta['command']
assert 'std::bad_alloc'in(root/'stderr.txt').read_text()
assert 'finished found='not in(root/'stdout.txt').read_text()
result=dict(verdict='PASS_PARTIAL_ARCHIVE_ONLY',manifest_entries=len(manifest),memos=memo_results,
            rectangle_events=dict(event_counts),unresolved_signal_ids=len(ids),trailing_record=trailer,
            replayed_bank_histories=bank_count,child_exit_code=meta['exit_code'],wall_seconds=meta['wall_seconds'],
            full_case_complete=False,scope='Integrity, checkpoint shape, available-record arithmetic and bank-history replay only. No search completeness or kernel proof.')
print(json.dumps(result,indent=2))
