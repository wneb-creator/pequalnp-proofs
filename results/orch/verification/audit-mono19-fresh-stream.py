from pathlib import Path
from collections import Counter
from array import array
import gzip, hashlib, json, re, resource, sys, time, os

# Independently written archival/structural auditor, not a mathematical verifier.
base = Path(sys.argv[1]); output = Path(sys.argv[2])
resource.setrlimit(resource.RLIMIT_AS, (1_000_000_000, 1_000_000_000))
os.sched_setaffinity(0, {2})
started = time.monotonic()
def digest(path):
    h = hashlib.sha256(); size = 0
    with path.open('rb') as f:
        while data := f.read(1048576): h.update(data); size += len(data)
    return size, h.hexdigest()
manifest_bytes = (base/'manifest.json').read_bytes()
assert hashlib.sha256(manifest_bytes).hexdigest() == '5fa082f87c631af36b8183bfb53693cba37db425e7954e24cc687de58f03e72e'
manifest = json.loads(manifest_bytes)
for name, meta in manifest.items():
    if 'bytes' in meta: expected = meta['bytes'], meta['sha256']; path = base/name
    else: expected = meta['gzip_bytes'], meta['gzip_sha256']; path = base/(name+'.gz')
    assert digest(path) == expected, name
print('All manifest file hashes and sizes match.', flush=True)
status = json.loads((base/'mono19-oredge-fresh-proof.status.json').read_text())
assert status['exit_code'] == 0 and '--memo-in' not in status['command']
assert '--mono-nine15' not in status['command']
log = (base/'mono19-oredge-fresh-proof.log').read_text()
assert 'finished found=0' in log and 'limit reached' not in log
source = (base/'copy_search_first_prooftrace.cpp').read_text()
profiles = [tuple(map(int, x)) for x in re.findall(r'\{(\d+),(\d+),(\d+),(\d+)\}', source.split('static const CP profiles[CP_COUNT] = ', 1)[1].split(';', 1)[0])]
assert len(profiles) == 1145
N = 2065513
states = array('I'); offsets = array('I', [0])*(N+1)
lengths = bytearray(N+1); remaining = bytearray(N+1); done = bytearray(N+1)
canons = array('I'); coffsets = array('I', [0])*(N+1); clengths = bytearray(N+1)
rectangle_seen = bytearray(N+1); signal_flags = bytearray(1184319)
kinds = {}; kindcounts = Counter(); events = Counter(); stack = []
lastnode = 0; lastsignal = -1; root = None; memo_refs = 0
def ref(ids):
    for x in ids:
        assert 0 <= x < len(signal_flags), x
        signal_flags[x] |= 1
def snapshot(n): return states[offsets[n]:offsets[n]+lengths[n]]
def canonical(n): return canons[coffsets[n]:coffsets[n]+clengths[n]]
def cofactor(e, rem, histlen):
    p=e['profile']; assert 0 <= p < len(profiles) and e['lower'] == profiles[p][2]
    hs=e['selected_history']; assert hs == sorted(set(hs))
    assert all(0 <= i < histlen for i in hs)
    assert e['mass'] >= 0 and e['lower']+e['mass'] > rem+len(hs)
def history(es, i):
    e=es[i]
    if e['left'] < 0: return []
    a,b=e['left'],e['right']
    return history(es,a)+history(es,b)+[[e['op'],es[a]['signal'],es[b]['signal'],e['signal']]]
edge_list=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
edges={tuple(sorted(x)) for x in edge_list}
inputs=[sum(1<<r for r in range(1024) if r>>i&1) for i in range(10)]
target=0
for a,b in edge_list: target |= inputs[a]&inputs[b]
full=(1<<1024)-1
def consume(e):
    global lastnode, lastsignal, root, memo_refs
    typ=e['event']; events[typ]+=1
    if typ=='header':
        assert events[typ]==1 and lastnode==0
        assert (e['mode'],e['cap'],e['first'],e['weak15'],e['target'])==(0,19,'oredge',0,11)
        autos=e['automorphisms']; assert len(autos)==120 and len({tuple(p) for p in autos})==120
        for p in autos:
            assert sorted(p)==list(range(10))
            assert {tuple(sorted((p[a],p[b]))) for a,b in edges}==edges
        ref([11]); return
    if typ=='signal':
        assert not stack and lastnode==N and done[1]
        n=e['id']; assert n>lastsignal; lastsignal=n
        assert 0 <= n < len(signal_flags) and not signal_flags[n]&2
        h=e['hex']; assert re.fullmatch(r'0x[0-9a-f]{256}',h)
        v=int(h,16); assert 0<v<full and v&1==0
        if 1<=n<=10: assert v==inputs[n-1]
        if n==11: assert v==target
        signal_flags[n]|=2; return
    assert lastsignal==-1
    if typ=='node':
        n=e['id']; assert n==lastnode+1 and n<=N; lastnode=n
        s=e['state']; rem=e['remaining']; hist=e['history']
        assert s==sorted(s) and 0<=rem<=19 and 0<len(s)<=20 and len(hist)+rem==19
        assert e['parent']==(stack[-1]['id'] if stack else 0)
        pool=set(range(1,11))
        for d,a,b,z in hist:
            assert d in (0,1) and a in pool and b in pool
            pool.add(z); ref([a,b,z])
        assert all(x in pool for x in s)
        if stack:
            parent=stack[-1]; pending=parent['pending']; assert pending is not None
            assert (n,s,rem,hist)==pending; parent['pending']=None
        else:
            assert n==1 and s==list(range(1,11))+[12] and rem==18 and hist==[[1,1,2,12]]
        offsets[n]=len(states); lengths[n]=len(s); remaining[n]=rem; states.extend(s); ref(s)
        stack.append(dict(id=n,state=s,rem=rem,hist=hist,entries=[],children=0,finished=0,pending=None,closed=False,basis=False))
        return
    f=stack[-1]; n=f['id']; es=f['entries']
    assert e.get('node',e.get('id'))==n
    if typ=='canonical':
        assert clengths[n]==0 and 0<=e['automorphism']<120
        assert len(e['state'])==len(f['state']) and e['state']==sorted(e['state'])
        coffsets[n]=len(canons); clengths[n]=len(e['state']); canons.extend(e['state']); ref(e['state'])
    elif typ=='basis':
        roots=sorted(set(f['state'])); total=[f['state'].count(x) for x in roots]
        assert not f['basis'] and e['roots']==roots and e['total']==total
        weights=[]; w=1
        for c in total: weights.append(w); w*=c+1
        f.update(basis=True,roots=roots,total=total,weights=weights)
    elif typ=='entry':
        assert f['basis'] and not f['closed']; i=e['index']; cs=e['counts']
        assert i==len(es) and len(cs)==len(f['roots']) and e['mass']==sum(cs)
        assert all(0<=x<=y for x,y in zip(cs,f['total']))
        assert e['code']==sum(x*y for x,y in zip(cs,f['weights']))
        a,b=e['left'],e['right']
        if a<0:
            assert a==b==-1 and i<len(f['roots']) and e['signal']==f['roots'][i]
            assert cs==[int(j==i) for j in range(len(cs))]
        else:
            assert 0<=a<=b<i and e['op'] in (0,1)
            assert cs==[x+y for x,y in zip(es[a]['counts'],es[b]['counts'])]
        ref([e['signal']]); es.append(e)
    elif typ=='subtree_cut':
        assert not f['closed']; a,b=e['left'],e['right']; assert 0<=a<=b<len(es) and e['op'] in (0,1)
        cs=[x+y for x,y in zip(es[a]['counts'],es[b]['counts'])]
        assert all(x<=y for x,y in zip(cs,f['total']))
        assert e['code']==sum(x*y for x,y in zip(cs,f['weights']))
        rem=f['rem']-sum(cs)+1; assert e['remaining']==rem
        cofactor(e,rem,len(f['hist'])+es[a]['mass']+es[b]['mass']-1)
        ref([e['signal']])
    elif typ=='closure_complete':
        assert not f['closed'] and e['entries']==len(es); f['closed']=True
    elif typ=='copy_child':
        assert f['closed'] and f['pending'] is None and f['children']==f['finished']
        i=e['entry']; assert i==f['children'] and i<len(es) and e['child']==lastnode+1
        z=es[i]; childstate=sorted([r for r,t,c in zip(f['roots'],f['total'],z['counts']) for _ in range(t-c)]+[z['signal']]*2)
        f['pending']=(e['child'],childstate,f['rem']-z['mass']+1,f['hist']+history(es,i)); f['children']+=1
    elif typ=='done':
        kind=e['kind']; assert kind not in ('open','found') and not done[n]
        assert f['pending'] is None and f['children']==f['finished']
        if kind=='memo':
            r=e['ref']; assert 0<r<n and done[r] and kinds[done[r]] in ('expand','tight_closure','rectangle_midclosure')
            assert remaining[r]==f['rem'] and clengths[n] and canonical(n)==canonical(r); memo_refs+=1
        else: assert e['ref']==-1
        if kind=='cofactor': cofactor(e,f['rem'],len(f['hist']))
        if kind=='prefix_formula': assert f['rem']+1==len(f['state']) and set(f['state'])<=set(range(1,11))|{12}
        if kind=='expand': assert f['closed'] and f['children']==len(es)
        if kind in ('tight_closure','rectangle','rectangle_midclosure','prefix_formula'): assert f['rem']+1==len(f['state'])
        if kind=='tight_closure': assert f['closed']
        if kind not in kinds.values(): kinds[len(kinds)+1]=kind
        done[n]=next(k for k,v in kinds.items() if v==kind); kindcounts[kind]+=1
        stack.pop()
        if stack: stack[-1]['finished']+=1
        else: root=dict(kind=kind,children=f['children'],entries=len(es),remaining=f['rem'],state=f['state'])
    else: raise AssertionError(('Unknown proof event',typ))

chunks=json.loads((base/'proof-chunks.json').read_text()); whole=hashlib.sha256(); totalbytes=0; carry=b''
for part in chunks['parts']:
    h=hashlib.sha256(); size=0
    with gzip.open(base/part['file'],'rb') as f:
        while block:=f.read(1048576):
            h.update(block); whole.update(block); size+=len(block); totalbytes+=len(block)
            lines=(carry+block).split(b'\n'); carry=lines.pop()
            for line in lines: consume(json.loads(line))
    assert (size,h.hexdigest())==(part['original_bytes'],part['original_sha256'])
    print(json.dumps(dict(part=part['file'],nodes=lastnode,events=sum(events.values()),seconds=round(time.monotonic()-started,2),rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)),flush=True)
assert not carry and not stack and lastnode==N and all(done[1:])
assert (totalbytes,whole.hexdigest())==(chunks['original_bytes'],chunks['original_sha256'])
assert all(x!=1 for x in signal_flags), 'Unresolved proof signal reference'
assert root['kind']=='expand' and root['children']==root['entries']==11
assert kindcounts['expand']+kindcounts['tight_closure']+kindcounts['rectangle_midclosure']==91097
print('Complete proof stream structural census passed.',flush=True)

def raw_lines(name):
    meta=manifest[name]; h=hashlib.sha256(); size=0
    with gzip.open(base/(name+'.gz'),'rb') as f:
        for line in f:
            h.update(line); size+=len(line); assert line.endswith(b'\n'); yield line
    assert (size,h.hexdigest())==(meta['original_bytes'],meta['original_sha256'])
rectevents=Counter(); rectsignals=bytearray(len(signal_flags)); matrix_records=[]
for line in raw_lines('mono19-oredge-fresh-proof-rectangles.jsonl'):
    e=json.loads(line); typ=e['event']; rectevents[typ]+=1
    if typ=='rectangle':
        n=e['node']; assert 0<n<=N and kinds[done[n]] in ('rectangle','rectangle_midclosure') and not rectangle_seen[n]
        assert e['remaining']==remaining[n] and array('I',e['state'])==snapshot(n)
        assert len(e['state'])==len(e['root_costs'])==e['remaining']+1
        assert min(e['root_costs'])>=0 and sum(e['root_costs'])==e['cost_sum']<e['total']
        assert 0<=e['matrix']<39; rectangle_seen[n]=1
        for v in e['state']: rectsignals[v]|=1
    elif typ=='matrix_loaded': matrix_records.append(e)
    elif typ=='signal':
        n=e['id']; assert 0<=n<len(rectsignals) and not rectsignals[n]&2
        assert re.fullmatch(r'0x[0-9a-f]{256}',e['hex']); rectsignals[n]|=2
    elif typ=='header': assert e['signed']==0 and e['cap']==19 and e['first']=='oredge' and int(e['target'],16)==target
    else: raise AssertionError(('Unknown rectangle event',typ))
assert rectevents['rectangle']==kindcounts['rectangle']+kindcounts['rectangle_midclosure']
assert all(x!=1 for x in rectsignals)
tokens=iter((base/'rectangles-v3.txt').read_text().split()); assert next(tokens)=='PNP_RECT_V1'
assert int(next(tokens))==len(matrix_records)==26
for i,e in enumerate(matrix_records):
    ident=int(next(tokens)); rows=int(next(tokens)); cols=int(next(tokens)); total=int(next(tokens))
    pos=[int(next(tokens)) for _ in range(rows)]; neg=[int(next(tokens)) for _ in range(cols)]
    weights=[[int(next(tokens)) for _ in range(cols)] for _ in range(rows)]
    assert (e['matrix'],e['id'],e['total'],e['positive_rows'],e['negative_rows'],e['weights'])==(13+i,ident,total,pos,neg,weights)
    assert all((target>>r)&1 for r in pos) and all(not((target>>r)&1) for r in neg)
    assert sum(map(sum,weights))==total
assert next(tokens,None) is None
print('Rectangle stream hashes, node links, margins and V3 payload passed.',flush=True)

memo_seen=set(); memo_count=0; root_orbits={tuple(sorted(inputs+[inputs[a]|inputs[b]])) for a,b in edges}; root_hits=0
for i,line in enumerate(raw_lines('mono19-oredge-fresh-proof-completed.memo')):
    if i==0: assert line==b'PNP_COPY_MEMO_V1 0 19 oredge 0\n'; continue
    fields=line.split(); assert fields[0]==b'S'; rem=int(fields[1]); size=int(fields[2]); assert len(fields)==size+3 and 0<size<=20 and 0<=rem<=19
    values=[int(x,16) for x in fields[3:]]; assert all(0<v<full and v&1==0 for v in values)
    hashed=hashlib.sha256(line).digest(); assert hashed not in memo_seen; memo_seen.add(hashed); memo_count+=1
    if rem==18 and tuple(sorted(values)) in root_orbits:root_hits+=1
assert memo_count==91097 and root_hits==1
bank_count=0
with (base/'mono19-oredge-fresh-proof-banks.jsonl').open() as f:
    for line in f:
        e=json.loads(line); bank_count+=1
        pool=set(inputs)
        for d,a,b in e['history']:
            a,b=(int(x,16) if isinstance(x,str) else x for x in (a,b))
            assert d in (0,1) and a in pool and b in pool
            pool.add(a&b if d==0 else a|b)
        ss=[int(x,16) if isinstance(x,str) else x for x in e['state']]
        assert all(x in pool for x in ss) and e['remaining']+1==len(ss)
report=dict(verdict='PASS',manifest_sha256=hashlib.sha256(manifest_bytes).hexdigest(),manifest_entries=len(manifest),proof_bytes=totalbytes,proof_sha256=whole.hexdigest(),proof_events=dict(events),node_status=dict(kindcounts),root=root,memo_dependencies=memo_refs,memo_records=memo_count,root_orbit_memo_records=root_hits,rectangle_events=dict(rectevents),bank_histories_replayed=bank_count,seconds=time.monotonic()-started,max_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,scope='Full archival hashes/CRC and structural completion audit. Every memo reference targets an earlier completed same-budget canonical state; every expanded node closes every retained-entry child. Histories/count/provenance shapes and strict cofactor inequalities checked. This does not recompute all 1024-row operations, canonical truth actions, cofactor supplies, weighted rectangle maxima, or exhaustive closure coverage, and is not a Lean proof of the complete case or posted gap.')
output.write_text(json.dumps(report,indent=2)+'\n'); print(json.dumps(report,indent=2),flush=True)
