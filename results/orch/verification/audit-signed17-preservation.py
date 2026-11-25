from pathlib import Path
import collections
import difflib
import gzip
import hashlib
import json
import time
import zlib

ROOT = Path(__file__).resolve().parents[1]
def sha(b):
    return hashlib.sha256(b).hexdigest()

def archive(path, expected):
    mb = (path / 'manifest.json').read_bytes()
    assert sha(mb) == expected
    data = json.loads(mb)
    records = data if isinstance(data, list) else [dict(path=k, **v) for k,v in data.items()]
    files = {'manifest.json'}
    payload = {}
    for r in records:
        name = r['path']
        if 'original_bytes' in r:
            fn = name + '.gz'
            packed = (path / fn).read_bytes()
            assert len(packed) == r['gzip_bytes'] and sha(packed) == r['gzip_sha256']
            raw = gzip.decompress(packed)
            assert len(raw) == r['original_bytes'] and sha(raw) == r['original_sha256']
        else:
            fn = name
            raw = (path / fn).read_bytes()
            assert len(raw) == r['bytes'] and sha(raw) == r['sha256']
        files.add(fn)
        payload[name] = raw
    assert files == {p.name for p in path.iterdir() if p.is_file()}
    return payload, len(records)

edges = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
target = sum(1 << r for r in range(1024) if any(r >> a & 1 and r >> b & 1 for a,b in edges))
def operation(d,a,b):
    return [a & b, a | b, a & ~b, ~a & b][d]

start = time.monotonic()
p, n = archive(ROOT / 'search/signed17-terminal-measurement', '123e4eacf738cf88ab13db7c3073e6f6b1c7f2b17d31d42aa93bded3f7dd0122')
patch = ''.join(difflib.unified_diff(p['live_search_resume.cpp'].decode().splitlines(True), p['signed17_formula_measured.cpp'].decode().splitlines(True), fromfile='live_search_resume.cpp', tofile='signed17_formula_measured.cpp'))
assert patch.encode() == p['instrumentation.patch']
summary = json.loads(p['formula-census-summary.json'])
status = json.loads(p['formula-census-status.json'])
assert summary['status'] == status and status['exit_code'] == 5 and status['command'][-1] == '180'
assert p['formula-census.stderr.txt'].decode().endswith('ordinary census time limit after 1045 banks\n')
assert p['signed17-formula-build.stdout.txt'] == p['signed17-formula-build.stderr.txt'] == b''
zd = zlib.decompressobj()
raw = zd.decompress(p['formula-tables-shortlist.zlib']) + zd.flush()
assert zd.eof and not zd.unused_data and not zd.unconsumed_tail
assert len(raw) == summary['binary_bytes'] and sha(raw) == summary['binary_sha256']
assert len(p['formula-tables-shortlist.zlib']) == summary['zlib_bytes']
lines = p['formula-banks.txt'].decode().splitlines()
ns = int(lines[0]); signals = [int(x,16) for x in lines[1:ns+1]]
assert ns == 1275 and int(lines[ns+1]) == 4258
banks = []
for line in lines[ns+2:]:
    part,node,kind,nr,*indices = line.split()
    indices = list(map(int,indices))
    assert len(indices) == int(nr)
    banks.append((part,int(node),int(kind),[signals[i] for i in indices]))
reps = json.loads(p['formula-representatives.json'])
assert len(banks) == len(reps) == 4258
for (part,node,kind,ws), rep in zip(banks,reps):
    assert (part,node,kind) == (rep['part'],rep['node'],int(rep['kind']=='formula1'))
    assert ws == [signals[i] for i in rep['state']]
rows = [json.loads(x) for x in p['formula-census.jsonl'].splitlines()]
pos = 0
def var():
    global pos
    value = shift = 0
    while True:
        b = raw[pos]; pos += 1
        value |= (b & 127) << shift
        if b < 128:
            assert shift == 0 or b != 0
            return value
        shift += 7
        assert shift <= 63

parent = -1
base = None
next_copy = 0
last_kind = None
totals = collections.Counter()
max_entries = 0
for row in rows:
    assert row['answer'] == 0
    if row['copy'] == -1:
        if parent >= 0:
            assert next_copy == (len(base) if last_kind else 0)
        parent += 1
        part,node,last_kind,original = banks[parent]
        ws = original
        next_copy = 0
    else:
        assert row['copy'] == next_copy and last_kind == 1
        mask,w = base[next_copy]
        ws = [v for i,v in enumerate(original) if not (mask >> i & 1)] + [w,w]
        next_copy += 1
    assert (row['part'],row['node']) == (part,node)
    nr,derived = var(),var()
    assert nr == row['roots'] == len(ws) and nr+derived == row['entries']
    es = [(1 << i,w) for i,w in enumerate(ws)]
    known = set(es)
    for j in range(derived):
        d,a,b = var(),var(),var()
        assert 0 <= d < 4 and a < len(es) and b < len(es)
        ma,va = es[a]; mb,vb = es[b]
        assert not ma & mb
        v = operation(d,va,vb); e = (ma|mb,v)
        assert v != 0 and v != va and v != vb and e not in known
        assert not (e[0] == (1 << nr)-1 and v == target)
        es.append(e); known.add(e)
    if row['copy'] == -1:
        base = es
    count = var()
    assert count == row['distinct_rows']
    previous = -1
    for j in range(count):
        pair = var(); positive,negative = pair >> 10,pair & 1023
        assert pair > previous and positive < 1024
        assert target >> positive & 1 and not (target >> negative & 1)
        previous = pair
    totals.update(tables=1,entries=nr+derived,derived_entries=derived,candidate_operations=row['tries'],row_rejections=row['row_rejects'],row_shortlist_total=count,base_tables=int(row['copy']==-1),copied_tables=int(row['copy']!=-1))
    max_entries = max(max_entries,nr+derived)
assert pos == len(raw) and dict(totals) == summary['measured']
assert parent+1 == summary['parent_banks_touched'] == 1046
assert max_entries == summary['largest_completed_table_entries'] == 2669
assert next_copy < len(base) and last_kind == 1
terminal = dict(manifest_entries=n, measured=dict(totals), parent_banks_touched=parent+1, completed_parents=parent, unfinished_parent_copy_tables=next_copy, unfinished_parent_total_copies=len(base), all_binary_bytes_consumed=pos, source_patch_exact=True, derived_operations_replayed=True, row_pairs_classified=True, scope='Preservation and table provenance/encoding audit; does not independently enumerate all rejected candidate operations or prove closure in Lean.')
print('TERMINAL',json.dumps(terminal),flush=True)

q, n = archive(ROOT / 'signed17-rectangle-applicability', '72b694c857879b2f49cb07e3ef364b41d9072040d578b9d02a39012a30e7a43e')
assert q['leaf-banks.json'] == p['leaf-banks.json']
data = json.loads(q['leaf-banks.json']); matrices = json.loads(q['matrices.json'])
assert len(data['signals']) == 1275 and len(data['banks']) == 4360 and len(matrices) == 62
signals = [int(x,16) for x in data['signals']]
actual = [set() for _ in matrices]
support_work = 0
for i,c in enumerate(matrices):
    ps,ns,w = c['positive_rows'],c['negative_rows'],c['weights']
    assert 0 < len(ps) <= 21 and 0 < len(ns) <= 21
    assert len(w)==len(ps) and all(len(row)==len(ns) for row in w)
    assert all(target >> r & 1 for r in ps) and all(not (target >> r & 1) for r in ns)
    assert c['total'] == sum(map(sum,w)) > 0
    assert sum(abs(x) for row in w for x in row) < 2**63
    for sig in signals:
        pm=sum(((sig>>r)&1)<<j for j,r in enumerate(ps))
        nm=sum((1-((sig>>r)&1))<<j for j,r in enumerate(ns))
        actual[i].update([(pm,nm),(pm^((1<<len(ps))-1),nm^((1<<len(ns))-1))])
    support_work += sum((1 << min(pm.bit_count(),nm.bit_count())) * max(pm.bit_count(),nm.bit_count()) for pm,nm in actual[i])
rows = json.loads(q['all-signed-bank-margins.json'])
assert len(rows)==len(data['banks'])
counts=collections.Counter()
for row,bank in zip(rows,data['banks']):
    for k in ['part','node','kind','roots']:
        assert row[k]==bank[k]
    assert len(row['positive_margins'])==len(row['both_margins'])==62
    assert all(isinstance(x,int) for x in row['both_margins'])
    assert max(row['both_margins'])<=0
    for group in ['union']+bank['roots']:
        counts[group+'_'+bank['kind']]+=1
replay=json.loads(q['replay-summary.json']); original=json.loads(q['all-signed-summary.json'])
assert json.loads(q['replay-full.txt'])==replay and json.loads(q['measure-all-signed-full.txt'])==original
assert replay['summary']==original['summary']
assert sum(map(len,actual))==replay['actual_unique_profiles']==157852
assert original['unique_profiles']==157852+390
for key,c in replay['summary'].items():
    assert c['banks']==counts[key] and c['both_polarity_margins']==0
assert q['build.txt']==q['rectangle-dynamic-build.txt']==b''
rectangle=dict(manifest_entries=n,matrices=62,banks=4360,signals=1275,actual_unique_profiles=sum(map(len,actual)),original_sanity_profiles=390,strict_signed_margins=0,all_margin_vectors_inspected=True,full_numerical_cost_rerun=False,estimated_gray_update_work=support_work,source_review='Gray-code smaller-support enumeration and exact-integer polarity/max application reviewed; preserved portable replay and1860 small-subset crosschecks read, no new native build or search.',scope='Evidence for these62 matrices and parent banks only. Formula1 copied bases are not discharged; no signed Lean theorem or whole-case exclusion.')
print('RECTANGLE',json.dumps(rectangle),flush=True)
out=dict(terminal=terminal,rectangle=rectangle,elapsed_seconds=time.monotonic()-start)
(ROOT/'verification/audit-signed17-preservation.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',flush=True)
