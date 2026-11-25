from pathlib import Path
import hashlib,gzip,json,collections,datetime
base=Path(__file__).resolve().parent/'search/mono19-or-edge-checkpoints'
out=base.parents[1]
manifest=json.loads((base/'manifest.json').read_text());census=json.loads((base/'census.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checks={};counts={};memo_keys={};refs=set();dictionary=set();events=collections.Counter();occ=0
for name,meta in manifest.items():
 if 'gzip_sha256' not in meta:
  p=base/name;assert p.stat().st_size==meta['bytes'];assert sha(p)==meta['sha256'];checks[name]='PASS';continue
 p=base/(name+'.gz');assert p.stat().st_size==meta['gzip_bytes'];assert sha(p)==meta['gzip_sha256']
 digest=hashlib.sha256();size=0;deficits=collections.Counter();keys=set()
 with gzip.open(p,'rb') as stream:
  for i,line in enumerate(stream):
   digest.update(line);size+=len(line)
   if name.endswith('.memo'):
    if i==0:assert line==b'PNP_COPY_MEMO_V1 0 19 oredge 0\n';continue
    parts=line.split();assert parts[0]==b'S';k,n=map(int,parts[1:3]);assert len(parts)==3+n and 0<=k<=19 and 1<=n<=k+1
    for w in parts[3:]:assert len(w)==258 and w[:2]==b'0x' and all(c in b'0123456789abcdefABCDEF' for c in w[2:])
    deficits[k-n+1]+=1;keys.add(hashlib.sha256(line).digest())
   else:
    e=json.loads(line);events[e['event']]+=1
    if e['event']=='header':assert e['signed']==0 and e['cap']==19 and e['first']=='oredge'
    elif e['event']=='rectangle':
     assert len(e['state'])==len(e['root_costs']) and sum(e['root_costs'])==e['cost_sum']<e['total']
     assert all(c>=0 for c in e['root_costs']);refs.update(e['state']);occ+=len(e['state'])
    else:
     assert e['event']=='signal' and e['id'] not in dictionary;dictionary.add(e['id']);assert len(e['hex'])==258;int(e['hex'],16)
 assert size==meta['original_bytes'] and digest.hexdigest()==meta['original_sha256'];checks[name]='PASS'
 if name.endswith('.memo'):
  counts[name]=dict(sorted(deficits.items()));memo_keys[name]=keys
  assert {str(k):v for k,v in deficits.items()}==census['memo_counts_by_deficit'][name]
assert dict(events)==census['event_counts'] and occ==census['root_occurrences'] and refs<=dictionary
assert memo_keys['mono19-oredge-completed-paused.memo']<=memo_keys['mono19-oredge-completed.memo']
assert sum(counts['mono19-oredge-completed.memo'].values())==52206
assert sum(counts['mono19-oredge-completed-paused.memo'].values())==52200
status=json.loads((base/'copy-first-checkpoint-oredge-mono19-1200.status.json').read_text());assert status['exit_status']==0
start=datetime.datetime.fromisoformat(status['started_utc']);end=datetime.datetime.fromisoformat(status['finished_utc']);assert abs((end-start).total_seconds()-status['wall_seconds'])<0.01
log=(base/'copy-first-checkpoint-oredge-mono19-1200.log').read_text();assert 'limit reached' in log and 'finished found=0' not in log
report={'verdict':'PASS','manifest_entries':len(checks),'checks':checks,'events':dict(events),'root_occurrences':occ,'referenced_signatures':len(refs),'dictionary_signatures':len(dictionary),'memo_deficit_counts':counts,'paused_subset_final':True,'exit_status':status['exit_status'],'scope':'Archive integrity and structural census only; root open, no complete Lean exclusion.'}
(out/'review-original-checkpoint-archive.json').write_text(json.dumps(report,indent=2)+'\n')
(out/'review-original-checkpoint-archive.txt').write_text('PASS: all11manifest entries, all4gzip CRC/decompressed streams, compressed/original hashes and sizes independently verified. Parsed every rectangle, signature and memo record; strict rectangle cost sums, duplicate-root cardinalities, complete referenced dictionary, memo shape/deficit census and paused-checkpoint inclusion all match. Final52206states, paused52200states,678304rectangle cuts,42821signatures. Status exit0 and1234.24seconds including pause agree with timestamps and full log. The root remains open; this is a bounded computational checkpoint, not a Lean certificate or complete first-gate exclusion. Exact root-cost maxima and mathematical cofactor bounds are outside this archive-integrity review.\n')
print(json.dumps({k:report[k] for k in ['verdict','manifest_entries','events','referenced_signatures','dictionary_signatures','exit_status','scope']}))
