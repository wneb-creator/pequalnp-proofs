#!/usr/bin/env python3
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--verify-only',action='store_true');p.parse_args()
r=Path(__file__).resolve().parent;m=json.loads((r/'manifest.json').read_text())
for n,h in m['files'].items():
 f=r/n;assert f.is_file() and hashlib.sha256(f.read_bytes()).hexdigest()==h,n
v=json.loads((r/'range-manifest.json').read_text());assert [e['start'] for e in v['entries']]==list(range(3840,4352,64))
for e in v['entries']:assert e['count']==64 and e['end_inclusive']==e['start']+63
for q in m['modules']:
 z=json.loads((r/q['result']).read_text());assert z['exit_code']==0 and not z['timed_out'];assert z['sha256']==hashlib.sha256((r/q['source']).read_bytes()).hexdigest()
a=json.loads((r/'aggregate-audit.json').read_text());assert a['expectedTypeElaborated'];assert all(not a[k] for k in ['foreignKernelExports','ownerMismatches','disallowedAxioms'])
assert all(set(x['axioms']) <= {'propext','Classical.choice','Quot.sound'} for x in a['declarations'])
print('PASS: packet hashes, completed512-node coverage, receipts and recorded aggregate audit')
