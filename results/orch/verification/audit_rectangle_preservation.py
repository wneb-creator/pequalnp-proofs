from pathlib import Path
import json,hashlib,re
repo=Path('/workspace/pequalnp-proofs');mp=repo/'results/orch/mono18-rectangle-preservation.json';m=json.loads(mp.read_text())
def read(rel):
 p=Path(rel);assert not p.is_absolute() and '..' not in p.parts and p.parts[:2]==('results','orch'),rel
 return (repo/p).read_bytes()
seen=set()
for f in m['files']:
 assert f['path'] not in seen;seen.add(f['path']);data=read(f['path']);assert len(data)==f['bytes'];assert hashlib.sha256(data).hexdigest()==f['sha256']
assert set(m['preserve_paths'])==seen|{str(mp.relative_to(repo))}
assert len(m['preserve_paths'])==183 and len(seen)==182
assert m['checked_module_count']==len(m['checked_modules'])==34
checked=set()
for e in m['checked_modules']:
 assert e['source'] not in checked
 assert {e['source'],e['build']['log'],e['build']['status'],*e['reviews']} <= seen
 checked.add(e['source']);s=read(e['source']);assert hashlib.sha256(s).hexdigest()==e['sha256'] and len(s)==e['bytes'];assert e['build']['exit']==0
 log=read(e['build']['log']);assert hashlib.sha256(log).hexdigest()==e['build']['log_sha256'];assert not re.search(rb'(^|\s)error(?:\([^)]*\))?:',log)
 status=json.loads(read(e['build']['status']));assert status['source']==e['source'] and status['source_sha256']==e['sha256'];assert status['log']==e['build']['log'] and status['log_sha256']==e['build']['log_sha256'];assert status['original_status']['exit']==0
 assert Path(status['original_status']['source']).name == Path(e['source']).name
 for r in e['reviews']:assert read(r)
assert set(m['drafts']['paths'])<=seen and not(set(m['drafts']['paths'])&checked)
for d in m['previously_reviewed_dependencies']:
 assert {d['source'],d['log'],*d['reviews']} <= seen
 assert hashlib.sha256(read(d['source'])).hexdigest()==d['sha256'];assert hashlib.sha256(read(d['log'])).hexdigest()==d['log_sha256'];assert all(read(r)for r in d['reviews'])
report={'verdict':'PASS','manifest_sha256':hashlib.sha256(mp.read_bytes()).hexdigest(),'files':len(seen),'payload_bytes':sum(f['bytes']for f in m['files']),'preserve_paths':len(m['preserve_paths']),'checked_modules':len(checked),'draft_paths':m['drafts']['paths'],'scope':'Integrity, declared status, source/log/status binding and draft separation only; no new Lean build or duplicate substantive theorem review.'}
(repo/'results/orch/review-mono18-rectangle-preservation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
