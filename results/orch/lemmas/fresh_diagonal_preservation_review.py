from pathlib import Path
import json,re,hashlib
base=Path('/tmp/oec/pequalnp-pilot-79');repo=Path('/workspace/pequalnp-proofs');d=json.loads((base/'three-plane-diagonal-final-preservation-manifest.json').read_text());assert len(d['files'])==23 and 'no DiagonalAnchorMoment Lean variant has compiled' in d['classification']
stat=[]
for e in d['files']:
 p=Path(e['path']);assert p.parent==repo/'results/orch/lemmas'
 assert p.is_file() and p.stat().st_size==e['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==e['sha256']
 if p.suffix=='.lean':assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',p.read_text())
 if p.name.endswith('status.json'):
  s=json.loads(p.read_text());stat.append([p.name,s.get('exit_code'),s.get('reason')]);assert s.get('exit_code')!=0
det=json.loads((repo/'results/orch/lemmas/three-plane-diagonal-anchor-integer-moment.json').read_text())
print('PASS 23 manifest files,',sum(e['bytes'] for e in d['files']),'bytes. Four attempted Lean build statuses checked as failures; exact tensor/moment calculation remains mathematical evidence, not a checked geometric exclusion.',stat,'manifest SHA',hashlib.sha256((base/'three-plane-diagonal-final-preservation-manifest.json').read_bytes()).hexdigest())
