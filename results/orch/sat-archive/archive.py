from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil
src=Path('/tmp/oec/pequalnp-pilot-42/sat')
dst=Path('/workspace/pequalnp-proofs/results/orch/sat-archive')
dst.mkdir(parents=True,exist_ok=True)
manifest=[]
for p in sorted(src.iterdir()):
 if p.is_file() and (p.suffix in {'.py','.log','.json'} or (p.suffix=='.txt' and ('witness' in p.name or 'help' in p.name))):
  data=p.read_bytes();(dst/p.name).write_bytes(data)
  manifest.append({'name':p.name,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()})
cnf=[]
for p in sorted(src.glob('*.cnf')):
 data=p.read_bytes();cnf.append({'name':p.name,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'archived':False,'reason':'regenerable from archived source'})
excluded=[{'name':p.name,'bytes':p.stat().st_size,'status':'incomplete; no UNSAT result; not a certificate'} for p in sorted(src.glob('*.lrat'))]
now=datetime.now(timezone.utc).isoformat()
(dst/'MANIFEST.json').write_text(json.dumps({'snapshot_utc':now,'files':manifest,'regenerable_cnf':cnf,'excluded_traces':excluded},indent=2)+'\n')
(dst/'README.md').write_text('''# L-meta-5112 SAT search archive\n\nSnapshot UTC: '''+now+'''.\n\nThese are unsuccessful search artifacts, not a proof or a refutation. No completed SAT witness or UNSAT certificate was obtained before this snapshot. The final result submitted by the root agent is tracked separately.\n\nGenerator sources, metadata, and complete stdout/stderr streams are preserved here. Logs of any still-running processes are complete through the snapshot time. `MANIFEST.json` records SHA-256 hashes and sizes. CNF files are reproducible from the generators and are represented by hashes; incomplete large LRAT traces remain excluded and explicitly unproven.\n\nKey generators:\n\n- `complete24.py`: exactly 14 arbitrary gates, Fin28 selectors including default zero, 24 selected original bit rows; no normalization assumptions.\n- `complete.py`: analogous 58-row encoding.\n- `free_and.py`: at most 10 OR gates with arbitrary conjunctions as operands and final output.\n- `free_and_closed.py`: canonical conjunction closure preserving all positive rows and decreasing negative rows; stronger normalization proof not completed here.\n- Other variants impose additional minimality or symmetry conditions and were used only for witness search. An UNSAT answer from those variants alone would not establish a refutation.\n\nEvery solver run either reached its time limit, was stopped for CPU availability, or was still active at snapshot time. Full logs record the actual status.\n''')
print('archived',len(manifest),'files','snapshot',now)
