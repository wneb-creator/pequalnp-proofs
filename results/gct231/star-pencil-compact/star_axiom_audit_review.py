from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re
base=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
c=base/'StarPencilClassification.lean';e=base/'StandardStarTriangleExtension.lean';a=base/'StarPencilAudit.lean'
assert sha(c)=='7bdbee0dc04cb54742c6a0e3a60c474cbd5a9bc50dc1df6529bca5899db32603' and sha(e)=='6489a8b3eb7ba20ea65c77dfb5f2c2dc34bcfb13926bc94f51b20864ed84f7b7'
src=a.read_text();assert src.startswith(c.read_text());body=e.read_text()[e.read_text().index('namespace '):];assert src.count(body)==1
rest=src[len(c.read_text()):].replace(body,'',1);names=['r_eq_zero_of_coefficients','coefficients_force_standard_star','standard_star_triangle_extension_impossible'];prefix='PEqualNP.Outside.L_gct_231_aux.StarPencil.'
assert [l for l in rest.splitlines() if l.strip()]==['#print axioms '+prefix+n for n in names]
run=json.loads((base/'star-axiom-audit.run.json').read_text());assert run['status']=='PASS' and run['returncode']==0 and run['wall_seconds']==49.444782572001714 and run['peak_group_rss_kib']==4350560
assert run['seconds_limit']==180 and run['resident_memory_mib_limit']==6144
log=(base/'star-axiom-audit.log').read_text();records=re.findall(r"'([^']+)' depends on axioms: \[([^]]+)\]",log);assert len(records)==3
for (name,axioms),expected in zip(records,names):assert name==prefix+expected and [s.strip() for s in axioms.split(',')]==['propext','Classical.choice','Quot.sound']
assert re.sub(r"'([^']+)' depends on axioms: \[([^]]+)\]",'',log).strip()==''
print('Exact driver preserves checked classification7bd and reviewed extension6489; only3axiom queries added. Audit exit0/49.444783s/4350560KiB; all3theorems standard3axioms only: PASS',flush=True)
print('Driver SHA256',sha(a),flush=True)
print('Original classification archive remains unchanged; this is separate completed audit evidence. No compiler rerun.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True);print('PASS',flush=True)
