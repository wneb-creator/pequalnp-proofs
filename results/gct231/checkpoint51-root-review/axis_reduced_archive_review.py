from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
base=Path('/workspace/pequalnp-proofs/results/gct231/axis-reduced-certificates');scratch=Path('/tmp/oec/pequalnp-pilot-75/gct231/triangle-kernel-zero')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1<<20),b''):h.update(chunk)
 return h.hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
man=base/'sha256.json';assert sha(man)=='954fd6b0909da2a3390ab3b2f5831dae3a61b2228db85e4a614e9c288f81dabf';d=json.loads(man.read_text());files={str(p.relative_to(base)):p for p in base.rglob('*') if p.is_file() and p!=man};assert len(files)==70 and set(files)==set(d)
assert sum(p.stat().st_size for p in files.values())+man.stat().st_size==2511096
for name,p in files.items():
 assert sha(p)==d[name] and not p.is_symlink();data=p.read_bytes();data.decode('utf8');assert b'\x00' not in data and not data.startswith((b'\x7fELF',b'MZ'))
 if (scratch/name).exists():assert data==(scratch/name).read_bytes(),name
assert sha(base/'AxisReducedCertificates.lean')=='8eeef2cb88b2869c59b72329d5b896b37f818f64b6e41c95d7ae4c10769c39cc'
for case,h in [('equal','2c6931d0ebc0435a94320453eace4dd742319b346fa196679f2aec89c1d0a44c'),('different','905e2335cc4c84cd50a6222c48213e9ab03d9f78bfa671523a624033245e4d05')]:assert sha(base/('axis-four-'+case+'-quotient-compressed-certificate.json'))==h
source=(base/'AxisReducedCertificates.lean').read_text();audit=(base/'AxisReducedAudit.lean').read_text();assert audit.startswith(source);ns='PEqualNP.Outside.L_gct_231_aux.AxisReduced.';names=['equal_chart_inconsistent','different_chart_inconsistent'];assert [l for l in audit[len(source):].splitlines() if l.strip()]==['#print axioms '+ns+n for n in names]
run=json.loads((base/'axis-reduced-audit.run.json').read_text());assert run['status']=='PASS' and run['returncode']==0 and run['wall_seconds']==45.37547578900194 and run['peak_group_rss_kib']==3269860 and run['seconds_limit']==90 and run['resident_memory_mib_limit']==4096
log=(base/'axis-reduced-audit.log').read_text();records=re.findall(r"'([^']+)' depends on axioms: \[([^]]+)\]",log);assert len(records)==2
for (actual,axes),name in zip(records,names):assert actual==ns+name and [v.strip() for v in axes.split(',')]==['propext','Classical.choice','Quot.sound']
assert re.sub(r"'([^']+)' depends on axioms: \[([^]]+)\]",'',log).strip()==''
prov=json.loads((base/'omitted-intermediate-provenance.json').read_text())
for name,item in prov['files'].items():assert not (base/name).exists() and (scratch/name).stat().st_size==item['bytes'] and sha(scratch/name)==item['sha256']
readme=(base/'README.md').read_text();assert 'not** been formalized in Lean or independently reviewed as a complete coverage proof' in readme and 'six explicitly displayed polynomial equations' in readme
print('Exact70-entry coverage/hash/text-only/all preserved scratch copies; compiled source and both reviewed exact certificates unchanged: PASS',flush=True)
print('Exactsource+2queries driver; exit0/45.375476s/3269860KiB under90s/4GiB; boththeorems standard3axioms: PASS',flush=True)
print('All6omitted intermediate sizes/fullstream hashes verified; smalltraces included text-only. README explicitly leaves geometry/coverage bridge unreviewed/unformalized. No solver/compile rerun.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True);print('PASS',flush=True)
