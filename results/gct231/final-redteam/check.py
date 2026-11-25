from pathlib import Path
import hashlib,json,re,stat
repo=Path('/workspace/pequalnp-proofs');out=Path(__file__).parent
source=repo/'lean/PEqualNP/Outside/L_gct_231.lean';archive=repo/'results/gct231/integration10'
raw=source.read_bytes();text=raw.decode('utf-8');lines=text.splitlines();digest=hashlib.sha256(raw).hexdigest()
assert digest=='f5508fba3b3c32933c3cfa55aa9b37a944c8b76b3ad031143e5ecae9bb5e30e2'
assert len(lines)==3133 and len(raw)==504298 and len(raw)<=512*1024
assert not source.is_symlink() and stat.S_ISREG(source.stat().st_mode) and source.stat().st_mode & 0o111==0
assert raw==(archive/'L_gct_231.lean').read_bytes()
entries={}
for row in (archive/'SHA256SUMS').read_text().splitlines():
 h,n=row.split('  ',1);assert n not in entries;entries[n]=h
 assert hashlib.sha256((archive/n).read_bytes()).hexdigest()==h,n
assert {str(p.relative_to(archive)) for p in archive.rglob('*') if p.is_file()}==set(entries)|{'SHA256SUMS'}
print('EXACT NAMED SOURCE AND INTEGRATION10 ARCHIVE PASS',digest,len(entries),flush=True)

imports=[];i=0
while i<len(lines) and lines[i].startswith('import '):
 assert re.fullmatch(r'import (Mathlib(?:\.[A-Za-z0-9_]+)*|PEqualNP\.Defs)',lines[i]);imports.append(lines[i]);i+=1
assert len(imports)==33 and not re.search(r'\bimport\b','\n'.join(lines[i:]))
banned=r'_root_|"|\bsorry\b|\baxiom\b|\bnative_decide\b|\bunsafe\b|\binitialize\b|\belab\b|\bsyntax\b|\bmacro\b|\bnotation\b|\battribute\b|\binstance\b|\binductive\b|\bstructure\b|\bopaque\b|#'
assert not re.search(banned,text)
assert '@[' not in text
options=[]
for j,line in enumerate(lines):
 if 'set_option' in line:
  assert re.fullmatch(r'set_option (maxRecDepth|maxHeartbeats|synthInstance\.maxSize|synthInstance\.maxHeartbeats) [0-9]+ in',line)
  k=j+1
  while lines[k].startswith('set_option '):k+=1
  assert re.match(r'(?:(?:noncomputable|private|protected) )*(?:def|abbrev|lemma|theorem)\b',lines[k]),(j+1,lines[k])
  options.append(line)
stack=[];outer=0;decls={}
for j,line in enumerate(lines):
 m=re.fullmatch(r'(namespace|section) ([A-Za-z0-9_.]+)',line)
 if m:
  if not stack:assert m.group(1)=='namespace' and m.group(2)=='PEqualNP.Outside.L_gct_231_aux';outer+=1
  stack.append(m.groups());continue
 m=re.fullmatch(r'end ([A-Za-z0-9_.]+)',line)
 if m:
  assert stack and stack[-1][1]==m.group(1),(j+1,stack,line);stack.pop();continue
 m=re.match(r'(?:(?:noncomputable|private|protected)\s+)*(def|abbrev|lemma|theorem)\s+([A-Za-z0-9_.]+)',line)
 if m:
  assert stack,(j+1,line)
  name='.'.join([name for kind,name in stack if kind=='namespace']+[m.group(2)])
  assert name not in decls;decls[name]=j+1
 if not stack and j>=i and line.strip():
  assert line.startswith('--'),(j+1,line[:100])
assert not stack and outer==1 and len(decls)==326
assert 'PEqualNP.Outside.L_gct_231' not in decls
index=json.loads((archive/'assembly-v7fallback-declaration-index.json').read_text());assert decls==index
print('FORMAT/NAMESPACE/DECLARATION PASS',len(imports),'imports',len(options),'scoped limits',len(decls),'declarations; main theorem absent',flush=True)

audit=(archive/'AxiomAudit10.lean').read_text().splitlines()
assert audit[0]=='import PEqualNP.Outside.L_gct_231'
queries=[line.removeprefix('#print axioms ') for line in audit[1:] if line.strip()]
assert len(queries)==326 and set(queries)==set(decls)
log=(archive/'axioms-partial-10.log').read_text()
found={}
pattern=r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
for m in re.finditer(pattern,log,re.S):
 name=m.group(1);assert name not in found
 axioms=sorted(x.strip() for x in (m.group(2) or '').split(',') if x.strip())
 assert set(axioms)<={'propext','Classical.choice','Quot.sound'},(name,axioms)
 found[name]=axioms
assert set(found)==set(decls)
saved=json.loads((archive/'axioms-partial-10-verified.json').read_text())
assert saved['status']=='PASS' and saved['returncode']==0 and saved['declarations']==326 and saved['source_sha256']==digest
assert found==saved['axioms_by_declaration']
build=(archive/'build-partial-10.log').read_text()
assert 'Build completed successfully (6687 jobs).' in build and re.search(r'Built PEqualNP.Outside.L_gct_231.*227s',build)
assert not re.search(r'(^|\n).*error(?:\(|:)',build)
validation=json.loads((archive/'validation.json').read_text())
assert validation['lake_build_exit']==validation['axiom_audit_exit']==0 and validation['module_seconds']==227 and validation['lake_jobs']==6687
print('BUILD AND ALL326 AXIOM AUDIT CONSISTENCY PASS',flush=True)

gap=json.loads((repo/'results/gct231/gap.json').read_text())
assert gap['id']=='L-gct-231' and gap['imports']==['PEqualNP.Defs']
assert (repo/'results/gct231/statement.txt').read_text().strip()==gap['statement']
assert gap['statement'].startswith('∃ L : Submodule ℂ')
meta=(repo/'results/gct231/validation.txt').read_text()
assert 'PARTIAL ONLY; no proof/refutation and no PR.' in meta and digest in meta
assert 'Sub-agents:' in meta and re.search(r'TIMING total=[0-9.]+ subagents=8',meta)
assert 'msg-8f0f42bb760e4ee78f16c6cd' in meta
checker=out.parent/'checker-partial-10.log'
checktext=checker.read_text() if checker.exists() else ''
verdicts=re.findall(r'(?:REJECTED|ACCEPTED|CHECKER FAULT)[^\n]*',checktext)
print('CHECKER10 OBSERVED',verdicts[-1] if verdicts else 'no terminal verdict in log yet',flush=True)
result={'status':'PASS_FOR_PRESERVATION_ONLY','not_full_gap':True,'source_sha256':digest,'lines':len(lines),'bytes':len(raw),'limit_slack_bytes':512*1024-len(raw),'archive_manifest_sha256':hashlib.sha256((archive/'SHA256SUMS').read_bytes()).hexdigest(),'imports':len(imports),'outer_namespace_count':outer,'declarations':len(decls),'all_axioms_standard':True,'main_theorem_present':False,'checker10_observed':verdicts[-1] if verdicts else 'PENDING','metadata_scope':'No proof/refutation/PR; timing and final checker/release/push metadata need final refresh if still running.'}
(out/'verdict.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
