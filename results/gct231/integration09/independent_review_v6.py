from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re
base=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();hs=lambda s:hashlib.sha256(s.encode()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
m=json.loads((base/'assembly-v6-manifest.json').read_text());p=base/'L_gct_231_IncrementalCandidateV6.lean';text=p.read_text();aux='PEqualNP.Outside.L_gct_231_aux'
assert sha(p)==m['candidate_sha256']=='d2a724e6eb3c78592987233a86919f6d41e2acdcdee49b7b4c862c92b770026a'
assert len(text.encode())==491683<512*1024 and len(text.splitlines())==3039
# Namespace depth validation is independent of the assembler manifest.
def scan(source):
 stack=[];top=[];outside=[];decls={};blocks=[];start=None
 lines=source.splitlines(keepends=True)
 for i,line in enumerate(lines):
  t=line.strip()
  if t.startswith(('namespace ','section ','end ')):assert line==line.lstrip()
  if line.startswith('namespace ') or line.startswith('section '):
   kind,name=t.split(' ',1)
   if not stack:
    assert kind=='namespace';top.append((i+1,name));start=i
   stack.append((kind,name))
  elif line.startswith('end '):
   kind,name=stack.pop();assert name==t[4:]
   if not stack:blocks.append((name,''.join(lines[start+1:i])))
  else:
   if not stack and t:outside.append(t)
   match=re.match(r'(?:(?:noncomputable|private|protected)\s+)*(?:theorem|lemma|def|abbrev)\s+([^\s(:]+)',line)
   if match:
    name='.'.join([name for kind,name in stack if kind=='namespace']+[match.group(1)])
    assert name not in decls;decls[name]=i+1
 assert not stack
 return top,outside,decls,blocks
outer,outside,decls,blocks=scan(text)
assert outer==[(34,aux)] and len(blocks)==1
assert outside==m['imports'] and all(t.startswith('import ') for t in outside)
assert len(decls)==322 and decls==json.loads((base/'assembly-v6-declaration-index.json').read_text())
print('CONTRIBUTING rule7 explicitly checked: exactly one top-level auxiliary namespace; only32import lines outside; all namespace/section/end commands column0 and named: PASS',flush=True)
old=Path(m['base']);assert sha(old)==m['base_sha256']=='c99884a7311d847e0b23c4b1147c4a30bb133630a07dace51a6129675c6feee2'
oldblocks=scan(old.read_text())[3];assert len(oldblocks)==1;oldbody=oldblocks[0][1]
assert hs(oldbody)==m['base_inner_body_sha256'] and text.count(oldbody)==1
source_cache={}
for c in m['components']:
 path=Path(c['source']);assert sha(path)==c['source_sha256']
 if path not in source_cache:source_cache[path]=scan(path.read_text())[3]
 oldns,body=source_cache[path][c['source_block']]
 assert oldns==c['old_namespace'] and hs(body)==c['inner_body_sha256'] and len(body.encode())==c['inner_body_bytes']
 block=c['new_scope_kind']+' '+c['new_relative_scope']+'\n'+body+'end '+c['new_relative_scope']+'\n'
 assert text.count(block)==1 and text.count(body)==1
 # Rebased norm has no reference back to its old fully qualified namespace.
 if oldns!=aux+'.'+c['new_relative_scope']:assert oldns+'.' not in body
 print('Exact innerbody/scoped wrapper',c['component'],c['source_block'],c['inner_body_sha256'],flush=True)
v5=json.loads((base/'assembly-v5-declaration-index.json').read_text());oldnames=set(v5);newnames=set(decls)
assert oldnames-newnames=={'PEqualNP.Outside.L_gct_231.trace.case2_projective_norm_obstruction'}
assert newnames-oldnames=={aux+'.Case2ProjectiveNorm.case2_projective_norm_obstruction'}
assert len([n for n in decls if n.endswith('.resultant_zero_of_common_root')])==1
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',text) and '_root_' not in text and '"' not in text
assert not re.search(r'^\s*(initialize|#|macro|syntax|elab|attribute)\b',text,re.M)
assert all(l.endswith(' in') for l in text.splitlines() if l.startswith('set_option '))
assert 'import' not in text[text.index('namespace '):]
assert not re.search(r'^(?:theorem|lemma)\s+L_gct_231(?:\s|:)',text,re.M)
print('All reviewed innerbodies/statements exact,322 declarations/no collisions; only norm theorem FQ name rebased, other names preserved. Forbidden-feature/import-position/size checks: PASS',flush=True)
print('Correction: V3-V5 earlier broad formatPASS missed the single outer namespace rule; this V6 review explicitly closes that omission. Partial preservation source only; main theorem and raw-to-normalized bridge remain absent. No compiler here.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True);print('PASS',flush=True)
