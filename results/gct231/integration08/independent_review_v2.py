from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
base=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat())
m=json.loads((base/'assembly-v2-manifest.json').read_text());candidate=base/'L_gct_231_CombinedCandidateV2.lean';text=candidate.read_text()
assert sha(candidate)==m['candidate_sha256']=='c99884a7311d847e0b23c4b1147c4a30bb133630a07dace51a6129675c6feee2'
assert len(text.encode())==267790 and len(text.splitlines())==2593
old=base/'Named1528Snapshot.lean';assert sha(old)==m['named_source_sha256']=='42c23a475a0793c31278bd6324609ad96d59e78b571e2152b346d3a0a79e656c'
assert len(old.read_text().splitlines())==1528
aux='PEqualNP.Outside.L_gct_231_aux'
def extract(source):
 lines=source.splitlines(keepends=True);opening=next(i for i,line in enumerate(lines) if line.startswith('namespace '));ns=lines[opening].strip()[10:]
 ending=max(i for i,line in enumerate(lines) if line.strip()=='end '+ns)
 assert not ''.join(lines[ending+1:]).strip()
 assert all(not line.strip() or line.startswith('import ') for line in lines[:opening])
 return [line.strip() for line in lines[:opening] if line.startswith('import ')],ns,''.join(lines[opening+1:ending])
imports,oldns,oldbody=extract(old.read_text());assert oldns==aux
assert hashlib.sha256(oldbody.encode()).hexdigest()==m['old_body_sha256']
assert text.count(oldbody)==1
expected_hashes={'CommonPlaneIntegration':'1aaaa15f2afadc317c741261a7fb57dad2dc2f408c8c41726940c7568919e522','FactorMatchingIntegration':'eb9de3de6915c657561b3e59966d28fae23cbc3e151f3027c87c0b7fd5c318a3','C4Coordinates':'22de414e9c8b8b992ce11a46d8167da4f09d86ddafc71f29e7bbd84317e317fe','PolynomialNonsquareIntegration':'a00e214f4f3390128431db17af70a7211ac730b705d3e92bc193563f8cd95451','IsolatedVertex':'1528a09dae1375675626720952ea9d8a2c7f6b35eeb852830db9e0a07da17344','C4OpenCertificates':'7944028ae577f616c88a4ba2f76717c5812c9a5fc480b73199b519797296401b','TriangleAxis':'f453366b19430a626696520b30cdcbefbd2131b6aa4cc32606fa2c7beeb89a22','C4Case2Endpoints':'719ac5d4b27dd5162d3b30db96f8bdf0dabce727f7be25b41bf36ebcb6126d74','Case3EndpointsIntegration':'2dfae559b3eb4b7445aea3e4d483c5663f6f83ff685cde7111790946ecb4d125'}
assert [c['component'] for c in m['components']]==list(expected_hashes)
chunks=[]
for c in m['components']:
 name=c['component'];path=Path(c['path']);assert sha(path)==c['source_sha256']==expected_hashes[name]
 imps,ns,body=extract(path.read_text());assert hashlib.sha256(body.encode()).hexdigest()==c['body_sha256']
 assert ns==c['old_namespace']
 for imp in imps:
  if imp=='import Mathlib.Basic.Complex.Basic' and 'import Mathlib.Data.Complex.Basic' in imports:continue
  if imp not in imports:imports.append(imp)
 if ns==aux:
  block='section '+name+'\n'+body+'end '+name+'\n';newns=aux
 else:
  block='namespace '+name+'\n'+body+'end '+name+'\n';newns=aux+'.'+name
 assert newns==c['new_namespace'] and text.count(block)==1
 assert ns+'.' not in body or ns==newns
 chunks.append(block)
 print('Exact component body/hash and enclosing scope PASS',name,sha(path))
expected='\n'.join(imports)+'\n\nnamespace '+aux+'\n'+oldbody+'\n'+''.join('\n'+chunk for chunk in chunks)+'\nend '+aux+'\n'
assert text==expected and imports==m['imports'] and len(imports)==len(set(imports))==29
compat=Path('/workspace/pequalnp-proofs/lean/.lake/packages/mathlib/Mathlib/Data/Complex/Basic.lean').read_text();assert 'public import Mathlib.Basic.Complex.Basic' in compat
print('Entire old1528-line body exact; all nine bodies exact; only import union and enclosing section/namespace rebasing changed: PASS')
stack=[];decls={}
for number,line in enumerate(text.splitlines(),1):
 word=line.strip()
 if line.startswith('namespace '):stack.append(('namespace',word[10:]))
 elif line.startswith('section '):stack.append(('section',word[8:]))
 elif line.startswith('end '):
  kind,name=stack.pop();assert name==word[4:]
 else:
  match=re.match(r'(?:(?:noncomputable|private|protected)\s+)*(?:theorem|lemma|def|abbrev)\s+([^\s(:]+)',line)
  if match:
   qualified='.'.join([name for kind,name in stack if kind=='namespace']+[match.group(1)])
   assert qualified not in decls;decls[qualified]=number
assert not stack and len(decls)==269 and decls==json.loads((base/'assembly-v2-declaration-index.json').read_text())
assert 'PEqualNP.Outside.L_gct_231.trace' not in text
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',text)
assert '_root_' not in text and '"' not in text
assert not re.search(r'^\s*(initialize|#|macro|syntax|elab|attribute)\b',text,re.M)
assert all(line.endswith(' in') for line in text.splitlines() if line.startswith('set_option '))
assert not re.search(r'^(?:theorem|lemma)\s+L_gct_231(?:\s|:)',text,re.M)
print('269 fully qualified declarations, no collisions or stale trace namespace, scoped opens/options and allowed source format: PASS')
print('Scope: source-preservation/namespace review only; no new compiler, no assertion of the posted existential theorem. Component proof audits remain separate.')
print('Finish UTC',datetime.now(timezone.utc).isoformat());print('PASS')
