from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re
base=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();hs=lambda s:hashlib.sha256(s.encode()).hexdigest()
print('Start UTC',datetime.now(timezone.utc).isoformat(),flush=True)
m=json.loads((base/'assembly-v7fallback-manifest.json').read_text());p=base/'L_gct_231_FinalFallbackV7.lean';text=p.read_text();aux='PEqualNP.Outside.L_gct_231_aux'
assert sha(p)==m['candidate_sha256']=='f5508fba3b3c32933c3cfa55aa9b37a944c8b76b3ad031143e5ecae9bb5e30e2'
assert len(text.encode())==504298<512*1024 and len(text.splitlines())==3133
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
assert outer==[(35,aux)] and len(blocks)==1 and outside==m['imports'] and len(outside)==33 and all(l.startswith('import ') for l in outside)
assert len(decls)==326 and decls==json.loads((base/'assembly-v7fallback-declaration-index.json').read_text())
old=Path(m['base']);assert sha(old)==m['base_sha256']=='d2a724e6eb3c78592987233a86919f6d41e2acdcdee49b7b4c862c92b770026a';ot,oi,od,ob=scan(old.read_text());assert len(ob)==1 and ob[0][0]==aux;oldbody=ob[0][1]
assert hs(oldbody)==m['base_inner_body_sha256'] and text.count(oldbody)==1
assert set(outside)-set(oi)=={'import Mathlib.Algebra.Field.ZMod'} and [l for l in outside if l in oi]==oi
chunks=[]
for c in m['components']:
 path=Path(c['source']);assert sha(path)==c['source_sha256'];st,si,sd,sb=scan(path.read_text())
 if c['label']=='CompactStar':
  ns,body=sb[c['source_block']];assert ns==aux+'.StarPencil';chunk='namespace StarPencil\n'+body+'end StarPencil\n'
 else:
  assert len(sb)==1 and sb[0][0]==aux
  body=sb[0][1];start=body.index('set_option maxHeartbeats 800000 in\ntheorem no_common_complex_zero_of_modular_coprime');excluded=body[:start].strip();assert oldbody.count(excluded)==1
  body=body[start:];assert body.count('theorem ')==1;chunk='section ModularTransferIntegration\n'+body+'end ModularTransferIntegration\n'
 assert hs(body)==c['inner_body_sha256'] and len(body.encode())==c['inner_body_bytes'] and text.count(body)==1 and text.count(chunk)==1
 chunks.append(chunk);print('Exact component innerbody',c['label'],c['inner_body_sha256'],flush=True)
expected='\n'.join(outside)+'\n\nnamespace '+aux+'\n'+oldbody+'\n'+'\n'.join(chunks)+'\nend '+aux+'\n';assert text==expected
assert set(od)<=set(decls) and set(decls)-set(od)=={aux+'.StarPencil.r_eq_zero_of_coefficients',aux+'.StarPencil.coefficients_force_standard_star',aux+'.StarPencil.standard_star_triangle_extension_impossible',aux+'.no_common_complex_zero_of_modular_coprime'}
assert len([n for n in decls if n.endswith('.resultant_zero_of_common_root')])==1
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',text) and '_root_' not in text and '"' not in text
assert not re.search(r'^\s*(initialize|#|macro|syntax|notation|elab|attribute|instance|inductive|structure)\b',text,re.M)
assert all(re.fullmatch(r'set_option (maxRecDepth|maxHeartbeats|synthInstance.maxSize|synthInstance.maxHeartbeats) [0-9]+ in',l) for l in text.splitlines() if l.startswith('set_option '))
assert 'import' not in text[text.index('namespace '):]
print('Entire checked3039innerbody exact; only3star lemmas+1transfer theorem added, existing common-root helper byte-identical/reused once;326declarations/no collisions: PASS',flush=True)
print('Exactly1outeraux namespace, only33imports outside, onlyZMod import added,504298bytes<512KiB, allowed scoped options/plain-file scan: PASS',flush=True)
print('Scope: preservation fallback only; no main theorem or raw-to-normalized bridge. No compiler/named-file edit.',flush=True)
print('Finish UTC',datetime.now(timezone.utc).isoformat(),flush=True);print('PASS',flush=True)
