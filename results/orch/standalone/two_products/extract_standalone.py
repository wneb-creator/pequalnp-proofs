from pathlib import Path
import re
import hashlib
base=Path('/tmp/oec/pequalnp-pilot-75/global/two_products')
repo=Path('/workspace/pequalnp-proofs')
deps=set(re.findall(r'^DEP (\S+)',(base/'dependency-probe.log').read_text(),re.M))
assert deps, 'no dependencies'
assert hashlib.sha256((repo/'results/orch/standalone/AtMostOneJunkStandalone.lean').read_bytes()).hexdigest() == '72c333a765a480d06fbae71d6afa211f788c15109a7f201eae70da7a1f798890'
extra=base/'extra-dependencies.txt'
if extra.exists():deps.update(extra.read_text().splitlines())

def parse(file):
 lines=file.read_text().splitlines(True)
 starts=[i for i,s in enumerate(lines) if re.match(r'^(?:import|namespace|end|open|set_option|(?:noncomputable )?(?:private )?(?:def|lemma|theorem|abbrev))\b',s)]
 starts.append(len(lines)); root=[]; stk=[(root,'')]; pending=[]
 for a,b in zip(starts,starts[1:]):
  text=''.join(lines[a:b]); first=lines[a].strip()
  if first.startswith('import '):continue
  if first.startswith('namespace '):
   short=first.split()[1]; full=(stk[-1][1]+'.' if stk[-1][1] else '')+short
   node={'type':'namespace','start':text,'name':full,'children':[],'end':''};stk[-1][0].append(node);stk.append((node['children'],full));continue
  if first.startswith('end '):
   if len(stk)>1:stk.pop();stk[-1][0][-1]['end']=text
   continue
  if first.startswith('set_option ') or (first.startswith('open ') and first.endswith(' in')):
   pending.append(text);continue
  dec=re.match(r'^(?:noncomputable )?(?:private )?(?:def|lemma|theorem|abbrev) (\S+)',first)
  if dec:
   name=(stk[-1][1]+'.' if stk[-1][1] else '')+dec[1]
   stk[-1][0].append({'type':'decl','name':name,'text':''.join(pending)+text,'line':a+1});pending=[]
  else:
   stk[-1][0].append({'type':'context','text':text})
 assert len(stk)==1
 return root

def keep(n):return n in deps or any(x.startswith(n+'._') or x.startswith(n+'.match_') for x in deps)
def active(nodes):return any(n['type']=='decl' and keep(n['name']) or n['type']=='namespace' and active(n['children']) for n in nodes)
def render(nodes,selected):
 out=''
 for n in nodes:
  if n['type']=='decl' and keep(n['name']):out+=n['text'];selected.append((n['name'],n['line'],len(n['text'].encode())))
  elif n['type']=='context':out+=n['text']
  elif n['type']=='namespace' and active(n['children']):out+=n['start']+render(n['children'],selected)+n['end']
 return out
texts=[]
for file in [repo/'results/orch/standalone/AtMostOneJunkStandalone.lean',Path('/tmp/oec/pequalnp-pilot-75/library/TwoSilentProductsGraphOnly.lean')]:
 selected=[];txt=render(parse(file),selected);texts.append(txt)
 print(file.name,'declarations',len(selected),'bytes',len(txt.encode()),'lines',txt.count('\n'))
 (base/(file.stem+'-retained.txt')).write_text('\n'.join(f'{l} {s} {b}' for s,l,b in selected)+'\n')
out='import Mathlib\nimport PEqualNP.Defs\n\n'+'\n'.join(texts)
out=out.replace('PEqualNP.Outside.L_meta_3760','PEqualNP.Outside.L_meta_2448_aux.foundation')
old_open = """open M1528.P1.S98 (W AO Least Bel aliasWire aliasGate eraseC erase_length erase_AO
  erase_wires erase_W_lt erase_gateAt_lt erase_gateAt_ge W_gate W_input W_or W_and
  gateAt_eq AO_of_IsAO2 IsAO2_of_AO prefix_W)
open M1528.P2 (OrStep OrR Leaf orStep_lt orR_le orStep_mono orR_mono orR_leaf_true orR_leaf
  orR_cone pairInput_true graphFun_pair orReaches_orR orR_orReaches mem_orIn opnd_eq nfc)
"""
assert out.count(old_open) == 1
out = out.replace(old_open, 'open M1528.P1.S98 (W AO W_gate W_input W_or W_and gateAt_eq prefix_W)\n')
(base/'TwoProductsStandalone2.lean').write_text(out)
print('TOTAL bytes',len(out.encode()),'lines',out.count('\n'))
