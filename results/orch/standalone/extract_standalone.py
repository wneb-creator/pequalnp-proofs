from pathlib import Path
import re
base=Path('/tmp/oec/pequalnp-pilot-75/global')
repo=Path('/workspace/pequalnp-proofs')
deps=set(re.findall(r'^DEP (\S+)',(base/'dependency-probe3.log').read_text(),re.M))
assert deps, 'no dependencies'
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
for file in [repo/'lean/PEqualNP/Outside/L_meta_3760.lean',repo/'lean/PEqualNP/Outside/L_meta_2448.lean',base/'AtMostOneJunkStarIntegrated2.lean']:
 selected=[];txt=render(parse(file),selected);texts.append(txt)
 print(file.name,'declarations',len(selected),'bytes',len(txt.encode()),'lines',txt.count('\n'))
 (base/(file.stem+'-retained.txt')).write_text('\n'.join(f'{l} {s} {b}' for s,l,b in selected)+'\n')
out='import Mathlib\nimport PEqualNP.Defs\n\n'+'\n'.join(texts)
out=out.replace('PEqualNP.Outside.L_meta_3760','PEqualNP.Outside.L_meta_2448_aux.foundation')
(base/'AtMostOneJunkStandalone2.lean').write_text(out)
print('TOTAL bytes',len(out.encode()),'lines',out.count('\n'))
