from pathlib import Path
import re
p=Path('/tmp/oec/pequalnp-pilot-182')
s=(p/'Engine.lean').read_text()
lines=s.splitlines()
start=re.compile(r'^(?:noncomputable )?(?:def|abbrev|structure|inductive) ([\w\'.]+)')
boundary=re.compile(r'^(?:noncomputable )?(?:def|abbrev|structure|inductive|lemma|theorem|section|end|set_option|namespace|open|variable|include|omit)\b')
blocks={}
order=[]
for i,line in enumerate(lines):
 m=start.match(line)
 if m:
  j=i+1
  while j<len(lines) and not boundary.match(lines[j]):j+=1
  name=m[1]
  blocks[name]='\n'.join(lines[i:j]).rstrip()
  order.append(name)
needed=set(['okS','okE','okP','pr','FF'])
while True:
 old=set(needed)
 for name in old:
  block=blocks[name]
  for token in re.findall(r'[A-Za-z_][\w\']*(?:\.[A-Za-z_][\w\']*)*',block):
   if token in blocks:needed.add(token)
 if old==needed:break
out='import Std\n\nnamespace Engine\n\n'
for n in order:
 if n in needed:
  out+=blocks[n].replace('noncomputable def ','def ').replace('ℕ','Nat')+'\n\n'
out+='end Engine\n'
(p/'NativeEngine.lean').write_text(out)
print('Selected',len(needed),'definitions;',len(out.splitlines()),'lines')
print('Names',','.join(n for n in order if n in needed))
