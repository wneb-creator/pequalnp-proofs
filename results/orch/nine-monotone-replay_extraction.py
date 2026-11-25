from pathlib import Path
import json,re,hashlib
here=Path(__file__).resolve().parent
repo=here.parents[1]
src=(repo/'lean/PEqualNP/Outside/L_meta_670.lean').read_text()
old=(here/'lemmas/NineSignedReach.lean').read_text()
s=src[src.index('abbrev Sig'):src.index('end PEqualNP.Outside.L_meta_670')]
a=old.index('lemma nine_reach_lower');b=old.index('\n\nend PEqualNP.Outside.L_meta_2373.NineSigned',a)
suffix=old[a:b].replace('nine_reach_lower','nine_monotone_reach_lower').replace('Lower true inputs graph 15','Lower false inputs graph 16').replace('signedRoot','monoRoot')
s+='\n'+suffix+'\n'
pat=re.compile(r'^(?:(?:private|noncomputable|protected)\s+)*(?:abbrev|def|lemma|theorem|structure|inductive)\s+([\w\'.]+)',re.M)
ms=list(pat.finditer(s));blocks=[]
for i,m in enumerate(ms):
 a=m.start()
 while a>0:
  prev=s.rfind('\n',0,a-1)+1;line=s[prev:a].strip()
  if line.startswith('set_option ')or line.startswith('@['):a=prev
  else:break
 b=ms[i+1].start()if i+1<len(ms)else len(s)
 while b>a:
  prev=s.rfind('\n',a,b-1)+1;line=s[prev:b].strip()
  if line.startswith('set_option ')or line.startswith('@[')or not line:b=prev
  else:break
 blocks.append((m.group(1),s[a:b]+'\n'))
chosen=json.loads((here/'nine-monotone-extraction-map.json').read_text())['new_decls']
assert [n for n,b in blocks if n in chosen]==chosen
out='import PetersenSeventeenFull\n\nnamespace PEqualNP.Outside.L_meta_2373.NineSigned\nopen PEqualNP.CircuitLowerBounds\n\n'+'\n'.join(b for n,b in blocks if n in chosen)+'\nend PEqualNP.Outside.L_meta_2373.NineSigned\n'
out=out.replace('PEqualNP.Outside.L_meta_670','PEqualNP.Outside.L_meta_2373.NineSigned')
assert out==(here/'lemmas/NineMonotoneExtension.lean').read_text()
print('Exact extraction replay PASS',hashlib.sha256(out.encode()).hexdigest(),len(chosen))
