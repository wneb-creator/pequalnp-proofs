import argparse
import json
import pathlib
import re
from collections import defaultdict

ap=argparse.ArgumentParser()
ap.add_argument('source',type=pathlib.Path)
ap.add_argument('output',type=pathlib.Path)
ap.add_argument('--helpers',type=pathlib.Path,required=True)
ap.add_argument('--report',type=pathlib.Path,required=True)
a=ap.parse_args()
s=a.source.read_text()
cmd=re.compile(r'^(?:import\b|namespace\b|end\b|(?:noncomputable\s+)?section\b|open\b|variable\b|set_option\b|(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive)\b)',re.M)
starts=[m.start() for m in cmd.finditer(s)]+[len(s)]
units=[];ns=[];stack=[]
for b,e in zip(starts,starts[1:]):
 block=s[b:e];line=block.splitlines()[0]
 units.append({'text':block,'namespace':tuple(ns)})
 if line.startswith('namespace '):
  stack.append(len(ns));ns.extend(line[len('namespace '):].strip().split('.'))
 elif line.startswith('section') or line.startswith('noncomputable section'):stack.append(len(ns))
 elif line.startswith('end') and stack:del ns[stack.pop():]
block_re=re.compile(r'^(?:theorem|lemma)\s+(\w+)\s*:\s*block\s+(\w+)\s+(\d+)\s+(\d+)\s+(\d+)\s*=\s*true')
cell_re=re.compile(r'apply\s+cellsBlock\s+\(ar\s*:=\s*(\d+)\)\s+\(rows\s*:=\s*(\d+)\)\s+\(d\s*:=\s*(\d+)\)')
table_re=re.compile(r'^(?:theorem|lemma)\s+(\w+)\s*:\s*checkedTables\s+(\w+)\s+(\d+)\s*:=')
blocks=defaultdict(list);tables={};keys={};symbolic=set()
for i,u in enumerate(units):
 broad=re.match(r'^(?:theorem|lemma)\s+\w+\s*:\s*block\s+(\w+)\s+\d+\s+\d+\s+(.+?)\s*=\s*true',u['text'])
 if broad and not re.fullmatch(r'\d+',broad.group(2).strip()):symbolic.add((u['namespace'],broad.group(1)))
 m=block_re.match(u['text'])
 if m:
  name,g,k,start,n=m.groups();key=(u['namespace'],g);keys[i]=key
  cell=cell_re.search(u['text'])
  if cell:blocks[key].append((int(k),int(start),int(n),*map(int,cell.groups())))
 m=table_re.match(u['text'])
 if m:
  name,g,top=m.groups();tables[(u['namespace'],g)]=(i,name,int(top))
eligible={};rejected=[]
for key,(idx,name,top) in tables.items():
 rows=blocks[key]
 if not rows:continue
 if key in symbolic:rejected.append((key[1],'symbolic counts'));continue
 by_k=defaultdict(list)
 for row in rows:by_k[row[0]].append(row)
 okay=True
 for k,rr in by_k.items():
  rr.sort(key=lambda t:t[1]);pos=0
  for _,start,n,*_ in rr:
   if start!=pos:okay=False
   pos=start+n
 if not okay:rejected.append((key[1],'noncontiguous'));continue
 eligible[key]=(idx,name,top,by_k)
wrapper='lemma pilotTablesBatched (g : Forest)\n    (chunks : Nat → List (Nat × Nat × Nat × Nat)) (top : Nat)\n    (h : ∀ k ≤ top, FiniteChunk.chunkSize (chunks k) = (g.levels k).1 ∧\n      FiniteChunk.proofChunks (fun (start n : Nat) (w : Nat × Nat × Nat) =>\n        cells g k start n w.1 w.2.1 w.2.2) 0 (chunks k)) : checkedTables g top := by\n  exact FiniteChunk.proofLevels_sound\n    (fun k start n => block g k start n = true) (fun k => (g.levels k).1)\n    (fun (k start n : Nat) (w : Nat × Nat × Nat) => cells g k start n w.1 w.2.1 w.2.2)\n    (fun _ _ => rfl) (fun k start x y => @block_merge g k start x y)\n    (fun k start n w => @cellsBlock g k start n w.1 w.2.1 w.2.2) chunks top h\n\n'
seen_ns=set();out=[s[:starts[0]]];pending=[];stats=[];removed=0
for i,u in enumerate(units):
 text=u['text'];line=text.splitlines()[0]
 if line.startswith('set_option '):pending.append(text);continue
 key=keys.get(i)
 if key in eligible:
  pending=[];removed+=1;continue
 m=table_re.match(text)
 if m:
  name,g,top=m.groups();key=(u['namespace'],g)
  if key in eligible:
   _,_,top,by_k=eligible[key]
   if u['namespace'] not in seen_ns:
    out.append(wrapper);seen_ns.add(u['namespace'])
   dat='pilotData_'+name
   ds='def '+dat+' : Nat → List (Nat × Nat × Nat × Nat)\n'
   for k,rr in sorted(by_k.items()):
    ds+='  | '+str(k)+' => ['+', '.join('('+','.join(map(str,(n,ar,rows,d)))+')' for _,start,n,ar,rows,d in rr)+']\n'
   ds+='  | _ => []\n\n'
   proof='theorem '+name+' : checkedTables '+g+' '+str(top)+' := by\n'
   proof+='  apply pilotTablesBatched '+g+' '+dat+' '+str(top)+'\n'
   proof+='  intro k hk\n  interval_cases k\n  all_goals refine ⟨by decide +kernel, ?_⟩\n'
   proof+='  all_goals simp only ['+dat+', FiniteChunk.proofChunks, cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd, and_true]\n'
   proof+="  all_goals repeat' apply And.intro\n  all_goals decide +kernel\n\n"
   out.append(ds);out.extend(pending);pending=[];out.append(proof)
   stats.append({'namespace':'.'.join(u['namespace']),'forest':g,'levels':len(by_k),'chunks':sum(map(len,by_k.values()))})
   continue
 out.extend(pending);pending=[];out.append(text)
out.extend(pending)
result=''.join(out)
helpers=a.helpers.read_text(); helpers='\n'.join(l for l in helpers.splitlines() if not l.startswith('import '))+'\n'
# Helpers are inserted after the complete leading import group.
match=re.match(r'(?:import [^\n]+\n)+',result)
assert match
result=result[:match.end()]+'\n'+helpers+result[match.end():]
a.output.write_text(result)
report={'source':str(a.source),'output':str(a.output),'before_bytes':len(s.encode()),'after_bytes':len(result.encode()),'removed_block_declarations':removed,'forests':stats,'rejected':rejected}
a.report.write_text(json.dumps(report,indent=2))
print(json.dumps({k:v for k,v in report.items() if k not in ('forests','rejected')}));print('forests',len(stats))
