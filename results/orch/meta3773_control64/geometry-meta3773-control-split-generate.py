from pathlib import Path
import argparse,resource
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
p=argparse.ArgumentParser(description='Assemble the explicit64-gate positive control from reviewed components.')
p.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args();d=a.directory
c=(d/'Meta3773Control64.template.txt').read_text();w=(d/'Meta3773InputWords.lean').read_text();r=(d/'Meta3773LiteralReplay808.lean').read_text()
def body(s):return '\n'.join(l for l in s.splitlines() if not l.startswith('import ')).strip()+'\n'
new='  refine ⟨controlGates64,(true,0,1),?_,?_,?_,?_⟩\n  · decide +kernel\n  · decide +kernel\n  · decide +kernel\n  · change (controlGates64.foldl (fun (w : List Nat) (g : Bool × Nat × Nat) =>\n      w ++ [if g.1 then w.getD g.2.1 0 ||| w.getD g.2.2 0\n            else w.getD g.2.1 0 &&& w.getD g.2.2 0])\n      (List.ofFn PEqualNP.Outside.L_meta_3773_aux.InputWords.word)).getLastD 0 =\n      (PEqualNP.Outside.L_meta_3773_aux.InputWords.rows.map Prod.fst).foldr Nat.bit 0\n    rw [PEqualNP.Outside.L_meta_3773_aux.InputWords.words_eq,\n      PEqualNP.Outside.L_meta_3773_aux.InputWords.labels_eq]\n    exact PEqualNP.Outside.L_meta_3773_aux.Replay.replay808\n'
needle='  refine ⟨controlGates64,(true,0,1),?_,?_,?_,?_⟩ <;> decide +kernel\n'
assert c.count(needle)==1;c=c.replace(needle,new)
imports='\n'.join(dict.fromkeys(l for s in [c,w,r]for l in s.splitlines()if l.startswith('import ')))+'\n\n'
full=imports+body(w)+'\n'+body(r)+'\n'+body(c)
assert all(l.rstrip()==l for l in full.splitlines())
a.output.write_text(full)
