from pathlib import Path
import hashlib,json,re
p=Path('/workspace/pequalnp-proofs/results/orch/lemmas/GuardGeometry.lean');s=p.read_text()
backup=Path('/tmp/oec/pequalnp-pilot-62/GuardGeometry-before-split.lean');assert not backup.exists();backup.write_text(s)
items=[
 ('residual_pair_card','a b','a ≠ b → a ∉ pencil {p} → b ∉ pencil {p} →\n    (residual {p} {{a, b}}).card = 5'),
 ('residual_singleton_ray_card','a q','a ∉ pencil {p} → q ≠ {p} →\n    ((residual {p} {{a}}).filter (sameRay {p} q)).card = 2'),
 ('capFor_spec','q r','q ≠ {p} → r ≠ {p} → ¬sameRay {p} q r →\n    IsFourCap (capFor {p} q r) ∧ avoidingPoints (capFor {p} q r) = {{{p}, q, r}}')]
for name,binders,body in items:
 pat=r'(?:set_option[^\n]*\n)+lemma '+name+r' :[\s\S]*?  decide \+kernel\n'
 m=re.search(pat,s);assert m is not None,name
 original=m.group();header=original[:original.index('lemma ')]
 helpers=[]
 for i in range(13):
  helpers.append(header+f'lemma {name}_{i} : ∀ {binders} : Fin 13,\n    '+body.format(p=i)+' := by\n  decide +kernel\n\n')
 proof='fun i => Fin.elim0 i'
 for i in reversed(range(13)):proof=f'Fin.cases {name}_{i} ({proof})'
 aggregate=original[:original.index(' := by')+len(' := by')]+f'\n  exact ({proof})\n'
 s=s[:m.start()]+''.join(helpers)+aggregate+s[m.end():]
p.write_text(s)
print(json.dumps({'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'lines':len(s.splitlines())}))
