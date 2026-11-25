from pathlib import Path
import re,hashlib
b=Path(__file__).resolve().parent.parent/'library'
old=(b/'FullStar31Lean.lean').read_text();new=(b/'FullStar31Individual.lean').read_text()
assert hashlib.sha256(old.encode()).hexdigest()=='4e3efa0b397320b678920ea30e5c1228261ee1d043e99e6134e2d8be60a9e6a3'
cut=old.index('set_option maxHeartbeats 4000000 in\ntheorem full_star_primitive_equations')
expected=old[:cut]+'end PEqualNP.Outside.L_gct_231_aux\n'
assert new==expected
assert len(new.splitlines())==916 and len(new.encode())==73248
assert len(re.findall(r'^theorem certEq\d{3} ',new,re.M))==31
assert 'full_star_primitive_equations' not in new
print('PASS byte-exact reviewed prefix; all31 individual coefficient helpers unchanged; only final conjunction removed and namespace closed')
print(hashlib.sha256(new.encode()).hexdigest())
