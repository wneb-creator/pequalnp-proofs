from pathlib import Path
import re

src=Path('/tmp/oec/pequalnp-pilot-85/Lower9811.lean').read_text().splitlines()
helper=Path('/tmp/oec/pequalnp-pilot-85/Dnf9811.lean').read_text()
helper=helper[helper.index('def dnf'):helper.rindex('end PEqualNP.')]
out=[];i=0
while i<len(src):
    l=src[i]
    if l=='import Mathlib.Tactic.ITauto':
        i+=1;continue
    out.append(l)
    if l=='namespace PEqualNP.Outside.L_meta_9811_aux':out.append(helper)
    m=re.match(r'def (f\d+|lowerTarget9811) \(x : Fin 14 → Bool\) : Bool := (.*)',l)
    if m:
        name,expr=m.groups();idx=name[1:] if name.startswith('f') else 'target'
        cs=[re.findall(r'x (\d+)',term) for term in expr.split(' || ')]
        if expr=='false':cs=[]
        lit='['+','.join('['+','.join(c)+']' for c in cs)+']'
        out += [f'def cs{idx} : List (List (Fin 14)) := {lit}',
                f'lemma d{idx} (x : Fin 14 → Bool) : {name} x = dnf cs{idx} x := by',
                f'  simp [{name}, cs{idx}, dnf]',
                '  <;> ac_rfl']
    m=re.match(r'(\s*)have he : .*=> f(\d+) \(Function.update .*\)\) = f(\d+) := by',l)
    if m:
        ind,a,b=m.groups()
        out += [ind+'  funext x',ind+f'  rw [d{a}, d{b}, dnf_pin_relabel]',
                ind+'  exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x']
        while '<;> itauto' not in src[i]:i+=1
    if re.match(r'\s*have he : .*lowerTarget9811 .* = f\d+ := by',l):
        ind=l[:len(l)-len(l.lstrip())]
        b=re.search(r'= f(\d+) := by',l)[1]
        out += [ind+'  funext x',ind+f'  rw [dtarget, d{b}, dnf_relabel]',
                ind+'  exact dnf_eq_of_subsumption _ _ (by decide +kernel) (by decide +kernel) x']
        while '<;> itauto' not in src[i]:i+=1
    i+=1
dest=Path('/tmp/oec/pequalnp-pilot-85/Lower9811Light.lean')
dest.write_text('\n'.join(out)+'\n')
print(dest,len(out),dest.stat().st_size)
assert '<;> itauto' not in dest.read_text()
