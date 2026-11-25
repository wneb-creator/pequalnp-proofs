import re
from pathlib import Path

ROOT=Path('/workspace/pequalnp-proofs')
IDS=[2444,4338,1673,1674,5120,1676,1677,1678]
PARENT='PEqualNP.Outside.L_meta_670'
IMPORTS=['Mathlib.Data.Finset.Card','Mathlib.Data.Finset.Image',
         'Mathlib.Data.Set.Image','Mathlib.Data.Nat.Bitwise',
         'Mathlib.Data.List.Sublists','Mathlib.Tactic.IntervalCases',
         'Mathlib.Tactic.Tauto','Mathlib.Tactic.FinCases',
         'Mathlib.Algebra.BigOperators.Intervals','PEqualNP.Defs']
out=['\n'.join('import '+x for x in IMPORTS)+'\n\nnamespace '+PARENT+'\n']
for number in IDS:
    src=ROOT/f'lean/PEqualNP/Outside/L_meta_{number}.lean'
    old=f'PEqualNP.Outside.L_meta_{number}'
    short=f'C{number}'
    new=PARENT+'.'+short
    text=src.read_text()
    lines=[]
    for line in text.splitlines():
        if line.startswith('import '):continue
        if line.startswith('theorem '+old+' :'):
            line=line.replace('theorem '+old+' :','lemma '+short+'.outcome :',1)
        elif line.startswith('theorem '+old+'\n'):
            line=line.replace('theorem '+old,'lemma '+short+'.outcome',1)
        elif line=='theorem '+old or line.startswith('theorem '+old+' :'):
            line=line.replace('theorem '+old,'lemma '+short+'.outcome',1)
        line=line.replace(old,new)
        if line.startswith('namespace '+new):
            line=line.replace('namespace '+new,'namespace '+short,1)
        elif line.startswith('end '+new):
            line=line.replace('end '+new,'end '+short,1)
        lines.append(line)
    out.append('section Source'+str(number)+'\n\n'+'\n'.join(lines)+'\n\nend Source'+str(number)+'\n')
for name in ['NormalizationFull.lean','Prepend.lean']:
    src=ROOT/'results/orch/lemmas'/name
    text=src.read_text()
    lines=[]
    for line in text.splitlines():
        if line.startswith('import '):continue
        if line.startswith('namespace '+PARENT+'.'):
            line=line.replace('namespace '+PARENT+'.','namespace ',1)
        elif line.startswith('end '+PARENT+'.'):
            line=line.replace('end '+PARENT+'.','end ',1)
        lines.append(line)
    out.append('\n'.join(lines)+'\n')
out.append('end '+PARENT+'\n')
footer=Path('/tmp/oec/pequalnp-pilot-61/assembly-footer.txt')
if footer.exists():out.append(footer.read_text())
destination=ROOT/'results/orch/lemmas/FullRaw.lean'
destination.write_text('\n'.join(out))
print(destination, destination.stat().st_size, 'bytes')
