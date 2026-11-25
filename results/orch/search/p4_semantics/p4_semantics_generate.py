from pathlib import Path
import json
root=Path('/tmp/oec/pequalnp-pilot-64');d=json.loads((root/'p4-bridge-trace.json').read_text());expr={int(k):v for k,v in d['expr'].items()}
def lit(n):
    if n==1:return 'true'
    if n==-1:return 'false'
    return ('!' if n<0 else '')+'(v'+str(abs(n))+' c)'
def deps(n):
    if abs(n)==1:return set()
    n=abs(n);e=expr[n];out={n}
    if e[0] in ['and','op','ite']:
        for v in e[1:]:out |= deps(v)
    elif e[0]=='mux':
        for v in e[2]:out |= deps(v)
    return out
def op(j,prefix):
    a=f'{prefix}.getD c.a{j}.val false';b=f'{prefix}.getD c.b{j}.val false'
    return f'if c.op{j} then ({a}) && ({b}) else ({a}) || ({b})'
lines=['import ReductionsIR','','namespace PEqualNP.Outside.Pilot64Bridge','','set_option maxRecDepth 100000','set_option maxHeartbeats 0','']
for n in range(4,9):
    for b in ['false','true']:
        lines += [f'@[simp] theorem select_{b}_{n} : ∀ (i : Fin {n}),', '    (['+', '.join([b]*n)+f'] : List Bool).getD i.val false = {b} := by decide']
        lines += [f'@[simp] theorem index_{b}_{n} : ∀ (i : Fin {n}),', '    (['+', '.join([b]*n)+f'] : List Bool)[i.val]'+"'(by exact i.isLt)"+f' = {b} := by decide']
for mask in range(16):
    for i in range(4):lines += [f'@[simp] theorem mask_bit_{mask}_{i} : ({mask} : Nat).testBit {i} = '+str(bool(mask>>i&1)).lower()+' := by decide']
lines += ['', 'def evalCircuit (c : Candidate) (mask : Nat) : List Bool :=','  let w0 := ['+', '.join(f'mask.testBit {i}' for i in range(4))+']']
for j in range(5):lines += [f'  let w{j+1} := w{j} ++ [{op(j,"w"+str(j))}]']
lines += ['  w5','','def derivativeCircuit (c : Candidate) (base seed : Nat) : List Bool :=','  let v0 := ['+', '.join(f'(1 <<< base).testBit {i}' for i in range(4))+']','  let d0 := ['+', '.join(f'decide (seed = {i})' for i in range(4))+']']
for j in range(5):
    av=f'v{j}.getD c.a{j}.val false';bv=f'v{j}.getD c.b{j}.val false';ad=f'd{j}.getD c.a{j}.val false';bd=f'd{j}.getD c.b{j}.val false'
    body=f'if c.op{j} then (({av}) && ({bd})) || (({ad}) && ({bv})) else ({ad}) || ({bd})'
    lines += [f'  let d{j+1} := d{j} ++ [{body}]',f'  let v{j+1} := v{j} ++ [{op(j,"v"+str(j))}]']
lines += ['  d5','','theorem output_eq_evalCircuit (c : Candidate) (r : Fin 16) :','    output c r = (evalCircuit c r.val).getD 8 false := by','  rcases r with ⟨r, hr⟩','  have h : '+' ∨ '.join(f'r = {i}' for i in range(16))+' := by omega','  rcases h with '+' | '.join('rfl' for _ in range(16))]
for mask,out in enumerate(d['outputs']):
    ds=sorted(deps(out));lines += [f'  · change {lit(out)} = (evalCircuit c {mask}).getD 8 false','    simp [evalCircuit, '+', '.join('v'+str(v) for v in ds)+']']
for side,base,seed,rootlit in [('Left',0,1,d['left']),('Right',1,0,d['right'])]:
    ds=sorted(deps(rootlit));lines += ['',f'theorem derivative{side}_eq (c : Candidate) :',f'    derivative{side} c = (derivativeCircuit c {base} {seed}).getD 8 false := by',f'  change {lit(rootlit)} = (derivativeCircuit c {base} {seed}).getD 8 false','  simp [derivativeCircuit, '+', '.join('v'+str(v) for v in ds)+']']
lines += ['','end PEqualNP.Outside.Pilot64Bridge','']
(root/'ReductionsSemantics.lean').write_text('\n'.join(lines))
print({'lines':len(lines),'bytes':sum(len(x)+1 for x in lines)})
