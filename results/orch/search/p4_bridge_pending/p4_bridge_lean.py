from pathlib import Path
import argparse,json

root=Path('/tmp/oec/pequalnp-pilot-64');d=json.loads((root/'p4-bridge-trace.json').read_text());expr={int(k):v for k,v in d['expr'].items()}
p=argparse.ArgumentParser();p.add_argument('--count',type=int,default=30);p.add_argument('--split',action='store_true');p.add_argument('--sample',action='store_true');p.add_argument('--output',default='ReductionsBridge.lean');a=p.parse_args()
def field(src):return 'c.'+src[1]+str(src[0])
def lit(n):
    if n==1:return 'true'
    if n==-1:return 'false'
    return ('!' if n<0 else '')+'(v'+str(abs(n))+' c)'
def deps(n):
    if abs(n)==1:return set()
    n=abs(n);e=expr[n];out={n}
    if e[0]=='and':out|=deps(e[1])|deps(e[2])
    return out
def name(n):return 'v'+str(n)
lines=['import Reductions','', 'namespace PEqualNP.Outside.Pilot64Bridge','', 'open PEqualNP.Library.LRAT','open PEqualNP.Outside.Pilot64KernelControl','', 'set_option maxRecDepth 100000','set_option maxHeartbeats 0','', 'structure Candidate where']
for j in range(5):lines += [f'  op{j} : Bool',f'  a{j} : Fin {4+j}',f'  b{j} : Fin {4+j}']
lines += ['', 'def valid (c : Candidate) : Prop :=','  '+' ∧ '.join(f'c.a{j}.val < c.b{j}.val' for j in range(5)),'']
for n in range(2,max(expr)+1):
    e=expr[n];kind=e[0]
    if kind=='freeop':body='c.op'+str(e[1])
    elif kind=='selector':body=f'decide ({field(e[1])}.val = {e[2]})'
    elif kind=='and':body=f'{lit(e[1])} && {lit(e[2])}'
    elif kind=='op':body=f'if {lit(e[1])} then {lit(e[2])} && {lit(e[3])} else {lit(e[2])} || {lit(e[3])}'
    elif kind=='ite':body=f'if {lit(e[1])} then {lit(e[2])} else {lit(e[3])}'
    elif kind=='mux':body='(['+', '.join(lit(v) for v in e[2])+f'] : List Bool).getD {field(e[1])}.val false'
    else:raise ValueError(e)
    lines += [f'def v{n} (c : Candidate) : Bool := {body}']
lines += ['', 'def assignment (c : Candidate) (n : Nat) : Bool :=', '  ([false, true, '+', '.join(f'v{n} c' for n in range(2,max(expr)+1))+'] : List Bool).getD n false','']
for n in range(1,max(expr)+1):lines += [f'theorem assignment_{n} (c : Candidate) : assignment c {n} = {lit(n)} := rfl']
lines += ['', 'def output (c : Candidate) (r : Fin 16) : Bool :=', '  (['+', '.join(lit(n) for n in d['outputs'])+'] : List Bool).getD r.val false','', 'def target (r : Fin 16) : Bool :=','  (r.val.testBit 0 && r.val.testBit 1) || (r.val.testBit 0 && r.val.testBit 2) || (r.val.testBit 1 && r.val.testBit 3)','', 'def derivativeLeft (c : Candidate) : Bool := '+lit(d['left']), 'def derivativeRight (c : Candidate) : Bool := '+lit(d['right']), '']
if a.split:
    (root/'ReductionsIR.lean').write_text('\n'.join(lines+['end PEqualNP.Outside.Pilot64Bridge','']))
    lines=['import ReductionsIR','','namespace PEqualNP.Outside.Pilot64Bridge','','open PEqualNP.Library.LRAT','open PEqualNP.Outside.Pilot64KernelControl','','set_option maxRecDepth 100000','set_option maxHeartbeats 0','']
full=a.count>=len(d['clauses']) and not a.sample;count=min(a.count,len(d['clauses']))
indices=list(range(count))
if a.sample:
    patterns={};extra=[]
    for i,(cl,t) in enumerate(zip(d['clauses'],d['tags'])):
        patterns.setdefault((t[0],tuple(v<0 for v in cl)),i)
        if t[0] in ['output','derivative']:extra.append(i)
    indices=sorted(set(patterns.values())|set(extra));count=len(indices)
lines += [('theorem encodedImpossible' if full else 'example')+' (c : Candidate) (hv : valid c)', '    (hr : ∀ r : Fin 16, output c r = target r)', '    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) : '+('False' if full else 'True')+' := by', '  rcases hv with ⟨h0, h1, h2, h3, h4⟩']
for i in indices:
    cl,t=d['clauses'][i],d['tags'][i]
    base=['ClauseSat','litVal']+['assignment_'+str(n) for n in sorted({abs(v) for v in cl})]
    enc=[2*abs(x)+(x<0) for x in cl];lines += ['  have hc'+str(i)+' : ClauseSat (assignment c) ['+','.join(map(str,enc))+'] := by']
    kind=t[0]
    if kind=='true':lines+=['    simp ['+', '.join(base)+']']
    elif kind in ['and','op','ite']:
        args=t[3:] if kind=='and' else t[2:]
        variables=sorted({abs(n) for n in args if abs(n)>1});cases=[]
        for q,n in enumerate(variables):cases.append(f'cases ha{q} : v{n} c')
        s=base+[name(t[1])]+[f'ha{q}' for q in range(len(variables))]
        lines+=['    '+' <;> '.join(cases+['simp ['+', '.join(s)+']'])]
    elif kind=='mux':
        z,src,index,sel,v=t[1:]
        lines += [f'    by_cases hs : {field(src)}.val = {index}', '    · simp ['+', '.join(base+[name(z),name(sel),'hs'])+']','    · simp ['+', '.join(base+[name(sel),'hs'])+']']
    elif kind=='alo':
        src,ls=t[1:];lines += [f'    have hb := {field(src)}.isLt','    simp ['+', '.join(base+[name(v) for v in ls])+']','    omega']
    elif kind in ['amo','order']:
        vs=t[-2:];unfold=sorted(set().union(*(deps(v) for v in vs)))
        lines += ['    simp ['+', '.join(base+[name(v) for v in unfold])+']','    all_goals omega']
    elif kind=='output':
        mask,want,out=t[1:];lines += [f'    have hh := hr ⟨{mask}, by decide⟩',f'    have ht : target ⟨{mask}, by decide⟩ = '+str(want).lower()+' := by decide','    rw [ht] at hh','    simpa ['+', '.join(base+['output'])+'] using hh']
    elif kind=='derivative':
        side,rootlit=t[1:];lines += ['    simpa ['+', '.join(base+['derivativeLeft' if side=='left' else 'derivativeRight'])+'] using '+('hl' if side=='left' else 'hd')]
    else:raise ValueError(t)
if full:
    lines+=['  apply cnfUnsat','  refine ⟨assignment c, ?_⟩','  simp only [formula, List.forall_mem_cons, List.forall_mem_nil]','  exact ⟨'+', '.join('hc'+str(i) for i in range(count))+', trivial⟩']
else:lines+=['  trivial']
lines+=['','end PEqualNP.Outside.Pilot64Bridge','']
(root/a.output).write_text('\n'.join(lines))
print({'clauses':count,'full':full,'lines':len(lines)})
