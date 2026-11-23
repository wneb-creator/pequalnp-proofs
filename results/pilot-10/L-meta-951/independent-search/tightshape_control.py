from pathlib import Path
import sys

# Positive control: eleven gates compute OR(0,1,2,3) and OR(3,4).
# This is far above their target sum four, so it is not a counterexample.
root=Path(__file__).resolve().parent
family='[[0,1,2,3],[3,4]]'
known=[(2,4,4)]
wire={i:i for i in range(5)}
wire['neg']=7
pending=[]
for prefix,initial in [('p',4),('q','neg')]:
    previous=initial
    for v in range(4):
        name=f'{prefix}{v}'
        pending.append((name,1,previous,v))
        previous=name
pending += [('pair',1,3,4),('out',0,'p3','q3')]
while pending:
    available=[]
    for node in pending:
        name,op,a,b=node
        if a in wire and b in wire:
            x,y=sorted([wire[a],wire[b]])
            available.append(((op,x,y),name,node))
    (op,a,b),name,node=min(available)
    wire[name]=7+len(known)
    known.append((op,a,b))
    pending.remove(node)
assert len(known)==11
sys.argv=['bv_tightshape.py',family,'11',str(root/'tightshape_control11'),'10000','one','null','canonical','tightshape']
source=(root/'bv_tightshape.py').read_text()
anchor="lines.append('(check-sat-using qfbv)')"
assert source.count(anchor)==1
fixed="""for j,(control_op,control_a,control_b) in enumerate(known):
    lines.append(f'(assert (and (= op{j} {lit(control_op,2)}) (= a{j} {idx(control_a)}) (= b{j} {idx(control_b)})))')
"""
exec(compile(source.replace(anchor,fixed+anchor),str(root/'bv_tightshape.py'),'exec'))
