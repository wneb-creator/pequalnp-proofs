from pathlib import Path
import sys

# Positive control, not a lower-bound counterexample: eleven gates for
# OR(0,1) and OR(2,3,4,5), whose ordinary OR target sum is four.
root=Path(__file__).resolve().parent
known=[(1,0,1)]
wire={i:i for i in range(6)}
wire['h']=8
pending=[('neg',2,'h','h')]
for prefix,initial in [('p','h'),('q','neg')]:
    previous=initial
    for v in range(2,6):
        name=f'{prefix}{v}'
        pending.append((name,1,previous,v))
        previous=name
pending += [('out',0,'p5','q5')]
while pending:
    available=[]
    for node in pending:
        name,op,a,b=node
        if a in wire and b in wire:
            x,y=sorted([wire[a],wire[b]])
            available.append(((op,x,y),name,node))
    (op,a,b),name,node=min(available)
    wire[name]=8+len(known)
    known.append((op,a,b))
    pending.remove(node)
assert len(known)==11
sys.argv=['bv_goodsource.py','[[0,1],[2,3,4,5]]','11',str(root/'goodsource_control11'),'10000','one','null','canonical','goodsource']
source=(root/'bv_goodsource.py').read_text()
anchor="lines.append('(check-sat-using qfbv)')"
assert source.count(anchor)==1
fixed="""for j,(control_op,control_a,control_b) in enumerate(known):
    lines.append(f'(assert (and (= op{j} {lit(control_op,2)}) (= a{j} {idx(control_a)}) (= b{j} {idx(control_b)})))')
"""
exec(compile(source.replace(anchor,fixed+anchor),str(root/'bv_goodsource.py'),'exec'))
