from pathlib import Path
import json
j=Path('/tmp/oec/pequalnp-pilot-79');D={0,1,3,9};p=2;chosen=[l for l in range(13)if(p+l)%13 in D];q=chosen[0];g=[]
def add(op,a,b):
 w=26+len(g);g.append([op,a,b]);return w
def OR(wires):
 u=wires[0]
 for v in wires[1:]:u=add(1,u,v)
 return u
N=[]
for l in range(13):N.append(OR([x for x in range(13)if(x+l)%13 in D and not(x==p and l in chosen)]))
U=OR([13+l for l in chosen if l!=q]);a=add(1,p,13+q);b=add(1,p,N[q]);c=add(1,13+q,U);bad=add(0,a,b);paired=add(0,bad,c)
outputs=[paired]+[add(0,13+l,N[l])for l in range(13)if l!=q];out=OR(outputs)
assert len(g)==66 and out==91 and g[0]==[1,0,1]
d={'source':'exact mixed-orientation edge-CNF seed','input_count':26,'active':66,'output':out,'gates':g,'bad_gate':bad-26}
(j/'meta3773-mixed66-seed.json').write_text(json.dumps(d,indent=2)+'\n')
(j/'meta3773-warm-mixed66.txt').write_text(str(len(g))+'\n'+'\n'.join(' '.join(map(str,x))for x in g)+'\n')
print(json.dumps({'gates':len(g),'bad_gate':bad-26,'point':p,'assigned_lines':chosen,'paired_line':q}))
