import sys,json
from pathlib import Path
d=json.loads(Path(sys.argv[1]).read_text());nstars=int(sys.argv[2]);n=len(d['preds']);k=d['window_budget'];nr=len(d['values']);c0,c1=d['base_channels']
assert nr<=64
values=[sum(row[i]<<r for r,row in enumerate(d['values'])) for i in range(n)];target=sum(v<<r for r,v in enumerate(d['targets']))
seed=[]
def gate(op,a,b):
    seed.append((op,a,b));return n+len(seed)-1
hs=[gate(1,1+i,1+nstars+i) for i in range(nstars)]
f=0
for h in hs:f=gate(0,f,h)
a=f
for j in range(1,4):a=gate(0,a,1+2*nstars+j)
b=gate(0,f,2*nstars+5);gate(1,a,b)
assert len(seed)==k
lines=[f'{n} {k} {nr} {c0} {c1} {target}']+[f'{v} {dx} {dy}' for v,dx,dy in zip(values,d['dx'],d['dy'])]+[' '.join(map(str,g)) for g in seed]
Path(sys.argv[3]).write_text('\n'.join(lines)+'\n')
print('prepared',sys.argv[3],'preds',n,'rows',nr,'gates',k)
