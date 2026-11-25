"""Exact finite row-separation check for a pool of live truth tables."""
import json
from pathlib import Path
N=10
FULL=(1<<(1<<N))-1
INPUTS=tuple(sum(1<<r for r in range(1<<N) if r>>i&1) for i in range(N))
EDGES=((0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5))
TARGET=0
for a,b in EDGES: TARGET|=INPUTS[a]&INPUTS[b]
NEG=tuple(r for r in range(1<<N) if not TARGET>>r&1)
def bad_pair(state,mode=False):
    for n in NEG:
        pos=TARGET
        for a in state:
            if a>>n&1:
                if mode: pos &=a
            else:
                pos &= FULL^a
            if not pos:break
        if pos:return ((pos&-pos).bit_length()-1,n)
    return None
if __name__=='__main__':
    front=json.loads(Path(str(Path(__file__).resolve().parent.parent/'cofactor/frontier-allcofactor-survivors.json')).read_text())
    for i,row in enumerate(front):
        state=tuple(map(int,row['state']))
        print('frontier',i,'mono',bad_pair(state),'signed',bad_pair(state,True))
    for a,b in ((0,1),(0,2)):
        for op in range(4):
            z=[INPUTS[a]&INPUTS[b],INPUTS[a]|INPUTS[b],INPUTS[a]&(FULL^INPUTS[b]),(FULL^INPUTS[a])&INPUTS[b]][op]
            for keep in range(4):
                state=[x for i,x in enumerate(INPUTS) if i not in (a,b) or ((keep&1) and i==a) or ((keep&2) and i==b)]+[z]
                print('first',a,b,op,keep,bad_pair(state,True))
