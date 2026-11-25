from pathlib import Path
import json
BASE=Path(__file__).resolve().parent
EDGES=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def read(name):
    rows=(BASE/name).read_text().splitlines()
    gates=[tuple(map(int,r.split())) for r in rows if r and r.split()[0].isdigit()]
    outs=[int(v) for r in rows if r.lower().startswith('outputs') for v in r.split()[1:]]
    return gates,outs

def eval_gates(bits,gates,signed=False):
    w=list(bits)
    for out,op,a,b in gates:
        assert out==len(w) and a<out and b<out
        if signed:
            u=(not w[a]) if op&2 else w[a]
            v=(not w[b]) if op&4 else w[b]
            w.append((u or v) if op&1 else (u and v))
        else:
            w.append((w[a] and w[b]) if op==0 else (w[a] or w[b]) if op==1 else not w[a])
    return w

report={}
for name,signed in [('exact20.txt',False),('best951.txt',False),('best952.txt',False),('best953.txt',False),('signed18-best956.txt',True),('signed17-best957.txt',True)]:
    gates,_=read(name);wrong=[]
    for x in range(1024):
        bits=[bool(x>>i&1) for i in range(10)]
        result=eval_gates(bits,gates,signed)[-1]
        if result!=any(bits[a] and bits[b] for a,b in EDGES):wrong.append(x)
    report[name]={'gates':len(gates),'errors':wrong,'count':len(wrong)}
assert report['exact20.txt']['count']==0
for name in ['orbit2-best958.txt','orbit2-best959.txt','orbit2-best960.txt']:
    if not (BASE/name).exists():continue
    gates,outs=read(name);wrong=[]
    for x in range(1024):
        bits=[bool(x>>i&1) for i in range(10)]
        w=eval_gates([bits[i] for i in [2,3,8,6,9,7,0]],gates)
        result=(bits[1] and w[outs[0]]) or (bits[4] and w[outs[1]]) or (bits[5] and w[outs[2]]) or w[outs[3]]
        if result!=any(bits[a] and bits[b] for a,b in EDGES):wrong.append(x)
    report[name]={'vector_gates':len(gates),'composed_gates':len(gates)+6,'errors':wrong,'count':len(wrong)}
gates,_=read('cycle-bank-best.txt');wrong=[]
for x in range(64):
    bits=[bool(x>>i&1) for i in range(6)]
    bank=bits+[bits[i] or bits[i+3] for i in range(3)]
    result=eval_gates(bank,gates,True)[-1]
    if result!=any(bits[i] and bits[(i+1)%6] for i in range(6)):wrong.append(x)
report['cycle-bank-best.txt']={'additional_signed_gates':len(gates),'errors':wrong,'count':len(wrong)}
print(json.dumps(report,indent=2))
assert all(v['count']>0 for k,v in report.items() if k!='exact20.txt')
