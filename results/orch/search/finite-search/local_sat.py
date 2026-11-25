import sys,json,itertools
from pathlib import Path
profile=Path(sys.argv[1]);d=json.loads(profile.read_text());output=Path(sys.argv[2]);n=len(d['preds']);k=d['window_budget'];rows=d['values'];targets=d['targets'];nr=len(rows);c0,c1=d['base_channels'];ch=nr+2
counter=0;clauses=[]
def var():
    global counter
    counter+=1;return counter
def add(*lits):clauses.append(list(lits))
def exactly_one(vs):
    add(*vs)
    for i,a in enumerate(vs):
        for b in vs[:i]:add(-a,-b)
def conj(a,b):
    y=var();add(-y,a);add(-y,b);add(y,-a,-b);return y
def gate_and(y,a,b,cond):
    add(-cond,-y,a);add(-cond,-y,b);add(-cond,y,-a,-b)
def gate_or(y,a,b,cond):
    add(-cond,y,-a);add(-cond,y,-b);add(-cond,-y,a,b)
wire=[]
for i in range(n):
    ws=[var() for _ in range(ch)];wire.append(ws)
    for v,value in zip(ws,[row[i] for row in rows]+[d['dx'][i],d['dy'][i]]):add(v if value else -v)
ops=[];choose=[]
for g in range(k):
    z=var();ops.append(z);sel=[[var() for _ in range(n+g)] for p in range(2)];choose.append(sel)
    for ss in sel:exactly_one(ss)
    for a in range(n+g):
        for b in range(a+1):add(-sel[0][a],-sel[1][b])
    taps=[[var() for _ in range(ch)] for p in range(2)]
    for p in range(2):
        for i,s in enumerate(sel[p]):
            for c in range(ch):add(-s,-taps[p][c],wire[i][c]);add(-s,taps[p][c],-wire[i][c])
    out=[var() for _ in range(ch)];wire.append(out)
    for c in range(nr):gate_and(out[c],taps[0][c],taps[1][c],z);gate_or(out[c],taps[0][c],taps[1][c],-z)
    for dc,bc in [(nr,c0),(nr+1,c1)]:
        a,b=taps[0][dc],taps[1][dc];p=conj(taps[0][bc],b);q=conj(a,taps[1][bc]);gate_or(out[dc],p,q,z);gate_or(out[dc],a,b,-z)
for c,v in enumerate(targets+[0,0]):add(wire[-1][c] if v else -wire[-1][c])
for g in range(k-1):add(*(choose[j][p][n+g] for j in range(g+1,k) for p in range(2)))
if len(sys.argv)>3 and sys.argv[3]=='ordered':
    for g in range(k-1):
        for b in range(n+g):
            for c in range(b):add(-choose[g][1][b],-choose[g+1][1][c])
        for b in range(n+g):
            for a in range(b):
                for c in range(a):add(-choose[g][1][b],-choose[g+1][1][b],-choose[g][0][a],-choose[g+1][0][c])
if 'and_count' in d:
    ac=d['and_count']
    for subset in itertools.combinations(ops,ac+1):add(*(-v for v in subset))
    for subset in itertools.combinations(ops,k-ac+1):add(*subset)
output.write_text('p cnf '+str(counter)+' '+str(len(clauses))+'\n'+'\n'.join(' '.join(map(str,c))+' 0' for c in clauses)+'\n')
Path(str(output)+'.meta.json').write_text(json.dumps({'profile':str(profile),'ops':ops,'choose':choose,'n':n,'k':k},indent=2)+'\n')
print(json.dumps({'n':n,'gates':k,'rows':nr,'variables':counter,'clauses':len(clauses),'cnf':str(output)}))
