import json,sys
from pathlib import Path
source=Path(sys.argv[1])
lines=source.read_text().splitlines()
if 'INDEPENDENT_CHECK_ERRORS 0' not in lines:
    raise SystemExit('No verified vector witness in this log')
rows=[]
outputs=None
for line in lines:
    fields=line.split()
    if fields and fields[0]=='OUTPUTS':outputs=list(map(int,fields[1:]))
    elif len(fields)==4 and all(f.isdigit() for f in fields):rows.append(list(map(int,fields)))
limit=int(sys.argv[2]) if len(sys.argv)>2 else 19
assert len(rows)+6<=limit and outputs is not None and len(outputs)==4
input_map=[2,3,8,6,9,7,0]
def wire(i):return input_map[i] if i<7 else i+3
circuit=[]
for i,(out,op,a,b) in enumerate(rows):
    assert out==7+i and 0<=a<out and 0<=b<out
    circuit.append([10+i,op,wire(a),wire(b)])
A,B,C,R=map(wire,outputs)
base=10+len(rows)
circuit.extend([[base,0,1,A],[base+1,0,4,B],[base+2,0,5,C],[base+3,1,base,base+1],[base+4,1,base+2,R],[base+5,1,base+3,base+4]])
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
for x in range(1024):
    values=[bool(x>>i&1) for i in range(10)]
    for out,op,a,b in circuit:
        assert out==len(values)
        values.append(values[a] and values[b] if op==0 else values[a] or values[b] if op==1 else not values[a])
    target=any((x>>a&1) and (x>>b&1) for a,b in edges)
    assert values[-1]==target,(x,values[-1],target)
if limit<=19:assert any(row[1]==2 for row in circuit)
destination=source.parent/f'PETERSEN_WITNESS{len(circuit)}.txt'
destination.write_text(''.join(' '.join(map(str,row))+'\n' for row in circuit))
receipt={'source':source.name,'gates':len(circuit),'not_gates':sum(row[1]==2 for row in circuit),'assignments_checked':1024,'result':'exact Petersen edge function'}
(source.parent/f'PETERSEN_WITNESS{len(circuit)}.json').write_text(json.dumps(receipt,indent=2)+'\n')
if limit<=19:(source.parent/'STOP_SEARCH').write_text('Independently verified19-gate candidate: '+source.name+'\n')
print(json.dumps(receipt))
