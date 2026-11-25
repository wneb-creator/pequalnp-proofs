from pathlib import Path
import sys,json
source=Path(sys.argv[1]);lines=source.read_text().splitlines()
assert 'WITNESS' in lines
rows=[];opmap={'AND':0,'OR':1,'NOT':2}
for line in lines:
    f=line.split()
    if len(f)==4 and f[0].isdigit() and f[1] in opmap:rows.append([int(f[0]),opmap[f[1]],int(f[2]),int(f[3])])
assert len(rows)==19 and any(r[1]==2 for r in rows)
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
for x in range(1024):
    values=[bool(x>>i&1)for i in range(10)]
    for out,op,a,b in rows:
        assert out==len(values) and 0<=a<out and 0<=b<out
        values.append(values[a]and values[b]if op==0 else values[a]or values[b]if op==1 else not values[a])
    assert values[-1]==any((x>>a&1)and(x>>b&1)for a,b in edges)
(source.parent/'PETERSEN_WITNESS19.txt').write_text(''.join(' '.join(map(str,row))+'\n'for row in rows))
receipt={'source':source.name,'gates':19,'not_gates':sum(row[1]==2 for row in rows),'assignments_checked':1024,'result':'exact Petersen edge function'}
(source.parent/'PETERSEN_WITNESS19.json').write_text(json.dumps(receipt,indent=2)+'\n')
(source.parent/'STOP_SEARCH').write_text('Independently verified19-gate candidate: '+source.name+'\n')
print(json.dumps(receipt))
