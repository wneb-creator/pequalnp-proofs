from pathlib import Path
import json
base=Path('/tmp/oec/pequalnp-pilot-42/sat')
vals=[256463372304,8521482511360,14003410187716736,55389823206179104,155696362464215096,218994303131713984,183565875465424384,229736628136996864,270286071508729856,288160007409369088,192860064594267704,288166778660192704,283797140973809664]
target=1764784;desired=json.loads((base/'rows-14.json').read_text());rows=[]
for pattern,t in desired:
 rows.append(next(r for r in range(58) if sum(((v>>r)&1)<<i for i,v in enumerate(vals))==pattern and ((target>>r)&1)==t))
n=14;width=len(rows);block=57+3*width;clauses=[]
def op(i):return 1+block*i
def sa(i,j):return 2+block*i+j
def sb(i,j):return 30+block*i+j
def av(i,r):return 58+block*i+r
def bv(i,r):return 58+width+block*i+r
def out(i,r):return 58+2*width+block*i+r
def add(*xs):clauses.append(list(xs))
def onehot(xs):
 add(*xs)
 for a,x in enumerate(xs):
  for y in xs[a+1:]:add(-x,-y)
for i in range(n):
 onehot([sa(i,j) for j in range(28)])
 onehot([sb(i,j) for j in range(28)])
 for source in range(28):
  for row,r in enumerate(rows):
   for select,arg in [(sa(i,source),av(i,row)),(sb(i,source),bv(i,row))]:
    if source<13:
     add(-select,arg if vals[source]>>r&1 else -arg)
    elif source>=13+i:
     add(-select,-arg)
    else:
     val=out(source-13,row)
     add(-select,-arg,val);add(-select,arg,-val)
 for row in range(width):
  a=av(i,row);b=bv(i,row);v=out(i,row);o=op(i)
  add(-o,-a,v);add(-o,-b,v);add(-o,a,b,-v)
  add(o,a,-v);add(o,b,-v);add(o,-a,-b,v)
for row,r in enumerate(rows):add(out(n-1,row) if target>>r&1 else -out(n-1,row))
with (base/'complete24.cnf').open('w') as f:
 f.write(f'p cnf {n*block} {len(clauses)}\n')
 for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
(base/'complete24-meta.json').write_text(json.dumps({'inputs':vals,'target':target,'gates':n,'rows':rows,'block':block,'variables':n*block,'clauses':len(clauses),'op_offset':1,'a_offset':2,'b_offset':30,'av_offset':58,'bv_offset':58+width,'output_offset':58+2*width},indent=2))
print('rows',rows,'variables',n*block,'clauses',len(clauses))
