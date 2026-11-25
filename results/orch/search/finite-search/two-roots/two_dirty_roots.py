import json,sys
from pathlib import Path
output=Path(sys.argv[1]);mode=sys.argv[2] if len(sys.argv)>2 else 'full';matching=int(sys.argv[3]) if len(sys.argv)>3 else 4;enforce_trace='no_trace' not in sys.argv;enforce_dirty='no_dirty' not in sys.argv;exact='fragment' not in sys.argv;rows=list(range(256)) if mode=='full' else ([m for m in range(256) if m.bit_count()<=2] if mode=='pairs' else sorted(set(json.loads(Path(mode).read_text()))));counter=0;clauses=[];memo={}
def var():
 global counter
 counter+=1;return counter
def add(*xs):clauses.append(list(xs))
TRUE=var();add(TRUE);FALSE=-TRUE
def gate(op,xs):
 xs=set(xs)
 if any(-x in xs for x in xs):return FALSE if op=='and' else TRUE
 if op=='and':
  if FALSE in xs:return FALSE
  xs.discard(TRUE)
 else:
  if TRUE in xs:return TRUE
  xs.discard(FALSE)
 if not xs:return TRUE if op=='and' else FALSE
 if len(xs)==1:return next(iter(xs))
 key=(op,tuple(sorted(xs)))
 if key in memo:return memo[key]
 y=var();memo[key]=y
 if op=='and':
  for x in xs:add(-y,x)
  add(y,*(-x for x in xs))
 else:
  for x in xs:add(y,-x)
  add(-y,*xs)
 return y
def AND(*xs):return gate('and',xs)
def OR(*xs):return gate('or',xs)
def equiv(a,b):add(-a,b);add(a,-b)
def clause_value(s,m):return OR(*(s[i] for i in range(8) if m>>i&1))
edge=[[var() for j in range(4)] for i in range(4)]
for i in range(matching):add(edge[i][i])
for i in range(4):
 for k in range(i):
  for j in range(4):
   for l in range(j):add(-edge[i][j],-edge[i][l],-edge[k][j],-edge[k][l])
dclauses=[[[var() for i in range(8)] for side in range(2)] for d in range(2)]
for pair in dclauses:
 for s in pair:add(*s)
 for i in range(8):add(-pair[0][i],-pair[1][i],*(pair[side][j] for side in range(2) for j in range(8) if j!=i))
raw=[[[var() for i in range(8)] for side in range(2)] for root in range(2)]
select=[[var() for d in range(2)] for side in range(2)]
for d in range(2):add(-select[0][d],-select[1][d])
for side in range(2):add(*raw[1][side],*select[side])
# Root1 may not have identical singleton predecessor supports.
rs=[raw[1][side]+select[side] for side in range(2)]
for i in range(10):add(-rs[0][i],-rs[1][i],*(rs[side][j] for side in range(2) for j in range(10) if j!=i))
D=[[None]*256 for _ in range(2)];R=[[None]*256 for _ in range(2)];G=[None]*256;operands=[[[None]*256 for _ in range(2)] for _ in range(2)]
for m in rows:
 g=OR(*(edge[i][j] for i in range(4) for j in range(4) if m>>i&1 and m>>(4+j)&1));G[m]=g
 for d in range(2):D[d][m]=AND(*(clause_value(s,m) for s in dclauses[d]))
 for side in range(2):
  operands[0][side][m]=OR(clause_value(raw[0][side],m),D[side][m])
  operands[1][side][m]=OR(clause_value(raw[1][side],m),*(AND(select[side][d],D[d][m]) for d in range(2)))
 for root in range(2):R[root][m]=AND(*(operands[root][side][m] for side in range(2)))
 if exact:equiv(OR(R[0][m],R[1][m]),g)
 else:add(-OR(R[0][m],R[1][m]),g)
for i in range(matching):add(OR(R[0][(1<<i)|(1<<(4+i))],R[1][(1<<i)|(1<<(4+i))]))
for d in range(2):
 add(D[d][17])
 if enforce_dirty:add(OR(*(AND(D[d][m],-G[m]) for m in rows)))
traces=[]
for base,direction in [(0,4),(4,0)]:
 dd=[OR(AND(s[base],t[direction]),AND(s[direction],t[base])) for s,t in dclauses]
 rt=[]
 for root in range(2):
  dt=[]
  for side in range(2):
   dt.append(OR(raw[root][side][direction],dd[side]) if root==0 else OR(raw[root][side][direction],*(AND(select[side][d],dd[d]) for d in range(2))))
  rt.append(OR(AND(operands[root][0][1<<base],dt[1]),AND(dt[0],operands[root][1][1<<base])))
 traces.append(OR(*rt))
 if enforce_trace:add(-traces[-1])
output.write_text('p cnf '+str(counter)+' '+str(len(clauses))+'\n'+'\n'.join(' '.join(map(str,c))+' 0' for c in clauses)+'\n')
Path(str(output)+'.meta.json').write_text(json.dumps({'rows':rows,'mode':mode,'matching':matching,'enforce_trace':enforce_trace,'enforce_dirty':enforce_dirty,'exact':exact,'edge':edge,'dclauses':dclauses,'raw':raw,'select':select,'D':D,'R':R,'G':G,'traces':traces},indent=2)+'\n')
print(json.dumps({'variables':counter,'clauses':len(clauses),'truth_rows':len(rows),'matching':matching,'enforce_trace':enforce_trace,'enforce_dirty':enforce_dirty,'shape':'two parallel dirty rectangles; root0=(A or D1) and (B or D2); root1 free side flags; exact graph; both marked traces zero'}))
