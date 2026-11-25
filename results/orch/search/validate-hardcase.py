import argparse, json, re
from pathlib import Path

ap=argparse.ArgumentParser()
ap.add_argument('stdout');ap.add_argument('--out',required=True)
a=ap.parse_args();source=Path(a.stdout).read_text();args=json.loads(source.splitlines()[0])
assert source.splitlines()[1]=='sat'
p,l,k=args['p'],args['l'],args['gates'];n=p+l
edges=[tuple(map(int,e.split(','))) for e in args['edges'].split(';')]
selectors={name:value=='true' for name,value in re.findall(r'\(([a-z0-9]+) (true|false)\)',source)}
inputs=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
target=sum(1<<x for x in range(1<<n) if any(x>>u&1 and x>>(p+v)&1 for u,v in edges))
positive=sum(1<<((1<<u)|(1<<(p+v))) for u,v in edges)
fullmask=(1<<(1<<n))-1
values=inputs.copy();operands=[]
for j in range(k):
 sides=[[i for i in range(n+j) if selectors[f'{pos}{j}s{i}']] for pos in ['a','b']]
 assert all(sides)
 for side in sides:assert not(any(i<p for i in side) and any(p<=i<n for i in side))
 operands.append(sides)
 arms=[0,0]
 for b in range(2):
  for i in sides[b]:arms[b]|=values[i]
 values.append(arms[0]&arms[1])
outputs=[i for i in range(n,n+k) if selectors[f'outs{i}']]
output=0
for i in outputs:output|=values[i]
assert output==target
dirty=[bool(values[n+j]&~target) for j in range(k)]
assert sum(dirty)>=2
first=dirty.index(True)
forced=values[:n+first]+[0]
for j in range(first+1,k):
 arms=[0,0]
 for b in range(2):
  for i in operands[j][b]:arms[b]|=forced[i]
 forced.append(arms[0]&arms[1])
forcedout=0
for i in outputs:forcedout|=forced[i]
lost_edges=[(u,v) for u,v in edges if not (forcedout>>((1<<u)|(1<<(p+v)))&1)]
nonstar_lost=any(u!=s and v!=t for u,v in lost_edges for s,t in lost_edges)
if args.get('lost_nonstar'):assert nonstar_lost
for j in range(k):
 assert values[n+j]&positive
 readers=[q for q in range(j+1,k) if any(n+j in side for side in operands[q])]
 assert readers or n+j in outputs
 if not dirty[j]:assert not readers
 if j==first:assert all(dirty[q] for q in readers)

# Compile an explicit binary circuit, sharing syntactically identical ORs.
gates=[];compiled=inputs.copy();colours=[1 if i<p else 2 for i in range(n)]
mapping=list(range(n));cache={frozenset([i]):i for i in range(n)}
def emit(op,left,right):
 v=(compiled[left]|compiled[right]) if op=='or' else (compiled[left]&compiled[right])
 c=(colours[left]|colours[right]) if op=='or' else 0
 assert c!=3
 w=n+len(gates);gates.append({'wire':w,'op':op,'left':left,'right':right,'dirty':bool(v&~target)})
 compiled.append(v);colours.append(c);return w
def make_or(items):
 terms=frozenset(items)
 if terms in cache:return cache[terms]
 largest=max((key for key in cache if key<=terms),key=lambda key:(len(key),tuple(sorted(key))))
 seen=largest;wire=cache[largest]
 for item in sorted(terms-largest):
  wire=emit('or',wire,item);seen=seen|{item};cache[seen]=wire
 return wire
for sides in operands:
 arms=[make_or([mapping[i] for i in side]) for side in sides]
 w=emit('and',*arms);mapping.append(w);cache[frozenset([w])]=w
out=make_or([mapping[i] for i in outputs])
assert compiled[out]==target
result={'args':args,'all_assignments':1<<n,'exact_function':True,'tcount_zero':True,
 'and_count':k,'dirty_and_indices':[j for j,d in enumerate(dirty) if d],
 'first_dirty_readers':[q for q in range(first+1,k) if any(n+first in side for side in operands[q])],
 'edges_lost_when_first_dirty_forced_false':lost_edges,'lost_edges_nonstar':nonstar_lost,
 'topform':True,'all_and_live':True,'all_and_positive_on_edge':True,
 'free_operands':operands,'free_outputs':outputs,
 'naive_binary_count':k+sum(len(side)-1 for sides in operands for side in sides)+len(outputs)-1,
 'shared_binary_count':len(gates),'binary_gates':gates,'binary_output':out}
Path(a.out).write_text(json.dumps(result,indent=2))
print(json.dumps({key:value for key,value in result.items() if key not in ['binary_gates','args']},indent=2))
