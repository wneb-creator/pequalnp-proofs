from pathlib import Path
import ast,hashlib,json,re
repo=Path('/workspace/pequalnp-proofs')
src=repo/'results/orch/lemmas/RectangleBank41908.lean'
s=src.read_text()
base=(repo/'results/orch/lemmas/RectangleOrEdge.lean').read_text()
def vector(text,name):
 m=re.search(r'def '+name+r'[^\n]*:= !\[(.*?)\]\n',text,re.S)
 return ast.literal_eval('['+m.group(1).replace('![','[')+']')
w=vector(s,'weight'); costs=vector(s,'costs');positions=vector(s,'positions')
positive=vector(base,'positiveRows');negative=vector(base,'negativeRows')
labels=ast.literal_eval(re.search(r'def labels[^\n]*:= (\[[^\n]+\])',s).group(1))
assert len(w)==15 and all(len(row)==15 for row in w)
assert len(costs)==10 and len(positions)==10
banks=json.loads(Path('/tmp/oec/pequalnp-pilot-87/library_route/copy-closure-banks-selected.json').read_text())
assert isinstance(banks,list) and all(isinstance(x,dict) for x in banks)
bank=next(x for x in banks if x['node']==41908)
actual=[int(x,16) for x in bank['state']]
inputs=[sum(1<<r for r in range(1024) if r&(1<<i)) for i in range(10)]
assert actual==[inputs[i] for i in labels]
assert bank['remaining']==len(labels)-1==19
maxima=[]
for i in range(10):
 assert set(positions[i])=={r for r,x in enumerate(positive) if x&(1<<i)}
 cols=[c for c,x in enumerate(negative) if not x&(1<<i)]
 vals=[sum(max(sum(w[positions[i][r]][c] for r in range(3) if mask&(1<<r)),0) for c in cols) for mask in range(8)]
 maxima.append(max(vals));assert max(vals)<=costs[i]
assert sum(map(sum,w))==116
assert sum(costs[i] for i in labels)==104
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def graph(x):return any(x&(1<<a) and x&(1<<b) for a,b in edges)
assert all(graph(x) for x in positive) and all(not graph(x) for x in negative)
print('PASS exact20root bank41908 at19gate tight budget; all1024truth bits per input match selected bank.')
print('PASS exact15positive/15negative rows and all80 rectangle support subsets.')
print('Maxima:',maxima,'stated caps:',costs)
print('Total target weight116; indexed bank cost104; strict gap12.')
print('Multiplicity:',[labels.count(i) for i in range(10)])
print('Source SHA256:',hashlib.sha256(src.read_bytes()).hexdigest())
print('Bank source SHA256:',hashlib.sha256(Path('/tmp/oec/pequalnp-pilot-87/library_route/copy-closure-banks-selected.json').read_bytes()).hexdigest())
