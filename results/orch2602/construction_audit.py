from pathlib import Path
import json,itertools,datetime
BASE=Path(__file__).resolve().parent
N=13
edges={(a,b) for a in range(N) for b in range(N) if (a-b)%N in {0,1,3,9}}
class Builder:
 def __init__(self):self.gates=[]
 def gate(self,op,a,b):
  assert a!=b and 0<=a<26+len(self.gates) and 0<=b<26+len(self.gates)
  self.gates.append((op,a,b));return 25+len(self.gates)
 def either(self,xs):
  v=xs[0]
  for x in xs[1:]:v=self.gate('or',v,x)
  return v
 def star(self,repeat):
  cols=[]
  for l in range(N):
   xs=[a for a in range(N) if(a,l)in edges]
   if l==0:
    v=0
    for w in repeat:v=self.gate('and',v,w)
    xs[xs.index(0)]=v
   cols.append(self.gate('and',13+l,self.either(xs)))
  return self.either(cols)
def antichain(items):
 out=[]
 for item in sorted(set(items),key=lambda x:(x.bit_count(),x)):
  if not any((x&item)==x for x in out):out.append(item)
 return frozenset(out)
def semantics(gates,out):
 wires=[frozenset([1<<i])for i in range(26)]
 for op,a,b in gates:wires.append(antichain((x|y for x in wires[a] for y in wires[b])if op=='and' else wires[a]|wires[b]))
 return wires[out]
def derivative(gates,out,base,direction):
 v=[i==base for i in range(26)];d=[i==direction for i in range(26)]
 for op,a,b in gates:
  d.append((v[a]and d[b])or(d[a]and v[b])if op=='and' else d[a]or d[b])
  v.append(v[a]and v[b]if op=='and'else v[a]or v[b])
 return d[out]
reports=[]
for title,repeats in [('star64',[]),('oneReread65',[13]),('doubleReread66',[13,0])]:
 b=Builder();out=b.star(repeats);normal=semantics(b.gates,out)
 assert normal==frozenset((1<<a)|(1<<(13+l))for a,l in edges)
 reports.append({'name':title,'size':len(b.gates),'output':out,'gates':b.gates,'minimalTrueAssignments':[hex(x)for x in sorted(normal)],'edgeCount':len(normal),'derivativeAtPoint0TowardLine0':derivative(b.gates,out,0,13),'derivativeAtLine0TowardPoint0':derivative(b.gates,out,13,0),'legalDistinctEarlierInputs':True,'exactFunctionVerifiedByMonotoneAntichain':True})
# Every minimum cover in this regular connected bipartite graph selects one side.
# For a chosen point subset A, all neighbors of the complementary point subset must be selected lines.
covers=[]
for mask in range(1<<N):
 A={a for a in range(N)if(mask>>a)&1};B={b for a,b in edges if a not in A};cost=len(A)+len(B)
 if cost<=13:covers.append({'points':sorted(A),'lines':sorted(B),'size':cost})
assert len(covers)==2 and all(x['size']==13 for x in covers)
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'Python exact symbolic antichain checks; not a Lean result','inputs':26,'verticesEachSide':13,'edges':len(edges),'leftDegrees':sorted(sum(a==p for a,b in edges)for p in range(N)),'rightDegrees':sorted(sum(b==l for a,b in edges)for l in range(N)),'fourCycles':sum(all((a,b)in edges for a in ps for b in ls)for ps in itertools.combinations(range(N),2)for ls in itertools.combinations(range(N),2)),'vertexCoversAtMost13':covers,'constructions':reports,'conclusion':'No counterexample at63or64 found. Double reread is attainable at66 by exactlytwo extraAND gates in the64gate star construction. This is not a lowerbound against other circuit architectures.'}
(BASE/'construction-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ['constructions','vertexCoversAtMost13']}))
print(json.dumps([{'name':x['name'],'size':x['size'],'derivatives':[x['derivativeAtPoint0TowardLine0'],x['derivativeAtLine0TowardPoint0']]}for x in reports]))
