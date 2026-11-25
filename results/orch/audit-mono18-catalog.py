from pathlib import Path
import hashlib,json,re,sys
catalog=Path(sys.argv[1]);canonical=Path(sys.argv[2]);cpp=Path(sys.argv[3]);out=Path(sys.argv[4])
s=catalog.read_text();c=canonical.read_text();raw=cpp.read_text()
cpblock=re.search(r'static const CP profiles\[CP_COUNT\] = \{(.*?)\};',raw,re.S).group(1)
profiles=[tuple(map(int,x)) for x in re.findall(r'\{(\d+),(\d+),(\d+),(\d+)\}',cpblock)]
assert len(profiles)==1145
N=(1<<1024)-1
inputs=[sum(1<<r for r in range(1024) if r>>j&1) for j in range(10)]
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
graph=0
for a,b in edges:graph|=inputs[a]&inputs[b]
def rotate(w,n):return ((w>>n)|(w<<(1024-n)))&N if n else w
def decode(v):
 if v<256:
  a=v&15;b=v>>4;assert 0<=a<b<10
  return inputs[a]&(N^inputs[b]),inputs[b]&(N^inputs[a]),(1<<b)-(1<<a)
 if v<272:
  a=v-256;assert a<10;return inputs[a],0,1024-(1<<a)
 a=v-272;assert a<10;return N^inputs[a],0,1<<a
def moved(w,codes):
 for code in reversed(codes):
  a,b,delta=decode(code)
  w=(a&rotate(w,delta))|((N^a)&((b&rotate(w,(1024-delta)%1024))|((N^b)&w)))
 return w
masks=[int(x) for x in re.search(r'def freeMask .*?:= !\[(.*?)\] i',c).group(1).split(',')]
bounds=[int(x) for x in re.search(r'def bound .*?:= !\[(.*?)\] i',c).group(1).split(',')]
assert len(masks)==len(bounds)==17
targets={}
for i,expr in re.findall(r'def target(\d+) : Sig := ([^\n]+)',c):
 mask=int(re.search(r'graphGoal (\d+)',expr).group(1));word=0
 for a,b in edges:
  if a<9 and b<9 and mask>>a&1 and mask>>b&1:word|=inputs[a]&inputs[b]
 for j in re.findall(r'inputs.getD (\d+) zero',expr):word|=inputs[int(j)]
 targets[int(i)]=word
entries=[]
for pid,z,o,rep,codes in re.findall(r'\((\d+), (\d+), (\d+), (\d+), \[([\d, ]*)\]\)',s):
 pid,z,o,rep=map(int,[pid,z,o,rep]);codes=[int(x) for x in codes.split(',') if x.strip()]
 assert (z,o,bounds[rep])==(profiles[pid][0],profiles[pid][1],profiles[pid][3])
 domain=N
 for i in range(10):
  if z>>i&1:domain&=N^inputs[i]
  elif o>>i&1:domain&=inputs[i]
 assert moved(graph,codes)==targets[rep]
 assert moved(domain,codes)==N
 free={0,N}|{inputs[i] for i in range(9) if masks[rep]>>i&1}
 for x in inputs:assert moved(x,codes) in free
 entries.append(pid)
assert len(entries)==len(set(entries))==299
report={'verdict':'PASS','profile_records':299,'canonical_priors':17,'each_word_width':1024,'checks_per_profile':['exact original weak profile zero/one/bound','moved Petersen target','domain maps to all ones','all ten input images free in canonical roots'],'omitted_profile':1086,'replacement_profile':1089,'source_sha256':hashlib.sha256(catalog.read_bytes()).hexdigest(),'canonical_sha256':hashlib.sha256(canonical.read_bytes()).hexdigest(),'cpp_sha256':hashlib.sha256(cpp.read_bytes()).hexdigest(),'scope':'Independent evaluation of the actual Lean literal records; Lean compilation and prior soundness remain separately required.'}
out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
