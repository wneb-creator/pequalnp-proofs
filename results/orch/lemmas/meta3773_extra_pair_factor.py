from pathlib import Path
import json,itertools,hashlib,resource,time
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(30,30));job=Path('/tmp/oec/pequalnp-pilot-79');D={0,1,3,9};target=tuple(sorted((1<<p)|(1<<(13+l)) for p in range(13) for l in range(13) if (p+l)%13 in D))
def norm(terms):
 out=[]
 for t in sorted(set(terms),key=lambda x:(x.bit_count(),x)):
  if not any(s&t==s for s in out):out.append(t)
 return tuple(sorted(out))
def combine(op,a,b):return norm(a+b) if op else norm(tuple(x|y for x in a for y in b))
def parse(d):
 vals=[(1<<i,) for i in range(26)];stars={}
 for op,a,b in d['gates']:
  assert a<len(vals) and b<len(vals)
  v=combine(op,vals[a],vals[b]);vals.append(v)
  if op==0 and ((a<26 and a>=13) or (b<26 and b>=13)):
   line=(a if 13<=a<26 else b)-13;stars[line]=v
 assert len(stars)==13
 return vals,stars
names=['meta3773-single-extra64-p0-l'+str(l)+'.json' for l in [2,8,12]]+['meta3773-single-extra64-p1-l'+str(l)+'.json' for l in [1,3,9]];data={n:json.loads((job/n).read_text()) for n in names};hashes={n:hashlib.sha256((job/n).read_bytes()).hexdigest() for n in names};parsed={n:parse(d) for n,d in data.items()}
for n,d in data.items():
 p,l=d['extra_edge'];assert parsed[n][0][d['output']]==norm(target+((1<<p)|(1<<(13+l)),))
def count_representation(order,mode):
 functions=[(1<<i,) for i in range(26)];memo={f:i for i,f in enumerate(functions)};gates=[]
 def emit(op,a,b):
  f=combine(op,functions[a],functions[b])
  if f in memo:return memo[f]
  w=len(functions);functions.append(f);gates.append((op,a,b));memo[f]=w;return w
 stars=[]
 for name in order:
  d=data[name];mapping=list(range(26));st={}
  for i,(op,a,b) in enumerate(d['gates']):
   w=emit(op,mapping[a],mapping[b]);mapping.append(w)
   if op==0 and ((13<=a<26) or (13<=b<26)):st[(a if 13<=a<26 else b)-13]=w
  stars.append(st)
 common=[i for i in range(13) if functions[stars[0][i]]==functions[stars[1][i]]];different=[i for i in range(13) if i not in common];assert len(common)==11 and len(different)==2
 def union(ws):
  w=ws[0]
  for x in ws[1:]:w=emit(1,w,x)
  return w
 R=union([stars[0][i] for i in common])
 if mode=='direct_common_or_factor':
  a=union([stars[0][i] for i in different]);b=union([stars[1][i] for i in different]);K=emit(0,a,b)
 else:
  correct=[]
  for i in different:
   true_star=tuple(sorted((1<<p)|(1<<(13+i)) for p in range(13) if (p+i)%13 in D))
   correct.append(next(st[i] for st in stars if functions[st[i]]==true_star))
  K=union(correct)
 out=emit(1,R,K);assert functions[out]==target;used=set()
 def visit(w):
  if w<26 or w in used:return
  used.add(w);_,a,b=gates[w-26];visit(a);visit(b)
 visit(out)
 return len(used)
reports=[]
for a,b in itertools.product(names[:3],names[3:]):
 va,sa=parsed[a];vb,sb=parsed[b];assert combine(0,va[data[a]['output']],vb[data[b]['output']])==target
 reports.append({'left':a,'right':b,'common_stars':11,'direct_common_or_factor_cost':min(count_representation([a,b],'direct_common_or_factor'),count_representation([b,a],'direct_common_or_factor')),'absorption_to_exact_stars_cost':min(count_representation([a,b],'exact'),count_representation([b,a],'exact'))})
assert all(hashlib.sha256((job/n).read_bytes()).hexdigest()==h for n,h in hashes.items());out={'scope':'Exact finite-DNF verification and explicit syntactic factoring counts for nine overapproximation pairs; no63gate witness and no global lower bound. The counts are constructed upper bounds, not a solver optimum.','source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'input_hashes':hashes,'reports':reports};(job/'meta3773-extra-pair-factor-result.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
