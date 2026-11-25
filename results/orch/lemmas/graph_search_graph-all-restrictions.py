import itertools,json,re,subprocess,datetime,collections
from pathlib import Path
P=Path('/tmp/oec/pequalnp-pilot-182')
E=[(0,2),(1,3),(0,4),(1,4),(2,4),(0,5),(1,5),(3,5),(0,6),(2,6),(3,6),(5,6)]
N=[set() for _ in range(7)]
for a,b in E:N[a].add(b);N[b].add(a)
V=set(range(7))
def parse(s):
 ts=re.findall(r'x[0-6]|AND|OR|[()]',s);at=0
 def rec():
  nonlocal at
  t=ts[at];at+=1
  if t.startswith('x'):return int(t[1:])
  assert t=='(',t
  a=rec();op=ts[at].lower();at+=1;b=rec();assert ts[at]==')';at+=1
  return (op,a,b)
 x=rec();assert at==len(ts);return x
def foldor(xs):
 assert xs
 x=xs[0]
 for y in xs[1:]:x=('or',x,y)
 return x
def fmt(e):
 if isinstance(e,int):return 'x'+str(e)
 return '('+fmt(e[1])+' '+e[0]+' '+fmt(e[2])+')'
def circuit(e):
 gates=[]
 def rec(e):
  if isinstance(e,int):return e
  a,b=rec(e[1]),rec(e[2]);gates.append([e[0],a,b]);return len(gates)+6
 out=rec(e);return gates,out

def zerof(z):
 log=P/f'restriction-{z}.log'
 if not log.exists():
  r=subprocess.run([str(P/'graph-restriction'),str(z)],capture_output=True,text=True,check=True)
  log.write_text(r.stdout+r.stderr)
 lines=log.read_text().splitlines();t=[x for x in lines if x.startswith('TARGET')][-1]
 _,cost,f=t.split(' ',2)
 return parse(f),int(cost)

existingzero=json.loads((P/'lower-bound-restriction-table.json').read_text())
entries=[];counts=collections.Counter();mismatches=[]
for status in itertools.product(range(3),repeat=7):
 z=sum(1<<i for i,s in enumerate(status) if s==1)
 o=sum(1<<i for i,s in enumerate(status) if s==2)
 if z==0 and o==0:continue
 zeros={i for i in V if z>>i&1};ones={i for i in V if o>>i&1};free=V-zeros-ones
 code=z+(o<<9)
 if any(a in ones and b in ones for a,b in E):counts['constant_true']+=1;continue
 singletons={b for a in ones for b in N[a] if b in free}
 edges=[(a,b) for a,b in E if a in free and b in free and a not in singletons and b not in singletons]
 if not singletons and not edges:counts['constant_false']+=1;continue
 if not ones:
  expr,dcost=zerof(z)
 else:
  terms=sorted(singletons)
  if edges:
   verts=sorted(set(v for e in edges for v in e))
   assert len(verts) in (2,3),(z,o,edges)
   assert set(edges)==set(itertools.combinations(verts,2)),(z,o,edges)
   if len(verts)==2:terms.append(('and',verts[0],verts[1]))
   else:
    a,b,c=verts
    terms.append(('or',('and',a,b),('and',c,('or',a,b))))
  expr=foldor(terms)
 gates,out=circuit(expr);cost=len(gates)
 if not ones:
  assert cost==dcost
  if str(z) in existingzero and existingzero[str(z)]['lower_bound']!=cost:mismatches.append([z,existingzero[str(z)]['lower_bound'],cost])
 for x in range(128):
  forced=(x&~z)|o
  target=any(bool(forced>>a&1) and bool(forced>>b&1) for a,b in E)
  w=[bool(x>>i&1) for i in range(7)]
  for op,a,b in gates:w.append(w[a]&w[b] if op=='and' else w[a]|w[b])
  assert w[out]==target,(code,x,gates,out)
 existing=not ones or (len(ones)==1 and len(zeros)<=1) or (len(ones)==2 and not zeros)
 entry={'code':code,'zero_mask':z,'one_mask':o,'zeros':sorted(zeros),'ones':sorted(ones),'singletons':sorted(singletons),'edges':edges,'candidate_lower_bound':cost,'verified_upper_bound':cost,'formula':fmt(expr),'gates':gates,'output':out,'existing168':existing,'all128_verified':True}
 entries.append(entry);counts['nonconstant']+=1;counts[f'ones{len(ones)}']+=1;counts[f'bound{cost}']+=1
entries.sort(key=lambda e:(-(e['zero_mask']|e['one_mask']).bit_count(),e['code']))
new=[e for e in entries if not e['existing168']]
positive=[e for e in entries if e['candidate_lower_bound']>0]
newpositive=[e for e in new if e['candidate_lower_bound']>0]
priority=[e for e in new if e['candidate_lower_bound']>=4]
summary={'generated_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'total_proper_ternary_restrictions':3**7-1,'counts':dict(counts),'zero_lower_bound_mismatches':mismatches,'existing168_count':sum(e['existing168'] for e in entries),'new_nonconstant_count':len(new),'new_positive_bound_count':len(newpositive),'new_bound_at_least4_count':len(priority),'notes':'Every explicit monotone construction verified onall128 inputs. Candidate lower bounds require independent Lean certificate; upper bounds alone do not establish them.'}
(P/'graph-all-restrictions.json').write_text(json.dumps({'summary':summary,'entries':entries},separators=(',',':'))+'\n')
(P/'graph-new-restriction-bounds.json').write_text(json.dumps([[e['code'],e['candidate_lower_bound']] for e in newpositive],separators=(',',':'))+'\n')
(P/'graph-all-restriction-bounds.json').write_text(json.dumps([[e['code'],e['candidate_lower_bound']] for e in positive],separators=(',',':'))+'\n')
(P/'graph-priority-restriction-bounds.json').write_text(json.dumps([[e['code'],e['candidate_lower_bound']] for e in priority],separators=(',',':'))+'\n')
(P/'graph-priority-restriction-bounds.lean.txt').write_text(str([(e['code'],e['candidate_lower_bound']) for e in priority])+'\n')
print(json.dumps(summary,indent=2))
print('Priority rows',[(e['code'],e['candidate_lower_bound']) for e in priority])
