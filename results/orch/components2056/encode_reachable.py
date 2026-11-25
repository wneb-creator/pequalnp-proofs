import argparse
import hashlib
import json
import time
from collections import defaultdict
from pathlib import Path

p=argparse.ArgumentParser()
p.add_argument('--library',required=True);p.add_argument('--bound',type=int,required=True)
p.add_argument('--prefix',required=True);p.add_argument('--pin-baseline',action='store_true')
args=p.parse_args();assert 1<=args.bound<=127
started=time.monotonic();library_text=Path(args.library).read_text();lib=json.loads(library_text)
n=lib['inputs'];N=len(lib['profiles']);productions=lib['productions'];width=args.bound.bit_length()
assert n==26 and lib['row_count']==756 and lib['positive_count']==52
values=[int(s,16) for s in lib['profiles']]
assert len(set(values))==N and values[lib['goal']]==(1<<52)-1
incoming=defaultdict(list)
for i,(parent,op,a,b) in enumerate(productions):
 assert n<=parent<N and op in (0,1) and 0<=a<N and 0<=b<N
 assert values[parent]==(values[a]|values[b] if op else values[a]&values[b])
 incoming[parent].append(i)
assert all(incoming[q] for q in range(n,N))
clauses=[];variables=0
def fresh():
 global variables
 variables+=1;return variables
def neg(x):return not x if type(x)is bool else -x
def add(*literals):
 if any(x is True for x in literals):return
 clause=[x for x in literals if x is not False]
 assert all(type(x)is int and x!=0 for x in clause)
 clauses.append(clause)
def at_most_one(xs):
 if len(xs)<=1:return
 prefix=[fresh() for _ in xs[:-1]]
 add(-xs[0],prefix[0])
 for i in range(1,len(xs)-1):
  add(-xs[i],prefix[i]);add(-prefix[i-1],prefix[i]);add(-xs[i],-prefix[i-1])
 add(-xs[-1],-prefix[-1])
def at_most_k(xs,k):
 previous=[]
 for i,x in enumerate(xs):
  current=[fresh() for _ in range(min(k,i+1))]
  add(-x,current[0])
  for j,old in enumerate(previous):add(-old,current[j])
  for j in range(1,len(current)):add(-x,-previous[j-1],current[j])
  if len(previous)==k:add(-x,-previous[-1])
  previous=current

selected=[fresh() for _ in range(N)]
chosen=[fresh() for _ in productions]
ranks=[None]*n+[[fresh() for _ in range(width)] for q in range(n,N)]
for q in range(n):add(selected[q])
add(selected[lib['goal']])
for q in range(n,N):
 add(-selected[q],*ranks[q])
 # Selected ranks are in1..bound. Bit arrays are least-significant first.
 for j in range(width):
  if not(args.bound>>j&1):
   different=[-ranks[q][k] if args.bound>>k&1 else ranks[q][k] for k in range(j+1,width)]
   add(-selected[q],-ranks[q][j],*different)
 for_producers=[chosen[i] for i in incoming[q]]
 add(-selected[q],*for_producers);at_most_one(for_producers)
for j,bit in enumerate(ranks[lib['goal']]):add(bit if args.bound>>j&1 else -bit)

comparisons={}
def strictly_less(child,parent):
 if child<n:return True # Inputs rank0; a selected parent is already positive.
 key=(child,parent)
 if key in comparisons:return comparisons[key]
 less=fresh();comparisons[key]=less;equal_prefix=True
 for x,y in zip(reversed(ranks[child]),reversed(ranks[parent])):
  add(-less,neg(equal_prefix),-x,y)
  eq=fresh()
  add(-eq,equal_prefix);add(-eq,-x,y);add(-eq,x,-y)
  add(neg(equal_prefix),-x,-y,eq);add(neg(equal_prefix),x,y,eq)
  equal_prefix=eq
 add(-less,-equal_prefix)
 return less
for index,(parent,op,a,b) in enumerate(productions):
 z=chosen[index];add(-z,selected[parent]);add(-z,selected[a]);add(-z,selected[b])
 add(-z,strictly_less(a,parent));add(-z,strictly_less(b,parent))
# Every selected non-root internal feeds a selected production.
# With strict increasing ranks, this makes every selected internal reach the root.
readers=defaultdict(set)
for index,(parent,op,a,b) in enumerate(productions):
 readers[a].add(index);readers[b].add(index)
for q in range(n,N):
 if q!=lib['goal']:add(-selected[q],*[chosen[i] for i in sorted(readers[q])])
at_most_k(selected[n:],args.bound)

if args.pin_baseline:
 control=lib['baseline64'];lookup={tuple(p):i for i,p in enumerate(productions)}
 selected_profiles=set(control['topological_profiles']);selected_producers={lookup[tuple(p)] for p in control['chosen']}
 assert len(selected_profiles)==len(selected_producers)==64
 for q in range(n,N):add(selected[q] if q in selected_profiles else -selected[q])
 for i,z in enumerate(chosen):add(z if i in selected_producers else -z)
 depths={q:0 for q in range(n)};by_parent={p[0]:p for p in control['chosen']}
 for q in control['topological_profiles']:
  _,_,a,b=by_parent[q];depths[q]=max(depths[a],depths[b])+1
 depths[lib['goal']]=args.bound
 for q in range(n,N):
  value=depths.get(q,0)
  assert value<=args.bound
  for j,bit in enumerate(ranks[q]):add(bit if value>>j&1 else -bit)

base=Path(args.prefix);base.parent.mkdir(parents=True,exist_ok=True)
cnf=base.with_suffix('.cnf')
with cnf.open('w') as f:
 f.write(f'p cnf {variables} {len(clauses)}\n')
 for clause in clauses:f.write(' '.join(map(str,clause))+' 0\n')
mapping={'library_sha256':hashlib.sha256(library_text.encode()).hexdigest(),'bound':args.bound,'rank_width':width,'selected':selected,'chosen':chosen,'ranks':ranks,'variables':variables,'clauses':len(clauses),'pin_baseline':args.pin_baseline,'require_output_reachability':True}
base.with_suffix('.mapping.json').write_text(json.dumps(mapping,separators=(',',':'))+'\n')
summary={'profiles':N,'noninput_profiles':N-n,'productions':len(productions),'rank_comparisons':len(comparisons),'bound':args.bound,'rank_width':width,'variables':variables,'clauses':len(clauses),'cnf_bytes':cnf.stat().st_size,'seconds':time.monotonic()-started,'pin_baseline':args.pin_baseline,'require_output_reachability':True}
base.with_suffix('.summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary),flush=True)
