import json
from pathlib import Path
n=8
y={0,1,2}
S=[{3,4,5,6,7},{0,4}]
gates=[('and',[0,1]),('and',[8,2]),('not',[9]),('and',[10,5]),('or',[3,11]),('and',[9,5]),('or',[4,13]),('or',[12,14]),('or',[6,7]),('or',[15,16]),('or',[0,14])]
outs=[17,18]
def run(bits, freeze=None):
 w=list(bits)
 for j,(op,ins) in enumerate(gates):
  v=[w[t] if t<len(w) else False for t in ins]
  w.append(freeze if j==2 and freeze is not None else all(v) if op=='and' else any(v) if op=='or' else not(v[0] if v else False))
 return w
def inp(mask):return [bool(mask>>i&1) for i in range(n)]
for mask in range(1<<n):
 bits=inp(mask);w=run(bits)
 assert all(w[o]==any(bits[p] for p in s) for o,s in zip(outs,S))
 if sum(bits)<len(y):assert w[n+2]
 a=run(bits,True);b=run([bits[i] or i in y for i in range(n)],False)
 assert (a[15] and b[15])==any(bits[i] for i in [3,4,5])
assert not run([i in y for i in range(n)])[n+2]
A=[set() for _ in range(n+len(gates))];B=[set() for _ in A];H=[set() for _ in A]
for p in range(n):
 a=run([i==p for i in range(n)],True);b=run([i in y or i==p for i in range(n)],False)
 for w in range(len(A)):
  if a[w]:A[w].add(p)
  if p not in y and b[w]:B[w].add(p)
  if a[w] and b[w]:H[w].add(p)
assert H[15]=={3,4,5} and all(len(h)<=1 for h in H[:15])
refund=[j for j in range(len(gates)) if any(A[n+j]==s for s in S) and any(s.isdisjoint(y) and B[n+j]==s for s in S)]
assert 7 not in refund
result={'scope':'Counterexample only to gatewise hybrid rewrite; NOT a refutation of L-meta-997','inputs':n,'gates':gates,'outputs':outs,'target_sets':[sorted(s) for s in S],'checked_inputs':1<<n,'problem_gate':7,'hybrid_singleton_support':sorted(H[15]),'maximum_prior_hybrid_singleton_support':max(map(len,H[:15])),'refund_gate_indices':refund,'posted_lhs':7,'posted_rhs':len(gates)+len(refund)+len(S),'verdict':'All assertions passed; any binary monotone gate over prior hybrid wires has at most2 singleton truths, whereas problem hybrid has3.'}
print(json.dumps(result,indent=2))
