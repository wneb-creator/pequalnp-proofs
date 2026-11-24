import itertools,json
from pathlib import Path
lines=[set((d+w)%13 for d in (0,1,3,9)) for w in range(13)]
A,B=lines[0],lines[1]
p=next(iter(A&B));a=sorted(A-{p});b=sorted(B-{p});q=min(set(range(13))-(A|B))
gates=[('or',[a[0],a[1]]),('or',[13,a[2]]),('or',[b[0],b[1]]),('or',[15,b[2]]),('or',[14,16]),('or',[17,q]),('and',[p,18]),('or',[14,19]),('or',[16,19])]
errors=[];upper=[];rows=0
for mask in range(1<<13):
 x=[bool(mask>>i&1) for i in range(13)];v=x.copy()
 for op,ins in gates:v.append(any(v[i] for i in ins) if op=='or' else all(v[i] for i in ins))
 targets=[any(x[i] for i in L) for L in (A,B)]
 if mask.bit_count() in (7,8):
  rows+=1
  if [v[20],v[21]]!=targets:errors.append(mask)
 if any(v[o] and not t for o,t in zip((20,21),targets)):upper.append(mask)
res={'line_ids':[0,1],'lines':[sorted(A),sorted(B)],'common':p,'foreign':q,'gates':gates,'outputs':[20,21],'total_gates':len(gates),'band_rows':rows,'band_errors':errors,'global_upper_errors':upper,'nonordinary_witness':1<<p,'scope':'Counterexample to proposed10-gate two-nonordinary-output bound; not a counterexample to39-gate13-output claim.'}
Path('two-nonordinary-nine.json').write_text(json.dumps(res,indent=2))
print(json.dumps(res,indent=2))
assert rows==3003 and not errors and not upper
