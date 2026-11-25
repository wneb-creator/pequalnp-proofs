from pathlib import Path
import json
D={0,1,3,9}
S=[0,1,2,3,4,9,10]
T=[p for p in range(13) if p not in S]
reps=[(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
def row(a,b,m,t,dual):
 if dual:a,b=b,a
 sign=-1 if dual else 1
 return [bool(mask>>((sign*(m*i+t))%13)&1)for mask in(a,b)for i in range(13)]
neg=[row(a,b,m,t,d)for a,b in reps for m in(1,3,9)for t in range(13)for d in(False,True)]
def add_star(gates,n,p,line_wires):
 sums=list(line_wires)
 while len(sums)>1:
  a=sums.pop(0);b=sums.pop(0);gates.append(('or',a,b));sums.insert(0,n+len(gates)-1)
 gates.append(('and',p,sums[0]));return n+len(gates)-1

def join(gates,n,outs):
 outs=list(outs)
 while len(outs)>1:
  a=outs.pop(0);b=outs.pop(0);gates.append(('or',a,b));outs.insert(0,n+len(gates)-1)
 return outs[0]

def run(gates,n,out,x):
 assert len(x)==n
 w=list(x)
 for op,a,b in gates:
  assert a<len(w)and b<len(w)
  w.append((w[a]and w[b])if op=='and'else(w[a]or w[b]))
 return w[out]
core=[]
core_out=join(core,20,[add_star(core,20,i,[7+w for w in range(13)if(p-w)%13 in D])for i,p in enumerate(S)])
assert len(core)==34
assert all(run(core,20,core_out,[(q==p)for q in S]+[(v==w)for v in range(13)])for p in S for w in range(13)if(p-w)%13 in D)
assert all(not run(core,20,core_out,[x[p]for p in S]+x[13:])for x in neg)
full=[]
# Embed the checked twenty-input core in twenty-six input positions.
wire=lambda k:S[k]if k<7 else 13+k-7 if k<20 else 26+k-20
for op,a,b in core:full.append((op,wire(a),wire(b)))
outs=[26+core_out-20]
outs.append(join(full,26,[add_star(full,26,p,[13+w for w in range(13)if(p-w)%13 in D])for p in T]))
full_out=join(full,26,outs)
assert len(full)==64
assert all(run(full,26,full_out,[(q==p)for q in range(13)]+[(v==w)for v in range(13)])for p in range(13)for w in range(13)if(p-w)%13 in D)
assert all(not run(full,26,full_out,x)for x in neg)
report={'core_points':S,'boundary_points':T,'core_inputs':20,'core_gates':len(core),'core_positive_pairs_checked':28,'negative_rows_checked':len(neg),'distinct_negative_rows':len({tuple(x)for x in neg}),'complete_inputs':26,'complete_gates':len(full),'complete_positive_pairs_checked':52,'all_checks_passed':True,'limitation':'This is a 34/64-gate sanity baseline, not the requested 33/63-gate witness.'}
print(json.dumps(report,indent=2))
Path(__file__).with_name('baseline-result.json').write_text(json.dumps(report,indent=2))
Path(__file__).with_name('baseline-circuits.json').write_text(json.dumps({'core':{'inputs':20,'gates':core,'output':core_out},'complete':{'inputs':26,'gates':full,'output':full_out}},indent=2))
