import runpy,sys,json
from pathlib import Path
sys.argv=['signed_search.py','--budget','0','--seconds','0','--output','/tmp/oec/pequalnp-pilot-108/signed-load.json']
g=runpy.run_path('/tmp/oec/pequalnp-pilot-108/signed_search.py')
E=g['E'];raw=g['raw'];T=g['T'];restrict=g['restrict'];domains=g['domains'];D=g['D']
cover=[1,3,4,5,6,7];owned={v:[] for v in cover}
for x,y in E:
 v=x if x in cover and (y not in cover or cover.index(x)<cover.index(y)) else y
 owned[v].append(y if v==x else x)
w=raw[:];gates=[];outs=[]
def add(op,a,b):
 out=len(w);w.append(w[a]&w[b] if op=='and' else w[a]|w[b]);gates.append((op,a,b));return out
for v in cover:
 ns=owned[v];z=ns[0]
 for j in ns[1:]:z=add('or',z,j)
 outs.append(add('and',v,z))
z=outs[0]
for j in outs[1:]:z=add('or',z,j)
assert len(gates)==20 and w[z]==T
banks=[{q for val in raw if (q:=restrict(val)[i])} for i in range(D)];paid=[0]*D
worst=999;checks=[]
for prefix in range(21):
 if prefix:
  val=w[9+prefix]
  for d,q in enumerate(restrict(val)):
   if q and q not in banks[d]:banks[d].add(q);paid[d]+=1
 future={z}
 for op,x,y in gates[prefix:]:future.add(x);future.add(y)
 live=[w[i] for i in sorted(future) if i<10+prefix]
 margin=min(20-prefix+paid[d]-L-sum(restrict(val)[d]==0 for val in live) for d,(_,L,_) in enumerate(domains))
 worst=min(worst,margin);checks.append([prefix,len(live),margin])
 assert margin>=0,(prefix,margin)
res={'known_circuit_gates':20,'correct_on_all_1024_inputs':True,'all_restriction_bounds_hold':True,'minimum_margin':worst,'prefix_checks':checks,'gates':gates}
Path('/tmp/oec/pequalnp-pilot-108/signed-bounds-validation.json').write_text(json.dumps(res))
print(json.dumps(res))
