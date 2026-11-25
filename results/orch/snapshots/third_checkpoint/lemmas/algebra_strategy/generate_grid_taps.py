import json
from pathlib import Path
from itertools import product
base=Path("results/orch/lemmas/algebra_strategy")
n=15
edges=[(i,6+3*i+j) for i in range(3) for j in range(3)]+[(3+j,6+3*i+j) for i in range(3) for j in range(3)]
def H(mask):return any(mask>>a&1 and mask>>b&1 for a,b in edges)
def A(mask):return bool(mask&7)
def B(mask):return bool(mask&56)
neg=[m for m in range(1<<n) if not H(m)]
maxneg=[m for m in neg if all(H(m|1<<i) for i in range(n) if not(m>>i&1))]
maxA=[m for m in neg if not A(m) and all(H(m|1<<i) for i in range(3,n) if not(m>>i&1))]
maxB=[m for m in neg if not B(m) and all(H(m|1<<i) for i in list(range(3))+list(range(6,n)) if not(m>>i&1))]
masks=sorted(set([1<<a|1<<b for a,b in edges]+maxneg+maxA+maxB+[1<<i for i in range(6)]))
tests=[{"mask":m,"targets":[int(H(m)), -1 if H(m) else int(A(m)), -1 if H(m) else int(B(m))]}for m in masks]
gates=[]
def gate(op,a,b):
 gates.append([op,a,b]);return n+len(gates)-1
def ors(xs):
 t=xs[0]
 for x in xs[1:]:t=gate(1,t,x)
 return t
terms=[]
for i in range(6):terms.append(gate(0,i,ors([b for a,b in edges if a==i])))
h=ors(terms)
a=ors([0,1,2]);b=ors([3,4,5]);outs=[h,a,b]
for mask in range(1<<n):
 vals=[bool(mask>>i&1) for i in range(n)]
 for op,a0,b0 in gates:vals.append(vals[a0] or vals[b0] if op else vals[a0] and vals[b0])
 assert [vals[o]for o in outs]==[H(mask),A(mask),B(mask)]
assert len(gates)==27
# Directly verify that the finite care tests cover all required conditional tap cases.
for m in neg:
 if A(m):assert any((1<<i)&m==1<<i for i in range(3))
 else:assert any(m&v==m for v in maxA)
 if B(m):assert any((1<<i)&m==1<<i for i in range(3,6))
 else:assert any(m&v==m for v in maxB)
inputmap=[0,1,3,2,4,5,7,9,13,16,12,8,15,14,10]
def remap(w):return inputmap[w]if w<15 else w+2
fg=[[op,remap(a0),remap(b0)]for op,a0,b0 in gates]
hh,aa,bb=[remap(o)for o in outs]
def fgadd(op,a0,b0):fg.append([op,a0,b0]);return 17+len(fg)-1
u=fgadd(0,6,aa);v=fgadd(0,11,bb);out=fgadd(1,fgadd(1,hh,u),v)
case=json.loads(Path("results/orch/lemmas/circuit_search/subsets/k6_p3.json").read_text())
for mask,target in case["tests"]:
 vals=[bool(mask>>i&1)for i in range(17)]
 for op,a0,b0 in fg:vals.append(vals[a0]or vals[b0]if op else vals[a0]and vals[b0])
 assert vals[out]==bool(target)
data={"name":"k6_grid_two_conditional_taps","inputs":15,"target_gates":24,"output_names":["H","A_sum_when_H_false","B_sum_when_H_false"],"edges":edges,"tests":tests,"maximal_negative_count":len(maxneg),"tap_A_negative_maxima":maxA,"tap_B_negative_maxima":maxB,"baseline":{"gates":gates,"outputs":outs},"input_map_to_k6":inputmap,"hub_inputs_in_k6":[6,11],"completion_gate_cost":4,"completion_baseline":{"gates":fg,"output":out}}
(base/"k6_grid_taps.json").write_text(json.dumps(data,indent=2))
print(f"{len(tests)} union tests, {len(maxneg)} H-maximal negatives, {len(maxA)}/{len(maxB)} tap-negative maxima; baseline27gates verified on all32768assignments,31gate completion verified on76tests")
