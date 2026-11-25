import json,z3
from pathlib import Path
from counterexample_freeand import synth as freeand
from counterexample_sat import synth as gates
z3.set_param("memory_max_size",256)
p=Path("/tmp/oec/pequalnp-pilot-55/root-followup-search.jsonl")
c5pair=[(i,(i+1)%5) for i in range(5)]+[(5+i,5+(i+1)%5) for i in range(5)]
print("Starting disjoint two-C5, at most8 OR with free AND",flush=True)
r=freeand(10,c5pair,8,timeout=180000);r["name"]="two_C5"
with p.open("a") as f:f.write(json.dumps(r)+"\n")
print(json.dumps(r),flush=True)
print("Starting C7, size10, at leastone unsound AND",flush=True)
r=gates(7,[(i,(i+1)%7) for i in range(7)],10,unsound=True,timeout=180000);r["name"]="C7"
with p.open("a") as f:f.write(json.dumps(r)+"\n")
print(json.dumps(r),flush=True)
