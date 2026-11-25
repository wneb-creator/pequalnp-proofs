"""Restrict the four-owner cone of the 27-gate six-feature approximation.

This is a search phase only: restriction does not establish restoration.
"""
import argparse
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SEARCH = HERE.parent / "circuit_search"
parser=argparse.ArgumentParser()
parser.add_argument("--source",default=str(SEARCH / "feature6-context-27g-best-25.json"))
parser.add_argument("--output",type=int,default=46)
parser.add_argument("--tag",default="context27-four-owner-kernel")
args=parser.parse_args()
gates = json.loads(Path(args.source).read_text())
packet = json.loads((SEARCH / "six-owner-gadgets.json").read_text())[1]
case = json.loads((SEARCH / "four-owner-private-zero-kernel.json").read_text())

# The four-owner cone ends at old wire 46; raw points [0,2,3,5] form an arc.
# Kernel line indices [4,5,6,7,8,9] stand for pairs 01,02,03,23,13,12.
raw_map = {0: 0, 2: 1, 3: 2, 5: 3, 7: 4, 6: 5,
           13: 6, 10: 7, 11: 8, 15: 9}
private = [9, 16, 14, 8]
zeroed = set(private + [1, 4, 12])
feature_supports = [{5, 8}, {4, 7}, {6, 9}]
wire_map = {}
records = []
for old in range(17):
    wire_map[old] = raw_map.get(old)
for i, feature in enumerate(packet["features"]):
    support = {raw_map[x] for x in feature["raw_indices"] if x in raw_map}
    if not support:
        new = None
    elif len(support) == 1:
        new = next(iter(support))
    else:
        assert support in feature_supports, support
        new = 10 + feature_supports.index(support)
    wire_map[17 + i] = new
    records.append({"old_wire": 17+i, "old_support": feature["raw_indices"],
                    "restricted_support": sorted(support), "new_wire": new})

new_gates = []
hashes = {}
for i, (op, a, b) in enumerate(gates):
    if 30+i > args.output:
        break
    a, b = wire_map[a], wire_map[b]
    if a is None or b is None:
        new = (b if a is None else a) if op else None
    elif a == b:
        new = a
    else:
        a, b = sorted((a, b))
        key = op, a, b
        if key not in hashes:
            hashes[key] = 13 + len(new_gates)
            new_gates.append(list(key))
        new = hashes[key]
    wire_map[30+i] = new
output = wire_map[args.output]

# Remove any now-unused gates and renumber deterministically.
live = set()
def visit(w):
    if w < 13 or w in live:
        return
    live.add(w)
    _, a, b = new_gates[w-13]
    visit(a)
    visit(b)
visit(output)
renaming = {i:i for i in range(13)}
pruned = []
for i,g in enumerate(new_gates):
    if 13+i in live:
        op,a,b=g
        renaming[13+i]=13+len(pruned)
        pruned.append([op,renaming[a],renaming[b]])
output=renaming[output]

def evaluate(raw):
    bits=[(raw>>i)&1 for i in range(10)]
    for s in feature_supports:
        bits.append(int(any(bits[x] for x in s)))
    for op,a,b in pruned:
        bits.append((bits[a]|bits[b]) if op else (bits[a]&bits[b]))
    return bits[output]

def target(raw):
    return int(any((raw>>a)&1 and (raw>>b)&1 for a,b in case["edges"]))

wrong_pos=[]
wrong_neg=[]
primes=[]
for raw in range(1<<10):
    original=[0]*17
    for old,new in raw_map.items():
        original[old]=(raw>>new)&1
    values=original[:]
    for feature in packet["features"]:
        values.append(int(any(original[x] for x in feature["raw_indices"])))
    for op,a,b in gates:
        values.append((values[a]|values[b]) if op else (values[a]&values[b]))
    assert evaluate(raw)==values[args.output],raw
    actual, expected=evaluate(raw),target(raw)
    if actual and not expected:
        wrong_neg.append(raw)
    if expected and not actual:
        wrong_pos.append(raw)
    if actual and all(not evaluate(raw^(1<<i)) for i in range(10) if (raw>>i)&1):
        primes.append([i for i in range(10) if (raw>>i)&1])
boundary_errors=[raw for raw,expected in case["raw_tests"] if evaluate(raw)!=expected]
result={
    "gates":pruned,"output":output,"inputs":13,"raw_inputs":10,
    "source":args.source,
    "source_output":args.output,"source_points":[0,2,3,5],
    "source_private_lines":private,
    "kernel_to_source":[0,2,3,5,7,6,13,10,11,15],
    "source_zeroed_raw":sorted(zeroed),"feature_substitutions":records,
    "gate_count":len(pruned),"and_count":sum(g[0]==0 for g in pruned),
    "full_false_negatives":wrong_pos,"full_false_positives":wrong_neg,
    "boundary_errors":boundary_errors,"minimal_terms":primes,
    "extra_minimal_terms":[p for p in primes if p not in case["edges"]],
    "status":"Approximation phase only. No exactness or restoration claim."
}
out=HERE/(args.tag+".json")
out.write_text(json.dumps(result,indent=2)+"\n")
print("gates",len(pruned),"AND",result["and_count"])
print("full errors",len(wrong_pos),len(wrong_neg))
print("boundary errors",len(boundary_errors))
print("extra minimal terms",result["extra_minimal_terms"])
print("written",out)
