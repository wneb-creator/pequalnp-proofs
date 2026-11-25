import argparse
import hashlib
import json
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument('witness')
ap.add_argument('output')
ap.add_argument('--scenario',choices=['cap4','collinear3'],default='cap4')
args = ap.parse_args()
base = Path('/tmp/oec/pequalnp-pilot-62')
source = Path(args.witness)
witness = json.loads(source.read_text())
data = json.loads((base/(args.scenario+'-full-truth.json')).read_text())
vertices = data['vertices']
n = len(vertices)
k = witness['or_count']
assert witness['input_count'] == n and 1 <= k <= len(data['positive_edges'])-1
ops = witness['operand_wire_lists']
out = witness['output_wire_list']
assert len(ops) == k
for g,branches in enumerate(ops):
    assert len(branches) == 2
    assert all(type(i) is int and 0 <= i < n+g for branch in branches for i in branch)
assert all(type(i) is int and 0 <= i < n+k for i in out)
def evaluate(q,count,operations,output):
    values = [bool(q>>i&1) for i in range(count)]
    for a,b in operations:
        values.append(all(values[i] for i in a) or all(values[i] for i in b))
    return all(values[i] for i in output)
local_values = [evaluate(q,n,ops,out) for q in range(1<<n)]
positive = data['positive_edges']
negative = data['maximal_negative_masks']
for q,value in enumerate(local_values):
    if any(q&p == p for p in positive): assert value
    if any(q&~r == 0 for r in negative): assert not value
def mapped(i): return vertices[i] if i < n else 26+i-n
global_ops = [[[mapped(i) for i in branch] for branch in pair] for pair in ops]
global_out = [mapped(i) for i in out]
global_edges = [(p,13+l) for p in range(13) for l in range(13) if (p-l)%13 in (0,1,3,9)]
remaining = [(p,l) for p,l in global_edges if not(p in vertices and l in vertices)]
assert len(remaining) == 52-len(positive)
for p,l in remaining:
    global_ops.append([global_out,[p,l]])
    global_out = [26+len(global_ops)-1]
assert len(global_ops) == k+len(remaining)
geometry = json.loads((base/'geometry-data.json').read_text())
generic = [r['S']|(r['D']<<13) for r in geometry['generic']]
global_positive = [(1<<p)|(1<<l) for p,l in global_edges]
checks = [(q,True) for q in global_positive]+[(q,False) for q in generic]+[(1<<i,False) for i in range(26)]+[(0,False)]
for q,value in checks: assert evaluate(q,26,global_ops,global_out) == value
result = {'scenario':'global','input_count':26,'or_count':len(global_ops),
          'operand_wire_lists':global_ops,'output_wire_list':global_out,
          'source_local_witness':str(source),'source_local_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
          'local_vertices':vertices,'local_or_count':k,'local_full_assignment_checks':1<<n,
          'checked_positive_samples':52,'checked_generic_negatives':468,
          'checked_singleton_negatives':26,'checked_empty_negative':True,
          'is_global_counterexample_candidate':len(global_ops)<=50}
Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({key:result[key] for key in ['or_count','local_or_count','local_full_assignment_checks','checked_positive_samples','checked_generic_negatives','checked_singleton_negatives','checked_empty_negative','is_global_counterexample_candidate']}))
