import argparse
import json
from pathlib import Path

ap=argparse.ArgumentParser()
ap.add_argument('witness')
ap.add_argument('mapping')
ap.add_argument('output')
ap.add_argument('--embed-theta4',action='store_true')
args=ap.parse_args()
base=Path('/tmp/oec/pequalnp-pilot-62')
witness=json.loads(Path(args.witness).read_text())
mapping=json.loads(Path(args.mapping).read_text())
n=witness['input_count']
operations=witness['operand_wire_lists']
output=witness['output_wire_list']
assert len(operations)==witness['or_count']
samples=list(range(1<<n)) if n<=12 else mapping['positive_samples']+mapping['negative_samples']
full=(1<<len(samples))-1
def initial_values(count,rows):
 return [sum(bool(q>>i&1)<<j for j,q in enumerate(rows)) for i in range(count)]
def conjunction(values,refs,mask):
 value=mask
 for ref in refs:
  assert 0<=ref<len(values)
  value &= values[ref]
 return value
def evaluate(count,ops,out,rows):
 mask=(1<<len(rows))-1
 values=initial_values(count,rows)
 for a,b in ops:values.append(conjunction(values,a,mask)|conjunction(values,b,mask))
 return values,conjunction(values,out,mask)
original_values,original_output=evaluate(n,operations,output,samples)
def shrink(refs,available):
 target=conjunction(available,refs,full)
 uncovered=full^target
 selected=[]
 candidates=sorted(set(refs))
 while uncovered:
  ref=max(candidates,key=lambda r:((uncovered&~available[r]).bit_count(),-r))
  assert uncovered&~available[ref]
  selected.append(ref)
  candidates.remove(ref)
  uncovered &= available[ref]
 for ref in selected.copy():
  without=[r for r in selected if r!=ref]
  if conjunction(available,without,full)==target:selected=without
 assert conjunction(available,selected,full)==target
 return sorted(selected)
compact=[]
for g,(a,b) in enumerate(operations):
 compact.append([shrink(a,original_values[:n+g]),shrink(b,original_values[:n+g])])
compact_output=shrink(output,original_values)
values,value=evaluate(n,compact,compact_output,samples)
assert values==original_values and value==original_output
reachable=set()
def visit(ref):
 if ref<n:return
 g=ref-n
 if g in reachable:return
 reachable.add(g)
 for side in compact[g]:
  for predecessor in side:visit(predecessor)
for ref in compact_output:visit(ref)
order=sorted(reachable)
renaming={n+g:n+i for i,g in enumerate(order)}
def rename(ref):return ref if ref<n else renaming[ref]
compact=[[[rename(r) for r in side] for side in compact[g]] for g in order]
compact_output=[rename(r) for r in compact_output]
_,value=evaluate(n,compact,compact_output,samples)
assert value==original_output
reduced_local_or_count=len(compact)
if args.embed_theta4:
 assert n==10 and witness['scenario']=='theta4'
 embedding=[2,0,1,3,9,13,25,14,15,19]
 def global_ref(ref):return embedding[ref] if ref<10 else 26+ref-10
 compact=[[[global_ref(r) for r in side] for side in operation] for operation in compact]
 compact_output=[global_ref(r) for r in compact_output]
 global_data=json.loads((base/'global-first-or-symmetry.json').read_text())
 local_edges={sum((q>>i&1)<<embedding[i] for i in range(10)) for q in mapping['positive_samples']}
 remaining=[q for q in global_data['positive_samples'] if q not in local_edges]
 assert len(local_edges)==12 and len(remaining)==40
 for q in remaining:
  edge=[i for i in range(26) if q>>i&1]
  assert len(edge)==2
  new_ref=26+len(compact)
  compact.append([compact_output,edge])
  compact_output=[new_ref]
 n=26
 mapping={'positive_samples':global_data['positive_samples'],
          'negative_samples':global_data['negative_samples']+[1<<i for i in range(26)]}
checked=mapping['positive_samples']+mapping['negative_samples']
_,truth=evaluate(n,compact,compact_output,checked)
assert truth==(1<<len(mapping['positive_samples']))-1
result={'input_count':n,'or_count':len(compact),'operand_wire_lists':compact,
        'output_wire_list':compact_output,'source_witness':str(Path(args.witness)),
        'source_or_count':witness['or_count'],'reduced_local_or_count':reduced_local_or_count,
        'checked_positive_samples':len(mapping['positive_samples']),
        'checked_negative_samples':len(mapping['negative_samples']),
        'is_global_counterexample_candidate':n==26 and len(compact)<=50,
        'lean_checked':False}
Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['operand_wire_lists','output_wire_list']}))
