"""Bit-cost measurements for a compact skeleton; not a complete Lean certificate."""
import json,math
from pathlib import Path
BASE=Path('/tmp/oec/pequalnp-pilot-87/library_route')
def readvar(data,pos):
 value=shift=0
 while True:
  b=data[pos];pos+=1;value|=(b&127)<<shift
  if b<128:return value,pos
  shift+=7
def gamma(n):return 2*(n+1).bit_length()-1
metrics=json.loads((BASE/'certificate-format-metrics.json').read_text());d=(BASE/'witness-shortlist-delta-gaps.bin').read_bytes();pos=0;gamma_bits=rice_bits=0
for _ in range(metrics['expanded_states']):
 count,pos=readvar(d,pos);gaps=[]
 for _ in range(count):v,pos=readvar(d,pos);gaps.append(v)
 gamma_bits += gamma(count)+sum(gamma(v)for v in gaps)
 rice_bits += gamma(count)+3+min(sum((v>>k)+1+k for v in gaps)for k in range(8))
assert pos==len(d)
dag=json.loads((BASE/'signed17-oredge-dag.json').read_text());selected={p:set(x)for p,x in dag['node_ids'].items()};done={};resumes={};nodes={};words={}
for part,name in [('part1','signed17-oredge-trace.jsonl'),('part2','signed17-oredge-part2.jsonl')]:
 with(BASE/name).open()as f:
  for line in f:
   x=json.loads(line);event=x['event']
   if event=='done'and x['id']in selected[part]:done[(part,x['id'])]=(x['kind'],x['a'])
   elif event=='resume':resumes[(part,x['id'])]=('part1',x['source_node'])
   elif event=='signal':words[(part,x['id'])]=int(x['hex'],16)
for part,name in [('part1','signed17-oredge-trace.jsonl'),('part2','signed17-oredge-part2.jsonl')]:
 with(BASE/name).open()as f:
  for line in f:
   x=json.loads(line)
   if x['event']=='node'and x['id']in selected[part]and done[(part,x['id'])][0]in('expand','formula0','formula1','memo'):
    nodes[(part,x['id'])]=x
proofs=sorted(k for k,(kind,_)in done.items()if kind in('expand','formula0','formula1'));proofid={k:i for i,k in enumerate(proofs)};refwidth=(len(proofs)-1).bit_length()
def resolve(key):
 kind,a=done[key]
 if kind=='memo':return resumes[(key[0],a)]if a<0 else(key[0],a)
 return key
def state(key):return tuple(sorted(words[(key[0],i)]for i in nodes[key]['state']))
identity_memos=0
for key,(kind,_)in done.items():
 if kind=='memo'and state(key)==state(resolve(key)):identity_memos+=1
stream=(BASE/'witness-exceptions.bin').read_bytes();pos=0;reference_bits=0;reference_count=0;nonidentity_references=0
for _ in range(metrics['expanded_states']):
 length,pos=readvar(stream,pos);count,pos=readvar(stream,pos);reference_bits+=gamma(length)+gamma(count)
 for _ in range(count):
  gap,pos=readvar(stream,pos);code,pos=readvar(stream,pos);key=('part2'if code&1 else'part1',code>>1);target=resolve(key);assert target in proofid
  transformed=state(key)!=state(target);nonidentity_references+=transformed
  reference_bits+=gamma(gap)+refwidth+1+(7 if transformed else 0);reference_count+=1
assert pos==len(stream)
wirewidth=(metrics['state_truth_functions']-1).bit_length();expanded_bits=0;derived_count=0
for key in proofs:
 if done[key][0]!='expand':continue
 n=nodes[key];derived=sum(not(1<=i<=10)for i in n['state']);derived_count+=derived
 expanded_bits+=refwidth+5+10+4+wirewidth*derived
result=dict(shortlist_gamma_bits=gamma_bits,shortlist_gamma_bytes=(gamma_bits+7)//8,shortlist_rice_bits=rice_bits,shortlist_rice_bytes=(rice_bits+7)//8,reference_count=reference_count,proof_reference_width=refwidth,identity_memos=identity_memos,nonidentity_reference_count=nonidentity_references,reference_gamma_bits=reference_bits,reference_gamma_bytes=(reference_bits+7)//8,expanded_state_packed_bits=expanded_bits,expanded_state_packed_bytes=(expanded_bits+7)//8,expanded_noninput_wire_occurrences=derived_count,shared_truth_function_count=metrics['state_truth_functions'],dictionary_bytes=metrics['shortlist_dictionary_bytes'])
result['binary_skeleton_bytes']=result['shortlist_gamma_bytes']+result['reference_gamma_bytes']+result['expanded_state_packed_bytes']+result['dictionary_bytes']
result['hex_literal_characters_before_overhead']=2*result['binary_skeleton_bytes']
result['limitations']=['Excludes all formula certificates and all Lean helper code.','Truth-function derivation programs, seed histories, exact memo permutation values, decoder proofs and delimiters are not emitted.','Reference bit budget reserves seven bits for each nonidentity permutation; values still need recovery.','This is a format/computation cost study; it is not a checked certificate.']
(BASE/'compact-skeleton-metrics.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
