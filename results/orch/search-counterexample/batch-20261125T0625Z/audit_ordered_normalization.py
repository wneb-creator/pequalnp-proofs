import ast,json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-62')
src=ast.parse((base/'global_ordered_cnf.py').read_text());node=next(n for n in src.body if isinstance(n,ast.FunctionDef) and n.name=='normalize_adjacent_order');scope={};exec(compile(ast.Module(body=[node],type_ignores=[]),'normalizer','exec'),scope);normalize=scope['normalize_adjacent_order']
mapping=json.loads((base/'global-50-dirty-cover36-900.mapping.json').read_text());samples=mapping['positive_samples']+mapping['negative_samples'];np=52;pm=(1<<np)-1;full=(1<<len(samples))-1
inputs=[sum(bool(q>>i&1)<<j for j,q in enumerate(samples)) for i in range(26)]
def decode(pairs):
 values=inputs.copy();operations=[]
 for pair in pairs:
  branches=[];refs=[]
  for sig in pair:
   chosen=[i for i,v in enumerate(values) if v&sig==sig]
   assert chosen
   value=full
   for i in chosen:value &= values[i]
   assert value&pm==sig
   branches.append(value);refs.append(chosen)
  operations.append(refs);values.append(branches[0]|branches[1])
 output_refs=[i for i,v in enumerate(values) if v&pm==pm];assert output_refs
 output=full
 for i in output_refs:output &= values[i]
 return output,{'input_count':26,'or_count':len(pairs),'operand_wire_lists':operations,'output_wire_list':output_refs,'operand_signatures':pairs}
reports=[]
for stem,filename in [('ordered-baseline51','repair-fixed51-stream-control.witness.json'),('ordered-marginal48','pg3-marginal48-canonical-invalid.json')]:
 witness=json.loads((base/filename).read_text());values=inputs.copy();pairs=[]
 for a,b in witness['operand_wire_lists']:
  terms=[]
  for refs in [a,b]:
   v=full
   for i in refs:v &= values[i]
   terms.append(v)
  pairs.append(sorted([t&pm for t in terms]));values.append(terms[0]|terms[1])
 original,_=decode(pairs);ordered,swaps=normalize(pairs);current=[p.copy() for p in pairs];previous=original
 for a,b in swaps:
  current[a],current[b]=current[b],current[a]
  output,_=decode(current);assert output&pm==pm and output&~previous==0;previous=output
 assert current==ordered and current[0]==pairs[0]
 final,program=decode(ordered);assert final==previous
 program.update({'source_witness':filename,'ordering_swaps':swaps,'full_generic_negative_errors':((final>>52)&((1<<468)-1)).bit_count(),'full_singleton_errors':(final>>520).bit_count(),'is_global_counterexample_candidate':len(pairs)<=50 and final==pm,'scope':'Finite ordering control; source invalidity remains unless full sample check passes'})
 (base/(stem+'.json')).write_text(json.dumps(program,indent=2)+'\n')
 reports.append({'source':filename,'or_count':len(pairs),'swaps':len(swaps),'negative_errors_before':(original&~pm).bit_count(),'negative_errors_after':(final&~pm).bit_count(),'candidate':program['is_global_counterexample_candidate']})
(base/'ordered-normalization-audit.json').write_text(json.dumps(reports,indent=2)+'\n');print(reports)
