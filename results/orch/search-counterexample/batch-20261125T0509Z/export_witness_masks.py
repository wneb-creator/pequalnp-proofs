import argparse
import json
from pathlib import Path

ap=argparse.ArgumentParser()
ap.add_argument('witness')
ap.add_argument('output')
args=ap.parse_args()
base=Path('/tmp/oec/pequalnp-pilot-62')
witness=json.loads(Path(args.witness).read_text())
assert witness['input_count']==26
geometry=json.loads((base/'geometry-data.json').read_text())
positive=[(1<<((line+offset)%13))|(1<<(13+line))
          for line in range(13) for offset in [0,1,3,9]]
negative=[q['S']|(q['D']<<13) for q in geometry['generic']]
assert len(positive)==52 and len(set(positive))==52 and len(negative)==468
samples=positive+negative
full=(1<<520)-1
values=[sum(bool(q>>i&1)<<j for j,q in enumerate(samples)) for i in range(26)]
inputs=values.copy()
def conjunction(refs):
 value=full
 for ref in refs:
  assert 0<=ref<len(values)
  value &= values[ref]
 return value
for left,right in witness['operand_wire_lists']:
 values.append(conjunction(left)|conjunction(right))
output=conjunction(witness['output_wire_list'])
assert output==(1<<52)-1
result={'sample_count':520,'positive_count':52,'negative_count':468,
        'input_masks':inputs,'or_masks':values[26:],'output_mask':output,
        'positive_samples':positive,'negative_samples':negative,
        'positive_order':'Flags.flag: line then offsets0,1,3,9',
        'negative_order':'geometry-data.json.generic; AllRows flatindex13*r.1+r.2',
        'source_witness':str(Path(args.witness))}
Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'input_masks':len(inputs),'or_masks':len(values)-26,'sample_count':520,
                  'output_is_exact_positive_bits':output==(1<<52)-1}))
