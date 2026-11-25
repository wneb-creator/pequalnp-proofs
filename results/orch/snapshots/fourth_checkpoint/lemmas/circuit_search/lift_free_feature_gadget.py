import argparse
import json
import pathlib

parser=argparse.ArgumentParser(description='Lift an exact free-prefix gadget to the original26-input plane.')
parser.add_argument('packet',type=pathlib.Path)
parser.add_argument('case',type=int)
parser.add_argument('gadget',type=pathlib.Path)
parser.add_argument('output',type=pathlib.Path)
args=parser.parse_args()
cases=json.loads(args.packet.read_text())
case=cases[args.case]
raw=json.loads(args.gadget.read_text())
gadget=raw['gates'] if isinstance(raw,dict) else raw
n=case['inputs']
gadget_output=raw.get('output',n+len(gadget)-1) if isinstance(raw,dict) else n+len(gadget)-1
assert len(gadget)<=case['max_gates']
combined=[g.copy() for g in case['outside_gates']]
mapping={i:original for i,original in enumerate(case['input_original'])}
for i,feature in enumerate(case['features'],case['raw_inputs']):mapping[i]=feature['outside_wire']
for i,(op,a,b) in enumerate(gadget):
    op={'and':0,'or':1}.get(op,op)
    assert op in (0,1) and 0<=a<n+i and 0<=b<n+i
    output=26+len(combined)
    combined.append([op,mapping[a],mapping[b]])
    mapping[n+i]=output
combined.append([1,case['outside_output'],mapping[gadget_output]])
assert len(combined)<=63
here=pathlib.Path(__file__).resolve().parent
plane=json.loads((here/'full-case.json').read_text())
errors=[0,0]
for mask,label in plane['tests']:
    values=[mask>>i&1 for i in range(26)]
    for i,(op,a,b) in enumerate(combined):
        assert op in (0,1) and 0<=a<26+i and 0<=b<26+i
        values.append(values[a]|values[b] if op else values[a]&values[b])
    if values[-1]!=label:errors[not label]+=1
assert errors==[0,0],errors
args.output.write_text(json.dumps(combined,indent=2)+'\n')
validation=dict(case=case['name'],gates=len(combined),inputs=26,positive_misses=errors[0],maximal_negative_errors=errors[1])
args.output.with_suffix('.validation.json').write_text(json.dumps(validation,indent=2)+'\n')
print(validation)
