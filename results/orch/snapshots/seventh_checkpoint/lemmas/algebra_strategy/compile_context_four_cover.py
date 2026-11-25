"""Materialize bounded-cover outputs in the existing fixed-prefix packet."""
import argparse,json
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('kind',choices=['subset','all21','errors'])
args=parser.parse_args()
HERE=Path(__file__).resolve().parent
case=json.loads((HERE.parent/'circuit_search/context-four-owner-packet.json').read_text())[0]
cover=json.loads((HERE/f'context-four-cover-joint-{args.kind}.json').read_text())
features={tuple(sorted(f['raw_indices'])):14+i for i,f in enumerate(case['features'])}
gates=[];cache={}
def gate(op,a,b):
    if a==b:return a
    key=(op,*sorted((a,b)))
    if key not in cache:
        cache[key]=29+len(gates);gates.append(list(key))
    return cache[key]
def union(ws):
    ws=list(dict.fromkeys(ws));w=ws[0]
    for b in ws[1:]:w=gate(1,w,b)
    return w
terms=[]
for box in cover['selected_rectangles']:
    left=union(box['rows'])
    chunks=[x['support'][0] if len(x['support'])==1 else features[tuple(sorted(x['support']))] for x in box['chunks']]
    terms.append(gate(0,left,union(chunks)))
output=union(terms)
N=1<<14
values=[int(('1'*(1<<i)+'0'*(1<<i))*(N//(2<<i)),2) for i in range(14)]
for feature in case['features']:
    v=0
    for j in feature['raw_indices']:v|=values[j]
    values.append(v)
for op,a,b in gates:values.append(values[a]|values[b] if op else values[a]&values[b])
actual=values[output];target=0
for a,b in case['edges']:target|=values[a]&values[b]
expected=0
for a,b in cover['achieved_edges']:expected|=values[a]&values[b]
assert actual==expected
result={'gates':gates,'output':output,'inputs':29,'raw_inputs':14,
        'packet':'circuit_search/context-four-owner-packet.json','packet_index':0,
        'gate_count':len(gates),'and_count':sum(g[0]==0 for g in gates),
        'false_negatives':(target&~actual).bit_count(),'false_positives':(actual&~target).bit_count(),
        'boundary_errors':[x for x,y in case['raw_tests'] if (actual>>x&1)!=y],
        'extra_minimal_terms':cover['achieved_extra_edges'],
        'source_cover':f'context-four-cover-joint-{args.kind}.json',
        'status':'Incorrect approximation: all16384 raw assignments checked against achieved augmented function.'}
(HERE/f'context-four-cover-{args.kind}-seed.json').write_text(json.dumps(result,indent=2)+'\n')
print('gates',len(gates),'AND',result['and_count'],'FP',result['false_positives'],'boundary',len(result['boundary_errors']))
