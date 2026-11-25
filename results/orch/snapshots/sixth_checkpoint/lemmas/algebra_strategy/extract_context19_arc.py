"""Extract a sufficient-packet approximation; no exactness claim."""
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
SEARCH=HERE.parent/'circuit_search'
source=json.loads((HERE/'feature6-seven19-absorbed.json').read_text())
old_packet=json.loads((SEARCH/'six-owner-gadgets.json').read_text())[1]
packet=json.loads((SEARCH/'context-four-owner-packet.json').read_text())[0]
raw_to_old=[0,2,3,5,7,6,13,10,11,15,9,16,14,8]
old_to_raw={old:new for new,old in enumerate(raw_to_old)}
supports=[frozenset(x['raw_indices']) for x in packet['features']]
memo={1:None,4:None}
out=[]
cache={}
def translate(w):
    if w in memo:return memo[w]
    if w<17:
        assert w in old_to_raw,('unsupported raw input',w)
        answer=old_to_raw[w]
    elif w<30:
        raw=old_packet['features'][w-17]['raw_indices']
        assert all(i in old_to_raw for i in raw),raw
        support=frozenset(old_to_raw[i] for i in raw)
        assert support in supports,('unavailable feature',support)
        answer=14+supports.index(support)
    else:
        op,a,b=source[w-30]
        a=translate(a)
        if not op and a is None:
            answer=None
        else:
            b=translate(b)
            if a is None or b is None:
                answer=(b if a is None else a) if op else None
            elif a==b:
                answer=a
            else:
                key=(op,*sorted((a,b)))
                if key not in cache:
                    cache[key]=29+len(out)
                    out.append(list(key))
                answer=cache[key]
    memo[w]=answer
    return answer
output=translate(52)

n=1<<14
cols=[int(('1'*(1<<i)+'0'*(1<<i))*(n//(2<<i)),2) for i in range(14)]
for feature in packet['features']:
    v=0
    for i in feature['raw_indices']:v|=cols[i]
    cols.append(v)
for op,a,b in out:cols.append(cols[a]|cols[b] if op else cols[a]&cols[b])
actual=cols[output]
old_cols=[0]*17
for new,old in enumerate(raw_to_old):old_cols[old]=cols[new]
for feature in old_packet['features']:
    v=0
    for i in feature['raw_indices']:v|=old_cols[i]
    old_cols.append(v)
for op,a,b in source:old_cols.append(old_cols[a]|old_cols[b] if op else old_cols[a]&old_cols[b])
assert actual==old_cols[52]
expected=0
for u,v in packet['edges']:expected|=cols[u]&cols[v]
extras=[]
for raw in range(n):
    if (actual>>raw)&1 and all(not ((actual>>(raw^(1<<i)))&1) for i in range(14) if (raw>>i)&1):
        term=[i for i in range(14) if (raw>>i)&1]
        if term not in packet['edges']:extras.append(term)
errors=[raw for raw,want in packet['raw_tests'] if ((actual>>raw)&1)!=want]
data={'gates':out,'output':output,'inputs':29,'raw_inputs':14,
      'packet':'circuit_search/context-four-owner-packet.json','packet_index':0,
      'source':'algebra_strategy/feature6-seven19-absorbed.json','source_output':52,
      'raw_to_source':raw_to_old,'source_gate_map':{str(k):v for k,v in memo.items() if k>=30},
      'gate_count':len(out),'and_count':sum(g[0]==0 for g in out),
      'false_negatives':(expected&~actual).bit_count(),
      'false_positives':(actual&~expected).bit_count(),
      'boundary_errors':errors,'extra_minimal_terms':extras,
      'status':'Approximation in a sufficient full-lift packet; not an exact witness.'}
(HERE/'context19-four-owner-seed.json').write_text(json.dumps(data,indent=2)+'\n')
print('paid gates',len(out),'AND',data['and_count'])
print('all16384 source equality checked; errors',data['false_negatives'],data['false_positives'])
print('boundary errors',len(errors),'extra primes',extras)
