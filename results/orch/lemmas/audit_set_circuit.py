import hashlib
import itertools
import json
from pathlib import Path

goals=(7,25,42,52)
goalbits=sum(1<<g for g in goals)
initial=sum(1<<s for s in (0,1,2,4,8,16,32))
def members(bits):
    return [i for i in range(64) if bits>>i&1]
def possible(bits):
    values=members(bits)
    result=0
    for a in values:
        for b in values:
            for value in (a|b,a&b,a&(63^b)):
                result|=1<<value
    return result&~bits
def free_goals(bits):
    while True:
        extra=possible(bits)&goalbits
        if not extra:return bits
        bits|=extra
layers=[{free_goals(initial)}]
for budget in range(3):
    following=set()
    for state in layers[-1]:
        additions=possible(state)&~goalbits
        for value in members(additions):following.add(free_goals(state|(1<<value)))
    layers.append(following)
counts=[len(layer) for layer in layers]
maxima=[max((state&goalbits).bit_count() for state in layer) for layer in layers]
assert counts==[1,15,189,2060] and maxima==[0,1,2,3]
assert not any((state&goalbits)==goalbits for layer in layers for state in layer)
report={'status':'PASS','goals':list(goals),'independent_layer_counts':counts,'independent_max_goals':maxima,'layers_sha256':[hashlib.sha256(('\n'.join(map(str,sorted(layer)))+'\n').encode()).hexdigest() for layer in layers],'scope':'Independent bitset implementation of the relaxed singleton-support set-circuit enumeration. Empty-input-normalized binary supports admit union, intersection or ordered difference; goal supports are closed freely, and at most3 non-goal additions cannot produce all4 targets. This is a finite Python calculation, not a Lean theorem or the guarded Petersen lower bound.'}
Path('/tmp/oec/pequalnp-pilot-96/set-circuit-independent-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
