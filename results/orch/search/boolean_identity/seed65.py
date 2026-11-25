import json
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from exact_rewrite import D, ARCHIVE, N, TARGET, INPUT, patterns, plane, graft, evaluate
source=json.loads((ARCHIVE/'q3-concurrent-control/control.json').read_text())
net=source['circuit']
# In control gate36 is x0 OR x6, gate37 is x0 OR y10, gate38 is their product.
assert net[36:39]==[[False,0,6],[False,0,23],[True,62,63]]
c=graft(net,38,(0,0,(1,6,23))); assert len(c)==65

def bad_edges(c):
    a=[v&TARGET if i<13 else 0 for i,v in enumerate(INPUT)]
    b=[v&TARGET if i>=13 else 0 for i,v in enumerate(INPUT)]
    both=[0]*26
    for op,i,j in c:
        x,y,z=(0,0,(a[i]&b[j])|(a[j]&b[i])) if op else (a[i]|a[j],b[i]|b[j],both[i]|both[j])
        a.append(x); b.append(y); both.append(z)
    return [list(pair) for i,pair in enumerate(plane.EDGES) if not (both[-1]>>i)&1]
assert plane.evaluate(c,patterns)==TARGET
assert bad_edges(c)==[[6,23]]
if __name__=='__main__':
    result={'gate_count':len(c),'non_read1_pairs':bad_edges(c),'positive_pairs':52,'maximal_independent_negatives':704,'boundary_errors':(evaluate(c)[-1]^TARGET).bit_count(),'distinguished_flag':[0,23],'circuit':c}
    (D/'direct65-control.json').write_text(json.dumps(result,indent=2)+'\n')
    print({k:v for k,v in result.items() if k!='circuit'})
