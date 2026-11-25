import ast
import json
import re
from pathlib import Path

from grid_taps_synthesis import evaluate_wires


def main():
    statement=json.loads(Path('/tmp/oec/pequalnp-pilot-57/assigned-gap.json').read_text())['gap']['statement']
    full=ast.literal_eval(re.search(r'\(\[(.*?)\] : List',statement).group(0).split(' : List')[0][1:])
    edges=[(a-1,b-1) for a,b in full if a!=0]
    n,k=25,12
    tap=[b-1 for a,b in full if a==0]
    assert len(edges)==48 and tap==[12,13,15,21]
    line_mask=sum(1<<i for i in range(k,n))
    neighbors=[sum(1<<b for a,b in edges if a==point) for point in range(k)]
    qmask=sum(1<<i for i in tap)
    def hit(mask):
        return any(mask>>a&1 and mask>>b&1 for a,b in edges)
    def maxima(forbidden):
        result=set()
        for points in range(1<<k):
            excluded=0
            for point in range(k):
                if points>>point&1: excluded |= neighbors[point]
            lines=line_mask&~excluded&~forbidden
            closure=sum(1<<point for point in range(k) if not neighbors[point]&lines)
            mask=closure|lines
            assert not hit(mask) and not mask&forbidden
            assert all(hit(mask|1<<i) for i in range(n)
                       if not mask>>i&1 and not forbidden>>i&1)
            result.add(mask)
        return result
    negative=maxima(0)
    tap_zero=maxima(qmask)
    positive={1<<a|1<<b for a,b in edges}
    masks=sorted(positive|negative|tap_zero|{1<<i for i in tap})
    constraints=[{'input':mask,'residual':hit(mask),'tap':None if hit(mask) else bool(mask&qmask)}
                 for mask in masks]
    gates=[]
    def add(op,a,b):
        gates.append([op,*sorted((a,b))])
        return n+len(gates)-1
    def join(xs):
        result=xs[0]
        for x in xs[1:]: result=add(1,result,x)
        return result
    stars=[]
    for point in range(k):
        stars.append(add(0,point,join([b for a,b in edges if a==point])))
    residual=join(stars)
    assert len(gates)==59
    tap_output=join(tap)
    assert len(gates)==62
    for row in constraints:
        values=evaluate_wires(gates,row['input'],n)
        assert values[residual]==row['residual']
        if row['tap'] is not None: assert values[tap_output]==row['tap']
    case={'name':'full_point0_residual_tap','inputs':n,'max_gates':61,
          'outside_original_point':0,'tap_input_indices':tap,
          'tap_original_lines':[i+1 for i in tap],
          'tap_zero_maxima':sorted(tap_zero),'constraints':constraints,
          'completion_additional_gates':2,'residual_target_gates':58,
          'residual_completion_gate_cost':5,
          'seed':{'gates':gates,'residual_output':residual,'tap_output':tap_output}}
    pack={'description':'Full25-input residual and conditional four-line tap for R_meta_650_517',
          'input_original':list(range(1,26)),'edges':edges,'cases':[case]}
    path=Path(__file__).with_name('full_residual_tap.json')
    path.write_text(json.dumps(pack,indent=2))
    print('FULL RESIDUAL TAP',len(positive),'positive',len(negative),'maximal-negative',
          len(tap_zero),'tap-zero-maxima',len(constraints),'total-care-tests',
          len(gates),'baseline-gates',flush=True)


if __name__=='__main__':
    main()
