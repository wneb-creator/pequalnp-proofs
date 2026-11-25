import argparse
import json
from pathlib import Path


def construct(point):
    n = 13
    differences = {0, 1, 3, 9}
    assert point not in differences
    incident = lambda p,l: (p-l) % n in differences
    lines_in = [l for l in range(n) if incident(point,l)]
    lines_out = [l for l in range(n) if not incident(point,l)]
    gates = []
    labels = []

    def gate(op,a,b,label):
        assert a != b and max(a,b) < 26+len(gates)
        gates.append([op,min(a,b),max(a,b)])
        labels.append(label)
        return 25+len(gates)

    def merge(wires,label):
        wires = list(wires)
        while len(wires) > 1:
            a,b = wires.pop(0),wires.pop(0)
            wires.append(gate(0,a,b,label))
        return wires[0]

    outer_stars = []
    for l in lines_out:
        leaves = merge([p for p in range(n) if incident(p,l)],f'outer leaf sum line {l}')
        outer_stars.append(gate(1,13+l,leaves,f'outer star line {l}'))
    a_out = merge(outer_stars,'outer star aggregation')
    assert len(gates) == 44
    inner_stars = []
    for l in lines_in:
        leaves = merge([p for p in range(n) if p != point and incident(p,l)],f'inner leaf sum line {l}')
        inner_stars.append(gate(1,13+l,leaves,f'inner star line {l}'))
    a_in = merge(inner_stars,'inner star aggregation')
    assert len(gates) == 59
    line_sum = merge([13+l for l in lines_in],'incident line sum')
    first = gate(0,point,a_out,'point OR outer part')
    first = gate(0,first,a_in,'first factor')
    second = gate(0,line_sum,a_out,'second factor')
    output = gate(1,first,second,'distributed final AND')
    assert len(gates) == 66

    edges = [(p,13+l) for p in range(n) for l in range(n) if incident(p,l)]
    neighborhood = [sum(1<<l for l in range(n) if incident(p,l)) for p in range(n)]
    negatives = []
    for points in range(1<<n):
        touched = 0
        for p in range(n):
            if (points>>p)&1:
                touched |= neighborhood[p]
        lines = ((1<<n)-1)^touched
        closure = sum(1<<p for p in range(n) if neighborhood[p]&lines == 0)
        if closure == points:
            negatives.append(points|(lines<<n))

    def scalar(mask):
        values = [bool((mask>>i)&1) for i in range(26)]
        for op,a,b in gates:
            values.append((values[a] and values[b]) if op else (values[a] or values[b]))
        return values

    def derivative(base,seed):
        values = scalar(1<<base)
        d = [i==seed for i in range(26)]
        for op,a,b in gates:
            d.append(((values[a] and d[b]) or (d[a] and values[b])) if op else (d[a] or d[b]))
        return d[-1]

    assert len(edges)==52 and len(negatives)==704
    assert all(scalar((1<<a)|(1<<b))[-1] for a,b in edges)
    assert all(not scalar(m)[-1] for m in negatives)
    assert not derivative(0,13) and not derivative(13,0)
    assert sum(op for op,a,b in gates)==14
    return dict(description='Alternative 66-gate exact incidence circuit; not a counterexample to posted64',
                chosen_point=point,lines_in=lines_in,lines_out=lines_out,inputs=26,output=output,
                gates=gates,gate_labels=labels,and_count=14,or_count=52,
                component_wires=dict(a_out=a_out,a_in=a_in,line_sum=line_sum),
                verified_positive_edges=52,verified_maximal_independent_sets=704,
                derivatives=[False,False],formula='(p OR A_out OR A_in) AND (L OR A_out)')


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--point',type=int,default=4)
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    result=construct(args.point)
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['gates','gate_labels']}))
