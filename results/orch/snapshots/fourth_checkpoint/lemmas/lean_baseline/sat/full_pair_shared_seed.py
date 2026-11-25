import json
from pathlib import Path

from core_tap_synthesis import truth_columns


def main():
    pack=json.loads(Path(__file__).with_name('full_residual_tap.json').read_text())
    case=pack['cases'][0]
    n=case['inputs']
    edges=[tuple(edge) for edge in pack['edges']]
    gates=[]
    cache={}
    def add(op,a,b):
        key=(op,*sorted((a,b)))
        if key not in cache:
            cache[key]=n+len(gates)
            gates.append(list(key))
        return cache[key]
    def join(xs):
        answer=xs[0]
        for x in xs[1:]: answer=add(1,answer,x)
        return answer
    pairs=[(12,13),(14,19),(20,23)]
    pair_wires={pair:add(1,*pair) for pair in pairs}
    def line_union(lines):
        rest=set(lines)
        wires=[]
        for pair,wire in pair_wires.items():
            if set(pair)<=rest:
                wires.append(wire)
                rest.difference_update(pair)
        wires+=sorted(rest)
        return join(wires)
    merged=[0,1]
    guards={point:[b for a,b in edges if a==point] for point in range(12)}
    union=set(guards[0])|set(guards[1])
    stars=[add(0,join(merged),line_union(union))]
    for point in range(2,12): stars.append(add(0,point,line_union(guards[point])))
    residual=join(stars)
    h_size=len(gates)
    tap=line_union(case['tap_input_indices'])
    assert h_size==56 and len(gates)==58
    original=truth_columns(n)
    wires=original.copy()
    for op,a,b in gates: wires.append((wires[a]|wires[b]) if op else (wires[a]&wires[b]))
    augmented=set(edges)|{(point,line) for point in merged for line in union}
    expected=0
    for a,b in augmented: expected|=original[a]&original[b]
    tap_expected=0
    for line in case['tap_input_indices']: tap_expected|=original[line]
    assert wires[residual]==expected and wires[tap]==tap_expected
    extra=sorted(augmented-set(edges))
    assert len(extra)==6
    result={'gates':gates,'outputs':[residual,tap],'extra_edges':extra,
            'residual_size':h_size,'joint_size':len(gates),'tap_is_correct':True,
            'input_original':pack['input_original']}
    Path(__file__).with_name('full_pair_shared_seed.json').write_text(json.dumps(result))
    full=[]
    for op,a,b in gates: full.append([op,a+1,b+1])
    full.append([0,0,tap+1])
    full.append([1,residual+1,26+len(gates)])
    assert len(full)==60
    Path(__file__).with_name('full_pair_shared_60.json').write_text(json.dumps(full))
    print('EXACT AUGMENTED RESIDUAL',h_size,'gates',len(augmented),'edges',len(extra),'extraedges',
          'joint',len(gates),'fullgraph-overapprox',len(full),'gates',flush=True)
    print('Extra original edges',[(a+1,b+1) for a,b in extra],flush=True)


if __name__=='__main__':
    main()
