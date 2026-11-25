import itertools
import json
from pathlib import Path


def main():
    geometry=json.loads(Path('results/orch/lemmas/circuit_search/geometry.json').read_text())
    original={tuple(edge) for edge in geometry['edges']}
    rows={point:{b for a,b in original if a==point} for point in range(13)}
    tests=[1<<a|1<<b for a,b in sorted(original)]
    tests += [p|(l<<13) for p,l in geometry['maximal_independent_sets']]
    tests += [1<<i for i in range(26)]
    inputs=[sum(1<<j for j,mask in enumerate(tests) if mask>>i&1) for i in range(26)]
    positive=(1<<52)-1
    results=[]
    for p,q in itertools.combinations(range(13),2):
        left=sorted(rows[p]-rows[q])
        right=sorted(rows[q]-rows[p])
        assert len(left)==len(right)==3 and len(rows[p]&rows[q])==1
        for matched in itertools.permutations(right):
            pairs=list(zip(left,matched))
            gates=[]
            def add(op,a,b):
                gates.append([op,*sorted((a,b))])
                return 26+len(gates)-1
            def join(wires):
                result=wires[0]
                for wire in wires[1:]: result=add(1,result,wire)
                return result
            pair_wires=[add(1,*pair) for pair in pairs]
            def line_union(lines):
                rest=set(lines)
                wires=[]
                for pair,wire in zip(pairs,pair_wires):
                    if set(pair)<=rest:
                        wires.append(wire)
                        rest.difference_update(pair)
                return join(wires+sorted(rest))
            stars=[add(0,add(1,p,q),line_union(rows[p]|rows[q]))]
            for point in range(13):
                if point not in (p,q): stars.append(add(0,point,line_union(rows[point])))
            output=join(stars)
            assert len(gates)==60 and output==85
            assert all(op in (0,1) and 0<=a<26+i and 0<=b<26+i
                       for i,(op,a,b) in enumerate(gates))
            extra=sorted({(p,b) for b in rows[q]-rows[p]}|
                         {(q,b) for b in rows[p]-rows[q]})
            assert len(extra)==6 and not original&set(extra)
            expected=positive
            for a,b in extra: expected |= inputs[a]&inputs[b]
            wires=inputs.copy()
            for op,a,b in gates:
                wires.append((wires[a]|wires[b]) if op else (wires[a]&wires[b]))
            assert wires[output]==expected
            assert wires[output]&positive==positive
            assert wires[output]>>(52+704)==0
            results.append({'points':[p,q],'pairs':pairs,'gates':gates,
                            'output':output,'size':60,'extra_edges':extra,
                            'positive_errors':0,'negative_errors':(expected>>52).bit_count(),
                            'singleton_errors':0,'pair_errors':6})
    assert len(results)==468
    path=Path(__file__).with_name('full_pair_shared_family.json')
    path.write_text(json.dumps(results))
    print('FULL60 PAIR FAMILY',len(results),'seeds',
          'negative-basis-errors',sorted({r['negative_errors'] for r in results}),
          'all52positives/all704negatives/all26singletons verified against explicitaugmentedgraph',flush=True)


if __name__=='__main__':
    main()
