import argparse
import heapq
import json
import time


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('rows')
    parser.add_argument('--output', required=True)
    parser.add_argument('--seconds', type=float, default=2)
    parser.add_argument('--formula-limit', type=int, default=10)
    args = parser.parse_args()
    with open(args.rows) as source:
        data = json.load(source)
    assert isinstance(data, dict) and isinstance(data['rows'], list)
    rows = data['rows']
    ninputs = data['cut_inputs']
    signatures = [sum(row['cuts'][i] << j for j,row in enumerate(rows)) for i in range(ninputs)]
    target = sum(row['value'] << j for j,row in enumerate(rows))
    dist, expression, heap = {}, {}, []
    for i,signature in enumerate(signatures):
        if signature not in dist:
            dist[signature] = 0
            expression[signature] = ('input',i)
            heapq.heappush(heap,(0,signature))
    settled = {}
    started = time.monotonic()
    comparisons = 0
    complete = True
    while heap:
        if time.monotonic()-started >= args.seconds:
            complete = False
            break
        cost,signature = heapq.heappop(heap)
        if dist[signature] != cost or signature in settled:
            continue
        settled[signature] = cost
        for other,other_cost in list(settled.items()):
            new_cost = cost+other_cost+1
            if new_cost > args.formula_limit:
                continue
            comparisons += 1
            for op,value in ((1,signature|other),(0,signature&other)):
                if new_cost < dist.get(value, args.formula_limit+1):
                    dist[value] = new_cost
                    expression[value] = (op,signature,other)
                    heapq.heappush(heap,(new_cost,value))

    def build(root_expression):
        gates = []
        known = {signature:i for i,signature in enumerate(signatures)}
        def wire(signature):
            if signature in known:
                return known[signature]
            op,a,b = expression[signature]
            left,right = wire(a),wire(b)
            gates.append([op,left,right])
            known[signature] = ninputs+len(gates)-1
            return known[signature]
        op,a,b = root_expression
        left,right = wire(a),wire(b)
        gates.append([op,left,right])
        return gates,ninputs+len(gates)-1

    best = None
    candidates = 0
    for a,da in settled.items():
        for b,db in settled.items():
            if a > b or da+db+1 > args.formula_limit:
                continue
            for op,value in ((1,a|b),(0,a&b)):
                if value != target:
                    continue
                candidates += 1
                gates,output = build((op,a,b))
                if best is None or len(gates) < len(best['gates']):
                    for row in rows:
                        values = list(row['cuts'])
                        for operation,left,right in gates:
                            values.append((values[left]|values[right]) if operation else (values[left]&values[right]))
                        assert values[output] == row['value']
                    best = dict(gates=gates,output=output,cut_inputs=ninputs,
                                expanded_formula_cost=da+db+1)
    result = dict(boundary_bits=len(rows), formula_limit=args.formula_limit,
                  completed_cost_bounded_formula_dp=complete,
                  settled_signatures=len(settled), comparisons=comparisons,
                  target_minimum_formula_cost=dist.get(target),
                  target_root_candidates=candidates,best=best,
                  elapsed_seconds=round(time.monotonic()-started,6),
                  scope='Minimum formula costs and one stored representation per signature; root pairs share equal signatures. Not exhaustive DAG search.')
    with open(args.output,'w') as target_file:
        json.dump(result,target_file,indent=2)
        target_file.write('\n')
    print(json.dumps({key:value for key,value in result.items() if key != 'best'} | {
        'best_dag_gate_count':None if best is None else len(best['gates'])}))


if __name__ == '__main__':
    main()
