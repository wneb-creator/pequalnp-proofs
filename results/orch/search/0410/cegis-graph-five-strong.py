import importlib.util
import itertools
import json
import pathlib

HERE = pathlib.Path('/tmp/oec/pequalnp-pilot-21/search')


def module(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


q = module('symbolic_five_driver', 'cegis-symbolic-five.py')
sw = module('graph_streaming_writer', 'streaming_cnf.py')
q.ROOT = HERE / 'symbolic-graph-five-strong'
q.ROOT.mkdir(exist_ok=True)
original_encode = q.s.encode
original_reachability = q.reachability


def all_five_nonordinary_support(c, aa, bb, meta, goals):
    supports = original_reachability(c, aa, bb, meta, goals)
    assert len(goals) == 5
    for support in supports[-5:]:
        assert len(support) == 13
        for excluded in itertools.combinations(range(13), 7):
            c.add(*(support[p] for p in range(13) if p not in excluded))
    return supports


generation = 0
EDGES = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]


def all_five_nonordinary(c, ops, aa, bb, meta, goals):
    points = set().union(*(q.s.LINES[w] for w in goals))
    rows = {1 << p for p in points}
    complements = {w: 8191 ^ sum(1 << p for p in q.s.LINES[w]) for w in goals}
    rows.update(complements.values())
    output_values = {}
    for row in sorted(rows):
        values = [c.var() for _ in ops]
        for j, op in enumerate(ops):
            children = [c.var(), c.var()]
            for selectors, value in zip((aa[j], bb[j]), children):
                for k, selected in enumerate(selectors):
                    if k < len(meta):
                        source = bool(row >> k & 1) if k < 13 else any(row >> p & 1 for p in meta[k][1])
                        c.add(-selected, value if source else -value)
                    else:
                        source = values[k-len(meta)]
                        c.add(-selected, -source, value)
                        c.add(-selected, source, -value)
            a, b = children
            value = values[j]
            c.add(-op, -value, a)
            c.add(-op, -value, b)
            c.add(-op, value, -a, -b)
            c.add(op, -a, value)
            c.add(op, -b, value)
            c.add(op, -value, a, b)
        output_values[row] = values[-len(goals):]
    for j, goal in enumerate(goals):
        c.add(output_values[complements[goal]][j],
              *(-output_values[1 << p][j] for p in q.s.LINES[goal]))


def graph_encode(base, meta, goals, ng, samples):
    global generation
    assert ng == 14 and len(goals) == 5
    q.s.CNF = sw.streaming_class(q.s.b.CNF, q.ROOT / f'graph-{generation:03d}.clauses.part')
    generation += 1
    c, ops, aa, bb = original_encode(base, meta, goals, ng, samples)
    internal = ng-len(goals)
    high = [[c.var() for _ in range(internal)] for _ in range(4)]
    for selectors in high:
        c.one(selectors)
    for u in range(4):
        for v in range(u+1, 4):
            for k in range(internal):
                c.add(-high[u][k], -high[v][k])
    # Swapping the two degree-three vertices, or the two degree-two vertices,
    # is a graph automorphism; the target-to-edge assignment remains free.
    for u, v in ((0, 1), (2, 3)):
        for a in range(internal):
            for b in range(a+1):
                c.add(-high[u][a], -high[v][b])
    assignment = [[c.var() for _ in EDGES] for _ in goals]
    for selectors in assignment:
        c.one(selectors)
    for edge in range(len(EDGES)):
        c.one([assignment[j][edge] for j in range(len(goals))])
    for j in range(len(goals)):
        root = internal+j
        c.add(-ops[root])
        for edge, (u, v) in enumerate(EDGES):
            chosen = assignment[j][edge]
            for a in range(internal):
                for b in range(internal):
                    if a == b:
                        continue
                    guard = (-chosen, -high[u][a], -high[v][b])
                    c.add(*guard, aa[root][len(base)+min(a, b)])
                    c.add(*guard, bb[root][len(base)+max(a, b)])
    all_five_nonordinary(c, ops, aa, bb, meta, goals)
    return c, ops, aa, bb


def sinks_without_live_requirement(c, aa, bb, base_count, output_count):
    # Unused internal padding is needed for completeness of the <=9-high-gate
    # template: live output padding would change the fixed graph decoder.
    first_output = base_count+len(aa)-output_count
    for a, b in zip(aa, bb):
        for selector in a[first_output:]+b[first_output:]:
            c.add(-selector)


if __name__ == '__main__':
    q.s.encode = graph_encode
    q.reachability = all_five_nonordinary_support
    q.live_sinks = sinks_without_live_requirement
    description = {
        'scope': 'restricted candidate template, not the unrestricted lower bound',
        'goals': q.GOALS,
        'fixed_direct_outputs': 8,
        'residual_output_support_minimum': 8,
        'all_five_residual_outputs_nonordinary': True,
        'nonordinary_test': 'own-complement true OR any missing line-singleton positive',
        'support_justification': 'Lean-checked NineOrdinary implies all five residual outputs nonordinary; checked small-support theorem gives at least eight raw support points',
        'high_network_gate_budget': 9,
        'selected_high_signals': 4,
        'decoder_edges': EDGES,
        'edge_to_target_permutation': 'unrestricted',
        'high_signals_may_feed_other_high_signals': True,
        'unused_high_network_padding_allowed': True,
        'candidate_check': 'independent scalar validation on all3003 original band rows',
    }
    (q.ROOT / 'template.json').write_text(json.dumps(description, indent=2)+'\n')
    print('GRAPH_TEMPLATE', json.dumps(description), flush=True)
    q.main()
    verdict = q.ROOT / 'unsat.json'
    if verdict.exists():
        record = json.loads(verdict.read_text())
        record['additional_graph_template_restriction'] = description
        verdict.write_text(json.dumps(record, indent=2)+'\n')
