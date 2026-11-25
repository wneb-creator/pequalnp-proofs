"""Exhaustive local CNF primitive check and exact star-circuit expansion control."""
import argparse
import itertools
import json
from pathlib import Path

import free_and_or_sat as model
import serve_sat


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    checked = 0
    for n in range(5):
        for types in itertools.product([False, True, None], repeat=n):
            cnf = serve_sat.CNF()
            selected = [cnf.var() for _ in range(n)]
            sources = [cnf.var() if kind is None else kind for kind in types]
            output = cnf.var()
            primary = cnf.variables
            model.conjunction_into(cnf, output, selected, sources)
            for mask in range(1 << primary):
                def value(literal, assignment):
                    return bool(assignment >> (abs(literal) - 1) & 1) == (literal > 0)

                terms = [(source if type(source) is bool else value(source, mask))
                         for chosen, source in zip(selected, sources) if value(chosen, mask)]
                expected = value(output, mask) == all(terms)
                found = any(all(any(value(lit, mask | (aux << primary)) for lit in clause)
                                for clause in cnf.clauses)
                            for aux in range(1 << (cnf.variables - primary)))
                assert found == expected
                checked += 1
    p, l, edges = serve_sat.graph_data('cycle6')
    nodes, output = model.star_control(p, l, edges)
    stars = serve_sat.make_problem(p, l, edges, len(nodes))[4]
    raw, raw_output = model.expand(p, l, nodes, output, False)
    masked, masked_output = model.expand(p, l, nodes, output, True)
    result = {
        'conjunction_primary_assignments_checked': checked, 'verdict': 'PASS',
        'control_graph': 'cycle6', 'OR_count': len(nodes),
        'raw_gate_count': len(raw), 'masked_gate_count': len(masked),
        'raw_verification': serve_sat.verify(p, l, edges, raw, raw_output, stars),
        'masked_verification': serve_sat.verify(p, l, edges, masked, masked_output, stars),
        'or_nodes': nodes, 'output_members': output}
    Path(args.output).write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
