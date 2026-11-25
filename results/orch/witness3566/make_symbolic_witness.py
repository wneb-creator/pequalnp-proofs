#!/usr/bin/env python3
"""Certify an amplified witness by small Boolean cuts and algebraic normalization."""
import argparse
import json
from pathlib import Path

from make_witness import render


def symbolic_render(data, plan):
    # Reuse all validated circuit/graph bridges from the ordinary generator.
    source = render(data, 'simp')
    # These definitions are used only through their equations, so no generated
    # executable code is needed for them.
    source = source.replace('def witnessExpr ', 'noncomputable def witnessExpr ')
    source = source.replace('def witnessGraphExpr ', 'noncomputable def witnessGraphExpr ')
    n = data['n']
    gates = data['gates']
    expressions = [f'b{i}' for i in range(n)]
    supports = [{i} for i in range(n)]
    for op, a, b in gates:
        term = f'({expressions[a]} {"&&" if op == "and" else "||"} {expressions[b]})'
        if len(term) > 2000000:
            raise ValueError('Expanded expression exceeds the generator size limit')
        expressions.append(term)
        supports.append(supports[a] | supports[b])

    declarations = []
    cut_data = []
    for i, cut in enumerate(plan['cuts']):
        wire = cut['wire']
        assert type(wire) is int and 0 <= wire < len(expressions)
        variables = set(supports[wire])
        if 'edges' in cut:
            edges = cut['edges']
            assert all(type(u) is int and type(v) is int and
                       0 <= u < n and 0 <= v < n for u, v in edges)
            target = ' || '.join(f'(b{u} && b{v})' for u, v in edges) or 'false'
            variables.update(v for e in edges for v in e)
        elif 'or_inputs' in cut:
            inputs = cut['or_inputs']
            assert all(type(v) is int and 0 <= v < n for v in inputs)
            target = ' || '.join(f'b{v}' for v in inputs) or 'false'
            variables.update(inputs)
        else:
            raise ValueError('A cut requires edges or or_inputs')
        variables = sorted(variables)
        assert variables
        args = ' '.join(f'b{v}' for v in variables)
        strategy = cut.get('strategy', 'auto')
        algebraic = '''simp [Bool.and_or_distrib_left, Bool.and_or_distrib_right,
    Bool.and_assoc, Bool.and_comm, Bool.and_left_comm,
    Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]'''
        if strategy in ('kernel', 'auto'):
            if len(variables) > 16:
                raise ValueError('Kernel cut has more than sixteen input variables')
            proof = f'  revert {args}\n  decide +kernel'
            if strategy == 'auto':
                proof = ('  first\n  | solve | ' + algebraic.replace('\n', '\n    ') +
                         f'\n  | revert {args}\n    decide +kernel')
        elif strategy == 'simp':
            proof = '  ' + algebraic
        else:
            raise ValueError('Unknown cut proof strategy')
        declarations.append(f'''set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem witness_cut_{i} ({args} : Bool) :
    {expressions[wire]} = ({target}) := by
{proof}
''')
        cut_data.append((wire, target, args))

    output = data.get('output', n + len(gates) - 1)
    rewrites = [f'  rw [witness_cut_{i} {args}]'
                for i, (_, _, args) in enumerate(cut_data)]
    replacement = f'''  change {expressions[output]} = _
{chr(10).join(rewrites)}
  simp only [witnessGraphExpr, Bool.and_or_distrib_left, Bool.and_or_distrib_right]
  ac_rfl'''
    start = source.index('set_option maxRecDepth 100000 in\nset_option maxHeartbeats 8000000 in\ntheorem witness_formula')
    proof_start = source.index(' := by\n', start) + len(' := by\n')
    proof_end = source.index('\n\nset_option maxRecDepth', proof_start)
    source = source[:start] + '\n'.join(declarations) + '\n' + source[start:proof_start] + replacement + source[proof_end:]
    return source


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('witness_json', type=Path)
    parser.add_argument('cut_plan_json', type=Path)
    parser.add_argument('lean_file', type=Path)
    args = parser.parse_args()
    data = json.loads(args.witness_json.read_text())
    plan = json.loads(args.cut_plan_json.read_text())
    args.lean_file.write_text(symbolic_render(data, plan))
    print(f'Generated {args.lean_file}: n={data["n"]}, gates={data["size"]}, cuts={len(plan["cuts"])}')


if __name__ == '__main__':
    main()
