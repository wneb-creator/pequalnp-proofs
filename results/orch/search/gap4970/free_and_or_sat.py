"""Exact limited-OR search with free nonempty conjunctions and serving stars."""
import argparse
import hashlib
import json
import resource
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path

import serve_sat


def conjunction_into(cnf, output, selected, sources):
    """output is the conjunction of all selected sources (selection is nonempty)."""
    bad = []
    for chosen, value in zip(selected, sources):
        if value is True:
            continue
        if value is False:
            b = chosen
        else:
            b = cnf.var()
            cnf.clause(-b, chosen)
            cnf.clause(-b, -value)
            cnf.clause(-chosen, value, b)
        bad.append(b)
        cnf.clause(serve_sat.neg(output), -b)
    cnf.clause(output, *bad)


def make_problem(p, l, edges, count):
    # Reuse the reviewed complete boundary/star test family without changing it.
    _, _, _, _, stars, tests, target = serve_sat.make_problem(p, l, edges, count)
    n = p + l
    cnf = serve_sat.CNF()
    members = [[[cnf.var() for _ in range(n + g)] for _ in range(2)] for g in range(count)]
    output_members = [cnf.var() for _ in range(n + count)]
    values = [[cnf.var() for _ in tests] for _ in range(count)]
    sides = [[[cnf.var() for _ in tests] for _ in range(2)] for _ in range(count)]
    for g in range(count):
        for side in range(2):
            cnf.clause(*members[g][side])
            for t, mask in enumerate(tests):
                sources = [bool(mask >> i & 1) for i in range(n)] + [values[j][t] for j in range(g)]
                conjunction_into(cnf, sides[g][side][t], members[g][side], sources)
        for t in range(len(tests)):
            a, b, z = sides[g][0][t], sides[g][1][t], values[g][t]
            cnf.clause(-a, z)
            cnf.clause(-b, z)
            cnf.clause(a, b, -z)
    cnf.clause(*output_members)
    for t, mask in enumerate(tests):
        sources = [bool(mask >> i & 1) for i in range(n)] + [values[g][t] for g in range(count)]
        conjunction_into(cnf, bool(target(mask)), output_members, sources)
    index = {mask: t for t, mask in enumerate(tests)}
    serving = [[cnf.var() for _ in stars] for _ in range(count)]
    for g in range(count):
        for s, star in enumerate(stars):
            for leaf in star['leaves']:
                cnf.clause(-serving[g][s], values[g][index[1 << leaf]])
            complement = ((1 << n) - 1) ^ star['mask']
            cnf.clause(-serving[g][s], -values[g][index[complement]])
    for edge in edges:
        cnf.clause(*(serving[g][s] for g in range(count) for s, star in enumerate(stars)
                     if edge in star['edges']))
    return cnf, members, output_members, stars, tests


def expand(p, l, nodes, output_members, mask_inputs):
    n = p + l
    gates = []
    signals = list(range(n))
    if mask_inputs:
        for i in range(n):
            signals[i] = n + len(gates)
            gates.append([0, i, i])
    conjunction_cache = {}

    def conjunction(wires):
        wires = tuple(sorted(set(wires)))
        assert wires
        if wires in conjunction_cache:
            return conjunction_cache[wires]
        out = wires[0]
        for wire in wires[1:]:
            a, b = sorted((out, wire))
            gates.append([0, a, b])
            out = n + len(gates) - 1
        conjunction_cache[wires] = out
        return out

    for left, right in nodes:
        a = conjunction(signals[i] for i in left)
        b = conjunction(signals[i] for i in right)
        # Preserve each actual OR node, including unused serving witnesses.
        gates.append([1, *sorted((a, b))])
        signals.append(n + len(gates) - 1)
    output = conjunction(signals[i] for i in output_members)
    return gates, output


def star_control(p, l, edges):
    n = p + l
    nodes = []
    products = []
    for a in range(p):
        leaves = [p + b for aa, b in edges if aa == a]
        assert len(leaves) >= 2
        root = leaves[0]
        for leaf in leaves[1:]:
            nodes.append([[root], [leaf]])
            root = n + len(nodes) - 1
        products.append([a, root])
    root = products[0]
    for product in products[1:]:
        nodes.append([root, product])
        root = [n + len(nodes) - 1]
    return nodes, root


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--graph', required=True)
    parser.add_argument('--or-gates', type=int, required=True)
    parser.add_argument('--seconds', type=int, default=30)
    parser.add_argument('--memory-mib', type=int, default=512)
    parser.add_argument('--output', required=True)
    parser.add_argument('--pin-star-control', action='store_true')
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_AS, (args.memory_mib * 1024 * 1024,) * 2)
    p, l, edges = serve_sat.graph_data(args.graph)
    cnf, members, output_members, stars, tests = make_problem(p, l, edges, args.or_gates)
    if args.pin_star_control:
        expected, expected_output = star_control(p, l, edges)
        assert len(expected) == args.or_gates
        for g, node in enumerate(expected):
            for side in range(2):
                for i, var in enumerate(members[g][side]):
                    cnf.clause(var if i in node[side] else -var)
        for i, var in enumerate(output_members):
            cnf.clause(var if i in expected_output else -var)
    base = Path(args.output)
    base.parent.mkdir(parents=True, exist_ok=True)
    with base.with_suffix('.cnf').open('w') as f:
        f.write(f'p cnf {cnf.variables} {len(cnf.clauses)}\n')
        for clause in cnf.clauses:
            f.write(' '.join(map(str, clause)) + ' 0\n')
    result = {
        'p': p, 'l': l, 'edges': edges, 'or_budget': args.or_gates,
        'cover_number': serve_sat.cover_number(p, l, edges), 'tests': len(tests),
        'variables': cnf.variables, 'clauses': len(cnf.clauses),
        'started_utc': datetime.now(timezone.utc).isoformat(),
        'memory_limit_mib': args.memory_mib, 'pinned_star_control': args.pin_star_control,
        'base_encoder_sha256': hashlib.sha256(Path(serve_sat.__file__).read_bytes()).hexdigest()}
    begin = time.monotonic()
    with base.with_suffix('.solver.stdout').open('w') as out, base.with_suffix('.solver.stderr').open('w') as err:
        process = subprocess.run([serve_sat.SOLVER, '-t', str(args.seconds), str(base.with_suffix('.cnf'))],
                                 stdout=out, stderr=err)
    result.update(seconds=time.monotonic() - begin, returncode=process.returncode,
                  status={10: 'SAT', 20: 'UNSAT', 0: 'UNKNOWN'}.get(process.returncode, 'ERROR'))
    if process.returncode == 10:
        model = set()
        for line in base.with_suffix('.solver.stdout').read_text().splitlines():
            if line.startswith('v '):
                model.update(int(v) for v in line.split()[1:] if int(v) > 0)
        nodes = [[[i for i, var in enumerate(side) if var in model] for side in node] for node in members]
        output = [i for i, var in enumerate(output_members) if var in model]
        assert output and all(left and right for left, right in nodes)
        raw, raw_output = expand(p, l, nodes, output, False)
        masked, masked_output = expand(p, l, nodes, output, True)
        checked = serve_sat.verify(p, l, edges, masked, masked_output, stars)
        assert sum(op for op, _, _ in masked) == args.or_gates
        reaches = [1 << i for i in range(p + l)]
        raw_t_count = 0
        for op, a, b in raw:
            reach = reaches[a] | reaches[b] if op else 0
            reaches.append(reach)
            raw_t_count += bool(op and reach & ((1 << p) - 1) and reach >> p)
        raw_verified = serve_sat.verify(p, l, edges, raw, raw_output, stars) if raw_t_count == 0 else None
        # Independently evaluate the collapsed model on every assignment too.
        for mask in range(1 << (p + l)):
            values = [bool(mask >> i & 1) for i in range(p + l)]
            for left, right in nodes:
                values.append(all(values[i] for i in left) or all(values[i] for i in right))
            actual = all(values[i] for i in output)
            expected = any((mask >> a) & (mask >> (p + b)) & 1 for a, b in edges)
            assert actual == expected
            raw_values = [bool(mask >> i & 1) for i in range(p + l)]
            for op, a, b in raw:
                raw_values.append(raw_values[a] or raw_values[b] if op else raw_values[a] and raw_values[b])
            assert raw_values[raw_output] == expected
        result.update(
            or_nodes=nodes, output_members=output, masked_circuit=masked, masked_output=masked_output,
            masked_gate_count=len(masked), masked_verification=checked,
            input_mask_and_count=p + l, raw_circuit=raw, raw_output=raw_output,
            raw_gate_count=len(raw), raw_t_count=raw_t_count, raw_verification=raw_verified,
            violates_proposed_or_bound=args.or_gates < len(edges) - 1,
            target_counterexample=(len(masked) + 1 < len(edges) + result['cover_number'] or
                (raw_verified is not None and len(raw) + 1 < len(edges) + result['cover_number'])))
    base.with_suffix('.result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
