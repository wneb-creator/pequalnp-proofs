import argparse
import datetime
import itertools
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--data', required=True)
    parser.add_argument('--rows', required=True)
    parser.add_argument('--budget', required=True, type=int)
    parser.add_argument('--seconds', required=True, type=int)
    parser.add_argument('--prefix', required=True)
    parser.add_argument('--fix-baseline', action='store_true')
    parser.add_argument('--emit-only', action='store_true')
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))
    started = time.monotonic()
    prefix = Path(args.prefix)
    prefix.parent.mkdir(parents=True, exist_ok=True)
    data = json.loads(Path(args.data).read_text())
    rows = json.loads(Path(args.rows).read_text())
    assert data['n'] == 26 and 0 < args.budget and args.seconds > 0
    assert all(type(r) is int and 0 <= r < 1 << 26 for r in rows)
    assert len(rows) == len(set(rows))
    edges = {(u, v - 13) for u, v in data['edges']}
    assert len(edges) == 52 and all(0 <= p < 13 and 0 <= l < 13 for p, l in edges)

    def target(row):
        return any(row >> p & 1 and row >> (13 + l) & 1 for p, l in edges)

    positive = [r for r in rows if target(r)]
    negative = [r for r in rows if not target(r)]
    assert set(positive) == {(1 << p) | (1 << (13 + l)) for p, l in edges}
    allowed = {(p, l) for p in range(13) for l in range(13)
               if not any(r >> p & 1 and r >> (13 + l) & 1 for r in negative)}
    extras = sorted(allowed - edges)
    assert edges <= allowed and len(extras) == 5 and len({p for p, _ in extras}) == 5
    original = [sum(1 << l for q, l in edges if q == p) for p in range(13)]
    enlarged = [sum(1 << l for q, l in allowed if q == p) for p in range(13)]
    assert all(s.bit_count() == 4 for s in original)
    assert all(s.bit_count() in (4, 5) for s in enlarged)

    supports = set()
    for output in enlarged:
        submask = output
        while submask:
            supports.add(submask)
            submask = (submask - 1) & output
    nonsingle = sorted((s for s in supports if s.bit_count() >= 2),
                       key=lambda s: (s.bit_count(), s))
    clauses = []
    variables = 0

    def fresh():
        nonlocal variables
        variables += 1
        return variables

    def add(*literals):
        if any(v is True for v in literals):
            return
        clause = [v for v in literals if v is not False]
        assert all(type(v) is int and v != 0 for v in clause)
        clauses.append(clause)

    chosen = {s: fresh() for s in nonsingle}
    production = {}
    for s in nonsingle:
        proper = sorted(t for t in supports if t != s and t & s == t)
        options = []
        for a, b in itertools.combinations(proper, 2):
            if a | b != s:
                continue
            witness = fresh()
            options.append((witness, a, b))
            add(-witness, chosen[s])
            if a in chosen:
                add(-witness, chosen[a])
            if b in chosen:
                add(-witness, chosen[b])
        assert options
        production[s] = options
        add(-chosen[s], *(w for w, _, _ in options))
    for small, large in zip(original, enlarged):
        add(chosen[small], chosen[large])

    # One-direction unary prefix counts suffice for an at-most constraint.
    previous = [True] + [False] * args.budget
    for x in chosen.values():
        current = [True] + [fresh() for _ in range(args.budget)]
        for j in range(1, args.budget + 1):
            add(-previous[j] if type(previous[j]) is int else not previous[j], current[j])
            add(-x, -previous[j - 1] if type(previous[j - 1]) is int
                else not previous[j - 1], current[j])
        add(-x, -previous[args.budget] if type(previous[args.budget]) is int
            else not previous[args.budget])
        previous = current

    baseline = set()
    for output in original:
        bits = [1 << l for l in range(13) if output >> l & 1]
        accumulated = bits[0]
        for bit in bits[1:]:
            accumulated |= bit
            baseline.add(accumulated)
    assert len(baseline) == 39
    if args.fix_baseline:
        for support, variable in chosen.items():
            add(variable if support in baseline else -variable)

    cnf = prefix.with_suffix('.cnf')
    with cnf.open('w') as file:
        file.write(f'p cnf {variables} {len(clauses)}\n')
        for clause in clauses:
            file.write(' '.join(map(str, clause)) + ' 0\n')
    record = {
        'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'encoder': 'OR support basis with overlapping strict-submask unions',
        'scope': 'sample-valid point-star circuits with shared line-only OR gates',
        'budget': args.budget, 'seconds_limit': args.seconds,
        'fixed_baseline': args.fix_baseline, 'sample_rows': len(rows),
        'allowed_extra_pairs': extras, 'output_families': 32,
        'candidate_supports': len(nonsingle), 'variables': variables,
        'clauses': len(clauses), 'conversion_seconds': time.monotonic() - started,
    }
    prefix.with_suffix('.mapping.json').write_text(json.dumps({
        'chosen': chosen, 'production': production, 'original': original,
        'enlarged': enlarged, 'baseline': sorted(baseline)}, indent=2) + '\n')
    print(json.dumps(record), flush=True)
    if args.emit_only:
        record['status'] = 'CNF emitted; solver not run'
    else:
        solver = '/tmp/oec/pequalnp-pilot-121/toolchain/lean-4.36.0-linux/bin/cadical'
        interrupted = None
        with prefix.with_suffix('.stdout').open('w') as out, prefix.with_suffix('.stderr').open('w') as err:
            process = subprocess.Popen([solver, '-t', str(args.seconds), '-w',
                str(prefix.with_suffix('.sol')), str(cnf)], stdout=out, stderr=err,
                start_new_session=True)
            prefix.with_suffix('.process.json').write_text(json.dumps({
                'wrapper_pid': os.getpid(), 'solver_pid': process.pid}) + '\n')

            def terminate(sig, frame):
                nonlocal interrupted
                interrupted = sig
                if process.returncode is not None:
                    raise SystemExit(128 + sig)
                try:
                    os.killpg(process.pid, sig)
                except ProcessLookupError:
                    pass

            signal.signal(signal.SIGTERM, terminate)
            process.wait()
        record['exit_code'] = process.returncode
        if interrupted is not None:
            record['status'] = 'interrupted'
        elif process.returncode == 10:
            assignment = {}
            for line in prefix.with_suffix('.sol').read_text().splitlines():
                if line.startswith('v '):
                    for literal in map(int, line[2:].split()):
                        if literal:
                            assignment[abs(literal)] = literal > 0
            assert set(assignment) == set(range(1, variables + 1))
            assert all(any(assignment[abs(v)] == (v > 0) for v in clause) for clause in clauses)
            selected = [s for s in nonsingle if assignment[chosen[s]]]
            assert len(selected) <= args.budget
            gates = []
            wires = {1 << l: 13 + l for l in range(13)}
            for s in selected:
                witnesses = [(a, b) for w, a, b in production[s] if assignment[w]]
                assert witnesses
                a, b = witnesses[0]
                assert a in wires and b in wires and a | b == s
                gates.append([1, wires[a], wires[b]])
                wires[s] = 26 + len(gates) - 1
            star_wires = []
            outputs = []
            for p, (small, large) in enumerate(zip(original, enlarged)):
                s = small if small in wires else large
                assert s in wires and small & s == small and s & large == s
                outputs.append(s)
                gates.append([0, p, wires[s]])
                star_wires.append(26 + len(gates) - 1)
            output = star_wires[0]
            for wire in star_wires[1:]:
                gates.append([1, output, wire])
                output = 26 + len(gates) - 1

            def evaluate(row):
                values = [bool(row >> i & 1) for i in range(26)]
                for op, a, b in gates:
                    assert a < len(values) and b < len(values)
                    values.append(values[a] or values[b] if op else values[a] and values[b])
                return values[output]

            assert len(gates) == len(selected) + 25
            assert all(evaluate(r) == target(r) for r in rows)
            mismatches = [r for r in data['rows'] if evaluate(r) != target(r)]
            status = ('SAT; full boundary passed; Lean verification required' if not mismatches
                      else 'SAT; sampled rows passed; full boundary incomplete')
            record.update({'status': status,
                'selected_supports': selected, 'selected_outputs': outputs,
                'gates': gates, 'output': output, 'size': len(gates),
                'sample_mismatches': 0, 'full_boundary_mismatches': mismatches,
                'verified_cnf_clauses': len(clauses)})
        elif process.returncode == 20:
            record['status'] = 'UNSAT; external solver only, restricted OR-basis class'
        elif process.returncode == 0:
            record['status'] = 'UNKNOWN; time or resource limit'
        else:
            record['status'] = 'solver error'
    record['elapsed_seconds'] = time.monotonic() - started
    prefix.with_suffix('.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({k: v for k, v in record.items()
        if k not in ('gates', 'full_boundary_mismatches', 'selected_supports')}), flush=True)
    if not args.emit_only and interrupted is not None:
        raise SystemExit(128 + interrupted)


if __name__ == '__main__':
    main()
