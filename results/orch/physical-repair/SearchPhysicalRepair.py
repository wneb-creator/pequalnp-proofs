"""Bounded physical-wire beam repair with complete extremal verification.

The beam is heuristic: exhaustion or a time limit establishes no lower bound.
Half of each beam preserves every positive edge; the rest uses balanced errors.
"""
import argparse
import importlib
import json
import time
from pathlib import Path


def evaluate(problem, gates):
    values = list(problem.INPUT_MASKS)
    for operation, (a, b) in gates:
        assert 0 <= a < len(values) and 0 <= b < len(values)
        values.append(values[a] & values[b] if operation == 'and'
                      else values[a] | values[b])
    output = values[-1]
    wp = (problem.TARGET & ~output).bit_count()
    wn = (output & (problem.ALL_TESTS ^ problem.TARGET)).bit_count()
    return wp, wn, output, values


def scalar_artifact(problem, gates, label):
    mistakes = []
    for x in sorted(problem.POSITIVES | problem.RAW_NEGATIVES):
        values = [bool(x >> j & 1) for j in range(problem.N)]
        for operation, (a, b) in gates:
            assert 0 <= a < len(values) and 0 <= b < len(values)
            values.append(values[a] and values[b] if operation == 'and'
                          else values[a] or values[b])
        expected = x in problem.POSITIVES
        if values[-1] != expected:
            mistakes.append({'input': x, 'actual': values[-1], 'expected': expected})
    if label == 'computational witness; requires Lean verification':
        assert not mistakes
    else:
        assert mistakes
    return {'inputs': problem.N, 'gates': gates, 'size': len(gates),
            'output': problem.N + len(gates) - 1,
            'wrong_tests': mistakes, 'wrong_raw_tests': len(mistakes),
            'proof_status': label}


def neighbors(problem, gates, values):
    for i, (operation, sources) in enumerate(gates):
        a, b = sources
        modifications = [('or' if operation == 'and' else 'and', sources)]
        modifications += [(operation, tuple(sorted((source, b))))
                          for source in range(problem.N + i) if source != a]
        modifications += [(operation, tuple(sorted((a, source))))
                          for source in range(problem.N + i) if source != b]
        seen = set()
        for replacement in modifications:
            if replacement in seen or replacement == (operation, sources):
                continue
            seen.add(replacement)
            changed = gates[:i] + (replacement,) + gates[i+1:]
            new_values = values[:problem.N+i]
            for op, (u, v) in changed[i:]:
                new_values.append(new_values[u] & new_values[v] if op == 'and'
                                  else new_values[u] | new_values[v])
            output = new_values[-1]
            wp = (problem.TARGET & ~output).bit_count()
            wn = (output & (problem.ALL_TESTS ^ problem.TARGET)).bit_count()
            yield changed, (wp, wn, output, new_values)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--problem', choices=['SearchAlternative6Problem',
                                            'SearchComplement12Problem',
                                            'SearchPlaneProblem'], required=True)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--seconds', type=float, default=120)
    parser.add_argument('--rounds', type=int, default=4)
    parser.add_argument('--width', type=int, default=16)
    args = parser.parse_args()
    assert args.width >= 2
    problem = importlib.import_module(args.problem)
    data = json.loads(args.input.read_text())
    gates = tuple((op, tuple(sorted(pair))) for op, pair in data['gates'])
    assert data['inputs'] == problem.N and gates
    assert data['output'] == problem.N + len(gates) - 1
    assert all(op in ('and', 'or') for op, _ in gates)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    initial = evaluate(problem, gates)
    beam = [(gates, initial)]
    seen = {gates}
    tested = 0
    started = time.monotonic()
    scale = len(problem.POSITIVES) / (len(problem.TESTS) - len(problem.POSITIVES))
    best_positive = initial[1] if not initial[0] else len(problem.TESTS)+1
    print(json.dumps({'event': 'start', 'size': len(gates), 'positive_errors': initial[0],
                      'negative_errors': initial[1], 'seconds': args.seconds,
                      'width': args.width, 'rounds': args.rounds}), flush=True)
    for round_number in range(args.rounds):
        candidates = {}
        timed_out = False
        for state, evaluation in beam:
            for changed, result in neighbors(problem, state, evaluation[3]):
                tested += 1
                if tested % 2048 == 0 and time.monotonic() - started >= args.seconds:
                    timed_out = True
                    break
                if changed in seen:
                    continue
                wp, wn, output, _ = result
                if wp == wn == 0:
                    artifact = scalar_artifact(problem, changed,
                                               'computational witness; requires Lean verification')
                    (args.output_dir / 'witness.json').write_text(json.dumps(artifact, indent=2) + '\n')
                    print(json.dumps({'event': 'WITNESS', 'size': len(changed),
                                      'tested': tested, 'seconds': time.monotonic()-started}), flush=True)
                    return
                # Retain one physical state per output signature in this bounded beam.
                if output not in candidates:
                    candidates[output] = (changed, result)
                if len(candidates) > max(64, args.width*8):
                    pool = list(candidates.values())
                    keep = sorted((item for item in pool if item[1][0] == 0),
                                  key=lambda item: item[1][1])[:args.width]
                    keep += sorted(pool, key=lambda item: item[1][0] + scale*item[1][1])[:args.width]
                    candidates = {item[1][2]: item for item in keep}
            if timed_out:
                break
        options = list(candidates.values())
        positive = sorted((item for item in options if item[1][0] == 0),
                          key=lambda item: item[1][1])[:args.width//2]
        balanced = sorted(options, key=lambda item: item[1][0] + scale*item[1][1])
        beam = positive[:]
        selected = {item[0] for item in beam}
        for item in balanced:
            if item[0] not in selected:
                beam.append(item)
                selected.add(item[0])
            if len(beam) >= args.width:
                break
        seen.update(selected)
        if positive and positive[0][1][1] < best_positive:
            best_positive = positive[0][1][1]
            artifact = scalar_artifact(problem, positive[0][0], 'INVALID positive-complete physical repair seed')
            (args.output_dir / ('improved-'+str(round_number)+'.json')).write_text(json.dumps(artifact, indent=2)+'\n')
        print(json.dumps({'event': 'round', 'round': round_number, 'tested': tested,
                          'beam': len(beam), 'best_positive_complete_negative_errors': best_positive,
                          'best_beam_errors': [item[1][:2] for item in beam[:4]],
                          'seconds': time.monotonic()-started, 'timed_out': timed_out}), flush=True)
        if timed_out or not beam:
            break
    print(json.dumps({'event': 'finished', 'tested': tested,
                      'seconds': time.monotonic()-started,
                      'conclusion': 'bounded heuristic search; no lower-bound conclusion'}), flush=True)


if __name__ == '__main__':
    main()
