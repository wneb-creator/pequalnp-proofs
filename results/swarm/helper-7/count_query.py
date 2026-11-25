"""Full-boundary circuit queries with optional conditional count restrictions.

The generic --mis-lower bound counts ALL maximal independent sets returned by
synthesize.graph_info. This script queries the complete graph function; partial
CEGAR row samples are not supported. Solver outcomes are computational evidence,
not Lean certificates.
"""
import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
import synthesize as s


def at_most_sequential(formula, literals, bound):
    """Exact unary prefix counter, truncated at the first forbidden count."""
    if bound < 0:
        formula.add()
        return []
    if bound >= len(literals):
        return []

    def negate(literal):
        return not literal if isinstance(literal, bool) else -literal

    def clause(*literals):
        if any(literal is True for literal in literals):
            return
        formula.add(*(literal for literal in literals if literal is not False))

    previous = {}
    states = []
    for i, literal in enumerate(literals, start=1):
        current = {}
        for count in range(1, min(i, bound + 1) + 1):
            state = formula.var()
            current[count] = state
            a = previous.get(count, False)
            b = literal
            c = True if count == 1 else previous.get(count - 1, False)
            # state iff a OR (b AND c).
            clause(negate(a), state)
            clause(negate(b), negate(c), state)
            clause(-state, a, b)
            clause(-state, a, c)
        states.append(current)
        previous = current
    formula.add(-previous[bound + 1])
    return states


def add_input_budget(formula, mapping, n, k):
    flags = []
    for j in range(k):
        for selectors in (mapping['left'][j], mapping['right'][j]):
            flag = formula.var()
            flags.append(flag)
            for source, selector in enumerate(selectors):
                formula.add(-selector, flag if source < n else -flag)
            formula.add(-flag, *selectors[:n])
            formula.add(flag, *selectors[n:])
    states = at_most_sequential(formula, flags, k + 1)
    return {'flags': flags, 'bound': k + 1, 'counter_states': states}


def maximal_false_and_bound(info):
    count = sum(not target for _, target in info['rows'])
    assert count >= 1
    return count, (count - 1).bit_length()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--graph', default='theta333')
    ap.add_argument('--k', type=int, default=11)
    ap.add_argument('--min-and', type=int, default=4)
    ap.add_argument('--mis-lower', action='store_true')
    ap.add_argument('--max-and', type=int)
    ap.add_argument('--seconds', type=int, default=1800)
    ap.add_argument('--solver', type=Path, default=s.DEFAULT_SOLVER)
    ap.add_argument('--lex', action='store_true')
    ap.add_argument('--input-budget', action='store_true')
    a = ap.parse_args()
    if a.solver is None:
        ap.error('Kissat was not found; provide --solver PATH')
    if not 0 <= a.min_and <= a.k:
        ap.error('--min-and must be between 0 and k')
    if a.max_and is not None and not a.min_and <= a.max_and <= a.k:
        ap.error('--max-and must be between min-and and k')
    g = json.loads((s.ROOT / 'graphs' / (a.graph + '.json')).read_text())
    info = s.graph_info(g['n'], g['edges'])
    mis_count, mis_bound = maximal_false_and_bound(info)
    effective_min = max(a.min_and, mis_bound if a.mis_lower else 0)
    autos = s.first_pair_symmetry(info)
    f, mp = s.encode(info, a.k, normalized=True, symmetry=autos,
                     undominated=True, oriented=True)
    if a.lex:
        for j in range(a.k - 1):
            for r in range(info['n'] + j):
                for left in range(r):
                    for next_left in range(left):
                        f.add(-mp['right'][j][r], -mp['right'][j + 1][r],
                              -mp['left'][j][left], -mp['left'][j + 1][next_left])
                    f.add(-mp['right'][j][r], -mp['right'][j + 1][r],
                          -mp['left'][j][left], -mp['left'][j + 1][left],
                          -mp['op'][j], mp['op'][j + 1])
    for pad, op in zip(mp['pad'], mp['op']):
        f.add(-pad, -op)
    min_and_states = at_most_sequential(f, [-op for op in mp['op']], a.k - effective_min)
    max_and_states = (at_most_sequential(f, mp['op'], a.max_and)
                      if a.max_and is not None else None)
    input_budget = add_input_budget(f, mp, info['n'], a.k) if a.input_budget else None
    mis_proof = (
        'For a circuit with A AND gates, globally select one parent at every AND gate. '
        'Each of the at most 2^A selections produces an OR-only clause above the circuit. '
        'At every false input, choosing a false parent at each false AND gate preserves '
        'the false output, so the circuit is the conjunction of these clauses. '
        'Each clause contributes at most one maximal false assignment. Hence M <= 2^A '
        'for M maximal false assignments, giving A >= ceil(log2(M)). For a graph '
        'function these assignments are exactly its maximal independent sets.')
    explicit_assumption = a.min_and > (mis_bound if a.mis_lower else 0)
    if explicit_assumption:
        justification = ('Conditional search with an externally requested AND lower bound '
                         'stronger than the enabled generic bound; no external theorem is assumed.')
    elif a.mis_lower:
        justification = 'Generic maximal-false-assignment bound: ' + mis_proof
    else:
        justification = 'Trivial nonnegative AND count; no additional lower-bound assumption.'
    name = a.graph + ('-count-lex' if a.lex else '-count')
    if a.mis_lower:
        name += '-mis-lower'
    if a.max_and is not None:
        name += '-max-and' + str(a.max_and)
    if a.input_budget:
        name += '-input-budget'
    d = s.ROOT / 'synthesis' / (name + '-' + str(time.time_ns()))
    d.mkdir(parents=True)
    f.write(d / 'input.cnf')
    (d / 'encoding.json').write_text(json.dumps({
        'info': info, 'mapping': mp, 'min_and': effective_min,
        'explicit_min_and': a.min_and, 'effective_min_and': effective_min,
        'mis_lower': a.mis_lower, 'mis_count': mis_count, 'mis_and_bound': mis_bound,
        'mis_lower_proof': mis_proof, 'min_and_counter_states': min_and_states,
        'conditional_explicit_min_and': explicit_assumption,
        'max_and': a.max_and, 'max_and_counter_states': max_and_states,
        'max_and_justification': (
            'Requested restriction for a conditional witness search; '
            'no global upper bound on the AND count is asserted.')
            if a.max_and is not None else None,
        'lex': a.lex, 'input_budget': input_budget,
        'justification': justification,
        'input_budget_justification': (
            'Every non-output gate has a later consumer, including padding gates. '
            'At least k-1 of the 2k operand slots therefore read internal gates; '
            'at most k+1 slots read original inputs.') if a.input_budget else None,
    }, indent=2))
    started = time.monotonic()
    with (d / 'solver.stdout').open('w') as out, (d / 'solver.stderr').open('w') as err:
        process = subprocess.Popen([str(a.solver), '--time=' + str(a.seconds),
                                    str(d / 'input.cnf')], stdout=out, stderr=err)
        print(json.dumps({'pid': process.pid, 'directory': str(d)}), flush=True)
        code = process.wait()
    result = {'graph': a.graph, 'k': a.k, 'min_and': effective_min,
              'explicit_min_and': a.min_and, 'effective_min_and': effective_min,
              'mis_lower': a.mis_lower, 'mis_count': mis_count, 'mis_and_bound': mis_bound,
              'conditional_explicit_min_and': explicit_assumption,
              'max_and': a.max_and,
              'conditional_max_and_restriction': a.max_and is not None,
              'lex': a.lex, 'input_budget': a.input_budget,
              'exit': code, 'seconds': time.monotonic() - started, 'directory': str(d),
              'status': 'SAT' if code == 10 else 'UNSAT' if code == 20 else 'UNKNOWN'}
    if code == 10:
        result['gates'] = s.decode((d / 'solver.stdout').read_text(), mp)
        result.update(s.verify(info, result['gates']))
    (d / 'result.json').write_text(json.dumps(result, indent=2))
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
