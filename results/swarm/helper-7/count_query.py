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


def primary_operand_flags(formula, mapping, n, k):
    flags = []
    for j in range(k):
        for selectors in (mapping['left'][j], mapping['right'][j]):
            flag = formula.var()
            flags.append(flag)
            for source, selector in enumerate(selectors):
                formula.add(-selector, flag if source < n else -flag)
            formula.add(-flag, *selectors[:n])
            formula.add(flag, *selectors[n:])
    return flags


def add_input_budget(formula, mapping, n, k):
    flags = primary_operand_flags(formula, mapping, n, k)
    states = at_most_sequential(formula, flags, k + 1)
    return {'flags': flags, 'bound': k + 1, 'counter_states': states}


def validate_primary_reader_graph(info):
    adjacency = [set() for _ in range(info['n'])]
    for a, b in info['edges']:
        adjacency[a].add(b)
        adjacency[b].add(a)
    if not adjacency or min(map(len, adjacency)) < 2:
        raise ValueError('--primary-reader-bound requires graph minimum degree at least 2')
    if any(len(adjacency[a] & adjacency[b]) >= 2
           for a in range(info['n']) for b in range(a + 1, info['n'])):
        raise ValueError('--primary-reader-bound requires a graph with no four-cycle')
    return {'minimum_degree': min(map(len, adjacency)), 'no_four_cycle': True}


def add_primary_reader_bound(formula, mapping, n, k, flags=None):
    if flags is None:
        flags = primary_operand_flags(formula, mapping, n, k)
    assert len(flags) == 2 * k
    raw = []
    readers = []
    for j in range(k):
        left_primary, right_primary = flags[2 * j:2 * j + 2]
        raw_gate, reader = formula.var(), formula.var()
        raw.append(raw_gate)
        readers.append(reader)
        formula.add(-raw_gate, left_primary)
        formula.add(-raw_gate, right_primary)
        formula.add(-left_primary, -right_primary, raw_gate)
        formula.add(-left_primary, reader)
        formula.add(-right_primary, reader)
        formula.add(-reader, left_primary, right_primary)
        for vertex in range(n):
            elsewhere = [selector for i in range(k) if i != j
                         for selector in (mapping['left'][i][vertex], mapping['right'][i][vertex])]
            formula.add(-raw_gate, -mapping['left'][j][vertex], *elsewhere)
            formula.add(-raw_gate, -mapping['right'][j][vertex], *elsewhere)
    counter = at_most_sequential(formula, [-reader for reader in readers], k - n)
    return {'primary_operand_flags': flags, 'raw_gate_flags': raw,
            'primary_reader_flags': readers, 'minimum_primary_readers': n,
            'counter_states': counter}


def pivotal_edge_flags(formula, mapping, info, k):
    rows = [r for r, (_, target) in enumerate(info['rows']) if target]
    n = info['n']
    pivots = []
    cuts = []
    for removed in range(k):
        left_values, right_values, values = {}, {}, {}
        for j in range(removed + 1, k):
            left_values[j] = [formula.var() for _ in rows]
            right_values[j] = [formula.var() for _ in rows]
            values[j] = [formula.var() for _ in rows]
            for edge_index, row in enumerate(rows):
                mask = info['rows'][row][0]
                for selectors, selected in [
                        (mapping['left'][j], left_values[j][edge_index]),
                        (mapping['right'][j], right_values[j][edge_index])]:
                    for source, selector in enumerate(selectors):
                        if source < n:
                            value = bool(mask & (1 << source))
                        elif source - n < removed:
                            value = mapping['val'][source - n][row]
                        elif source - n == removed:
                            value = False
                        else:
                            value = values[source - n][edge_index]
                        if isinstance(value, bool):
                            formula.add(-selector, selected if value else -selected)
                        else:
                            formula.add(-selector, -selected, value)
                            formula.add(-selector, selected, -value)
                op = mapping['op'][j]
                left, right, output = (left_values[j][edge_index],
                                       right_values[j][edge_index], values[j][edge_index])
                formula.add(-op, -left, -right, output)
                formula.add(-op, left, -output)
                formula.add(-op, right, -output)
                formula.add(op, left, right, -output)
                formula.add(op, -left, output)
                formula.add(op, -right, output)
        gate_pivots = []
        for edge_index, row in enumerate(rows):
            pivot = formula.var()
            gate_pivots.append(pivot)
            original_output = mapping['val'][k - 1][row]
            formula.add(-pivot, original_output)
            if removed == k - 1:
                formula.add(pivot, -original_output)
            else:
                cut_output = values[k - 1][edge_index]
                formula.add(-pivot, -cut_output)
                formula.add(pivot, -original_output, cut_output)
        pivots.append(gate_pivots)
        cuts.append({'left_values': left_values, 'right_values': right_values, 'values': values})
    return {'positive_row_indices': rows, 'pivotal_flags': pivots, 'cuts': cuts}


def add_edge_pivotal(formula, mapping, info, k, dirty_and_two=False):
    data = pivotal_edge_flags(formula, mapping, info, k)
    for pivots in data['pivotal_flags']:
        formula.add(*pivots)
    if dirty_and_two:
        negative_rows = [r for r, (_, target) in enumerate(info['rows']) if not target]
        dirty_flags, counters = [], []
        for j, pivots in enumerate(data['pivotal_flags']):
            dirty = formula.var()
            dirty_flags.append(dirty)
            bad_values = [mapping['val'][j][r] for r in negative_rows]
            formula.add(-dirty, mapping['op'][j])
            formula.add(-dirty, *bad_values)
            for bad in bad_values:
                formula.add(-mapping['op'][j], -bad, dirty)
            before = len(formula.clauses)
            counter = at_most_sequential(formula, [-pivot for pivot in pivots], len(pivots) - 2)
            assert len(formula.clauses) > before
            assert len(formula.clauses[-1]) <= 1
            formula.clauses[-1].insert(0, -dirty)
            counters.append(counter)
        data.update(dirty_and_flags=dirty_flags, negative_row_indices=negative_rows,
                    dirty_and_counter_states=counters)
    return data


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
    ap.add_argument('--primary-reader-bound', action='store_true')
    ap.add_argument('--edge-pivotal', action='store_true')
    ap.add_argument('--dirty-and-two-pivotal', action='store_true',
                    help='also enables --edge-pivotal')
    a = ap.parse_args()
    if a.solver is None:
        ap.error('Kissat was not found; provide --solver PATH')
    if not 0 <= a.min_and <= a.k:
        ap.error('--min-and must be between 0 and k')
    if a.max_and is not None and not a.min_and <= a.max_and <= a.k:
        ap.error('--max-and must be between min-and and k')
    g = json.loads((s.ROOT / 'graphs' / (a.graph + '.json')).read_text())
    info = s.graph_info(g['n'], g['edges'])
    if (a.edge_pivotal or a.dirty_and_two_pivotal) and not info['edges']:
        ap.error('pivotal-edge normal forms require a nonempty graph edge set')
    primary_graph_check = None
    if a.primary_reader_bound:
        try:
            primary_graph_check = validate_primary_reader_graph(info)
        except ValueError as error:
            ap.error(str(error))
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
    primary_reader_bound = (add_primary_reader_bound(
        f, mp, info['n'], a.k, input_budget['flags'] if input_budget else None)
        if a.primary_reader_bound else None)
    edge_pivotal_enabled = a.edge_pivotal or a.dirty_and_two_pivotal
    edge_pivotal = (add_edge_pivotal(f, mp, info, a.k, a.dirty_and_two_pivotal)
                    if edge_pivotal_enabled else None)
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
        justification = ('The explicit AND lower restriction is not globally justified here. '
                         'Without a separate global lower-bound justification, UNSAT describes '
                         'only the encoded minimum-circuit normal-form subclass. External solver '
                         'support is separate research evidence, not a Lean certificate.')
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
    if a.primary_reader_bound:
        name += '-primary-reader-bound'
    if edge_pivotal_enabled:
        name += '-edge-pivotal'
    if a.dirty_and_two_pivotal:
        name += '-dirty-two'
    d = s.ROOT / 'synthesis' / (name + '-' + str(time.time_ns()))
    d.mkdir(parents=True)
    f.write(d / 'input.cnf')
    (d / 'encoding.json').write_text(json.dumps({
        'info': info, 'mapping': mp, 'min_and': effective_min,
        'explicit_min_and': a.min_and, 'effective_min_and': effective_min,
        'mis_lower': a.mis_lower, 'mis_count': mis_count, 'mis_and_bound': mis_bound,
        'mis_lower_proof': mis_proof, 'min_and_counter_states': min_and_states,
        'conditional_explicit_min_and': explicit_assumption,
        'explicit_min_and_scope': ('UNSAT is restricted to the encoded normal-form subclass '
                                  'unless this explicit lower bound is justified globally.')
                                  if explicit_assumption else 'No additional explicit lower-bound assumption.',
        'max_and': a.max_and, 'max_and_counter_states': max_and_states,
        'max_and_justification': (
            'Requested restriction for a conditional witness search; '
            'no global upper bound on the AND count is asserted.')
            if a.max_and is not None else None,
        'lex': a.lex, 'input_budget': input_budget,
        'edge_pivotal': edge_pivotal,
        'dirty_and_two_pivotal': a.dirty_and_two_pivotal,
        'edge_pivotal_proof': (
            'Choose a minimum-size circuit. If forcing a gate false leaves all edge '
            'inputs true, monotonicity preserves every negative input, so constant '
            'folding removes that gate without changing the graph function. Thus '
            'each gate is pivotal on an edge; trailing OR-copy padding is also pivotal. '
            'Cut evaluations recompute every later gate exactly, including shared paths.')
            if edge_pivotal_enabled else None,
        'dirty_and_two_pivotal_proof': (
            'Among minimum-size circuits choose one minimizing the global number of '
            'AND gates true on a negative input. A dirty AND with only one pivotal '
            'edge can be replaced by the AND of that edge endpoints. On all other '
            'edges forcing the old gate false already preserves the output; on the '
            'unique pivotal edge the replacement is true. On negative inputs it is '
            'false, so downstream values only decrease. The size and operations stay '
            'fixed while the global number of dirty AND gates decreases. Therefore '
            'every dirty AND has at least two pivotal edges. MIS rows detect dirtiness '
            'exactly by monotonicity. This is a simultaneous minimum-circuit normal form.')
            if a.dirty_and_two_pivotal else None,
        'primary_reader_bound': primary_reader_bound,
        'primary_reader_graph_check': primary_graph_check,
        'primary_reader_bound_proof': (
            'In a graph of minimum degree at least 2 with no four-cycle, an input v '
            'cannot occur only once in a gate with a distinct primary sibling u. '
            'An AND sole reader would force every neighbor of v to equal u. An OR '
            'sole reader would force N(v) to be a subset of N(u), giving two common '
            'neighbors. Thus every input of a raw/raw gate occurs at another gate. '
            'Give a primary occurrence weight one half in a raw/raw gate and weight '
            'one in a gate with exactly one primary operand. Each essential input '
            'receives weight at least one, and each primary-reading gate distributes '
            'total weight one. Hence at least n gates read a primary input. '
            'Normalized real gates have distinct operands; padding gates copy an '
            'internal predecessor and never have primary operands.')
            if a.primary_reader_bound else None,
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
              'explicit_min_and_scope': ('Encoded normal-form subclass only unless externally '
                                        'justified as a global lower bound.')
                                        if explicit_assumption else 'No additional explicit lower-bound assumption.',
              'max_and': a.max_and,
              'conditional_max_and_restriction': a.max_and is not None,
              'lex': a.lex, 'input_budget': a.input_budget,
              'primary_reader_bound': a.primary_reader_bound,
              'edge_pivotal': edge_pivotal_enabled,
              'dirty_and_two_pivotal': a.dirty_and_two_pivotal,
              'exit': code, 'seconds': time.monotonic() - started, 'directory': str(d),
              'status': 'SAT' if code == 10 else 'UNSAT' if code == 20 else 'UNKNOWN'}
    if code == 10:
        result['gates'] = s.decode((d / 'solver.stdout').read_text(), mp)
        result.update(s.verify(info, result['gates']))
    (d / 'result.json').write_text(json.dumps(result, indent=2))
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
