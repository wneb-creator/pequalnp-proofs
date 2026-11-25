"""Conditional full-row synthesis with one fixed original input used exactly once."""
import argparse
import itertools
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
import synthesize as s
import count_query as counting


def orbits(elements, images):
    parent = {item: item for item in elements}

    def find(item):
        while parent[item] != item:
            parent[item] = parent[parent[item]]
            item = parent[item]
        return item

    for image in images:
        for item, mapped in zip(elements, image):
            a, b = find(item), find(mapped)
            if a != b:
                parent[max(a, b)] = min(a, b)
    classes = {}
    for item in elements:
        classes.setdefault(find(item), []).append(item)
    return list(classes.values())


def vertex_orbits(info, automorphisms):
    vertices = list(range(info['n']))
    return orbits(vertices, automorphisms)


def stabilizer_symmetry(info, automorphisms, vertex):
    n = info['n']
    edge_set = set(map(tuple, info['edges']))
    stabilizer = [permutation for permutation in automorphisms
                  if permutation[vertex] == vertex]
    if list(range(n)) not in stabilizer:
        stabilizer.append(list(range(n)))
    for permutation in stabilizer:
        assert sorted(permutation) == list(range(n))
        assert permutation[vertex] == vertex
        assert {tuple(sorted((permutation[a], permutation[b])))
                for a, b in edge_set} == edge_set
    pairs = list(itertools.combinations(range(n), 2))
    pair_images = [[tuple(sorted((permutation[a], permutation[b]))) for a, b in pairs]
                   for permutation in stabilizer]
    pair_orbits = orbits(pairs, pair_images)
    representatives = [min(orbit, key=lambda pair: (pair[1], pair[0]))
                       for orbit in pair_orbits]
    representatives.sort(key=lambda pair: (pair[1], pair[0]))
    return {'representatives': representatives, 'automorphisms': stabilizer,
            'fixed_vertex': vertex, 'group_scope': 'fixed-vertex stabilizer only'}


def add_lex(formula, mapping, n, k):
    for j in range(k - 1):
        for right in range(n + j):
            for left in range(right):
                for next_left in range(left):
                    formula.add(-mapping['right'][j][right], -mapping['right'][j + 1][right],
                                -mapping['left'][j][left], -mapping['left'][j + 1][next_left])
                formula.add(-mapping['right'][j][right], -mapping['right'][j + 1][right],
                            -mapping['left'][j][left], -mapping['left'][j + 1][left],
                            -mapping['op'][j], mapping['op'][j + 1])


def add_single_use(formula, mapping, vertex, reader_op):
    occurrences = [selector for left, right in zip(mapping['left'], mapping['right'])
                   for selector in (left[vertex], right[vertex])]
    formula.add(*occurrences)
    states = counting.at_most_sequential(formula, occurrences, 1)
    if reader_op != 'any':
        for j, (left, right) in enumerate(zip(mapping['left'], mapping['right'])):
            required_op = mapping['op'][j] if reader_op == 'and' else -mapping['op'][j]
            formula.add(-left[vertex], required_op)
            formula.add(-right[vertex], required_op)
    return {'occurrence_selectors': occurrences, 'counter_states': states,
            'reader_op': reader_op}


def run(info, name, vertex, reader_op, k, seconds, solver, group):
    classes = vertex_orbits(info, group['automorphisms'])
    stabilizer = stabilizer_symmetry(info, group['automorphisms'], vertex)
    f, mapping = s.encode(info, k, normalized=True, symmetry=stabilizer,
                          undominated=True, oriented=True)
    add_lex(f, mapping, info['n'], k)
    for pad, op in zip(mapping['pad'], mapping['op']):
        f.add(-pad, -op)
    budget = counting.add_input_budget(f, mapping, info['n'], k)
    single = add_single_use(f, mapping, vertex, reader_op)
    essential = sorted({v for edge in info['edges'] for v in edge})
    directory = ROOT / 'synthesis' / (
        f'{name}-single-v{vertex}-{reader_op}-k{k}-{time.time_ns()}')
    directory.mkdir(parents=True)
    metadata = {
        'graph': name, 'info': info, 'mapping': mapping, 'k': k,
        'fixed_vertex': vertex, 'reader_op': reader_op,
        'scope': 'Conditional fixed-vertex case; this individual run is not a global lower bound.',
        'coverage_required': (
            'Global exclusion requires completed cases for every displayed vertex-orbit '
            'representative and both reader operations, or reader_op=any for each representative. '
            'It also requires the displayed pigeonhole condition and the reviewed normalization.'),
        'vertex_orbits': classes, 'vertex_representatives': [orbit[0] for orbit in classes],
        'automorphism_count': len(group['automorphisms']),
        'automorphism_enumeration_truncated': group['truncated'],
        'first_pair_symmetry': stabilizer,
        'normalization': {'dominance': True, 'oriented': True, 'lex': True},
        'essential_vertices': essential, 'input_budget': budget, 'single_use': single,
        'pigeonhole_condition': k + 1 < 2 * len(essential),
        'pigeonhole_justification': (
            'Every essential input is read. Every non-output gate has a later consumer, '
            'so among 2k operand slots at most k+1 read original inputs. '
            'If k+1 is less than twice the number of essential inputs, some essential '
            'input has exactly one occurrence. This is applied after normalization, '
            'then that vertex is mapped to an orbit representative.'),
    }
    f.write(directory / 'input.cnf')
    (directory / 'encoding.json').write_text(json.dumps(metadata, indent=2))
    started = time.monotonic()
    with (directory / 'solver.stdout').open('w') as stdout, \
            (directory / 'solver.stderr').open('w') as stderr:
        process = subprocess.Popen([str(solver), f'--time={seconds}',
                                    str(directory / 'input.cnf')], stdout=stdout, stderr=stderr)
        print(json.dumps({'event': 'started', 'pid': process.pid,
                          'directory': str(directory), 'vertex': vertex,
                          'reader_op': reader_op}), flush=True)
        code = process.wait()
    output = (directory / 'solver.stdout').read_text()
    result = {'graph': name, 'k': k, 'vertex': vertex, 'reader_op': reader_op,
              'conditional': True, 'global_exclusion_claimed': False,
              'exit': code, 'seconds': time.monotonic() - started,
              'status': 'SAT' if code == 10 else 'UNSAT' if code == 20 else 'UNKNOWN',
              'vars': f.nvars, 'clauses': len(f.clauses), 'directory': str(directory)}
    if code == 10:
        assert 's SATISFIABLE' in output
        gates = s.decode(output, mapping)
        result.update(s.verify(info, gates))
        occurrences = [(j, gate['op']) for j, gate in enumerate(gates)
                       for source in (gate['left'], gate['right']) if source == vertex]
        assert len(occurrences) == 1
        assert reader_op == 'any' or occurrences[0][1] == reader_op
        result['gates'] = gates
        result['sole_reader'] = occurrences[0]
    elif code == 20:
        assert 's UNSATISFIABLE' in output
    (directory / 'result.json').write_text(json.dumps(result, indent=2))
    print(json.dumps(result), flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--graph', default='Heawood12inc')
    parser.add_argument('--k', type=int, default=20)
    parser.add_argument('--vertex', type=int)
    parser.add_argument('--reader-op', choices=('any', 'and', 'or'), default='any')
    parser.add_argument('--seconds', type=int, default=600)
    parser.add_argument('--solver', type=Path, default=s.DEFAULT_SOLVER)
    args = parser.parse_args()
    graph = json.loads((ROOT / 'graphs' / (args.graph + '.json')).read_text())
    info = s.graph_info(graph['n'], graph['edges'])
    group = s.first_pair_symmetry(info)
    classes = vertex_orbits(info, group['automorphisms'])
    essential = {v for edge in info['edges'] for v in edge}
    print(json.dumps({'event': 'orbits', 'graph': args.graph,
                      'automorphisms': len(group['automorphisms']),
                      'enumeration_truncated': group['truncated'],
                      'vertex_orbits': classes, 'representatives': [orbit[0] for orbit in classes],
                      'essential_inputs': len(essential),
                      'input_slots_bound': args.k + 1,
                      'pigeonhole_condition': args.k + 1 < 2 * len(essential)}), flush=True)
    if args.vertex is None:
        return
    if args.solver is None:
        parser.error('Kissat was not found; provide --solver PATH')
    if args.vertex not in essential:
        parser.error('--vertex must name a nonisolated input')
    if args.k < 1 or args.seconds < 1:
        parser.error('--k and --seconds must be positive')
    run(info, args.graph, args.vertex, args.reader_op, args.k,
        args.seconds, args.solver, group)


if __name__ == '__main__':
    main()
