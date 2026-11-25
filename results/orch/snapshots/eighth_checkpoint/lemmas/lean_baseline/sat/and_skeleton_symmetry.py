import itertools

from and_skeleton_sat import evaluate, normalize


def validate_symmetry(data, symmetry):
    n = data['inputs']
    edges = {tuple(sorted(edge)) for edge in data['edges']}
    assert symmetry['inputs'] == n
    assert {tuple(sorted(edge)) for edge in symmetry['edges']} == edges
    pairs = set(itertools.combinations(range(n), 2)) - edges
    representatives = [tuple(pair) for pair in symmetry['representatives']]
    assert len(representatives) == 2 and len(set(representatives)) == 2
    assert all(pair in pairs for pair in representatives)
    maps = {}
    for item in symmetry['pair_maps']:
        pair = tuple(item['pair'])
        target = tuple(item['representative'])
        permutation = item['to_representative']
        assert pair in pairs and pair not in maps and target in representatives
        assert sorted(permutation) == list(range(n))
        assert {tuple(sorted((permutation[a], permutation[b]))) for a, b in edges} == edges
        assert tuple(sorted(permutation[v] for v in pair)) == target
        maps[pair] = (target, permutation)
    assert set(maps) == pairs
    for vertex in range(n):
        assert any(vertex in pair for pair in pairs)
    return representatives, maps


def rephase(data, seed, symmetry):
    representatives, maps = validate_symmetry(data, symmetry)
    seed = normalize(seed)
    n = data['inputs']
    choices = []
    for pair in maps:
        values, final = evaluate(seed, sum(1 << vertex for vertex in pair))
        if any(values[n:]):
            choices.append((final, pair))
    if not choices:
        return seed, {'rephased': False, 'reason': 'phase has no dirty independent pair'}
    _, pair = min(choices)
    representative, permutation = maps[pair]

    def source(v):
        return permutation[v] if v < n else v

    transformed = normalize({
        'inputs': n,
        'and_gates': [
            {'left': [source(v) for v in gate['left']],
             'right': [source(v) for v in gate['right']]}
            for gate in seed['and_gates']
        ],
        'output': [source(v) for v in seed['output']],
    })
    for test in data['tests']:
        mask = test['mask']
        moved = sum(1 << permutation[v] for v in range(n) if mask >> v & 1)
        old_values, old_final = evaluate(seed, mask)
        new_values, new_final = evaluate(transformed, moved)
        assert old_values[n:] == new_values[n:] and old_final == new_final
    mask = sum(1 << v for v in representative)
    values, final = evaluate(transformed, mask)
    assert any(values[n:])
    return transformed, {
        'rephased': True, 'old_dirty_pair': list(pair),
        'new_dirty_pair': list(representative), 'permutation': permutation,
        'phase_output_on_dirty_pair': final,
    }


def representative_clauses(input_literals, representatives):
    assert len(representatives) == 2
    n = len(input_literals)
    masks = [sum(1 << v for v in pair) for pair in representatives]
    assert masks[0] != masks[1]
    different = masks[0] ^ masks[1]
    pivot = (different & -different).bit_length() - 1
    pivot_literal = input_literals[pivot]
    clauses = []
    for vertex, literal in enumerate(input_literals):
        first = bool(masks[0] >> vertex & 1)
        second = bool(masks[1] >> vertex & 1)
        if first == second:
            clauses.append([literal if first else -literal])
        elif vertex != pivot:
            same = first == bool(masks[0] >> pivot & 1)
            target = pivot_literal if same else -pivot_literal
            clauses.extend([[-literal, target], [literal, -target]])
    return clauses
