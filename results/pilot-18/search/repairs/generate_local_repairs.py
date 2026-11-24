"""Candidate-only SAT repair of a few arbitrary gates in a supplied circuit.

No solver is invoked. Free gate count defaults to 3..7, with no clean prefix or
junk requirement. The output selector and every gate outside the holes are fixed.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import random
import sys

sys.dont_write_bytecode = True
ROOT = Path('/tmp/oec/pequalnp-pilot-18')
BASE_SHA = 'b10d8832060d1c554fd3daa563b7159d515a3c55adc49718989eaa9bd0c2f24f'
RAW_SHA = 'd244bfc58d60560041c5890592f3c2de90905c78fcd058f691b27e7785131401'
EDGES = [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(path, name, expected):
    require(sha(path.read_bytes()) == expected, 'Dependency SHA256 mismatch')
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def target(mask):
    return any(mask & (1 << u) and mask & (1 << v) for u, v in EDGES)


def scalar_values(gates, mask, flip=None):
    values = [bool(mask & (1 << v)) for v in range(11)] + [False, True]
    for g, (op, a, b) in enumerate(gates):
        value = values[a] and values[b] if op == 'and' else values[a] or values[b]
        values.append(not value if g == flip else value)
    return values


def source_summary(data):
    gates, output = data['gates'], data['output']
    positive_errors, negative_errors = [], []
    for mask in range(2048):
        actual = scalar_values(gates, mask)[output]
        if actual != target(mask):
            (positive_errors if target(mask) else negative_errors).append(mask)
    maximal = [m for m in range(2048) if not target(m) and all(
        m & (1 << v) or target(m | (1 << v)) for v in range(11))]
    edge_rows = [(1 << u) | (1 << v) for u, v in EDGES]
    boundary_errors = [m for m in edge_rows + maximal if scalar_values(gates, m)[output] != target(m)]
    influence = [sum(scalar_values(gates, m, flip=g)[output] == target(m)
                     for m in boundary_errors) for g in range(len(gates))]
    live = set()
    if output >= 13:
        live.add(output - 13)
    for g in reversed(range(len(gates))):
        if g in live:
            live.update(w - 13 for w in gates[g][1:] if w >= 13)
    return {'full_2048_false_negative_count': len(positive_errors),
            'full_2048_false_positive_count': len(negative_errors),
            'boundary_false_negative_masks': [m for m in edge_rows if m in positive_errors],
            'boundary_false_positive_masks': [m for m in maximal if m in negative_errors],
            'boundary_error_masks': boundary_errors, 'error_flip_influence': influence,
            'live_gates': sorted(live), 'dead_gates': sorted(set(range(len(gates))) - live),
            'exact_target': not positive_errors and not negative_errors}


def choose_holes(data, summary, count, mode, rng):
    gates = data['gates']
    all_gates = list(range(len(gates)))
    live = summary['live_gates']
    dead = summary['dead_gates']
    output = data['output'] - 13
    holes = []

    def add(g):
        if 0 <= g < len(gates) and g not in holes and len(holes) < count:
            holes.append(g)

    if mode == 'tail_and_dead':
        add(output)
        if dead:
            add(rng.choice(dead))
        for g in reversed(live):
            add(g)
    elif mode == 'error_influence':
        order = list(all_gates)
        rng.shuffle(order)
        order.sort(key=lambda g: summary['error_flip_influence'][g], reverse=True)
        if dead:
            add(rng.choice(dead))
        for g in order:
            add(g)
    elif mode == 'connected':
        adjacency = [set() for _ in gates]
        for g, (_, a, b) in enumerate(gates):
            for wire in (a, b):
                if wire >= 13:
                    adjacency[g].add(wire - 13)
                    adjacency[wire - 13].add(g)
        add(rng.choice(live or all_gates))
        while len(holes) < count:
            frontier = sorted(set().union(*(adjacency[g] for g in holes)) - set(holes))
            if not frontier:
                break
            add(rng.choice(frontier))
    else:
        require(mode == 'uniform', 'Unknown hole-selection mode')
        if rng.randrange(4):
            add(output)
    remainder = [g for g in all_gates if g not in holes]
    rng.shuffle(remainder)
    for g in remainder:
        add(g)
    require(len(holes) == count, 'Failed to select requested number of holes')
    return sorted(holes)


def dimacs(cnf):
    return (f'p cnf {cnf.variables} {len(cnf.clauses)}\n' +
            ''.join(' '.join(map(str, c)) + ' 0\n' for c in cnf.clauses)).encode('ascii')


def repair(base, source, holes):
    gates, output = source['gates'], source['output']
    size = len(gates)
    require(size in (21, 22), 'Size22 is reserved for compatibility controls')
    require(holes == sorted(set(holes)) and all(0 <= g < size for g in holes), 'Invalid holes')
    cnf, meta = base.build(size=size, first_junk=0, second_junk=False, prefix_sort=False,
                          last_output=False, live=False, productive_prefix=False)
    original_hash, original_count = sha(dimacs(cnf)), len(cnf.clauses)
    marker = [meta['junk'][0]]
    require(cnf.clauses.count(marker) == 1, 'Forced-junk unit must occur exactly once')
    removed_index = cnf.clauses.index(marker)
    cnf.clauses.pop(removed_index)
    pins = []
    fixed = sorted(set(range(size)) - set(holes))
    for g in fixed:
        op, a, b = gates[g]
        require(op in ('and', 'or') and 0 <= a <= b < 13 + g, 'Invalid fixed gate')
        pins += [[meta['ops'][g] if op == 'and' else -meta['ops'][g]],
                 [meta['lefts'][g][a]], [meta['rights'][g][b]]]
    pins.append([meta['output_selectors'][output]])
    cnf.clauses.extend(pins)
    require(marker not in cnf.clauses, 'Forced junk unit was retained')
    meta.update(enforce_junk=False, clean_prefix_length=0,
                first_junk_field_means_clean_prefix_boundary=True,
                forced_first_junk_unit_removed=marker, removed_unit_original_index=removed_index,
                base_with_forced_junk_sha256=original_hash, base_with_forced_junk_clauses=original_count,
                local_repair=True, free_gates=holes, fixed_gates=fixed,
                fixed_gate_descriptions=[gates[g] for g in fixed], pin_clauses=pins,
                fixed_output_wire=output, candidate_only=size == 21,
                known22_control=size == 22, assigned_shard_exhaustion=False,
                scope='Candidate-only local repair; no global or assigned-shard exhaustion.',
                base_generator_sha256=BASE_SHA, program=Path(__file__).name,
                program_sha256=sha(Path(__file__).read_bytes()),
                variables=cnf.variables, clauses=len(cnf.clauses))
    return cnf, meta


def generate(source, output, base_path, samples, seed, minimum, maximum):
    require(not output.exists(), 'Output directory must be fresh')
    require(1 <= samples <= 500 and 3 <= minimum <= maximum <= 7, 'Invalid bounded family size')
    raw = source.read_bytes()
    data = json.loads(raw)
    validator = load(ROOT / 'validate_raw_candidate.py', 'raw_structure_checker', RAW_SHA)
    offset, gates, outwire = validator.check_structure(data)
    require(offset == 13 and len(gates) == 21, 'Production repair source must have 21 augmented gates')
    # Sorting operands is the base encoding's commutativity convention only.
    canonical = {'inputs': 11, 'gate_wire_offset': 13, 'gates': [[op, *sorted((a, b))] for op, a, b in gates],
                 'output': outwire, 'size': 21}
    base = load(base_path, 'reviewed_local_repair_base', BASE_SHA)
    require(base.N == 11 and base.EDGES == EDGES, 'Base graph mismatch')
    summary = source_summary(canonical)
    rng = random.Random(seed)
    output.mkdir(parents=True, exist_ok=False)
    (output / 'source.json').write_bytes(raw)
    (output / 'source-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    manifest = {'kind': 'candidate_only_local_repairs', 'complete': False, 'seed': seed, 'samples': samples,
                'source_sha256': sha(raw), 'source_summary_sha256': sha((output / 'source-summary.json').read_bytes()),
                'program_sha256': sha(Path(__file__).read_bytes()), 'base_generator_sha256': BASE_SHA,
                'assigned_shard_exhaustion': False, 'cases': []}
    modes = ['tail_and_dead', 'error_influence', 'connected', 'uniform']
    for index in range(samples):
        count = minimum + index % (maximum - minimum + 1)
        mode = modes[index % len(modes)]
        holes = choose_holes(canonical, summary, count, mode, rng)
        cnf, meta = repair(base, canonical, holes)
        name = f'r{index:04d}-free{count:02d}'
        meta.update(source_sha256=sha(raw), family_seed=seed, family_index=index, selection_mode=mode)
        raw_cnf = dimacs(cnf)
        meta['sha256'] = sha(raw_cnf)
        path = output / (name + '.cnf')
        path.write_bytes(raw_cnf)
        path.with_suffix('.json').write_text(json.dumps(meta, indent=2) + '\n')
        entry = {'case': name, 'free_gates': holes, 'selection_mode': mode,
                 'cnf_sha256': meta['sha256'], 'metadata_sha256': sha(path.with_suffix('.json').read_bytes()),
                 'variables': cnf.variables, 'clauses': len(cnf.clauses)}
        manifest['cases'].append(entry)
        print(json.dumps(entry), flush=True)
    manifest['complete'] = True
    (output / 'family.json').write_text(json.dumps(manifest, indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--base-generator', type=Path, default=ROOT / 'search_l1342_shard17_ancestorreverse.py')
    parser.add_argument('--samples', type=int, default=20)
    parser.add_argument('--seed', type=int, default=134218)
    parser.add_argument('--min-free', type=int, default=3)
    parser.add_argument('--max-free', type=int, default=7)
    args = parser.parse_args()
    generate(args.source, args.output, args.base_generator, args.samples, args.seed, args.min_free, args.max_free)
