"""Candidate-only distance repairs after rescheduling, with unrestricted output.

Existing families are never modified. No solver is invoked. Each supplied seed
must have 21 gates and exactly 20 live gates. Its unused gate is replaced by a
missing-edge AND, moved to three positions, and the live core is topologically
rescheduled. Every core value and the selected source output are checked on all
2048 inputs before any formula is written.
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
DISTANCE_SHA = '39e65cae78a5bd8dd6417cf1132fb77187867d6765f20d62e10fd51bcedc9da1'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def dependencies():
    path = ROOT / 'lean-setup/generate_distance_repairs.py'
    if sha(path.read_bytes()) != DISTANCE_SHA:
        raise ValueError('Distance helper SHA256 mismatch')
    spec = importlib.util.spec_from_file_location('reviewed_distance_repairs', path)
    distance = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(distance)
    helper = distance.helper()
    base = helper.load(ROOT / 'search_l1342_shard17_ancestorreverse.py', 'rescheduled_base', helper.BASE_SHA)
    return distance, helper, base


def reorder(data, summary, mode, position, rng, helper):
    gates, core, dead = data['gates'], summary['live_gates'], summary['dead_gates']
    helper.require(len(gates) == 21 and len(core) == 20 and len(dead) == 1, 'Expected 20 live gates and one unused slot')
    helper.require(position in (0, 10, 20), 'Unsupported dead-slot position')
    missing = summary['boundary_false_negative_masks']
    helper.require(bool(missing), 'Seed must miss an edge; exact candidates should be validated directly')
    endpoints = [v for v in range(11) if missing[0] & (1 << v)]
    helper.require(len(endpoints) == 2, 'Missing boundary row is not an edge')
    predecessors = {g: {w - 13 for w in gates[g][1:] if w >= 13} for g in core}
    helper.require(all(pred <= set(core) for pred in predecessors.values()), 'Live core reads a supposedly dead gate')
    pending, emitted, order = set(core), set(), []
    while pending:
        available = sorted(g for g in pending if predecessors[g] <= emitted)
        helper.require(bool(available), 'Cyclic core')
        if mode == 'original':
            chosen = available[0]
        elif mode == 'random':
            chosen = rng.choice(available)
        else:
            raise ValueError('Unsupported schedule mode')
        order.append(chosen)
        emitted.add(chosen)
        pending.remove(chosen)
    helper.require(order[-1] == data['output'] - 13, 'All-live core output must be last')
    order.insert(position, dead[0])
    mapping = {old: new for new, old in enumerate(order)}
    transformed = []
    for old in order:
        if old == dead[0]:
            transformed.append(['and', *endpoints])
        else:
            op, a, b = gates[old]
            move = lambda wire: wire if wire < 13 else 13 + mapping[wire - 13]
            transformed.append([op, *sorted((move(a), move(b)))])
    result = {'inputs': 11, 'gate_wire_offset': 13, 'size': 21, 'gates': transformed,
              'output': 13 + mapping[data['output'] - 13]}
    for g, (_, a, b) in enumerate(transformed):
        helper.require(0 <= a <= b < 13 + g, 'Rescheduled reference is not acyclic')
    for mask in range(2048):
        before = helper.scalar_values(gates, mask)
        after = helper.scalar_values(transformed, mask)
        helper.require(before[data['output']] == after[result['output']], 'Rescheduling changed the source output')
        helper.require(all(before[13 + old] == after[13 + mapping[old]] for old in core), 'Rescheduling changed a live gate value')
        helper.require(after[13 + position] == bool(mask & (1 << endpoints[0]) and mask & (1 << endpoints[1])), 'Incorrect missing-edge slot')
    info = {'schedule_mode': mode, 'dead_position': position, 'old_to_new_gate': mapping,
            'old_dead_gate': dead[0], 'replacement_edge': endpoints,
            'all_2048_core_and_output_values_preserved': True}
    return result, info


def unrestricted_distance(distance, helper, base, data, budget):
    size = len(data['gates'])
    cnf, meta = helper.repair(base, data, list(range(size)))
    pinned_parent_hash = sha(helper.dimacs(cnf))
    marker = [meta['output_selectors'][data['output']]]
    helper.require(meta['pin_clauses'] == [marker] and cnf.clauses.count(marker) == 1,
                   'Expected exactly one explicit source-output pin')
    output_index = cnf.clauses.index(marker)
    cnf.clauses.pop(output_index)
    meta.pop('fixed_output_wire')
    meta.update(pin_clauses=[], output_selection_free=True, seed_output_wire=data['output'],
                removed_output_pin=marker, removed_output_pin_index=output_index,
                output_pinned_parent_sha256=pinned_parent_hash,
                variables=cnf.variables, clauses=len(cnf.clauses))
    cnf, meta = distance.add_distance(base, cnf, meta, data['gates'], budget)
    helper.require(marker not in cnf.clauses, 'Source-output pin survived')
    meta.update(program=Path(__file__).name, program_sha256=sha(Path(__file__).read_bytes()),
                distance_helper_sha256=DISTANCE_SHA,
                scope='Candidate-only rescheduled gate-distance repair with unrestricted output; no exhaustion claim.')
    return cnf, meta


def generate(sources, output, seed, budgets):
    if output.exists() or not 1 <= len(sources) <= 4 or budgets != sorted(set(budgets)) or not budgets or not all(1 <= k <= 7 for k in budgets):
        raise ValueError('Fresh directory, 1..4 sources and distinct increasing budgets 1..7 required')
    distance, helper, base = dependencies()
    validator = helper.load(ROOT / 'validate_raw_candidate.py', 'rescheduled_structure_checker', helper.RAW_SHA)
    loaded = []
    for path in sources:
        raw = path.read_bytes()
        obj = json.loads(raw)
        offset, gates, outwire = validator.check_structure(obj)
        helper.require(offset == 13 and len(gates) == 21, 'Source must have 21 augmented gates')
        data = {'inputs': 11, 'gate_wire_offset': 13, 'size': 21, 'output': outwire,
                'gates': [[op, *sorted((a, b))] for op, a, b in gates]}
        loaded.append((raw, data, helper.source_summary(data)))
    rng = random.Random(seed)
    output.mkdir(parents=True, exist_ok=False)
    manifest = {'kind': 'candidate_only_rescheduled_multisource_freeoutput_repairs', 'complete': False,
                'seed': seed, 'budgets': budgets, 'program_sha256': sha(Path(__file__).read_bytes()),
                'distance_helper_sha256': DISTANCE_SHA, 'local_helper_sha256': distance.HELPER_SHA,
                'base_generator_sha256': helper.BASE_SHA, 'assigned_shard_exhaustion': False,
                'sources': [], 'variants': [], 'cases': []}
    for si, (raw, data, summary) in enumerate(loaded):
        source_name = f'source-{si:02d}.json'
        (output / source_name).write_bytes(raw)
        manifest['sources'].append({'file': source_name, 'sha256': sha(raw), 'summary': summary})
        for mode in ('original', 'random'):
            # Reuse one randomly selected core order at all three slot positions.
            state = rng.getstate()
            for position in (0, 10, 20):
                rng.setstate(state)
                variant, info = reorder(data, summary, mode, position, rng, helper)
                variant_name = f's{si:02d}-{mode}-p{position:02d}'
                variant_path = output / (variant_name + '.seed.json')
                variant_path.write_text(json.dumps(variant, indent=2) + '\n')
                entry = {'variant': variant_name, 'source_index': si, 'sha256': sha(variant_path.read_bytes()), **info}
                manifest['variants'].append(entry)
                for budget in budgets:
                    cnf, meta = unrestricted_distance(distance, helper, base, variant, budget)
                    meta.update(source_sha256=sha(raw), variant_seed_sha256=entry['sha256'],
                                variant_name=variant_name, family_seed=seed, source_index=si, **info)
                    raw_cnf = helper.dimacs(cnf)
                    meta['sha256'] = sha(raw_cnf)
                    name = f'{variant_name}-k{budget:02d}'
                    path = output / (name + '.cnf')
                    path.write_bytes(raw_cnf)
                    path.with_suffix('.json').write_text(json.dumps(meta, indent=2) + '\n')
                    case = {'case': name, 'variant': variant_name, 'source_index': si, 'budget': budget,
                            'dead_position': position, 'schedule_mode': mode,
                            'variables': cnf.variables, 'clauses': len(cnf.clauses),
                            'cnf_sha256': meta['sha256'], 'metadata_sha256': sha(path.with_suffix('.json').read_bytes())}
                    manifest['cases'].append(case)
                    print(json.dumps(case), flush=True)
    manifest['complete'] = True
    (output / 'family.json').write_text(json.dumps(manifest, indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--sources', nargs='+', type=Path, required=True)
    parser.add_argument('--budgets', nargs='+', type=int, default=[4, 5])
    parser.add_argument('--seed', type=int, default=134222)
    args = parser.parse_args()
    generate(args.sources, args.output, args.seed, args.budgets)
