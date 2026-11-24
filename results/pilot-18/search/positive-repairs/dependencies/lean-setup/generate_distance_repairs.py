"""Candidate-only SAT repair changing at most K gate descriptions; no solver."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
ROOT = Path('/tmp/oec/pequalnp-pilot-18')
HELPER_SHA = '857f7082cb81bda879891aba76a84e59f0a1b030f6c6c0eccf08f507cf96cd97'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def helper():
    path = ROOT / 'lean-setup/generate_local_repairs.py'
    if sha(path.read_bytes()) != HELPER_SHA:
        raise ValueError('Reviewed local repair helper SHA256 mismatch')
    spec = importlib.util.spec_from_file_location('reviewed_repair_helper', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def add_distance(base, cnf, meta, gates, budget):
    if not 0 <= budget < len(gates):
        raise ValueError('Distance budget outside gate count')
    old_variables, old_clauses = cnf.variables, len(cnf.clauses)
    keeps, matches = [], []
    for g, (op, a, b) in enumerate(gates):
        keep = cnf.var()
        match = [meta['ops'][g] if op == 'and' else -meta['ops'][g],
                 meta['lefts'][g][a], meta['rights'][g][b]]
        for literal in match:
            cnf.add(-keep, literal)
        cnf.add(keep, *[-literal for literal in match])
        keeps.append(keep)
        matches.append(match)
    counter = base.totalizer_atleast(cnf, [-keep for keep in keeps], budget + 1)
    if len(counter) != budget + 1:
        raise ValueError('Wrong totalizer width')
    cnf.add(-counter[budget])
    meta.update(local_repair_kind='gate_description_distance',
                gate_distance_budget=budget, keep_gate_flags=keeps,
                keep_gate_match_literals=matches, changed_gate_thresholds=counter,
                seed_gate_descriptions=gates, source_operand_order='ascending',
                distance_added_variables=cnf.variables-old_variables,
                distance_added_clauses=len(cnf.clauses)-old_clauses,
                variables=cnf.variables, clauses=len(cnf.clauses))
    return cnf, meta


def generate(source, output, base_path, budgets):
    if output.exists() or not budgets or budgets != sorted(set(budgets)) or not all(0 <= k <= 7 for k in budgets):
        raise ValueError('Fresh directory and distinct increasing budgets 0..7 required')
    h = helper()
    raw = source.read_bytes()
    data = json.loads(raw)
    validator = h.load(ROOT / 'validate_raw_candidate.py', 'distance_structure_checker', h.RAW_SHA)
    offset, gates, outwire = validator.check_structure(data)
    h.require(offset == 13 and len(gates) == 21, 'Production distance repair requires 21 augmented gates')
    canonical = {'inputs': 11, 'gate_wire_offset': 13, 'size': 21, 'output': outwire,
                 'gates': [[op, *sorted((a, b))] for op, a, b in gates]}
    base = h.load(base_path, 'reviewed_distance_base', h.BASE_SHA)
    output.mkdir(parents=True, exist_ok=False)
    (output / 'source.json').write_bytes(raw)
    summary = h.source_summary(canonical)
    (output / 'source-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    manifest = {'kind': 'candidate_only_gate_distance_repairs', 'complete': False,
                'source_sha256': sha(raw), 'program_sha256': sha(Path(__file__).read_bytes()),
                'local_repair_helper_sha256': HELPER_SHA, 'base_generator_sha256': h.BASE_SHA,
                'assigned_shard_exhaustion': False, 'cases': []}
    for budget in budgets:
        cnf, meta = h.repair(base, canonical, list(range(21)))
        parent_sha = sha(h.dimacs(cnf))
        cnf, meta = add_distance(base, cnf, meta, canonical['gates'], budget)
        meta.update(source_sha256=sha(raw), unrestricted_repair_parent_sha256=parent_sha,
                    local_repair_helper_sha256=HELPER_SHA, program=Path(__file__).name,
                    program_sha256=sha(Path(__file__).read_bytes()),
                    scope='Candidate-only distance-bounded repair; no global or assigned-shard exhaustion.')
        raw_cnf = h.dimacs(cnf)
        meta['sha256'] = sha(raw_cnf)
        name = f'distance-{budget:02d}'
        path = output / (name + '.cnf')
        path.write_bytes(raw_cnf)
        path.with_suffix('.json').write_text(json.dumps(meta, indent=2) + '\n')
        entry = {'case': name, 'budget': budget, 'variables': cnf.variables, 'clauses': len(cnf.clauses),
                 'cnf_sha256': meta['sha256'], 'metadata_sha256': sha(path.with_suffix('.json').read_bytes()),
                 'added_variables': meta['distance_added_variables'], 'added_clauses': meta['distance_added_clauses']}
        manifest['cases'].append(entry)
        print(json.dumps(entry), flush=True)
    manifest['complete'] = True
    (output / 'family.json').write_text(json.dumps(manifest, indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--base-generator', type=Path, default=ROOT / 'search_l1342_shard17_ancestorreverse.py')
    parser.add_argument('--budgets', nargs='+', type=int, default=[2, 3, 4, 5])
    args = parser.parse_args()
    generate(args.source, args.output, args.base_generator, args.budgets)
