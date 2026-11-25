"""Bounded, sequential AND-five census using the frozen reviewed T0 encoder."""
import argparse
from datetime import datetime, timezone
import hashlib
import itertools
import json
from pathlib import Path
import subprocess
import sys

import free_or_and_sat as model


ENCODER_SHA256 = 'f8b7264c258883137ed6a5e0eb488bf1a1e043c85e7270a6874adc7f29bb3b44'


def graph_isomorphism(source, target):
    """Return an explicit side-preserving or side-swapping graph isomorphism."""
    source = {tuple(edge) for edge in source}
    target = {tuple(edge) for edge in target}
    target_rows = {frozenset(b for a, b in target if a == row): row for row in range(6)}
    assert len(target_rows) == 6
    for swap in (False, True):
        edges = {(b, a) for a, b in source} if swap else source
        for columns in itertools.permutations(range(6)):
            transformed = [frozenset(columns[b] for a, b in edges if a == row)
                           for row in range(6)]
            if set(transformed) != set(target_rows):
                continue
            rows = [target_rows[row] for row in transformed]
            assert sorted(rows) == list(range(6))
            assert {(rows[a], columns[b]) for a, b in edges} == target
            return {'swap_sides': swap, 'rows': rows, 'columns': list(columns)}
    raise AssertionError('The stored punctured-Fano result does not match its census class')


def main(args):
    root = Path(__file__).resolve().parent
    encoder = root / 'free_or_and_sat.py'
    assert hashlib.sha256(encoder.read_bytes()).hexdigest() == ENCODER_SHA256
    manifest = json.loads((root / 'case_manifest_6x6.json').read_text())
    assert isinstance(manifest, dict) and isinstance(manifest['classes'], list)
    assert manifest['class_count'] == len(manifest['classes']) == 25
    cases = [case for case in manifest['classes'] if case['AND5_not_excluded_by_MIS']]
    assert len(cases) == 24
    cases.sort(key=lambda case: (case['maximal_independent_count'], -len(case['edges']), case['mask']))
    for case in cases:
        assert case['p'] == case['l'] == case['cover_number'] == 6
        assert min(case['degrees']) >= 2 and case['maximal_independent_count'] <= 32
        graph_path = root / 'cases6' / f"graph_{case['mask']}.json"
        stored = json.loads(graph_path.read_text())
        assert stored['p'] == stored['l'] == 6 and stored['edges'] == case['edges']
    known_path = root / 'free_or_and_fano_minor_and5_120s.result.json'
    known = json.loads(known_path.read_text())
    assert known['status'] == 'UNSAT' and known['and_budget'] == 5 and not known['pin_control']
    assert known['p'] == known['l'] == 6
    known_mask = manifest['controls']['fano_minus_incident_pair']
    known_case = next(case for case in cases if case['mask'] == known_mask)
    isomorphism = graph_isomorphism(known['edges'], known_case['edges'])
    plan = {'classes_total': 24, 'fresh_solver_calls': 23,
            'seconds_per_case': args.seconds, 'memory_mb': args.memory_mb,
            'encoder_sha256': ENCODER_SHA256, 'reused_mask': known_mask,
            'reuse_isomorphism': isomorphism, 'ordered_masks': [case['mask'] for case in cases]}
    if args.dry_run:
        print(json.dumps(plan, indent=2))
        return

    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    assert not (output / 'SUMMARY.json').exists(), 'Use a fresh output directory'
    results = []
    started = datetime.now(timezone.utc).isoformat()
    for case in cases:
        mask = case['mask']
        base = output / f'case_{mask}'
        if mask == known_mask:
            summary = {'mask': mask, 'status': 'UNSAT', 'reused': True,
                       'source_result': str(known_path), 'seconds': known['seconds'],
                       'isomorphism': isomorphism}
        else:
            assert hashlib.sha256(encoder.read_bytes()).hexdigest() == ENCODER_SHA256
            command = [sys.executable, str(encoder), '--graph',
                       str(root / 'cases6' / f'graph_{mask}.json'),
                       '--gates', '5', '--seconds', str(args.seconds),
                       '--memory-mb', str(args.memory_mb), '--output', str(base)]
            with base.with_suffix('.driver.stdout').open('w') as out, \
                    base.with_suffix('.driver.stderr').open('w') as err:
                process = subprocess.run(command, stdout=out, stderr=err)
            if process.returncode != 0:
                raise RuntimeError(f'Case {mask} failed; complete diagnostics retained')
            result = json.loads(base.with_suffix('.result.json').read_text())
            assert isinstance(result, dict) and result['and_budget'] == 5
            assert result['p'] == result['l'] == 6 and result['edges'] == case['edges']
            assert result['status'] in ('SAT', 'UNSAT', 'UNKNOWN'), result
            summary = {'mask': mask, 'status': result['status'], 'reused': False,
                       'seconds': result['seconds'], 'variables': result['variables'],
                       'clauses': result['clauses']}
            if result['status'] == 'SAT':
                record, verified = model.reconstruct(6, 6, [tuple(edge) for edge in case['edges']],
                                                     result['operands'], result['output_ands'])
                assert json.loads(json.dumps(record)) == json.loads(base.with_suffix('.circuit.json').read_text())
                assert verified['inputs_verified'] == 4096 and verified['tCount'] == 0
                assert verified['and_count'] <= 5 and verified['cover_number'] == 6
                summary.update(full_replay=verified,
                               proposed_AND_bound_counterexample=True,
                               target_counterexample=verified['counterexample'])
        summary.update(edge_count=len(case['edges']),
                       maximal_independent_count=case['maximal_independent_count'])
        results.append(summary)
        report = {'plan': plan, 'started_utc': started,
                  'updated_utc': datetime.now(timezone.utc).isoformat(),
                  'classes_completed': len(results), 'results': results,
                  'claim': 'Uncertified exact free-OR/limited-AND experiments; no Lean certificate.'}
        (output / 'SUMMARY.json').write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps(summary), flush=True)
        if summary['status'] == 'SAT':
            break


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', required=True)
    parser.add_argument('--seconds', type=int, default=30)
    parser.add_argument('--memory-mb', type=int, default=512)
    parser.add_argument('--dry-run', action='store_true')
    args = parser.parse_args()
    assert 0 < args.seconds <= 30 and 0 < args.memory_mb <= 512
    main(args)
