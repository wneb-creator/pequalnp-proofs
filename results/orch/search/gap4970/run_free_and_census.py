"""Short bounded free-AND/limited-OR census over the reviewed 4-by-4 classes."""
import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path


def density_priority(case):
    n = case['p'] + case['l']
    adjacency = [set() for _ in range(n)]
    for a, b in case['edges']:
        adjacency[a].add(case['p'] + b)
        adjacency[case['p'] + b].add(a)
    unseen = set(range(n))
    excess = 0
    while unseen:
        todo = [min(unseen)]
        component = set()
        while todo:
            v = todo.pop()
            if v in component:
                continue
            component.add(v)
            todo.extend(adjacency[v] - component)
        unseen -= component
        edges = sum(len(adjacency[v]) for v in component) // 2
        excess = max(excess, edges - len(component))
    return (-excess, -len(case['edges']), case['mask'])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir', required=True)
    parser.add_argument('--seconds', type=int, default=5)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((root / 'case_manifest_4x4.json').read_text())
    cases = sorted(manifest['classes'], key=density_priority)
    results = []
    for case in cases:
        base = output / f"case_{case['mask']}"
        budget = len(case['edges']) - 2
        command = [sys.executable, str(root / 'free_and_or_sat.py'),
                   '--graph', str(root / 'cases4' / f"graph_{case['mask']}.json"),
                   '--or-gates', str(budget), '--seconds', str(args.seconds), '--output', str(base)]
        with base.with_suffix('.driver.stdout').open('w') as out, base.with_suffix('.driver.stderr').open('w') as err:
            process = subprocess.run(command, stdout=out, stderr=err)
        if process.returncode != 0:
            raise RuntimeError(f"Case {case['mask']} driver exited {process.returncode}; full diagnostics retained")
        result = json.loads(base.with_suffix('.result.json').read_text())
        cnf = base.with_suffix('.cnf')
        summary = {
            'mask': case['mask'], 'OR_budget': budget, 'status': result['status'],
            'seconds': result['seconds'], 'component_edge_excess': -density_priority(case)[0],
            'violates_proposed_or_bound': result.get('violates_proposed_or_bound', False),
            'target_counterexample': result.get('target_counterexample', False),
            'regenerable_cnf': {'bytes': cnf.stat().st_size,
                'sha256': hashlib.sha256(cnf.read_bytes()).hexdigest(), 'disposition': 'deleted after solve'}}
        cnf.unlink()
        results.append(summary)
        report = {
            'results': results, 'classes_completed': len(results), 'classes_total': len(cases),
            'labeled_cases_in_scope': manifest['labeled_count'],
            'claim': 'Uncertified exact free-AND/limited-OR SAT experiments; no Lean lower-bound certificate.'}
        (output / 'SUMMARY.json').write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps(summary), flush=True)
        if result['status'] == 'SAT':
            break


if __name__ == '__main__':
    main()
