"""Enumerate C4-free 3-by-3 graph cases satisfying the necessary serving condition."""
import importlib.util
import itertools
import json
from pathlib import Path

root = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('serve_sat', root / 'serve_sat.py')
serve_sat = importlib.util.module_from_spec(spec)
spec.loader.exec_module(serve_sat)
permutations = list(itertools.permutations(range(3)))
classes = {}
for mask in range(1, 1 << 9):
    edges = [(a, b) for a in range(3) for b in range(3) if mask >> (3 * a + b) & 1]
    if not serve_sat.no_four_cycle(3, 3, edges):
        continue
    degrees_left = [sum(a == u for a, b in edges) for u in range(3)]
    degrees_right = [sum(b == v for a, b in edges) for v in range(3)]
    if any(degrees_left[a] < 2 and degrees_right[b] < 2 for a, b in edges):
        continue
    representatives = []
    for left in permutations:
        for right in permutations:
            representatives.append(sum(1 << (3 * left[a] + right[b]) for a, b in edges))
            representatives.append(sum(1 << (3 * left[b] + right[a]) for a, b in edges))
    canonical = min(representatives)
    classes.setdefault(canonical, 0)
    classes[canonical] += 1
cases = []
case_dir = root / 'cases'
case_dir.mkdir(exist_ok=True)
for mask in sorted(classes):
    edges = [(a, b) for a in range(3) for b in range(3) if mask >> (3 * a + b) & 1]
    tau = serve_sat.cover_number(3, 3, edges)
    case = {'p': 3, 'l': 3, 'edges': edges, 'mask': mask, 'cover_number': tau,
            'counterexample_gates': len(edges) + tau - 2, 'labeled_cases': classes[mask]}
    (case_dir / f'graph_{mask}.json').write_text(json.dumps(case, indent=2) + '\n')
    cases.append(case)
report = {'classes': cases, 'class_count': len(cases), 'labeled_count': sum(classes.values()),
          'excluded': 'Empty graphs are trivial; an isolated K2 component contradicts the serving-star hypothesis.'}
(root / 'case_manifest.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'class_count': len(cases), 'labeled_count': sum(classes.values()),
                  'gate_counts': sorted(set(case['counterexample_gates'] for case in cases))}))
