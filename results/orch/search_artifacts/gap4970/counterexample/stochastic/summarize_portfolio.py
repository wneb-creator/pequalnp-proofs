import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path

P = Path(__file__).resolve().parent
records = json.loads((P / 'portfolio1-results.json').read_text())
assert len(records) == 5 and all(r['exit_code'] in (0, 75) for r in records)
results = []
for record in records:
    name = record['graph']
    graph = json.loads((P / (name + '.json')).read_text())
    full_log = (P / (name + '-portfolio1.stdout')).read_text()
    done = re.search(r'^(?:DONE|STOPPED) no_counterexample iterations=(\d+) seconds=([0-9.]+)$', full_log, re.M)
    assert done
    best = json.loads((P / (name + '-portfolio1.best-hyp.json')).read_text())
    results.append({'graph': name, 'target_gates': graph['target_gates'], 'posted_bound': graph['target_gates'] + 1,
                    'iterations': int(done[1]), 'seconds': float(done[2]),
                    'best_boundary_false_negatives': best['boundary_false_negatives'],
                    'best_boundary_false_positives': best['boundary_false_positives'],
                    'best_missing_star_edges': best['missing_star_edges'], 'best_tCount': best['tCount'],
                    'verdict': 'NO_COUNTEREXAMPLE_FOUND', 'full_run_record': record})
summary = {'scope': 'Heuristic search, not a proof or refutation', 'results': results,
           'total_iterations': sum(r['iterations'] for r in results), 'total_seconds': sum(r['seconds'] for r in results)}
(P / 'portfolio1-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
for r in results:
    print(r['graph'], r['iterations'], 'mutations;', r['seconds'], 'seconds; best errors', r['best_boundary_false_negatives'], r['best_boundary_false_positives'])
print('TOTAL', summary['total_iterations'], 'mutations;', summary['total_seconds'], 'seconds; no counterexample')
