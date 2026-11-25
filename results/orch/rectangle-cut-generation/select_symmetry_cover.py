import argparse
import json
import time
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import csr_matrix

BASE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--data', default=str(BASE / 'dynamic-symmetry-original13'))
parser.add_argument('--banks', default=str(BASE / 'dynamic-cross-v1/banks.json'))
parser.add_argument('--output', default=str(BASE / 'dynamic-symmetry-selected-v1'))
parser.add_argument('--matrices', default=str(BASE / 'rectangle-all-certificates.json'))
args = parser.parse_args()
DATA = Path(args.data)
matrices = json.loads(Path(args.matrices).read_text())
permutations = json.loads((DATA / 'permutations.json').read_text())
banks = json.loads(Path(args.banks).read_text())
margins = np.load(DATA / 'margins.npy')
coverage = margins.reshape((len(banks), -1)) > 0
covered_banks = coverage.any(axis=1)
representatives = {}
for i in range(coverage.shape[1]):
    covered = tuple(np.flatnonzero(coverage[:, i]).tolist())
    if not covered:
        continue
    mi, pi = divmod(i, 120)
    rank = (max(abs(x) for row in matrices[mi]['weights'] for x in row), mi, pi)
    if covered not in representatives or rank < representatives[covered][0]:
        representatives[covered] = (rank, i)
ids = [i for _, i in representatives.values()]
cover = coverage[covered_banks, :][:, ids].astype(float)
start = time.monotonic()
solution = milp(np.ones(len(ids)), integrality=np.ones(len(ids)),
                bounds=Bounds(np.zeros(len(ids)), np.ones(len(ids))),
                constraints=LinearConstraint(csr_matrix(cover), np.ones(int(covered_banks.sum())), np.full(int(covered_banks.sum()), np.inf)),
                options={'time_limit': 15.})
assert solution.x is not None, solution.message
chosen = [ids[i] for i, x in enumerate(solution.x) if x > 0.5]
assert coverage[:, chosen].any(axis=1)[covered_banks].all()
selected = []
for i in chosen:
    mi, pi = divmod(i, 120)
    m, p = matrices[mi], permutations[pi]
    def moved(r):
        return sum(((r >> j) & 1) << p[j] for j in range(10))
    selected.append({'name': f'Symmetry{m["name"]}P{pi}',
                     'source_matrix': m['name'], 'source_matrix_index': mi,
                     'permutation_index': pi, 'permutation': p,
                     'positive_rows': [moved(r) for r in m['positive_rows']],
                     'negative_rows': [moved(r) for r in m['negative_rows']],
                     'weights': m['weights'], 'total': m['total'],
                     'covered_nodes': [banks[j]['node'] for j in np.flatnonzero(coverage[:, i])],
                     'margins': [int(margins[j, mi, pi]) for j in np.flatnonzero(coverage[:, i])]})
summary = {'banks': len(banks), 'candidate_pairs': int(coverage.shape[1]),
           'covered_banks': int(covered_banks.sum()),
           'uncovered_nodes': [b['node'] for b, c in zip(banks, covered_banks) if not c],
           'unique_nonempty_covers': len(ids), 'selected_count': len(chosen),
           'solver_status': int(solution.status), 'solver_message': solution.message,
           'mip_gap': float(solution.mip_gap), 'seconds': time.monotonic() - start,
           'selected_names': [m['name'] for m in selected]}
output = Path(args.output)
assert not output.exists()
output.mkdir()
(output / 'matrices.json').write_text(json.dumps(selected, indent=2) + '\n')
(output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2), flush=True)
