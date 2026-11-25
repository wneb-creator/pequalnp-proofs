import sys
sys.dont_write_bytecode = True
import hashlib
import itertools
import json
import runpy
from datetime import datetime, timezone
from pathlib import Path

import counterexample_cnf

N = 7
MASK = 211519409853589
EDGES = [(0, 1, 0), (2, 3, 0), (0, 2, 1), (1, 3, 1), (0, 3, 2), (1, 2, 2)]
EDGE_INDEX = {frozenset((u, v)): j for j, (u, v, c) in enumerate(EDGES)}
COLOR = {frozenset((u, v)): c for u, v, c in EDGES}


def colored_automorphisms(n, mask):
    assert n == N and mask == MASK
    result = []
    for perm in itertools.permutations(range(4)):
        color_map = {}
        column_map = {}
        for j, (u, v, c) in enumerate(EDGES):
            image = frozenset((perm[u], perm[v]))
            image_color = COLOR[image]
            if c in color_map:
                assert color_map[c] == image_color
            color_map[c] = image_color
            column_map[j] = EDGE_INDEX[image]
        full = tuple(perm) + tuple(4 + color_map[c] for c in range(3))
        full += tuple(N + column_map[j] for j in range(6)) + (13,)
        assert sorted(full) == list(range(14))
        for p in range(N):
            for line in range(N):
                assert ((mask >> (N * p + line)) & 1) == (
                    (mask >> (N * full[p] + full[N + line] - N)) & 1
                )
        result.append(full)
    assert len(set(result)) == 24
    return result


if __name__ == '__main__':
    autos = colored_automorphisms(N, MASK)
    print(json.dumps({
        'event': 'colored_lift_start',
        'at': datetime.now(timezone.utc).isoformat(),
        'N': N,
        'mask': MASK,
        'gate_budget': 22,
        'timeout_s': 900,
        'automorphism_method': '24 induced permutations of K4 vertices; each independently checked on all incidence pairs',
        'automorphisms': autos,
        'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'base_encoder_sha256': hashlib.sha256(Path(counterexample_cnf.__file__).read_bytes()).hexdigest(),
    }), flush=True)
    counterexample_cnf.automorphisms = colored_automorphisms
    sys.argv = ['counterexample_cadical_trial.py', '--N', str(N), '--mask', str(MASK),
                '--gates', '22', '--timeout', '900', '--label', 'colored-k4-twentytwo']
    runpy.run_path(str(Path(__file__).with_name('counterexample_cadical_trial.py')), run_name='__main__')
