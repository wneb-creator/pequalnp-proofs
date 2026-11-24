import json
from pathlib import Path

DATA = json.loads(Path(__file__).with_suffix('.json').read_text())
N = DATA['inputs']
EDGES = [tuple(e) for e in DATA['core_edges']]
POSITIVES = {(1 << u) | (1 << v) for u, v in EDGES}
RAW_NEGATIVES = set()
NEGATIVES = set()
for left in range(64):
    allowed = [v for v in range(6, N) if not any(left >> u & 1 and b == v for u, b in EDGES)]
    RAW_NEGATIVES.add(left | sum(1 << v for v in allowed))
    closed = [u for u in range(6) if not any(a == u and b in allowed for a, b in EDGES)]
    NEGATIVES.add(sum(1 << u for u in closed) + sum(1 << v for v in allowed))
TESTS = sorted(POSITIVES) + sorted(NEGATIVES)
INPUT_MASKS = [sum(1 << t for t, x in enumerate(TESTS) if x >> j & 1) for j in range(N)]
TARGET = (1 << len(POSITIVES)) - 1
ALL_TESTS = (1 << len(TESTS)) - 1

def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask -= low
