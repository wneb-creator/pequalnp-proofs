import json
from pathlib import Path

DATA = json.loads(Path(__file__).with_suffix('.json').read_text())
POINTS = len(DATA['points'])
N = DATA['inputs']
EDGES = [tuple(edge) for edge in DATA['core_edges']]
NEIGHBORS = [tuple(b if a == i else a for a,b in EDGES if i in (a,b)) for i in range(N)]
POSITIVES = {(1 << a) | (1 << b) for a,b in EDGES}
RAW_NEGATIVES = set()
NEGATIVES = set()
for left in range(1 << POINTS):
    allowed = [v for v in range(POINTS, N)
               if not any(left >> a & 1 and b == v for a,b in EDGES)]
    RAW_NEGATIVES.add(left | sum(1 << v for v in allowed))
    closed = [u for u in range(POINTS)
              if not any(a == u and b in allowed for a,b in EDGES)]
    NEGATIVES.add(sum(1 << u for u in closed) + sum(1 << v for v in allowed))
TESTS = sorted(POSITIVES) + sorted(NEGATIVES)
INPUT_MASKS = [sum(1 << t for t,x in enumerate(TESTS) if x >> i & 1) for i in range(N)]
TARGET = (1 << len(POSITIVES)) - 1
ALL_TESTS = (1 << len(TESTS)) - 1


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask -= bit
