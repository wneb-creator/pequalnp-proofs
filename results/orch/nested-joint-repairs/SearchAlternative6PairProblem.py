"""Complete Alternative6 basis augmented with small false assignments for fitness.

The original 24 positive and 64 maximal-negative assignments remain present.
All singleton and nonedge-pair assignments are additional negative fitness tests.
RAW_NEGATIVES deliberately remains the original complete 64-assignment basis.
"""
from SearchAlternative6Problem import N, EDGES, POSITIVES, RAW_NEGATIVES, bits

SMALL_NEGATIVES = {1 << i for i in range(N)}
SMALL_NEGATIVES.update((1 << i) | (1 << j)
                       for i in range(N) for j in range(i + 1, N)
                       if ((1 << i) | (1 << j)) not in POSITIVES)
NEGATIVES = set(RAW_NEGATIVES) | SMALL_NEGATIVES
assert not POSITIVES & NEGATIVES
TESTS = sorted(POSITIVES) + sorted(NEGATIVES)
INPUT_MASKS = [sum(1 << t for t, x in enumerate(TESTS) if x >> j & 1)
               for j in range(N)]
TARGET = (1 << len(POSITIVES)) - 1
ALL_TESTS = (1 << len(TESTS)) - 1
