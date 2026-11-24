"""Complete plane basis augmented with singleton/nonedge-pair fitness tests."""
from SearchPlaneProblem import (N, POINTS, EDGES, NEIGHBORS, POSITIVES,
                               RAW_NEGATIVES, AUTOMORPHISMS, bits)

SMALL_NEGATIVES = {1 << i for i in range(N)}
SMALL_NEGATIVES.update((1 << i) | (1 << j)
                       for i in range(N) for j in range(i + 1, N)
                       if ((1 << i) | (1 << j)) not in POSITIVES)
assert not SMALL_NEGATIVES & RAW_NEGATIVES
NEGATIVES = set(RAW_NEGATIVES) | SMALL_NEGATIVES
assert not POSITIVES & NEGATIVES
TESTS = sorted(POSITIVES) + sorted(NEGATIVES)
INPUT_MASKS = [sum(1 << t for t, x in enumerate(TESTS) if x >> j & 1)
               for j in range(N)]
TARGET = (1 << len(POSITIVES)) - 1
ALL_TESTS = (1 << len(TESTS)) - 1
MAXIMAL_NEGATIVE_MASK = sum(1 << t for t, x in enumerate(TESTS) if x in RAW_NEGATIVES)
SMALL_NEGATIVE_MASK = sum(1 << t for t, x in enumerate(TESTS) if x in SMALL_NEGATIVES)
assert (MAXIMAL_NEGATIVE_MASK | SMALL_NEGATIVE_MASK) == ALL_TESTS ^ TARGET
