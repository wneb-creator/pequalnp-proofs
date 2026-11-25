from collections import Counter
from functools import cache

POINTS = 13
DEGREE = 4
EDGES = POINTS * DEGREE
TARGET = 63

def neighbor_bound(k):
    return (16 * k + k + 2) // (k + 3)

@cache
def pair_gate_bound(count):
    return next(g for g in range(14) if g * (g + 1) // 2 >= count)

@cache
def side_states(total, unused, dangerous_labels, bound):
    result = []
    for selected in range(13, total - unused + 1):
        min_deficit = EDGES + 2 * total - selected - 1 - bound
        for full_groups in range(dangerous_labels + 1):
            max_deficit = 2 * dangerous_labels + full_groups - (3 if full_groups else 2)
            if max_deficit >= min_deficit:
                break
        else:
            continue
        possible = [r for r in range(selected - dangerous_labels + 1)
                    if neighbor_bound(max(0, POINTS - r)) <= selected - r]
        if possible:
            pure = max(pair_gate_bound(dangerous_labels), neighbor_bound(full_groups) - 1)
            result.append((selected, max(possible), pure))
    return result

def impossible(bound):
    before = Counter()
    after = Counter()
    for total in range(POINTS, (bound + 1) // 2 + 1):
        for a in range(4, 14):
            for b in range(a, 14):
                if a + b > total:
                    continue
                for sr, r, pure_x in side_states(total, a, b, bound):
                    for sc, c, pure_y in side_states(total, b, a, bound):
                        if 2 * total - 1 + pure_x + pure_y > bound:
                            continue
                        before[total] += 1
                        w = min((4 * sr - EDGES) // 3, (4 * sc - EDGES) // 3)
                        if sr + sc - total <= r + c + w:
                            after[total] += 1
    return dict(before), dict(after)

for bound in (63, 64, 65, 66):
    print(bound, impossible(bound))
