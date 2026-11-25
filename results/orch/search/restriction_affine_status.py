"""Enumerate the geometric presence-mask inequalities for the order-three affine plane."""

from collections import Counter
from itertools import product


def affine_rows():
    points = list(product(range(3), repeat=2))
    rows = [
        sum(1 << i for i, (x, y) in enumerate(points) if (y - slope * x - b) % 3 == 0)
        for slope, b in product(range(3), repeat=2)
    ]
    rows.extend(sum(1 << i for i, (x, _) in enumerate(points) if x == b) for b in range(3))
    return rows


def count_masks(rows, columns, surplus_cap):
    counts = Counter()
    for mask in range(1 << len(rows)):
        exclusively_present = sum(not (column & ~mask) for column in columns)
        present_incidents = sum((column & mask).bit_count() for column in columns)
        missing_rows = len(rows) - mask.bit_count()
        lower = missing_rows + present_incidents - exclusively_present
        if lower <= surplus_cap:
            counts[mask.bit_count()] += 1
    return dict(sorted(counts.items()))


if __name__ == "__main__":
    rows = affine_rows()
    columns = [sum(1 << r for r, row in enumerate(rows) if row >> i & 1) for i in range(9)]
    assert all(row.bit_count() == 3 for row in rows)
    assert all(column.bit_count() == 4 for column in columns)
    for side, family, opposite in [("lines", rows, columns), ("points", columns, rows)]:
        print(side, count_masks(family, opposite, surplus_cap=23))
