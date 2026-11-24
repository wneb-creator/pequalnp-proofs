"""Finite checks for formula rewrites under circuit sharing; not gap refutations."""
from itertools import combinations


def variable_masks(n):
    return [sum(((z >> i) & 1) << z for z in range(1 << n)) for i in range(n)]


def split_shared_sums():
    values = variable_masks(8)
    mixed_pairs = [values[i] | values[i + 4] for i in range(4)]
    mixed_outputs = [mixed_pairs[i] | mixed_pairs[j] for i, j in combinations(range(4), 2)]
    restricted_outputs = [
        values[offset + i] | values[offset + j]
        for offset in (0, 4)
        for i, j in combinations(range(4), 2)
    ]
    assert len(mixed_pairs) + len(mixed_outputs) == 10
    assert len(set(restricted_outputs)) == 12
    assert set(restricted_outputs).isdisjoint(values)
    print("Shared sums: 10 gates before splitting; 12 distinct noninput outputs after splitting.")


def fixed_filter_interface():
    values = variable_masks(4)
    a, b, c, d = values
    left, right, filter_value = a | b, c | d, a | c
    target = left & right & filter_value
    assert target == (a & (c | d)) | (b & c)
    forbidden = sum(1 << z for z in (1, 2, 4, 8, 10))
    # Supplying the required interface functions freely only strengthens the model.
    initial = values + [left, right, filter_value, 0, (1 << 16) - 1]
    checked = 0
    for i, first in enumerate(initial):
        for j, second in enumerate(initial[: i + 1]):
            for op, result in (("or", first | second), ("and", first & second)):
                if op == "and" and result & forbidden:
                    continue
                assert result != target, (i, j, op)
                available = initial + [result]
                for k, first2 in enumerate(available):
                    for l, second2 in enumerate(available[: k + 1]):
                        for op2, result2 in (("or", first2 | second2), ("and", first2 & second2)):
                            if op2 == "and" and result2 & forbidden:
                                continue
                            checked += 1
                            assert result2 != target, (i, j, op, k, l, op2)
    print(f"Fixed interface: checked {checked} valid sequences of at most two extra gates.")
    print("No clean implementation of F from the freely supplied A,B,H plus inputs and constants.")
    print("Thus all four interface values need at least six clean gates; the original dirty cone uses five.")
    print("This is a multioutput/interface obstruction, not a refutation of the singleoutput target.")


if __name__ == "__main__":
    split_shared_sums()
    fixed_filter_interface()
