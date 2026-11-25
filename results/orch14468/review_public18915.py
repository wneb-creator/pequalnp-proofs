#!/usr/bin/env python3
"""Independent replay of the actual Lean atlas, truth tables, and lift witnesses."""
import hashlib
import itertools
import json
import pathlib
import re
import sys

source = pathlib.Path(sys.argv[1])
out = pathlib.Path(sys.argv[2])
text = source.read_text()
MASK = (1 << 512) - 1
PAIR_MASK = (1 << 152) - 1
MOD = 2305843009213693951


def body(name):
    match = re.search(r"^def " + re.escape(name) + r"\b.*?(?=^(?:def |theorem |end |namespace |set_option |abbrev )|\Z)", text, re.M | re.S)
    assert match, name
    return match.group()


def hex_cases(name):
    return {int(k): int(v, 16) for k, v in re.findall(r"\| (\d+) => (0x[0-9a-f]+)", body(name))}


packed = {k: hex_cases("gbK" + str(k))[0] for k in range(2, 7)}
counts = {int(k): int(v) for k, v in re.findall(r"\| (\d+) => (\d+)", body("gbN"))}
assert counts == {6: 1, 5: 44, 4: 91, 3: 25, 2: 5}
widths = {6: 5, 5: 16, 4: 27, 3: 38, 2: 49}
for k, width in widths.items():
    assert f"| {k} => packedAt gbK{k} (i*{width}) {width}" in body("gbR")


def packed_at(k, pos, width):
    # Each actual gbK function has exactly one nonzero word.
    return (packed[k] >> pos) & ((1 << width) - 1)


lookup_params = {
    6: (6, 1, 5, 1, 2, 1),
    5: (788, 14, 704, 6, 53, 7),
    4: (2667, 30, 2457, 7, 110, 8),
    3: (1006, 8, 950, 7, 81, 6),
    2: (249, 1, 245, 4, 12, 4),
}
for k, (off, divisor, shift, bits, slots, width) in lookup_params.items():
    expected = f"| {k} => packedAt gbK{k} ({off}+((h/{divisor}+packedAt gbK{k} ({shift}+(h % {divisor})*{bits}) {bits}) % {slots})*{width}) {width}"
    assert expected in body("gbI"), k


def lookup(k, h):
    if k not in counts:
        return 0
    off, divisor, shift, bits, slots, width = lookup_params[k]
    bucket = (h // divisor + packed_at(k, shift + (h % divisor) * bits, bits)) % slots
    return packed_at(k, off + bucket * width, width)


def binary(op, a, b):
    return (a & b, a | b, a & ~b & MASK, ~a & b & MASK)[op]


inputs = [sum(1 << r for r in range(512) if (r >> j) & 1) for j in range(9)]
assert [int(v, 16) for v in re.findall(r"0x[0-9a-f]+", body("inputs"))] == inputs
base = inputs[:5]
target = int(re.search(r"rawDecor 31 gbPos gbNeg, (0x[0-9a-f]+)", body("gbAtlas")).group(1), 16)
pos = hex_cases("gbPos")
neg = hex_cases("gbNeg")
positive_rows = [sum(((pos.get(j, 0) >> i) & 1) << j for j in range(9)) for i in range(152)]
negative_rows = [sum(((neg.get(j, 0) >> i) & 1) << j for j in range(9)) for i in range(152)]
assert all((target >> p) & 1 and not ((target >> n) & 1) for p, n in zip(positive_rows, negative_rows))


def difference(word):
    return sum((((word >> p) ^ (word >> n)) & 1) << i for i, (p, n) in enumerate(zip(positive_rows, negative_rows)))


states = {}
for k, count in counts.items():
    for i in range(count):
        record = packed_at(k, i * widths[k], widths[k])
        depth = 6 - k
        bank = base[:]
        code = record
        for _ in range(depth):
            a_index = code & 15
            b_index = (code >> 4) & 15
            a = bank[a_index] if a_index < len(bank) else 0
            b = bank[b_index] if b_index < len(bank) else 0
            bank.append(binary((code >> 8) & 3, a, b))
            code >>= 10
        live = [word for j, word in enumerate(bank) if (code >> j) & 1]
        assert len(set(live)) == len(live), (k, i, "duplicate")
        assert target not in live, (k, i, "target")
        states[k, i] = live

assert states[6, 0] == base


def key(word):
    n = word % MOD
    return ((n * n % MOD) * (n + 7) + 971 * n) % MOD


totals = dict(states=len(states), attempts=0, size_pruned=0, separation_pruned=0, redundant_pruned=0, linked=0)
for (k, i), live in sorted(states.items()):
    for a, b in itertools.combinations(live, 2):
        for op in range(4):
            z = binary(op, a, b)
            for keep_a, keep_b in itertools.product([False, True], repeat=2):
                totals["attempts"] += 1
                rest = [v for v in live if (v != a or keep_a) and (v != b or keep_b)]
                child = [z] + rest
                if len(child) > k:
                    totals["size_pruned"] += 1
                    continue
                cover = 0
                for word in child:
                    cover |= difference(word)
                if cover != PAIR_MASK:
                    totals["separation_pruned"] += 1
                    continue
                if z in [0, MASK] or z in live:
                    totals["redundant_pruned"] += 1
                    continue
                code = lookup(k - 1, sum(key(w) for w in child))
                row = code // 2
                assert row < counts.get(k - 1, 0), (k, i, op, keep_a, keep_b, "bad link")
                # The supplied mirrorSteps is empty, so odd tags are also identity.
                assert set(child) == set(states[k - 1, row]), (k, i, op, "wrong linked set")
                totals["linked"] += 1

assert "def mirrorSteps : List Move := []" in text
assert "gbN, gbR, (fun _ _ => 0), gbI" in body("gbAtlas")

full_positions = [int(v) for v in re.findall(r"inputs.getD (\d+) zero", body("fullRoots"))]
full_word = int(re.search(r"0x[0-9a-f]+", body("fullWord")).group(), 16)
edges = [(0, 4), (1, 5), (0, 6), (2, 6), (0, 7), (1, 7), (2, 7), (3, 7), (5, 7)]
for row in range(512):
    assignment = [(row >> j) & 1 for j in full_positions]
    assert any(assignment[a] and assignment[b] for a, b in edges) == bool((full_word >> row) & 1)
    assert ((full_word >> (row & ~224)) & 1) == ((target >> row) & 1)

base_witnesses = [(0, 2, 3), (1, 1, 3), (2, 1, 5), (3, 1, 9), (4, 8, 24)]
lift_witnesses = [(5, 1, 33), (6, 1, 65), (7, 32, 160)]
for word, variables, witnesses in [(target, range(5), base_witnesses), (full_word, full_positions, lift_witnesses)]:
    for j, r, s in witnesses:
        assert ((word >> r) ^ (word >> s)) & 1
        assert all(((r >> q) & 1) == ((s >> q) & 1) for q in variables if q != j)

mono = [(op, [int(x) for x in args.split(',')]) for op, args in re.findall(r"⟨\.(and|or),\[([0-9,]+)\]⟩", body("mono"))]
assert len(mono) == 11
for row in range(256):
    bank = [bool((row >> j) & 1) for j in range(8)]
    for op, args in mono:
        assert len(args) <= 2 and all(i < len(bank) for i in args)
        values = [bank[i] for i in args]
        bank.append(all(values) if op == 'and' else any(values))
    assert bank[18] == any(bank[a] and bank[b] for a, b in edges)

report = {
    "source": str(source),
    "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
    "verdict": "PASS independent finite atlas replay and semantic tables",
    "atlas": totals,
    "row_count_by_budget": counts,
    "separating_pairs": 152,
    "full_truth_table_rows": 512,
    "monotone_witness_rows": 256,
    "monotone_witness_gates": 11,
    "lift": {"fixed_coordinate_mask": 224, "base_binary_floor": 7, "essential_roots": 3, "resulting_binary_floor": 10},
    "scope": "Independent computational audit; Lean compilation and checker are separate validations."
}
out.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
