#!/usr/bin/env python3
"""Census duplicate positive/negative rows in Lean literal sample arrays."""

import argparse
import datetime
import hashlib
import json
import re
from pathlib import Path


class LiteralArray:
    def __init__(self, name, body):
        self.name = name
        self.tokens = re.findall(r"#\[|0[xX][0-9a-fA-F]+|[0-9]+|[(),\]\-]", body)
        assert "".join(self.tokens) == re.sub(r"\s+", "", body), name
        self.index = 0

    def consume(self, token):
        assert self.tokens[self.index] == token, (self.name, self.index, token)
        self.index += 1

    def atom(self):
        token = self.tokens[self.index]
        if token == "(":
            self.consume("(")
            value = self.atom()
            self.consume(")")
            return value
        if token == "-":
            self.consume("-")
            return -self.atom()
        self.index += 1
        return int(token, 16) if token.lower().startswith("0x") else int(token)

    def pairs(self):
        self.consume("#[")
        values = []
        while self.tokens[self.index] != "]":
            self.consume("(")
            a = self.atom()
            self.consume(",")
            b = self.atom()
            self.consume(")")
            values.append((a, b))
            if self.tokens[self.index] == ",":
                self.consume(",")
            else:
                break
        self.consume("]")
        assert self.index == len(self.tokens), self.name
        return values


def census(source, width):
    text = source.read_text()
    pattern = re.compile(
        r"^def\s+(\w+)\s*:\s*Array\s*\(Bits\s*×\s*Bits\)\s*:=\s*(#\[[^\n]*\])\s*$",
        re.M,
    )
    modulus = 1 << width
    arrays = []
    for match in pattern.finditer(text):
        name, body = match.groups()
        values = LiteralArray(name, body).pairs()
        assert len(values) == 9, (name, len(values))
        reduced = [(a % modulus, b % modulus) for a, b in values]
        pairs = [
            (
                sum(((a >> k) & 1) << j for j, (a, b) in enumerate(reduced)),
                sum(((b >> k) & 1) << j for j, (a, b) in enumerate(reduced)),
            )
            for k in range(width)
        ]
        first = {}
        classes = {}
        for k, pair in enumerate(pairs):
            first.setdefault(pair, k)
            classes.setdefault(pair, []).append(k)
        prefix = max(first.values()) + 1
        assert set(pairs[:prefix]) == set(pairs)
        assert prefix == 1 or set(pairs[:prefix - 1]) != set(pairs)
        arrays.append({
            "sample_array": name,
            "original_width": width,
            "unique_pair_count": len(first),
            "smallest_covering_prefix": prefix,
            "unique_positive_count": len({a for a, b in pairs}),
            "unique_negative_count": len({b for a, b in pairs}),
            "max_literal_abs_bit_length": max(abs(v).bit_length() for ab in values for v in ab),
            "negative_literal_count": sum(v < 0 for ab in values for v in ab),
            "last_new_pair": {
                "index": prefix - 1,
                "positive": pairs[prefix - 1][0],
                "negative": pairs[prefix - 1][1],
            },
            "first_occurrence_positions": list(first.values()),
            "pair_classes": [
                {
                    "positive_assignment": a,
                    "negative_assignment": b,
                    "first_index": first[(a, b)],
                    "positions": positions,
                }
                for (a, b), positions in classes.items()
            ],
        })
    headers = re.findall(r"^def\s+\w+\s*:\s*Array\s*\(Bits\s*×\s*Bits\)\s*:=", text, re.M)
    assert arrays and len(arrays) == len(headers)
    maximum_unique = max(a["unique_pair_count"] for a in arrays)
    maximum_prefix = max(a["smallest_covering_prefix"] for a in arrays)
    return {
        "source": str(source),
        "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "original_width": width,
        "arrays": arrays,
        "global_max_unique_pairs": maximum_unique,
        "global_smallest_covering_prefix": maximum_prefix,
        "worst_by_unique_pairs": [a["sample_array"] for a in arrays if a["unique_pair_count"] == maximum_unique],
        "worst_by_covering_prefix": [a["sample_array"] for a in arrays if a["smallest_covering_prefix"] == maximum_prefix],
        "note": f"Negative literals reduced modulo 2^{width} before bit extraction. No source or proof was modified.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--width", type=int, default=None,
                        help="Explicit interpretation width; defaults to the source Bits declaration.")
    args = parser.parse_args()
    declared = re.search(r"^abbrev Bits := BitVec ([0-9]+)\s*$", args.source.read_text(), re.M)
    assert declared is not None, "Cannot infer the concrete Bits width"
    declared_width = int(declared.group(1))
    width = declared_width if args.width is None else args.width
    report = census(args.source, width)
    report["source_declared_width"] = declared_width
    report["interpretation_override"] = width != declared_width
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "arrays"}, indent=2))


if __name__ == "__main__":
    main()
