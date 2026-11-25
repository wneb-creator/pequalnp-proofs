"""Slice and translate a positive-hint LRAT refutation for the proved Lean RUP checker."""

import argparse
import hashlib
import json
import sys
from pathlib import Path


def read_cnf(path):
    clauses = {}
    pending = []
    expected = None
    with path.open() as stream:
        for line in stream:
            if not line.strip() or line.startswith("c"):
                continue
            if line.startswith("p"):
                header = line.split()
                if len(header) != 4 or header[1] != "cnf":
                    raise ValueError("invalid DIMACS header")
                expected = int(header[3])
                continue
            for value in map(int, line.split()):
                if value:
                    pending.append(value)
                else:
                    clauses[len(clauses) + 1] = pending
                    pending = []
    if pending or expected != len(clauses):
        raise ValueError("incomplete DIMACS input or clause-count mismatch")
    return clauses


def parse_record(line):
    fields = line.split()
    if not fields or fields[0] == b"c":
        return None
    identifier = int(fields[0])
    if len(fields) > 1 and fields[1] == b"d":
        return None
    values = list(map(int, fields[1:]))
    if not values or values[-1] != 0:
        raise ValueError("incomplete LRAT record")
    split = values.index(0)
    clause = values[:split]
    hints = values[split + 1:-1]
    if any(h == 0 for h in hints):
        raise ValueError("unexpected zero inside LRAT hint list")
    return identifier, clause, hints


def read_signed_varint(stream):
    value = 0
    shift = 0
    while True:
        raw = stream.read(1)
        if not raw:
            raise ValueError("truncated binary LRAT varint")
        byte = raw[0]
        value |= (byte & 127) << shift
        if byte < 128:
            return -(value // 2) if value & 1 else value // 2
        shift += 7


def read_zero_terminated(stream):
    values = []
    while True:
        value = read_signed_varint(stream)
        if value == 0:
            return values
        values.append(value)


def read_record(stream, binary):
    if not binary:
        line = stream.readline()
        return (False, None) if not line else (True, parse_record(line))
    tag = stream.read(1)
    if not tag:
        return False, None
    if tag == b"d":
        read_zero_terminated(stream)
        return True, None
    if tag != b"a":
        raise ValueError("unknown binary LRAT record tag")
    identifier = read_signed_varint(stream)
    clause = read_zero_terminated(stream)
    hints = read_zero_terminated(stream)
    return True, (identifier, clause, hints)


def index_lrat(path, initial_count):
    offsets = {}
    final = None
    previous = initial_count
    with path.open("rb") as stream:
        binary = stream.read(1) in (b"a", b"d")
        stream.seek(0)
        while True:
            offset = stream.tell()
            present, record = read_record(stream, binary)
            if not present:
                break
            if record is None:
                continue
            identifier, clause, hints = record
            if identifier <= previous:
                raise ValueError("addition identifiers must strictly increase")
            previous = identifier
            offsets[identifier] = offset
            if not clause:
                final = identifier
    if final is None:
        raise ValueError("no empty clause: the input is not a completed refutation")
    return offsets, final, binary


def literal(value):
    return 2 * abs(value) + int(value < 0)


def complement(value):
    return value ^ 1


def pack(tokens, width, chunk_size=1024):
    words = []
    for start in range(0, len(tokens), chunk_size):
        chunk = tokens[start:start + chunk_size]
        word = 1 << (width * len(chunk))
        for i, token in enumerate(chunk):
            if token < 0 or token >= (1 << width):
                raise ValueError("token is outside the packed width")
            word |= token << (width * i)
        words.append(word)
    return words


def convert(cnf_path, lrat_path):
    initial = read_cnf(cnf_path)
    count = len(initial)
    offsets, final, binary = index_lrat(lrat_path, count)
    records = {}
    needed = set()
    pending = [final]
    with lrat_path.open("rb") as stream:
        while pending:
            identifier = pending.pop()
            if identifier in needed:
                continue
            needed.add(identifier)
            if identifier <= count:
                if identifier not in initial:
                    raise ValueError("missing initial clause")
                continue
            if identifier not in offsets:
                raise ValueError("missing derived clause")
            stream.seek(offsets[identifier])
            present, record = read_record(stream, binary)
            if not present or record is None:
                raise ValueError("proof index does not point to an addition")
            _, clause, hints = record
            if any(h < 0 for h in hints):
                raise ValueError("needed proof contains RAT/negative hints")
            if any(h >= identifier for h in hints):
                raise ValueError("hint does not refer to an earlier clause")
            records[identifier] = (clause, hints)
            pending.extend(hints)

    database = {identifier: {literal(x) for x in initial[identifier]}
                for identifier in needed if identifier <= count}
    traces = {}
    for identifier in sorted(records):
        clause, hints = records[identifier]
        encoded = [literal(x) for x in clause]
        falsified = set(encoded)
        trace = []
        conflict = False
        for hint in hints:
            remaining = database[hint] - falsified
            if not remaining:
                trace.append((hint, None))
                conflict = True
                break
            if len(remaining) != 1:
                raise ValueError(f"non-unit hint {hint} while proving clause {identifier}")
            unit = next(iter(remaining))
            if complement(unit) in falsified:
                continue
            trace.append((hint, unit))
            falsified.add(complement(unit))
        if not conflict:
            raise ValueError(f"no RUP conflict for clause {identifier}")
        database[identifier] = set(encoded)
        traces[identifier] = (encoded, trace)

    # Drop hints after conflict and unit hints that made no new assignment.
    kept = set()
    pending = [final]
    while pending:
        identifier = pending.pop()
        if identifier in kept:
            continue
        kept.add(identifier)
        if identifier > count:
            pending.extend(hint for hint, _ in traces[identifier][1])
    derived = sorted(identifier for identifier in kept if identifier > count)
    remap = {identifier: count + i + 1 for i, identifier in enumerate(derived)}
    tokens = []
    for identifier in derived:
        clause, trace = traces[identifier]
        tokens.extend([remap[identifier] - 1, *clause, 0])
        for hint, unit in trace:
            tokens.append((hint if hint <= count else remap[hint]) - 1)
            if unit is not None:
                tokens.append(unit)
    width = max(1, max(tokens, default=0).bit_length())
    keep_words = [0] * ((count + 1023) // 1024)
    for identifier in kept:
        if identifier <= count:
            index = identifier - 1
            keep_words[index // 1024] |= 1 << (index % 1024)
    return {
        "initial_clauses": count,
        "indexed_additions": len(offsets),
        "kept_initial": sum(identifier <= count for identifier in kept),
        "kept_additions": len(derived),
        "token_count": len(tokens),
        "width": width,
        "tokens": tokens,
        "words": pack(tokens, width),
        "keep_words": keep_words,
        "final_original_id": final,
        "binary_input": binary,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cnf", type=Path)
    parser.add_argument("lrat", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--emit-lean", type=Path,
                        help="write packed certificate data definitions, without an acceptance lemma")
    args = parser.parse_args()
    sys.set_int_max_str_digits(0)
    result = convert(args.cnf, args.lrat)
    result["cnf_sha256"] = hashlib.sha256(args.cnf.read_bytes()).hexdigest()
    with args.lrat.open("rb") as stream:
        result["lrat_sha256"] = hashlib.file_digest(stream, "sha256").hexdigest()
    result["packer_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    if args.emit_lean:
        words = ",\n   ".join(map(str, result["words"]))
        keep = ",\n   ".join(map(str, result["keep_words"]))
        source = (
            f"def certWidth : Nat := {result['width']}\n\n"
            f"def certWords : List Nat :=\n  [{words}]\n\n"
            f"def certKeepWords : List Nat :=\n  [{keep}]\n\n"
            "def certFk (m : Nat) : List Nat :=\n"
            "  (List.range m).map fun i =>\n"
            "    if (certKeepWords.getD (i / 1024) 0).testBit (i % 1024) then i + 1 else 0\n"
        )
        args.emit_lean.write_text(source)
        result["lean_data_bytes"] = len(source.encode())
    args.output.write_text(json.dumps(result, separators=(",", ":")))
    print(json.dumps({key: value for key, value in result.items()
                      if key not in {"tokens", "words", "keep_words"}}, indent=2))


if __name__ == "__main__":
    main()
