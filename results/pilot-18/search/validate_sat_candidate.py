#!/usr/bin/env python3
"""Audit a Kissat witness for L-meta-1342 and normalize its circuit.

Usage: python3 validate_sat_candidate.py INSTANCE.cnf KISSAT.stdout
Reads INSTANCE.json, requires a full signed SAT model, checks every DIMACS
clause, and checks the decoded and normalized circuits on all 2048 inputs.
Only after success, writes INSTANCE.validated.original.json,
INSTANCE.validated.normalized.json, and INSTANCE.validated.json.
Uses only the Python standard library; never invokes a solver or Lean.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile

N = 11
VIRTUAL_FALSE = 11
VIRTUAL_TRUE = 12
AUGMENTED_INPUTS = 13
EDGES = ((0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6),
         (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10),
         (7, 9), (8, 9))
INPUT_COUNT = 1 << N
ALL_ROWS = (1 << INPUT_COUNT) - 1
INPUT_TABLES = tuple(sum(1 << mask for mask in range(INPUT_COUNT)
                         if mask & (1 << vertex)) for vertex in range(N))
SINGLETON_ROWS = sum(1 << (1 << vertex) for vertex in range(N))
MINIMAL_EDGE_ROWS = sum(1 << ((1 << u) | (1 << v)) for u, v in EDGES)
TARGET = 0
for _u, _v in EDGES:
    TARGET |= INPUT_TABLES[_u] & INPUT_TABLES[_v]
NEGATIVE_ROWS = ALL_ROWS ^ TARGET
INTEGER = re.compile(r'[+-]?[0-9]+\Z')
HEX256 = re.compile(r'[0-9a-fA-F]{64}\Z')


class ValidationError(Exception):
    """A malformed input or a failed witness check."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValidationError(message)


def natural(value, label: str) -> int:
    require(type(value) is int and value >= 0, f'{label} must be a nonnegative integer')
    return value


def flag(meta: dict, name: str, default: bool = False) -> bool:
    value = meta.get(name, default)
    require(type(value) is bool, f'metadata {name} must be Boolean')
    return value


def integer_token(word: str, where: str) -> int:
    require(INTEGER.fullmatch(word) is not None, f'noninteger token in {where}')
    return int(word)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate key in metadata JSON')
        result[key] = value
    return result


def invalid_json_constant(_):
    raise ValidationError('nonfinite number in metadata JSON')


def load_metadata(raw: bytes) -> dict:
    try:
        meta = json.loads(raw.decode('utf-8'), object_pairs_hook=unique_object,
                          parse_constant=invalid_json_constant)
    except (UnicodeError, json.JSONDecodeError) as error:
        raise ValidationError('metadata is not valid UTF-8 JSON') from error
    require(type(meta) is dict, 'metadata must be an object')
    natural(meta.get('variables'), 'metadata variables')
    natural(meta.get('clauses'), 'metadata clauses')
    natural(meta.get('size'), 'metadata size')
    expected = meta.get('sha256')
    require(type(expected) is str and HEX256.fullmatch(expected) is not None,
            'metadata sha256 must be a SHA-256 hex digest')
    for name, expected_value in (('inputs', N), ('virtual_false', VIRTUAL_FALSE),
                                 ('virtual_true', VIRTUAL_TRUE)):
        if name in meta:
            require(type(meta[name]) is int and meta[name] == expected_value,
                    f'metadata {name} disagrees with this fixed graph model')
    return meta


def parse_model(raw: bytes, variables: int) -> tuple[dict[int, bool], int]:
    try:
        text = raw.decode('utf-8')
    except UnicodeError as error:
        raise ValidationError('Kissat stdout is not valid UTF-8') from error
    assignment = {}
    statuses = 0
    terminated = False
    duplicates = 0
    model_lines = 0
    for line_number, line in enumerate(text.splitlines(), 1):
        words = line.split()
        if not words:
            continue
        if words[0] == 's':
            require(words == ['s', 'SATISFIABLE'], 'solver did not report SATISFIABLE')
            statuses += 1
            require(statuses == 1, 'multiple solver status records')
        elif words[0] == 'v':
            model_lines += 1
            require(len(words) > 1, f'empty model record at line {line_number}')
            for word in words[1:]:
                lit = integer_token(word, f'model line {line_number}')
                if lit == 0:
                    terminated = True
                    continue
                require(not terminated, 'model literals occur after the final zero terminator')
                var = abs(lit)
                require(1 <= var <= variables, f'model variable {var} is outside the DIMACS range')
                value = lit > 0
                if var in assignment:
                    require(assignment[var] == value, f'conflicting signs for model variable {var}')
                    duplicates += 1
                assignment[var] = value
    require(statuses == 1, 'missing SATISFIABLE status')
    require(model_lines > 0 and terminated, 'missing zero-terminated signed model')
    require(len(assignment) == variables,
            f'incomplete model: assigned {len(assignment)} of {variables} variables')
    return assignment, duplicates


def check_cnf(raw: bytes, meta: dict, assignment: dict[int, bool]) -> int:
    try:
        text = raw.decode('ascii')
    except UnicodeError as error:
        raise ValidationError('DIMACS is not ASCII text') from error
    header = False
    count = 0
    pending = False
    satisfied = False
    for line_number, line in enumerate(text.splitlines(), 1):
        stripped = line.strip()
        if not stripped or stripped.startswith('c'):
            continue
        words = stripped.split()
        if words[0] == 'p':
            require(not header and len(words) == 4 and words[:2] == ['p', 'cnf'],
                    'invalid or repeated DIMACS header')
            variables = integer_token(words[2], 'DIMACS header')
            clauses = integer_token(words[3], 'DIMACS header')
            require(variables == meta['variables'] and clauses == meta['clauses'],
                    'DIMACS header disagrees with metadata counts')
            header = True
            continue
        require(header, 'DIMACS clause precedes the header')
        for word in words:
            lit = integer_token(word, f'DIMACS line {line_number}')
            if lit == 0:
                count += 1
                require(satisfied, f'CNF clause {count} is not satisfied by the model')
                require(count <= meta['clauses'], 'DIMACS contains more clauses than declared')
                pending = False
                satisfied = False
            else:
                var = abs(lit)
                require(1 <= var <= meta['variables'],
                        f'CNF literal in clause {count + 1} is outside the DIMACS range')
                pending = True
                satisfied = satisfied or assignment[var] == (lit > 0)
    require(header, 'missing DIMACS header')
    require(not pending, 'unterminated final CNF clause')
    require(count == meta['clauses'], 'DIMACS clause count disagrees with its header')
    return count


def variable(value, meta: dict, label: str) -> int:
    require(type(value) is int and 1 <= value <= meta['variables'],
            f'{label} is not a valid positive variable ID')
    return value


def selector_index(xs, width: int, assignment: dict[int, bool], meta: dict, label: str) -> int:
    require(type(xs) is list and len(xs) == width, f'{label} has the wrong source-domain size')
    ids = [variable(x, meta, label) for x in xs]
    require(len(set(ids)) == len(ids), f'{label} repeats a selector variable')
    selected = [i for i, var in enumerate(ids) if assignment[var]]
    require(len(selected) == 1, f'{label} does not select exactly one wire')
    return selected[0]


def decode(meta: dict, assignment: dict[int, bool]) -> tuple[list[list], int]:
    size = meta['size']
    for name in ('ops', 'lefts', 'rights'):
        require(type(meta.get(name)) is list and len(meta[name]) == size,
                f'metadata {name} has the wrong gate count')
    gates = []
    for i in range(size):
        op = variable(meta['ops'][i], meta, f'operation at gate {i}')
        left = selector_index(meta['lefts'][i], AUGMENTED_INPUTS + i,
                              assignment, meta, f'left selector at gate {i}')
        right = selector_index(meta['rights'][i], AUGMENTED_INPUTS + i,
                               assignment, meta, f'right selector at gate {i}')
        gates.append(['and' if assignment[op] else 'or', left, right])
    output = selector_index(meta.get('output_selectors'), AUGMENTED_INPUTS + size,
                            assignment, meta, 'output selector')
    return gates, output


def truth_tables(gates: list[list], augmented: bool = True) -> list[int]:
    tables = list(INPUT_TABLES)
    if augmented:
        tables.extend((0, ALL_ROWS))
    for i, gate in enumerate(gates):
        require(type(gate) in (list, tuple) and len(gate) == 3, f'invalid gate {i}')
        op, a, b = gate
        require(op in ('and', 'or'), f'invalid operation at gate {i}')
        require(type(a) is int and type(b) is int and
                0 <= a < len(tables) and 0 <= b < len(tables),
                f'gate {i} has a nonpreceding source')
        tables.append(tables[a] & tables[b] if op == 'and' else tables[a] | tables[b])
    return tables


def check_target(tables: list[int], output: int, label: str) -> None:
    require(type(output) is int and 0 <= output < len(tables), f'{label} output is invalid')
    difference = tables[output] ^ TARGET
    if difference:
        first = (difference & -difference).bit_length() - 1
        raise ValidationError(f'{label} circuit disagrees with the target at input mask {first}')


def reachable_gates(gates: list[list], output: int, offset: int) -> set[int]:
    seen = set()
    todo = [output]
    while todo:
        wire = todo.pop()
        if wire >= offset:
            gate = wire - offset
            require(0 <= gate < len(gates), 'invalid gate during reachability audit')
            if gate not in seen:
                seen.add(gate)
                todo.extend(gates[gate][1:])
    return seen


def check_requested(meta: dict, gates: list[list], output: int, tables: list[int]) -> tuple[list[int], dict]:
    size = len(gates)
    first = meta.get('first_junk', -1)
    require(type(first) is int and -1 <= first < size, 'metadata first_junk is out of range')
    enforce = flag(meta, 'enforce_junk', True)
    second = flag(meta, 'second_junk')
    junk = [i for i, (op, _, _) in enumerate(gates)
            if op == 'and' and tables[AUGMENTED_INPUTS + i] & NEGATIVE_ROWS]
    checks = {'enforce_junk': enforce, 'first_junk': first, 'second_junk': second}
    if first >= 0:
        require(not any(i < first for i in junk),
                'prefix AND is true on a negative target input')
        checks['prefix_clean_check'] = 'passed'
        checks['prefix_clean_and_gates_checked'] = sum(op == 'and' for op, _, _ in gates[:first])
    else:
        checks['prefix_clean_check'] = 'skipped: first_junk=-1'
    if enforce and first >= 0:
        require(bool(junk) and junk[0] == first, 'decoded first junk AND disagrees with metadata')
        if second:
            require(len(junk) >= 2, 'decoded circuit lacks the requested second junk AND')
        checks['junk_check'] = 'passed'
    else:
        checks['junk_check'] = 'skipped: enforce_junk=false or first_junk=-1'
    prefix_flags = ('prefix_sort', 'prefix_lex', 'productive_prefix', 'prefix_distinct',
                    'prefix_dominance', 'prefix_copy_chain')
    for name in prefix_flags:
        checks[name] = flag(meta, name)
    prefix_needed = any(checks[name] for name in prefix_flags)
    require(not prefix_needed or first >= 0, 'prefix checks require a nonnegative first_junk boundary')
    prefix = gates[:max(first, 0)]
    keys = [(max(a, b), min(a, b), 0 if op == 'and' else 1) for op, a, b in prefix]
    if checks['prefix_sort']:
        require(all(a[0] <= b[0] for a, b in zip(keys, keys[1:])), 'prefix maximum sources are not sorted')
    if checks['prefix_lex']:
        require(all(a <= b for a, b in zip(keys, keys[1:])), 'prefix is not lexicographically AND-first sorted')
    if checks['prefix_distinct']:
        require(len(set(keys)) == len(keys), 'prefix repeats a gate description')
    if checks['productive_prefix']:
        for i, (op, a, b) in enumerate(prefix):
            if op == 'and':
                require(bool(tables[a] & SINGLETON_ROWS) and bool(tables[b] & SINGLETON_ROWS),
                        f'prefix AND {i} has an operand with empty singleton support')
    if checks['prefix_dominance']:
        pairs = 0
        for i, (op, _, _) in enumerate(prefix):
            if op != 'and':
                continue
            g_table = tables[AUGMENTED_INPUTS + i]
            for h in range(i):
                b_wire = AUGMENTED_INPUTS + h
                b_table = tables[b_wire]
                if b_table & NEGATIVE_ROWS:
                    continue
                require(bool(g_table & ~b_table & MINIMAL_EDGE_ROWS),
                        f'prefix AND {i} lacks a minimal-edge witness against earlier clean wire {b_wire}')
                pairs += 1
        checks['prefix_dominance_pairs_checked'] = pairs
    if checks['prefix_copy_chain']:
        copying = False
        count = 0
        for i, (op, a, b) in enumerate(prefix):
            is_copy = op == 'or' and a == b
            if copying:
                require(is_copy, f'prefix copy chain is interrupted at gate {i}')
            if is_copy:
                require(i == 0 or a == AUGMENTED_INPUTS + i - 1,
                        f'prefix OR copy {i} does not copy the previous gate')
                copying = True
                count += 1
        checks['prefix_copy_chain_gates_checked'] = count
    checks['last_output'] = flag(meta, 'last_output')
    checks['live'] = flag(meta, 'live')
    if checks['last_output'] or checks['live']:
        require(size > 0 and output == AUGMENTED_INPUTS + size - 1,
                'requested last output is not the final gate')
    if checks['live']:
        require(reachable_gates(gates, output, AUGMENTED_INPUTS) == set(range(size)),
                'decoded circuit contains a gate that does not reach its output')
    last_op = meta.get('last_op')
    require(last_op in (None, 'and', 'or'), 'invalid metadata last_op')
    if last_op is not None:
        require(checks['last_output'] or checks['live'], 'last_op requires a last-output constraint')
        require(bool(gates) and gates[-1][0] == last_op, 'last operation disagrees with metadata')
    checks['last_op'] = last_op
    if 'suffix_shape' in meta:
        shape = meta['suffix_shape']
        require(first >= 0 and type(shape) is str and len(shape) == size - first and
                all(x in 'AO' for x in shape), 'invalid metadata suffix_shape')
        require(''.join('A' if g[0] == 'and' else 'O' for g in gates[first:]) == shape,
                'suffix operation shape disagrees with metadata')
        checks['suffix_shape'] = shape
    return junk, checks


def normalize_circuit(gates: list[list], output: int) -> dict:
    """Remove constants/identities, then prune and renumber. Constant fixtures
    return constant_output; valid witnesses for the fixed target never do."""
    truth_tables(gates, augmented=True)  # Validate structure even for direct callers.
    require(type(output) is int and 0 <= output < AUGMENTED_INPUTS + len(gates),
            'invalid original output for normalization')
    mapping = [('wire', i) for i in range(N)] + [('constant', False), ('constant', True)]
    reduced = []
    folded = 0
    aliases = 0

    def const(ref, value):
        return ref[0] == 'constant' and ref[1] is value

    for op, ai, bi in gates:
        a, b = mapping[ai], mapping[bi]
        result = None
        if op == 'and':
            if const(a, False) or const(b, False): result = ('constant', False)
            elif const(a, True): result = b
            elif const(b, True): result = a
        else:
            if const(a, True) or const(b, True): result = ('constant', True)
            elif const(a, False): result = b
            elif const(b, False): result = a
        if result is None and a == b:
            result = a
        if result is not None:
            if result[0] == 'constant': folded += 1
            else: aliases += 1
        else:
            require(a[0] == b[0] == 'wire', 'normalization retained an unresolved constant')
            result = ('wire', N + len(reduced))
            reduced.append([op, *sorted((a[1], b[1]))])
        mapping.append(result)
    result = mapping[output]
    statistics = {'original_gate_count': len(gates), 'constant_folded_gates': folded,
                  'identity_or_alias_gates': aliases, 'gates_before_dead_pruning': len(reduced)}
    if result[0] == 'constant':
        statistics['dead_gates_pruned'] = len(reduced)
        return {'inputs': N, 'gates': [], 'output': None, 'constant_output': result[1],
                'size': 0, 'normalization': statistics}
    live = reachable_gates(reduced, result[1], N)
    renumber = {i: i for i in range(N)}
    final = []
    for i, (op, a, b) in enumerate(reduced):
        if i in live:
            require(a in renumber and b in renumber, 'normalization lost a live predecessor')
            final.append([op, renumber[a], renumber[b]])
            renumber[N + i] = N + len(final) - 1
    statistics['dead_gates_pruned'] = len(reduced) - len(final)
    require(result[1] in renumber, 'normalization lost the output')
    require(len(final) <= len(gates), 'normalization increased the gate count')
    return {'inputs': N, 'gates': final, 'output': renumber[result[1]],
            'size': len(final), 'normalization': statistics}


def audit(cnf_path: Path, stdout_path: Path) -> tuple[dict, dict, dict]:
    metadata_path = cnf_path.with_suffix('.json')
    cnf_raw = cnf_path.read_bytes()
    metadata_raw = metadata_path.read_bytes()
    model_raw = stdout_path.read_bytes()
    meta = load_metadata(metadata_raw)
    digest = hashlib.sha256(cnf_raw).hexdigest()
    require(digest == meta['sha256'].lower(), 'CNF SHA-256 disagrees with metadata')
    assignment, duplicate_literals = parse_model(model_raw, meta['variables'])
    clauses = check_cnf(cnf_raw, meta, assignment)
    gates, output = decode(meta, assignment)
    tables = truth_tables(gates)
    check_target(tables, output, 'original')
    junk, checks = check_requested(meta, gates, output, tables)
    normalized = normalize_circuit(gates, output)
    require('constant_output' not in normalized, 'normalization produced a constant for a nonconstant target')
    normalized_tables = truth_tables(normalized['gates'], augmented=False)
    check_target(normalized_tables, normalized['output'], 'normalized')
    require(reachable_gates(normalized['gates'], normalized['output'], N) ==
            set(range(normalized['size'])), 'normalization left a dead gate')
    provenance = {'cnf_sha256': digest, 'metadata_sha256': hashlib.sha256(metadata_raw).hexdigest(),
                  'kissat_stdout_sha256': hashlib.sha256(model_raw).hexdigest()}
    original = {'schema_version': 1, 'gap': 'L-meta-1342', 'inputs': N,
                'virtual_false': VIRTUAL_FALSE, 'virtual_true': VIRTUAL_TRUE,
                'gates': gates, 'output': output, 'size': len(gates), 'junk': junk,
                'verified_inputs': INPUT_COUNT, 'requested_constraints': checks,
                'provenance': provenance}
    normalized.update(schema_version=1, gap='L-meta-1342', verified_inputs=INPUT_COUNT,
                      provenance=provenance, gate_wire_offset=N,
                      meets_posted_gate_limit=normalized['size'] <= 21)
    report = {'status': 'VALIDATED', 'gap': 'L-meta-1342', 'sat_status': 'SATISFIABLE',
              'assigned_variables': len(assignment), 'consistent_duplicate_model_literals': duplicate_literals,
              'clauses_checked': clauses, 'verified_inputs_per_circuit': INPUT_COUNT,
              'original_gate_count': len(gates), 'normalized_gate_count': normalized['size'],
              'posted_gate_limit': 21, 'meets_posted_gate_limit': normalized['size'] <= 21,
              'requested_constraints': checks, 'provenance': provenance,
              'lean_checked': False, 'scope': 'SAT model and circuit validation only; not gap-checker acceptance'}
    return original, normalized, report


def atomic_json(path: Path, value: dict) -> None:
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8', dir=path.parent,
                                         prefix=path.name + '.tmp.', delete=False) as stream:
            temporary = Path(stream.name)
            json.dump(value, stream, indent=2, sort_keys=True, allow_nan=False)
            stream.write('\n')
        os.replace(temporary, path)
        temporary = None
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def validate(cnf_path: Path, stdout_path: Path) -> dict:
    original, normalized, report = audit(cnf_path, stdout_path)
    destinations = {
        'original_candidate': cnf_path.with_suffix('.validated.original.json'),
        'normalized_candidate': cnf_path.with_suffix('.validated.normalized.json'),
        'validation_report': cnf_path.with_suffix('.validated.json'),
    }
    inputs = {cnf_path.resolve(), cnf_path.with_suffix('.json').resolve(), stdout_path.resolve()}
    require(all(path.resolve() not in inputs for path in destinations.values()),
            'a result path would overwrite an input')
    report['artifacts'] = {key: str(path.resolve()) for key, path in destinations.items()}
    atomic_json(destinations['original_candidate'], original)
    atomic_json(destinations['normalized_candidate'], normalized)
    atomic_json(destinations['validation_report'], report)
    return report


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cnf', type=Path)
    parser.add_argument('kissat_stdout', type=Path)
    args = parser.parse_args(argv)
    try:
        report = validate(args.cnf, args.kissat_stdout)
    except (ValidationError, OSError, ValueError) as error:
        print(f'REJECTED: {error}', file=sys.stderr)
        return 1
    print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == '__main__':
    sys.exit(main())
