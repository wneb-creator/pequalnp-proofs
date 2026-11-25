from datetime import datetime, timezone
from itertools import product
from pathlib import Path
import json
import random
import time

started = datetime.now(timezone.utc).isoformat()
timer = time.monotonic()
edge_pairs = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5),
              (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]
rows = [tuple(bool(mask & (1 << i)) for i in range(9)) for mask in range(512)]
legal_pins = [pins for pins in product(range(10), repeat=2)
              if 0 in pins and not all(i in (0, 9) for i in pins)]

def read(wires, i):
    return wires[i] if i < len(wires) else False

def gate_eval(op, vals):
    if op == 'and':
        return all(vals)
    if op == 'or':
        return any(vals)
    assert op == 'not'
    return not (vals[0] if vals else False)

def circuit_eval(gates, output, wires):
    wires = list(wires)
    for op, pins in gates:
        wires.append(gate_eval(op, [read(wires, i) for i in pins]))
    return read(wires, output)

assert len(legal_pins) == 16
normalization_checks = 0
for pins in legal_pins:
    other = pins[1] if pins[0] == 0 else pins[0]
    assert 1 <= other < 9
    for row in rows:
        bank = row + (not row[0],)
        got = gate_eval('or', [read(bank, i) for i in pins])
        assert got == (row[0] or row[other])
        normalization_checks += 1

# Distinct arities, repetitions, forward references, and absent outputs are included.
rng = random.Random(3178)
circuits = []
for size in range(14):
    for _ in range(3):
        gates = []
        for j in range(size):
            op = rng.choice(['and', 'or', 'not'])
            pins = tuple(rng.randrange(11 + size + 4) for _ in range(rng.randrange(3)))
            gates.append((op, pins))
        circuits.append((gates, rng.randrange(11 + size + 4)))
for op in ['and', 'or', 'not']:
    for pins in [(), (0,), (0, 0), (1, 9), (11, 999)]:
        circuits.append(([(op, pins)], 11))

prefix_checks = 0
count_checks = 0
for gates, output in circuits:
    suffix_nots = sum(op == 'not' for op, _ in gates)
    suffix_binary = sum(op != 'not' for op, _ in gates)
    assert suffix_nots + suffix_binary == len(gates)
    for pins in legal_pins:
        full = [('not', (0,)), ('or', pins)] + gates
        assert len(full) == len(gates) + 2
        assert sum(op == 'not' for op, _ in full) == suffix_nots + 1
        assert sum(op != 'not' for op, _ in full) == suffix_binary + 1
        assert all(op in ('and', 'or', 'not') and len(ps) <= 2 for op, ps in full)
        count_checks += 1
        for row in rows:
            bank = row + (not row[0],)
            augmented = bank + (gate_eval('or', [read(bank, i) for i in pins]),)
            assert circuit_eval(full, output, row) == circuit_eval(gates, output, augmented)
            prefix_checks += 1

# The numerical bridge used by the proposed reduction is exhaustive in its range.
arithmetic_checks = 0
for size in range(14):
    for nots in range(size + 1):
        non_nots = size - nots
        if 13 <= non_nots + 1:
            assert nots <= 1
        arithmetic_checks += 1

report = {
    'started_utc': started,
    'finished_utc': datetime.now(timezone.utc).isoformat(),
    'elapsed_seconds': round(time.monotonic() - timer, 3),
    'legal_pin_lists': legal_pins,
    'normalization_checks': normalization_checks,
    'distinct_sample_circuits': len(circuits),
    'prefix_evaluation_checks': prefix_checks,
    'prefix_gate_count_checks': count_checks,
    'arithmetic_checks': arithmetic_checks,
    'verdict': 'PASS',
    'scope': 'Finite validation of pin normalization, evaluation-prefix identity, count identities, and arithmetic bridge. Does not exhaust all circuits or prove the circuit lower bound.'
}
out = Path('/tmp/oec/pequalnp-pilot-52/finite-analysis-validation.json')
out.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
