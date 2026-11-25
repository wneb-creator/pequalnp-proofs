"""Minimize shared NOT gates when realizing a signed binary circuit.

Each gate is (op, left, right, left_neg, right_neg), with op 0=AND, 1=OR.
Input and gate wires have their usual sequential indices. This is a search
utility, not a Lean proof or a lower-bound certificate.
"""


def realize_min_not(n, gates, output=None, output_neg=False):
    m = len(gates)
    if output is None:
        output = n + m - 1
    assert n > 0 and 0 <= output < n + m
    for j, (op, left, right, left_neg, right_neg) in enumerate(gates):
        assert op in (0, 1)
        assert 0 <= left < n + j and 0 <= right < n + j
        assert left_neg in (0, 1, False, True) and right_neg in (0, 1, False, True)
    active, pending = set(), [output]
    while pending:
        wire = pending.pop()
        if wire < n or wire in active:
            continue
        active.add(wire)
        pending.extend(gates[wire - n][1:3])
    mapping = {i: i for i in range(n)}
    trimmed = []
    for j, (op, left, right, left_neg, right_neg) in enumerate(gates):
        if n + j in active:
            mapping[n + j] = n + len(trimmed)
            trimmed.append((op, mapping[left], mapping[right], left_neg, right_neg))
    output = mapping[output]
    gates, m = trimmed, len(trimmed)
    edges = []
    incident = [[] for _ in range(m)]
    for j, (op, left, right, left_neg, right_neg) in enumerate(gates):
        assert op in (0, 1)
        for source, sign in ((left, left_neg), (right, right_neg)):
            assert 0 <= source < n + j and sign in (0, 1, False, True)
            eid = len(edges)
            edges.append((source, n + j, int(sign)))
            incident[j].append(eid)
            if source >= n:
                incident[source - n].append(eid)
    eid = len(edges)
    edges.append((output, None, int(output_neg)))
    if output >= n:
        incident[output - n].append(eid)
    needs = [sign for _, _, sign in edges]
    counts = [0] * (n + m)
    for (source, _, _), need in zip(edges, needs):
        counts[source] += need
    cost = sum(c > 0 for c in counts)
    best_cost, best_phase = cost, 0
    phase = 0
    for step in range(1, 1 << m):
        bit = (step & -step).bit_length() - 1
        phase ^= 1 << bit
        for edge in incident[bit]:
            source = edges[edge][0]
            before = counts[source] > 0
            counts[source] += 1 if not needs[edge] else -1
            needs[edge] ^= 1
            cost += (counts[source] > 0) - before
        if cost < best_cost:
            best_cost, best_phase = cost, phase
            if not best_cost:
                break
    phases = [0] * n + [(best_phase >> j) & 1 for j in range(m)]
    physical = []
    positive = list(range(n))
    negative = {}

    def read(source, neg):
        if not neg:
            return positive[source]
        if source not in negative:
            negative[source] = n + len(physical)
            physical.append((2, positive[source], positive[source]))
        return negative[source]

    for j, (op, left, right, left_neg, right_neg) in enumerate(gates):
        p = phases[n + j]
        a = read(left, int(left_neg) ^ phases[left] ^ p)
        b = read(right, int(right_neg) ^ phases[right] ^ p)
        positive.append(n + len(physical))
        physical.append((op ^ p, a, b))
    physical_output = read(output, int(output_neg) ^ phases[output])
    assert len(physical) == m + best_cost
    return {
        'binary_count': m,
        'not_count': best_cost,
        'phases': phases[n:],
        'gates': physical,
        'output_wire': physical_output,
    }
