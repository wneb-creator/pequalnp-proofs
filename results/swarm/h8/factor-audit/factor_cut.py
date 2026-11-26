"""Exploratory exact Horn/parity cut for L670's monotone SingleFactor.

No result from this module is a Lean proof.  The constraints correspond to
L670.hornRule and L670.parityRule and retain row witnesses for proof replay.
"""
from itertools import combinations, product


def factor_constraints(wires, pairs):
    positives = sorted({p for p, _ in pairs})
    negatives = sorted({n for _, n in pairs})
    cells = {}
    row_labels = {p: {} for p in positives}
    col_labels = {n: {} for n in negatives}
    for p, n in product(positives, negatives):
        labels = [i for i, w in enumerate(wires) if w >> p & 1 and not w >> n & 1]
        if len(labels) == 1:
            i = labels[0]
            cells[p, n] = i
            row_labels[p].setdefault(i, n)
            col_labels[n].setdefault(i, p)
    row_cross, col_cross = {}, {}
    for p, labels in row_labels.items():
        for a, b in combinations(sorted(labels), 2):
            row_cross.setdefault((a, b), (p, labels[a], labels[b]))
    for n, labels in col_labels.items():
        for a, b in combinations(sorted(labels), 2):
            col_cross.setdefault((a, b), (n, labels[a], labels[b]))
    parity = {
        ab: (*row_cross[ab], *col_cross[ab])
        for ab in row_cross.keys() & col_cross.keys()
    }
    horns = {}
    for (p, n), c in cells.items():
        for a, na in row_labels[p].items():
            for b, pb in col_labels[n].items():
                if c in (a, b):
                    continue
                key = min(a, b), max(a, b), c
                horns.setdefault(key, (p, n, pb, na, a, b))
    return parity, horns


def factor_cut(wires, pairs, cap):
    """Return witness constraints if they exclude a Live state, otherwise None."""
    if cap > len(wires):
        return None
    if cap < len(wires) - 1:
        return {"kind": "width"}
    parity, horns = factor_constraints(wires, pairs)
    if cap == len(wires) - 1 and parity:
        ab, witness = next(iter(parity.items()))
        return {"kind": "cross", "wires": ab, "rows": witness}

    graph = [[] for _ in wires]
    for a, b in parity:
        graph[a].append(b)
        graph[b].append(a)
    colors = [None] * len(wires)
    components = []
    for start in range(len(wires)):
        if colors[start] is not None:
            continue
        colors[start] = 0
        component = []
        todo = [start]
        while todo:
            a = todo.pop()
            component.append(a)
            for b in graph[a]:
                if colors[b] is None:
                    colors[b] = 1 - colors[a]
                    todo.append(b)
                elif colors[b] == colors[a]:
                    return {"kind": "parity", "parity": parity}
        components.append(component)
    for values in product([0, 1], repeat=len(components)):
        bits = [0] * len(wires)
        for component, value in zip(components, values):
            for a in component:
                bits[a] = colors[a] ^ value
        if all(not bits[a] or not bits[b] or bits[c] for a, b, c in horns):
            return None
    return {"kind": "factor", "parity": parity, "horns": horns}


def constraints_satisfiable(constraints):
    clauses = []
    for kind, variables, _ in constraints:
        if kind == "p":
            a, b = variables
            clauses.extend([{a: 0, b: 0}, {a: 1, b: 1}])
        else:
            a, b, c = variables
            if c in (a, b):
                continue
            clauses.append({a: 1, b: 1, c: 0})

    def solve(values):
        while True:
            changed = False
            for clause in clauses:
                if any(v in values and values[v] != b for v, b in clause.items()):
                    continue
                missing = [v for v in clause if v not in values]
                if not missing:
                    return False
                if len(missing) == 1:
                    v = missing[0]
                    values[v] = 1 - clause[v]
                    changed = True
            if not changed:
                break
        choices = []
        for clause in clauses:
            if any(v in values and values[v] != b for v, b in clause.items()):
                continue
            choices = [v for v in clause if v not in values]
            break
        if not choices:
            return True
        v = choices[0]
        return solve(values | {v: 0}) or solve(values | {v: 1})

    return solve({})


def minimal_factor_core(wires, pairs):
    parity, horns = factor_constraints(wires, pairs)
    constraints = [("p", key, witness) for key, witness in sorted(parity.items())]
    constraints += [("h", key, witness) for key, witness in sorted(horns.items())]
    if constraints_satisfiable(constraints):
        return None
    i = 0
    while i < len(constraints):
        attempt = constraints[:i] + constraints[i+1:]
        if not constraints_satisfiable(attempt):
            constraints = attempt
        else:
            i += 1
    return constraints


def core_tags(core):
    """Only-wire facts needed to replay a core using existing L670 lemmas."""
    tags = set()
    for kind, variables, witness in core:
        if kind == "p":
            a, b = variables
            p, na, nb, n, pa, pb = witness
            tags.update([(a, p, na), (b, p, nb), (a, pa, n), (b, pb, n)])
        else:
            _, _, c = variables
            p, n, pb, na, a, b = witness
            tags.update([(a, p, na), (b, pb, n), (c, p, n)])
    return sorted(tags)
