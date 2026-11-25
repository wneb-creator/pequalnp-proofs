from collections import Counter
from itertools import combinations_with_replacement, product
import json
from repair_neighborhood import CNF


def holds(clauses, assignment):
    return all(any(assignment[abs(lit)] == (lit > 0) for lit in clause) for clause in clauses)


def contradiction(clauses, assignment):
    assignment = dict(assignment)
    changed = True
    while changed:
        changed = False
        for clause in clauses:
            if any(abs(lit) in assignment and assignment[abs(lit)] == (lit > 0) for lit in clause):
                continue
            open_literals = [lit for lit in clause if abs(lit) not in assignment]
            if not open_literals:
                return True
            if len(open_literals) == 1:
                literal = open_literals[0]
                assignment[abs(literal)] = literal > 0
                changed = True
    return False


cardinality_cases = 0
for count in range(1, 9):
    for budget in range(min(count, 4) + 1):
        for signed in (False, True):
            literals = [-(i + 1) if signed and i % 2 else i + 1 for i in range(count)]
            cnf = CNF(count)
            counters = cnf.at_most(literals, budget)
            for bits in product((False, True), repeat=count):
                assignment = {abs(lit): value if lit > 0 else not value for lit, value in zip(literals, bits)}
                if sum(bits) > budget:
                    assert contradiction(cnf.clauses, assignment)
                else:
                    for i, row in enumerate(counters):
                        for j, variable in enumerate(row):
                            assignment[variable] = sum(bits[:i + 1]) >= j + 1
                    assert holds(cnf.clauses, assignment)
                cardinality_cases += 1

mux_cases = 0
pairs = list(combinations_with_replacement(range(3), 2))
for old_a, old_b in pairs:
    cnf = CNF(6)
    flip = cnf.var()
    left = cnf.mux(flip, old_a + 1, old_b + 1)
    right = cnf.mux(flip, old_b + 4, old_a + 4)
    for new_a, new_b in pairs:
        minimum = 2
        for flipped in (False, True):
            fixed = {i + 1: i == new_a for i in range(3)}
            fixed.update({i + 4: i == new_b for i in range(3)})
            fixed[flip] = flipped
            accepted = []
            for lm, rm in product((False, True), repeat=2):
                if holds(cnf.clauses, {**fixed, left: lm, right: rm}):
                    accepted.append((lm, rm))
            assert len(accepted) == 1
            minimum = min(minimum, 2 - sum(accepted[0]))
            mux_cases += 1
        expected = 2 - sum((Counter((old_a, old_b)) & Counter((new_a, new_b))).values())
        assert minimum == expected

print(json.dumps({'status': 'PASS', 'cardinality_assignments': cardinality_cases,
                  'operand_matching_cases': mux_cases, 'signed_literals_tested': True}))
