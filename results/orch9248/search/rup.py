"""Exact constructive unit propagation for the repository's PHP/RUP definitions."""
import itertools
import json
import re
from pathlib import Path

EVEN = sum(1 << (2*i) for i in range(20))
ODD = EVEN << 1


def negate(mask):
    return ((mask & EVEN) << 1) | ((mask & ODD) >> 1)


def literals(mask):
    return [i for i in range(40) if mask >> i & 1]


def mask_of(clause):
    return sum(1 << i for i in set(clause))


def php():
    clauses = [sum(1 << (2*(4*p+h)) for h in range(4)) for p in range(5)]
    clauses += [sum(1 << (2*(4*p+h)+1) for p in pair)
                for h in range(4) for pair in itertools.combinations(range(5),2)]
    assert len(clauses) == 45
    return clauses


def propagation(database, candidate=0):
    """Returns conflict, ordered clause-index hints, and all forced literals.

    Every successful certificate ends with an actual falsified known clause.
    Merely inconsistent assumptions are not accepted as an immediate conflict.
    """
    forced = negate(candidate)
    false = candidate
    hints = []
    while True:
        changed = False
        for index,clause in enumerate(database):
            remaining = clause & ~false
            if not remaining:
                return True,hints+[index],forced
            if remaining & (remaining-1) == 0 and not (remaining & forced):
                forced |= remaining
                false |= negate(remaining)
                hints.append(index)
                changed = True
        if not changed:
            return False,hints,forced


def verify_hints(database,candidate,hints):
    forced = negate(candidate)
    for number,index in enumerate(hints):
        if not 0 <= index < len(database):
            return False
        clause = database[index]
        remaining = clause & ~negate(forced)
        if not remaining:
            return number == len(hints)-1
        if remaining & (remaining-1):
            return False
        forced |= remaining
    return False


def check_run(clauses):
    database = php()
    steps = []
    for number,clause in enumerate(clauses):
        ok,hints,forced = propagation(database,clause)
        assert ok, ('not RUP',number,literals(clause))
        assert verify_hints(database,clause,hints)
        steps.append([literals(clause),hints])
        database.append(clause)
    return dict(learned_count=len(clauses),contains_empty=0 in clauses,
                oldest_first_clauses=[literals(c) for c in clauses],steps=steps,
                literal_encoding='2*(4*pigeon+hole)+(0 positive,1 negative)',
                input_order='5 positive pigeon rows, then hole-major pairs p<q',
                newest_first_run=list(reversed([literals(c) for c in clauses])))


def candidates(max_width=3):
    for width in range(1,max_width+1):
        for variables in itertools.combinations(range(20),width):
            for signs in itertools.product((0,1),repeat=width):
                yield sum(1 << (2*v+s) for v,s in zip(variables,signs))


def minimal_rup(database,pool):
    found = []
    for clause in pool:
        if any(known & clause == known for known in database):
            continue
        if any(known & clause == known for known in found):
            continue
        if propagation(database,clause)[0]:
            found.append(clause)
    return found


def extract_baseline(source):
    text = Path(source).read_text()
    clauses = []
    for name,definition in re.findall(r'def c(\d+) : Clause VV := (.*)',text):
        assert int(name) == len(clauses)
        entries = re.findall(r'\(\((\d+), (\d+)\), (true|false)\)',definition)
        clause = mask_of(2*(4*int(p)+int(h))+(0 if sign == 'true' else 1)
                         for p,h,sign in entries)
        clauses.append(clause)
    return clauses


if __name__ == '__main__':
    baseline = extract_baseline('lean/PEqualNP/Outside/L_meta_9250.lean')
    report = check_run(baseline)
    destination = Path(__file__).resolve().parent/'baseline20.json'
    destination.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'baseline_count':len(baseline),'verified':True,'path':str(destination)}))
