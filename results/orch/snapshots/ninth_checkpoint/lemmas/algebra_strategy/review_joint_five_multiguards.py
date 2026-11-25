"""Independent full-truth, prime-term and cost audit; no circuit correctness claim."""
import hashlib
import itertools
import json
import math
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
SEARCH = HERE.parent / "circuit_search"
case = json.loads((HERE / "five-owner-joint-packet.json").read_text())[0]
seeds = json.loads((SEARCH / "joint-five-multiguard-seeds.json").read_text())
assembler = runpy.run_path(str(HERE / "assemble_five_owner.py"))["assemble_five"]
raw, available = case["raw_inputs"], case["inputs"]
count = 1 << raw
columns = [sum(1 << mask for mask in range(count) if mask >> i & 1) for i in range(raw)]
for feature in case["features"]:
    columns.append(0)
    for i in feature["raw_indices"]:
        columns[-1] |= columns[i]
target = 0
for a, b in case["edges"]:
    target |= columns[a] & columns[b]

def evaluate(n, gates, inputs):
    values = list(inputs)
    for i, (op, a, b) in enumerate(gates):
        assert op in (0, 1) and 0 <= a < n+i and 0 <= b < n+i
        values.append((values[a] | values[b]) if op else (values[a] & values[b]))
    return values[-1]

def prime_terms(truth):
    return [mask for mask in range(count) if truth >> mask & 1 and all(not(truth >> (mask ^ (1 << i)) & 1) for i in range(raw) if mask >> i & 1)]

def minimal(terms):
    kept = []
    for term in sorted(set(terms), key=lambda x: (x.bit_count(), x)):
        if not any(old & term == old for old in kept):
            kept.append(term)
    return frozenset(kept)

def full_dnf(gates):
    values = [frozenset([1 << i]) for i in range(26)]
    for op, a, b in gates:
        values.append(minimal(values[a] | values[b]) if op else minimal(x | y for x in values[a] for y in values[b]))
    return values[-1]

def disjunction(s):
    answer = 0
    for i in s:
        answer |= columns[i]
    return answer

rows = []
neighbors = [{b for a, b in case["edges"] if a == p} for p in range(5)]
outside_edges = [(owner["outside_point"], line) for owner in case["outside_owners"] for line in owner["original_neighbors"]]
assert len(outside_edges) == 32
for index, seed in enumerate(seeds):
    gates = seed["gates"]
    actual = evaluate(available, gates, columns)
    group = set(seed["group"])
    formula = disjunction(group) & disjunction(set().union(*(neighbors[p] for p in group)))
    for a in seed["guard_sets"]:
        a = set(a)
        formula &= disjunction(a) | disjunction(set().union(*(neighbors[p] for p in group-a)))
    for p in set(range(5)) - group:
        formula |= columns[p] & disjunction(neighbors[p])
    assert actual == formula, (index, "guard formula")
    assert target & ~actual == 0, (index, "missing edge")
    assert sum(op == 0 for op, _, _ in gates) == seed["ands"] >= 6
    false = (actual & ~target).bit_count()
    wrong = [mask for mask, label in case["raw_tests"] if not label and actual >> mask & 1]
    one_owner = sum((mask & 31).bit_count() == 1 for mask in wrong)
    dnfs = [frozenset([1 << i]) for i in range(raw)]
    for feature in case["features"]:
        dnfs.append(frozenset(1 << i for i in feature["raw_indices"]))
    for op, a, b in gates:
        dnfs.append(minimal(dnfs[a] | dnfs[b]) if op else minimal(x | y for x in dnfs[a] for y in dnfs[b]))
    primes = list(dnfs[-1])
    from_primes = 0
    for term in primes:
        product = (1 << count) - 1
        for i in range(raw):
            if term >> i & 1:
                product &= columns[i]
        from_primes |= product
    assert from_primes == actual
    quadratic = 0
    for term in primes:
        if term.bit_count() == 2:
            a, b = [i for i in range(raw) if term >> i & 1]
            quadratic |= columns[a] & columns[b]
    assert all(term.bit_count() >= 2 for term in primes)
    higher = (actual & ~quadratic).bit_count()
    assert higher > 0
    assert (false, len(wrong), one_owner, len(wrong)+16*one_owner, higher) == (seed["false_assignments"], seed["boundary_errors"], seed["one_owner_errors"], seed["weighted_score"], seed["assignments_requiring_higher_terms"])
    full, metadata = assembler(case, gates)
    assert metadata == seed["assembly"]
    active = {available + len(gates) - 1}
    for i in reversed(range(len(gates))):
        if available+i in active:
            active.update(gates[i][1:])
    used = active & set(range(available))
    independent_extra = sum(owner["prefix_extra_cost_table"][sum(1 << i for i, token in enumerate(owner["optional_inputs"]) if token in used)] for owner in case["outside_owners"])
    assert len(gates) + independent_extra <= 23
    assert len(full) == 39 + independent_extra + len(gates) + 1 <= 63
    expected_primes = [sum(1 << case["input_original"][i] for i in range(raw) if term >> i & 1) for term in primes]
    expected_primes.extend((1 << a) | (1 << b) for a, b in outside_edges)
    assert full_dnf(full) == minimal(expected_primes), (index, "full assembly semantics")
    rows.append(dict(index=index, gates=len(gates), ands=seed["ands"], prefix_extra=independent_extra, boundary_errors=len(wrong), weighted_score=seed["weighted_score"], false_assignments=false, higher_degree_primes=sum(t.bit_count()>2 for t in primes), higher_only_assignments=higher))
expected_builds = sum(math.comb(5,size)*sum(math.comb((1 << size)-2,k) for k in range(2,4))*2 for size in (3,4,5))
assert expected_builds == 14240
assert len(seeds) == 382
report = dict(status="APPROVED computational seed audit; all seeds remain incorrect", seeds=len(seeds), enumerated_constructions=expected_builds, full_raw_assignments_checked=len(seeds)*count, full26_semantics="exact minimal-DNF comparison against core plus outside stars", min_weighted_score=min(r["weighted_score"] for r in rows), data_sha256=hashlib.sha256((SEARCH / "joint-five-multiguard-seeds.json").read_bytes()).hexdigest(), generator_sha256=hashlib.sha256((SEARCH / "generate_joint_five_multiguards.py").read_bytes()).hexdigest(), rows=rows)
(HERE / "joint-five-multiguards-independent-review.json").write_text(json.dumps(report,indent=2)+"\n")
print(json.dumps({k:v for k,v in report.items() if k!="rows"},indent=2))
