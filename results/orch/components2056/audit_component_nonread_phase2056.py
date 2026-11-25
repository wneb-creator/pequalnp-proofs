from pathlib import Path
from itertools import zip_longest
import datetime
import hashlib
import json
import time

root = Path("/tmp/oec/pequalnp-pilot-121/components2056")
started = time.monotonic()

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def assignment(path, n):
    values = bytearray(n + 1)
    seen = bytearray(n + 1)
    sat = False
    count = 0
    with path.open() as stream:
        for line in stream:
            if line.startswith("s "):
                sat = line.strip() == "s SATISFIABLE"
            if line.startswith("v "):
                for literal in map(int, line[2:].split()):
                    if not literal:
                        continue
                    var = abs(literal)
                    assert 1 <= var <= n
                    value = literal > 0
                    assert not seen[var] or values[var] == value
                    if not seen[var]:
                        seen[var] = 1
                        count += 1
                    values[var] = value
    assert sat and count == n
    return values


def clauses(path, n, count):
    header = False
    with path.open() as stream:
        for line in stream:
            if not line.strip() or line.startswith("c "):
                continue
            if line.startswith("p "):
                assert not header and line.split() == ["p", "cnf", str(n), str(count)]
                header = True
                continue
            assert header
            literals = list(map(int, line.split()))
            assert literals[-1] == 0 and all(0 < abs(x) <= n for x in literals[:-1])
            yield literals[:-1]
    assert header

reports = []
for label, actual in [("control67", True), ("target63", False)]:
    phase_path = root / f"v5-nonread-{label}-warm.phase.json"
    phase = json.loads(phase_path.read_text())
    n, expected_count = phase["variables"], phase["clauses"]
    mask_path = root / phase["mask_name"]
    mask = mask_path.read_bytes()
    assert len(mask) == (n + 7) // 8 and digest(mask_path) == phase["mask_sha256"]
    flip = bytearray(n + 1)
    for var in range(1, n + 1):
        flip[var] = (mask[(var - 1) // 8] >> ((var - 1) % 8)) & 1
    original_path = root / f"v5-nonread-{label}.cnf"
    warm_path = root / f"v5-nonread-{label}-warm.cnf"
    assert digest(original_path) == phase["original_cnf_sha256"]
    assert digest(warm_path) == phase["warm_cnf_sha256"]
    if actual:
        warm_assignment = assignment(root / "v5-nonread-control67-warm-checked.sol", n)
        original_assignment = assignment(root / "v5-nonread-control67-warm-checked.unrenamed.sol", n)
        assert all(original_assignment[v] == (warm_assignment[v] ^ flip[v]) for v in range(1, n + 1))
    failures = []
    count = 0
    for count, pair in enumerate(zip_longest(clauses(original_path, n, expected_count),
                                             clauses(warm_path, n, expected_count)), 1):
        original, renamed = pair
        assert original is not None and renamed is not None
        assert renamed == [-x if flip[abs(x)] else x for x in original]
        if not any((x > 0) == (not flip[abs(x)]) for x in original):
            failures.append({"index": count, "literals": original})
        if actual:
            assert any(original_assignment[abs(x)] == (x > 0) for x in original)
            assert any(warm_assignment[abs(x)] == (x > 0) for x in renamed)
    assert count == expected_count and failures == phase["violated_original_clauses"]
    reports.append({"case": label, "variables": n, "clauses": count,
                    "every_sign_mapping_checked": True, "preferred_phase_failures": failures,
                    "native_and_unrenamed_assignment_checked": actual,
                    "phase_sha256": digest(phase_path)})
    print(label, count, "clauses checked", flush=True)
meta = json.loads((root / "v5-nonread-control67-warm-checked.metadata.json").read_text())
assert digest(root / "v5-nonread-control67-warm-checked.candidate.json") == meta["candidate_sha256"] == "0a751f1c6fbf2e5e6209239443d122f3b8334e84519ed3139ba4373f0fb33f35"
result = {"reviewer": "circuit_search", "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
          "helper_sha256": digest(root / "extend_nonread_phase.py"),
          "runner_sha256": digest(root / "run_sat_nonread_warm.py"),
          "baseline_runner_sha256": digest("/workspace/pequalnp-proofs/results/orch/components2056/run_sat_warm_checked_v2.py"),
          "static_delta_approved": True, "reports": reports,
          "actual_candidate_matches_independently_reviewed_cold67": True,
          "candidate_sha256": meta["candidate_sha256"], "elapsed_seconds": time.monotonic() - started,
          "scope": "Exact phase-renaming/helper/wrapper and actual-model validation; no63-gate witness or lower-bound claim."}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result), flush=True)
