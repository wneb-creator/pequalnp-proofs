import hashlib
import itertools
import json
from pathlib import Path

base = Path("results/orch/lemmas")
source = base / "circuit_search/k6-partition-seeds.json"
casefile = base / "circuit_search/subsets/k6_p3.json"
all_seeds = json.loads(source.read_text())
assert isinstance(all_seeds, list) and len(all_seeds) == 203
seeds = [s for s in all_seeds if any(len(b) > 1 for b in s["blocks"])]
assert len(seeds) == 202
case = json.loads(casefile.read_text())
negatives = [m for m, target in case["tests"] if not target]
signatures = []
for seed in seeds:
    signature = 0
    for i, mask in enumerate(negatives):
        values = [bool(mask >> j & 1) for j in range(17)]
        for op, a, b in seed["gates"]:
            values.append(values[a] or values[b] if op else values[a] and values[b])
        if values[seed["output"]]:
            signature |= 1 << i
    assert signature.bit_count() == seed["negative_errors"]
    signatures.append(signature)
exact = []
best_count = len(negatives) + 1
best_pair = None
for i, j in itertools.combinations(range(len(seeds)), 2):
    count = (signatures[i] & signatures[j]).bit_count()
    if count < best_count:
        best_count, best_pair = count, (i, j)
    if count == 0:
        exact.append([i, j])
result = {
    "kind": "computational census, not a Lean lower-bound theorem",
    "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
    "case_sha256": hashlib.sha256(casefile.read_bytes()).hexdigest(),
    "proper_partition_count": len(seeds),
    "pair_count": len(seeds) * (len(seeds) - 1) // 2,
    "exact_AND_pairs": exact,
    "best_common_negative_count": best_count,
    "best_blocks": [seeds[i]["blocks"] for i in best_pair],
}
(base / "algebra_strategy/k6_partition_pair_guards.json").write_text(json.dumps(result, indent=2))
print(json.dumps(result, indent=2))
