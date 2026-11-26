from pathlib import Path
import argparse
import hashlib
import json

parser = argparse.ArgumentParser()
parser.add_argument("--repo", type=Path, required=True)
parser.add_argument("--out", type=Path, required=True)
args = parser.parse_args()
args.out.mkdir(parents=True, exist_ok=True)
source_dir = args.repo / "results" / "swarm"
# Each tuple is tracked source, exact SHA256, emitted module, optional namespace suffix/count.
specs = [
    ("FoundationI0I3I4.lean", "1aa3197a97326f137cbd49f1d518b9eb3ca794b728c4f858b5d6115fe154d830", "FoundationI0I3I4Audit", None, 0),
    ("TwoIneligible.lean", "6b72cd35d68206bc570a30c92a998aab4f37c06e0a8d308f09dbc5cd4047e733", "I2Standalone", ".I2Standalone", 143),
    ("NeighborhoodCase.lean", "78c4c4242296ea4f5ec3efd0607950b5c729378b97f889520f902701f9596b64", "N0CompleteAudit", None, 0),
    ("RemainingOne.lean", "28c296687c586e814f3584e4892c530b042fa0ffa2f5e53f805de8577b546ba5", "RemainingI1Audit", None, 0),
    ("OneIneligibleCensus.lean", "4ac9d5967a0fe35a31ba1a62333174bcac4fd9e366a683786ee124c7a0ece05b", "R1StandaloneAudit", ".R1Standalone", 7),
    ("R0Resource.lean", "714960ac5ab128277ecd9849841855828c5d4b743acb68fd7ea62b0b0861b78b", "H8R0CompactAudit", None, 0),
    ("R0CurrentAdapter.lean", "93859579d38fe8fa48dbdd62c6dd6a9dc01fb750781e9cb54abaebbf4c0ed75a", "R0CurrentAdapterAudit", None, 0),
    ("RemainingThree.lean", "3a47ae782dcfb1806a2460c5a5cc7e461af3d94e7d4d24797e6ad1321879771d", "RemainingThree", None, 0),
]
manifest = {}
for name, expected, module, suffix, count in specs:
    original = (source_dir / name).read_bytes()
    actual = hashlib.sha256(original).hexdigest()
    if actual != expected:
        raise SystemExit(f"Unexpected source hash for {name}: {actual}")
    data = original
    if suffix is not None:
        old = b"PEqualNP.Outside.L_meta_2590_aux"
        new = old + suffix.encode("ascii")
        assert new not in data and data.count(old) == count
        data = data.replace(old, new)
        assert data.replace(new, old) == original
    target = module + ".lean"
    (args.out / target).write_bytes(data)
    manifest[name] = {
        "source_bytes": len(original), "source_sha256": actual,
        "module": module, "output_bytes": len(data),
        "output_sha256": hashlib.sha256(data).hexdigest(),
        "prefix_replacements": count,
    }
(args.out / "reproduction-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps(manifest, indent=2))
