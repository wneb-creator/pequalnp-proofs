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
pinned = {
    "FoundationI0I3I4.lean": "1aa3197a97326f137cbd49f1d518b9eb3ca794b728c4f858b5d6115fe154d830",
    "TwoIneligible.lean": "6b72cd35d68206bc570a30c92a998aab4f37c06e0a8d308f09dbc5cd4047e733",
    "NeighborhoodCase.lean": "78c4c4242296ea4f5ec3efd0607950b5c729378b97f889520f902701f9596b64",
}
manifest = {}
for name, expected in pinned.items():
    data = (source_dir / name).read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    if actual != expected:
        raise SystemExit(f"Unexpected source hash for {name}: {actual}")
    manifest[name] = {"bytes": len(data), "sha256": actual}
    if name == "FoundationI0I3I4.lean":
        target = "FoundationI0I3I4Audit.lean"
    elif name == "NeighborhoodCase.lean":
        target = "N0CompleteAudit.lean"
    else:
        target = "I2Standalone.lean"
        old = b"PEqualNP.Outside.L_meta_2590_aux"
        new = old + b".I2Standalone"
        assert new not in data and data.count(old) == 143
        relocated = data.replace(old, new)
        assert relocated.replace(new, old) == data
        data = relocated
    (args.out / target).write_bytes(data)
    manifest[target] = {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}
wrapper = (source_dir / "RemainingOne.lean").read_bytes()
(args.out / "RemainingOne.lean").write_bytes(wrapper)
manifest["RemainingOne.lean"] = {"bytes": len(wrapper), "sha256": hashlib.sha256(wrapper).hexdigest()}
(args.out / "reproduction-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps(manifest, indent=2))
