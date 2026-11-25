import argparse
import hashlib
import json
import re
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("module")
parser.add_argument("output", type=Path)
parser.add_argument("--module-dir", type=Path, default=Path("/tmp/oec/pequalnp-pilot-62/lean-modules"))
parser.add_argument("--manifest", type=Path)
args = parser.parse_args()
seen, active, ordered = set(), set(), []

def visit(module):
    if module == "PEqualNP.Defs" or module in seen:
        return
    if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*", module):
        raise ValueError("Invalid module name")
    if module in active:
        raise ValueError("Cyclic module dependency")
    path = args.module_dir.joinpath(*module.split(".")).with_suffix(".lean")
    text = path.read_text()
    active.add(module)
    body = []
    for line in text.splitlines():
        if line.startswith("import "):
            for dependency in line.split("--", 1)[0].split()[1:]:
                visit(dependency)
        else:
            body.append(line)
    active.remove(module)
    seen.add(module)
    ordered.append((module, path, text, "\n".join(body).strip()))

visit(args.module)
source = "import PEqualNP.Defs\n\n" + "\n\n".join(item[3] for item in ordered) + "\n"
if "_root_" in source or '"' in source or re.search(r"\b(sorry|axiom|native_decide|admit)\b", source):
    raise ValueError("A forbidden token occurs in the flattened proof source")
for attributes in re.findall(r"@\[([^\]]+)\]", source):
    if attributes.strip() != "simp":
        raise ValueError("Only simp attributes are allowed")
for option in re.findall(r"\bset_option\s+(\S+)", source):
    if option not in {"maxRecDepth", "maxHeartbeats"}:
        raise ValueError("An unexpected option occurs in the proof source")
args.output.write_text(source)
manifest = {
    "status": "Flattened source; requires its own lake build and checker run",
    "sha256": hashlib.sha256(source.encode()).hexdigest(),
    "lines": len(source.splitlines()),
    "modules": [{"module": name, "source": str(path), "sha256": hashlib.sha256(text.encode()).hexdigest()}
                for name, path, text, _ in ordered],
}
manifest_path = args.manifest or Path("/tmp/oec/pequalnp-pilot-62") / (args.output.stem + ".manifest.json")
manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps({"modules": len(ordered), "lines": manifest["lines"], "sha256": manifest["sha256"]}))
