"""Assemble the checked cofactor certificate and effective-reader bound."""

from pathlib import Path
import hashlib

REPO = Path(__file__).resolve().parents[2]
HERE = REPO / "results/orch1884/lemmas"
parts = [
    REPO / "results/orch2590/lemmas/MonoBase.lean",
    HERE / "NineCircuitFloor.lean",
    HERE / "ReaderBound.lean",
    HERE / "ConcreteReaderBound.lean",
]
chunks = []
for index, path in enumerate(parts):
    text = path.read_text()
    if index:
        text = "\n".join(line for line in text.splitlines() if not line.startswith("import "))
    chunks.append(text)
full = "\n\n".join(chunks)
full = full.replace("PEqualNP.Outside.L_meta_2590.Mono18",
                    "PEqualNP.Outside.L_meta_1884.ReaderCertificate")
assert len(full.encode()) < 512 * 1024
assert "_root_" not in full
assert '"' not in full
output = HERE / "ReaderStandalone.lean"
output.write_text(full + "\n")
data = output.read_bytes()
print({"bytes": len(data), "lines": len(full.splitlines()),
       "sha256": hashlib.sha256(data).hexdigest()})
