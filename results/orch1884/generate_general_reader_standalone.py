"""Assemble both cofactor modes and the general effective-reader inequality."""

from pathlib import Path
import hashlib
import re

REPO = Path(__file__).resolve().parents[2]
HERE = REPO / "results/orch1884/lemmas"
base = (HERE / "GeneralReaderBase.lean").read_text()
compiler = (HERE / "NineGeneralFloor.lean").read_text()
start = compiler.index("lemma reach_to_signed")
finish = compiler.index("lemma count_partition", start)
compiler = compiler[:start] + compiler[finish:]
compiler = compiler.replace("circuit_floor signed_floor", "circuit_floor nineSignedFloor")
parts = [base, compiler, (HERE / "GeneralReaderBound.lean").read_text(),
         (HERE / "GeneralConcreteReaderBound.lean").read_text()]
full = parts[0]
for part in parts[1:]:
    full += "\n\n" + "\n".join(line for line in part.splitlines()
                                   if not line.startswith("import "))
full = full.replace("PEqualNP.Outside.L_meta_2590.Mono18",
                    "PEqualNP.Outside.L_meta_1884.GeneralReaderCertificate")
renames = {
    "panelDispatchBlock": "pdb",
    "graphGoal": "ggl",
    "before_sound": "bef",
    "extendKnown": "extK",
    "boundsBefore": "bpre",
    "mixedEmpty": "memp",
    "strong_full": "sfull",
    "cellsBlock": "cblk",
    "contextWire": "cwire",
    "isMaskedConstant": "isMC",
}
before = full
for old, new in renames.items():
    assert not re.search(r"\b" + re.escape(new) + r"\b", full), new
    assert re.search(r"\b(?:def|theorem|lemma)\s+" + re.escape(old) + r"\b", full), old
    full = re.sub(r"\b" + re.escape(old) + r"\b", new, full)
roundtrip = full
for old, new in renames.items():
    roundtrip = re.sub(r"\b" + re.escape(new) + r"\b", old, roundtrip)
assert roundtrip == before
assert len(full.encode()) < 512 * 1024
assert "_root_" not in full
assert '"' not in full
assert not any(line.startswith("set_option ") and not line.endswith(" in")
               for line in full.splitlines())
output = HERE / "GeneralReaderStandalone.lean"
output.write_text(full + "\n")
data = output.read_bytes()
print({"bytes": len(data), "lines": len(full.splitlines()),
       "renaming_bytes_saved": len(before.encode()) - len(full.encode()),
       "sha256": hashlib.sha256(data).hexdigest()})
