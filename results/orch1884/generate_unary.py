"""Assemble a test using the already checked Binary17 floor."""

from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
HERE = REPO / "results/orch1884/lemmas"
old = (REPO / "results/orch/lemmas/Binary17.lean").read_text().splitlines()
model = "\n".join(old[3987:4456]).replace("namespace Extended", "namespace UnaryModel", 1)
extension = (HERE / "UnaryExtension.lean").read_text()
test = "import Binary17\nnamespace PEqualNP.Outside.L_meta_1884.Unary17\n"
test += "open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2592.Binary17\n"
test += model + "\n\n" + extension
test += "\nend PEqualNP.Outside.L_meta_1884.Unary17\n"
(HERE / "Unary17Check.lean").write_text(test)
base = "\n".join(old).replace(
    "PEqualNP.Outside.L_meta_2592.Binary17", "PEqualNP.Outside.L_meta_1884.Unary17")
ending = "end PEqualNP.Outside.L_meta_1884.Unary17"
assert base.endswith(ending)
standalone = base[:-len(ending)]
standalone += "\nnamespace Extended\n" + extension.replace("UnaryModel", "Extended")
standalone += "\n" + ending + "\n"
assert len(standalone.encode()) < 512 * 1024
assert "_root_" not in standalone
assert '"' not in standalone
(HERE / "Unary17Standalone.lean").write_text(standalone)
print({"test_bytes": len(test.encode()), "test_lines": len(test.splitlines()),
       "standalone_bytes": len(standalone.encode()), "standalone_lines": len(standalone.splitlines())})
