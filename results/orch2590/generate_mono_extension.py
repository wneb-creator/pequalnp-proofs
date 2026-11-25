"""Build the small extension test and the eventual single-file artifact."""

from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
NAMESPACE = "PEqualNP.Outside.L_meta_2590.Mono18"
HERE = REPO / "results/orch2590/lemmas"
old = (REPO / "results/orch/lemmas/Binary17.lean").read_text().splitlines()
extended = "\n".join(old[3987:4456])
geometry = "\n".join(old[4543:4644])
geometry = geometry.replace("namespace Geometry\n", """namespace Geometry

lemma base_bit_zero (i) : bit i zero = false := by simp [bit, zero]
lemma base_bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d = 0 then bit i a && bit i b else if d = 1 then bit i a || bit i b else
      if d = 2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
""", 1)
geometry = geometry.replace("Extended.bit_bin, bit_bin]", "Extended.bit_bin, base_bit_bin]")
geometry = geometry.replace("[bit_bin, bit_zero]", "[base_bit_bin, base_bit_zero]")
new = (HERE / "MonoExtension.lean").read_text()
prefix, suffix = new.split("end Extended", 1)
extension = extended + "\n\n" + prefix + "end Extended\n\n" + geometry + "\n" + suffix
test = "import MonoBase\nnamespace " + NAMESPACE
test += "\nopen PEqualNP.CircuitLowerBounds\n" + extension
test += "\nend " + NAMESPACE + "\n"
(HERE / "MonoExtensionCheck.lean").write_text(test)
base = (HERE / "MonoBase.lean").read_text()
ending = "end " + NAMESPACE + "\n"
assert base.endswith(ending)
full = base[:-len(ending)] + extension + "\n" + ending
assert len(full.encode()) < 512 * 1024
assert "_root_" not in full
assert '"' not in full
(HERE / "Mono18.lean").write_text(full)
print({"test_bytes": len(test.encode()), "full_bytes": len(full.encode()),
       "full_lines": len(full.splitlines())})
