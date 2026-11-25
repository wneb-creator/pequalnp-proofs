"""Retain both checked nine-input certificates and remove unused circuit wrappers."""

from pathlib import Path
import hashlib

REPO = Path(__file__).resolve().parents[2]
SOURCE = REPO / "lean/PEqualNP/Outside/L_meta_4332.lean"
DROP = [(123, 133), (146, 147), (225, 233), (237, 272), (307, 367), (760, 765),
        (2341, 2352), (6128, 6192), (6865, 6977)]
lines = SOURCE.read_text().splitlines()
retained = [line for index, line in enumerate(lines, 1)
            if not any(lo <= index <= hi for lo, hi in DROP)]
text = "\n".join(retained) + "\n"
text = text.replace("PEqualNP.Outside.L_meta_4332",
                    "PEqualNP.Outside.L_meta_1884.GeneralReaderCertificate")
text += """
lemma nineFloorOfCert {u : Bool} {n : Nat}
    (cert : Impossible u graph n inputs.toFinset) : Lower u inputs graph (n + 1) := by
  apply lower_impossible graph_proper (by decide +kernel) (by decide +kernel) _ cert
  intro a ha
  have idx (b : Sig) (hb : b ∈ inputs) : ∃ i : Fin 9, inputs.getD i.val zero = b := by
    rw [← input_list] at hb
    exact List.mem_ofFn.mp hb
  obtain ⟨i, rfl⟩ := idx a ha
  refine ⟨absentRow670 i, presentRow670 i, requiredInputs.1 i, ?_⟩
  intro v hv hne
  obtain ⟨j, rfl⟩ := idx v hv
  apply requiredInputs.2 i j
  rintro rfl
  exact hne rfl

theorem nineMonoFloor : Lower false inputs graph 16 := nineFloorOfCert monoRoot
theorem nineSignedFloor : Lower true inputs graph 15 := nineFloorOfCert signedRoot

end PEqualNP.Outside.L_meta_1884.GeneralReaderCertificate
"""
assert "_root_" not in text
assert '"' not in text
output = REPO / "results/orch1884/lemmas/GeneralReaderBase.lean"
output.write_text(text)
data = output.read_bytes()
print({"bytes": len(data), "lines": len(text.splitlines()),
       "sha256": hashlib.sha256(data).hexdigest()})
