#!/usr/bin/env python3
"""Inline the strengthened Petersen seventeen-binary-gate partial."""

from pathlib import Path
import hashlib
import json
import re


REPO = Path(__file__).resolve().parents[2]
PARTIAL = "PEqualNP.Outside.L_meta_2592_binary17"
AUX = PARTIAL + "_aux"
SOURCES = [
    "lean/PEqualNP/Outside/L_meta_7493.lean",
    "lean/PEqualNP/Outside/L_meta_5236.lean",
    "results/orch/lemmas/Restriction.lean",
    "results/orch/lemmas/PairCode.lean",
    "results/orch/lemmas/FirstMerge.lean",
    "results/orch/lemmas/CutCost.lean",
    "results/orch/lemmas/FirstOrigin.lean",
    "results/orch/lemmas/Compression.lean",
    "results/orch/lemmas/FirstBinary.lean",
    "results/orch/lemmas/CutFloor.lean",
    "results/orch/lemmas/BinarySixteen.lean",
    "results/orch/lemmas/DeletionFifteen.lean",
    "results/orch/lemmas/BinarySeventeen.lean",
    "results/orch/lemmas/SeventeenCorollaries.lean",
]
OUTPUT = REPO / "results/orch/lemmas/BinarySeventeenStandalone.lean"
SCRATCH = Path("/tmp/oec/pequalnp-pilot-101")


def rename_namespaces(source: str) -> str:
    replacements = {
        "PEqualNP.Outside.L_meta_2592_aux": AUX,
        "PEqualNP.Outside.L_meta_7493": AUX + ".DeletionBase",
        "PEqualNP.Outside.L_meta_5236": AUX + ".DeletionCertificate",
        "PEqualNP.Outside.L_meta_2592_restrict": AUX + ".Elimination",
    }
    for old, new in replacements.items():
        source = source.replace(old, new)
    return source


def component(relative: str) -> tuple[str, dict]:
    raw = (REPO / relative).read_text(encoding="utf-8")
    source = raw
    if relative == SOURCES[0]:
        boundary = "namespace CircuitProof.RunAsm\n"
        assert source.count(boundary) == 1
        source = source.split(boundary)[0].rstrip() + "\n\nend PEqualNP.Outside.L_meta_7493\n"
    if relative == "lean/PEqualNP/Outside/L_meta_5236.lean":
        boundary = "namespace Extended\n"
        assert source.count(boundary) == 1
        source = source.split(boundary)[0].rstrip() + "\n\nend PEqualNP.Outside.L_meta_5236\n"
    if relative == "results/orch/lemmas/CutFloor.lean":
        boundary = "set_option maxHeartbeats 2000000 in\nlemma cut_floor"
        assert source.count(boundary) == 1
        source = source.split(boundary)[0].rstrip() + "\n\nend PEqualNP.Outside.L_meta_2592_aux.CutFloor\n"
    if relative == "results/orch/lemmas/BinarySixteen.lean":
        boundary = "theorem binary_floor "
        assert source.count(boundary) == 1
        source = source.split(boundary)[0].rstrip() + "\n\nend PEqualNP.Outside.L_meta_2592_aux.BinarySixteen\n"
    if relative == "results/orch/lemmas/Restriction.lean":
        boundary = "namespace CircuitProof\n\nopen PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity\n\ndef originStep"
        assert source.count(boundary) == 1
        position = source.index(boundary)
        shared = source[:position].replace(
            "PEqualNP.Outside.L_meta_2592_restrict", "PEqualNP.Outside.L_meta_7493"
        )
        assert (REPO / SOURCES[0]).read_text(encoding="utf-8").startswith(shared)
        source = "namespace PEqualNP.Outside.L_meta_2592_restrict\n\n" + source[position:]
        source = source.replace(
            "namespace CircuitProof\n",
            "namespace CircuitProof\n\nopen PEqualNP.Outside.L_meta_7493.CircuitProof\n",
            1,
        )
    if relative in {"results/orch/lemmas/CutFloor.lean", "results/orch/lemmas/DeletionFifteen.lean"}:
        opening = "open PEqualNP.Outside.L_meta_2592_restrict.CircuitProof\n"
        assert source.count(opening) == 1
        source = source.replace(
            opening, "open PEqualNP.Outside.L_meta_7493.CircuitProof\n" + opening
        )
    source = "\n".join(
        line for line in source.splitlines()
        if not re.fullmatch(r"import [A-Za-z0-9_.]+", line)
    ).strip()
    source = rename_namespaces(source)
    return source, {
        "source": relative,
        "sha256": hashlib.sha256(raw.encode()).hexdigest(),
        "bytes": len(raw.encode()),
    }


TARGET = """fun x : Fin 10 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5"""
STATEMENT = f"""∀ C : PEqualNP.CircuitLowerBounds.Circuit,
  PEqualNP.MetaComplexity.FanInTwo C →
  (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = ({TARGET}) x) →
  17 ≤ List.countP (fun g : PEqualNP.CircuitLowerBounds.Gate =>
    PEqualNP.CircuitLowerBounds.GateOp.rec true true false (fun _ => true) true g.op) C.gates"""
WRAPPER = f"""theorem {PARTIAL} : {STATEMENT} := by
  intro C fan correct
  change ∀ x : Fin 10 → Bool,
    C.eval (List.ofFn x) = {AUX}.Restriction.petersen x at correct
  have lower := {AUX}.BinarySeventeen.binary_floor C fan correct
  have count_eq : {AUX}.DeletionBase.CircuitProof.nonNotCount C.gates =
      List.countP (fun g : PEqualNP.CircuitLowerBounds.Gate =>
        PEqualNP.CircuitLowerBounds.GateOp.rec true true false (fun _ => true) true g.op)
        C.gates := by
    unfold {AUX}.DeletionBase.CircuitProof.nonNotCount
    congr 1
    funext g
    cases g.op <;> rfl
  rw [← count_eq]
  exact lower
"""


def main() -> None:
    bodies, manifest = [], []
    for relative in SOURCES:
        body, record = component(relative)
        bodies.append(body)
        manifest.append(record)
    source = "import Mathlib\nimport PEqualNP.Defs\n\n" + "\n\n".join(bodies)
    source += "\n\n" + WRAPPER
    assert len(source.encode("utf-8")) <= 512 * 1024
    for forbidden in ["_root_", '"', "sorry", "native_decide", "bv_decide", "polyrith"]:
        assert forbidden not in source, forbidden
    assert not re.search(r"\bimport\b", "\n".join(source.splitlines()[2:]))
    assert not re.search(r"^\s*#", source, re.MULTILINE)
    OUTPUT.write_text(source, encoding="utf-8")
    (SCRATCH / "binary-seventeen-statement.txt").write_text(STATEMENT + "\n", encoding="utf-8")
    (SCRATCH / "binary-seventeen-inline-manifest.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
    )
    print(f"Wrote {OUTPUT}: {len(source.splitlines())} lines, {len(source.encode())} bytes")
    print(f"Partial theorem: {PARTIAL}")
    print(f"SHA256: {hashlib.sha256(source.encode()).hexdigest()}")


if __name__ == "__main__":
    main()
