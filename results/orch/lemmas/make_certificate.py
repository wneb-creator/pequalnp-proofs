#!/usr/bin/env python3
"""Generate a kernel-checkable circuit upper-bound certificate for pilot-84."""
import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("circuit", type=Path)
parser.add_argument("output", type=Path)
args = parser.parse_args()
base = Path(__file__).parent
data = json.loads(args.circuit.read_text())
gates = data["gates"]
out = data["output"]
assert isinstance(out, int) and out >= 0
assert isinstance(gates, list)
for op, a, b in gates:
    assert op in ("and", "or")
    assert isinstance(a, int) and a >= 0
    assert isinstance(b, int) and b >= 0

for a in range(33):
    for b in range(33):
        wires = [i == a for i in range(33)] + [i == b for i in range(33)]
        for op, i, j in gates:
            x = wires[i] if i < len(wires) else False
            y = wires[j] if j < len(wires) else False
            wires.append(x and y if op == "and" else x or y)
        value = wires[out] if out < len(wires) else False
        target = any(
            (a in (i, 11 + i) and b in ((i + 1) % 11, 22 + i))
            or (b in (i, 11 + i) and a in ((i + 1) % 11, 22 + i))
            for i in range(11)
        )
        assert value == target, (a, b)

ending = "end PEqualNP.Outside.L_meta_9502\n"
proto = base.joinpath("RowProto.lean").read_text()
assert proto.endswith(ending)
text = proto.removesuffix(ending)
row_path = base.joinpath("row-graph/RowGraph.lean")
if not row_path.exists():
    row_path = base.joinpath("RowGraph.lean")
row = row_path.read_text()
row = row.split("namespace PEqualNP.Outside.L_meta_9502\n", 1)[1]
row = row.rsplit("end PEqualNP.Outside.L_meta_9502", 1)[0]
text += row + "\ndef rawGates : List (Bool × Nat × Nat) :=\n  [\n"
text += "\n".join(
    "    (" + ("true" if op == "and" else "false")
    + ", " + str(a) + ", " + str(b) + ")"
    + ("," if i + 1 < len(gates) else "")
    for i, (op, a, b) in enumerate(gates)
)
text += "\n  ]\n\ndef circ : Circuit := ⟨rawGates.map rawGate, " + str(out) + "⟩\n\n"
text += "lemma circ_mono : Monotone2 circ := by\n  simp [Monotone2, circ, rawGates, rawGate]\n\n"
text += "lemma circ_size : circ.size ≤ " + str(len(gates)) + " := by decide\n\n"
text += "set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n"
text += "lemma row_eval : ∀ a : Fin 33,\n"
text += "    ((rawGates.foldl rowStep (rowInput a)).getD " + str(out) + " 0) =\n"
text += "      BitVec.ofNat 33 (adjRows.getD a.val 0) := by\n  decide +kernel\n\n"
text += "lemma circ_rep : Represents adjGraph circ := by\n  intro a b\n"
text += "  change (Circuit.mk (rawGates.map rawGate) " + str(out) + ").eval (oneEach a b) = _\n"
text += "  rw [row_circuit_sound, row_eval, adjRows_correct]\n\n"
text += "lemma upper_bound : RepSizeAtMost adjGraph " + str(len(gates)) + " :=\n"
text += "  ⟨circ, circ_mono, circ_size, circ_rep⟩\n\n" + ending
assert len(text.encode()) <= 512 * 1024
args.output.write_text(text)
print("Generated", len(gates), "gate certificate after exhaustive Python validation:", args.output)
