import argparse
import ast
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("witness", type=Path)
parser.add_argument("masks", type=Path)
parser.add_argument("output", type=Path)
parser.add_argument("--statement", type=Path, default=Path("/tmp/oec/pequalnp-pilot-62/statement.txt"))
parser.add_argument("--sample-data", type=Path, default=Path("/workspace/pequalnp-proofs/results/orch/checked/canonical-sample-data.lean"))
args = parser.parse_args()
witness = json.loads(args.witness.read_text())
certificate = json.loads(args.masks.read_text())
n, k = witness["input_count"], witness["or_count"]
if type(n) is not int or n != 26 or type(k) is not int or not 0 <= k < 51:
    raise ValueError("A candidate needs26 original inputs and fewer than51 OR operations")
operations = witness["operand_wire_lists"]
if not isinstance(operations, list) or len(operations) != k:
    raise ValueError("OR operation count mismatch")

sample_source = args.sample_data.read_text()
start = sample_source.index("([") + 1
end = sample_source.index("] : List Nat", start) + 1
fixed_inputs = ast.literal_eval(sample_source[start:end])
if certificate["sample_count"] != 520 or certificate["input_masks"] != fixed_inputs:
    raise ValueError("The certificate must use the exact checked520-sample input masks")
expected = certificate["or_masks"]
if not isinstance(expected, list) or len(expected) != k:
    raise ValueError("Intermediate-mask count mismatch")
if any(type(mask) is not int or mask < 0 for mask in expected):
    raise ValueError("Intermediate masks must be nonnegative integers")

def lean_refs(refs, bound):
    if not isinstance(refs, list) or any(type(r) is not int or not 0 <= r < bound for r in refs):
        raise ValueError("Invalid or forward signal reference")
    return "[" + ", ".join(f"⟨{r}, by decide⟩" for r in refs) + "]"

values = list(fixed_inputs)
truth = (1 << 520) - 1
rendered = []
for i, pair in enumerate(operations):
    if not isinstance(pair, list) or len(pair) != 2:
        raise ValueError("Each OR needs exactly two conjunction lists")
    rendered.append(tuple(lean_refs(refs, 26 + i) for refs in pair))
    operands = []
    for refs in pair:
        value = truth
        for r in refs:
            value &= values[r]
        operands.append(value)
    value = operands[0] | operands[1]
    if value != expected[i]:
        raise ValueError("An intermediate OR mask disagrees with direct replay")
    values.append(value)
body = lean_refs(witness["output_wire_list"], 26 + k)
result = truth
for r in witness["output_wire_list"]:
    result &= values[r]
if result != (1 << 52) - 1 or certificate["output_mask"] != result:
    raise ValueError("The candidate does not accept all52 flags and reject all468 generic rows")
for left, right in reversed(rendered):
    body = f"(({left}, {right}),\n{body})"

statement = args.statement.read_text().strip()
source = """import CanonicalRefutationWrapper
import GeometryCompleteness
import GeometryRowsAgreement

namespace PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

"""
source += f"def candidate : Program 26 {k} :=\n{body}\n\n"
source += "def candidateCertificates : List Nat :=\n  [" + ", ".join(map(str, expected)) + "]\n\n"
source += "set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n"
source += f"lemma candidate_check : checkMasks {k} candidate sampleTruthMask sampleInputMasks\n    candidateCertificates positiveResultMask = true := by\n  decide +kernel\n\n"
source += "set_option maxRecDepth 10000 in\nset_option maxHeartbeats 3000000 in\n"
source += "lemma candidate_refutation : ¬ (" + statement + ") := by\n"
source += f"  exact refutes_posted {k} candidate candidateCertificates (by decide) candidate_check\n    GeometryComplete.admissible_complete AllRows.row_eq\n\n"
source += "end PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler\n"
source += "\nset_option maxRecDepth 10000 in\nset_option maxHeartbeats 3000000 in\n"
source += "theorem PEqualNP.Outside.L_meta_1896 : ¬ (" + statement + ") :=\n"
source += "  PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler.candidate_refutation\n"
args.output.write_text(source)
print(json.dumps({"or_count": k, "samples": 520, "lean_status": "prepared_not_checked", "output": str(args.output)}))
