import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("witness", type=Path)
parser.add_argument("output", type=Path)
parser.add_argument("--name", default="witness")
args = parser.parse_args()
reserved = set("abbrev axiom by class constant def deriving do else end example false for fun if import in inductive instance let match mutual namespace noncomputable opaque open partial private protected return section structure syntax theorem true universe variable where while with".split())
if (not args.name.isidentifier() or not args.name.isascii()
        or args.name in reserved or "_root_" in args.name):
    raise ValueError("The Lean definition name must be an ordinary ASCII identifier")
data = json.loads(args.witness.read_text())
n, k = data["input_count"], data["or_count"]
if type(n) is not int or type(k) is not int or n < 0 or k < 0:
    raise ValueError("Counts must be nonnegative integers")
operations = data["operand_wire_lists"]
if len(operations) != k:
    raise ValueError("Operation count mismatch")

def lean_refs(refs, bound):
    if not isinstance(refs, list):
        raise ValueError("Wire references must be lists")
    if any(type(x) is not int or not 0 <= x < bound for x in refs):
        raise ValueError("A wire reference is outside the available signals")
    return "[" + ", ".join(f"⟨{x}, by decide⟩" for x in refs) + "]"

body = lean_refs(data["output_wire_list"], n + k)
for i in reversed(range(k)):
    operands = operations[i]
    if not isinstance(operands, list) or len(operands) != 2:
        raise ValueError("Each OR operation needs exactly two operand lists")
    left, right = (lean_refs(x, n + i) for x in operands)
    body = f"(({left}, {right}),\n{body})"

text = (
    "import CanonicalCompilerDefs\n\n"
    "namespace PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler\n\n"
    f"def {args.name} : Program {n} {k} :=\n{body}\n\n"
    "end PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler\n"
)
args.output.write_text(text)
