"""Preserve the checked monotone cofactor certificate, omitting signed-only tails."""

from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
SOURCE = REPO / "lean/PEqualNP/Outside/L_meta_4332.lean"
OUT = REPO / "results/orch2590/lemmas/MonoBase.lean"
NAMESPACE = "PEqualNP.Outside.L_meta_2590.Mono18"

lines = SOURCE.read_text().splitlines()
# Inclusive source line ranges, kept in source order.
ranges = ((1, 6127), (6193, 6216), (6227, 6260),
          (6295, 6302), (6311, 6709), (6855, 6859))
body = "\n\n".join("\n".join(lines[start - 1:stop]) for start, stop in ranges)
body = body.replace("PEqualNP.Outside.L_meta_4332", NAMESPACE)
bridge = (REPO / "results/orch2590/lemmas/NineMonoFloorSnippet.lean").read_text()
bridge = bridge[bridge.index("set_option maxHeartbeats 1000000 in\nlemma nineMonoFloorOfCert"):]
body += "\n\n" + bridge
body += "\ntheorem nineMonoFloor : Lower false inputs graph 16 := nineMonoFloorOfCert monoRoot\n"
body += "\nend " + NAMESPACE + "\n"
assert len(body.encode()) < 512 * 1024
assert "_root_" not in body
assert '"' not in body
OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text(body)
print({"source": str(SOURCE), "output": str(OUT), "bytes": len(body.encode()),
       "lines": len(body.splitlines()), "source_ranges": ranges})
