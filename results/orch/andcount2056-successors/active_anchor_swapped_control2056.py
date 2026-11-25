from pathlib import Path
import hashlib
import importlib.util
import json
import subprocess

root = Path(__file__).parent
stem = root / "active-anchor-control13-free1"
prefix = root / "active-anchor-control13-forced-swap"
mapping = json.loads(stem.with_suffix(".mapping.json").read_text())
flipped = set(mapping["flipped_variables"])
original_extra = -mapping["left"][12][12]
renamed_extra = -original_extra if abs(original_extra) in flipped else original_extra
with stem.with_suffix(".cnf").open() as source, prefix.with_suffix(".cnf").open("w") as target:
    header = source.readline().split()
    assert header[:2] == ["p", "cnf"]
    variables, clauses = map(int, header[2:])
    target.write(f"p cnf {variables} {clauses + 1}\n")
    for line in source:
        target.write(line)
    target.write(f"{renamed_extra} 0\n")
mapping["control_extra_original_literal"] = original_extra
prefix.with_suffix(".mapping.json").write_text(json.dumps(mapping, indent=2) + "\n")
solver = "/tmp/oec/pequalnp-pilot-121/toolchain/lean-4.36.0-linux/bin/cadical"
with prefix.with_suffix(".stdout").open("w") as out, prefix.with_suffix(".stderr").open("w") as err:
    result = subprocess.run([solver, "--phase=false", "-t", "10", "-w",
                             str(prefix.with_suffix(".sol")), str(prefix.with_suffix(".cnf"))],
                            stdout=out, stderr=err)
assert result.returncode == 10
assignment = {}
for line in prefix.with_suffix(".sol").read_text().splitlines():
    if line.startswith("v "):
        for literal in map(int, line[2:].split()):
            if literal:
                assignment[abs(literal)] = literal > 0
assert set(assignment) == set(range(1, variables + 1))
verified = 0
with prefix.with_suffix(".cnf").open() as stream:
    next(stream)
    for line in stream:
        literals = list(map(int, line.split()))
        assert literals[-1] == 0
        assert any(assignment[abs(x)] == (x > 0) for x in literals[:-1])
        verified += 1
assert verified == clauses + 1
original = {i: not value if i in flipped else value for i, value in assignment.items()}
assert original[abs(original_extra)] == (original_extra > 0)
model = {"ands": [{key: [i for i, variable in enumerate(mapping[key][j]) if original[variable]]
                    for key in ("left", "right")} for j in range(13)],
         "output": [j for j, variable in enumerate(mapping["output"]) if original[variable]]}
spec = importlib.util.spec_from_file_location("base", root / "andcount2056.py")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
edges, rows = base.geometry()
warm = base.star_model(13, edges)
assert model["ands"][:12] == warm["ands"][:12]
assert model["ands"][12] != warm["ands"][12]
assert base.evaluate(model, rows)[1] == (1 << 52) - 1
assert all(original[v] for v in mapping["active"])
circuit = base.materialize(model)
assert base.ordinary_eval(circuit, rows) == (1 << 52) - 1
prefix.with_suffix(".and-model.json").write_text(json.dumps(model, indent=2) + "\n")
prefix.with_suffix(".ordinary.json").write_text(json.dumps(circuit, indent=2) + "\n")
prefix.with_suffix(".ordinary.txt").write_text("".join(f"{op} {a} {b}\n" for op, a, b in circuit["gates"]))
with prefix.with_suffix(".exhaustive.stdout").open("w") as out, prefix.with_suffix(".exhaustive.stderr").open("w") as err:
    full = subprocess.run(["/tmp/oec/pequalnp-pilot-121/window2056-sat/verify_plane2056",
                           str(prefix.with_suffix(".ordinary.txt"))], stdout=out, stderr=err)
assert full.returncode == 0
report = {"status": "SAT; all clauses and all67108864 assignments passed",
          "variables": variables, "clauses_verified": verified, "last_record_changed": True,
          "ordinary_size": circuit["size"], "original_extra_literal": original_extra,
          "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
prefix.with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report), flush=True)
