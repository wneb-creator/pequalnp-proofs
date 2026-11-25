"""Actual subprocess tests with fake phases only; no live command bundle read."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
LAUNCHER = HERE / "sequence_launcher.py"
EXPECTED = "034a2628a985a62275bee37e4265a0415d6087ff7f8df5b4e5e7dec72e26b43d"
assert hashlib.sha256(LAUNCHER.read_bytes()).hexdigest() == EXPECTED
SEQUENCE = HERE.parent.parent / "core-phase/storage_sequence.py"
root = Path(tempfile.mkdtemp(prefix="launcher-fixture-", dir=HERE))
child = root / "fake_phase.py"
child.write_text("""import json,sys
from pathlib import Path
log=Path(sys.argv[1]); label=sys.argv[2]; status=int(sys.argv[3]); action=sys.argv[4]
with log.open('a') as stream:
 stream.write(json.dumps({'label':label,'action':action,'status':status})+'\\n')
sys.exit(status)
""")
other_input = root / "fake-config.txt"
other_input.write_text("unchanged fixture configuration\n")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def case(name, action, base_status=0, core_status=0, mutate=None):
    folder = root / name
    folder.mkdir()
    log = folder / "phases.jsonl"
    commands = {"sequence_source": str(SEQUENCE),
                "required_files": [{"path": str(p), "sha256": digest(p)}
                                   for p in (SEQUENCE, child, other_input)],
                "base_command": [sys.executable, str(child), str(log), "base", str(base_status)],
                "core_command": [sys.executable, str(child), str(log), "core", str(core_status)]}
    command_path = folder / "commands.json"
    command_path.write_text(json.dumps(commands))
    expected_hash = digest(command_path)
    old_input = other_input.read_bytes()
    if mutate == "input":
        other_input.write_text("changed fixture configuration\n")
    elif mutate == "commands":
        commands["base_command"][-1] = "87"
        command_path.write_text(json.dumps(commands))
    elif mutate == "unpinned-sequence":
        commands["required_files"] = commands["required_files"][1:]
        command_path.write_text(json.dumps(commands))
        expected_hash = digest(command_path)
    try:
        result = subprocess.run([sys.executable, str(LAUNCHER),
                                 "--commands", str(command_path),
                                 "--commands-sha256", expected_hash, action],
                                capture_output=True, text=True, timeout=10)
        (folder / "launcher.stdout").write_text(result.stdout)
        (folder / "launcher.stderr").write_text(result.stderr)
        rows = [json.loads(line) for line in log.read_text().splitlines()] if log.exists() else []
        return result, rows
    finally:
        other_input.write_bytes(old_input)


r, rows = case("enter-order", "enter")
assert r.returncode == 0 and [(x["label"], x["action"]) for x in rows] == [("base", "enter"), ("core", "enter")]
print("PASS actual launcher enter runs base then core")
r, rows = case("restore-core-failure", "restore", core_status=9)
assert r.returncode == 9 and [(x["label"], x["action"]) for x in rows] == [("core", "restore"), ("base", "restore")]
print("PASS core restoration failure still runs base and preserves failure status")
r, rows = case("enter-base-failure", "enter", base_status=7)
assert r.returncode == 7 and [x["label"] for x in rows] == ["base"]
print("PASS failed base entry prevents later core entry")
r, rows = case("modified-required-input", "enter", mutate="input")
assert r.returncode != 0 and not rows and "reviewed phase input changed" in r.stderr
print("PASS modified required file is refused before any phase")
r, rows = case("modified-command-bundle", "enter", mutate="commands")
assert r.returncode != 0 and not rows and "reviewed phase commands changed" in r.stderr
print("PASS modified command bundle is refused before any phase")
r, rows = case("unpinned-sequence", "restore", mutate="unpinned-sequence")
assert r.returncode != 0 and not rows and "sequence source is not pinned" in r.stderr
print("PASS unpinned sequence source is refused before any phase")
assert digest(LAUNCHER) == EXPECTED
print(json.dumps({"status": "PASS", "cases": 6, "source_sha256": EXPECTED,
                  "fixture_directory": str(root), "production_invocations": 0}))
