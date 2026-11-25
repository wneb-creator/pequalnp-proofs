from pathlib import Path
from datetime import datetime, timezone
import gzip
import hashlib
import json
import shutil

src = Path('/tmp/oec/pequalnp-pilot-62/meta2448')
repo = Path('/workspace/pequalnp-proofs/results/meta2448')
tag = 'petersen-atmost19-sensitive-v13-run1200'
normal_status_present = (src / (tag + '.status.json')).is_file()
status_path = src / (tag + ('.status.json' if normal_status_present else '.interruption-status.json'))
status = json.loads(status_path.read_text())
guard = json.loads((src / (tag + '.guard-status.json')).read_text())
assert not guard['live_group_members_after_cleanup']
outer = json.loads((src / (tag + '.detached-guardian.json')).read_text())
try:
    raw = (Path('/proc') / str(outer['guardian_pid']) / 'stat').read_text()
    fields = raw[raw.rfind(')') + 2:].split()
    if int(fields[19]) == outer['guardian_process_start_ticks']:
        assert fields[0] == 'Z', 'outer guardian is still writing its final log'
except (FileNotFoundError, ProcessLookupError):
    pass
for path in Path('/proc').iterdir():
    if not path.name.isdecimal():
        continue
    try:
        raw = (path / 'stat').read_text()
        fields = raw[raw.rfind(')') + 2:].split()
        assert int(fields[2]) != guard['owned_process_group'] or fields[0] == 'Z'
    except (FileNotFoundError, ProcessLookupError, PermissionError):
        pass


def digest(path, opener=open):
    h = hashlib.sha256()
    with opener(path, 'rb') as inp:
        for chunk in iter(lambda: inp.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


provenance = json.loads((src / (tag + '.source-provenance.json')).read_text())
assert digest(src / (tag + '.cnf')) == provenance[tag + '.cnf']['sha256']
out = repo / ('search-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ') + '-final')
out.mkdir(exist_ok=False)
files = [src / n for n in [
    'synthesize_v13.py', 'guard_synthesis_v15.py',
    'launch_detached_guard_v4.py', 'freeze_final_petersen_run.py']]
files += sorted(src.glob(tag + '.*'))
records = []
for f in files:
    original_hash = digest(f)
    original_size = f.stat().st_size
    stored_name = f.name + ('.gz' if f.suffix == '.cnf' else '')
    dest = out / stored_name
    if f.suffix == '.cnf':
        with f.open('rb') as inp, dest.open('xb') as raw:
            with gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0, compresslevel=6) as enc:
                shutil.copyfileobj(inp, enc, 1024 * 1024)
        assert digest(dest, gzip.open) == original_hash
    else:
        shutil.copyfile(f, dest)
        assert digest(dest) == original_hash
    assert digest(f) == original_hash and f.stat().st_size == original_size
    records.append({
        'original_name': f.name, 'original_path': str(f),
        'sha256': original_hash, 'bytes': original_size,
        'stored_name': stored_name,
        'compression': 'gzip' if f.suffix == '.cnf' else 'none',
        'archive_sha256': digest(dest), 'archive_bytes': dest.stat().st_size})
(out / 'ORIGINAL-FILES.json').write_text(json.dumps(records, indent=2) + '\n')
summary = {
    'model_status': status, 'normal_model_status_present': normal_status_present,
    'status_origin': status_path.name,
    'guardian_child_exit': guard['wrapper_child_exit'],
    'shared_memory_guard_stop': guard['shared_memory_guard_stop'],
    'cleanup_signals': guard['cleanup_signals'],
    'live_group_members_after_cleanup': guard['live_group_members_after_cleanup'],
    'ended_utc': guard['ended_utc'],
    'candidate_file_present': (src / (tag + '.witness.json')).is_file()}
(out / 'ACTUAL-RESULT.json').write_text(json.dumps(summary, indent=2) + '\n')
(out / 'README.md').write_text("""# Final strengthened Petersen search

The actual model or explicit interruption record and cleanup status are preserved without reinterpretation in ACTUAL-RESULT.json and the complete original logs. A missing normal model status is identified explicitly; no final solver verdict is inferred from an interruption. This is the reviewed normalized at-most19 proper-binary monotone model, with full edge/MIS separation, first-pair symmetry, independent-gate ordering, pre-target signed domination, exact shadow sensitivity, and earliest-prefix AND>=6/OR>=4 bounds. Its known20-gate control passed full1024-input and80-substitution independent replay before launch.

The detached outer guardian retained its own PID/start identity and unchanged1GiB child address-space/6.5GiB shared-memory policies. Archive creation requires either normal model status or an explicit interruption record, guardian completion, and no live members in its owned group. The stop-request record identifies lease-loss interruption if applicable.

A SAT model would still require independent candidate verification and an argument about every minimum star circuit to refute L-meta-2448. An UNSAT result is a finite-model outcome with mathematically reviewed but unformalized global-minimum normalization; it is not a Lean proof of the posted theorem. UNKNOWN establishes neither existence nor nonexistence. No full-gap conclusion follows from a timeout.

The CNF is stored once as lossless gzip, with original and compressed hashes/sizes and a verified decompression round trip. Complete stdout/stderr logs, commands, source versions, mapping, identities and actual status are preserved. No original input, proof or cache artifact was deleted.
""")
(out / 'SHA256SUMS').write_text(''.join(
    digest(f) + '  ' + f.name + '\n'
    for f in sorted(out.iterdir()) if f.name != 'SHA256SUMS'))
print(json.dumps({
    'directory': str(out), 'files': len(list(out.iterdir())),
    'bytes': sum(f.stat().st_size for f in out.iterdir()),
    'result': summary}), flush=True)
