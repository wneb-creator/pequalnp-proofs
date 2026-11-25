from pathlib import Path
import hashlib
import json
import resource
import shutil

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
job = Path('/tmp/oec/pequalnp-pilot-79')
repo = Path('/workspace/pequalnp-proofs')
destination = repo / 'results/orch/meta3773_sat_final'
destination.mkdir(exist_ok=True)


def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


names = [
    'meta3773_six_dense_repair_sat.py', 'meta3773_six_dense_verify_encoding.py',
    'meta3773_six_dense_verify_padding.py', 'meta3773_six_dense_verify_physical.py',
    'meta3773_dense_phase_run.py', 'meta3773-six-dense-patch-data.json',
    'meta3773-six-dense-matched-over-seed.json', 'meta3773-six-dense-known29.json',
    'meta3773-six-dense-known29-verification.log',
    'meta3773-six-dense-known29-physical-verification.log',
    'meta3773-six-dense-padding-verification.log',
    'meta3773_dense_seed_verify.py', 'meta3773-dense-seed-physical-verification.log',
]
for prefix, numbers in [
    ('meta3773-six-sat-r', [1]),
    ('meta3773-six-dense-repair-r', [0, 990, 992]),
    ('meta3773-six-dense-phase-r', [0, 990, 991]),
]:
    for number in numbers:
        for suffix in ['-metadata.json', '-status.json', '-source.py', '-run.log',
                       '-solver.log', '-candidate.json']:
            name = prefix + str(number) + suffix
            if (job / name).is_file():
                names.append(name)
records = []
for name in sorted(set(names)):
    source = job / name
    digest = sha(source)
    target = destination / name
    shutil.copyfile(source, target)
    assert sha(source) == sha(target) == digest
    records.append({'path': str(target.relative_to(repo)), 'sha256': digest,
        'bytes': target.stat().st_size})

cnf_bindings = []
for name in ['meta3773-six-sat-r1.cnf', 'meta3773-six-dense-repair-r0.cnf',
             'meta3773-six-dense-repair-r990.cnf', 'meta3773-six-dense-phase-r990.cnf',
             'meta3773-six-dense-phase-r0.cnf']:
    source = job / name
    if source.is_file():
        cnf_bindings.append({'scratch_file': name, 'sha256': sha(source),
            'bytes': source.stat().st_size,
            'preservation': 'deterministic source/data regeneration; not copied'})
(destination / 'CNF_BINDINGS.json').write_text(json.dumps(cnf_bindings, indent=2) + '\n')

readme = '''# Final restricted SAT attempts

No 63-gate witness or global refutation is claimed. These are incomplete
diagnostics, not new Lean proofs.

The original six-point round 1 fixes all seven outside OR trees to variant 0
and exactly seven AND gates. It returned unknown after 110.02 seconds. Its
scope is only that tree configuration.

The denser six-point model uses 17 raw inputs, 13 compatible outside OR
signals, 76 extremal rows, and a 28-gate local budget. Its 25-gate matched
overapproximation accepts all 24 positive edges and incorrectly accepts 26
maximal negative cuts. Padding by an absorbed valid edge and two OR gates,
then colex ordering, was checked to preserve its function on all 131,072
physical assignments. The bounded repair permits at most eight gate changes
and leaves all compatible outside-tree choices free. It retains the reviewed
active-gate, positive-gate, bad-AND and helper-count restrictions.

The dense 29-gate positive control passes every one of its 298,062 original
and polarity-renamed clauses. Its decoded function passes exhaustive physical
verification. That control has 29 local gates and is not a 28-gate witness.
The warm wrapper only renames variable polarities and always checks the
original clauses after inverse model decoding, then all 131,072 physical
inputs. Production statuses and full solver logs give each actual outcome.

This small delta preserves complete sources, exact inputs, metadata and all
stdout/stderr. The large final DIMACS files are not duplicated: CNF_BINDINGS
records their exact hashes and lengths. They regenerate deterministically
using the frozen source snapshots and exact input files. The old six-point
input is already in ../meta3773_sat_six; all dense inputs are in this folder.
With files restored under /tmp/oec/pequalnp-pilot-79, the generation commands are:

    python /tmp/oec/pequalnp-pilot-79/meta3773-six-sat-r1-source.py --round 1 --gates 28 --and-count 7 --fixed-trees --generate-only
    python /tmp/oec/pequalnp-pilot-79/meta3773-six-dense-repair-r0-source.py --round 0 --near-seed /tmp/oec/pequalnp-pilot-79/meta3773-six-dense-matched-over-seed.json --changes 8 --generate-only
    python /tmp/oec/pequalnp-pilot-79/meta3773_dense_phase_run.py --stem meta3773-six-dense-repair-r0 --run 0 --generate-only

All invocations run from the repository or named job directory. The wrappers
bind source/data/CNF hashes and apply ordinary child environments, disabled
core dumps, and CPU/address-space/wall limits. Any actual witness still needs
assembly and checking on the original 26-input instance and prescribed head.
'''
(destination / 'README.md').write_text(readme)
for source in [destination / 'README.md', destination / 'CNF_BINDINGS.json', Path(__file__)]:
    target = destination / source.name
    if source != target:
        shutil.copyfile(source, target)
    records.append({'path': str(target.relative_to(repo)), 'sha256': sha(target),
        'bytes': target.stat().st_size})
manifest = {'classification': 'final incomplete circuit searches; no new proof',
    'files': sorted(records, key=lambda row: row['path']),
    'total_bytes': sum(row['bytes'] for row in records)}
(job / 'three-plane-meta3773-final-archive-manifest.json').write_text(
    json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'files': len(records), 'bytes': manifest['total_bytes']}))
