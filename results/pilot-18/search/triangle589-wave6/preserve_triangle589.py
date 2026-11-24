"""Portable preservation of both triangle packs and bounded algebra; no engines run."""
from pathlib import Path
import json,hashlib,tarfile,io,gzip,datetime
R=Path('/tmp/oec/pequalnp-pilot-18');H=R/'orch/S05'
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
    payload={};origins={}
    def add(name,b,origin):
        assert not b.startswith(b'\x7fELF');b.decode('utf-8');assert name not in payload
        payload[name]=b;origins[name]=origin
    chosen=[]
    for p in H.iterdir():
        if ('triangle589' in p.name or 'best3' in p.name or 'guarded-component' in p.name) and not p.name.startswith('triangle589-preservation'):
            if p.is_dir():chosen.extend(q for q in p.rglob('*') if q.is_file() and '__pycache__' not in q.parts)
            else:chosen.append(p)
    for name in ['complete_positive_context.py','enumerate_guarded_component.py','enumerate_shared_guarded_component.py','verify_triangle589_archive.py']:
        chosen.append(H/name)
    for p in sorted(set(chosen)):
        assert p.is_file() and not p.is_symlink();add('scratch/'+str(p.relative_to(R)),p.read_bytes(),str(p))
    report=Path('/workspace/pequalnp-proofs/results/orch/lemmas/S05-algebraic-construction.md')
    add('reports/S05-algebraic-construction.md',report.read_bytes(),str(report)+' historical snapshot')
    # Flatten the already independently reviewed binary-free engine archive unchanged.
    engine=H/'direct21-preservation-v1.tar.gz'
    assert sha(engine.read_bytes())=='70858a65855a12f1345980afbfd2c490bec7963fcf3c1c3aa58847108b441323'
    with tarfile.open(engine,'r:gz') as tar:
        for member in tar.getmembers():
            assert member.isfile() and not member.name.startswith('/') and '..' not in Path(member.name).parts
            add('reviewed-engine/'+member.name,tar.extractfile(member).read(),str(engine)+'!'+member.name)
    add('README.md',b'''# Triangle589 and improved best3 research preservation

These are inexact 21-gate search seeds, not witnesses for the posted theorem.
Initial seed: F OR x2(x0 OR x7)(x1 OR x4), 0 full FN / 10 full FP / 6 boundary FP.
Best3 seed: F OR x2*x4*(x0 OR x7), 0 full FN / 5 full FP / 3 boundary FP.
Both contain only AND/OR operations and 21 live gates. Original sources, both
packs (16 and 8 schedules), complete self-test logs, main scalar reviews, all
bounded triangle-context sources/results/logs and supporting algebra are retained.
No context enumeration found an exact <=21 circuit. These local failures are not
a global lower bound or a shard refutation. No new Lean theorem is claimed.

The reviewed-engine/ tree is the exact flattened contents of the independently
reviewed direct21-preservation-v1 archive SHA256
70858a65855a12f1345980afbfd2c490bec7963fcf3c1c3aa58847108b441323.
It has engine and parent source, derivation, compiler/build provenance, complete
finite controls, unchanged wrapper/raw-validator sources, and review. The compiled
engine is deliberately absent; its observed binary hash remains in build-result.json.
Build recipe: g++ -std=c++17 -O3 -Wall -Wextra -Wpedantic SOURCE -o OUTPUT.
Do not launch a production search from this archive without main's admission.
Any candidate still requires the unchanged independent raw validator and Lean.

The original scripts and metadata retain historical absolute scratch paths. Their
archive mapping is scratch/<path relative to /tmp/oec/pequalnp-pilot-18>. They are
verbatim provenance, not instructions to overwrite those locations. Pack semantics
and all payload hashes can be checked anywhere, without compiling or launching:

python3 scratch/orch/S05/verify_triangle589_archive.py ARCHIVE.tar.gz --report REPORT.json

This portable verifier reads members without extraction, checks their exact hashes,
all 49152 packed outputs, all 1032192 remapped original intermediate values, FNV
metadata, source functions and gate-index structure. It never executes an engine.
The two generators are included; reproducing them in a fresh copied root requires
relocating their hardcoded ROOT/R/H paths. Generated pack bytes are deterministic;
metadata source paths and preparer hashes record the original generation location.

Completed production-wave logs are separately preserved by main; this archive
contains immutable source snapshots and finite controls, and does not read active
worker output directories. The proposed broader six-gate core-prefix enumeration
has NOT been run or claimed. Free-E results are formula and one-shared-intermediate
families only. Main alone handles review, copying into repository and publication.
''','generated preservation README')
    manifest=dict(status='RESEARCH_PRESERVATION_ONLY_NO_WITNESS',created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),engine_archive_sha256=sha(engine.read_bytes()),compiled_binaries_included=False,files=[dict(member=name,sha256=sha(b),bytes=len(b),origin=origins[name]) for name,b in sorted(payload.items())])
    mb=(json.dumps(manifest,indent=2)+'\n').encode();payload['manifest.json']=mb
    archive=H/'triangle589-preservation-v1.tar.gz'
    with archive.open('xb') as raw,gzip.GzipFile(fileobj=raw,mode='wb',mtime=0) as gz,tarfile.open(fileobj=gz,mode='w') as tar:
        for name,b in sorted(payload.items()):
            info=tarfile.TarInfo(name);info.size=len(b);info.mode=0o644;info.mtime=0;tar.addfile(info,io.BytesIO(b))
    (H/'triangle589-preservation-manifest.json').write_bytes(mb)
    print(json.dumps(dict(archive=str(archive),sha256=sha(archive.read_bytes()),bytes=archive.stat().st_size,members=len(payload),manifest_sha256=sha(mb))))
if __name__=='__main__':main()
