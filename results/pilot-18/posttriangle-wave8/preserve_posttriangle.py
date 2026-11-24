"""Freeze finished S05 candidate/math work; no binaries or active outputs."""
from pathlib import Path
import tarfile,io,json,hashlib,gzip,datetime,subprocess
H=Path('/tmp/oec/pequalnp-pilot-18/orch/S05')
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
    payload={};origins={}
    def add(path,name=None):
        path=Path(path);name=name or 'S05/'+str(path.relative_to(H));b=path.read_bytes();assert not b.startswith(b'\x7fELF')
        if name in payload:assert payload[name]==b
        payload[name]=b;origins[name]=str(path)
    handoffs=['candidate134227-repair-handoff.json','candidate134227-fanout2-handoff.json','candidate134227-multiport-handoff.json','allnegative-best4-pack-handoff.json','allnegative-best4-repair-handoff.json','allnegative-best4-rotated-pack-handoff.json']
    for name in handoffs:
        p=H/name;add(p);d=json.loads(p.read_bytes())
        for e in d['artifacts']:
            q=Path(e['path']);assert q.is_relative_to(H) and sha(q.read_bytes())==e['sha256'];add(q)
    for pattern in ['*free*E*','free_E*','freeE*','free-E*']:
        for p in H.glob(pattern):
            if p.is_file():add(p)
    for name in ['triangle589_best3_internal_context.py','prepare_triangle589_best3_pack.py','candidate134227_fanout2.py','candidate134227_multiport.py','control_allnegative_best4_pack.py','verify_posttriangle_archive.py','preserve_posttriangle.py']:
        add(H/name)
    add(Path('/workspace/pequalnp-proofs/results/orch/lemmas/S05-algebraic-construction.md'),'historical-S05-report.md')
    archive=H.parent/'S08/all-negative-engine-preservation-v1/S08-all-negative-engine-v1.tar.gz';assert sha(archive.read_bytes())=='edfb85398c9f9522470de2e782a75fca862b034e7726b16fcd7216ac7050c6f0'
    with tarfile.open(archive) as tf:
        for m in tf.getmembers():
            assert m.isfile();name='reviewed141/'+m.name.split('/',1)[1];b=tf.extractfile(m).read();assert not b.startswith(b'\x7fELF');payload[name]=b;origins[name]=str(archive)+'::'+m.name
    readme='''S05 post-triangle candidate preservation, frozen completed work only.

Both new packs have eight distinct schedules. The original-center and rotated-
center packs compute F OR x0*x2*x4, with four false positives; neither is an
exact witness. All production admission belongs to main. The finite selftests
use the reviewed141 engine, whose complete source/build provenance, original
controls and independent reviews are flattened unchanged under reviewed141/.
Binary hashes are retained there; no binaries are included.

The134227 sources, all bounded internal/fanout/multiport repair code and full
logs are included. The free-E sixgate scan completed7478prefix states with no
candidate. Its mathematical completeness argument awaits independent review;
there is no global21-gate lower bound. The7/8-input contributor searches are
heuristic beams, finding exact12/13gate controls only. No solver/Lean is run by
this package. The postarchive proof notes and initial control failure are kept.

Portable verification: python3 S05/verify_posttriangle_archive.py ARCHIVE.tar.gz
This checks all member hashes, both packed outputs and intermediate values,
four original/control functions, and both small gadget controls; it launches
no engine or search. Producer scripts retain historical absolute paths and
pins for provenance; rebasing their paths is required to rerun elsewhere.
Old cited S04 input snapshots are copied under candidate134227-repair/.
Earlier solver-mode work is preserved separately by S06 and omitted here.
Historical report/metadata fields describe their original timestamped state.
'''
    payload['README.txt']=readme.encode();origins['README.txt']='generated documentation'
    manifest=dict(created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='Finished bounded candidate/math/pack work; no binaries, active outputs, production, SAT, Lean or target witness.',files=[dict(path=name,sha256=sha(b),bytes=len(b),source_path=origins[name]) for name,b in sorted(payload.items())])
    manifest_bytes=(json.dumps(manifest,indent=2)+'\n').encode();payload['manifest.json']=manifest_bytes
    out=H/'posttriangle-preservation-v1.tar.gz'
    with out.open('xb') as raw:
        with gzip.GzipFile(fileobj=raw,mode='wb',mtime=0) as gz:
            with tarfile.open(fileobj=gz,mode='w') as tf:
                for name,b in sorted(payload.items()):
                    info=tarfile.TarInfo(name);info.size=len(b);info.mode=0o644;info.mtime=0;tf.addfile(info,io.BytesIO(b))
    with (H/'posttriangle-preservation-manifest.json').open('xb') as f:f.write(manifest_bytes)
    cmd=['python3','-B',str(H/'verify_posttriangle_archive.py'),str(out)]
    with (H/'posttriangle-verification.stdout').open('x') as stdout,(H/'posttriangle-verification.stderr').open('x') as stderr:p=subprocess.run(cmd,stdout=stdout,stderr=stderr,timeout=10)
    assert p.returncode==0
    data=dict(status='READY_MAIN_REVIEW_NO_PRODUCTION',archive_path=str(out),archive_sha256=sha(out.read_bytes()),archive_bytes=out.stat().st_size,manifest_sha256=sha(manifest_bytes),members=len(payload),verification=json.loads((H/'posttriangle-verification.stdout').read_text()),verification_command=cmd,engine_archive_sha256=sha(archive.read_bytes()),files=[dict(path=str(H/n),sha256=sha((H/n).read_bytes())) for n in ['posttriangle-preservation-v1.tar.gz','posttriangle-preservation-manifest.json','posttriangle-verification.stdout','posttriangle-verification.stderr','verify_posttriangle_archive.py','preserve_posttriangle.py']])
    with (H/'posttriangle-preservation-handoff.json').open('x') as f:json.dump(data,f,indent=2);f.write('\n')
    print(json.dumps(data))
if __name__=='__main__':main()
