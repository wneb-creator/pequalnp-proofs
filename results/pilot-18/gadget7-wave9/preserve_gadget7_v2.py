"""Compact frozen seven-input source/control preservation with CNF recipes."""
from pathlib import Path
import json,hashlib,gzip,tarfile,io,datetime,subprocess
H=Path('/tmp/oec/pequalnp-pilot-18/orch/S05')
def sha(b):return hashlib.sha256(b).hexdigest()
def main():
    payload={};origins={};recipes=[];handoff=json.load(open(H/'gadget7-handoff.json'))
    def add(p,name=None):
        p=Path(p);name=name or str(p.relative_to(H));b=p.read_bytes();assert not b.startswith(b'\x7fELF')
        if name in payload:assert payload[name]==b
        payload[name]=b;origins[name]=str(p)
    for name,r in handoff['files'].items():
        p=H/name;assert sha(p.read_bytes())==r['sha256'] and p.stat().st_size==r['bytes']
        if name.endswith('.cnf'):
            stem=p.stem;recipes.append(dict(path=name,sha256=r['sha256'],bytes=r['bytes'],gates=11 if stem in ['generic11','bad11-pinned'] else 12,pinned='positive12' if stem=='positive12-pinned' else 'bad11' if stem=='bad11-pinned' else None))
        else:add(p)
    for n in ['gadget7-handoff.json','package_gadget7.stdout','package_gadget7.stderr','verify_gadget7_archive.py','preserve_gadget7_v2.py']:add(H/n)
    main_review=H.parent/'MAIN/main-gadget7-review.json'
    assert sha(main_review.read_bytes())=='af69f66387be6371d6d04e09b48f86b44b2ef48b04ef2c83c140e3ed30dc8fed'
    add(main_review,'main-review/main-gadget7-review.json')
    add(H/'preserve_gadget7.py','archive-parent/preserve_gadget7.py')
    add(H/'derive_gadget7_archive_v2.py')
    add(H/'gadget7-preservation-v2-derivation.json')
    for e in json.load(open(H/'gadget7-lift-handoff.json'))['artifacts']:
        p=Path(e['path']);assert p.is_relative_to(H) and sha(p.read_bytes())==e['sha256'];add(p)
    payload['cnf-recipes.json']=(json.dumps(recipes,indent=2)+'\n').encode();origins['cnf-recipes.json']='generated from exact pinned handoff'
    payload['PRESERVATION.txt']=b'''Frozen seven-input generator, validator, derivation, full controls/models/proofs/logs.
No executable binaries, raw CNFs or production outputs. Four exact CNFs and
metadata reconstruct from the pinned generator and retained circuit fixtures.
Both small bad11 proofs apply ONLY to the fully pinned fixture. Generic11
is unresolved in this historical source/control snapshot. Positive12 gives
full22, exceeds both limits, and is not a21-gate witness. Lean is separate.
All historical absolute paths/status fields retain their original meaning.

Portable verifier: python3 verify_gadget7_archive.py ARCHIVE.tar.gz FRESH_DIR
It restores all payloads, regenerates four CNFs/metadata byte-exact, validates
both retained positive models on128 and2048inputs and rejects the bad model.
It starts no solver or checker. Main owns production and independent review.
Completed MAIN encoding review is included. Both active SAT-only runtime
outputs are excluded and were not read. S06 separately preserves the SAT-only
runner and independent review. No S06 source or main runner was changed.
''';origins['PRESERVATION.txt']='generated documentation'
    manifest=dict(created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scope='Frozen seven-input source/control data only; no production or global proof claim.',files=[dict(path=n,sha256=sha(b),bytes=len(b),source_path=origins[n]) for n,b in sorted(payload.items())],omitted_CNFs=recipes)
    mb=(json.dumps(manifest,indent=2)+'\n').encode();payload['manifest.json']=mb
    out=H/'gadget7-preservation-v2.tar.gz'
    with out.open('xb') as raw:
        with gzip.GzipFile(fileobj=raw,mode='wb',mtime=0) as gz:
            with tarfile.open(fileobj=gz,mode='w') as tf:
                for n,b in sorted(payload.items()):
                    m=tarfile.TarInfo(n);m.size=len(b);m.mode=0o644;m.mtime=0;tf.addfile(m,io.BytesIO(b))
    (H/'gadget7-preservation-v2-manifest.json').write_bytes(mb)
    cmd=['python3','-B',str(H/'verify_gadget7_archive.py'),str(out),str(H/'gadget7-preservation-restore-v2')]
    with (H/'gadget7-preservation-v2-verify.stdout').open('x') as stdout,(H/'gadget7-preservation-v2-verify.stderr').open('x') as stderr:r=subprocess.run(cmd,stdout=stdout,stderr=stderr,timeout=10)
    assert r.returncode==0
    d=dict(status='READY_MAIN_REVIEW',main_review_sha256=sha(main_review.read_bytes()),active_runtime_included=False,source_control_handoff_sha256=sha((H/'gadget7-handoff.json').read_bytes()),archive_sha256=sha(out.read_bytes()),archive_bytes=out.stat().st_size,members=len(payload),manifest_sha256=sha(mb),verification_command=cmd,verification=json.loads((H/'gadget7-preservation-v2-verify.stdout').read_text()),files=[dict(path=str(H/n),sha256=sha((H/n).read_bytes()),bytes=(H/n).stat().st_size) for n in ['gadget7-preservation-v2.tar.gz','gadget7-preservation-v2-manifest.json','gadget7-preservation-v2-verify.stdout','gadget7-preservation-v2-verify.stderr','verify_gadget7_archive.py','preserve_gadget7_v2.py']])
    with (H/'gadget7-preservation-v2-handoff.json').open('x') as f:json.dump(d,f,indent=2);f.write('\n')
    print(json.dumps(d))
if __name__=='__main__':main()
