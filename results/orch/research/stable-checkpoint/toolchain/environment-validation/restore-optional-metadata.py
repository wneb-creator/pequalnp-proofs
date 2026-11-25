from pathlib import Path
import hashlib,json,os,stat,sys,tarfile,zstandard
BASE=Path('/tmp/oec/pequalnp-pilot-78/toolchain/optional-metadata-backup')
ROOT=Path('/workspace/pequalnp-proofs/lean/.lake/packages')
names=set(sys.argv[1:]);assert names,'usage: restore-optional-metadata.py all|Mathlib.Module ...'
count=0
for manifest_path in sorted(BASE.glob('chunk-*.json.zst')):
    rows=json.loads(zstandard.ZstdDecompressor().decompress(manifest_path.read_bytes()))
    selected={r['path']:r for r in rows if 'all' in names or r['module'] in names}
    if not selected:continue
    archive_path=manifest_path.with_name(manifest_path.name.replace('.json.zst','.tar.zst'))
    with archive_path.open('rb') as raw,zstandard.ZstdDecompressor().stream_reader(raw) as unpacked,tarfile.open(fileobj=unpacked,mode='r|') as archive:
        for member in archive:
            if member.name not in selected:continue
            row=selected[member.name];assert member.isfile()
            data=archive.extractfile(member).read();assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256']
            p=ROOT/row['path'];assert p.is_relative_to(ROOT) and not p.is_symlink()
            if p.exists():assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
            else:
                p.parent.mkdir(parents=True,exist_ok=True);temporary=p.with_name(p.name+'.metadata-restore');temporary.write_bytes(data);temporary.chmod(row['mode']);os.utime(temporary,ns=(row['atime_ns'],row['mtime_ns']));os.replace(temporary,p)
            s=p.stat();assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'] and s.st_mtime_ns==row['mtime_ns'] and stat.S_IMODE(s.st_mode)==row['mode']
            count+=1
print(json.dumps({'restored_or_verified_files':count,'requested':sorted(names)}))
