from pathlib import Path
import hashlib,io,json,os,stat,tarfile,time,zstandard
BASE=Path('/tmp/oec/pequalnp-pilot-78/toolchain')
ROOT=Path('/workspace/pequalnp-proofs/lean/.lake/packages')
OUT=BASE/'optional-metadata-backup';OUT.mkdir(exist_ok=True)
plan=json.loads(zstandard.ZstdDecompressor().decompress((BASE/'optional-lake-metadata-plan.json.zst').read_bytes()))
required=set(json.loads((BASE/'source-archive-plan.json').read_text())['required_modules'])
assert plan['files']==53262 and len(required)==2780
start=time.monotonic();reclaimed=0;archived=0
for number,offset in enumerate(range(0,len(plan['files_list']),1000)):
    entries=plan['files_list'][offset:offset+1000]
    archive_path=OUT/f'chunk-{number:03}.tar.zst'
    manifest_path=OUT/f'chunk-{number:03}.json.zst'
    assert not archive_path.exists() and not manifest_path.exists()
    manifest=[]
    with archive_path.open('wb') as raw,zstandard.ZstdCompressor(level=6).stream_writer(raw,closefd=False) as packed,tarfile.open(fileobj=packed,mode='w|') as archive:
        for entry in entries:
            p=Path(entry['path']);assert p.is_relative_to(ROOT) and entry['module'] not in required
            assert p.suffix in ('.hash','.trace') and not p.is_symlink()
            s=p.stat();assert stat.S_ISREG(s.st_mode) and s.st_size==entry['bytes'] and s.st_mtime_ns==entry['mtime_ns']
            data=p.read_bytes();rel=str(p.relative_to(ROOT));digest=hashlib.sha256(data).hexdigest()
            row={'path':rel,'module':entry['module'],'bytes':len(data),'allocated':s.st_blocks*512,'sha256':digest,'mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns,'atime_ns':s.st_atime_ns}
            manifest.append(row)
            info=tarfile.TarInfo(rel);info.size=len(data);info.mode=row['mode'];info.mtime=s.st_mtime
            archive.addfile(info,io.BytesIO(data))
    encoded=json.dumps(manifest,separators=(',',':')).encode();compressed=zstandard.ZstdCompressor(level=6).compress(encoded)
    manifest_path.write_bytes(compressed);assert zstandard.ZstdDecompressor().decompress(manifest_path.read_bytes())==encoded
    expected={row['path']:row for row in manifest};verified=set();sample=None
    with archive_path.open('rb') as raw,zstandard.ZstdDecompressor().stream_reader(raw) as unpacked,tarfile.open(fileobj=unpacked,mode='r|') as archive:
        for member in archive:
            assert member.isfile() and member.name in expected
            row=expected[member.name];data=archive.extractfile(member).read()
            assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256']
            verified.add(member.name)
            if sample is None:sample=(row,data)
    assert verified==set(expected)
    if number==0:
        row,data=sample;sample_path=OUT/'restore-smoke.tmp';sample_path.write_bytes(data);sample_path.chmod(row['mode']);os.utime(sample_path,ns=(row['atime_ns'],row['mtime_ns']))
        sample_stat=sample_path.stat();assert hashlib.sha256(sample_path.read_bytes()).hexdigest()==row['sha256'] and sample_stat.st_mtime_ns==row['mtime_ns'] and stat.S_IMODE(sample_stat.st_mode)==row['mode']
        (OUT/'restore-smoke.json').write_text(json.dumps({'pass':True,'sample':row['path'],'sha256':row['sha256'],'mode':row['mode'],'mtime_ns':row['mtime_ns'],'original_present':(ROOT/row['path']).is_file()},indent=2))
        sample_path.unlink()
    for row in manifest:
        p=ROOT/row['path'];s=p.stat()
        assert s.st_size==row['bytes'] and s.st_mtime_ns==row['mtime_ns'] and hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
        p.unlink();archived+=1;reclaimed+=row['allocated']
    free=os.statvfs(OUT).f_bavail*os.statvfs(OUT).f_frsize
    print(json.dumps({'chunk':number,'archived_files':archived,'original_allocated_bytes':reclaimed,'free_bytes':free,'seconds':time.monotonic()-start}),flush=True)
report={'pass':True,'files':archived,'original_allocated_bytes':reclaimed,'backup_allocated_bytes':sum(p.stat().st_blocks*512 for p in OUT.iterdir() if p.is_file()),'elapsed_seconds':time.monotonic()-start,'scope':'Only hash/trace build metadata outside current selective build closure; all runtime artifacts and current closure metadata unchanged.'}
(OUT/'result.json').write_text(json.dumps(report,indent=2));print(json.dumps(report),flush=True)
