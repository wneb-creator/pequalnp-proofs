from pathlib import Path
import json,hashlib,re,signal
b=Path('/workspace/pequalnp-proofs/results/gct231')
for name,stem,cap,elapsed,count in [('c4-trace-capped','path-c4-batch32',256,14.988737917001345,11),('neogb-compact','path-c4-qc-batch32',512,86.75161443699835,57)]:
    d=b/name;checksum=d/'SHA256SUMS'
    manifest={line.split('  ',1)[1]:line.split('  ',1)[0] for line in checksum.read_text().splitlines()}
    actual={str(p.relative_to(d)) for p in d.rglob('*') if p.is_file() and p!=checksum}
    assert set(manifest)==actual and len(manifest)==count
    for filename,digest in manifest.items():assert hashlib.sha256((d/filename).read_bytes()).hexdigest()==digest
    print('archive PASS',name,count,hashlib.sha256(checksum.read_bytes()).hexdigest())
    run=json.loads((d/(stem+'.run.json')).read_text())
    stats=json.loads((d/(stem+'.trace-summary.json')).read_text())
    assert run['status']=='UNKNOWN_OUTPUT_FILE_SIZE_LIMIT'
    assert run['returncode']==-signal.SIGXFSZ
    assert run['wall_seconds']==elapsed and run['output_file_mib_limit']==cap
    assert run['seconds_limit']==600 and run['memory_mib_limit']==4096 and run['pairs']==32
    assert stats['raw_bytes']==cap*1024**2==sum(stats['bytes_by_kind'].values())
    assert 'Truncated unsuccessful' in stats['scope'] and 'no certificate' in stats['scope']
    ip=d/Path(run['input']).name
    assert hashlib.sha256(ip.read_bytes()).hexdigest()==run['input_sha256']
    assert hashlib.sha256((d/(stem+'.f4.in')).read_bytes()).hexdigest()==run['companion_sha256']
    assert not (d/(stem+'.trace')).exists() and not (d/(stem+'.basis.json')).exists()
    note=(d/'README.md').read_text();assert stats['raw_sha256'] in note
    if name=='neogb-compact':
        log=(d/(stem+'.log')).read_text()
        rounds=re.findall(r'^\s*\d+\s+\d+\s+\d+\s+\d+\s+x\s+\d+\s+[\d.]+%\s+\d+ new\s+\d+ zero\s+[\d.]+\s+\|\s+[\d.]+',log,re.M)
        assert len(rounds)==31
        mod=(b/'native-c4-qc/neogb-path-c4-qc-p1009.in').read_text().splitlines()
        qq=ip.read_text().splitlines();assert mod[1:]==qq[1:] and qq[0]=='12 16 0 492'
    print('status PASS SIGXFSZ',cap,'MiB',elapsed,'seconds; no basis/certificate; retainedinputhashesmatch')
print('PASS omitted failed raw traces were not reread or replayed; summaries remain diagnostics only')
