"""Copy one atomic published polynomial snapshot without touching the live solver."""
import argparse,gzip,hashlib,json,shutil
from datetime import datetime,timezone
from pathlib import Path
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('prefix',type=Path)
parser.add_argument('destination',type=Path)
args=parser.parse_args()
meta_path=Path(str(args.prefix)+'.checkpoint.latest.json')
metadata_bytes=meta_path.read_bytes()
metadata=json.loads(metadata_bytes)
snapshot=Path(str(args.prefix)+f'.checkpoint.s{metadata["sequence"]:06d}.in')
assert not args.destination.exists()
args.destination.mkdir(parents=True)
digest=hashlib.sha256();total=0
with snapshot.open('rb') as source, (args.destination/'snapshot.in.gz').open('wb') as raw:
    with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0,compresslevel=6) as compressed:
        for block in iter(lambda:source.read(1024*1024),b''):
            digest.update(block);total+=len(block);compressed.write(block)
with gzip.open(args.destination/'snapshot.in.gz','rb') as check:
    verify=hashlib.sha256()
    for block in iter(lambda:check.read(1024*1024),b''):verify.update(block)
assert verify.digest()==digest.digest()
(args.destination/'snapshot-metadata.json').write_bytes(metadata_bytes)
for suffix,name in [('.launch.json','launch.json'),('.log','stdout-stderr-through-snapshot.log')]:
    shutil.copyfile(args.prefix.with_suffix(suffix),args.destination/name)
record={'preserved_utc':datetime.now(timezone.utc).isoformat(),
        'snapshot_sha256_uncompressed':digest.hexdigest(),'snapshot_bytes_uncompressed':total,
        'original_snapshot':str(snapshot),'metadata':metadata,
        'scope':'Partial finite-field restart generating set, not a final basis or mathematical verdict. Log is the entire prefix captured during an ongoing run.'}
(args.destination/'preservation.json').write_text(json.dumps(record,indent=2)+'\n')
manifest={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(args.destination.iterdir())}
raw=(json.dumps(manifest,indent=2)+'\n').encode();(args.destination/'sha256.json').write_bytes(raw)
print(json.dumps({'directory':str(args.destination),'files':len(manifest),
    'manifest_sha256':hashlib.sha256(raw).hexdigest(),'uncompressed_bytes':total,
    'compressed_bytes':(args.destination/'snapshot.in.gz').stat().st_size,
    'round':metadata['round'],'sequence':metadata['sequence']},sort_keys=True))
