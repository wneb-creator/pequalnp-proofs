import argparse
import hashlib
import json
import struct
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('directory',type=Path)
parser.add_argument('depth',type=int)
args=parser.parse_args()
front=args.directory/('frontier-'+str(args.depth)+'.bin')
wire=args.directory/'wires.bin'
with front.open('rb') as f:
    header=f.read(16)
    assert len(header)==16
    nw,ns=struct.unpack('<QQ',header)
    assert nw>=10 and wire.stat().st_size>=144*nw
    for _ in range(ns):
        header=f.read(8)
        assert len(header)==8
        n,d=struct.unpack('<II',header)
        assert n<=20 and d==args.depth
        body=f.read(4*n+12*d)
        assert len(body)==4*n+12*d
    assert not f.read(1)
sha=hashlib.sha256()
with front.open('rb') as f:
    for block in iter(lambda:f.read(1<<20),b''):sha.update(block)
print(json.dumps(dict(status='PASS',depth=args.depth,states=ns,wires=nw,
                     frontier_bytes=front.stat().st_size,frontier_sha256=sha.hexdigest())))
