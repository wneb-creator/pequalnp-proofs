"""Remove pools whose selected maximum-bound witness requires L670.sgC."""
import argparse
import hashlib
import json
import struct
from pathlib import Path

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--input',required=True,type=Path)
parser.add_argument('--map',required=True,type=Path)
parser.add_argument('--output',required=True,type=Path)
args=parser.parse_args()
data=(args.input/'pools.bin').read_bytes()
mapping=json.loads(args.map.read_text())
assert hashlib.sha256(data).hexdigest()==mapping['pools_sha256']
records=mapping['records']
assert struct.unpack_from('<I',data)[0]==len(records)==1185
offset=4
parts=[]
ids=[]
for i,record in enumerate(records):
    n=struct.unpack_from('<I',data,offset+132)[0]
    size=136+128*n
    assert offset+size<=len(data)
    if record[1]!=0:
        parts.append(data[offset:offset+size])
        ids.append(i)
    offset+=size
assert offset==len(data) and len(parts)==1078
args.output.mkdir(parents=True,exist_ok=True)
(args.output/'pools.bin').write_bytes(struct.pack('<I',len(parts))+b''.join(parts))
header=(args.input/'probe-data.hpp').read_text()
assert header.count('n!=1185')==1
(args.output/'probe-data.hpp').write_text(header.replace('n!=1185','n!=1078'))
(args.output/'old-pool-ids.json').write_text(json.dumps(ids)+'\n')
print(json.dumps(dict(status='PASS',pools=len(parts),removed=len(records)-len(parts))))
