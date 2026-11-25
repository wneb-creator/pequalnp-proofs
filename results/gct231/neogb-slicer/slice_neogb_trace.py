"""Slice a compact exact trace to ancestors of its last nonzero constant output.

This is an untrusted storage transformation. The existing exact replay verifies
its result independently. No polynomial arithmetic or solver verdict is assumed.
"""
import argparse
from array import array
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('trace');ap.add_argument('output');args=ap.parse_args()
source=Path(args.trace);target=Path(args.output)
parents1=array('Q',[0]);parents2=array('Q',[0]);kinds=bytearray([0])
outputs=set();counts=Counter();constant=None;started=False;rawhash=hashlib.sha256()
with source.open('rb') as stream:
    for line_number,line in enumerate(stream,1):
        rawhash.update(line)
        assert line.endswith(b'\n'),('Incomplete trace line',line_number)
        rec=line[:-1].split(b'\t');kind=rec[0];counts[kind.decode()]+=1
        if kind==b'G':
            assert not started,('Late generator',line_number)
            continue
        if kind==b'O':
            assert len(rec)==3
            node=int(rec[1]);assert 0<node<len(kinds)
            outputs.add(node)
            if re.fullmatch(rb'\(-?[1-9][0-9]*(?:/[1-9][0-9]*)?\*1\)',rec[2]):
                constant=node
            continue
        node=int(rec[1]);assert node==len(kinds),('Nonconsecutive node',line_number,node,len(kinds))
        left=right=0
        if kind==b'I':
            # In this compact adapter only initial basis roots may be literal I.
            # An unexpected fallback input needs the unsliced general replay.
            assert not started,('Late literal input needs general replay',line_number)
            assert len(rec)==3
        elif kind==b'M':
            assert len(rec)==4
            started=True;left=int(rec[2]);assert left in outputs
            shift=tuple(map(int,rec[3].split(b',')));assert shift and min(shift)>=0
        elif kind==b'S':
            assert len(rec)==4
            started=True;left=int(rec[2])
        elif kind==b'A':
            assert len(rec)==5
            started=True;left=int(rec[2]);right=int(rec[3])
        else:
            raise AssertionError(('Unknown record',line_number,kind))
        assert 0<=left<node and 0<=right<node
        parents1.append(left);parents2.append(right);kinds.append(kind[0])
assert constant is not None,'No nonzero constant output; no certificate slice created'
needed=bytearray(len(kinds));stack=[constant]
while stack:
    node=stack.pop()
    if not node or needed[node]:continue
    needed[node]=1;stack.extend((parents1[node],parents2[node]))
outcounts=Counter();outbytes=0;outhash=hashlib.sha256()
with source.open('rb') as stream,target.open('wb') as out:
    for line in stream:
        fields=line.split(b'\t',2)
        if fields[0]==b'G' or needed[int(fields[1])]:
            out.write(line);outbytes+=len(line);outhash.update(line);outcounts[fields[0].decode()]+=1
result={'source':str(source),'source_sha256':rawhash.hexdigest(),'source_bytes':source.stat().st_size,
        'output':str(target),'output_sha256':outhash.hexdigest(),'output_bytes':outbytes,
        'source_records':dict(counts),'output_records':dict(outcounts),'constant_node':constant,
        'source_nodes':len(kinds)-1,'needed_nodes':sum(needed),
        'scope':'Untrusted syntactic dependency slice; exact replay is still required.'}
target.with_suffix('.slice.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
