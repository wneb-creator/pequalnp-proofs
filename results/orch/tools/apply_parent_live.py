#!/usr/bin/env python3
import argparse
import json
import re
from pathlib import Path
from packing_parser import definitions
from trim_rule_payload import word_tree

OUT=Path('/tmp/oec/pequalnp-pilot-61')

def transform(source,rows):
    defs=definitions(source)
    edits=[]
    for row in rows:
        data=row['dataName'];new=f'def {data} (i : Nat) : Nat := '+word_tree([int(x,16) for x in row['dataHexchunks']])+'\n'
        edits.append((defs[data],new))
        fields=[str(row[k]) for k in ['count','depth','columnWidth','parentWidth','indexWidth','offsetWidth','exceptionCount']]+[row['exceptionPacked'],data]
        edits.append((defs[row['name']],f'def {row["name"]} : Packing := ('+','.join(fields)+')\n'))
    for old,new in edits:
        assert source.count(old)==1,old[:100]
        source=source.replace(old,new)
    defs=definitions(source)
    start=source.index(defs['cmpException']);end=source.index(defs['readNode'])+len(defs['readNode'])
    assert start<end
    source=source[:start]+(OUT/'parent_live_codec.lean.txt').read_text()+'\n'+source[end:]
    fast=re.search(r'^noncomputable def fastState\b[\s\S]*?(?=^theorem fastState_eq\b)',source,re.M)
    if fast:
        old=fast.group()
        new='''noncomputable def fastState (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (selected g.mask).map fun e => (inputs.getD (idxOf perm e.1) zero).toNat
  let depth := (g.levels k).2.1
  selectLive (cmpLive g depth k i) (decodeN depth (cmpOps g depth k i) raw)
'''
        source=source.replace(old,new)
    return source

def main():
    parser=argparse.ArgumentParser();parser.add_argument('source',type=Path);parser.add_argument('encoded',type=Path);parser.add_argument('output',type=Path)
    args=parser.parse_args();old=args.source.read_text();new=transform(old,json.loads(args.encoded.read_text()));args.output.write_text(new)
    print(json.dumps({'source':str(args.source),'output':str(args.output),'old_bytes':len(old.encode()),'new_bytes':len(new.encode()),'saved_bytes':len(old.encode())-len(new.encode())}))

if __name__=='__main__':main()
