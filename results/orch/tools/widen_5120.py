#!/usr/bin/env python3
"""Widen L5120's sample dimension, repeating its final sample row.

Only generic sample width/packed-row stride and typed sample arrays change.
Circuit truth words, opcode certificates, witness rows and hash hints stay intact.
"""
import argparse
import json
import re
from pathlib import Path

PAD = '''def padSample (n : Nat) : Bits :=
  BitVec.ofNat 768 (n + (if n.testBit 90 then 2^768-2^91 else 0))
'''

def transform(source):
    first=re.search(r'^def g15d\d',source,re.M)
    assert first,'first forest not found'
    prefix=source[:first.start()];tail=source[first.start():]
    changes=[]
    lines=[]
    for line in prefix.splitlines(keepends=True):
        if re.match(r'^def\s+(?:rowPack|witnesses)[A-Za-z0-9_]*\b',line):
            lines.append(line)
            continue
        if re.search(r'\b(?:91|92)\b',line):changes.append(line.rstrip('\n'))
        line=re.sub(r'\b91\b','768',line)
        line=re.sub(r'\b92\b','769',line)
        lines.append(line)
    prefix=''.join(lines)
    match=re.search(r'^abbrev Bits\s*:=\s*BitVec 768\s*$',prefix,re.M)
    assert match
    prefix=prefix[:match.end()]+'\n'+PAD+prefix[match.end():]
    arrays=[];padded=0
    pattern=re.compile(r'^def\s+(\w+)\s*:\s*Array\s*\(Bits\s*×\s*Bits\)\s*:=\s*#\[[^\n]*\]',re.M)
    def sample_array(match):
        nonlocal padded
        name=match.group(1);text=match.group();head,body=text.split(':=',1)
        nums=re.findall(r'0x[0-9a-fA-F]+|\b\d+\b',body)
        assert nums and all(int(n,0)<2**91 for n in nums),(name,'sample out of range')
        count=0
        def sample(m):
            nonlocal count,padded
            n=int(m.group(),0)
            if n & (1<<90):
                count+=1;padded+=1
                return '(padSample '+m.group()+')'
            return m.group()
        body=re.sub(r'0x[0-9a-fA-F]+|\b\d+\b',sample,body)
        arrays.append({'name':name,'sample_literals':len(nums),'padded_literals':count})
        return head+':='+body
    tail=pattern.sub(sample_array,tail)
    assert len(arrays)==14,('unexpected sample array count',len(arrays))
    result=prefix+tail
    return result,{'old_bytes':len(source.encode()),'new_bytes':len(result.encode()),'generic_width_lines':changes,'sample_arrays':arrays,'padded_literals':padded}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source',type=Path);parser.add_argument('output',type=Path)
    parser.add_argument('--report',required=True,type=Path)
    args=parser.parse_args();result,report=transform(args.source.read_text())
    args.output.write_text(result);args.report.write_text(json.dumps(report,indent=2))
    print(json.dumps({k:v for k,v in report.items() if k not in ('generic_width_lines','sample_arrays')}))

if __name__=='__main__':main()
