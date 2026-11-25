#!/usr/bin/env python3
from pathlib import Path
import argparse
import json
from parent_rule_analysis import parse_rows
from analyze_parent_live_codec import analyze
from encode_parent_rules import chunks

OUT=Path('/tmp/oec/pequalnp-pilot-61')

def encode(case):
    source=Path(f'/workspace/pequalnp-proofs/lean/PEqualNP/Outside/L_meta_{case}.lean')
    _,_,_,original_rows=parse_rows(source)
    hints={x['name']:x for x in analyze(case)['levels']}
    original={(r['forest'],r['level']):r for r in original_rows}
    output=[]
    for row in original_rows:
        n,d,cw,raw=row['count'],row['depth'],row['cw'],row['raw_length'];hint=hints[row['name']]
        prev=original.get((row['forest'],row['level']+1));pc=prev['count'] if prev else 0
        pw=pc.bit_length() if d else 0;iw=max(0,(n-1).bit_length());rw=pw+12 if d else 0
        prefix=0;exceptions=[];payload=0;payload_size=0;offsets=[];rule_offsets={}
        for i,(node,plan) in enumerate(zip(row['nodes'],hint['nodes_data'])):
            if d:
                last=(node['ops']>>(10*(d-1)))&1023
                code=plan['parent']|(last<<pw)|(plan['drops']<<(pw+10))
                prefix|=code<<(i*rw)
            else:assert node['live']==(1<<raw)-1 and node['ops']==0
            if plan['exception']:exceptions.append((i,node['ops'],node['live']))
            rules=tuple(map(tuple,plan['new_rules']))
            assert len(rules)<32
            if rules not in rule_offsets:
                rule_offsets[rules]=payload_size;entry=len(rules)
                for j,(col,paid) in enumerate(rules):entry|=(col|(paid<<cw))<<(5+j*(cw+d))
                payload|=entry<<payload_size;payload_size+=5+len(rules)*(cw+d)
            offsets.append(rule_offsets[rules])
        ow=max(offsets,default=0).bit_length();prefix_bits=n*rw
        data=prefix|(sum(v<<(i*ow) for i,v in enumerate(offsets))<<prefix_bits)|(payload<<(prefix_bits+n*ow))
        ew=iw+10*d+raw+d
        exception=sum((i|(ops<<iw)|(live<<(iw+10*d)))<<(j*ew) for j,(i,ops,live) in enumerate(exceptions))
        output.append({'name':row['name'],'dataName':row['data'],'forest':row['forest'],'mask':row['mask'],'level':row['level'],'rawLength':raw,'count':n,'depth':d,'columnWidth':cw,'parentWidth':pw,'indexWidth':iw,'offsetWidth':ow,'exceptionCount':len(exceptions),'exceptionPacked':hex(exception),'parentCount':pc,'recordWidth':rw,'prefixBits':prefix_bits,'payloadBits':payload_size,'totalBits':prefix_bits+n*ow+payload_size,'dataHexchunks':chunks(data),'dataHex':hex(data),'nodes':hint['nodes_data']})
    indexed={(r['forest'],r['level']):r for r in output};cache={}
    def decode(row,i):
        key=(row['forest'],row['level'],i)
        if key in cache:return cache[key]
        n,d,cw,pw,iw,ow,raw=[row[k] for k in ['count','depth','columnWidth','parentWidth','indexWidth','offsetWidth','rawLength']]
        data=int(row['dataHex'],16);rw=row['recordWidth'];record=(data>>(i*rw))&((1<<rw)-1)
        ex=None;packed=int(row['exceptionPacked'],16);ew=iw+10*d+raw+d
        for j in range(row['exceptionCount']):
            x=(packed>>(j*ew))&((1<<ew)-1)
            if x&((1<<iw)-1)==i:ex=x>>iw;break
        parent=record&((1<<pw)-1);inherited=()
        if d and parent<row['parentCount']:
            po,pl,inherited=decode(indexed[row['forest'],row['level']+1],parent)
        if ex is not None:ops=ex&((1<<(10*d))-1);live=ex>>(10*d)
        elif not d:ops=0;live=(1<<raw)-1
        else:
            op=(record>>pw)&1023;ops=po|(op<<(10*(d-1)));a=op&15;b=(op>>4)&15
            removed=((1<<a) if record>>(pw+10)&1 else 0)|((1<<b) if record>>(pw+11)&1 else 0)
            live=(pl^(pl&removed))|(1<<(raw+d-1))
        start=n*rw;pos=start+n*ow+((data>>(start+i*ow))&((1<<ow)-1));nr=(data>>pos)&31
        rules=tuple(((data>>(pos+5+j*(cw+d)))&((1<<cw)-1),(data>>(pos+5+j*(cw+d)+cw))&((1<<d)-1)) for j in range(nr))+inherited
        value=ops,live,rules;cache[key]=value;return value
    for row in output:
        orig=original[row['forest'],row['level']]
        for i,node in enumerate(orig['nodes']):
            ops,live,rules=decode(row,i)
            assert ops==node['ops'],(row['name'],i,'ops')
            assert live==node['live'],(row['name'],i,'live')
            assert set(node['rules'])<=set(rules),(row['name'],i,'rules')
            assert len(set(rules))==len(rules),(row['name'],i,'duplicate rules')
        del row['dataHex']
    return output

def main():
    parser=argparse.ArgumentParser();parser.add_argument('cases',nargs='+',type=int);args=parser.parse_args()
    for case in args.cases:
        encoded=encode(case);path=OUT/f'L_meta_{case}-parent-live.json';path.write_text(json.dumps(encoded,separators=(',',':')))
        print(case,'levels',len(encoded),'nodes',sum(r['count'] for r in encoded),'hex_chars',sum(sum(map(len,r['dataHexchunks']))+len(r['exceptionPacked']) for r in encoded))

if __name__=='__main__':main()
