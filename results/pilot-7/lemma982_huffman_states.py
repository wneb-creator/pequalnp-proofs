import argparse
import collections
import json
from pathlib import Path

from lemma982_checkpoint_pack import packed
from lemma982_fullstate_size import huffman

ROOT = Path('/tmp/oec/pequalnp-pilot-7')


def zz(x): return 2*x if x >= 0 else -2*x-1


def codebook(freq):
    lengths = huffman(freq)
    codes, symbols, starts, counts, bases = {}, [], [0], [0], [0]
    code = 0
    for length in range(1, max(lengths.values())+1):
        code *= 2
        group = sorted(x for x in freq if lengths[x] == length)
        starts.append(code)
        counts.append(len(group))
        bases.append(len(symbols))
        for x in group:
            codes[x] = (code, length)
            symbols.append(x)
            code += 1
    base_width = max(1,max(symbols).bit_length())
    best = None
    for block in [4,8,16,32,64]:
        chunks = []
        for i in range(0,len(symbols),block):
            part = symbols[i:i+block]
            base = min(part)
            width = (max(part)-base).bit_length()
            code = base+(width << base_width)
            code += sum((v-base) << (base_width+5+j*width) for j,v in enumerate(part))
            chunks.append(code)
        cost = sum(len(hex(c))+1 for c in chunks)
        if best is None or cost < best[0]:
            best = (cost,dict(base_width=base_width,block=block,count=len(symbols),hex=list(map(hex,chunks))))
    symbol_data = best[1]
    for i,value in enumerate(symbols):assert symbol_at(symbol_data,i)==value
    return dict(codes=codes, symbols=symbol_data,
                starts=starts, counts=counts, bases=bases, max_length=len(starts)-1)


def symbol_at(p,index):
    code=int(p['hex'][index//p['block']],16)
    base=code % (1 << p['base_width'])
    width=(code >> p['base_width']) % 32
    offset=code >> (p['base_width']+5+(index%p['block'])*width)
    return base+offset % (1 << width)


def emit_book(name, book):
    lines = []
    for key in ['starts','counts','bases']:
        lines.append(f'def {name}{key} : Array Nat := #['+','.join(map(str,book[key]))+']')
    p = book['symbols']
    lines.append(f'def {name}symbols : Array Nat := #['+','.join(p['hex'])+']')
    lines.append(f'def {name}symbolBaseWidth : Nat := {p["base_width"]}')
    lines.append(f'def {name}symbolBlock : Nat := {p["block"]}')
    return '\n'.join(lines)+'\n'


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--block',type=int,default=16)
    args=parser.parse_args()
    datas=[json.loads(p.read_text()) for p in sorted(ROOT.glob('lemma982-reoriented-core*.json'))]
    dp, tp = collections.Counter(), collections.Counter()
    cores=[]
    for d in datas:
        blocks=[]; bases=[]
        for layer in d['recipes']:
            bases.append(len(blocks))
            for start in range(0,len(layer),args.block):
                block=[]; previous=0
                for parent,tag in layer[start:start+args.block]:
                    delta=zz(parent-previous)
                    dp[delta]+=1; tp[tag]+=1
                    block.append((delta,tag)); previous=parent
                blocks.append(block)
        cores.append((d,blocks,bases))
    db,tb=codebook(dp),codebook(tp)
    booksrc='namespace PEqualNP.Outside.L_meta_982_aux.HuffmanData\n'+emit_book('delta',db)+emit_book('tag',tb)+'end PEqualNP.Outside.L_meta_982_aux.HuffmanData\n'
    (ROOT/f'lemma982-huffman{args.block}-books.lean').write_text(booksrc)
    summaries=[]
    for d,blocks,bases in cores:
        bitpos=0; offsets=[]; chunks=[]
        def put_bit(bit):
            nonlocal bitpos
            if bitpos//1024==len(chunks):chunks.append(0)
            chunks[bitpos//1024]|=bit << (bitpos%1024)
            bitpos+=1
        def put(book,symbol):
            code,length=book['codes'][symbol]
            for j in range(length-1,-1,-1):put_bit((code>>j)&1)
        for block in blocks:
            offsets.append(bitpos)
            for delta,tag in block:put(db,delta);put(tb,tag)
        def read(book,pos):
            code=0
            for length in range(1,book['max_length']+1):
                code=code*2+((chunks[pos//1024]>>(pos%1024))&1);pos+=1
                i=code-book['starts'][length]
                if 0<=i<book['counts'][length]:
                    index=book['bases'][length]+i;v=symbol_at(book['symbols'],index)
                    return v,pos
            raise AssertionError('invalid Huffman code')
        for s,layer in enumerate(d['recipes']):
            for i,expected in enumerate(layer):
                pos=offsets[bases[s]+i//args.block]; parent=0
                for _ in range(i%args.block+1):
                    delta,pos=read(db,pos);tag,pos=read(tb,pos)
                    parent += delta//2 if delta%2==0 else -(delta//2+1)
                assert [parent,tag]==expected,(d['case'],s,i)
        po=packed(offsets,max(1,max(offsets,default=0).bit_length()))
        c=d['case'];lines=['namespace PEqualNP.Outside.L_meta_982_aux.HuffmanData',
            f'def h{c}data : Array Nat := #['+','.join(hex(x) for x in chunks)+']',
            f'def h{c}offsets : Array Nat := #['+','.join(po['hex'])+']',
            f'def h{c}offsetWidth : Nat := {po["width"]}',f'def h{c}offsetBlock : Nat := {po["block"]}',
            f'def h{c}layerBase : Array Nat := #['+','.join(map(str,bases))+']',
            f'def h{c}counts : Array Nat := #['+','.join(map(str,d['counts']))+']',
            'end PEqualNP.Outside.L_meta_982_aux.HuffmanData']
        source='\n'.join(lines)+'\n'
        (ROOT/f'lemma982-huffman{args.block}-core{c}.lean').write_text(source)
        metadata=dict(case=c,block=args.block,counts=d['counts'],layer_base=bases,offsets=po,
                      data_hex=[hex(x) for x in chunks],all_records_round_trip=True,
                      bits=bitpos,source_bytes=len(source.encode()))
        (ROOT/f'lemma982-huffman{args.block}-core{c}.json').write_text(json.dumps(metadata,indent=2)+'\n')
        summaries.append({k:metadata[k] for k in ['case','bits','source_bytes']})
        print(json.dumps(summaries[-1]),flush=True)
    report=dict(block=args.block,codebook_source_bytes=len(booksrc.encode()),
                total_state_data_source_bytes=sum(s['source_bytes'] for s in summaries)+len(booksrc.encode()),
                max_delta_code_length=db['max_length'],max_tag_code_length=tb['max_length'],
                cores=summaries,all_records_round_trip=True,lean_decoder_not_yet_checked=True)
    (ROOT/f'lemma982-huffman{args.block}-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='cores'}),flush=True)


if __name__=='__main__':main()
