"""Emit radix-32 Huffman tables and pure reconstructed-state wrappers.

The packed records and their ordering are unchanged.  Large arrays become
two-level literal arrays; every array scan has at most 32 entries.
"""
import json
from pathlib import Path

ROOT = Path('/tmp/oec/pequalnp-pilot-7')
NS = 'PEqualNP.Outside.L_meta_982_aux'


def radix_source(source):
    lines = []
    for line in source.splitlines():
        if ': Array Nat := #[' in line and ('symbols :' in line or 'data :' in line):
            before, values = line.split(' : Array Nat := #[', 1)
            values = values[:-1].split(',')
            assert len(values) <= 1024
            blocks = ['#[' + ','.join(values[i:i+32]) + ']'
                      for i in range(0, len(values), 32)]
            line = before + f' : {NS}.Huffman.Table := #[' + ','.join(blocks) + ']'
        lines.append(line)
    return '\n'.join(lines) + '\n'


def main():
    (ROOT/'lemma982-huffman32-radix-books.lean').write_text(radix_source(
        (ROOT/'lemma982-huffman32-books.lean').read_text()))
    common = f'''namespace {NS}.HuffmanData
open {NS}.Huffman
def readDelta := read deltastarts deltacounts deltabases deltasymbolBaseWidth deltasymbolBlock deltasymbols
def readTag := read tagstarts tagcounts tagbases tagsymbolBaseWidth tagsymbolBlock tagsymbols
end {NS}.HuffmanData
'''
    (ROOT/'Huffman982CommonWrappers.lean.txt').write_text(common)
    info = []
    for case in range(31):
        d = json.loads((ROOT/f'root982-slice-core{case}.json').read_text())
        h = json.loads((ROOT/f'lemma982-huffman32-core{case}.json').read_text())
        cap = len(h['counts'])-1
        radix = radix_source((ROOT/f'lemma982-huffman32-core{case}.lean').read_text())
        (ROOT/f'lemma982-huffman32-radix-core{case}.lean').write_text(radix)
        # These root declarations are optional when the semantic bridge already
        # provides the same sliced input list and coordinate count.
        inputs = f'''namespace {NS}.HuffmanData
def c{case}Inputs : List Nat := [{','.join(d['inputs_hex'])}]
def c{case}K : Nat := {d['K']}
end {NS}.HuffmanData
'''
        wrappers = f'''namespace {NS}.HuffmanData
open {NS}.Huffman
def c{case}Mask : Nat := 2^(c{case}K+c{case}K)-1
def c{case}Root := c{case}Inputs.foldr insertWord []
def c{case}Count (s : Nat) := h{case}counts.getD s 0
def c{case}Blocks := recordBlock 32 h{case}offsetWidth h{case}offsetBlock h{case}offsets h{case}layerBase h{case}data readDelta readTag
def c{case}Records := recordFromBlocks 32 c{case}Blocks
def c{case}States := state {cap} c{case}Mask c{case}Root c{case}Records
end {NS}.HuffmanData
'''
        (ROOT/f'Huffman982Core{case}Inputs.lean.txt').write_text(inputs)
        (ROOT/f'Huffman982Core{case}StateWrappers.lean.txt').write_text(wrappers)
        info.append(dict(case=case,cap=cap,K=d['K'],data_bytes=len(radix.encode()),
                         inputs_bytes=len(inputs.encode()),wrappers_bytes=len(wrappers.encode())))
    report = dict(cores=info,
        data_and_books_bytes=sum(i['data_bytes'] for i in info)+(ROOT/'lemma982-huffman32-radix-books.lean').stat().st_size,
        input_literals_bytes=sum(i['inputs_bytes'] for i in info),
        wrappers_bytes=sum(i['wrappers_bytes'] for i in info)+len(common.encode()),
        large_table_max_width=32,large_table_depth=2)
    (ROOT/'lemma982-huffman-radix-source-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='cores'}))


if __name__ == '__main__':
    main()
