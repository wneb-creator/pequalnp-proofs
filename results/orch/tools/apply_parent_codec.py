import argparse
import json
import pathlib
import re
from packing_parser import definitions
from trim_rule_payload import word_tree

ROOT=pathlib.Path('/tmp/oec/pequalnp-pilot-61')
def transform(source,rows,block16=False):
    defs=definitions(source)
    for row in rows:
        name=row['dataName']
        words=[int(x,16) for x in row['dataHexchunks']]
        new=f'def {name} (i : Nat) : Nat := {word_tree(words)}\n'
        source=source.replace(defs[name],new)
        fields=[str(row[key]) for key in ['count','depth','columnWidth','parentWidth','indexWidth','offsetWidth','exceptionCount']]
        fields.append(row['exceptionPacked']);fields.append(name)
        newpack=f'def {row["name"]} : Packing := ('+','.join(fields)+')\n'
        source=source.replace(defs[row['name']],newpack)
    source,n=re.subn(r'abbrev Packing\s*:=\s*Nat × Nat × Nat × Nat × Nat × Nat × Nat × \(Nat → Nat\)',
                     'abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)',source)
    assert n==1,n
    source,n=re.subn(r'def emptyPacking : Packing\s*:=\s*\(0,0,0,0,0,0,0,fun _ => 0\)',
                     'def emptyPacking : Packing := (0,0,0,0,0,0,0,0,fun _ => 0)',source)
    assert n==1,n
    defs2=definitions(source)
    source=source.replace(defs2['readNode'],(ROOT/'parent_codec.lean.txt').read_text())
    pos=source.index('def stateSet')
    rulehelper=(ROOT/'parent_rules.lean.txt').read_text()
    if block16:rulehelper=(ROOT/'parent_rules_block16.lean.txt').read_text()+rulehelper[rulehelper.index('def cmpRules'):]
    source=source[:pos]+rulehelper+source[pos:]
    defs3=definitions(source)
    names=[name for name,body in defs3.items() if 'getPairs data cw depth nr st' in body and 'buildRule g ops depth bank a b' in body]
    assert len(names)==2,names
    for name in names:
        old=defs3[name]
        new=re.sub(r'  let \(num,depth,cw,iw,pw,offw,lw,data\)\s*:=\s*g.levels k',
                   '  let depth := (g.levels k).2.1',old)
        new,n=re.subn(r'  let start\s*:=.*?\n  let st\s*:=.*?\n','',new,flags=re.S)
        assert n==1,(name,n)
        assert new.count('getPairs data cw depth nr st')==1,name
        new=new.replace('getPairs data cw depth nr st','cmpRules g depth k i')
        source=source.replace(old,new)
    return source

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('input');p.add_argument('encoded');p.add_argument('output')
    p.add_argument('--namespace');p.add_argument('--cut-before');p.add_argument('--block16',action='store_true')
    a=p.parse_args()
    source=pathlib.Path(a.input).read_text()
    rows=json.loads(pathlib.Path(a.encoded).read_text())
    out=transform(source,rows,a.block16)
    stem=pathlib.Path(a.input).stem
    oldns='PEqualNP.Outside.'+stem
    newns=a.namespace or oldns
    if a.namespace:out=out.replace(oldns,a.namespace)
    if a.cut_before:out=out[:out.index(a.cut_before)]+'\nend '+newns+'\n'
    pathlib.Path(a.output).write_text(out)
    print('input',len(source.encode()),'output',len(out.encode()),'bytes')
