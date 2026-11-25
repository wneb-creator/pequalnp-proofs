import argparse
import pathlib
from packing_parser import parse_module

def word_tree(words,lo=0,hi=None):
    if hi is None: hi=len(words)
    if hi-lo==1:return hex(words[lo])
    mid=(lo+hi)//2
    return f'(if i<{mid} then {word_tree(words,lo,mid)} else {word_tree(words,mid,hi)})'

def transform(path):
    source,defs,forests,rows=parse_module(path)
    savings=0
    seen=set()
    for row in rows:
        name=row['data']
        if name in seen:raise ValueError('duplicate packing data: '+name)
        seen.add(name)
        bits=row['prefix_bits']
        n=row['prefix']
        words=[(n>>(8192*j))&((1<<8192)-1) for j in range(max(1,(bits+8191)//8192))]
        assert sum(w<<(8192*j) for j,w in enumerate(words)) == n
        old=defs[name]
        new=f'def {name} (i : Nat) : Nat := {word_tree(words)}\n'
        if source.count(old)!=1:raise ValueError('ambiguous declaration')
        source=source.replace(old,new)
        savings+=len(old)-len(new)
    mark='def stateSet'
    helper='def allRulePairs (g : Forest) (depth : Nat) : List (Nat × Nat) :=\n  (List.range (2^depth)).flatMap fun p => (List.range g.cols.length).map fun i => (i,p)\n'
    assert mark in source
    source=source.replace(mark,helper+mark,1)
    count=source.count('getPairs data cw depth nr st')
    assert count==2,count
    source=source.replace('getPairs data cw depth nr st','allRulePairs g depth')
    return source,savings,len(rows)

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('input');p.add_argument('output')
    p.add_argument('--namespace')
    a=p.parse_args()
    source,savings,rows=transform(a.input)
    if a.namespace:
        stem=pathlib.Path(a.input).stem
        source=source.replace('PEqualNP.Outside.'+stem,a.namespace)
    pathlib.Path(a.output).write_text(source)
    print('trimmed',rows,'levels; saved',savings,'source characters; result',len(source.encode()),'bytes')
