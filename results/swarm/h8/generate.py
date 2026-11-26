import ast
import argparse
import hashlib
import itertools
import json
import re
import struct
import time
from pathlib import Path

parser = argparse.ArgumentParser(description='Generate H9 contraction-search data from checked L670.')
parser.add_argument('--source', type=Path, default=Path(__file__).resolve().parents[3]/'lean/PEqualNP/Outside/L_meta_670.lean')
parser.add_argument('--out-dir', type=Path, required=True)
parser.add_argument('--signed', action='store_true')
args = parser.parse_args()
TASK_DIR = args.out_dir.resolve()
TASK_DIR.mkdir(parents=True, exist_ok=True)
SOURCE = args.source
S = SOURCE.read_text()
FULL = (1 << 512) - 1
INPUTS = [sum(1 << x for x in range(512) if x >> i & 1) for i in range(9)]
EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
TARGET = 0
for a,b in EDGES:
    TARGET |= INPUTS[a] & INPUTS[b]

def literal(name):
    match = re.search(r'^def '+re.escape(name)+r'[^\n]*:= (.+)$', S, re.M)
    return ast.literal_eval(match.group(1).replace('#[', '['))

def binary(op,a,b):
    return (a&b) if op == 0 else (a|b) if op == 1 else (a&~b) if op == 2 else (~a&b)

def typeword(t):
    return binary(t//81,INPUTS[t//9%9],INPUTS[t%9])

NEG = [x for x in range(512) if not (TARGET>>x&1) and all(TARGET>>(x|1<<i)&1 for i in range(9) if not(x>>i&1))]
POS = sorted({(1<<a)|(1<<b) for a,b in EDGES})
PAIRS = list(itertools.product(POS,NEG))
COVER_FULL = (1<<len(PAIRS))-1

def cover(w):
    return sum(1<<j for j,(p,n) in enumerate(PAIRS) if w>>p&1 and not(w>>n&1))

COLS = list(dict.fromkeys(literal('moC')+literal('sgC')))
POOLS = []
for z,o,q,s,L in COLS:
    dom = sum(1<<r for r in range(512) if not(r&(z%512)) and r&o == o)
    vals = set([0,dom]+[v&dom for v in INPUTS])
    if z//512:
        vals.add(typeword(z//512-1)&dom)
    POOLS.append((dom,L,tuple(sorted(vals))))

def export(signed=False):
    tag='signed-' if signed else ''
    pools=POOLS
    pairs=PAIRS
    if signed:
        samples=literal('sgY')
        pairs=[(sum(((samples[i][0]>>j)&1)<<i for i in range(9)),sum(((samples[i][1]>>j)&1)<<i for i in range(9))) for j in range(152)]
        assert all(TARGET>>p&1 and not(TARGET>>n&1) for p,n in pairs)
        pools=[]
        for z,o,q,s,L in dict.fromkeys(literal('sgC')):
            dom=sum(1<<r for r in range(512) if not(r&(z%512)) and r&o==o)
            vals=set([0,dom]+[v&dom for v in INPUTS])
            if z//512:vals.add(typeword(z//512-1)&dom)
            vals|={dom^v for v in vals}
            pools.append((dom,L,tuple(sorted(vals))))
    data = dict(inputs=[str(w) for w in INPUTS], target=str(TARGET), pairs=pairs,
                pools=[(str(d),L,[str(w) for w in ws]) for d,L,ws in pools])
    (TASK_DIR/'probe-data.json').write_text(json.dumps(data))
    rows = ['#pragma once', '#include <array>', '#include <cstdint>', '#include <vector>',
            'using Word = std::array<uint64_t,8>;',
            'struct PoolData { Word domain; int bound; std::vector<Word> wires; };']
    def word(n):
        return '{{'+','.join(hex((n>>(64*i))&((1<<64)-1))+'ULL' for i in range(8))+'}}'
    rows.append('const std::vector<Word> rawInputs = {'+','.join(map(word,INPUTS))+'};')
    rows.append('const Word target = '+word(TARGET)+';')
    rows.append('const std::vector<std::pair<int,int>> boundaryPairs = {'+','.join('{'+str(p)+','+str(n)+'}' for p,n in pairs)+'};')
    rows.append('const std::vector<PoolData> poolData = {'+','.join('{'+word(d)+','+str(L)+',{'+','.join(map(word,ws))+'}}' for d,L,ws in pools)+'};')
    edge_set={tuple(sorted(e)) for e in EDGES}
    degrees=[sum(i in e for e in EDGES) for i in range(9)]
    autos=[]
    groups=[[i for i,d in enumerate(degrees) if d==v] for v in sorted(set(degrees))]
    for combo in itertools.product(*(list(itertools.permutations(g)) for g in groups)):
        p=list(range(9))
        for g,perm in zip(groups,combo):
            for i,j in zip(g,perm):p[i]=j
        if {tuple(sorted((p[a],p[b]))) for a,b in EDGES}==edge_set:autos.append(p)
    rows.append('const std::vector<std::array<int,9>> automorphisms = {'+','.join('{{'+','.join(map(str,p))+'}}' for p in autos)+'};')
    print('automorphisms',len(autos),flush=True)
    all_known=[]
    for forest in (['sg'] if signed else ['mo','sg']):
        section=re.search(r'^def '+forest+r'Levels[^\n]*\n(.*?)^def ',S,re.M|re.S).group(1)
        for k,fields in re.findall(r'\| (\d+) => \(([^\n]+)\)',section):
            fields=fields.split(',')
            num,d,cw,dictionary,flags,ow,marker=map(int,fields[:7])
            func=fields[7]
            body=re.search(r'^def '+func+r'[^\n]*:= (.+)$',S,re.M).group(1)
            tokens=re.findall(r'0x[0-9a-fA-F]+|\d+|[A-Za-z]+|[()<]',body)
            def value(j):
                pos=0
                def parse():
                    nonlocal pos
                    t=tokens[pos];pos+=1
                    if t=='(':
                        v=parse();assert tokens[pos]==')';pos+=1;return v
                    if t=='if':
                        assert tokens[pos:pos+2]==['j','<'];pos+=2
                        lim=int(tokens[pos]);pos+=1
                        assert tokens[pos]=='then';pos+=1
                        a=parse();assert tokens[pos]=='else';pos+=1
                        b=parse();return a if j<lim else b
                    return int(t,0)
                ans=parse();assert pos==len(tokens);return ans
            chunks={}
            def packed(pos,n):
                i,shift=divmod(pos,8192)
                if i not in chunks:chunks[i]=value(i)
                result=chunks[i]>>shift
                if shift+n>8192:
                    if i+1 not in chunks:chunks[i+1]=value(i+1)
                    result |= chunks[i+1]<<(8192-shift)
                return result&((1<<n)-1)
            for i in range(num):
                if marker<1024:record=packed(i*(10*d+9+d),10*d+9+d)
                else:
                    prefixwidth=10*max(d-1,0)
                    base=(dictionary%65536)*prefixwidth
                    off=base+(dictionary//65536)*(9+d)+i*(flags%16+(10 if d else 0)+flags//16)
                    pre=packed(off,flags%16)
                    lastbits=10 if d else 0
                    last=packed(off+flags%16,lastbits)
                    mask=packed(off+flags%16+lastbits,flags//16)
                    record=packed(pre*prefixwidth,prefixwidth)|(last<<prefixwidth)|(packed(base+mask*(9+d),9+d)<<(10*d))
                ops=record&((1<<(10*d))-1)
                bank=INPUTS[:]
                for j in range(d):
                    code=ops>>(10*j)
                    bank.append(binary(code>>8&3,bank[code&15],bank[code>>4&15]))
                live=record>>(10*d)
                state=[w for j,w in enumerate(bank) if live>>j&1]
                assert len(state)==len(set(state)) and TARGET not in state
                all_known.append((int(k),state))
    blob=bytearray(struct.pack('<I',len(all_known)))
    for k,ws in all_known:
        blob+=struct.pack('<II',k,len(ws))
        for w in ws:blob+=w.to_bytes(64,'little')
    (TASK_DIR/(tag+'known-states.bin')).write_bytes(blob)
    rows += ['#include <fstream>', '#include <stdexcept>',
        'inline std::vector<std::pair<int,std::vector<Word>>> loadKnownStates(const char* path) {',
        'std::ifstream in(path, std::ios::binary);',
        'auto read32=[&](){ uint32_t n=0; in.read(reinterpret_cast<char*>(&n),4); return n; };',
        'uint32_t n=read32(); if(n!='+str(len(all_known))+') throw std::runtime_error("known count");',
        'std::vector<std::pair<int,std::vector<Word>>> result;',
        'for(uint32_t i=0;i<n;i++){ auto k=read32(), count=read32(); if(count>16) throw std::runtime_error("known width"); std::vector<Word> ws(count); for(auto&w:ws) in.read(reinterpret_cast<char*>(w.data()),64); result.push_back({int(k),std::move(ws)}); }',
        'if(!in) throw std::runtime_error("known file"); return result;',
        '}']
    print('knownStates',len(all_known),flush=True)
    (TASK_DIR/(tag+'probe-data.hpp')).write_text('\n'.join(rows)+'\n')

def pools_for(prefix):
    ans=[]
    for dom,L,raw in POOLS:
        states=[(frozenset(raw),0)]
        for op,a,b in prefix:
            a,b = a&dom,b&dom
            new=[]
            for vals,paid in states:
                z=binary(op,a,b)&dom
                if a in vals and b in vals and z not in vals:
                    new.append((vals|{z},paid+1))
            states += new
        ans.extend((dom,L,vals,paid) for vals,paid in states)
    return ans

def probe(depth=1):
    first=(1,INPUTS[4],INPUTS[6])
    start=tuple(sorted(INPUTS+[binary(*first)]))
    work=[(start,(first,),15)]
    for level in range(depth):
        stats=dict(states=len(work),moves=0,length=0,sep=0,redundant=0,projection=0,open=0)
        nxt={}
        for ws,prefix,k in work:
            pools=pools_for(prefix)
            covers={w:cover(w) for w in ws}
            for i,a in enumerate(ws):
                for b in ws[i+1:]:
                    rest0=[w for w in ws if w != a and w != b]
                    for op in range(2):
                        z=binary(op,a,b)
                        cz=cover(z)
                        for ka,kb in itertools.product([False,True],repeat=2):
                            stats['moves']+=1
                            rest=rest0+([a] if ka else [])+([b] if kb else [])
                            if len(rest)+1>k:
                                stats['length']+=1;continue
                            cov=cz
                            for w in rest:cov |= covers[w]
                            if cov != COVER_FULL:
                                stats['sep']+=1;continue
                            if z in ws or z in (0,FULL):
                                stats['redundant']+=1;continue
                            closed=False
                            for dom,L,vals,paid in pools:
                                zr=z&dom
                                if any(w&dom not in vals for w in rest):continue
                                extra=zr not in vals
                                constants=sum(w&dom in (0,dom) for w in rest+[z])
                                if k-1+paid+extra >= L+constants:continue
                                if extra and not(a&dom in vals and b&dom in vals):continue
                                closed=True;break
                            if closed:
                                stats['projection']+=1;continue
                            stats['open']+=1
                            child=tuple(sorted(rest+[z]))
                            nxt.setdefault(child,(child,prefix+((op,a,b),),k-1))
        print(level+1,stats,'distinct',len(nxt),flush=True)
        work=list(nxt.values())

if __name__ == '__main__':
    export(args.signed)
    print('source_sha256', hashlib.sha256(SOURCE.read_bytes()).hexdigest(), flush=True)
    print('mode', 'signed' if args.signed else 'monotone', flush=True)
