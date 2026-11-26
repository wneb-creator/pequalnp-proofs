import ast
import argparse
import itertools
import json
import re
import struct
from pathlib import Path

parser=argparse.ArgumentParser(description='Generate full Petersen signed contraction data; not a Lean proof')
parser.add_argument('--repo',required=True,type=Path)
parser.add_argument('--output',required=True,type=Path)

args=parser.parse_args()
ROOT=args.output.resolve()
ROOT.mkdir(parents=True,exist_ok=True)
SOURCE=args.repo/'lean/PEqualNP/Outside/L_meta_670.lean' 
TEXT=SOURCE.read_text()
EDGES=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
EDGESET={tuple(sorted(e)) for e in EDGES}
H9=[e for e in EDGES if 9 not in e]
INPUTS=[sum(1<<r for r in range(1024) if r>>i&1) for i in range(10)]
FULL=(1<<1024)-1
TARGET=0
for a,b in EDGES:TARGET|=INPUTS[a]&INPUTS[b]
POS=sorted((1<<a)|(1<<b) for a,b in EDGES)
NEG=[r for r in range(1024) if not(TARGET>>r&1) and all(TARGET>>(r|1<<i)&1 for i in range(10) if not(r>>i&1))]

def adjacent(a,b):return tuple(sorted((a,b))) in EDGESET
AUTOS=[]
def autos(part,unused):
    if not unused:
        AUTOS.append(part);return
    i=len(part)
    for v in unused:
        if all(adjacent(i,j)==adjacent(v,part[j]) for j in range(i)):
            autos(part+[v],[w for w in unused if w!=v])
autos([],list(range(10)))
assert len(AUTOS)==120 and AUTOS[0]==list(range(10))
ISOS=[next(p for p in AUTOS if p[9]==v) for v in range(10)]
assert all({tuple(sorted((p[a],p[b]))) for a,b in H9}=={e for e in EDGESET if p[9] not in e} for p in ISOS)

def literal(name):
    m=re.search(r'^def '+name+r'[^\n]*:= (.+)$',TEXT,re.M)
    return ast.literal_eval(m.group(1))
EXTRA=(args.repo/'lean/PEqualNP/Outside/L_meta_6581.lean').read_text()
extra=ast.literal_eval(re.search(r'^def rootSCols[^\n]*:= (.+)$',EXTRA,re.M).group(1))
COLS=list(dict.fromkeys(literal('sgC')+extra))
POOLS=[]
METADATA=[]
for v,p in enumerate(ISOS):
    def transport(mask):return sum(1<<p[i] for i in range(9) if mask>>i&1)
    for ci,col in enumerate(COLS):
        z,o,q,s,L=col
        zero=transport(z%512)|(1<<v)
        one=transport(o)
        dom=sum(1<<r for r in range(1024) if not(r&zero) and r&one==one)
        vals={0,dom}|{w&dom for w in INPUTS}
        if z//512:
            t=z//512-1
            a,b=INPUTS[p[t//9%9]],INPUTS[p[t%9]]
            val=(a&b) if t//81==0 else (a|b) if t//81==1 else (a&~b) if t//81==2 else (~a&b)
            vals.add(val&dom)
        vals|={dom^w for w in vals}
        POOLS.append((dom,L,tuple(sorted(vals))))
        METADATA.append(dict(vertex=v,isomorphism=p,column=ci,source=col,zero=zero,one=one,bound=L))
    dom=FULL^INPUTS[v]
    vals={0,dom}|{w&dom for w in INPUTS}
    vals|={dom^w for w in vals}
    POOLS.append((dom,15,tuple(sorted(vals))))
    METADATA.append(dict(vertex=v,isomorphism=p,column='whole-signed-H9',bound=15))
# Exact duplicate domains/root pools keep maximum lower bound.
unique={}
for d,L,ws in POOLS:unique[d,ws]=max(L,unique.get((d,ws),0))
POOLS=[(d,L,ws) for (d,ws),L in unique.items()]
blob=bytearray(struct.pack('<I',len(POOLS)))
for d,L,ws in POOLS:
    blob+=d.to_bytes(128,'little')+struct.pack('<II',L,len(ws))
    for w in ws:blob+=w.to_bytes(128,'little')
(ROOT/'pools.bin').write_bytes(blob)
(ROOT/'metadata.json').write_text(json.dumps(dict(autos=AUTOS,isomorphisms=ISOS,positives=POS,negatives=NEG,metadata=METADATA,pools_count=len(POOLS))))

def word(n):return '{{'+','.join(hex(n>>(64*i)&((1<<64)-1))+'ULL' for i in range(16))+'}}'
lines=['#pragma once','#include <array>','#include <vector>','#include <cstdint>','#include <fstream>','#include <stdexcept>',
       'using Word=std::array<uint64_t,16>;',
       'struct PoolData { Word domain; int bound; std::vector<Word> wires; };',
       'const std::vector<Word> rawInputs={'+','.join(map(word,INPUTS))+'};',
       'const Word target='+word(TARGET)+';',
       'const std::vector<std::pair<int,int>> boundaryPairs={'+','.join('{'+str(p)+','+str(n)+'}' for p,n in itertools.product(POS,NEG))+'};',
       'const std::vector<std::array<int,10>> automorphisms={'+','.join('{{'+','.join(map(str,p))+'}}' for p in AUTOS)+'};',
       'inline std::vector<PoolData> loadPools() {',
       'std::ifstream in("pools.bin",std::ios::binary);',
       'auto read32=[&](){uint32_t n=0;in.read(reinterpret_cast<char*>(&n),4);return n;};',
       'uint32_t n=read32();if(n!='+str(len(POOLS))+')throw std::runtime_error("poolcount"); std::vector<PoolData> out;',
       'for(uint32_t i=0;i<n;i++){PoolData p;in.read(reinterpret_cast<char*>(p.domain.data()),128);p.bound=read32();uint32_t s=read32();if(s>24)throw std::runtime_error("poolwidth");p.wires.resize(s);for(auto&w:p.wires)in.read(reinterpret_cast<char*>(w.data()),128);out.push_back(std::move(p));}',
       'if(!in)throw std::runtime_error("poolfile");return out;}',
       'const auto poolData=loadPools();',
       'const std::vector<std::pair<int,std::vector<Word>>> knownStates={};']
(ROOT/'probe-data.hpp').write_text('\n'.join(lines)+'\n')
print('autos',len(AUTOS),'boundary',len(POS),len(NEG),'signed_source_columns',len(COLS),'pools',len(POOLS))
