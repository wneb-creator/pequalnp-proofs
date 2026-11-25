from pathlib import Path
import re
import itertools

src=Path('/workspace/pequalnp-proofs/lean/PEqualNP/Outside/L_meta_8039.lean').read_text()
code=src[src.index('namespace CoverCheck'):src.index('end CoverCheck')+len('end CoverCheck')]
mp={'7':'8','9':'11','15':'17','64':'128','127':'255','32767':'131071'}
code=re.sub(r'\b(7|9|15|64|127|32767)\b',lambda m:mp[m[0]],code)
code=code.replace('bits64','bits128')
raw=[130,132,8,16,32,64]
profiles=[154,198,180,104]
ones=255
key=lambda x:min(x,ones^x)
seeds=[key(x) for x in raw]
cells0=[(p,1<<r) for p in profiles for r in range(8) if not (p>>r)&1]
order=[0,5,9,15]+[i for i in range(len(cells0)) if i not in [0,5,9,15]]
cells=[cells0[i] for i in order]
hit=lambda c,z:c[0]&z==0 and c[1]&z!=0
coverage={z:sum(1<<i for i,c in enumerate(cells) if hit(c,z)) for z in range(256)}
opts=[[(key(z),coverage[z]) for z in range(256) if hit(c,z)] for c in cells]
priority=sorted(range(17),key=lambda i:len(opts[i]))
show=lambda xs:'['+', '.join(map(str,xs))+']'
code=re.sub(r'def raw : List M := .*', 'def raw : List M := '+show(raw),code)
code=re.sub(r'def profiles : List M := .*', 'def profiles : List M := '+show(profiles),code)
code=re.sub(r'def cells : List \(M × M\) :=\n.*', 'def cells : List (M × M) :=\n  '+show(cells),code)
def maskexpr(x):
 lo=x&((1<<64)-1);hi=x>>64
 return f'({lo} ||| ({hi} <<< 64))' if hi else str(lo)
seedmask=sum(1<<x for x in seeds)
code=re.sub(r'def seedsMask : Nat := .*','def seedsMask : Nat := '+maskexpr(seedmask),code)
pm=0
for a,b in itertools.product(seeds,repeat=2):
 for x,y in itertools.product([a,ones^a],[b,ones^b]):pm|=1<<key(x&y)
code=re.sub(r'bif Nat.beq m seedsMask then .* else prodMask m','bif Nat.beq m seedsMask then '+maskexpr(pm)+' else prodMask m',code)
def tree(lo,hi):
 vals={coverage[x] for x in range(lo,hi)}
 if len(vals)==1:return str(next(iter(vals)))
 mid=(lo+hi)//2
 return f'(bif Nat.blt z {mid} then {tree(lo,mid)} else {tree(mid,hi)})'
code=re.sub(r'def covMaskOf \(z : Nat\) : Nat :=\n.*','def covMaskOf (z : Nat) : Nat :=\n  bif Nat.ble 256 z then 0 else '+tree(0,256),code)
optlines=['def coverOptions : Nat → List (Nat × Nat)']+[f'  | {i} => {show(xs)}' for i,xs in enumerate(opts)]+['  | _ => []']
code=re.sub(r'def coverOptions : Nat → List \(Nat × Nat\).*?\n  \| _ => \[\]', '\n'.join(optlines),code,flags=re.S)
code=re.sub(r'preferUncovered cov \[.*\]','preferUncovered cov '+show(priority),code)
Path('/workspace/pequalnp-proofs/results/orch/lemmas/Certificate.lean').write_text('import PEqualNP.Defs\n\nnamespace PEqualNP.Outside.L_meta_2592_aux\n\n'+code+'\n\nend PEqualNP.Outside.L_meta_2592_aux\n')
print('Certificate generated',len(code.splitlines()),'lines',len(code),'bytes')
print('raw',raw,'seeds',seeds,'profiles',profiles,'cells',cells,'priority',priority)
