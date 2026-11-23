from pathlib import Path
import json,math,collections,gzip
m=json.loads(Path('Nonprefix12Manifest.json').read_text());assert [s['recipe'] for s in m['signals'][:9]]==[[i+1] for i in range(9)]
N=len(m['signals'])-9; rows={tuple(r['v']) for l in m['levels'] for r in l['records']};groups=collections.defaultdict(list)
for row in rows:
 mask=sum(1<<i for i in row if i<9);xs=[i-9 for i in row if i>=9];rank=sum(math.comb(x,j+1) for j,x in enumerate(xs));groups[mask,len(xs)].append((rank,row))
for key in groups:groups[key].sort()
chunks=[];offsets=[0];payload=0;groupwords=[];globalrows=[];metadata=[]
for (mask,n),items in sorted(groups.items()):
 width=max(1,(math.comb(N,n)-1).bit_length());start=len(globalrows);chunkstart=len(chunks)
 groupwords.append(mask|(n<<9)|(start<<11)|(chunkstart<<24));metadata.append({'mask':mask,'n':n,'start':start,'count':len(items),'chunkstart':chunkstart,'width':width})
 for at in range(0,len(items),32):
  vals=[rank for rank,row in items[at:at+32]];deltas=[b-a-1 for a,b in zip(vals,vals[1:])]
  costs=[sum((x>>k)+1+k if x>>k<7 else 7+width for x in deltas) for k in range(width+1)];k=min(range(len(costs)),key=costs.__getitem__)
  code=vals[0]|(k<<width);bits=width+5
  for d in deltas:
   q=d>>k
   if q<7:
    token=((1<<q)-1)|((d% (1<<k))<<(q+1));size=q+1+k
   else:token=127|(d<<7);size=7+width
   code|=token<<bits;bits+=size
  chunks.append({'code':code,'bits':bits,'width':width,'k':k,'ranks':vals});payload|=code<<offsets[-1];offsets.append(offsets[-1]+bits)
 for rank,row in items:globalrows.append({'mask':mask,'extras':[i for i in row if i>=9],'v':list(row),'rank':rank,'key':mask|(n<<9)|(rank<<11)})
assert len(chunks)<256 and max(offsets)<65536 and len(globalrows)<8192
rowids={tuple(r['v']):i for i,r in enumerate(globalrows)}
levels=[{'k':l['k'],'t':l['t'],'rows':sorted({rowids[tuple(r['v'])] for r in l['records']})} for l in m['levels']]
manifest={'signals':m['signals'],'rows':globalrows,'levels':levels,'groups':metadata}
Path('Cut12CodecManifest.json').write_text(json.dumps(manifest,separators=(',',':')));Path('Cut12CodecManifest.json.gz').write_bytes(gzip.compress(Path('Cut12CodecManifest.json').read_bytes(),mtime=0))
wirebits=sum(sum(t<<(4*j) for j,t in enumerate(w['recipe']))<<(28*i) for i,w in enumerate(m['signals']))
groupbits=sum(w<<(32*i) for i,w in enumerate(groupwords));offsetbits=sum(w<<(16*i) for i,w in enumerate(offsets))
data={'payload':hex(payload),'groups':hex(groupbits),'offsets':hex(offsetbits),'recipes':hex(wirebits),'wirecount':len(m['signals']),'rowcount':len(globalrows),'groupcount':len(groups),'chunkcount':len(chunks),'payloadbits':offsets[-1]}
Path('Cut12CodecData.json').write_text(json.dumps(data,separators=(',',':')))
head=f'''namespace PEqualNP.Outside.L_meta_670_aux.Cut12Data

def wireCount : Nat := {len(m['signals'])}
def rowCount : Nat := {len(globalrows)}
def groupCount : Nat := {len(groups)}

def recipeBits : Nat := 0x{wirebits:x}
def groupBits : Nat := 0x{groupbits:x}
def offsetBits : Nat := 0x{offsetbits:x}
def chunkBits : Nat := 0x{payload:x}
'''
body='''
def wireRecipe (i : Nat) : Nat := (recipeBits >>> (28*i)) % 268435456

def groupHeader (g : Nat) : Nat := (groupBits >>> (32*g)) % 4294967296

def groupStart (g : Nat) : Nat := (groupHeader g >>> 11) % 8192

def locateGroup : Nat → Nat → Nat → Nat → Nat
  | 0, _, lo, _ => lo
  | fuel+1, i, lo, hi =>
    if hi ≤ lo+1 then lo else
    let mid := (lo+hi)/2
    if groupStart mid ≤ i then locateGroup fuel i mid hi
    else locateGroup fuel i lo mid

def rankWidth : Nat → Nat
  | 1 => 10
  | 2 => 18
  | 3 => 25
  | _ => 1

def chunkOffset (i : Nat) : Nat := (offsetBits >>> (16*i)) % 65536

def chunkCode (i : Nat) : Nat :=
  let start := chunkOffset i
  (chunkBits >>> start) % ((1 : Nat) <<< (chunkOffset (i+1)-start))

def readDelta : Nat → Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, w, c, _ => (c % ((1 : Nat) <<< w), c >>> w)
  | fuel+1, k, w, c, q =>
    if c % 2 = 0 then
      ((q <<< k) + ((c >>> 1) % ((1 : Nat) <<< k)), c >>> (k+1))
    else readDelta fuel k w (c >>> 1) (q+1)

def advanceRank : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, r => r
  | count+1, k, w, c, r =>
    let z := readDelta 7 k w c 0
    advanceRank count k w z.2 (r+z.1+1)

def rankAt (chunk i n : Nat) : Nat :=
  let w := rankWidth n
  let c := chunkCode chunk
  let first := c % ((1 : Nat) <<< w)
  let k := (c >>> w) % 32
  advanceRank i k w (c >>> (w+5)) first

def smallChoose (x : Nat) : Nat → Nat
  | 1 => x
  | 2 => x*(x-1)/2
  | 3 => x*(x-1)*(x-2)/6
  | _ => 1

def locateIndex : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, lo, _ => lo
  | fuel+1, n, r, lo, hi =>
    if hi ≤ lo+1 then lo else
    let mid := (lo+hi)/2
    if smallChoose mid n ≤ r then locateIndex fuel n r mid hi
    else locateIndex fuel n r lo mid

def unrank : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | n+1, r, hi =>
    let x := locateIndex 10 (n+1) r 0 hi
    unrank n (r-smallChoose x (n+1)) x ++ [x+9]

def row (i : Nat) : Nat × List Nat :=
  if i < rowCount then
    let g := locateGroup 7 i 0 groupCount
    let h := groupHeader g
    let mask := h % 512
    let n := (h >>> 9) % 4
    let localIndex := i-groupStart g
    let chunk := (h >>> 24) % 256 + localIndex/32
    (mask, unrank n (rankAt chunk (localIndex%32) n) 546)
  else (0,[])

def wireIds (i : Nat) : List Nat :=
  let r := row i
  (List.range 9).filter (fun j => (r.1 >>> j) % 2 == 1) ++ r.2

end PEqualNP.Outside.L_meta_670_aux.Cut12Data
'''
Path('Cut12CodecBody.lean').write_text(head+body)
representatives={0,len(globalrows)-1}
for n in range(4):
 candidates=[g for g in metadata if g['n']==n]
 if candidates:
  g=max(candidates,key=lambda g:g['count']);representatives|={g['start'],g['start']+g['count']//2,g['start']+g['count']-1}
for j in range(0,len(globalrows),max(1,len(globalrows)//20)):representatives.add(j)
tests=['import Mathlib',head+body,'open PEqualNP.Outside.L_meta_670_aux.Cut12Data']
for i in sorted(representatives):tests.append(f'example : wireIds {i} = '+str(globalrows[i]['v']).replace(' ','')+' := by decide')
for i in [0,8,9,len(m['signals'])-1]:tests.append(f'example : wireRecipe {i} = 0x{sum(t<<(4*j) for j,t in enumerate(m["signals"][i]["recipe"])):x} := by decide')
Path('Cut12CodecTest.lean').write_text('\n'.join(tests)+'\n')
print('rows',len(globalrows),'wires',len(m['signals']),'groups',len(groups),'chunks',len(chunks),'payloadbits',offsets[-1],'Leanbytes',len(head+body),'tests',len(representatives)+4,'manifestgzipbytes',Path('Cut12CodecManifest.json.gz').stat().st_size)
