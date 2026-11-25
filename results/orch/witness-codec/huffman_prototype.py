from collections import Counter
import heapq
import hashlib
import json
from pathlib import Path
import prototype

ROOT=Path(__file__).resolve().parent
DATA=Path('/tmp/oec/pequalnp-pilot-87/library_route/mono18-weak-dag/shortlist-witness-candidate.bin').read_bytes()
assert hashlib.sha256(DATA).hexdigest()=='c99a645e1337e3ea0a04cda950552dfad549fd5c8e99be53449eff465c4f7650'
raw=[DATA[i:i+32768]for i in range(0,len(DATA),32768)]
chunks=[prototype.encode(x)for x in raw]
frequencies=Counter(b for _,packed in chunks for b in packed)
heap=[(freq,byte,byte)for byte,freq in frequencies.items()]
heapq.heapify(heap)
serial=256
while len(heap)>1:
    left=heapq.heappop(heap);right=heapq.heappop(heap)
    heapq.heappush(heap,(left[0]+right[0],serial,(left[2],right[2])))
    serial+=1
nodes=[]
codes={}
def tree(node,code=0,length=0):
    if isinstance(node,int):
        codes[node]=(code,length)
        return 512+node
    index=len(nodes);nodes.append(None)
    left=tree(node[0],code,length+1)
    right=tree(node[1],code|(1<<length),length+1)
    nodes[index]=(left,right)
    return index
assert tree(heap[0][2])==0
packed_tree=sum((a|(b<<10))<<(20*i)for i,(a,b)in enumerate(nodes))
def pack(data):
    result=0;bits=0
    for byte in data:
        code,length=codes[byte]
        result|=code<<bits;bits+=length
    return result,bits
encoded=[pack(packed)for _,packed in chunks]
def unpack(packed,length):
    result=[]
    for _ in range(length):
        node=0
        while node<512:
            node=nodes[node][packed&1];packed>>=1
        result.append(node-512)
    return bytes(result)
for (_,before),(after,_)in zip(chunks,encoded):assert unpack(after,len(before))==before
decoder='''import WitnessDecoder

namespace PEqualNP.Outside.L_meta_2373.WitnessCodec

def huffByte (tree : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, bits, _ => (0, bits)
  | fuel + 1, bits, node =>
    let child := (tree >>> (20 * node + 10 * (bits &&& 1))) &&& 1023
    if 512 ≤ child then (child - 512, bits >>> 1)
    else huffByte tree fuel (bits >>> 1) child

def huffBytes (tree : Nat) : Nat → Nat → Nat → Nat → Nat × Nat
  | 0, bits, _, out => (out, bits)
  | fuel + 1, bits, count, out =>
    let byte := huffByte tree 16 bits 0
    huffBytes tree fuel byte.2 (count + 1) (out ||| (byte.1 <<< (8 * count)))

def decodeHuff (tree : Nat) : Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, count, out => (count, out)
  | fuel + 1, bits, count, out =>
    let header := huffByte tree 16 bits 0
    if header.1 < 128 then
      let size := header.1 + 1
      let bytes := huffBytes tree size header.2 0 0
      decodeHuff tree fuel bytes.2 (count + size) (out ||| (bytes.1 <<< (8 * count)))
    else
      let size := header.1 - 128 + 3
      let distance := huffBytes tree 2 header.2 0 0
      decodeHuff tree fuel distance.2 (count + size) (copyBytes distance.1 size count out)

end PEqualNP.Outside.L_meta_2373.WitnessCodec
'''
(ROOT/'WitnessHuffman.lean').write_text(decoder)
payload='import WitnessHuffman\n\nnamespace PEqualNP.Outside.L_meta_2373.WitnessCodec\n\ndef tree : Nat := '+hex(packed_tree)+'\n\ndef payload : List (Nat × Nat) := ['+','.join('('+str(command)+','+hex(value)+')'for (command,_),(value,_)in zip(chunks,encoded))+']\n\nend PEqualNP.Outside.L_meta_2373.WitnessCodec\n'
(ROOT/'ShortlistHuffmanPayload.lean').write_text(payload)
benchmark='import WitnessHuffman\n\nnamespace PEqualNP.Outside.L_meta_2373.WitnessCodec\n\ndef tree : Nat := '+hex(packed_tree)+'\n\ndef actual : Nat × Nat := ('+str(chunks[0][0])+','+hex(encoded[0][0])+')\n\ndef expected : Nat × Nat := (32768,0x'+raw[0][::-1].hex().lstrip('0')+')\n\nset_option maxRecDepth 65536 in\nset_option maxHeartbeats 0 in\nlemma decoded : decodeHuff tree actual.1 actual.2 0 0 = expected := by\n  decide +kernel\n\nend PEqualNP.Outside.L_meta_2373.WitnessCodec\n'
(ROOT/'ShortlistHuffmanBenchmark32768.lean').write_text(benchmark)
result=dict(input_bytes=len(DATA),input_sha256=hashlib.sha256(DATA).hexdigest(),chunks=len(chunks),tree_internal_nodes=len(nodes),tree_packed_bits=packed_tree.bit_length(),max_code_length=max(v[1]for v in codes.values()),lz_bytes=sum(len(x[1])for x in chunks),huffman_bits=sum(x[1]for x in encoded),payload_source_bytes=len(payload.encode()),decoder_source_bytes=len(decoder.encode()),base_decoder_source_bytes=len(prototype.DECODER.encode()),benchmark_source_bytes=len(benchmark.encode()),scope='Complete candidate bytes roundtrip in Python; Lean finite equality benchmark only first32768bytes. Not a complete search certificate.')
(ROOT/'huffman-report.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
