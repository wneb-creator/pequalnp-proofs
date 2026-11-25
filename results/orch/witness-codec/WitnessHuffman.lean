import WitnessDecoder

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
