import Mathlib.Data.List.Basic

namespace PEqualNP.Outside.L_meta_2373.WitnessCodec

def copyBytes (distance : Nat) : Nat → Nat → Nat → Nat
  | 0, _, out => out
  | remaining + 1, count, out =>
    let byte := (out >>> (8 * (count - distance))) &&& 255
    copyBytes distance remaining (count + 1) (out ||| (byte <<< (8 * count)))

def decode : Nat → Nat → Nat → Nat → Nat × Nat
  | 0, _, count, out => (count, out)
  | fuel + 1, packed, count, out =>
    let header := packed &&& 255
    if header < 128 then
      let size := header + 1
      let bytes := (packed >>> 8) &&& ((1 <<< (8 * size)) - 1)
      decode fuel (packed >>> (8 * (size + 1))) (count + size)
        (out ||| (bytes <<< (8 * count)))
    else
      let size := header - 128 + 3
      let distance := (packed >>> 8) &&& 65535
      decode fuel (packed >>> 24) (count + size) (copyBytes distance size count out)

def decodeItem (item : Nat × Nat) : Nat × Nat := decode item.1 item.2 0 0

end PEqualNP.Outside.L_meta_2373.WitnessCodec
