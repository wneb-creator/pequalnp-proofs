import Init

namespace LookupForcing

def forceWord {α : Type} (n : Nat) (f : Nat → α) : α :=
  Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n

theorem forceWord_eq {α : Type} (n : Nat) (f : Nat → α) : forceWord n f = f n := by
  cases n <;> rfl

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

def lookupBase (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

def lookupFast (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  forceWord h fun h =>
  forceWord (packedAt data ((h % nb)*sw) sw) fun sh =>
  forceWord ((h/nb+sh) % slots) fun row =>
  forceWord (packedAt data (nb*sw+row*vw) vw) fun word =>
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

theorem lookupFast_eq (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) :
    lookupFast nb slots sw vw iw pw data h = lookupBase nb slots sw vw iw pw data h := by
  simp only [lookupFast, forceWord_eq]
  rfl



def benchData (_i : Nat) : Nat := 0x71198115833604b01a0000606e88fc000242d7c1fb0faad280000000907200000000000000000011a60000c095e07a03c80000000207200b0000f0374218000083d74340000000000010fe000191d800038c8000000000050001a19c0000000f0d80002417105f0001002bc08ec1b0001e12c0000000f0e7e92d81a6801000081e2997c07b60460002f86e047b093591c0b42863642440b4814a40900000001016701f80992cbb0308000c10b416439d943b147aae0000000140000000051cc437e4b4604d43368120000516302b9f1000004067d0c8043000061b56b100000c580000000783f104c0003fbb80009070d07382c4f54000000014a410460001715080ea8740833a5880002404721a41d7010e870e0a6000041e7802d68a0000000000000016605c32d9336823a9a000d7e20d86d416e10a400828f5440c813b83e60a220d8fa1581020e4099e8197842301210c9aa808357404e01fd304041e1023c6482e6b2cf063e21e71a6056370a003201825400056b139c293c35f0f8311d9031132ca772115827b06218a0203561cf86910f5a5f4b8b233b382b58ee49dec3300d7802d8c0502fd10109b0c0a907ee0a0fc274022d3a10d5060b108505d001d3c31732301838cca1790204071480aad97c1b8000509cd0a402a9482901e3171c30000064ac78e80004854e040ddec841106f32a0420d715820cb2810092535383b24a5005e83218280109ecf40006a47e0540003c1d6c17800c84f7001b077b0900001c268000e088000143b221e2f0000390d00040c17340800211f04000c3852005c082b04030102880201024c3d0e17000f0511410100573e04001200070500016400040b010407000d00010204010004000a010e07000000003720
def benchHash (i : Nat) := ((List.range 6).map fun j => let n := i*(j+7)+12345678901; (n*n+971*n)%2305843009213693951).sum

def checksum := (List.range 3000).foldl (fun acc i => match lookupFast 79 299 8 15 8 3 benchData (benchHash i) with
  | none => acc
  | some (a,b) => acc+1+a+b) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem benchmark : checksum = 10491 := by decide +kernel
end LookupForcing
