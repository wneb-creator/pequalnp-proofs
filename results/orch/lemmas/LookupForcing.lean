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

end LookupForcing
