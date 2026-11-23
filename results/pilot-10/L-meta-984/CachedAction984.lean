import Mathlib

namespace PEqualNP.Outside.L_meta_984.Cached

def cachedAction (keys values : Nat → Nat) (count : Nat) (lookup : Nat → Nat)
    (fallback : Nat → Nat) (w : Nat) : Nat :=
  let i := lookup w
  if i < count ∧ keys i = w then values i else fallback w

theorem cachedAction_eq (keys values : Nat → Nat) (count : Nat) (lookup : Nat → Nat)
    (fallback : Nat → Nat) (hcorrect : ∀ i < count, values i = fallback (keys i))
    (w : Nat) : cachedAction keys values count lookup fallback w = fallback w := by
  unfold cachedAction
  dsimp only
  split
  · rename_i h
    rw [hcorrect _ h.1, h.2]
  · rfl

theorem cachedAction_function (keys values : Nat → Nat) (count : Nat) (lookup : Nat → Nat)
    (fallback : Nat → Nat) (hcorrect : ∀ i < count, values i = fallback (keys i)) :
    cachedAction keys values count lookup fallback = fallback := by
  funext w
  exact cachedAction_eq keys values count lookup fallback hcorrect w

theorem map_cachedAction (keys values : Nat → Nat) (count : Nat) (lookup : Nat → Nat)
    (fallback : Nat → Nat) (hcorrect : ∀ i < count, values i = fallback (keys i))
    (ws : List Nat) :
    ws.map (cachedAction keys values count lookup fallback) = ws.map fallback := by
  rw [cachedAction_function keys values count lookup fallback hcorrect]

theorem cachedAction_preserves (keys values : Nat → Nat) (count : Nat) (lookup : Nat → Nat)
    (fallback : Nat → Nat) (hcorrect : ∀ i < count, values i = fallback (keys i))
    (P : List Nat → Prop) (ws : List Nat) (h : P (ws.map fallback)) :
    P (ws.map (cachedAction keys values count lookup fallback)) := by
  rw [map_cachedAction keys values count lookup fallback hcorrect]
  exact h

end PEqualNP.Outside.L_meta_984.Cached
