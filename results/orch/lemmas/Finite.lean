import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_670.FiniteChunk

def chunkSize {α : Type} (chunks : List (Nat × α)) : Nat :=
  (chunks.map Prod.fst).sum

def checkChunks {α : Type} (check : Nat → Nat → α → Bool) (start : Nat) :
    List (Nat × α) → Bool
  | [] => true
  | (n, w) :: rest => check start n w && checkChunks check (start + n) rest

lemma checkChunks_sound {α : Type} (holds : Nat → Nat → Prop)
    (check : Nat → Nat → α → Bool)
    (empty : ∀ start, holds start 0)
    (merge : ∀ start a b, holds start a → holds (start + a) b → holds start (a + b))
    (sound : ∀ start n w, check start n w = true → holds start n)
    (chunks : List (Nat × α)) (start : Nat)
    (h : checkChunks check start chunks = true) : holds start (chunkSize chunks) := by
  induction chunks generalizing start with
  | nil => exact empty start
  | cons chunk rest ih =>
    rcases chunk with ⟨n, w⟩
    change check start n w && checkChunks check (start + n) rest = true at h
    obtain ⟨first, tail⟩ := Bool.and_eq_true_iff.mp h
    exact merge start n (chunkSize rest) (sound start n w first) (ih (start + n) tail)

def checkLevels {α : Type} (size : Nat → Nat)
    (check : Nat → Nat → Nat → α → Bool) (chunks : Nat → List (Nat × α)) (top : Nat) :=
  (List.range (top + 1)).all fun k =>
    decide (chunkSize (chunks k) = size k) && checkChunks (check k) 0 (chunks k)

lemma checkLevels_sound {α : Type} (holds : Nat → Nat → Nat → Prop)
    (size : Nat → Nat) (check : Nat → Nat → Nat → α → Bool)
    (empty : ∀ k start, holds k start 0)
    (merge : ∀ k start a b, holds k start a → holds k (start + a) b → holds k start (a + b))
    (sound : ∀ k start n w, check k start n w = true → holds k start n)
    (chunks : Nat → List (Nat × α)) (top : Nat)
    (h : checkLevels size check chunks top = true) :
    ∀ k ≤ top, holds k 0 (size k) := by
  intro k hk
  have tested := List.all_eq_true.mp h k (List.mem_range.mpr (by omega))
  obtain ⟨count, pass⟩ := Bool.and_eq_true_iff.mp tested
  have eq : chunkSize (chunks k) = size k := of_decide_eq_true count
  rw [← eq]
  exact checkChunks_sound (holds k) (check k) (empty k) (merge k) (sound k) (chunks k) 0 pass

end PEqualNP.Outside.L_meta_670.FiniteChunk
