import Mathlib.Data.Nat.BinaryRec
import Mathlib.Data.List.Sublists
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3773_aux.FastInputWords

open PEqualNP.GenericRejection

def D : Finset (Fin 13) := {0,1,3,9}
def disj (s : Finset (Fin 13)) :=
  Finset.univ.filter fun l : Fin 13 => ∀ p ∈ s, p+l ∉ D
def edges := (List.finRange 13).flatMap fun p =>
  ([0,1,3,9] : List (Fin 13)).map fun d =>
    (true, incidenceInput {p} {d-p})
def small := (List.range 4).flatMap fun k =>
  ((List.finRange 13).sublistsLen k).map List.toFinset
def ordinary := small.flatMap fun s =>
  [(false, incidenceInput s (disj s)), (false, incidenceInput (disj s) s)]
def rows := edges ++ ordinary
def word (i : Fin 26) : ℕ :=
  (rows.map fun r => r.2.getD i.val false).foldr Nat.bit 0

lemma input_left {n m : ℕ} (s : Finset (Fin n)) (t : Finset (Fin m)) (i : Fin n) :
    (incidenceInput s t).getD i.val false = decide (i ∈ s) := by
  unfold incidenceInput
  rw [List.getD_append _ _ _ _ (by simpa using i.isLt)]
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp

lemma input_right {n m : ℕ} (s : Finset (Fin n)) (t : Finset (Fin m)) (i : Fin m) :
    (incidenceInput s t).getD (n+i.val) false = decide (i ∈ t) := by
  unfold incidenceInput
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp

lemma input_left_at {n m : ℕ} (s : Finset (Fin n)) (t : Finset (Fin m)) (i : Fin n) :
    (incidenceInput s t)[i.val]?.getD false = decide (i ∈ s) := by
  exact input_left s t i

lemma input_right_at {n m : ℕ} (s : Finset (Fin n)) (t : Finset (Fin m)) (i : Fin m) :
    (incidenceInput s t)[n+i.val]?.getD false = decide (i ∈ t) := by
  exact input_right s t i

def leftBits (i : Fin 13) : List Bool :=
  ((List.finRange 13).flatMap fun p =>
    ([0,1,3,9] : List (Fin 13)).map fun _ => decide (i = p)) ++
  (small.flatMap fun s =>
    [decide (i ∈ s), decide (∀ p ∈ s, p+i ∉ D)])

def rightBits (i : Fin 13) : List Bool :=
  ((List.finRange 13).flatMap fun p =>
    ([0,1,3,9] : List (Fin 13)).map fun d => decide (i = d-p)) ++
  (small.flatMap fun s =>
    [decide (∀ p ∈ s, p+i ∉ D), decide (i ∈ s)])

lemma word_left (i : Fin 13) :
    word (Fin.castAdd 13 i) = (leftBits i).foldr Nat.bit 0 := by
  unfold word rows edges ordinary leftBits
  simp only [Fin.val_castAdd, List.map_append, List.map_flatMap, List.map_map]
  congr 1
  simp [input_left_at, disj]

lemma word_right (i : Fin 13) :
    word (Fin.natAdd 13 i) = (rightBits i).foldr Nat.bit 0 := by
  unfold word rows edges ordinary rightBits
  simp only [Fin.val_natAdd, List.map_append, List.map_flatMap, List.map_map]
  congr 1
  simp [input_right_at, disj]

end PEqualNP.Outside.L_meta_3773_aux.FastInputWords
