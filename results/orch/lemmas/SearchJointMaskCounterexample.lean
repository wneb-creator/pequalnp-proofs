import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.SearchJointMaskCounterexample

abbrev Input := Fin 6 → Bool

def host (x : Input) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 3) ||
    (x 1 && x 5) || (x 2 && x 3)

def first (x : Input) : Bool := (x 0 || x 1) && (x 3 || x 4)

def second (x : Input) : Bool := (x 1 || x 2) && (x 3 || x 5)

def pair (i j : Fin 6) : Input := fun v => decide (v = i ∨ v = j)

def Adj (i j : Fin 6) : Prop := host (pair i j) = true

lemma host_bipartite : ∀ i j : Fin 6, Adj i j → (i.val < 3 ↔ ¬ j.val < 3) := by
  unfold Adj
  decide

lemma host_c4_free : ∀ a b c d : Fin 6, a ≠ b → c ≠ d →
    Adj a c → Adj a d → Adj b c → Adj b d → False := by
  unfold Adj
  decide

def Below (f : Input → Bool) : Prop := ∀ x, f x = true → host x = true

def masked (f : Input → Bool) (c : Fin 6) (x : Input) : Bool := f x && x c

lemma disjoint_operand_sets :
    Disjoint ({0, 1} : Finset (Fin 6)) {3, 4} ∧
    Disjoint ({1, 2} : Finset (Fin 6)) {3, 5} := by decide

lemma first_dirty : first (pair 1 4) = true ∧ host (pair 1 4) = false := by decide

lemma second_dirty : second (pair 2 5) = true ∧ host (pair 2 5) = false := by decide

lemma joint_below : Below (fun x => first x && second x) := by
  unfold Below
  decide

lemma joint_productive : (first (pair 1 3) && second (pair 1 3)) = true := by decide

lemma clean_masks : Below (masked first 0) ∧ Below (masked first 3) ∧
    Below (masked second 1) ∧ Below (masked second 3) := by
  unfold Below
  decide

def Contributed (i j : Fin 6) : Prop :=
  (∃ c, Below (masked first c) ∧ masked first c (pair i j) = true) ∨
  (∃ c, Below (masked second c) ∧ masked second c (pair i j) = true)

lemma three_disjoint_edges : Contributed 0 4 ∧ Contributed 1 5 ∧ Contributed 2 3 := by
  refine ⟨Or.inl ⟨0, clean_masks.1, ?_⟩,
    Or.inr ⟨1, clean_masks.2.2.1, ?_⟩, Or.inr ⟨3, clean_masks.2.2.2, ?_⟩⟩ <;> decide

lemma uncovered_matching : ∀ a b : Fin 6, ∃ i j : Fin 6,
    ((i = 0 ∧ j = 4) ∨ (i = 1 ∧ j = 5) ∨ (i = 2 ∧ j = 3)) ∧
    i ≠ a ∧ i ≠ b ∧ j ≠ a ∧ j ≠ b := by decide

lemma no_two_vertex_cover : ¬ ∃ a b : Fin 6,
    ∀ i j, Contributed i j → i = a ∨ i = b ∨ j = a ∨ j = b := by
  rintro ⟨a, b, hc⟩
  obtain ⟨i, j, hij, hia, hib, hja, hjb⟩ := uncovered_matching a b
  have he : Contributed i j := by
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact three_disjoint_edges.1
    · exact three_disjoint_edges.2.1
    · exact three_disjoint_edges.2.2
  rcases hc i j he with h | h | h | h
  · exact hia h
  · exact hib h
  · exact hja h
  · exact hjb h

end PEqualNP.Outside.L_meta_1477.SearchJointMaskCounterexample
