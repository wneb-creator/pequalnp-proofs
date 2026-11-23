import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_984_aux.PseudoforestFacts
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def edges : List (Fin 7 × Fin 7) :=
  [(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(4,6)]

def graph : SimpleGraph (Fin 7) where
  Adj u v := (u,v) ∈ edges ∨ (v,u) ∈ edges
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def formula (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) ||
  (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)

theorem sparse : ∀ S : Finset (Fin 7),
    {e : Sym2 (Fin 7) | e ∈ graph.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card := by
  intro S
  have h : {e : Sym2 (Fin 7) | e ∈ graph.edgeSet ∧ ∀ v ∈ e, v ∈ S} =
      ((Finset.univ.filter fun e : Sym2 (Fin 7) =>
        e ∈ graph.edgeSet ∧ ∀ v ∈ e, v ∈ S) : Set (Sym2 (Fin 7))) := by
    ext e
    simp
  rw [h, Set.ncard_coe_finset]
  exact (by decide : ∀ S : Finset (Fin 7),
    (Finset.univ.filter fun e : Sym2 (Fin 7) =>
      e ∈ graph.edgeSet ∧ ∀ v ∈ e, v ∈ S).card ≤ S.card) S

theorem no_four : ∀ v (p : graph.Walk v v), p.IsCycle → p.length ≠ 4 := by
  intro v p hp hl
  cases p with
  | nil => simp at hl
  | @cons u a v h₀ p =>
    cases p with
    | nil => simp at hl
    | @cons a b v h₁ p =>
      cases p with
      | nil => simp at hl
      | @cons b c v h₂ p =>
        cases p with
        | nil => simp at hl
        | @cons c d v h₃ p =>
          cases p with
          | nil =>
            have hn := hp.support_nodup
            simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
              List.tail_cons] at hn
            exact (by decide : ∀ a b c d : Fin 7,
              graph.Adj a b → graph.Adj b c → graph.Adj c d → graph.Adj d a →
              ¬ [b,c,d,a].Nodup) _ _ _ _ h₀ h₁ h₂ h₃ hn
          | cons h₄ p => simp only [SimpleGraph.Walk.length_cons] at hl; omega

theorem edge_count : graph.edgeSet.ncard = 7 := by
  have h : graph.edgeSet = ((Finset.univ.filter fun e : Sym2 (Fin 7) =>
      e ∈ graph.edgeSet) : Set (Sym2 (Fin 7))) := by ext e; simp
  rw [h, Set.ncard_coe_finset]
  decide

theorem formula_eq : ∀ x : Fin 7 → Bool, formula x = true ↔
    ∃ u v, graph.Adj u v ∧ x u = true ∧ x v = true := by decide

theorem maximal_false_count :
    {x : Fin 7 → Bool | formula x = false ∧ ∀ y : Fin 7 → Bool,
      (∀ i : Fin 7, x i = true → y i = true) → formula y = false → y = x}.ncard = 9 := by
  have h : {x : Fin 7 → Bool | formula x = false ∧ ∀ y : Fin 7 → Bool,
      (∀ i : Fin 7, x i = true → y i = true) → formula y = false → y = x} =
      ((Finset.univ.filter fun x : Fin 7 → Bool => formula x = false ∧
        ∀ y : Fin 7 → Bool, (∀ i : Fin 7, x i = true → y i = true) →
          formula y = false → y = x) : Set (Fin 7 → Bool)) := by ext x; simp
  rw [h, Set.ncard_coe_finset]
  decide

end PEqualNP.Outside.L_meta_984_aux.PseudoforestFacts
