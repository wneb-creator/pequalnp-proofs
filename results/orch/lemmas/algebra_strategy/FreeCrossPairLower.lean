import Mathlib
import PEqualNP.MetaComplexity.Helpers.Elim
import PEqualNP.MetaComplexity.Helpers.PermInputs
import PEqualNP.MetaComplexity.L102

namespace PEqualNP.Outside.L_meta_650_aux.FreeCrossPair

open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds

def f9 (x : Fin 9 → Bool) : Bool :=
  (x 0 && (x 2 || x 3 || x 5 || x 7)) ||
  (x 1 && (x 2 || x 4 || x 6 || x 8))

def f8 (x : Fin 8 → Bool) : Bool := f9 (Fin.snoc x false)
def f7 (x : Fin 7 → Bool) : Bool := f8 (Fin.snoc x false)
def f6 (x : Fin 6 → Bool) : Bool := f7 (Fin.snoc x false)
def f5 (x : Fin 5 → Bool) : Bool := f6 (Fin.snoc x false)

theorem no_eight_raw : ¬ HasCircuitSize 9 f9 8 := by
  intro h
  have h8 : HasCircuitSize 8 f8 7 :=
    Helpers.gate_elim 8 f9 false 7
      (by refine ⟨fun i => decide (i.val = 1), ?_⟩; decide)
      (by refine ⟨fun i => decide (i.val = 0 ∨ i.val = 2), fun _ => false, ?_⟩; decide)
      h
  have h7 : HasCircuitSize 7 f7 6 :=
    Helpers.gate_elim 7 f8 false 6
      (by refine ⟨fun i => decide (i.val = 0), ?_⟩; decide)
      (by refine ⟨fun i => decide (i.val = 0 ∨ i.val = 2), fun _ => false, ?_⟩; decide)
      h8
  have h6 : HasCircuitSize 6 f6 5 :=
    Helpers.gate_elim 6 f7 false 5
      (by refine ⟨fun i => decide (i.val = 1), ?_⟩; decide)
      (by refine ⟨fun i => decide (i.val = 0 ∨ i.val = 2), fun _ => false, ?_⟩; decide)
      h7
  have h5 : HasCircuitSize 5 f5 4 :=
    Helpers.gate_elim 5 f6 false 4
      (by refine ⟨fun i => decide (i.val = 0), ?_⟩; decide)
      (by refine ⟨fun i => decide (i.val = 0 ∨ i.val = 2), fun _ => false, ?_⟩; decide)
      h6
  let π : Fin 5 → Fin 5 := ![1, 3, 2, 0, 4]
  have hp := Helpers.PermInputs.relabel_size π f5 4 h5
  have eq_path : (fun x : Fin 5 → Bool => f5 (x ∘ π)) =
      (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5,
        i.val + 1 = j.val ∧ x i = true ∧ x j = true)) := by
    exact funext (by decide +kernel)
  rw [eq_path] at hp
  have := (PEqualNP.MetaComplexity.L102 5 4).mp hp
  omega

def encode (x : Fin 9 → Bool) : Fin 18 → Bool :=
  Fin.append x ![x 3 || x 4, x 3 || x 6, x 3 || x 8,
    x 5 || x 4, x 5 || x 6, x 5 || x 8,
    x 7 || x 4, x 7 || x 6, x 7 || x 8]

def witness (i : Fin 9) : Fin 9 → Bool := fun k =>
  if i.val = 0 ∨ i.val = 1 then decide (k.val = 2)
  else if i.val = 2 then decide (k.val = 0)
  else if i.val = 3 ∨ i.val = 5 ∨ i.val = 7 then
    decide (k.val = 0 ∨ k.val = 4 ∨ k.val = 6 ∨ k.val = 8)
  else decide (k.val = 1 ∨ k.val = 3 ∨ k.val = 5 ∨ k.val = 7)

theorem witness_properties : ∀ i : Fin 9,
    f9 (Function.update (witness i) i true) ≠ f9 (witness i) ∧
    ∀ k : Fin 18, k ≠ i.castAdd 9 →
      encode (Function.update (witness i) i true) k = encode (witness i) k := by
  decide +kernel

def rawIndices : Finset (Fin 18) := Finset.univ.image (Fin.castAdd 9)

theorem rawIndices_card : rawIndices.card = 9 := by
  rw [rawIndices, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact Fin.ext (congrArg (fun z : Fin 18 => z.val) h)

theorem no_eight_free_cross (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ 8)
    (hcorrect : ∀ x : Fin 9 → Bool, C.eval (List.ofFn (encode x)) = f9 x) : False := by
  set S := (Helpers.suppsFrom C.gates (Helpers.inputSupps 18)).getD C.output ∅ with hS
  have hraw : rawIndices ⊆ S := by
    intro k hk
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
    by_contra hi
    have hw := witness_properties i
    apply hw.1
    rw [← hcorrect, ← hcorrect]
    exact (Helpers.agree_wiresFrom _ _ C.gates _ _ _ (Helpers.agree_inputs _ _)).2.2
      C.output (fun j hj => hw.2 j (fun e => hi (e ▸ hj)))
  have hcard := Helpers.cnt_suppsFrom C.gates 0 (Helpers.inputSupps 18)
    hfan Helpers.cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hcard
  rw [← hS] at hcard
  have hlength : C.gates.length ≤ 8 := hsize
  have heq : S = rawIndices := by
    symm
    apply Finset.eq_of_subset_of_card_le hraw
    rw [rawIndices_card]
    omega
  let π : Fin 18 → Fin 9 := fun k => ⟨k.val % 9, Nat.mod_lt _ (by decide)⟩
  have hrel := Helpers.PermInputs.relabel_size π
    (fun x : Fin 18 → Bool => C.eval (List.ofFn x)) 8 ⟨C, hfan, hsize, fun _ => rfl⟩
  have hfun : (fun x : Fin 9 → Bool => C.eval (List.ofFn (x ∘ π))) = f9 := by
    funext x
    rw [← hcorrect]
    exact (Helpers.agree_wiresFrom _ _ C.gates _ _ _ (Helpers.agree_inputs _ _)).2.2
      C.output (by
        intro k hk
        rw [← hS, heq] at hk
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
        simp [π, encode, Fin.append, Nat.mod_eq_of_lt i.isLt])
  rw [hfun] at hrel
  exact no_eight_raw hrel

end PEqualNP.Outside.L_meta_650_aux.FreeCrossPair
