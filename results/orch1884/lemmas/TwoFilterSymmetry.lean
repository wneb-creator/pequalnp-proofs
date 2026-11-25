import CanonicalTwoFilter
import PEqualNP.MetaComplexity.Helpers.PermInputs

namespace PEqualNP.Outside.L_meta_1884.TwoFilterSymmetry

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def permutation (v w : Fin 10) : Fin 10 → Fin 10 :=
  if v = 1 then
    if w = 4 then ![0,1,2,7,5,4,6,3,9,8] else id
  else if v = 4 then
    if w = 1 then ![0,5,7,2,1,4,8,9,3,6] else ![0,4,3,2,1,5,9,8,7,6]
  else
    if w = 1 then ![0,5,7,9,4,1,8,2,6,3] else ![0,4,3,8,5,1,9,2,6,7]

set_option maxRecDepth 20000 in
lemma permutation_properties : ∀ v w : Fin 10,
    (v = 1 ∨ v = 4 ∨ v = 5) → (w = 1 ∨ w = 4 ∨ w = 5) → v ≠ w →
    permutation v w 0 = 0 ∧ permutation v w v = 1 ∧ permutation v w w = 5 ∧
      Function.Injective (permutation v w) := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
lemma permutation_target : ∀ v w : Fin 10,
    (v = 1 ∨ v = 4 ∨ v = 5) → (w = 1 ∨ w = 4 ∨ w = 5) → v ≠ w →
    ∀ x : Fin 10 → Bool, SoleOrPartner.target (x ∘ permutation v w) = SoleOrPartner.target x := by
  decide

def rename (π : Fin 10 → Fin 10) (i : Nat) : Nat :=
  if hi : i < 10 then (π ⟨i, hi⟩).val else i

def lift (π : Fin 10 → Fin 10) (i : Fin 11) : Fin 11 :=
  if hi : i.val < 10 then ⟨(π ⟨i.val, hi⟩).val, by omega⟩ else i

def gate (π : Fin 10 → Fin 10) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rename π)⟩

lemma rename_raw (π : Fin 10 → Fin 10) (i : Fin 10) : rename π i.val = (π i).val := by
  simp only [rename, dite_eq_left i.isLt]

lemma rename_large (π : Fin 10 → Fin 10) (i : Nat) (hi : 10 ≤ i) : rename π i = i := by
  simp only [rename, dite_eq_right (by omega : ¬i < 10)]

lemma rename_injective (π : Fin 10 → Fin 10) (hπ : Function.Injective π) :
    Function.Injective (rename π) := by
  intro a b hab
  by_cases ha : a < 10 <;> by_cases hb : b < 10
  · simp only [rename, dite_eq_left ha, dite_eq_left hb] at hab
    have he := hπ (Fin.ext hab)
    exact congrArg Fin.val he
  · have hb' : 10 ≤ b := by omega
    rw [rename_large π b hb'] at hab
    have hr : rename π a < 10 := by simpa only [rename, dite_eq_left ha] using (π ⟨a, ha⟩).isLt
    omega
  · have ha' : 10 ≤ a := by omega
    rw [rename_large π a ha'] at hab
    have hr : rename π b < 10 := by simpa only [rename, dite_eq_left hb] using (π ⟨b, hb⟩).isLt
    omega
  · simpa only [rename, dite_eq_right ha, dite_eq_right hb] using hab

lemma rename_eq_wmap (π : Fin 10 → Fin 10) (i : Nat) :
    rename π i = Helpers.PermInputs.wmap 11 11 (lift π) i := by
  by_cases hi : i < 10
  · have hi11 : i < 11 := by omega
    simp only [rename, lift, Helpers.PermInputs.wmap, dite_eq_left hi, dite_eq_left hi11]
  · by_cases hi11 : i < 11
    · have he : i = 10 := by omega
      subst i
      rfl
    · simp only [rename, Helpers.PermInputs.wmap, dite_eq_right hi, dite_eq_right hi11]
      omega

def seed (x : Fin 10 → Bool) (i : Fin 11) : Bool :=
  if hi : i.val < 10 then x ⟨i.val, hi⟩ else !x 0

lemma input_eq (x : Fin 10 → Bool) : TwoFilterAuxBridge.input x = List.ofFn (seed x) := rfl

lemma seed_comp (π : Fin 10 → Fin 10) (h0 : π 0 = 0) (x : Fin 10 → Bool) :
    seed x ∘ lift π = seed (x ∘ π) := by
  funext i
  by_cases hi : i.val < 10
  · have hp := (π ⟨i.val, hi⟩).isLt
    simp only [Function.comp_apply, lift, seed, dite_eq_left hi, dite_eq_left hp]
  · have he : i = 10 := Fin.ext (by omega)
    subst i
    simp [Function.comp_apply, lift, seed, h0]

lemma eval_relabel (π : Fin 10 → Fin 10) (h0 : π 0 = 0) (D : Circuit) (x : Fin 10 → Bool) :
    Circuit.eval ⟨D.gates.map (gate π), rename π D.output⟩ (TwoFilterAuxBridge.input x) =
      D.eval (TwoFilterAuxBridge.input (x ∘ π)) := by
  have hg : gate π = Helpers.PermInputs.relGate 11 11 (lift π) := by
    funext g
    simp only [gate, Helpers.PermInputs.relGate]
    congr 1
    apply List.map_congr_left
    intro i _
    exact rename_eq_wmap π i
  rw [hg, rename_eq_wmap π D.output, input_eq, input_eq, ← seed_comp π h0 x]
  exact (Helpers.PermInputs.rel_fold 11 11 (lift π) D.gates _ _
    (Helpers.PermInputs.rel_init 11 11 (lift π) (seed x))).2.2 D.output

lemma away (π : Fin 10 → Fin 10) (hπ : Function.Injective π) (v : Fin 10)
    (ins : List Nat) (hv : v.val ∉ ins) : (π v).val ∉ ins.map (rename π) := by
  intro hmem
  obtain ⟨i, hi, heq⟩ := List.mem_map.mp hmem
  have he : i = v.val := rename_injective π hπ (heq.trans (rename_raw π v).symm)
  exact hv (he ▸ hi)

lemma rails_preserved (π : Fin 10 → Fin 10) (hπ : Function.Injective π) (h0 : π 0 = 0)
    (i : Nat) : rename π i ∈ Forced13Compile.rails ↔ i ∈ Forced13Compile.rails := by
  have hzero : rename π 0 = 0 := by
    change rename π (0 : Fin 10).val = 0
    rw [rename_raw, h0]
    rfl
  have hten : rename π 10 = 10 := rename_large π 10 (by decide)
  simp only [Forced13Compile.rails, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · left; exact rename_injective π hπ (h.trans hzero.symm)
    · right; exact rename_injective π hπ (h.trans hten.symm)
  · rintro (rfl | rfl)
    · exact Or.inl hzero
    · exact Or.inr hten

lemma reads_preserved (π : Fin 10 → Fin 10) (hπ : Function.Injective π) (h0 : π 0 = 0)
    (g : Gate) : ElimManyCount.reads Forced13Compile.rails (gate π g) =
      ElimManyCount.reads Forced13Compile.rails g := by
  simp only [ElimManyCount.reads, gate, List.any_map]
  congr 1
  funext i
  simp only [Function.comp_apply, rails_preserved π hπ h0]

end PEqualNP.Outside.L_meta_1884.TwoFilterSymmetry
