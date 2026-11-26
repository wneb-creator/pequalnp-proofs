import Checker

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18
open PEqualNP.Outside.L_meta_6581

def essentialRows (i : Fin 10) : Extended.Row × Extended.Row :=
  ([(640, 128), (640, 512), (160, 128), (288, 32), (576, 512), (528, 512), (132, 128), (33, 32), (264, 256), (66, 64)] : List (Extended.Row × Extended.Row)).getD i.val (0,0)

set_option maxRecDepth 8192 in
lemma essential_checked : ∀ i : Fin 10,
    (Extended.bit (essentialRows i).1 Extended.target !=
      Extended.bit (essentialRows i).2 Extended.target) &&
    Extended.initial.all (fun a =>
      (Extended.bit (essentialRows i).1 a == Extended.bit (essentialRows i).2 a) ||
      a == Extended.pins.getD i.val Extended.zero) = true := by
  decide +kernel

lemma initial_required {k : Nat} {S : Finset Word}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) : S = Extended.initial.toFinset := by
  apply Finset.Subset.antisymm
  · intro a ha
    exact List.mem_toFinset.mpr (raw a ha)
  · intro a ha
    obtain ⟨i,rfl⟩ := (Cofactor.pin_mem a).mp (List.mem_toFinset.mp ha)
    have checked := essential_checked i
    simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,decide_eq_true_eq] at checked
    obtain ⟨b,hb,diff⟩ := Extended.live_row_difference run checked.1
    have chk := checked.2 b (raw b hb)
    simp only [Bool.or_eq_true,beq_iff_eq] at chk
    exact (chk.resolve_left diff) ▸ hb

lemma atLeastEighteen (closed : Impossible Extended.target 17 Extended.initial)
    {k : Nat} {S : Finset Word} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) : 18 ≤ k := by
  by_contra! small
  rw [initial_required run raw] at run
  exact closed k (by omega) run

end PEqualNP.Outside.L_meta_2373_aux.Cert18
