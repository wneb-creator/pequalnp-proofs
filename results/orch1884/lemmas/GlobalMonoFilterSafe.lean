import SharedFilterSafety
import DirectFilterCore

namespace PEqualNP.Outside.L_meta_1884.GlobalMonoFilterSafe

open PEqualNP.CircuitLowerBounds SoleOrPartner SharedFilter

theorem safe (v w : Fin 10) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v ≠ w)
    (H : (Fin 10 → Bool) → Bool)
    (hm : ∀ x y, (∀ i, x i = true → y i = true) → H x = true → H y = true)
    (hiv : independent v H) (hiw : independent w H) (hfv : factor v H) (hfw : factor w H) :
    ∀ x, H x = true → target x = true := by
  have hfm : fiberMono H := fun x y _ hxy => hm x y hxy
  intro x hx
  cases ht : target x
  · obtain ⟨a,b,hnegative,hpair,_,_⟩ := unsafe_pair v w hv hw hvw H hfm hiv hiw hfv hfw
      (support x) (by simpa only [point_support] using ht)
      (by simpa only [point_support] using hx)
    have hfalse := rejects_nonedge_zero_extension v hv H hfm hiv hfv a b hnegative hpair
    have htrue : H (triple a b 0) = true := by
      apply hm (pair a b) (triple a b 0) _ hpair
      intro i hi
      simp only [pair,decide_eq_true_eq] at hi
      rcases hi with hi | hi <;> simp [triple,hi]
    rw [hfalse] at htrue
    cases htrue
  · rfl

def positiveSeed (x : Fin 10 → Bool) : List Bool := List.ofFn x ++ [false]

lemma seed_agree (x : Fin 10 → Bool) :
    SoleReader.agree 10 (DirectFilter.seed x) (positiveSeed x) := by
  refine ⟨by simp [DirectFilter.seed,positiveSeed],by simp [DirectFilter.seed],?_⟩
  intro i hi
  change (List.ofFn x ++ [!x 0]).getD i false = (List.ofFn x ++ [false]).getD i false
  by_cases hil : i < 10
  · rw [List.getD_append _ _ _ _ (by simpa using hil),
      List.getD_append _ _ _ _ (by simpa using hil)]
  · rw [List.getD_eq_default _ _ (by simp;omega),
      List.getD_eq_default _ _ (by simp;omega)]

lemma operand_fixed_free (pre : List Gate) (ins : List Nat)
    (away : ∀ g ∈ pre, 10 ∉ g.inputs) (hi : 10 ∉ ins) (x : Fin 10 → Bool) :
    DirectFilter.operand pre ins x =
      (ins.map fun i => (SoleReader.run pre (positiveSeed x)).getD i false).headD false := by
  apply congrArg (fun bs : List Bool => bs.headD false)
  apply List.map_congr_left
  intro i his
  exact SoleReader.partner_independent pre _ _ (seed_agree x) away
    (fun he => hi (he ▸ his))

theorem operand_mono (pre : List Gate) (ins : List Nat)
    (allowed : ∀ g ∈ pre, g.op = .and ∨ g.op = .or)
    (away : ∀ g ∈ pre, 10 ∉ g.inputs) (hi : 10 ∉ ins)
    (x y : Fin 10 → Bool) (hxy : ∀ i, x i = true → y i = true) :
    DirectFilter.operand pre ins x = true → DirectFilter.operand pre ins y = true := by
  have hinput : SafeNot.above (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp,?_⟩
    intro i
    by_cases hlt : i < 10
    · simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hlt,dite_true,Option.getD_some]
      exact Bool.le_iff_imp.mpr (hxy ⟨i,hlt⟩)
    · rw [List.getD_eq_default _ _ (by simp;omega),
        List.getD_eq_default _ _ (by simp;omega)]
  have hseed : SafeNot.above (positiveSeed x) (positiveSeed y) :=
    SafeNot.append_above hinput le_rfl
  have hr := SafeNot.run_above pre _ _ hseed allowed
  rw [operand_fixed_free pre ins away hi x,operand_fixed_free pre ins away hi y]
  cases ins with
  | nil => simp
  | cons i rest => exact Bool.le_iff_imp.mp (hr.2 i)

end PEqualNP.Outside.L_meta_1884.GlobalMonoFilterSafe
