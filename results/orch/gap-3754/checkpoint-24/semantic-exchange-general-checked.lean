import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3754.Exchange

open PEqualNP.EdgeOwnership

def ors {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

def dirty {n : ℕ} (A : Finset (Fin n)) (v m : Fin n) (x : Fin n → Bool) : Bool :=
  ors A x && (x v || x m)

lemma dirty_expansion {n : ℕ} (A : Finset (Fin n)) (v m : Fin n) (hv : v ∈ A)
    (x : Fin n → Bool) : dirty A v m x = (x v || (x m && ors A x)) := by
  cases he : x v
  · simp [dirty,he,Bool.and_comm]
  · have ha : ors A x = true := decide_eq_true ⟨v,hv,he⟩
    simp [dirty,he,ha]

lemma three_support_pair_false {n : ℕ} (A Z : Finset (Fin n)) (m p q : Fin n)
    (hmA : m ∉ A) (hmZ : m ∉ Z) (hAZ : Disjoint A Z) :
    (pairInput p q m && ors A (pairInput p q) && ors Z (pairInput p q)) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [Bool.and_eq_true, ors, decide_eq_true_eq, pairInput] at h
  obtain ⟨⟨hmpq,a,ha,hapq⟩,z,hz,hzpq⟩ := h
  have haz : a ≠ z := by
    intro he
    exact Finset.disjoint_left.mp hAZ ha (he ▸ hz)
  rcases hmpq with rfl | rfl
  · have hap : a ≠ m := fun e => hmA (e ▸ ha)
    have hzp : z ≠ m := fun e => hmZ (e ▸ hz)
    exact haz ((hapq.resolve_left hap).trans (hzpq.resolve_left hzp).symm)
  · have haq : a ≠ m := fun e => hmA (e ▸ ha)
    have hzq : z ≠ m := fun e => hmZ (e ▸ hz)
    exact haz ((hapq.resolve_right haq).trans (hzpq.resolve_right hzq).symm)

lemma dirty_edge_bypass {n : ℕ} (A Z : Finset (Fin n)) (v m p q : Fin n)
    (hv : v ∈ A) (hmA : m ∉ A) (hmZ : m ∉ Z) (hAZ : Disjoint A Z) :
    (dirty A v m (pairInput p q) && ors Z (pairInput p q)) =
      (pairInput p q v && ors Z (pairInput p q)) := by
  rw [dirty_expansion A v m hv]
  have h := three_support_pair_false A Z m p q hmA hmZ hAZ
  cases hvx : pairInput p q v <;> cases hmx : pairInput p q m <;>
    cases hax : ors A (pairInput p q) <;> cases hzx : ors Z (pairInput p q) <;> simp_all

lemma dirty_full_lift {n : ℕ} (A Z : Finset (Fin n)) (v m : Fin n)
    (hv : v ∈ A) (hmZ : m ∈ Z) (x : Fin n → Bool) :
    (dirty A v m x && ors Z x) = ((x v && ors Z x) || (x m && ors A x)) := by
  rw [dirty_expansion A v m hv]
  have hm : x m = true → ors Z x = true := fun hx => decide_eq_true ⟨m,hmZ,hx⟩
  cases hvx : x v <;> cases hmx : x m <;> cases hax : ors A x <;> cases hzx : ors Z x <;> simp_all

lemma restore_function {n : ℕ} (v m : Fin n)
    (F A Anew D H : (Fin n → Bool) → Bool)
    (hD : ∀ x, D x = (A x && (x v || x m)))
    (hA : ∀ x, x v = false → Anew x = A x)
    (hzero : ∀ x, x v = false → D x = false → H x = F x)
    (hmiddle : ∀ x, x v = true → x m = false → F x = true → H x = true)
    (hboth : ∀ x, x v = true → x m = true → H x = true)
    (hH : ∀ x, H x = true → F x = true)
    (hlift : ∀ x, x m = true → Anew x = true → F x = true) :
    ∀ x, F x = (H x || (x m && Anew x)) := by
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hF
    simp only [Bool.or_eq_true]
    cases hv : x v
    · cases hd : D x
      · left
        rw [hzero x hv hd]
        exact hF
      · right
        have h := hD x
        rw [hv,hd] at h
        have hmA : A x = true ∧ x m = true := by
          simpa only [Bool.false_or,Bool.and_eq_true] using h.symm
        rw [hmA.2,hA x hv,hmA.1]
        rfl
    · cases hm : x m
      · left; exact hmiddle x hv hm hF
      · left; exact hboth x hv hm
  · intro h
    have h' : H x = true ∨ (x m = true ∧ Anew x = true) := by
      simpa only [Bool.or_eq_true,Bool.and_eq_true] using h
    rcases h' with h | ⟨hm,ha⟩
    · exact hH x h
    · exact hlift x hm ha

lemma pair_witness_both {n : ℕ} (v m : Fin n) (H : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → H x = true → H y = true)
    (hpair : H (pairInput v m) = true) :
    ∀ x, x v = true → x m = true → H x = true := by
  intro x hv hm
  apply hmono (pairInput v m) x ?_ hpair
  intro i hi
  simp only [pairInput,decide_eq_true_eq] at hi
  rcases hi with rfl | rfl <;> assumption

lemma triple_pair_forces_partner {n : ℕ} (A B Z : Finset (Fin n)) (v m p q : Fin n)
    (hAB : ∀ a∈A,a∈B → a=v) (hAZ : Disjoint A Z)
    (hBZ : ∀ b∈B,b∈Z → b=m) (hv : pairInput p q v=false)
    (hA : ors A (pairInput p q)=true) (hB : ors B (pairInput p q)=true)
    (hZ : ors Z (pairInput p q)=true) : pairInput p q m=true := by
  obtain ⟨a,ha,hax⟩ := of_decide_eq_true hA
  obtain ⟨b,hb,hbx⟩ := of_decide_eq_true hB
  obtain ⟨z,hz,hzx⟩ := of_decide_eq_true hZ
  have hab : a≠b := by
    intro he
    have hav := hAB a ha (he.symm ▸ hb)
    rw [hav,hv] at hax
    cases hax
  have haz : a≠z := by
    intro he
    exact Finset.disjoint_left.mp hAZ ha (he.symm ▸ hz)
  have ha' : a=p ∨ a=q := by simpa only [pairInput,decide_eq_true_eq] using hax
  have hb' : b=p ∨ b=q := by simpa only [pairInput,decide_eq_true_eq] using hbx
  have hz' : z=p ∨ z=q := by simpa only [pairInput,decide_eq_true_eq] using hzx
  have hbz : b=z := by
    rcases ha' with rfl | rfl
    · rcases hb' with rfl | rfl
      · exact (hab rfl).elim
      · rcases hz' with rfl | rfl
        · exact (haz rfl).elim
        · rfl
    · rcases hb' with rfl | rfl
      · rcases hz' with rfl | rfl
        · rfl
        · exact (haz rfl).elim
      · exact (hab rfl).elim
  have hbm : b=m := hBZ b hb (hbz.symm ▸ hz)
  simpa only [hbm] using hbx

end PEqualNP.Outside.L_meta_3754.Exchange
