import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884.SoleOrPartner

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def singleton (v : Fin 10) : Fin 10 → Bool := fun j => decide (j = v)

def pair (v w : Fin 10) : Fin 10 → Bool := fun j => decide (j = v ∨ j = w)

def triple (v w u : Fin 10) : Fin 10 → Bool :=
  fun j => decide (j = v ∨ j = w ∨ j = u)

lemma witness : ∀ v : Fin 10, v ≠ 0 → ∀ w : Fin 10, w ≠ v →
    ∃ u : Fin 10, u ≠ 0 ∧ u ≠ v ∧ u ≠ w ∧
      target (pair w u) = false ∧ target (triple v w u) = true := by decide

lemma rejects_other_singleton (v : Fin 10) (hv : v ≠ 0)
    (H : (Fin 10 → Bool) → Bool)
    (hmono : ∀ x y : Fin 10 → Bool, x 0 = y 0 →
      (∀ i, x i = true → y i = true) → H x = true → H y = true)
    (hfactor : ∀ x y : Fin 10 → Bool,
      (∀ i, i ≠ v → x i = y i) →
      (x v || H x) = (y v || H y) → target x = target y)
    (w : Fin 10) (hw : w ≠ v) : H (singleton w) = false := by
  cases hh : H (singleton w)
  · rfl
  · obtain ⟨u, hu0, huv, huw, hnegative, hpositive⟩ := witness v hv w hw
    have hzero : singleton w 0 = pair w u 0 := by
      simp [singleton, pair, Ne.symm hu0]
    have hle : ∀ i, singleton w i = true → pair w u i = true := by
      intro i hi
      simp only [singleton, decide_eq_true_eq] at hi
      simp [pair, hi]
    have hp : H (pair w u) = true := hmono _ _ hzero hle hh
    have hagree : ∀ i, i ≠ v → pair w u i = triple v w u i := by
      intro i hi
      simp [pair, triple, hi]
    have hgate : (pair w u v || H (pair w u)) =
        (triple v w u v || H (triple v w u)) := by
      simp [hp, triple]
    have hbad := hfactor _ _ hagree hgate
    rw [hnegative, hpositive] at hbad
    cases hbad

lemma rejects_zero (v : Fin 10) (hv : v ≠ 0)
    (H : (Fin 10 → Bool) → Bool)
    (hmono : ∀ x y : Fin 10 → Bool, x 0 = y 0 →
      (∀ i, x i = true → y i = true) → H x = true → H y = true)
    (hfactor : ∀ x y : Fin 10 → Bool,
      (∀ i, i ≠ v → x i = y i) →
      (x v || H x) = (y v || H y) → target x = target y) :
    H (fun _ => false) = false := by
  have hex : ∀ v : Fin 10, ∃ w : Fin 10, w ≠ 0 ∧ w ≠ v := by decide
  obtain ⟨w, hw0, hwv⟩ := hex v
  have hreject := rejects_other_singleton v hv H hmono hfactor w hwv
  cases hh : H (fun _ => false)
  · rfl
  · have hzero : (false : Bool) = singleton w 0 := by
      simp [singleton, Ne.symm hw0]
    have hle : ∀ i : Fin 10, false = true → singleton w i = true := by
      simp
    have hbad := hmono (fun _ => false) (singleton w) hzero hle hh
    rw [hreject] at hbad
    cases hbad

lemma rejects_singleton (v : Fin 10) (hv : v ≠ 0)
    (H : (Fin 10 → Bool) → Bool)
    (hmono : ∀ x y : Fin 10 → Bool, x 0 = y 0 →
      (∀ i, x i = true → y i = true) → H x = true → H y = true)
    (hindependent : ∀ x y : Fin 10 → Bool,
      (∀ i, i ≠ v → x i = y i) → H x = H y)
    (hfactor : ∀ x y : Fin 10 → Bool,
      (∀ i, i ≠ v → x i = y i) →
      (x v || H x) = (y v || H y) → target x = target y)
    (w : Fin 10) : H (singleton w) = false := by
  by_cases hw : w = v
  · subst w
    have hagree : ∀ i : Fin 10, i ≠ v → singleton v i = false := by
      intro i hi
      simp [singleton, hi]
    rw [hindependent (singleton v) (fun _ => false) hagree]
    exact rejects_zero v hv H hmono hfactor
  · exact rejects_other_singleton v hv H hmono hfactor w hw


def quad (v w u z : Fin 10) : Fin 10 → Bool :=
  fun j => decide (j = v ∨ j = w ∨ j = u ∨ j = z)

def exceptional (v w u : Fin 10) : Prop :=
  (v = 1 ∧ ((w = 3 ∧ u = 9) ∨ (w = 9 ∧ u = 3) ∨
    (w = 7 ∧ u = 8) ∨ (w = 8 ∧ u = 7))) ∨
  (v = 4 ∧ ((w = 2 ∧ u = 6) ∨ (w = 6 ∧ u = 2) ∨
    (w = 7 ∧ u = 8) ∨ (w = 8 ∧ u = 7))) ∨
  (v = 5 ∧ ((w = 2 ∧ u = 6) ∨ (w = 6 ∧ u = 2) ∨
    (w = 3 ∧ u = 9) ∨ (w = 9 ∧ u = 3)))

lemma pair_witness : ∀ v : Fin 10, v ≠ 0 → ∀ w u : Fin 10,
    w ≠ u → w ≠ v → u ≠ v → target (pair w u) = false →
    exceptional v w u ∨ ∃ z : Fin 10, z ≠ 0 ∧ z ≠ v ∧
      target (triple w u z) = false ∧ target (quad v w u z) = true := by
  intro v
  fin_cases v <;> simp only [exceptional] <;> decide

lemma exceptional_zero : ∀ v w u : Fin 10, exceptional v w u →
    target (triple w u 0) = false ∧ target (quad v w u 0) = true := by
  intro v
  fin_cases v <;> simp only [exceptional] <;> decide

lemma localizes_nonedge_pair (v : Fin 10) (hv : v ≠ 0)
    (H : (Fin 10 → Bool) → Bool)
    (hmono : ∀ x y : Fin 10 → Bool, x 0 = y 0 →
      (∀ i, x i = true → y i = true) → H x = true → H y = true)
    (hindependent : ∀ x y : Fin 10 → Bool,
      (∀ i, i ≠ v → x i = y i) → H x = H y)
    (hfactor : ∀ x y : Fin 10 → Bool,
      (∀ i, i ≠ v → x i = y i) →
      (x v || H x) = (y v || H y) → target x = target y)
    (w u : Fin 10) (hnegative : target (pair w u) = false)
    (hh : H (pair w u) = true) : exceptional v w u := by
  have hsingle := rejects_singleton v hv H hmono hindependent hfactor
  have hwu : w ≠ u := by
    intro heq
    subst u
    have hp : pair w w = singleton w := by funext i; simp [pair, singleton]
    rw [hp, hsingle] at hh
    cases hh
  have hwv : w ≠ v := by
    intro heq
    subst w
    have hagree : ∀ i, i ≠ v → pair v u i = singleton u i := by
      intro i hi
      simp [pair, singleton, hi]
    rw [hindependent _ _ hagree, hsingle] at hh
    cases hh
  have huv : u ≠ v := by
    intro heq
    subst u
    have hagree : ∀ i, i ≠ v → pair w v i = singleton w i := by
      intro i hi
      simp [pair, singleton, hi]
    rw [hindependent _ _ hagree, hsingle] at hh
    cases hh
  rcases pair_witness v hv w u hwu hwv huv hnegative with hex | hother
  · exact hex
  · obtain ⟨z, hz0, hzv, hneg, hpos⟩ := hother
    have hzero : pair w u 0 = triple w u z 0 := by
      simp [pair, triple, Ne.symm hz0]
    have hle : ∀ i, pair w u i = true → triple w u z i = true := by
      intro i hi
      simp only [pair, decide_eq_true_eq] at hi
      rcases hi with hi | hi <;> simp [triple, hi]
    have hH : H (triple w u z) = true := hmono _ _ hzero hle hh
    have hagree : ∀ i, i ≠ v → triple w u z i = quad v w u z i := by
      intro i hi
      simp [triple, quad, hi]
    have hgate : (triple w u z v || H (triple w u z)) =
        (quad v w u z v || H (quad v w u z)) := by
      simp [hH, quad]
    have hbad := hfactor _ _ hagree hgate
    rw [hneg, hpos] at hbad
    cases hbad

lemma rejects_nonedge_zero_extension (v : Fin 10) (hv : v ≠ 0)
    (H : (Fin 10 → Bool) → Bool)
    (hmono : ∀ x y : Fin 10 → Bool, x 0 = y 0 →
      (∀ i, x i = true → y i = true) → H x = true → H y = true)
    (hindependent : ∀ x y : Fin 10 → Bool,
      (∀ i, i ≠ v → x i = y i) → H x = H y)
    (hfactor : ∀ x y : Fin 10 → Bool,
      (∀ i, i ≠ v → x i = y i) →
      (x v || H x) = (y v || H y) → target x = target y)
    (w u : Fin 10) (hnegative : target (pair w u) = false)
    (hh : H (pair w u) = true) : H (triple w u 0) = false := by
  have hex := localizes_nonedge_pair v hv H hmono hindependent hfactor w u hnegative hh
  obtain ⟨hneg, hpos⟩ := exceptional_zero v w u hex
  cases hH : H (triple w u 0)
  · rfl
  · have hagree : ∀ i, i ≠ v → triple w u 0 i = quad v w u 0 i := by
      intro i hi
      simp [triple, quad, hi]
    have hgate : (triple w u 0 v || H (triple w u 0)) =
        (quad v w u 0 v || H (quad v w u 0)) := by
      simp [hH, quad]
    have hbad := hfactor _ _ hagree hgate
    rw [hneg, hpos] at hbad
    cases hbad

end PEqualNP.Outside.L_meta_1884.SoleOrPartner
