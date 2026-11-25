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

end PEqualNP.Outside.L_meta_1884.SoleOrPartner
