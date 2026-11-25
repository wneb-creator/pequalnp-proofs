import SharedFilter

namespace PEqualNP.Outside.L_meta_1884.SharedFilter

open Finset SoleOrPartner

def support (x : Fin 10 → Bool) : Finset (Fin 10) := univ.filter (fun i => x i = true)

lemma point_support (x : Fin 10 → Bool) : point (support x) = x := by
  funext i
  cases hi : x i <;> simp [point, support, hi]

lemma exceptional_vertex (v a b : Fin 10) (h : exceptional v a b) :
    v = 1 ∨ v = 4 ∨ v = 5 := by
  rcases h with h | h | h
  · exact Or.inl h.1
  · exact Or.inr (Or.inl h.1)
  · exact Or.inr (Or.inr h.1)

lemma no_three_exceptional (v w z a b : Fin 10)
    (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (hv : exceptional v a b) (hw : exceptional w a b) (hz : exceptional z a b) : False := by
  unfold exceptional at hv hw hz
  omega

theorem safe_if_filter_not_neighbor (v w : Fin 10)
    (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hvw : v ≠ w)
    (hv1 : v ≠ 1) (hv4 : v ≠ 4) (hv5 : v ≠ 5)
    (H : (Fin 10 → Bool) → Bool) (hm : fiberMono H)
    (hiv : independent v H) (hiw : independent w H)
    (hfv : factor v H) (hfw : factor w H) :
    ∀ x : Fin 10 → Bool, H x = true → target x = true := by
  intro x hx
  cases ht : target x
  · obtain ⟨a, b, _, _, hve, _⟩ := unsafe_pair v w hv0 hw0 hvw H hm hiv hiw hfv hfw
      (support x) (by simpa only [point_support] using ht)
      (by simpa only [point_support] using hx)
    rcases exceptional_vertex v a b hve with h | h | h
    · exact False.elim (hv1 h)
    · exact False.elim (hv4 h)
    · exact False.elim (hv5 h)
  · rfl

theorem safe_if_three_filters (v w z : Fin 10)
    (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hz0 : z ≠ 0)
    (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z)
    (H : (Fin 10 → Bool) → Bool) (hm : fiberMono H)
    (hiv : independent v H) (hiw : independent w H) (hiz : independent z H)
    (hfv : factor v H) (hfw : factor w H) (hfz : factor z H) :
    ∀ x : Fin 10 → Bool, H x = true → target x = true := by
  intro x hx
  cases ht : target x
  · obtain ⟨a, b, hneg, hH, hve, hwe⟩ := unsafe_pair v w hv0 hw0 hvw H hm hiv hiw hfv hfw
      (support x) (by simpa only [point_support] using ht)
      (by simpa only [point_support] using hx)
    have hze := localizes_nonedge_pair z hz0 H hm hiz hfz a b hneg hH
    exact False.elim (no_three_exceptional v w z a b hvw hvz hwz hve hwe hze)
  · rfl

lemma factor_of_and_filter (v : Fin 10) (H : (Fin 10 → Bool) → Bool)
    (hi : independent v H)
    (hf : ∀ x y : Fin 10 → Bool, (∀ i, i ≠ v → x i = y i) →
      (x v && !H x) = (y v && !H y) → target x = target y) : factor v H := by
  intro x y hagree hgate
  apply hf x y hagree
  have heq := hi x y hagree
  rw [← heq] at hgate ⊢
  cases hx : x v <;> cases hy : y v <;> cases hH : H x <;> simp_all

end PEqualNP.Outside.L_meta_1884.SharedFilter
