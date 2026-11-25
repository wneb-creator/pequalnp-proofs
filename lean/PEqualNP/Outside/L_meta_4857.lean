import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4857

open SimpleGraph

def IsLoop {V : Type*} (G : SimpleGraph V) (q : ℕ → V) (m : ℕ) : Prop :=
  q m = q 0 ∧ ∀ t < m, G.Adj (q t) (q (t + 1))

theorem small_mod (x k : ℕ) (h : x < 2 * k) : x % k = if x < k then x else x - k := by
  split_ifs with h1
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem girth_le {V : Type*} {G : SimpleGraph V} (q : ℕ → V) (m : ℕ) (hl : IsLoop G q m)
    (hm : 3 ≤ m) (hinj : ∀ a b, a < m → b < m → q a = q b → a = b) : G.egirth ≤ m := by
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 3 := ⟨m - 3, by omega⟩
  have key : ∀ a b : ℕ, a < r + 3 → b < r + 3 → (r + 3 - a + b) % (r + 3) = 1 →
      G.Adj (q a) (q b) := by
    intro a b ha hb hab
    rw [small_mod _ _ (by omega)] at hab
    split_ifs at hab with h1
    · have : a = r + 2 := by omega
      subst this
      have hb0 : b = 0 := by omega
      subst hb0
      rw [← hl.1]
      exact hl.2 _ (by omega)
    · have hb' : b = a + 1 := by omega
      subst hb'
      exact hl.2 a ha
  let f : cycleGraph (r + 3) →g G := ⟨fun u => q u.val, by
    intro u v huv
    rw [cycleGraph_adj'] at huv
    rcases huv with h | h
    · rw [Fin.val_sub] at h
      exact (key v.val u.val v.isLt u.isLt h).symm
    · rw [Fin.val_sub] at h
      exact key u.val v.val u.isLt v.isLt h⟩
  have hf : Function.Injective f := fun u v h => Fin.ext (hinj _ _ u.isLt v.isLt h)
  have hc := (cycleGraph.isCycle_cycle (n := r)).map hf
  have := hc.egirth_le_length
  simpa using this

theorem exists_odd_loop {V : Type*} {G : SimpleGraph V} (h : ¬ G.Colorable 2) :
    ∃ k, Odd k ∧ ∃ q, IsLoop G q k := by
  have h' : ¬ G.IsBipartite := h
  rw [isBipartite_iff_forall_walk_even_length] at h'
  push Not at h'
  obtain ⟨v, w, hw⟩ := h'
  refine ⟨w.length, hw, fun i => w.getVert i, ?_, ?_⟩
  · simp
  · intro t ht
    exact w.adj_getVert_succ ht

theorem core {V : Type*} (G : SimpleGraph V)
    (hdeg : ∀ v, (∃ u, G.Adj v u) → (G.neighborSet v).ncard = 3)
    (hg : (7 : ℕ∞) ≤ G.egirth) (hodd : ∃ k, Odd k ∧ ∃ q, IsLoop G q k) :
    ∃ k, 7 ≤ k ∧ Odd k ∧ ∃ c d : ℕ → V,
      (∀ a b, a < k → b < k → c a = c b → a = b) ∧
      (∀ a b, a < k → b < k → d a = d b → a = b) ∧
      (∀ a < k, G.Adj (c a) (d a) ∧ ∀ b < k, d a ≠ c b) ∧
      (∀ a b, a < k → b < k → (G.Adj (c a) (c b) ↔ (a + 1) % k = b ∨ (b + 1) % k = a)) := by
  classical
  have hmin : ∀ m < Nat.find hodd, m % 2 = 1 → ∀ q, IsLoop G q m → False :=
    fun m hm ho q hq => Nat.find_min hodd hm ⟨Nat.odd_iff.mpr ho, q, hq⟩
  obtain ⟨hko, p, hp⟩ := Nat.find_spec hodd
  generalize Nat.find hodd = k at hmin hko p hp
  have hk2 : k % 2 = 1 := Nat.odd_iff.mp hko
  have hk3 : 3 ≤ k := by
    have h1 : k ≠ 1 := by
      intro h1
      subst h1
      have := hp.2 0 (by omega)
      rw [hp.1] at this
      exact this.ne rfl
    omega
  set c : ℕ → V := fun t => p (t % k) with hc
  have hcper : ∀ t, c (t + k) = c t := by
    intro t
    simp [c]
  have hcmod : ∀ t, c (t % k) = c t := by
    intro t
    simp [c]
  have hcadj : ∀ t, G.Adj (c t) (c (t + 1)) := by
    intro t
    have h1 : t % k < k := Nat.mod_lt _ (by omega)
    have h2 : (t + 1) % k = (t % k + 1) % k := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < k by omega)]
    simp only [c]
    rw [h2, small_mod (t % k + 1) k (by omega)]
    split_ifs with h3
    · exact hp.2 _ h1
    · have h4 : t % k + 1 = k := by omega
      have := hp.2 _ h1
      rw [h4, hp.1] at this
      rw [show t % k + 1 - k = 0 by omega]
      exact this
  have hkey : ∀ a b, a < b → b < k → p a = p b → False := by
    intro a b hlt hy hxy
    have l1 : IsLoop G (fun t => p (a + t)) (b - a) := by
      refine ⟨by simp [show a + (b - a) = b by omega, hxy], fun t ht => ?_⟩
      exact hp.2 _ (by omega)
    have l2 : IsLoop G (fun t => c (b + t)) (k - (b - a)) := by
      refine ⟨?_, fun t _ => hcadj (b + t)⟩
      simp only [Nat.add_zero]
      rw [show b + (k - (b - a)) = a + k by omega, hcper]
      simp [c, Nat.mod_eq_of_lt (show a < k by omega), Nat.mod_eq_of_lt hy, hxy]
    rcases Nat.even_or_odd (b - a) with he | ho
    · rw [Nat.even_iff] at he
      exact hmin _ (by omega) (by omega) _ l2
    · rw [Nat.odd_iff] at ho
      exact hmin _ (by omega) ho _ l1
  have hcinj2 : ∀ x y, c x = c y → x % k = y % k := by
    intro x y hxy
    have hx := Nat.mod_lt x (show 0 < k by omega)
    have hy := Nat.mod_lt y (show 0 < k by omega)
    rcases lt_trichotomy (x % k) (y % k) with h | h | h
    · exact (hkey _ _ h hy hxy).elim
    · exact h
    · exact (hkey _ _ h hx hxy.symm).elim
  have hcinj : ∀ x y, x < k → y < k → c x = c y → x = y := by
    intro x y hx hy hxy
    have := hcinj2 x y hxy
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  have hloop_chord : ∀ s m, G.Adj (c (s + m)) (c s) →
      IsLoop G (fun t => if t ≤ m then c (s + t) else c s) (m + 1) := by
    intro s m hadj
    refine ⟨by simp, fun t ht => ?_⟩
    dsimp only
    by_cases h : t < m
    · rw [if_pos (by omega : t ≤ m), if_pos (by omega : t + 1 ≤ m)]
      exact hcadj (s + t)
    · have : t = m := by omega
      subst this
      rw [if_pos le_rfl, if_neg (by omega)]
      exact hadj
  have hloop_w : ∀ w s m, G.Adj w (c s) → G.Adj (c (s + m)) w →
      IsLoop G (fun t => if t = 0 ∨ m + 1 < t then w else c (s + t - 1)) (m + 2) := by
    intro w s m h1 h2
    refine ⟨by simp, fun t ht => ?_⟩
    dsimp only
    by_cases h0 : t = 0
    · subst h0
      rw [if_pos (by omega), if_neg (by omega)]
      simpa using h1
    by_cases hm : t = m + 1
    · subst hm
      rw [if_neg (by omega), if_pos (by omega)]
      simpa using h2
    rw [if_neg (by omega), if_neg (by omega)]
    have := hcadj (s + t - 1)
    rwa [show s + t - 1 + 1 = s + (t + 1) - 1 by omega] at this
  have hseven : ∀ q m, IsLoop G q m → 3 ≤ m → (∀ a b, a < m → b < m → q a = q b → a = b) →
      7 ≤ m := by
    intro q m hl hm hi
    have := le_trans hg (girth_le q m hl hm hi)
    exact_mod_cast this
  have hk7 : 7 ≤ k := by
    refine hseven c k ⟨?_, fun t _ => hcadj t⟩ hk3 hcinj
    simpa using hcper 0
  have hchord : ∀ x y, x < y → y < k → G.Adj (c x) (c y) → y = x + 1 ∨ (x = 0 ∧ y = k - 1) := by
    intro x y hxy hy hadj
    by_contra hne
    have h1 : y ≠ x + 1 := fun h => hne (Or.inl h)
    have h2 : x ≠ 0 ∨ y ≠ k - 1 := by
      by_cases hx : x = 0
      · right
        intro h
        exact hne (Or.inr ⟨hx, h⟩)
      · left
        exact hx
    have l1 := hloop_chord x (y - x) (by rw [show x + (y - x) = y by omega]; exact hadj.symm)
    have l2 := hloop_chord y (k - (y - x))
      (by rw [show y + (k - (y - x)) = x + k by omega, hcper]; exact hadj)
    rcases Nat.even_or_odd (y - x) with he | ho
    · rw [Nat.even_iff] at he
      exact hmin _ (by omega) (by omega) _ l1
    · rw [Nat.odd_iff] at ho
      exact hmin _ (by omega) (by omega) _ l2
  have hadjiff : ∀ a b, a < k → b < k →
      (G.Adj (c a) (c b) ↔ (a + 1) % k = b ∨ (b + 1) % k = a) := by
    intro a b ha hb
    constructor
    · intro h
      rw [small_mod (a + 1) k (by omega), small_mod (b + 1) k (by omega)]
      rcases lt_trichotomy a b with hab | hab | hab
      · rcases hchord a b hab hb h with h' | h'
        · split_ifs <;> omega
        · split_ifs <;> omega
      · subst hab
        exact (h.ne rfl).elim
      · rcases hchord b a hab ha h.symm with h' | h'
        · split_ifs <;> omega
        · split_ifs <;> omega
    · rintro (h | h)
      · rw [← h, hcmod]
        exact hcadj a
      · rw [← h, hcmod]
        exact (hcadj b).symm
  have hnb : ∀ i < k, ∃ w, G.Adj (c i) w ∧ ∀ j < k, w ≠ c j := by
    intro i hi
    have h3 := hdeg (c i) ⟨_, hcadj i⟩
    have hne : c (i + 1) ≠ c (i + k - 1) := by
      intro h
      have := hcinj2 _ _ h
      rw [small_mod (i + 1) k (by omega), small_mod (i + k - 1) k (by omega)] at this
      split_ifs at this <;> omega
    obtain ⟨w, hw, hw1, hw2⟩ : ∃ w ∈ G.neighborSet (c i), w ≠ c (i + 1) ∧ w ≠ c (i + k - 1) := by
      by_contra hcon
      push Not at hcon
      have hsub : G.neighborSet (c i) ⊆ {c (i + 1), c (i + k - 1)} := by
        intro w hw
        by_cases h : w = c (i + 1)
        · simp [h]
        · simp [hcon w hw h]
      have := Set.ncard_le_ncard hsub
      rw [Set.ncard_pair hne] at this
      omega
    refine ⟨w, hw, fun j hj hwj => ?_⟩
    subst hwj
    have hadj : G.Adj (c i) (c j) := hw
    rw [hadjiff i j hi hj] at hadj
    rcases hadj with h | h
    · apply hw1
      rw [← h, hcmod]
    · apply hw2
      rw [← hcmod (i + k - 1)]
      congr 1
      rw [small_mod (j + 1) k (by omega)] at h
      rw [small_mod (i + k - 1) k (by omega)]
      split_ifs at h ⊢ <;> omega
  have : Nonempty V := ⟨p 0⟩
  choose! d hd using hnb
  have hwinj : ∀ w s m, (∀ j < k, w ≠ c j) → s < k → m + 1 ≤ k → ∀ a b, a < m + 2 → b < m + 2 →
      (fun t => if t = 0 ∨ m + 1 < t then w else c (s + t - 1)) a =
      (fun t => if t = 0 ∨ m + 1 < t then w else c (s + t - 1)) b → a = b := by
    intro w s m hw hs hm a b ha hb hab
    have hw' : ∀ j, w ≠ c j := by
      intro j h
      rw [← hcmod] at h
      exact hw _ (Nat.mod_lt _ (by omega)) h
    dsimp only at hab
    by_cases ha0 : a = 0
    · by_cases hb0 : b = 0
      · omega
      · rw [if_pos (Or.inl ha0), if_neg (by omega)] at hab
        exact absurd hab (hw' _)
    · by_cases hb0 : b = 0
      · rw [if_neg (by omega), if_pos (Or.inl hb0)] at hab
        exact absurd hab.symm (hw' _)
      · rw [if_neg (by omega), if_neg (by omega)] at hab
        have := hcinj2 _ _ hab
        rw [small_mod (s + a - 1) k (by omega), small_mod (s + b - 1) k (by omega)] at this
        split_ifs at this <;> omega
  have hdinj : ∀ x y, x < k → y < k → d x = d y → x = y := by
    intro x y hx hy hxy
    by_contra hne
    wlog hlt : x < y generalizing x y
    · exact this y x hy hx hxy.symm (Ne.symm hne) (by omega)
    have hwx : G.Adj (d x) (c x) := (hd x hx).1.symm
    have hwy : G.Adj (d x) (c y) := by rw [hxy]; exact (hd y hy).1.symm
    have hwn : ∀ j < k, d x ≠ c j := (hd x hx).2
    have l1 := hloop_w (d x) x (y - x) hwx
      (by rw [show x + (y - x) = y by omega]; exact hwy.symm)
    have l2 := hloop_w (d x) y (k - (y - x)) hwy
      (by rw [show y + (k - (y - x)) = x + k by omega, hcper]; exact hwx.symm)
    have g1 := hseven _ _ l1 (by omega) (hwinj (d x) x (y - x) hwn hx (by omega))
    have g2 := hseven _ _ l2 (by omega) (hwinj (d x) y (k - (y - x)) hwn hy (by omega))
    rcases Nat.even_or_odd (y - x) with he | ho
    · rw [Nat.even_iff] at he
      exact hmin _ (by omega) (by omega) _ l2
    · rw [Nat.odd_iff] at ho
      exact hmin _ (by omega) (by omega) _ l1
  exact ⟨k, hk7, hko, c, d, hcinj, hdinj, fun a ha => hd a ha, hadjiff⟩

end PEqualNP.Outside.L_meta_4857

theorem PEqualNP.Outside.L_meta_4857 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)), ¬x2.Colorable (2 : ℕ) → (∀ x5 ∉ x3, (x2.neighborSet x5).ncard = (3 : ℕ)) → (7 : ℕ∞) ≤ x2.egirth → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x3) → ∃ (x8 : ℕ), (7 : ℕ) ≤ x8 ∧ Odd x8 ∧ ∃ (x9 : Fin x8 ↪ Fin x1) (x10 : Fin x8 ↪ Fin x1), (∀ (x11 : Fin x8), x2.Adj (x9 x11) (x10 x11) ∧ x10 x11 ∉ Set.range ⇑x9) ∧ ∀ (x11 x12 : Fin x8), x2.Adj (x9 x11) (x9 x12) ↔ (↑x11 + (1 : ℕ)) % x8 = ↑x12 ∨ (↑x12 + (1 : ℕ)) % x8 = ↑x11 := by
  intro n G A hcol hdeg hg hA
  obtain ⟨k, hk7, hko, c, d, hci, hdi, hcd, hiff⟩ := PEqualNP.Outside.L_meta_4857.core G
    (fun v hv => hdeg v (by obtain ⟨u, hu⟩ := hv; exact hA v u hu)) hg
    (PEqualNP.Outside.L_meta_4857.exists_odd_loop hcol)
  refine ⟨k, hk7, hko, ⟨fun i => c i.val, fun a b h => Fin.ext (hci _ _ a.isLt b.isLt h)⟩,
    ⟨fun i => d i.val, fun a b h => Fin.ext (hdi _ _ a.isLt b.isLt h)⟩,
    fun i => ⟨(hcd i i.isLt).1, ?_⟩, fun a b => hiff _ _ a.isLt b.isLt⟩
  rintro ⟨j, hj⟩
  exact (hcd i i.isLt).2 j j.isLt hj.symm
