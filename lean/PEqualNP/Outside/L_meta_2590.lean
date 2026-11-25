import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset

namespace PEqualNP.Outside.L_meta_2590_aux

namespace FirstDirty

def singleton {n : ℕ} (v : Fin n) : Fin n → Bool := fun u => decide (u = v)

def pair {n : ℕ} (u v : Fin n) : Fin n → Bool :=
  fun w => decide (w = u ∨ w = v)

def Independent {n : ℕ} (G : Fin n → Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∀ u v, x u = true → x v = true → ¬ G u v

lemma singleton_independent {n : ℕ} {G : Fin n → Fin n → Prop}
    (hirr : ∀ u, ¬ G u u) (v : Fin n) : Independent G (singleton v) := by
  intro u w hu hw
  simp only [singleton, decide_eq_true_eq] at hu hw
  subst u
  subst w
  exact hirr v

lemma pair_le {n : ℕ} {u v : Fin n} {x : Fin n → Bool}
    (hu : x u = true) (hv : x v = true) :
    ∀ w, pair u v w = true → x w = true := by
  intro w hw
  simp only [pair, decide_eq_true_eq] at hw
  rcases hw with rfl | rfl
  · exact hu
  · exact hv

lemma independent_down {n : ℕ} {G : Fin n → Fin n → Prop}
    {x y : Fin n → Bool} (hxy : ∀ u, x u = true → y u = true)
    (hy : Independent G y) : Independent G x := by
  intro u v hu hv
  exact hy u v (hxy u hu) (hxy v hv)

lemma linear_before {n k : ℕ} {G : Fin n → Fin n → Prop}
    (V : ℕ → (Fin n → Bool) → Bool) (op : ℕ → Bool) (a b : ℕ → ℕ)
    (hirr : ∀ u, ¬ G u u)
    (hinput : ∀ (u : Fin n) x, V u.val x = x u)
    (hprev : ∀ j < k, a j < n + j ∧ b j < n + j)
    (hgate : ∀ j < k, ∀ x, V (n + j) x =
      if op j then V (a j) x && V (b j) x else V (a j) x || V (b j) x)
    (hpure : ∀ j < k, op j = true → ∀ x, Independent G x → V (n + j) x = false)
    (x : Fin n → Bool) (hx : Independent G x) :
    ∀ w < n + k, V w x = true ↔ ∃ v, x v = true ∧ V w (singleton v) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwi : w < n
    · let u : Fin n := ⟨w, hwi⟩
      change V u.val x = true ↔ _
      rw [hinput]
      constructor
      · intro hu
        exact ⟨u, hu, by rw [hinput u]; simp [singleton]⟩
      · rintro ⟨v, hv, hvs⟩
        rw [hinput u] at hvs
        simp only [singleton, decide_eq_true_eq] at hvs
        exact hvs.symm ▸ hv
    · let j := w - n
      have hj : j < k := by dsimp [j]; omega
      have hwj : w = n + j := by dsimp [j]; omega
      have hja : a j < w := by simpa [hwj] using (hprev j hj).1
      have hjb : b j < w := by simpa [hwj] using (hprev j hj).2
      by_cases hop : op j = true
      · have hfalse : V w x = false := hwj ▸ hpure j hj hop x hx
        have hsfalse : ∀ v, V w (singleton v) = false := fun v =>
          hwj ▸ hpure j hj hop _ (singleton_independent hirr v)
        simp [hfalse, hsfalse]
      · have hopen : op j = false := Bool.eq_false_iff.mpr hop
        have hrec (y : Fin n → Bool) :
            V w y = (V (a j) y || V (b j) y) := by
          rw [hwj, hgate j hj, hopen]
          rfl
        rw [hrec, Bool.or_eq_true, ih (a j) hja (by omega), ih (b j) hjb (by omega)]
        constructor
        · rintro (⟨v, hv, ha⟩ | ⟨v, hv, hb⟩)
          · exact ⟨v, hv, by rw [hrec, Bool.or_eq_true]; exact Or.inl ha⟩
          · exact ⟨v, hv, by rw [hrec, Bool.or_eq_true]; exact Or.inr hb⟩
        · rintro ⟨v, hv, hvs⟩
          rw [hrec, Bool.or_eq_true] at hvs
          exact hvs.elim (fun ha => Or.inl ⟨v, hv, ha⟩) (fun hb => Or.inr ⟨v, hv, hb⟩)

lemma wire_monotone {n k : ℕ}
    (V : ℕ → (Fin n → Bool) → Bool) (op : ℕ → Bool) (a b : ℕ → ℕ)
    (hinput : ∀ (u : Fin n) x, V u.val x = x u)
    (hprev : ∀ j < k, a j < n + j ∧ b j < n + j)
    (hgate : ∀ j < k, ∀ x, V (n + j) x =
      if op j then V (a j) x && V (b j) x else V (a j) x || V (b j) x)
    {x y : Fin n → Bool} (hxy : ∀ u, x u = true → y u = true) :
    ∀ w < n + k, V w x = true → V w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hval
    by_cases hwi : w < n
    · let u : Fin n := ⟨w, hwi⟩
      change V u.val y = true
      rw [hinput]
      have hvu : V u.val x = true := hval
      rw [hinput] at hvu
      exact hxy u hvu
    · let j := w - n
      have hj : j < k := by dsimp [j]; omega
      have hwj : w = n + j := by dsimp [j]; omega
      have hja : a j < w := by simpa [hwj] using (hprev j hj).1
      have hjb : b j < w := by simpa [hwj] using (hprev j hj).2
      have ha := ih (a j) hja (by omega)
      have hb := ih (b j) hjb (by omega)
      rw [hwj, hgate j hj] at hval ⊢
      cases hop : op j <;> simp only [hop, Bool.false_eq_true, ↓reduceIte,
        Bool.or_eq_true, Bool.and_eq_true] at hval ⊢
      · exact hval.elim (fun h => Or.inl (ha h)) (fun h => Or.inr (hb h))
      · exact ⟨ha hval.1, hb hval.2⟩

lemma first_dirty_pair {n k : ℕ} {G : Fin n → Fin n → Prop}
    (V : ℕ → (Fin n → Bool) → Bool) (op : ℕ → Bool) (a b : ℕ → ℕ)
    (hirr : ∀ u, ¬ G u u)
    (hinput : ∀ (u : Fin n) x, V u.val x = x u)
    (hprev : ∀ j ≤ k, a j < n + j ∧ b j < n + j)
    (hgate : ∀ j ≤ k, ∀ x, V (n + j) x =
      if op j then V (a j) x && V (b j) x else V (a j) x || V (b j) x)
    (hpure : ∀ j < k, op j = true → ∀ x, Independent G x → V (n + j) x = false)
    (hop : op k = true)
    (hdirty : ∃ x, Independent G x ∧ V (n + k) x = true) :
    ∃ u v, Independent G (pair u v) ∧ ¬ G u v ∧
      V (a k) (singleton u) = true ∧ V (b k) (singleton v) = true ∧
      V (n + k) (pair u v) = true := by
  obtain ⟨x, hx, hval⟩ := hdirty
  rw [hgate k (Nat.le_refl k), hop] at hval
  simp only [↓reduceIte, Bool.and_eq_true] at hval
  have hlin := linear_before V op a b hirr hinput
    (fun j hj => hprev j (Nat.le_of_lt hj))
    (fun j hj => hgate j (Nat.le_of_lt hj)) hpure x hx
  obtain ⟨u, hu, hau⟩ := (hlin (a k) (hprev k (Nat.le_refl k)).1).mp hval.1
  obtain ⟨v, hv, hbv⟩ := (hlin (b k) (hprev k (Nat.le_refl k)).2).mp hval.2
  refine ⟨u, v, independent_down (pair_le hu hv) hx, hx u v hu hv, hau, hbv, ?_⟩
  have hmono (s t : Fin n → Bool) := wire_monotone (x := s) (y := t) V op a b hinput
    (fun j (hj : j < k + 1) => hprev j (by omega))
    (fun j (hj : j < k + 1) => hgate j (by omega))
  rw [hgate k (Nat.le_refl k), hop]
  simp only [↓reduceIte, Bool.and_eq_true]
  constructor
  · apply hmono (singleton u) (pair u v) _ (a k) (by have := (hprev k (Nat.le_refl k)).1; omega) hau
    intro w hw
    simp only [singleton, decide_eq_true_eq] at hw
    subst w
    simp [pair]
  · apply hmono (singleton v) (pair u v) _ (b k) (by have := (hprev k (Nat.le_refl k)).2; omega) hbv
    intro w hw
    simp only [singleton, decide_eq_true_eq] at hw
    subst w
    simp [pair]

lemma all_pure_of_pairs {n k : ℕ} {G : Fin n → Fin n → Prop}
    (V : ℕ → (Fin n → Bool) → Bool) (op : ℕ → Bool) (a b : ℕ → ℕ)
    (hirr : ∀ u, ¬ G u u)
    (hinput : ∀ (u : Fin n) x, V u.val x = x u)
    (hprev : ∀ j < k, a j < n + j ∧ b j < n + j)
    (hgate : ∀ j < k, ∀ x, V (n + j) x =
      if op j then V (a j) x && V (b j) x else V (a j) x || V (b j) x)
    (hpairs : ∀ j < k, op j = true → ∀ u v, Independent G (pair u v) →
      V (n + j) (pair u v) = false) :
    ∀ j < k, op j = true → ∀ x, Independent G x → V (n + j) x = false := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hop x hx
    cases hv : V (n + j) x with
    | false => rfl
    | true =>
      obtain ⟨u, v, huv, _, _, _, htrue⟩ := first_dirty_pair V op a b hirr hinput
        (fun i hi => hprev i (by omega))
        (fun i hi => hgate i (by omega))
        (fun i hi => ih i hi (by omega)) hop ⟨x, hx, hv⟩
      have hfalse := hpairs j hj hop u v huv
      rw [hfalse] at htrue
      contradiction

end FirstDirty

namespace I3Geometry

abbrev V := Fin 10

def neighbors (v : V) : Nat :=
  [50, 69, 138, 276, 521, 385, 770, 548, 104, 208].getD v.val 0

abbrev adj (u v : V) : Prop := (neighbors u).testBit v.val = true

def mask (m : Nat) : Finset V := Finset.univ.filter (fun v => m.testBit v.val)

abbrev Independent (I : Finset V) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, ¬ adj u v

def rows : List (Nat × Nat × List Nat) :=
  [(69, 50, [1, 0, 4, 3, 2, 6, 5, 9, 8, 7]),
  (261, 769, [0, 4, 9, 6, 1, 5, 3, 7, 8, 2]),
  (517, 769, [0, 4, 9, 7, 5, 1, 3, 6, 2, 8]),
  (73, 769, [0, 4, 3, 8, 5, 1, 9, 2, 6, 7]),
  (137, 769, [0, 1, 6, 8, 5, 4, 2, 9, 3, 7]),
  (521, 50, [1, 2, 3, 4, 0, 6, 7, 8, 9, 5]),
  (193, 769, [0, 4, 3, 2, 1, 5, 9, 8, 7, 6]),
  (385, 50, [1, 2, 3, 8, 6, 0, 7, 4, 5, 9]),
  (769, 769, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
  (42, 769, [4, 0, 5, 8, 3, 9, 1, 7, 6, 2]),
  (138, 50, [2, 1, 0, 4, 3, 7, 6, 5, 9, 8]),
  (522, 769, [1, 0, 4, 9, 6, 2, 5, 3, 7, 8]),
  (50, 50, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
  (146, 769, [4, 0, 5, 7, 9, 3, 1, 8, 2, 6]),
  (274, 769, [4, 0, 1, 6, 9, 3, 5, 2, 8, 7]),
  (546, 769, [4, 0, 1, 2, 3, 9, 5, 6, 7, 8]),
  (386, 769, [1, 0, 4, 3, 2, 6, 5, 9, 8, 7]),
  (770, 50, [2, 1, 6, 8, 3, 7, 0, 9, 5, 4]),
  (52, 769, [4, 3, 8, 5, 0, 9, 2, 6, 7, 1]),
  (84, 769, [1, 6, 8, 5, 0, 2, 9, 3, 7, 4]),
  (276, 50, [2, 3, 4, 0, 1, 7, 8, 9, 5, 6]),
  (100, 769, [1, 6, 8, 3, 2, 0, 9, 5, 4, 7]),
  (548, 50, [2, 3, 4, 9, 7, 1, 8, 0, 6, 5]),
  (772, 769, [2, 1, 0, 4, 3, 7, 6, 5, 9, 8]),
  (104, 50, [2, 3, 8, 5, 7, 1, 4, 6, 0, 9]),
  (552, 769, [1, 2, 3, 8, 6, 0, 7, 4, 5, 9]),
  (200, 769, [2, 1, 6, 8, 3, 7, 0, 9, 5, 4]),
  (112, 769, [4, 3, 2, 1, 0, 9, 8, 7, 6, 5]),
  (208, 50, [2, 3, 8, 6, 1, 7, 4, 5, 9, 0]),
  (400, 769, [1, 2, 3, 4, 0, 6, 7, 8, 9, 5])]

def mapRow (r : Nat × Nat × List Nat) (v : V) : V :=
  ⟨(r.2.2.getD v.val 0) % 10, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma rows_valid : ∀ r ∈ rows,
    Function.Bijective (mapRow r) ∧
    (∀ u v : V, adj (mapRow r u) (mapRow r v) ↔ adj u v) ∧
    (mask r.1).image (mapRow r) = mask r.2.1 ∧
    (r.2.1 = 50 ∨ r.2.1 = 769) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma rows_cover : ∀ I : Finset V, I.card = 3 → Independent I →
    ∃ r ∈ rows, mask r.1 = I := by
  decide +kernel

lemma classify (I : Finset V) (hc : I.card = 3) (hi : Independent I) :
    ∃ σ : Equiv.Perm V,
      (∀ u v : V, adj (σ u) (σ v) ↔ adj u v) ∧
      (I.image σ = mask 50 ∨ I.image σ = mask 769) := by
  obtain ⟨r, hr, heq⟩ := rows_cover I hc hi
  obtain ⟨hb, ha, hm, ht⟩ := rows_valid r hr
  let σ : Equiv.Perm V := Equiv.ofBijective (mapRow r) hb
  refine ⟨σ, ha, ?_⟩
  have hs : I.image σ = mask r.2.1 := by
    rw [← heq]
    exact hm
  rcases ht with h | h
  · exact Or.inl (hs.trans (congrArg mask h))
  · exact Or.inr (hs.trans (congrArg mask h))

lemma canonical_masks : mask 50 = ({1, 4, 5} : Finset V) ∧
    mask 769 = ({0, 8, 9} : Finset V) := by
  decide +kernel

lemma canonical_neighborhood : ∀ v : V,
    v ∈ mask 50 ↔ adj 0 v := by
  decide +kernel

def cycleEdges : Finset (V × V) :=
  {(2, 3), (2, 7), (3, 8), (6, 8), (6, 9), (7, 9)}

def clawEdges : Finset (V × V) :=
  {(1, 2), (1, 6), (2, 3), (2, 7), (3, 4), (5, 7)}

lemma complement_neighborhood_edges : ∀ u v : V,
    u ∉ mask 50 ∧ v ∉ mask 50 ∧ adj u v ↔
      (u, v) ∈ cycleEdges ∨ (v, u) ∈ cycleEdges := by
  decide +kernel

lemma complement_claw_edges : ∀ u v : V,
    u ∉ mask 769 ∧ v ∉ mask 769 ∧ adj u v ↔
      (u, v) ∈ clawEdges ∨ (v, u) ∈ clawEdges := by
  decide +kernel

lemma canonical_forced_exposure :
    Independent (mask 104) ∧ Independent (mask 138) ∧ Independent (mask 50) ∧
    adj 4 3 ∧ adj 5 7 ∧ adj 6 1 ∧
    (∀ i ∈ ({0, 9} : Finset V), ∃ a ∈ mask 104, adj i a) ∧
    (∀ i ∈ ({0, 8} : Finset V), ∃ a ∈ mask 138, adj i a) ∧
    (∀ i ∈ ({8, 9} : Finset V), ∃ a ∈ mask 50, adj i a) := by
  decide +kernel

end I3Geometry

end PEqualNP.Outside.L_meta_2590_aux
