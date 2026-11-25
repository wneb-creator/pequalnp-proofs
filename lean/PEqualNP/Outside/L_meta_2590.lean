import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import PEqualNP.Defs
import Mathlib.Data.Finset.Card

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

namespace CircuitPurity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def value {n : ℕ} (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma value_input {n : ℕ} (C : Circuit) (u : Fin n) (x : Fin n → Bool) :
    value C u.val x = x u := by
  unfold value
  rw [wires_eq_foldl, foldl_getD_lt _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma value_and {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hop : (C.gates[j]).op = GateOp.and) (x : Fin n → Bool) :
    value C (n + j) x = true ↔
      ∀ i ∈ (C.gates[j]).inputs, i < n + j ∧ value C i x = true := by
  have h := foldl_getD_gate C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold value
  rw [wires_eq_foldl, h, hop]
  simp [GateOp.eval]

lemma value_or {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hop : (C.gates[j]).op = GateOp.or) (x : Fin n → Bool) :
    value C (n + j) x = true ↔
      ∃ i ∈ (C.gates[j]).inputs, i < n + j ∧ value C i x = true := by
  have h := foldl_getD_gate C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold value
  rw [wires_eq_foldl, h, hop]
  simp [GateOp.eval]

lemma pair_supported {n w : ℕ} (hn : 0 < n) {G : Fin n → Fin n → Prop}
    (hirr : ∀ v, ¬ G v v) (V : ℕ → (Fin n → Bool) → Bool)
    (is : List ℕ) (hlen : is.length ≤ 2)
    (hlin : ∀ i < w, ∀ y, Independent G y →
      (V i y = true ↔ ∃ v, y v = true ∧ V i (singleton v) = true))
    (x : Fin n → Bool) (hx : Independent G x)
    (htrue : ∀ i ∈ is, i < w ∧ V i x = true) :
    ∃ u v, Independent G (pair u v) ∧
      ∀ i ∈ is, i < w ∧ V i (pair u v) = true := by
  cases is with
  | nil =>
    let u : Fin n := ⟨0, hn⟩
    refine ⟨u, u, ?_, by simp⟩
    have heq : pair u u = singleton u := by funext v; simp [pair, singleton]
    rw [heq]
    exact singleton_independent hirr u
  | cons a is =>
    have ha := htrue a (by simp)
    obtain ⟨u, hu, hau⟩ := (hlin a ha.1 x hx).mp ha.2
    cases is with
    | nil =>
      have hp : Independent G (pair u u) := independent_down (pair_le hu hu) hx
      refine ⟨u, u, hp, ?_⟩
      intro i hi
      simp only [List.mem_singleton] at hi
      subst i
      exact ⟨ha.1, (hlin a ha.1 _ hp).mpr ⟨u, by simp [pair], hau⟩⟩
    | cons b is =>
      have hnil : is = [] := by cases is <;> simp_all
      subst is
      have hb := htrue b (by simp)
      obtain ⟨v, hv, hbv⟩ := (hlin b hb.1 x hx).mp hb.2
      have hp : Independent G (pair u v) := independent_down (pair_le hu hv) hx
      refine ⟨u, v, hp, ?_⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi
      · subst i
        exact ⟨ha.1, (hlin a ha.1 _ hp).mpr ⟨u, by simp [pair], hau⟩⟩
      · subst i
        exact ⟨hb.1, (hlin b hb.1 _ hp).mpr ⟨v, by simp [pair], hbv⟩⟩

lemma linear_before_of_pure {n k : ℕ} {G : Fin n → Fin n → Prop}
    (hirr : ∀ v, ¬ G v v) (C : Circuit) (hmono : Monotone2 C)
    (hk : k ≤ C.gates.length)
    (hprior : ∀ j (hj : j < C.gates.length), j < k →
      (C.gates[j]).op = GateOp.and →
      ∀ x, Independent G x → value C (n + j) x = false) :
    ∀ w < n + k, ∀ x, Independent G x →
      (value C w x = true ↔ ∃ v, x v = true ∧ value C w (singleton v) = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw x hx
    by_cases hwi : w < n
    · let u : Fin n := ⟨w, hwi⟩
      have hin (y : Fin n → Bool) : value C w y = y u := value_input C u y
      simp only [hin, singleton, decide_eq_true_eq]
      constructor
      · intro hu
        exact ⟨u, hu, rfl⟩
      · rintro ⟨v, hv, huv⟩
        exact huv.symm ▸ hv
    · let j := w - n
      have hjk : j < k := by dsimp [j]; omega
      have hj : j < C.gates.length := lt_of_lt_of_le hjk hk
      have hwj : w = n + j := by dsimp [j]; omega
      have hgm := hmono (C.gates[j]) (List.getElem_mem hj)
      rcases hgm.1 with hand | hor
      · have hfalse (y : Fin n → Bool) (hy : Independent G y) : value C w y = false := by
          rw [hwj]
          exact hprior j hj hjk hand y hy
        have hsf : ∀ v, value C w (singleton v) = false :=
          fun v => hfalse _ (singleton_independent hirr v)
        simp [hfalse x hx, hsf]
      · have horec (y : Fin n → Bool) : value C w y = true ↔
            ∃ i ∈ (C.gates[j]).inputs, i < w ∧ value C i y = true := by
          simpa only [hwj] using value_or C j hj hor y
        constructor
        · intro ht
          obtain ⟨i, hi, hiw, hiv⟩ := (horec x).mp ht
          obtain ⟨v, hv, hivs⟩ := (ih i hiw (by omega) x hx).mp hiv
          exact ⟨v, hv, (horec _).mpr ⟨i, hi, hiw, hivs⟩⟩
        · rintro ⟨v, hv, hvs⟩
          obtain ⟨i, hi, hiw, hivs⟩ := (horec _).mp hvs
          exact (horec _).mpr ⟨i, hi, hiw, (ih i hiw (by omega) x hx).mpr ⟨v, hv, hivs⟩⟩

lemma circuit_first_impure_pair {n : ℕ} (hn : 0 < n) {G : Fin n → Fin n → Prop}
    (hirr : ∀ v, ¬ G v v) (C : Circuit) (hmono : Monotone2 C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (C.gates[j]).op = GateOp.and)
    (hprior : ∀ r (hr : r < C.gates.length), r < j →
      (C.gates[r]).op = GateOp.and →
      ∀ x, Independent G x → value C (n + r) x = false)
    (hdirty : ∃ x, Independent G x ∧ value C (n + j) x = true) :
    ∃ u v, Independent G (pair u v) ∧ ¬ G u v ∧ value C (n + j) (pair u v) = true := by
  obtain ⟨x, hx, hval⟩ := hdirty
  have hlin := linear_before_of_pure hirr C hmono (Nat.le_of_lt hj) hprior
  have hlen := (hmono (C.gates[j]) (List.getElem_mem hj)).2
  obtain ⟨u, v, huv, hsupports⟩ := pair_supported hn hirr (value C)
    (C.gates[j]).inputs hlen hlin x hx ((value_and C j hj hop x).mp hval)
  exact ⟨u, v, huv, huv u v (by simp [pair]) (by simp [pair]),
    (value_and C j hj hop _).mpr hsupports⟩

lemma linear_of_pairs {n : ℕ} (hn : 0 < n) {G : Fin n → Fin n → Prop}
    (hirr : ∀ v, ¬ G v v) (C : Circuit) (hmono : Monotone2 C)
    (hpairs : ∀ j (hj : j < C.gates.length), (C.gates[j]).op = GateOp.and →
      ∀ u v, Independent G (pair u v) → value C (n + j) (pair u v) = false) :
    ∀ w < n + C.gates.length, ∀ x, Independent G x →
      (value C w x = true ↔ ∃ v, x v = true ∧ value C w (singleton v) = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw x hx
    by_cases hwi : w < n
    · let u : Fin n := ⟨w, hwi⟩
      have hin (y : Fin n → Bool) : value C w y = y u := value_input C u y
      simp only [hin, singleton, decide_eq_true_eq]
      constructor
      · intro hu
        exact ⟨u, hu, rfl⟩
      · rintro ⟨v, hv, huv⟩
        exact huv.symm ▸ hv
    · let j := w - n
      have hj : j < C.gates.length := by dsimp [j]; omega
      have hwj : w = n + j := by dsimp [j]; omega
      have hgm := hmono (C.gates[j]) (List.getElem_mem hj)
      rcases hgm.1 with hand | hor
      · have hfalse (y : Fin n → Bool) (hy : Independent G y) : value C w y = false := by
          cases hv : value C w y with
          | false => rfl
          | true =>
            have hval : ∀ i ∈ (C.gates[j]).inputs, i < w ∧ value C i y = true := by
              simpa only [hwj] using (value_and C j hj hand y).mp (hwj ▸ hv)
            obtain ⟨u, v, huv, hav⟩ := pair_supported hn hirr (value C)
              (C.gates[j]).inputs hgm.2
              (fun i hi z hz => ih i hi (by omega) z hz) y hy hval
            have ht : value C (n + j) (pair u v) = true :=
              (value_and C j hj hand _).mpr (by simpa only [hwj] using hav)
            rw [hpairs j hj hand u v huv] at ht
            contradiction
        have hsf : ∀ v, value C w (singleton v) = false :=
          fun v => hfalse _ (singleton_independent hirr v)
        simp [hfalse x hx, hsf]
      · have horec (y : Fin n → Bool) : value C w y = true ↔
            ∃ i ∈ (C.gates[j]).inputs, i < w ∧ value C i y = true := by
          simpa only [hwj] using value_or C j hj hor y
        constructor
        · intro ht
          obtain ⟨i, hi, hiw, hiv⟩ := (horec x).mp ht
          obtain ⟨v, hv, hivs⟩ := (ih i hiw (by omega) x hx).mp hiv
          exact ⟨v, hv, (horec _).mpr ⟨i, hi, hiw, hivs⟩⟩
        · rintro ⟨v, hv, hvs⟩
          obtain ⟨i, hi, hiw, hivs⟩ := (horec _).mp hvs
          exact (horec _).mpr ⟨i, hi, hiw, (ih i hiw (by omega) x hx).mpr ⟨v, hv, hivs⟩⟩

lemma circuit_pure_of_pairs {n : ℕ} (hn : 0 < n) {G : Fin n → Fin n → Prop}
    (hirr : ∀ v, ¬ G v v) (C : Circuit) (hmono : Monotone2 C)
    (hpairs : ∀ j (hj : j < C.gates.length), (C.gates[j]).op = GateOp.and →
      ∀ u v, Independent G (pair u v) → value C (n + j) (pair u v) = false) :
    ∀ j (hj : j < C.gates.length), (C.gates[j]).op = GateOp.and →
      ∀ x, Independent G x → value C (n + j) x = false := by
  intro j hj hop x hx
  cases hv : value C (n + j) x with
  | false => rfl
  | true =>
    obtain ⟨u, hu, hsu⟩ := (linear_of_pairs hn hirr C hmono hpairs
      (n + j) (by omega) x hx).mp hv
    have heq : pair u u = singleton u := by funext v; simp [pair, singleton]
    have hp : Independent G (pair u u) := by rw [heq]; exact singleton_independent hirr u
    have hf := hpairs j hj hop u u hp
    rw [heq] at hf
    rw [hf] at hsu
    contradiction

lemma circuit_purity_iff_pair_purity {n : ℕ} (hn : 0 < n) {G : Fin n → Fin n → Prop}
    (hirr : ∀ v, ¬ G v v) (C : Circuit) (hmono : Monotone2 C) :
    (∀ j (hj : j < C.gates.length), (C.gates[j]).op = GateOp.and →
      ∀ x, Independent G x → value C (n + j) x = false) ↔
    (∀ j (hj : j < C.gates.length), (C.gates[j]).op = GateOp.and →
      ∀ u v, Independent G (pair u v) → value C (n + j) (pair u v) = false) := by
  constructor
  · intro h j hj hop u v huv
    exact h j hj hop _ huv
  · exact circuit_pure_of_pairs hn hirr C hmono

lemma circuit_impure_pair {n : ℕ} (hn : 0 < n) {G : Fin n → Fin n → Prop}
    (hirr : ∀ v, ¬ G v v) (C : Circuit) (hmono : Monotone2 C)
    (hdirty : ∃ j, ∃ hj : j < C.gates.length, (C.gates[j]).op = GateOp.and ∧
      ∃ x, Independent G x ∧ value C (n + j) x = true) :
    ∃ j, ∃ hj : j < C.gates.length, (C.gates[j]).op = GateOp.and ∧
      ∃ u v, Independent G (pair u v) ∧ value C (n + j) (pair u v) = true := by
  classical
  by_contra hnone
  have hpairs : ∀ j (hj : j < C.gates.length), (C.gates[j]).op = GateOp.and →
      ∀ u v, Independent G (pair u v) → value C (n + j) (pair u v) = false := by
    intro j hj hop u v huv
    cases hv : value C (n + j) (pair u v) with
    | false => rfl
    | true => exact False.elim (hnone ⟨j, hj, hop, u, v, huv, hv⟩)
  obtain ⟨j, hj, hop, x, hx, hval⟩ := hdirty
  have hfalse := circuit_pure_of_pairs hn hirr C hmono hpairs j hj hop x hx
  rw [hfalse] at hval
  contradiction

end CircuitPurity

namespace ResidualCodes

lemma three_incomparable_need_three {α : Type*} [DecidableEq α]
    (U A B C : Finset α) (hA : A ⊆ U) (hB : B ⊆ U) (hC : C ⊆ U)
    (hAB : ¬ A ⊆ B) (hBA : ¬ B ⊆ A) (hCA : ¬ C ⊆ A)
    (hCB : ¬ C ⊆ B) (hAC : ¬ A ⊆ C) : 3 ≤ U.card := by
  by_contra hsmall
  have htwo : U.card ≤ 2 := by omega
  obtain ⟨a, haA, haB⟩ := Finset.not_subset.mp hAB
  obtain ⟨b, hbB, hbA⟩ := Finset.not_subset.mp hBA
  have hab : a ≠ b := by intro he; exact hbA (he ▸ haA)
  have hpair : ({a, b} : Finset α) ⊆ U := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hA haA
    · exact hB hbB
  have hcard : ({a, b} : Finset α).card = 2 := by simp [hab]
  have hU : ({a, b} : Finset α) = U :=
    Finset.eq_of_subset_of_card_le hpair (by omega)
  obtain ⟨c, hcC, hcA⟩ := Finset.not_subset.mp hCA
  obtain ⟨d, hdC, hdB⟩ := Finset.not_subset.mp hCB
  have hc : c = b := by
    have h := hC hcC
    rw [← hU] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    exact h.resolve_left (fun he => hcA (he ▸ haA))
  have hd : d = a := by
    have h := hC hdC
    rw [← hU] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    exact h.resolve_right (fun he => hdB (he ▸ hbB))
  apply hAC
  intro x hx
  have h := hA hx
  rw [← hU] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl
  · exact hd ▸ hdC
  · exact hc ▸ hcC

lemma three_unit_profiles : ∀ A B C : Finset (Fin 3),
    ¬ A ⊆ B → ¬ B ⊆ A → ¬ A ⊆ C → ¬ C ⊆ A → ¬ B ⊆ C → ¬ C ⊆ B →
    (A.card = 1 ∧ B.card = 1 ∧ C.card = 1) ∨
    (A.card = 2 ∧ B.card = 2 ∧ C.card = 2) := by
  decide +kernel

end ResidualCodes

namespace I4Codes

lemma two_incomparable_avoiding_nonempty_need_three {α : Type*} [DecidableEq α]
    (U A B C : Finset α) (hA : A ⊆ U) (hB : B ⊆ U) (hC : C ⊆ U)
    (hne : C.Nonempty) (hAB : ¬ A ⊆ B) (hBA : ¬ B ⊆ A)
    (hAC : ¬ A ⊆ C) (hBC : ¬ B ⊆ C) : 3 ≤ U.card := by
  obtain ⟨a, haA, haB⟩ := Finset.not_subset.mp hAB
  obtain ⟨b, hbB, hbA⟩ := Finset.not_subset.mp hBA
  obtain ⟨c, hcC⟩ := hne
  have hab : a ≠ b := by
    intro he
    exact hbA (he ▸ haA)
  by_cases hca : c = a
  · obtain ⟨d, hdA, hdC⟩ := Finset.not_subset.mp hAC
    have had : a ≠ d := by
      intro he
      exact hdC ((hca.trans he) ▸ hcC)
    have hbd : b ≠ d := by
      intro he
      exact hbA (he ▸ hdA)
    exact Finset.two_lt_card.mpr ⟨a, hA haA, b, hB hbB, d, hA hdA, hab, had, hbd⟩
  · by_cases hcb : c = b
    · obtain ⟨d, hdB, hdC⟩ := Finset.not_subset.mp hBC
      have had : a ≠ d := by
        intro he
        exact haB (he ▸ hdB)
      have hbd : b ≠ d := by
        intro he
        exact hdC ((hcb.trans he) ▸ hcC)
      exact Finset.two_lt_card.mpr ⟨a, hA haA, b, hB hbB, d, hB hdB, hab, had, hbd⟩
    · exact Finset.two_lt_card.mpr
        ⟨a, hA haA, b, hB hbB, c, hC hcC, hab, Ne.symm hca, Ne.symm hcb⟩

end I4Codes


namespace R2Profiles

abbrev Code := Finset (Fin 2)
abbrev CycleCodes := Fin 6 → Code

abbrev Conditions (center : Code) (f : CycleCodes) : Prop :=
  center.Nonempty ∧
  (∀ i, ¬ center ⊆ f i) ∧
  (∀ i, (f i).Nonempty ∨ (f (i + 1)).Nonempty) ∧
  (∀ i j, i ≠ j → i.val % 2 = j.val % 2 → (f i).Nonempty → ¬ f i ⊆ f j)

def code (n : Nat) : Code :=
  if n = 0 then ∅ else if n = 1 then {0} else if n = 2 then {1} else Finset.univ

def ofList (l : List Nat) : CycleCodes := fun i => code (l.getD i.val 0)

def profiles : Finset CycleCodes :=
  {ofList [0, 1, 1, 0, 2, 2],
   ofList [0, 1, 2, 0, 1, 2],
   ofList [0, 2, 1, 0, 2, 1],
   ofList [0, 2, 2, 0, 1, 1],
   ofList [1, 0, 2, 1, 0, 2],
   ofList [1, 0, 2, 2, 0, 1],
   ofList [1, 1, 0, 2, 2, 0],
   ofList [1, 2, 0, 1, 2, 0],
   ofList [2, 0, 1, 1, 0, 2],
   ofList [2, 0, 1, 2, 0, 1],
   ofList [2, 1, 0, 2, 1, 0],
   ofList [2, 2, 0, 1, 1, 0]}

def mk (a b c d e f : Code) : CycleCodes :=
  fun i => [a, b, c, d, e, f].getD i.val ∅

lemma mk_eta (f : CycleCodes) : mk (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) = f := by
  funext i
  fin_cases i <;> rfl

lemma code_cases (s : Code) : s = ∅ ∨ s = {0} ∨ s = {1} ∨ s = Finset.univ := by
  have h : ∀ s : Code, s = ∅ ∨ s = {0} ∨ s = {1} ∨ s = Finset.univ := by decide +kernel
  exact h s

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 10000 in
lemma classify_0_0 : ∀ (b c d e f : Code),
    Conditions (∅ : Code) (mk (∅ : Code) b c d e f) →
      (∅ : Code) = Finset.univ ∧ mk (∅ : Code) b c d e f ∈ profiles := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 10000 in
lemma classify_0_1 : ∀ (b c d e f : Code),
    Conditions (∅ : Code) (mk ({0} : Code) b c d e f) →
      (∅ : Code) = Finset.univ ∧ mk ({0} : Code) b c d e f ∈ profiles := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 10000 in
lemma classify_0_2 : ∀ (b c d e f : Code),
    Conditions (∅ : Code) (mk ({1} : Code) b c d e f) →
      (∅ : Code) = Finset.univ ∧ mk ({1} : Code) b c d e f ∈ profiles := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 10000 in
lemma classify_0_3 : ∀ (b c d e f : Code),
    Conditions (∅ : Code) (mk (Finset.univ : Code) b c d e f) →
      (∅ : Code) = Finset.univ ∧ mk (Finset.univ : Code) b c d e f ∈ profiles := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 10000 in
lemma classify_1_0 : ∀ (b c d e f : Code),
    Conditions ({0} : Code) (mk (∅ : Code) b c d e f) →
      ({0} : Code) = Finset.univ ∧ mk (∅ : Code) b c d e f ∈ profiles := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 10000 in
lemma classify_1_1 : ∀ (b c d e f : Code),
    Conditions ({0} : Code) (mk ({0} : Code) b c d e f) →
      ({0} : Code) = Finset.univ ∧ mk ({0} : Code) b c d e f ∈ profiles := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 10000 in
lemma classify_1_2 : ∀ (b c d e f : Code),
    Conditions ({0} : Code) (mk ({1} : Code) b c d e f) →
      ({0} : Code) = Finset.univ ∧ mk ({1} : Code) b c d e f ∈ profiles := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 10000 in
lemma classify_1_3 : ∀ (b c d e f : Code),
    Conditions ({0} : Code) (mk (Finset.univ : Code) b c d e f) →
      ({0} : Code) = Finset.univ ∧ mk (Finset.univ : Code) b c d e f ∈ profiles := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 10000 in
lemma classify_2_0 : ∀ (b c d e f : Code),
    Conditions ({1} : Code) (mk (∅ : Code) b c d e f) →
      ({1} : Code) = Finset.univ ∧ mk (∅ : Code) b c d e f ∈ profiles := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 10000 in
lemma classify_2_1 : ∀ (b c d e f : Code),
    Conditions ({1} : Code) (mk ({0} : Code) b c d e f) →
      ({1} : Code) = Finset.univ ∧ mk ({0} : Code) b c d e f ∈ profiles := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 10000 in
lemma classify_2_2 : ∀ (b c d e f : Code),
    Conditions ({1} : Code) (mk ({1} : Code) b c d e f) →
      ({1} : Code) = Finset.univ ∧ mk ({1} : Code) b c d e f ∈ profiles := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 10000 in
lemma classify_2_3 : ∀ (b c d e f : Code),
    Conditions ({1} : Code) (mk (Finset.univ : Code) b c d e f) →
      ({1} : Code) = Finset.univ ∧ mk (Finset.univ : Code) b c d e f ∈ profiles := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 10000 in
lemma classify_3_0 : ∀ (b c d e f : Code),
    Conditions (Finset.univ : Code) (mk (∅ : Code) b c d e f) →
      (Finset.univ : Code) = Finset.univ ∧ mk (∅ : Code) b c d e f ∈ profiles := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 10000 in
lemma classify_3_1 : ∀ (b c d e f : Code),
    Conditions (Finset.univ : Code) (mk ({0} : Code) b c d e f) →
      (Finset.univ : Code) = Finset.univ ∧ mk ({0} : Code) b c d e f ∈ profiles := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 10000 in
lemma classify_3_2 : ∀ (b c d e f : Code),
    Conditions (Finset.univ : Code) (mk ({1} : Code) b c d e f) →
      (Finset.univ : Code) = Finset.univ ∧ mk ({1} : Code) b c d e f ∈ profiles := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 10000 in
lemma classify_3_3 : ∀ (b c d e f : Code),
    Conditions (Finset.univ : Code) (mk (Finset.univ : Code) b c d e f) →
      (Finset.univ : Code) = Finset.univ ∧ mk (Finset.univ : Code) b c d e f ∈ profiles := by
  decide +kernel

lemma classify_coordinates (center a b c d e f : Code)
    (h : Conditions center (mk a b c d e f)) :
    center = Finset.univ ∧ mk a b c d e f ∈ profiles := by
  rcases code_cases center with rfl | rfl | rfl | rfl <;>
    rcases code_cases a with rfl | rfl | rfl | rfl
  · exact classify_0_0 b c d e f h
  · exact classify_0_1 b c d e f h
  · exact classify_0_2 b c d e f h
  · exact classify_0_3 b c d e f h
  · exact classify_1_0 b c d e f h
  · exact classify_1_1 b c d e f h
  · exact classify_1_2 b c d e f h
  · exact classify_1_3 b c d e f h
  · exact classify_2_0 b c d e f h
  · exact classify_2_1 b c d e f h
  · exact classify_2_2 b c d e f h
  · exact classify_2_3 b c d e f h
  · exact classify_3_0 b c d e f h
  · exact classify_3_1 b c d e f h
  · exact classify_3_2 b c d e f h
  · exact classify_3_3 b c d e f h

lemma classify (center : Code) (f : CycleCodes) (h : Conditions center f) :
    center = Finset.univ ∧ f ∈ profiles := by
  have hm := classify_coordinates center (f 0) (f 1) (f 2) (f 3) (f 4) (f 5)
  rw [mk_eta] at hm
  exact hm h

lemma profiles_card : profiles.card = 12 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma profiles_valid : ∀ f ∈ profiles, Conditions Finset.univ f := by
  intro f hf
  simp only [profiles, Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

abbrev OppositeEmpties (f : CycleCodes) : Prop :=
  ∃ i : Fin 3, ∀ j : Fin 6,
    f j = ∅ ↔ j.val = i.val ∨ j.val = i.val + 3

abbrev SingletonNonempty (f : CycleCodes) : Prop :=
  ∀ i, (f i).Nonempty → ∃ u, f i = {u}

abbrev TwoEach (f : CycleCodes) : Prop :=
  ∀ u : Fin 2, (Finset.univ.filter fun i => u ∈ f i).card = 2

abbrev AdjacentUnits (f : CycleCodes) : Prop :=
  ∀ u : Fin 2, ∃ i : Fin 6, ∀ j : Fin 6,
    u ∈ f j ↔ j = i ∨ j = i + 1

abbrev OppositeUnits (f : CycleCodes) : Prop :=
  ∀ u : Fin 2, ∃ i : Fin 6, ∀ j : Fin 6,
    u ∈ f j ↔ j = i ∨ j = i + 3

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma profiles_shape : ∀ f ∈ profiles,
    OppositeEmpties f ∧ SingletonNonempty f ∧ TwoEach f ∧
      (AdjacentUnits f ∨ OppositeUnits f) := by
  intro f hf
  simp only [profiles, Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

lemma adjacent_count : (profiles.filter AdjacentUnits).card = 6 := by decide +kernel
lemma opposite_count : (profiles.filter OppositeUnits).card = 6 := by decide +kernel

lemma shape (center : Code) (f : CycleCodes) (h : Conditions center f) :
    center = Finset.univ ∧ OppositeEmpties f ∧ SingletonNonempty f ∧ TwoEach f ∧
      (AdjacentUnits f ∨ OppositeUnits f) := by
  obtain ⟨hc, hf⟩ := classify center f h
  exact ⟨hc, profiles_shape f hf⟩

lemma classify_iff (center : Code) (f : CycleCodes) :
    Conditions center f ↔ center = Finset.univ ∧ f ∈ profiles := by
  constructor
  · exact classify center f
  · rintro ⟨rfl, hf⟩
    exact profiles_valid f hf

def vertex (i : Fin 6) : Fin 10 :=
  ([2, 3, 8, 6, 9, 7] : List (Fin 10)).getD i.val 0

def edgeBit (u v : Fin 10) : Bool :=
  ([50, 69, 138, 276, 521, 385, 770, 548, 104, 208].getD u.val 0).testBit v.val

abbrev IndependentTriple (k x y : Fin 10) : Prop :=
  k ≠ x ∧ k ≠ y ∧ x ≠ y ∧
  edgeBit k x = false ∧ edgeBit x k = false ∧
  edgeBit k y = false ∧ edgeBit y k = false ∧
  edgeBit x y = false ∧ edgeBit y x = false

abbrev IndependentHit (f : CycleCodes) : Prop :=
  ∃ k : Fin 10, ∃ i j : Fin 6,
    k ∈ ({1, 4, 5} : Finset (Fin 10)) ∧ edgeBit 0 k = true ∧
    f i = {0} ∧ f j = {1} ∧ IndependentTriple k (vertex i) (vertex j)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 10000 in
lemma profiles_hit : ∀ f ∈ profiles, IndependentHit f := by
  intro f hf
  simp only [profiles, Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

lemma independent_hit (center : Code) (f : CycleCodes) (h : Conditions center f) :
    center = Finset.univ ∧ IndependentHit f := by
  obtain ⟨hc, hf⟩ := classify center f h
  exact ⟨hc, profiles_hit f hf⟩

end R2Profiles

namespace I3Branch

-- Circuit normalization and wire counting, adapted from L_meta_971.
namespace DagTools

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

@[local simp] theorem gop_true (a b : Bool) : gop true a b = (a && b) := rfl

@[local simp] theorem gop_false (a b : Bool) : gop false a b = (a || b) := rfl

abbrev Dag := List (Bool × ℕ × ℕ)

def tag (D : Dag) (j : ℕ) : Bool := (D.getD j (false, 0, 0)).1

def opA (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.1

def opB (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.2

def wstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

def wl (D : Dag) (w : List Bool) : List Bool := D.foldl wstep w

def val (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wl D (List.ofFn x)).getD w false

def Strict (n : ℕ) (D : Dag) : Prop :=
  ∀ j, j < D.length → opA D j < n + j ∧ opB D j < n + j ∧ opA D j ≠ opB D j

def readers (D : Dag) (w : ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => opA D j = w ∨ opB D j = w)

def fanout (D : Dag) (w : ℕ) : ℕ := (readers D w).card

def Live (n : ℕ) (D : Dag) : Prop := ∀ w, w + 1 < n + D.length → 1 ≤ fanout D w

def StrictLive (n : ℕ) (D : Dag) : Prop := Strict n D ∧ Live n D ∧ D ≠ []

def outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1

def single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

def supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)

def surplusOn (D : Dag) (K : Finset ℕ) : ℕ := ∑ w ∈ K, (fanout D w - 1)

def inner (n : ℕ) (D : Dag) : Finset ℕ := Finset.range (n + D.length - 1)

def totalSurplus (n : ℕ) (D : Dag) : ℕ := surplusOn D (inner n D)

def Bplus (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => (supp n D w).Nonempty))

def Bzero (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => ¬ (supp n D w).Nonempty))

def branchW (n : ℕ) (D : Dag) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => 2 ≤ fanout D w)

def eligSet (n : ℕ) (D : Dag) : Finset (Fin n) := (branchW n D).biUnion (supp n D)

def ineligSet (n : ℕ) (D : Dag) : Finset (Fin n) := Finset.univ \ eligSet n D

def units (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (inner n D).sigma (fun w => Finset.range (fanout D w - 1))

def unitsPlus (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => (supp n D u.1).Nonempty)

def arcs (D : Dag) : Finset (ℕ × Bool) := Finset.range D.length ×ˢ Finset.univ

def src (D : Dag) (e : ℕ × Bool) : ℕ := if e.2 = true then opB D e.1 else opA D e.1

def exitArcs (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ × Bool) :=
  (arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∉ K)

def merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => n + j ∈ K ∧ opA D j ∈ K ∧ opB D j ∈ K)

def sources (n : ℕ) (K : Finset ℕ) : Finset ℕ := K.filter (fun w => w < n)

def carrierT (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => (supp n D w ∩ T).Nonempty)

def carrierDiff (n : ℕ) (D : Dag) (x y : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)

def PureBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v}

def reservedUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ))

def residualUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  unitsPlus n D \ reservedUnits n D b

theorem tag_eq (D : Dag) (j : ℕ) (h : j < D.length) : tag D j = (D[j]).1 := by
  simp [tag, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem opA_eq (D : Dag) (j : ℕ) (h : j < D.length) : opA D j = (D[j]).2.1 := by
  simp [opA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem opB_eq (D : Dag) (j : ℕ) (h : j < D.length) : opB D j = (D[j]).2.2 := by
  simp [opB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem wl_cons (g : Bool × ℕ × ℕ) (D : Dag) (w : List Bool) :
    wl (g :: D) w = wl D (wstep w g) := rfl

theorem wl_append (D E : Dag) (w : List Bool) : wl (D ++ E) w = wl E (wl D w) := by
  simp [wl, List.foldl_append]

theorem wstep_length (w : List Bool) (g : Bool × ℕ × ℕ) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

theorem wl_length (D : Dag) : ∀ w : List Bool, (wl D w).length = w.length + D.length := by
  induction D with
  | nil => intro w; simp [wl]
  | cons g D ih => intro w; rw [wl_cons, ih, wstep_length]; simp; omega

theorem wstep_getD_lt (w : List Bool) (g : Bool × ℕ × ℕ) (i : ℕ) (h : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem wl_getD_lt (D : Dag) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wl D w).getD i false = w.getD i false := by
  induction D with
  | nil => intro w i _; rfl
  | cons g D ih =>
    intro w i h
    rw [wl_cons, ih _ _ (by rw [wstep_length]; omega), wstep_getD_lt _ _ _ h]

theorem getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem wstep_getD_last (w : List Bool) (g : Bool × ℕ × ℕ) :
    (wstep w g).getD w.length false = gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false) := by
  simp [wstep, List.getD_eq_getElem?_getD]

theorem wl_getD_gate (D : Dag) (w : List Bool) (j : ℕ) (hj : j < D.length) :
    (wl D w).getD (w.length + j) false =
      gop (tag D j) ((wl (D.take j) w).getD (opA D j) false)
        ((wl (D.take j) w).getD (opB D j) false) := by
  have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1) := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  rw [tag_eq D j hj, opA_eq D j hj, opB_eq D j hj]
  conv_lhs => rw [hsplit, wl_append, wl_cons]
  rw [wl_getD_lt _ _ _ (by rw [wstep_length, hlen]; omega), ← hlen, wstep_getD_last]

theorem wl_take_getD (D : Dag) (w : List Bool) (j i : ℕ) (hi : i < w.length + j)
    (hj : j ≤ D.length) :
    (wl (D.take j) w).getD i false = (wl D w).getD i false := by
  have hsplit : D = D.take j ++ D.drop j := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  conv_rhs => rw [hsplit, wl_append]
  rw [wl_getD_lt (D.drop j) (wl (D.take j) w) i (by rw [hlen]; exact hi)]

theorem val_input (D : Dag) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val D x i = x ⟨i, h⟩ := by
  unfold val
  rw [wl_getD_lt _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

theorem val_ge (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : n + D.length ≤ w) :
    val D x w = false := by
  unfold val
  exact getD_ge _ _ (by rw [wl_length]; simpa using h)

theorem val_take (D : Dag) {n : ℕ} (x : Fin n → Bool) (k w : ℕ) (hw : w < n + k)
    (hk : k ≤ D.length) : val (D.take k) x w = val D x w := by
  unfold val
  exact wl_take_getD D _ k w (by simpa using hw) hk

theorem val_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  have h := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [h, wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]

theorem val_unique {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (f : ℕ → Bool)
    (hin : ∀ i (h : i < n), f i = x ⟨i, h⟩)
    (hg : ∀ j, j < D.length → f (n + j) = gop (tag D j) (f (opA D j)) (f (opB D j))) :
    ∀ w, w < n + D.length → val D x w = f w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · rw [val_input D x w hn, hin w hn]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      obtain ⟨ha, hb, -⟩ := hS j hj
      rw [val_gate hS x j hj, hg j hj, ih _ ha (by omega), ih _ hb (by omega)]

abbrev Ref := Bool ⊕ ℕ

def refVal (W : List Bool) : Ref → Bool
  | Sum.inl b => b
  | Sum.inr k => W.getD k false

def na_look (m : List Ref) (i : ℕ) : Ref := m.getD i (Sum.inl false)

def na_comb (t : Bool) : Ref → Ref → Ref ⊕ (ℕ × ℕ)
  | Sum.inl a, r => Sum.inl (if a = t then r else Sum.inl a)
  | Sum.inr i, Sum.inl b => Sum.inl (if b = t then Sum.inr i else Sum.inl b)
  | Sum.inr i, Sum.inr j => if i = j then Sum.inl (Sum.inr i) else Sum.inr (i, j)

def na_isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def na_step (n : ℕ) (st : List Ref × Dag) (g : Gate) : List Ref × Dag :=
  match g.inputs with
  | [] => (st.1 ++ [Sum.inl (na_isAnd g.op)], st.2)
  | [a] => (st.1 ++ [na_look st.1 a], st.2)
  | a :: b :: _ =>
    match na_comb (na_isAnd g.op) (na_look st.1 a) (na_look st.1 b) with
    | Sum.inl r => (st.1 ++ [r], st.2)
    | Sum.inr p => (st.1 ++ [Sum.inr (n + st.2.length)], st.2 ++ [(na_isAnd g.op, p.1, p.2)])

def na_ok (B : ℕ) : Ref → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < B

def na_Good (n : ℕ) (st : List Ref × Dag) : Prop :=
  Strict n st.2 ∧ ∀ r ∈ st.1, na_ok (n + st.2.length) r

theorem na_ok_mono {B B' : ℕ} (h : B ≤ B') (r : Ref) (hr : na_ok B r) : na_ok B' r := by
  rcases r with b | k
  · trivial
  · exact lt_of_lt_of_le hr h

theorem na_look_val (W : List Bool) (m : List Ref) (i : ℕ) :
    refVal W (na_look m i) = (m.map (refVal W)).getD i false := by
  simp only [na_look, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases m[i]? <;> rfl

theorem na_look_ok (B : ℕ) (m : List Ref) (hm : ∀ r ∈ m, na_ok B r) (i : ℕ) :
    na_ok B (na_look m i) := by
  simp only [na_look, List.getD_eq_getElem?_getD]
  rcases h : m[i]? with _ | r
  · trivial
  · exact hm r (List.mem_of_getElem? h)

theorem na_refVal_wstep (W : List Bool) (g : Bool × ℕ × ℕ) (r : Ref) (hr : na_ok W.length r) :
    refVal (wstep W g) r = refVal W r := by
  rcases r with b | k
  · rfl
  · exact wstep_getD_lt W g k hr

theorem na_comb_inl (t : Bool) (W : List Bool) (a b r : Ref) (h : na_comb t a b = Sum.inl r) :
    refVal W r = gop t (refVal W a) (refVal W b) := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h
    cases t <;> cases a <;> simp [refVal]
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h
      cases t <;> cases b <;> simp [refVal]
    · simp only [na_comb] at h
      split_ifs at h with hij
      simp only [Sum.inl.injEq] at h
      subst h; subst hij
      cases t <;> simp [refVal]

theorem na_comb_ok (B : ℕ) (t : Bool) (a b r : Ref) (ha : na_ok B a) (hb : na_ok B b)
    (h : na_comb t a b = Sum.inl r) : na_ok B r := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h; split_ifs
    · exact hb
    · trivial
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h; split_ifs
      · exact ha
      · trivial
    · simp only [na_comb] at h
      split_ifs at h
      simp only [Sum.inl.injEq] at h
      subst h; exact ha

theorem na_comb_inr (t : Bool) (a b : Ref) (p : ℕ × ℕ) (h : na_comb t a b = Sum.inr p) :
    a = Sum.inr p.1 ∧ b = Sum.inr p.2 ∧ p.1 ≠ p.2 := by
  rcases a with a | i
  · simp [na_comb] at h
  · rcases b with b | j
    · simp [na_comb] at h
    · simp only [na_comb] at h
      split_ifs at h with hij
      cases h
      exact ⟨rfl, rfl, hij⟩

theorem na_eval0 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    op.eval [] = na_isAnd op := by
  rcases hop with rfl | rfl <;> rfl

theorem na_eval1 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (u : Bool) :
    op.eval [u] = u := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval]

theorem na_eval2 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (u v : Bool) : op.eval [u, v] = gop (na_isAnd op) u v := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval, na_isAnd]

theorem na_getD_append_lt (D E : Dag) (k : ℕ) (h : k < D.length) :
    (D ++ E).getD k (false, 0, 0) = D.getD k (false, 0, 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem na_getD_snoc (D : Dag) (g : Bool × ℕ × ℕ) :
    (D ++ [g]).getD D.length (false, 0, 0) = g := by
  simp [List.getD_eq_getElem?_getD]

theorem na_strict_snoc {n : ℕ} {D : Dag} (hS : Strict n D) (t : Bool) (i j : ℕ)
    (hi : i < n + D.length) (hj : j < n + D.length) (hij : i ≠ j) :
    Strict n (D ++ [(t, i, j)]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  by_cases hk' : k < D.length
  · simp only [opA, opB, na_getD_append_lt D _ k hk']
    exact hS k hk'
  · have hkD : k = D.length := by omega
    subst hkD
    simp only [opA, opB, na_getD_snoc]
    exact ⟨hi, hj, hij⟩

theorem na_strict_take {n : ℕ} {D : Dag} (hS : Strict n D) (k : ℕ) : Strict n (D.take k) := by
  intro j hj
  simp only [List.length_take] at hj
  have hj1 : j < k := by omega
  have hj2 : j < D.length := by omega
  have e : (D.take k).getD j (false, 0, 0) = D.getD j (false, 0, 0) := by
    simp [List.getD_eq_getElem?_getD, hj1]
  simp only [opA, opB, e]
  exact hS j hj2

theorem na_step_spec (n : ℕ) (st : List Ref × Dag) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : na_Good n st) :
    na_Good n (na_step n st g) ∧ (na_step n st g).2.length ≤ st.2.length + 1 ∧
    ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
      (na_step n st g).1.map (refVal (wl (na_step n st g).2 (List.ofFn x))) =
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
  obtain ⟨m, D⟩ := st
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  obtain ⟨hS, hok⟩ := h
  dsimp only at hS hok hop hlen ⊢
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · trivial
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, refVal, na_eval0 op hop]
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · exact na_look_ok _ m hok a
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, na_eval1 op hop,
        na_look_val]
  · have hla := na_look_ok _ m hok a
    have hlb := na_look_ok _ m hok b
    rcases hc : na_comb (na_isAnd op) (na_look m a) (na_look m b) with r | p
    · refine ⟨⟨by simpa only [na_step, hc] using hS, ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact hok r' hr
        · exact na_comb_ok _ _ _ _ _ hla hlb hc
      · subst hw
        simp only [na_step, hc, List.map_append, List.map_cons, List.map_nil, na_eval2 op hop,
          na_comb_inl _ (wl D (List.ofFn x)) _ _ _ hc, na_look_val]
    · obtain ⟨ea, eb, hne⟩ := na_comb_inr _ _ _ _ hc
      rw [ea] at hla
      rw [eb] at hlb
      have hS' := na_strict_snoc hS (na_isAnd op) p.1 p.2 hla hlb hne
      refine ⟨⟨by simpa only [na_step, hc] using hS', ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton, List.length_append,
          List.length_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact na_ok_mono (by omega) r' (hok r' hr)
        · show n + D.length < n + (D.length + 1)
          omega
      · subst hw
        have hWlen : (wl D (List.ofFn x)).length = n + D.length := by
          rw [wl_length, List.length_ofFn]
        have hW' : wl (D ++ [(na_isAnd op, p.1, p.2)]) (List.ofFn x) =
            wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2) := by
          rw [wl_append]; rfl
        have h1 : m.map (refVal (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2))) =
            m.map (refVal (wl D (List.ofFn x))) :=
          List.map_congr_left (fun r hr => na_refVal_wstep _ _ r (by rw [hWlen]; exact hok r hr))
        have h2 : (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2)).getD (n + D.length) false =
            gop (na_isAnd op) ((m.map (refVal (wl D (List.ofFn x)))).getD a false)
              ((m.map (refVal (wl D (List.ofFn x)))).getD b false) := by
          rw [← hWlen, wstep_getD_last, ← na_look_val, ← na_look_val, ea, eb]; rfl
        simp only [na_step, hc, hW', List.map_append, List.map_cons, List.map_nil, h1, refVal,
          h2, na_eval2 op hop]
  · simp at hlen

theorem na_fold_spec (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ st : List Ref × Dag, na_Good n st →
      na_Good n (gs.foldl (na_step n) st) ∧
      (gs.foldl (na_step n) st).2.length ≤ st.2.length + gs.length ∧
      ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
        (gs.foldl (na_step n) st).1.map
            (refVal (wl (gs.foldl (na_step n) st).2 (List.ofFn x))) =
          gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro st h; exact ⟨h, by simp, fun x w hw => hw⟩
  | cons g gs ih =>
    intro st h
    obtain ⟨h1, h2, h3⟩ := na_step_spec n st g (hgs g (by simp)) h
    obtain ⟨i1, i2, i3⟩ := ih (fun g' hg' => hgs g' (by simp [hg'])) _ h1
    refine ⟨i1, ?_, fun x w hw => ?_⟩
    · simp only [List.foldl_cons, List.length_cons]; omega
    · simp only [List.foldl_cons]; exact i3 x _ (h3 x w hw)

theorem na_init (n : ℕ) (x : Fin n → Bool) :
    ((List.range n).map Sum.inr).map (refVal (wl ([] : Dag) (List.ofFn x))) = List.ofFn x := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [refVal, wl, List.getD_eq_getElem?_getD, h1]

theorem exists_strict_of_monotone2 {n : ℕ} (C : Circuit) (hmono : Monotone2 C) :
    (∃ b : Bool, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = b) ∨
    (∃ i : Fin n, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = x i) ∨
    (∃ D : Dag, Strict n D ∧ D ≠ [] ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x)) := by
  have h0 : na_Good n ((List.range n).map Sum.inr, ([] : Dag)) := by
    refine ⟨fun j hj => absurd hj (by simp), fun r hr => ?_⟩
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    simpa [na_ok] using hk
  obtain ⟨⟨hS, hok⟩, hlen, hsem⟩ := na_fold_spec n C.gates hmono _ h0
  generalize C.gates.foldl (na_step n) ((List.range n).map Sum.inr, ([] : Dag)) = st
    at hS hok hlen hsem
  obtain ⟨m, D⟩ := st
  dsimp only at hS hok hlen hsem
  have hev : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = refVal (wl D (List.ofFn x)) (na_look m C.output) := by
    intro x
    rw [na_look_val, hsem x (List.ofFn x) (na_init n x)]
    rfl
  have hk := na_look_ok _ m hok C.output
  rcases hr : na_look m C.output with b | k
  · exact Or.inl ⟨b, fun x => by rw [hev x, hr]; rfl⟩
  · rw [hr] at hk
    have hk' : k < n + D.length := hk
    by_cases hkn : k < n
    · exact Or.inr (Or.inl ⟨⟨k, hkn⟩, fun x => by rw [hev x, hr]; exact val_input D x k hkn⟩)
    · have hl : (D.take (k - n + 1)).length = k - n + 1 := by
        rw [List.length_take]; omega
      refine Or.inr (Or.inr ⟨D.take (k - n + 1), na_strict_take hS _, ?_, ?_, fun x => ?_⟩)
      · intro h
        rw [h] at hl
        simp at hl
      · rw [hl]
        simp only [List.length_nil, Nat.zero_add] at hlen
        unfold Circuit.size
        omega
      · have ho : outW n (D.take (k - n + 1)) = k := by unfold outW; rw [hl]; omega
        rw [ho, val_take D x (k - n + 1) k (by omega) (by omega), hev x, hr]
        rfl

theorem na_no_reader {D : Dag} {w : ℕ} (h : fanout D w = 0) (j : ℕ) (hj : j < D.length) :
    opA D j ≠ w ∧ opB D j ≠ w := by
  unfold fanout readers at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  have := h (Finset.mem_range.mpr hj)
  tauto

def na_sh (c a : ℕ) : ℕ := if c < a then a - 1 else a

def na_up (c w : ℕ) : ℕ := if w < c then w else w + 1

def na_del (n j : ℕ) (D : Dag) : Dag :=
  (D.eraseIdx j).map (fun g => (g.1, na_sh (n + j) g.2.1, na_sh (n + j) g.2.2))

theorem na_del_length (n j : ℕ) (D : Dag) (hj : j < D.length) :
    (na_del n j D).length = D.length - 1 := by
  simp [na_del, List.length_eraseIdx, hj]

theorem na_del_ops (n j : ℕ) (D : Dag) (k : ℕ) (hk : na_up j k < D.length) :
    tag (na_del n j D) k = tag D (na_up j k) ∧
    opA (na_del n j D) k = na_sh (n + j) (opA D (na_up j k)) ∧
    opB (na_del n j D) k = na_sh (n + j) (opB D (na_up j k)) := by
  have e : (na_del n j D).getD k (false, 0, 0) =
      ((D.getD (na_up j k) (false, 0, 0)).1, na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.1,
        na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.2) := by
    simp only [na_del, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eraseIdx]
    unfold na_up at hk ⊢
    split_ifs at hk ⊢ <;> simp [List.getElem?_eq_getElem hk]
  unfold tag opA opB
  rw [e]
  exact ⟨rfl, rfl, rfl⟩

theorem na_del_strict {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) : Strict n (na_del n j D) := by
  intro k hk
  rw [na_del_length n j D hj] at hk
  have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
  have hk2 : (k < j ∧ na_up j k = k) ∨ (j ≤ k ∧ na_up j k = k + 1) := by
    unfold na_up; split_ifs <;> omega
  obtain ⟨ha, hb, hab⟩ := hS _ hk'
  obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
  obtain ⟨-, ea, eb⟩ := na_del_ops n j D k hk'
  rw [ea, eb]
  generalize na_up j k = k' at *
  generalize opA D k' = a at *
  generalize opB D k' = b at *
  refine ⟨?_, ?_, ?_⟩ <;> unfold na_sh <;> split_ifs <;> omega

theorem na_del_val {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) (x : Fin n → Bool) (w : ℕ) (hw : w < n + (D.length - 1)) :
    val (na_del n j D) x w = val D x (na_up (n + j) w) := by
  refine val_unique (na_del_strict hS j hj hf) x (fun u => val D x (na_up (n + j) u))
    (fun i hi => ?_) (fun k hk => ?_) w (by rw [na_del_length n j D hj]; exact hw)
  · have e : na_up (n + j) i = i := by unfold na_up; split_ifs <;> omega
    show val D x (na_up (n + j) i) = x ⟨i, hi⟩
    rw [e]; exact val_input D x i hi
  · rw [na_del_length n j D hj] at hk
    have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
    obtain ⟨et, ea, eb⟩ := na_del_ops n j D k hk'
    obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
    have e1 : na_up (n + j) (n + k) = n + na_up j k := by unfold na_up; split_ifs <;> omega
    have e2 : ∀ a, a ≠ n + j → na_up (n + j) (na_sh (n + j) a) = a := by
      intro a ha; unfold na_up na_sh; split_ifs <;> omega
    show val D x (na_up (n + j) (n + k)) = gop (tag (na_del n j D) k)
      (val D x (na_up (n + j) (opA (na_del n j D) k)))
      (val D x (na_up (n + j) (opB (na_del n j D) k)))
    rw [e1, et, ea, eb, e2 _ ra, e2 _ rb]
    exact val_gate hS x _ hk'

theorem na_live_aux {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y) :
    ∀ (s : ℕ) (D : Dag), D.length = s → Strict n D → D ≠ [] →
      (∀ x : Fin n → Bool, val D x (outW n D) = F x) →
      ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ s ∧
        ∀ x : Fin n → Bool, val D' x (outW n D') = F x := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro D hlen hS hne hD
    have hpos : 0 < D.length := List.length_pos_iff.mpr hne
    by_cases hL : Live n D
    · exact ⟨D, ⟨hS, hL, hne⟩, hlen.le, hD⟩
    · obtain ⟨w, hw, hf0⟩ : ∃ w, w + 1 < n + D.length ∧ fanout D w = 0 := by
        by_contra hcon
        exact hL (fun w hw => by
          by_contra h0
          exact hcon ⟨w, hw, by omega⟩)
      by_cases hwn : w < n
      · exfalso
        obtain ⟨x, y, hxy, hFne⟩ := hess ⟨w, hwn⟩
        apply hFne
        rw [← hD x, ← hD y]
        have hout : outW n D ≠ w := by unfold outW; omega
        have key := val_unique hS y (fun u => if u = w then y ⟨w, hwn⟩ else val D x u)
          (fun i hi => by
            by_cases hiw : i = w
            · subst hiw; simp
            · simp only [hiw, ite_false]
              rw [val_input D x i hi]
              exact hxy ⟨i, hi⟩ (fun h => hiw (congrArg Fin.val h)))
          (fun j hj => by
            obtain ⟨ha, hb⟩ := na_no_reader hf0 j hj
            have hnj : n + j ≠ w := by omega
            simp only [hnj, ha, hb, ite_false]
            exact val_gate hS x j hj)
          (outW n D) (by unfold outW; omega)
        simp only [hout, ite_false] at key
        exact key.symm
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        have hl := na_del_length n j D hj
        obtain ⟨D', h1, h2, h3⟩ := ih (D.length - 1) (by omega) (na_del n j D) hl
          (na_del_strict hS j hj hf0)
          (fun h => by rw [h] at hl; simp at hl; omega)
          (fun x => by
            have ho : outW n (na_del n j D) = n + (D.length - 1) - 1 := by unfold outW; rw [hl]
            have hu : na_up (n + j) (n + (D.length - 1) - 1) = outW n D := by
              unfold na_up outW; split_ifs <;> omega
            rw [ho, na_del_val hS j hj hf0 x _ (by omega), hu]
            exact hD x)
        exact ⟨D', h1, by omega, h3⟩

theorem exists_strictLive_of_strict {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x : Fin n → Bool, val D x (outW n D) = F x) :
    ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ D.length ∧
      ∀ x : Fin n → Bool, val D' x (outW n D') = F x :=
  na_live_aux F hess D.length D rfl hS hne hD

theorem normalize_strictLive {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (hnc : ∀ b : Bool, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ b)
    (hnp : ∀ i : Fin n, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ x i)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Dag, StrictLive n D ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x) := by
  rcases exists_strict_of_monotone2 (n := n) C hmono with
    ⟨b, hb⟩ | ⟨i, hi⟩ | ⟨D, hS, hne, hlen, hD⟩
  · obtain ⟨x, hx⟩ := hnc b
    exact absurd (hb x) hx
  · obtain ⟨x, hx⟩ := hnp i
    exact absurd (hi x) hx
  · obtain ⟨D', h1, h2, h3⟩ :=
      exists_strictLive_of_strict (fun x => C.eval (List.ofFn x)) hess D hS hne hD
    exact ⟨D', h1, by omega, h3⟩

section SurplusFlow

variable {n : ℕ} {D : Dag}

theorem sb_mem_inner {w : ℕ} : w ∈ inner n D ↔ w + 1 < n + D.length := by
  unfold inner; rw [Finset.mem_range]; omega

theorem sb_src_false (j : ℕ) : src D (j, false) = opA D j := by simp [src]

theorem sb_src_true (j : ℕ) : src D (j, true) = opB D j := by simp [src]

theorem fanout_eq_zero_of_ge (hS : Strict n D) (w : ℕ) (h : n + D.length ≤ w + 1) :
    fanout D w = 0 := by
  unfold fanout readers
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  have hj2 := Finset.mem_range.mp hj
  have := hS j hj2
  omega

theorem lt_of_fanout_pos (hS : Strict n D) {w : ℕ} (h : 1 ≤ fanout D w) :
    w + 1 < n + D.length := by
  by_contra hc
  have := fanout_eq_zero_of_ge hS w (by omega)
  omega

theorem sb_card_arcs_filter (P : ℕ × Bool → Prop) [DecidablePred P] :
    ((arcs D).filter P).card = ∑ j ∈ Finset.range D.length,
      ((if P (j, false) then 1 else 0) + (if P (j, true) then 1 else 0)) := by
  rw [Finset.card_filter, arcs, Finset.sum_product]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fintype.sum_bool, add_comm]

theorem sb_card_arcs : (arcs D).card = 2 * D.length := by
  simp [arcs, Finset.card_product, Nat.mul_comm]

theorem sb_src_lt (hS : Strict n D) (e : ℕ × Bool) (he : e ∈ arcs D) :
    src D e + 1 < n + D.length := by
  obtain ⟨j, c⟩ := e
  have hj : j < D.length := by simpa [arcs] using he
  have := hS j hj
  cases c
  · rw [sb_src_false]; omega
  · rw [sb_src_true]; omega

theorem sb_fanout_arcs (hS : Strict n D) (w : ℕ) :
    fanout D w = ((arcs D).filter (fun e => src D e = w)).card := by
  rw [sb_card_arcs_filter, fanout, readers, Finset.card_filter]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have := (hS j (Finset.mem_range.mp hj)).2.2
  rw [sb_src_false, sb_src_true]
  split_ifs <;> omega

theorem sb_sum_fanout_eq (hS : Strict n D) (K : Finset ℕ) :
    ∑ w ∈ K, fanout D w = ((arcs D).filter (fun e => src D e ∈ K)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := src D)
    (s := (arcs D).filter (fun e => src D e ∈ K)) (t := K)
    (fun e he => Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2)]
  refine Finset.sum_congr rfl (fun w hw => ?_)
  rw [sb_fanout_arcs hS, Finset.filter_filter]
  congr 1
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, rfl⟩; exact ⟨he, hw, rfl⟩
  · rintro ⟨he, -, h⟩; exact ⟨he, h⟩

theorem sb_surplus_add_card {K : Finset ℕ} (hL : ∀ w ∈ K, 1 ≤ fanout D w) :
    surplusOn D K + K.card = ∑ w ∈ K, fanout D w := by
  rw [surplusOn, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w hw => Nat.sub_add_cancel (hL w hw))

theorem surplus_identity (h : StrictLive n D) : totalSurplus n D + n = D.length + 1 := by
  obtain ⟨hS, hL, hne⟩ := h
  have hpos : 0 < D.length := List.length_pos_iff.mpr hne
  have h1 : surplusOn D (inner n D) + (inner n D).card = ∑ w ∈ inner n D, fanout D w :=
    sb_surplus_add_card (fun w hw => hL w (sb_mem_inner.mp hw))
  have h2 : ∑ w ∈ inner n D, fanout D w = 2 * D.length := by
    rw [sb_sum_fanout_eq hS, Finset.filter_true_of_mem, sb_card_arcs]
    intro e he
    exact sb_mem_inner.mpr (sb_src_lt hS e he)
  have h3 : (inner n D).card = n + D.length - 1 := Finset.card_range _
  unfold totalSurplus
  omega

theorem totalSurplus_split (n : ℕ) (D : Dag) : totalSurplus n D = Bplus n D + Bzero n D := by
  unfold totalSurplus Bplus Bzero surplusOn
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem live_reaches_out (h : StrictLive n D) (w : ℕ) (hw : w < n + D.length) :
    Relation.ReflTransGen (fun a b => b < n + D.length ∧ n ≤ b ∧
      (opA D (b - n) = a ∨ opB D (b - n) = a)) w (outW n D) := by
  obtain ⟨hS, hL, -⟩ := h
  generalize hk : n + D.length - w = k
  induction k using Nat.strong_induction_on generalizing w with
  | _ k ih =>
    by_cases hlast : w + 1 = n + D.length
    · have hw2 : w = outW n D := by unfold outW; omega
      rw [hw2]
    · obtain ⟨j, hj⟩ := Finset.card_pos.mp (hL w (by omega))
      simp only [readers, Finset.mem_filter, Finset.mem_range] at hj
      have hs := hS j hj.1
      refine Relation.ReflTransGen.head (b := n + j) ⟨by omega, by omega, ?_⟩
        (ih (n + D.length - (n + j)) (by omega) (n + j) (by omega) rfl)
      simpa using hj.2

theorem mem_supp {v : Fin n} {w : ℕ} : v ∈ supp n D w ↔ val D (single v) w = true := by
  simp [supp]

theorem val_mono (hS : Strict n D) (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) : val D x w = true → val D y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn]; exact hxy _
    · by_cases hw : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        rw [val_gate hS x j hj, val_gate hS y j hj]
        have h1 := ih _ ha
        have h2 := ih _ hb
        cases tag D j <;>
          simp only [gop_true, gop_false, Bool.and_eq_true, Bool.or_eq_true] <;> tauto
      · rw [val_ge D x w (by omega)]; simp

theorem supp_input (D : Dag) (i : Fin n) : supp n D i.val = {i} := by
  ext v
  rw [mem_supp, val_input D (single v) i.val i.isLt]
  simp [single, eq_comm]

theorem supp_ge (D : Dag) (w : ℕ) (h : n + D.length ≤ w) : supp n D w = ∅ := by
  ext v
  simp [mem_supp, val_ge D (single v) w h]

theorem supp_gate (hS : Strict n D) (j : ℕ) (hj : j < D.length) :
    supp n D (n + j) = if tag D j = true then supp n D (opA D j) ∩ supp n D (opB D j)
      else supp n D (opA D j) ∪ supp n D (opB D j) := by
  ext v
  rw [mem_supp, val_gate hS _ j hj]
  cases tag D j <;> simp [mem_supp]

theorem carrier_flow (h : StrictLive n D) (K : Finset ℕ) (hK : K ⊆ inner n D)
    (hpred : ∀ j, j < D.length → n + j ∈ K → opA D j ∈ K ∨ opB D j ∈ K) :
    (exitArcs n D K).card + (merges n D K).card = (sources n K).card + surplusOn D K := by
  obtain ⟨hS, hL, -⟩ := h
  have hKlt : ∀ w ∈ K, w + 1 < n + D.length := fun w hw => sb_mem_inner.mp (hK hw)
  have h1 : surplusOn D K + K.card = ((arcs D).filter (fun e => src D e ∈ K)).card := by
    rw [← sb_sum_fanout_eq hS, sb_surplus_add_card (fun w hw => hL w (hKlt w hw))]
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (arcs D).filter (fun e => src D e ∈ K)) (fun e : ℕ × Bool => n + e.1 ∈ K)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have h3 : ((arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∈ K)).card =
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card + (merges n D K).card := by
    rw [sb_card_arcs_filter, merges, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have := hpred j (Finset.mem_range.mp hj)
    rw [sb_src_false, sb_src_true]
    by_cases hj2 : n + j ∈ K <;> by_cases ha : opA D j ∈ K <;> by_cases hb : opB D j ∈ K <;>
      simp_all
  have h4 : K.card = (sources n K).card +
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := K) (fun w => w < n), sources]
    congr 1
    have himg : K.filter (fun w => ¬ w < n) =
        ((Finset.range D.length).filter (fun j => n + j ∈ K)).image (fun j => n + j) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hw, hn⟩
        have := hKlt w hw
        exact ⟨w - n, ⟨by omega, by rwa [Nat.add_sub_cancel' (by omega)]⟩, by omega⟩
      · rintro ⟨j, ⟨-, hj⟩, rfl⟩
        exact ⟨hj, by omega⟩
    rw [himg, Finset.card_image_of_injective _ (add_right_injective n)]
  unfold exitArcs
  omega

theorem sb_carrierT_sub (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) : carrierT n D T ⊆ inner n D := by
  intro w hw
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hw
  rw [sb_mem_inner]
  by_contra hc
  have hw2 : w = outW n D := by unfold outW; omega
  rw [hw2, hout] at hw
  exact Finset.not_nonempty_empty hw.2

theorem sb_sources_carrierT (D : Dag) (T : Finset (Fin n)) :
    (sources n (carrierT n D T)).card = T.card := by
  have himg : sources n (carrierT n D T) = T.image (fun v : Fin n => v.val) := by
    ext w
    simp only [sources, carrierT, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨⟨-, v, hv⟩, hw⟩
      have hs : supp n D w = {⟨w, hw⟩} := supp_input D ⟨w, hw⟩
      rw [hs, Finset.mem_inter, Finset.mem_singleton] at hv
      exact ⟨v, hv.2, by rw [hv.1]⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨by have := v.isLt; omega, v, ?_⟩, v.isLt⟩
      rw [supp_input]; simp [hv]
  rw [himg, Finset.card_image_of_injective _ Fin.val_injective]

theorem carrier_flow_union (h : StrictLive n D) (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) :
    (exitArcs n D (carrierT n D T)).card + (merges n D (carrierT n D T)).card =
      T.card + surplusOn D (carrierT n D T) := by
  rw [← sb_sources_carrierT D T]
  refine carrier_flow h _ (sb_carrierT_sub T hout) (fun j hj hK => ?_)
  obtain ⟨ha, hb, -⟩ := h.1 j hj
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hK ⊢
  obtain ⟨v, hv⟩ := hK.2
  rw [Finset.mem_inter, supp_gate h.1 j hj] at hv
  split_ifs at hv with ht
  · rw [Finset.mem_inter] at hv
    exact Or.inl ⟨by omega, v, Finset.mem_inter.mpr ⟨hv.1.1, hv.2⟩⟩
  · rw [Finset.mem_union] at hv
    rcases hv.1 with h1 | h1
    · exact Or.inl ⟨by omega, v, Finset.mem_inter.mpr ⟨h1, hv.2⟩⟩
    · exact Or.inr ⟨by omega, v, Finset.mem_inter.mpr ⟨h1, hv.2⟩⟩

theorem carrier_flow_diff (h : StrictLive n D) (x y : Fin n) (hxy : x ≠ y)
    (hout : x ∉ supp n D (outW n D)) :
    (exitArcs n D (carrierDiff n D x y)).card + (merges n D (carrierDiff n D x y)).card =
      1 + surplusOn D (carrierDiff n D x y) := by
  have hsub : carrierDiff n D x y ⊆ inner n D := by
    intro w hw
    simp only [carrierDiff, Finset.mem_filter, Finset.mem_range] at hw
    rw [sb_mem_inner]
    by_contra hc
    have hw2 : w = outW n D := by unfold outW; omega
    rw [hw2] at hw
    exact hout hw.2.1
  have hsrc : sources n (carrierDiff n D x y) = {x.val} := by
    ext w
    simp only [sources, carrierDiff, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨-, hx, -⟩, hw⟩
      have hs : supp n D w = {⟨w, hw⟩} := supp_input D ⟨w, hw⟩
      rw [hs, Finset.mem_singleton] at hx
      rw [hx]
    · rintro rfl
      refine ⟨⟨by have := x.isLt; omega, ?_, ?_⟩, x.isLt⟩
      · rw [supp_input]; exact Finset.mem_singleton_self x
      · rw [supp_input, Finset.mem_singleton]; exact fun hc => hxy hc.symm
  have hfl := carrier_flow h _ hsub (fun j hj hK => ?_)
  · rw [hsrc, Finset.card_singleton] at hfl; exact hfl
  · obtain ⟨ha, hb, -⟩ := h.1 j hj
    simp only [carrierDiff, Finset.mem_filter, Finset.mem_range] at hK ⊢
    obtain ⟨-, hx, hy⟩ := hK
    rw [supp_gate h.1 j hj] at hx hy
    split_ifs at hx hy with ht
    · rw [Finset.mem_inter] at hx hy
      by_cases hya : y ∈ supp n D (opA D j)
      · exact Or.inr ⟨by omega, hx.2, fun hc => hy ⟨hya, hc⟩⟩
      · exact Or.inl ⟨by omega, hx.1, hya⟩
    · rw [Finset.mem_union] at hx hy
      rcases hx with h1 | h1
      · exact Or.inl ⟨by omega, h1, fun hc => hy (Or.inl hc)⟩
      · exact Or.inr ⟨by omega, h1, fun hc => hy (Or.inr hc)⟩

theorem mem_units {u : Σ _ : ℕ, ℕ} :
    u ∈ units n D ↔ u.1 ∈ inner n D ∧ u.2 + 1 < fanout D u.1 := by
  rw [units, Finset.mem_sigma, Finset.mem_range]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

theorem sb_card_units_filter (n : ℕ) (D : Dag) (p : ℕ → Prop) [DecidablePred p] :
    ((units n D).filter (fun u => p u.1)).card = surplusOn D ((inner n D).filter p) := by
  have hs : (units n D).filter (fun u => p u.1) =
      ((inner n D).filter p).sigma (fun w => Finset.range (fanout D w - 1)) := by
    ext u; simp only [units, Finset.mem_filter, Finset.mem_sigma]; tauto
  rw [hs, Finset.card_sigma, surplusOn]
  simp

theorem card_unitsPlus (n : ℕ) (D : Dag) : (unitsPlus n D).card = Bplus n D := by
  unfold unitsPlus Bplus
  exact sb_card_units_filter n D (fun w => (supp n D w).Nonempty)

theorem mem_eligSet {v : Fin n} :
    v ∈ eligSet n D ↔ ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := by
  simp only [eligSet, branchW, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨w, ⟨-, h2⟩, hv⟩; exact ⟨w, h2, hv⟩
  · rintro ⟨w, h2, hv⟩
    refine ⟨w, ⟨?_, h2⟩, hv⟩
    by_contra hc
    rw [supp_ge D w (by omega)] at hv
    exact Finset.notMem_empty v hv

theorem mem_ineligSet {v : Fin n} :
    v ∈ ineligSet n D ↔ ∀ w, v ∈ supp n D w → fanout D w ≤ 1 := by
  rw [ineligSet, Finset.mem_sdiff, mem_eligSet]
  constructor
  · rintro ⟨-, h⟩ w hw
    by_contra hc
    exact h ⟨w, by omega, hw⟩
  · intro h
    refine ⟨Finset.mem_univ v, ?_⟩
    rintro ⟨w, hw, hv⟩
    have := h w hv
    omega

theorem sb_singleton_inter_nonempty {v : Fin n} {T : Finset (Fin n)} :
    (({v} : Finset (Fin n)) ∩ T).Nonempty ↔ v ∈ T := by
  constructor
  · rintro ⟨u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.1 ▸ hu.2
  · intro h
    exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self v, h⟩⟩

theorem sb_reserved_inj (b : Fin n → ℕ) (hb : PureBranch n D b) :
    Set.InjOn (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) (eligSet n D : Set (Fin n)) := by
  intro v hv v2 hv2 he
  have hbv : b v = b v2 := congrArg Sigma.fst he
  have h1 := (hb v hv).2
  rw [hbv, (hb v2 hv2).2] at h1
  exact (Finset.singleton_injective h1).symm

theorem reserved_subset (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    reservedUnits n D b ⊆ unitsPlus n D := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨h2, hs⟩ := hb v hv
  have h1 : 1 ≤ fanout D (b v) := by omega
  rw [unitsPlus, Finset.mem_filter, mem_units]
  refine ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS h1), ?_⟩, ?_⟩
  · show 0 + 1 < fanout D (b v)
    omega
  · show (supp n D (b v)).Nonempty
    rw [hs]; exact Finset.singleton_nonempty v

theorem card_reserved (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (reservedUnits n D b).card = (eligSet n D).card :=
  Finset.card_image_of_injOn (sb_reserved_inj b hb)

theorem elig_le_Bplus (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (eligSet n D).card ≤ Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_le_card (reserved_subset hS b hb)

theorem card_residual (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (residualUnits n D b).card + (eligSet n D).card = Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_sdiff_add_card_eq_card (reserved_subset hS b hb)

theorem surplus_carrierT_eq (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (T : Finset (Fin n)) :
    surplusOn D (carrierT n D T) = (T ∩ eligSet n D).card +
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
  have h1 : surplusOn D (carrierT n D T) =
      ((units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
    rw [sb_card_units_filter n D (fun w => (supp n D w ∩ T).Nonempty)]
    symm
    refine Finset.sum_subset (fun w hw => ?_) (fun w hw hnot => ?_)
    · rw [Finset.mem_filter] at hw
      have := sb_mem_inner.mp hw.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hw.2⟩
    · rw [carrierT, Finset.mem_filter] at hw
      have hni : w ∉ inner n D := fun hc => hnot (Finset.mem_filter.mpr ⟨hc, hw.2⟩)
      rw [sb_mem_inner] at hni
      simp [fanout_eq_zero_of_ge hS w (by omega)]
  have h2 : (units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) ∪
        (residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) := by
    ext u
    have hsub := reserved_subset hS b hb
    simp only [residualUnits, unitsPlus, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · intro hu
      by_cases hr : u ∈ reservedUnits n D b
      · exact Or.inl ⟨hr, hu.2⟩
      · exact Or.inr ⟨⟨⟨hu.1, hu.2.mono Finset.inter_subset_left⟩, hr⟩, hu.2⟩
    · rintro (hu | hu)
      · exact ⟨(Finset.mem_filter.mp (hsub hu.1)).1, hu.2⟩
      · exact ⟨hu.1.1.1, hu.2⟩
  have h3 : Disjoint ((reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty))
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)) :=
    Finset.disjoint_filter_filter Finset.disjoint_sdiff
  have h4 : (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (T ∩ eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) := by
    rw [reservedUnits, Finset.filter_image]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hv, hne⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty] at hne
      exact ⟨hne, hv⟩
    · rintro ⟨hT, hv⟩
      refine ⟨hv, ?_⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty]
      exact hT
  rw [h1, h2, Finset.card_union_of_disjoint h3, h4,
    Finset.card_image_of_injOn ((sb_reserved_inj b hb).mono
      (Finset.coe_subset.mpr Finset.inter_subset_right))]

theorem surplus_carrierT_le (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (T : Finset (Fin n)) :
    surplusOn D (carrierT n D T) + (eligSet n D).card ≤
      (T ∩ eligSet n D).card + Bplus n D := by
  have h1 := surplus_carrierT_eq hS b hb T
  have h2 := card_residual hS b hb
  have h3 := Finset.card_filter_le (residualUnits n D b)
    (fun u => (supp n D u.1 ∩ T).Nonempty)
  omega

end SurplusFlow

def liftP {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (σ ⟨w, h⟩).val else w

def relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) : Dag :=
  D.map (fun g => (g.1, liftP σ g.2.1, liftP σ g.2.2))

theorem tr_liftP_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : w < n) :
    liftP σ w = (σ ⟨w, h⟩).val := by
  simp [liftP, h]

theorem tr_liftP_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : n ≤ w) : liftP σ w = w := by
  simp [liftP, Nat.not_lt.mpr h]

theorem tr_liftP_lt_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n ≤ m) (w : ℕ) :
    liftP σ w < m ↔ w < m := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h]
    have := (σ ⟨w, h⟩).isLt
    constructor <;> intro <;> omega
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h)]

theorem liftP_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ⁻¹ (liftP σ w) = w := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h, tr_liftP_lt σ⁻¹ (σ ⟨w, h⟩).isLt]; simp
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h), tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]

theorem tr_liftP_inv' {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ (liftP σ⁻¹ w) = w := by
  simpa using liftP_inv σ⁻¹ w

theorem tr_liftP_inj {n : ℕ} (σ : Equiv.Perm (Fin n)) {a b : ℕ} :
    liftP σ a = liftP σ b ↔ a = b := by
  refine ⟨fun h => ?_, congrArg _⟩
  have := congrArg (liftP σ⁻¹) h
  rwa [liftP_inv, liftP_inv] at this

theorem relabel_length {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) :
    (relabel σ D).length = D.length := by
  simp [relabel]

theorem tr_tag {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    tag (relabel σ D) j = tag D j := by
  rw [tag_eq _ j (by rw [relabel_length]; exact hj), tag_eq D j hj]; simp [relabel]

theorem tr_opA {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opA (relabel σ D) j = liftP σ (opA D j) := by
  rw [opA_eq _ j (by rw [relabel_length]; exact hj), opA_eq D j hj]; simp [relabel]

theorem tr_opB {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opB (relabel σ D) j = liftP σ (opB D j) := by
  rw [opB_eq _ j (by rw [relabel_length]; exact hj), opB_eq D j hj]; simp [relabel]

theorem relabel_strict {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Strict n (relabel σ D) := by
  intro j hj
  rw [relabel_length] at hj
  obtain ⟨ha, hb, hab⟩ := hS j hj
  rw [tr_opA σ D j hj, tr_opB σ D j hj]
  exact ⟨(tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr ha,
    (tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr hb, fun h => hab ((tr_liftP_inj σ).mp h)⟩

theorem relabel_val {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (w : ℕ) :
    val (relabel σ D) x (liftP σ w) = val D (fun i => x (σ i)) w := by
  by_cases hw : w < n + D.length
  · refine (val_unique (relabel_strict σ hS) x
      (fun w' => val D (fun i => x (σ i)) (liftP σ⁻¹ w')) ?_ ?_ (liftP σ w) ?_).trans ?_
    · intro i hi
      show val D (fun i => x (σ i)) (liftP σ⁻¹ i) = x ⟨i, hi⟩
      rw [tr_liftP_lt σ⁻¹ hi, val_input D _ _ (σ⁻¹ ⟨i, hi⟩).isLt]
      simp
    · intro j hj
      rw [relabel_length] at hj
      show val D (fun i => x (σ i)) (liftP σ⁻¹ (n + j)) =
        gop (tag (relabel σ D) j) (val D (fun i => x (σ i)) (liftP σ⁻¹ (opA (relabel σ D) j)))
          (val D (fun i => x (σ i)) (liftP σ⁻¹ (opB (relabel σ D) j)))
      rw [tr_liftP_ge σ⁻¹ (Nat.le_add_right n j), tr_tag σ D j hj, tr_opA σ D j hj,
        tr_opB σ D j hj, liftP_inv, liftP_inv, val_gate hS _ j hj]
    · rw [relabel_length]; exact (tr_liftP_lt_iff σ (Nat.le_add_right _ _) w).mpr hw
    · show val D (fun i => x (σ i)) (liftP σ⁻¹ (liftP σ w)) = _
      rw [liftP_inv]
  · have hw' := Nat.not_lt.mp hw
    rw [tr_liftP_ge σ (le_trans (Nat.le_add_right _ _) hw'),
      val_ge _ _ _ (by rw [relabel_length]; exact hw'), val_ge _ _ _ hw']

theorem relabel_fanout {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (w : ℕ) :
    fanout (relabel σ D) (liftP σ w) = fanout D w := by
  unfold fanout readers
  rw [relabel_length]
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [tr_opA σ D j hj', tr_opB σ D j hj', tr_liftP_inj, tr_liftP_inj]

theorem relabel_live {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hL : Live n D) :
    Live n (relabel σ D) := by
  rcases eq_or_ne D [] with rfl | hne
  · exact hL
  · intro w' hw'
    rw [relabel_length] at hw'
    have hpos := List.length_pos_iff.mpr hne
    rw [← tr_liftP_inv' σ w', relabel_fanout]
    apply hL
    by_cases h : w' < n
    · have := (tr_liftP_lt_iff σ⁻¹ le_rfl w').mpr h
      omega
    · rw [tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]; exact hw'

theorem relabel_strictLive {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (h : StrictLive n D) :
    StrictLive n (relabel σ D) :=
  ⟨relabel_strict σ h.1, relabel_live σ h.2.1, by simpa [relabel] using h.2.2⟩

theorem relabel_out {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (hne : D ≠ [])
    (x : Fin n → Bool) :
    val (relabel σ D) x (outW n (relabel σ D)) = val D (fun i => x (σ i)) (outW n D) := by
  have hpos := List.length_pos_iff.mpr hne
  have e : outW n (relabel σ D) = liftP σ (outW n D) := by
    rw [tr_liftP_ge σ (by unfold outW; omega)]; simp [outW, relabel_length]
  rw [e, relabel_val σ hS]

theorem tr_single_comp {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    (fun i => single v (σ i)) = single (σ⁻¹ v) := by
  funext i
  simp only [single, decide_eq_decide]
  constructor
  · intro h; rw [← h]; simp
  · intro h; rw [h]; simp

theorem relabel_supp {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (w : ℕ) :
    supp n (relabel σ D) (liftP σ w) = (supp n D w).image σ := by
  ext v
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [relabel_val σ hS, tr_single_comp]
  constructor
  · intro h; exact ⟨σ⁻¹ v, h, by simp⟩
  · rintro ⟨a, ha, rfl⟩; simpa using ha

theorem relabel_eligSet {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    eligSet n (relabel σ D) = (eligSet n D).image σ := by
  ext v
  simp only [eligSet, Finset.mem_biUnion, Finset.mem_image, branchW, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨w', ⟨hw', hf⟩, hv⟩
    obtain ⟨w, rfl⟩ : ∃ w, w' = liftP σ w := ⟨liftP σ⁻¹ w', (tr_liftP_inv' σ w').symm⟩
    rw [relabel_supp σ hS, Finset.mem_image] at hv
    obtain ⟨a, ha, rfl⟩ := hv
    rw [relabel_fanout] at hf
    rw [relabel_length, tr_liftP_lt_iff σ (Nat.le_add_right _ _)] at hw'
    exact ⟨a, ⟨w, ⟨hw', hf⟩, ha⟩, rfl⟩
  · rintro ⟨a, ⟨w, ⟨hw, hf⟩, ha⟩, rfl⟩
    refine ⟨liftP σ w, ⟨?_, ?_⟩, ?_⟩
    · rw [relabel_length]; exact (tr_liftP_lt_iff σ (Nat.le_add_right _ _) w).mpr hw
    · rw [relabel_fanout]; exact hf
    · rw [relabel_supp σ hS]; exact Finset.mem_image_of_mem _ ha

theorem relabel_ineligSet {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    ineligSet n (relabel σ D) = (ineligSet n D).image σ := by
  ext v
  simp only [ineligSet, relabel_eligSet σ hS, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · intro h
    exact ⟨σ⁻¹ v, fun hm => h ⟨σ⁻¹ v, hm, by simp⟩, by simp⟩
  · rintro ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact ha (σ.injective hab ▸ hb)

theorem inelig_card_add (n : ℕ) (D : Dag) : (ineligSet n D).card + (eligSet n D).card = n := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (eligSet n D))
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

def sem_Edge {n : ℕ} (G : Fin n → Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, G u v ∧ x u = true ∧ x v = true

def sem_Comp (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) : Prop :=
  ∀ x : Fin n → Bool, val D x (outW n D) = true ↔ sem_Edge G x

def sem_Gr {n : ℕ} (G : Fin n → Fin n → Prop) : Prop :=
  (∀ u v, G u v → G v u) ∧ (∀ u, ¬ G u u) ∧ (∀ v w, v ≠ w → ∃ z, G v z ∧ ¬ G w z) ∧
    (∀ u v, ∃ a, G u a ∧ a ≠ v)

def sem_step (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  b < n + D.length ∧ n ≤ b ∧ (opA D (b - n) = a ∨ opB D (b - n) = a)

def sem_two {n : ℕ} (u z : Fin n) : Fin n → Bool := fun i => decide (i = u) || decide (i = z)

def sem_ins {n : ℕ} (v : Fin n) (x : Fin n → Bool) : Fin n → Bool := fun i => decide (i = v) || x i

def sem_ind {n : ℕ} (A : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ A)

theorem sem_rtg_mono {α : Type} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih (h _ _ hbc)

section SemCore

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_ins_agree (v : Fin n) (x : Fin n → Bool) : ∀ k, k ≠ v → x k = sem_ins v x k := by
  intro k hk; simp [sem_ins, hk]

theorem sem_ins_self (v : Fin n) (x : Fin n → Bool) : sem_ins v x v = true := by simp [sem_ins]

theorem sem_ins_ge (v : Fin n) (x : Fin n → Bool) : ∀ i, x i = true → sem_ins v x i = true := by
  intro i hi; simp [sem_ins, hi]

theorem sem_single_le {x : Fin n → Bool} {u : Fin n} (hu : x u = true) :
    ∀ i, single u i = true → x i = true := by
  intro i hi
  simp only [single, decide_eq_true_eq] at hi
  rw [hi]; exact hu

theorem sem_val_of_supp (hS : Strict n D) {u : Fin n} {w : ℕ} (hu : u ∈ supp n D w)
    {x : Fin n → Bool} (hx : x u = true) : val D x w = true :=
  val_mono hS (single u) x (sem_single_le hx) w (mem_supp.mp hu)

theorem sem_supp_lt {v : Fin n} {w : ℕ} (hv : v ∈ supp n D w) : w < n + D.length := by
  by_contra hc
  rw [supp_ge D w (by omega)] at hv
  exact Finset.notMem_empty v hv

theorem sem_supp_and (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    supp n D (n + j) = supp n D (opA D j) ∩ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

theorem sem_supp_or (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = false) :
    supp n D (n + j) = supp n D (opA D j) ∪ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

theorem sem_supp_and_sub (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true)
    (s : Bool) : supp n D (n + j) ⊆ supp n D (src D (j, s)) := by
  rw [sem_supp_and hS hj ht]
  cases s
  · rw [sb_src_false]; exact Finset.inter_subset_left
  · rw [sb_src_true]; exact Finset.inter_subset_right

theorem sem_src_lt (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) < n + j := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  cases s
  · rw [sb_src_false]; exact ha
  · rw [sb_src_true]; exact hb

theorem sem_src_ne (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) ≠ src D (j, !s) := by
  obtain ⟨-, -, hne⟩ := hS j hj
  cases s
  · simpa [src] using hne
  · simpa [src] using hne.symm

theorem sem_step_src {j : ℕ} (hj : j < D.length) (s : Bool) :
    sem_step n D (src D (j, s)) (n + j) := by
  refine ⟨by omega, by omega, ?_⟩
  rw [Nat.add_sub_cancel_left]
  cases s
  · exact Or.inl (sb_src_false j).symm
  · exact Or.inr (sb_src_true j).symm

theorem sem_step_iff {a b : ℕ} : sem_step n D a b ↔
    ∃ j s, j < D.length ∧ b = n + j ∧ src D (j, s) = a := by
  constructor
  · rintro ⟨h1, h2, h3 | h3⟩
    · exact ⟨b - n, false, by omega, by omega, by rw [sb_src_false]; exact h3⟩
    · exact ⟨b - n, true, by omega, by omega, by rw [sb_src_true]; exact h3⟩
  · rintro ⟨j, s, hj, rfl, rfl⟩
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    cases s
    · exact Or.inl (sb_src_false j).symm
    · exact Or.inr (sb_src_true j).symm

theorem sem_step_lt (hS : Strict n D) {a b : ℕ} (h : sem_step n D a b) : a < b := by
  obtain ⟨h1, h2, h3⟩ := h
  have := hS (b - n) (by omega)
  omega

theorem sem_step_reader {a c : ℕ} (h : sem_step n D a c) : c - n ∈ readers D a := by
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by have := h.1; have := h.2.1; omega, h.2.2⟩

theorem sem_step_fanout {a c : ℕ} (h : sem_step n D a c) : 1 ≤ fanout D a :=
  Finset.card_pos.mpr ⟨_, sem_step_reader h⟩

theorem sem_step_unique {a c c' : ℕ} (h1 : sem_step n D a c) (h2 : sem_step n D a c')
    (hf : fanout D a = 1) : c = c' := by
  have m1 := sem_step_reader h1
  have m2 := sem_step_reader h2
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (show (readers D a).card = 1 from hf)
  rw [hr, Finset.mem_singleton] at m1 m2
  have := h1.2.1
  have := h2.2.1
  omega

theorem sem_changed_path (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (w : ℕ) (hw : val D x w ≠ val D y w) :
    Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b) v.val w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn] at hw
      have hwv : (⟨w, hn⟩ : Fin n) = v := by
        by_contra hc; exact hw (hxy _ hc)
      rw [← hwv]
    · by_cases hlt : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        have hg := hw
        rw [val_gate hS x j hj, val_gate hS y j hj] at hg
        by_cases h1 : val D x (opA D j) = val D y (opA D j)
        · have h2 : val D x (opB D j) ≠ val D y (opB D j) := by
            intro h2; apply hg; rw [h1, h2]
          exact Relation.ReflTransGen.tail (ih _ hb h2)
            ⟨⟨hlt, by omega, Or.inr (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
        · exact Relation.ReflTransGen.tail (ih _ ha h1)
            ⟨⟨hlt, by omega, Or.inl (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
      · exfalso; apply hw; rw [val_ge D x w (by omega), val_ge D y w (by omega)]

def sem_Dom (n : ℕ) (D : Dag) (b v : ℕ) : Prop :=
  b = v ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v (outW n D)

theorem sem_dom_eq (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (b : ℕ) (hdom : sem_Dom n D b v.val)
    (hb : val D x b = val D y b) : val D x (outW n D) = val D y (outW n D) := by
  by_contra hne
  rcases hdom with rfl | hdom
  · rw [val_input D x _ v.isLt, val_input D y _ v.isLt] at hb
    have hxy2 : x = y := by
      funext k
      by_cases hk : k = v
      · rw [hk]; exact hb
      · exact hxy k hk
    exact hne (by rw [hxy2])
  · exact hdom (sem_rtg_mono
      (fun a c h => ⟨h.1, fun hc => h.2 (by rw [hc]; exact hb)⟩)
      (sem_changed_path hS x y v hxy _ hne))

def sem_Chain (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  Relation.ReflTransGen (fun a c => sem_step n D a c ∧ fanout D a = 1) a b

theorem sem_chain_dom (hS : Strict n D) {v b : ℕ} (h : sem_Chain n D v b) :
    sem_Dom n D b v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | @head a c hstep _ ih =>
    by_cases hba : b = a
    · exact Or.inl hba
    · right
      intro hp
      rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c', hs, hrest⟩
      · have h0 := fanout_eq_zero_of_ge hS a (by rw [heq]; unfold outW; omega)
        have h1 := hstep.2
        omega
      · have hcc : c = c' := sem_step_unique hstep.1 hs.1 hstep.2
        subst hcc
        rcases ih with rfl | ih
        · exact hs.2 rfl
        · exact ih hrest

theorem sem_carrier_chain (hS : Strict n D) (v : Fin n) : ∀ w, v ∈ supp n D w →
    (∀ u, u < w → v ∈ supp n D u → fanout D u ≤ 1) → sem_Chain n D v.val w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv hlow
    by_cases hn : w < n
    · have hs : supp n D w = {⟨w, hn⟩} := supp_input D ⟨w, hn⟩
      rw [hs, Finset.mem_singleton] at hv
      rw [hv]; exact Relation.ReflTransGen.refl
    · have hlt := sem_supp_lt hv
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      have key : ∀ s : Bool, v ∈ supp n D (src D (j, s)) → sem_Chain n D v.val (n + j) := by
        intro s hva
        have hstep : sem_step n D (src D (j, s)) (n + j) := sem_step_src hj s
        have hlt' := sem_src_lt hS hj s
        have h1 := sem_step_fanout hstep
        have h2 := hlow _ hlt' hva
        exact Relation.ReflTransGen.tail (ih _ hlt' hva (fun u hu => hlow u (by omega)))
          ⟨hstep, by omega⟩
      rw [supp_gate hS j hj] at hv
      split_ifs at hv with ht
      · exact key false (by rw [sb_src_false]; exact (Finset.mem_inter.mp hv).1)
      · rcases Finset.mem_union.mp hv with h1 | h1
        · exact key false (by rw [sb_src_false]; exact h1)
        · exact key true (by rw [sb_src_true]; exact h1)

theorem sem_single_no_edge (hG : sem_Gr G) (v : Fin n) : ¬ sem_Edge G (single v) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [single, decide_eq_true_eq] at ha hc
  rw [ha, hc] at hac
  exact hG.2.1 _ hac

theorem sem_two_edge {u v : Fin n} (huv : G u v) : sem_Edge G (sem_two u v) :=
  ⟨u, v, huv, by simp [sem_two], by simp [sem_two]⟩

theorem sem_supp_out (hG : sem_Gr G) (hC : sem_Comp n G D) : supp n D (outW n D) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2
    (fun v hv => sem_single_no_edge hG v ((hC _).1 (mem_supp.1 hv)))

theorem sem_dom_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
    (b : ℕ) (hdom : sem_Dom n D b v.val) : supp n D b ⊆ {v} := by
  intro u hu
  rw [Finset.mem_singleton]
  by_contra huv
  obtain ⟨hsym, hirr, hsep, -⟩ := hG
  obtain ⟨z, hvz, huz⟩ := hsep v u (Ne.symm huv)
  have hxb : val D (sem_two u z) b = true := sem_val_of_supp hS hu (by simp [sem_two])
  have hyb : val D (sem_ins v (sem_two u z)) b = true :=
    sem_val_of_supp hS hu (by simp [sem_ins, sem_two])
  have hout := sem_dom_eq hS _ _ v (sem_ins_agree v (sem_two u z)) b hdom (by rw [hxb, hyb])
  have h1 : ¬ sem_Edge G (sem_two u z) := by
    rintro ⟨a, c, hac, ha, hc⟩
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at ha hc
    rcases ha with ha | ha <;> rcases hc with hc | hc <;> rw [ha, hc] at hac
    · exact hirr _ hac
    · exact huz hac
    · exact huz (hsym _ _ hac)
    · exact hirr _ hac
  have h2 : sem_Edge G (sem_ins v (sem_two u z)) :=
    ⟨v, z, hvz, sem_ins_self v _, by simp [sem_ins, sem_two]⟩
  have h3 := (hC _).mpr h2
  rw [← hout] at h3
  exact h1 ((hC _).mp h3)

theorem sem_first_branch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
    (hv : v ∈ eligSet n D) :
    ∃ b, 2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b := by
  classical
  have hex : ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := mem_eligSet.mp hv
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  have hch : sem_Chain n D v.val (Nat.find hex) :=
    sem_carrier_chain hS v _ h2 (fun u hu huv => by
      have := Nat.find_min hex hu
      by_contra hc
      exact this ⟨by omega, huv⟩)
  exact ⟨Nat.find hex, h1, Finset.Subset.antisymm
    (sem_dom_pure hG hS hC v _ (sem_chain_dom hS hch)) (Finset.singleton_subset_iff.mpr h2), hch⟩

def sem_FirstBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v)

theorem sem_exists_firstBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, sem_FirstBranch n D b := by
  classical
  have h : ∀ v : Fin n, ∃ b, v ∈ eligSet n D →
      2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b := by
    intro v
    by_cases hv : v ∈ eligSet n D
    · obtain ⟨b, hb⟩ := sem_first_branch hG hS hC v hv
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose b hb using h
  exact ⟨b, fun v hv => hb v hv⟩

theorem sem_firstBranch_pure {b : Fin n → ℕ} (hb : sem_FirstBranch n D b) : PureBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1⟩

theorem sem_exists_pureBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, PureBranch n D b := by
  obtain ⟨b, hb⟩ := sem_exists_firstBranch hG hS hC
  exact ⟨b, sem_firstBranch_pure hb⟩

theorem sem_mem_inelig {v : Fin n} : v ∈ ineligSet n D ↔ v ∉ eligSet n D := by
  simp [ineligSet]

theorem sem_inelig_chain (hS : Strict n D) {v : Fin n} (hv : v ∈ ineligSet n D) {w : ℕ}
    (hw : v ∈ supp n D w) : sem_Chain n D v.val w :=
  sem_carrier_chain hS v w hw (fun u _ hu => mem_ineligSet.mp hv u hu)

theorem sem_inelig_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {v : Fin n}
    (hv : v ∈ ineligSet n D) {w : ℕ} (hw : v ∈ supp n D w) : supp n D w = {v} :=
  Finset.Subset.antisymm (sem_dom_pure hG hS hC v w (sem_chain_dom hS (sem_inelig_chain hS hv hw)))
    (Finset.singleton_subset_iff.mpr hw)

theorem sem_mem_carrier1 {v : Fin n} {w : ℕ} : w ∈ carrierT n D {v} ↔ v ∈ supp n D w := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.2 ▸ hu.1
  · intro h
    exact ⟨sem_supp_lt h, v, Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self v⟩⟩

theorem sem_mem_exit1 {v : Fin n} {e : ℕ × Bool} : e ∈ exitArcs n D (carrierT n D {v}) ↔
    e.1 < D.length ∧ v ∈ supp n D (src D e) ∧ v ∉ supp n D (n + e.1) := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, sem_mem_carrier1]

theorem sem_inelig_surplus {v : Fin n} (hv : v ∈ ineligSet n D) :
    surplusOn D (carrierT n D {v}) = 0 := by
  unfold surplusOn
  refine Finset.sum_eq_zero (fun w hw => ?_)
  have := mem_ineligSet.mp hv w (sem_mem_carrier1.mp hw)
  omega

theorem sem_joint_meeting (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) :
    ∃ j, j < D.length ∧ tag D j = true ∧ val D (sem_two u v) (n + j) = true ∧
      u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) ∧
      ∃ s : Bool, u ∈ supp n D (src D (j, s)) ∧ v ∉ supp n D (src D (j, s)) ∧
        v ∈ supp n D (src D (j, !s)) ∧ u ∉ supp n D (src D (j, !s)) := by
  classical
  have hex : ∃ w, val D (sem_two u v) w = true ∧ u ∉ supp n D w ∧ v ∉ supp n D w :=
    ⟨outW n D, (hC _).2 (sem_two_edge huv), by rw [sem_supp_out hG hC]; simp,
      by rw [sem_supp_out hG hC]; simp⟩
  obtain ⟨hw1, hw2, hw3⟩ := Nat.find_spec hex
  have hmin : ∀ a, a < Nat.find hex → val D (sem_two u v) a = true →
      u ∈ supp n D a ∨ v ∈ supp n D a := by
    intro a ha hva
    by_contra hc
    rw [not_or] at hc
    exact Nat.find_min hex ha ⟨hva, hc.1, hc.2⟩
  generalize Nat.find hex = w at hw1 hw2 hw3 hmin
  have hlt : w < n + D.length := by
    by_contra hc
    rw [val_ge D _ w (by omega)] at hw1
    exact Bool.false_ne_true hw1
  have hn : n ≤ w := by
    by_contra hc
    have hc' : w < n := by omega
    rw [val_input D _ w hc'] at hw1
    have hs : supp n D w = {⟨w, hc'⟩} := supp_input D ⟨w, hc'⟩
    rw [hs, Finset.mem_singleton] at hw2 hw3
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hw1
    rcases hw1 with h | h
    · exact hw2 h.symm
    · exact hw3 h.symm
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hval := hw1
  rw [val_gate hS _ j hj] at hw1
  rw [supp_gate hS j hj] at hw2 hw3
  cases ht : tag D j
  · exfalso
    rw [ht] at hw1 hw2 hw3
    simp only [gop_false, Bool.or_eq_true] at hw1
    simp only [Bool.false_eq_true, ite_false, Finset.mem_union, not_or] at hw2 hw3
    rcases hw1 with h | h
    · rcases hmin _ ha h with h' | h'
      · exact hw2.1 h'
      · exact hw3.1 h'
    · rcases hmin _ hb h with h' | h'
      · exact hw2.2 h'
      · exact hw3.2 h'
  · rw [ht] at hw1 hw2 hw3
    simp only [gop_true, Bool.and_eq_true] at hw1
    simp only [ite_true, Finset.mem_inter, not_and] at hw2 hw3
    have hsupp : u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) := by
      rw [sem_supp_and hS hj ht]
      simp only [Finset.mem_inter, not_and]
      exact ⟨hw2, hw3⟩
    refine ⟨j, hj, ht, hval, hsupp.1, hsupp.2, ?_⟩
    rcases hmin _ ha hw1.1 with hA | hA
    · have hB : u ∉ supp n D (opB D j) := hw2 hA
      have hBv : v ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_left hB
      exact ⟨false, by simpa [src] using hA, by simpa [src] using fun h => hw3 h hBv,
        by simpa [src] using hBv, by simpa [src] using hB⟩
    · have hB : v ∉ supp n D (opB D j) := hw3 hA
      have hBu : u ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_right hB
      exact ⟨true, by simpa [src] using hBu, by simpa [src] using hB,
        by simpa [src] using hA, by simpa [src] using fun h => hw2 h hBu⟩

theorem sem_inelig_consumer (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {v : Fin n} (hv : v ∈ ineligSet n D) :
    ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧ supp n D (src D e) = {v} ∧
      supp n D (n + e.1) = ∅ ∧ (∀ a, G v a → a ∈ supp n D (src D (e.1, !e.2))) ∧
      exitArcs n D (carrierT n D {v}) = {e} ∧ merges n D (carrierT n D {v}) = ∅ := by
  have hS := h.1
  have hfl := carrier_flow_union h {v} (by rw [sem_supp_out hG hC]; simp)
  rw [sem_inelig_surplus hv, Finset.card_singleton] at hfl
  have hmeet : ∀ a, G v a → ∃ j s, j < D.length ∧ tag D j = true ∧
      (j, s) ∈ exitArcs n D (carrierT n D {v}) ∧ a ∈ supp n D (src D (j, !s)) := by
    intro a hva
    obtain ⟨j, hj, ht, -, hju, -, s, h1, -, h3, -⟩ := sem_joint_meeting hG hS hC hva
    exact ⟨j, s, hj, ht, sem_mem_exit1.mpr ⟨hj, h1, hju⟩, h3⟩
  obtain ⟨a0, ha0, -⟩ := hG.2.2.2 v v
  obtain ⟨j0, s0, hj0, ht0, hm0, -⟩ := hmeet a0 ha0
  have hcard : (exitArcs n D (carrierT n D {v})).card = 1 := by
    have := Finset.card_pos.mpr ⟨_, hm0⟩
    omega
  have hmer : merges n D (carrierT n D {v}) = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
  rw [he, Finset.mem_singleton] at hm0
  subst hm0
  have hsrc : supp n D (src D (j0, s0)) = {v} :=
    sem_inelig_pure hG hS hC hv
      (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.1
  have hnot : v ∉ supp n D (n + j0) :=
    (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.2
  refine ⟨(j0, s0), hj0, ht0, hsrc, ?_, ?_, he, hmer⟩
  · refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
    have hx2 := sem_supp_and_sub hS hj0 ht0 s0 hx
    rw [hsrc, Finset.mem_singleton] at hx2
    exact hnot (hx2 ▸ hx)
  · intro a hva
    obtain ⟨j, s, -, -, hm, ha⟩ := hmeet a hva
    rw [he, Finset.mem_singleton] at hm
    rw [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ha

theorem sem_elig_cover (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) : u ∈ eligSet n D ∨ v ∈ eligSet n D := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨eu, -, -, -, -, hnu, hxu, -⟩ := sem_inelig_consumer hG h hC (sem_mem_inelig.mpr hc.1)
  obtain ⟨ev, -, -, hsv, -, -, hxv, -⟩ := sem_inelig_consumer hG h hC (sem_mem_inelig.mpr hc.2)
  obtain ⟨j, hj, -, -, hju, hjv, s, h1, -, h3, -⟩ := sem_joint_meeting hG h.1 hC huv
  have m1 : (j, s) ∈ exitArcs n D (carrierT n D {u}) := sem_mem_exit1.mpr ⟨hj, h1, hju⟩
  have m2 : (j, !s) ∈ exitArcs n D (carrierT n D {v}) := sem_mem_exit1.mpr ⟨hj, h3, hjv⟩
  rw [hxu, Finset.mem_singleton] at m1
  rw [hxv, Finset.mem_singleton] at m2
  subst m1
  subst m2
  obtain ⟨a, hua, hav⟩ := hG.2.2.2 u v
  have h5 : a ∈ supp n D (src D (j, !s)) := hnu a hua
  rw [hsv, Finset.mem_singleton] at h5
  exact hav h5

theorem sem_ind_no_edge {A : Finset (Fin n)} (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) :
    ¬ sem_Edge G (sem_ind A) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [sem_ind, decide_eq_true_eq] at ha hc
  exact hA a ha c hc hac

theorem sem_exposure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (A : Finset (Fin n)) (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) (x : Fin n)
    (hnb : ∃ a ∈ A, G x a) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ x ∈ supp n D (src D (j, s)) ∧
      x ∉ supp n D (n + j) ∧ Disjoint (supp n D (src D (j, s))) A := by
  by_contra hcon
  have hmask : ∀ j s, j < D.length → tag D j = true → x ∈ supp n D (src D (j, s)) →
      x ∉ supp n D (n + j) → val D (sem_ind A) (src D (j, s)) = true ∧
        val D (sem_ins x (sem_ind A)) (src D (j, s)) = true := by
    intro j s hj ht h1 h2
    have hnd : ¬ Disjoint (supp n D (src D (j, s))) A :=
      fun hd => hcon ⟨j, s, hj, ht, h1, h2, hd⟩
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨a, ha1, ha2⟩ := hnd
    exact ⟨sem_val_of_supp hS ha1 (by simp [sem_ind, ha2]),
      sem_val_of_supp hS ha1 (by simp [sem_ins, sem_ind, ha2])⟩
  have key : ∀ w, x ∉ supp n D w → val D (sem_ind A) w = val D (sem_ins x (sem_ind A)) w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hn : w < n
      · rw [val_input D _ w hn, val_input D _ w hn]
        have hs : supp n D w = {⟨w, hn⟩} := supp_input D ⟨w, hn⟩
        rw [hs, Finset.mem_singleton] at hw
        exact sem_ins_agree x _ _ (fun hc => hw hc.symm)
      · by_cases hlt : w < n + D.length
        · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
          have hj : j < D.length := by omega
          obtain ⟨ha, hb, -⟩ := hS j hj
          rw [val_gate hS _ j hj, val_gate hS _ j hj]
          cases ht : tag D j
          · rw [sem_supp_or hS hj ht, Finset.mem_union, not_or] at hw
            rw [ih _ ha hw.1, ih _ hb hw.2]
          · have hw2 := hw
            rw [sem_supp_and hS hj ht, Finset.mem_inter, not_and] at hw2
            by_cases hxa : x ∈ supp n D (opA D j)
            · have h1 := hmask j false hj ht (by rw [sb_src_false]; exact hxa) hw
              rw [sb_src_false] at h1
              rw [ih _ hb (hw2 hxa), h1.1, h1.2]
            · by_cases hxb : x ∈ supp n D (opB D j)
              · have h1 := hmask j true hj ht (by rw [sb_src_true]; exact hxb) hw
                rw [sb_src_true] at h1
                rw [ih _ ha hxa, h1.1, h1.2]
              · rw [ih _ ha hxa, ih _ hb hxb]
        · rw [val_ge D _ w (by omega), val_ge D _ w (by omega)]
  have hout := key (outW n D) (by rw [sem_supp_out hG hC]; exact Finset.notMem_empty x)
  obtain ⟨a, ha, hxa⟩ := hnb
  have h2 : sem_Edge G (sem_ins x (sem_ind A)) :=
    ⟨x, a, hxa, sem_ins_self x _, by simp [sem_ins, sem_ind, ha]⟩
  have h3 := (hC _).mpr h2
  rw [← hout] at h3
  exact sem_ind_no_edge hA ((hC _).mp h3)

theorem sem_first_mask (hS : Strict n D) (T M : Finset (Fin n)) (hM : 2 ≤ M.card) (w : ℕ)
    (hw : supp n D w ∩ T = M) :
    ∃ j, j < D.length ∧ n + j ≤ w ∧ supp n D (n + j) ∩ T = M ∧
      j ∈ merges n D (carrierT n D T) ∧ (∀ u, u < n + j → supp n D u ∩ T ≠ M) ∧
      ((tag D j = true ∧ M ⊂ supp n D (opA D j) ∩ T ∧ M ⊂ supp n D (opB D j) ∩ T) ∨
        (tag D j = false ∧ supp n D (opA D j) ∩ T ⊂ M ∧ supp n D (opB D j) ∩ T ⊂ M ∧
          (supp n D (opA D j) ∩ T) ∪ (supp n D (opB D j) ∩ T) = M ∧
          (supp n D (opA D j) ∩ T).Nonempty ∧ (supp n D (opB D j) ∩ T).Nonempty)) := by
  classical
  have hex : ∃ u, supp n D u ∩ T = M := ⟨w, hw⟩
  have hle : Nat.find hex ≤ w := Nat.find_min' hex hw
  have hmin : ∀ u, u < Nat.find hex → supp n D u ∩ T ≠ M := fun u hu => Nat.find_min hex hu
  have hspec := Nat.find_spec hex
  generalize Nat.find hex = f at hle hmin hspec
  have hMne : M.Nonempty := Finset.card_pos.mp (by omega)
  have hmem : ∀ {u : ℕ}, (supp n D u ∩ T).Nonempty → u ∈ carrierT n D T := by
    intro u hu
    obtain ⟨v, hv⟩ := hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (sem_supp_lt (Finset.mem_inter.mp hv).1), v, hv⟩
  have hflt : f < n + D.length := by
    obtain ⟨v, hv⟩ := hMne
    rw [← hspec] at hv
    exact sem_supp_lt (Finset.mem_inter.mp hv).1
  have hfn : n ≤ f := by
    by_contra hc
    have hc' : f < n := by omega
    have hs : supp n D f = {⟨f, hc'⟩} := supp_input D ⟨f, hc'⟩
    have h1 : M.card ≤ 1 := by
      rw [← hspec, hs]
      exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
    omega
  obtain ⟨j, rfl⟩ : ∃ j, f = n + j := ⟨f - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hna := hmin _ ha
  have hnb := hmin _ hb
  refine ⟨j, hj, hle, hspec, ?_, hmin, ?_⟩
  · have hAB : (supp n D (opA D j) ∩ T).Nonempty ∧ (supp n D (opB D j) ∩ T).Nonempty := by
      cases ht : tag D j
      · rw [sem_supp_or hS hj ht, Finset.union_inter_distrib_right] at hspec
        constructor
        · rw [Finset.nonempty_iff_ne_empty]
          intro he
          rw [he, Finset.empty_union] at hspec
          exact hnb hspec
        · rw [Finset.nonempty_iff_ne_empty]
          intro he
          rw [he, Finset.union_empty] at hspec
          exact hna hspec
      · rw [sem_supp_and hS hj ht] at hspec
        obtain ⟨v, hv⟩ := hMne
        rw [← hspec] at hv
        simp only [Finset.mem_inter] at hv
        exact ⟨⟨v, Finset.mem_inter.mpr ⟨hv.1.1, hv.2⟩⟩, ⟨v, Finset.mem_inter.mpr ⟨hv.1.2, hv.2⟩⟩⟩
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, hmem (by rw [hspec]; exact hMne), hmem hAB.1, hmem hAB.2⟩
  · cases ht : tag D j
    · right
      rw [sem_supp_or hS hj ht, Finset.union_inter_distrib_right] at hspec
      have hsa : supp n D (opA D j) ∩ T ⊆ M := by rw [← hspec]; exact Finset.subset_union_left
      have hsb : supp n D (opB D j) ∩ T ⊆ M := by rw [← hspec]; exact Finset.subset_union_right
      refine ⟨rfl, Finset.ssubset_iff_subset_ne.mpr ⟨hsa, hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb, hnb⟩, hspec, ?_, ?_⟩
      · rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he, Finset.empty_union] at hspec
        exact hnb hspec
      · rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he, Finset.union_empty] at hspec
        exact hna hspec
    · left
      rw [sem_supp_and hS hj ht] at hspec
      have hsa : M ⊆ supp n D (opA D j) ∩ T := by
        rw [← hspec]
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        exact ⟨hv.1.1, hv.2⟩
      have hsb : M ⊆ supp n D (opB D j) ∩ T := by
        rw [← hspec]
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        exact ⟨hv.1.2, hv.2⟩
      exact ⟨rfl, Finset.ssubset_iff_subset_ne.mpr ⟨hsa, Ne.symm hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb, Ne.symm hnb⟩⟩

end SemCore

def sem_W (n : ℕ) (D : Dag) (x : Fin n) : Finset (ℕ × Bool) := exitArcs n D (carrierT n D {x})

def sem_bar (e : ℕ × Bool) : ℕ × Bool := (e.1, !e.2)

section SemCodes

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_mem_W {x : Fin n} {e : ℕ × Bool} : e ∈ sem_W n D x ↔
    e.1 < D.length ∧ x ∈ supp n D (src D e) ∧ x ∉ supp n D (n + e.1) := sem_mem_exit1

theorem sem_bar_bar (e : ℕ × Bool) : sem_bar (sem_bar e) = e := by simp [sem_bar]

theorem sem_bar_ne (e : ℕ × Bool) : sem_bar e ≠ e := by
  intro h
  have h2 := congrArg Prod.snd h
  simp [sem_bar] at h2

theorem sem_same_gate {e f : ℕ × Bool} (h : e.1 = f.1) : f = e ∨ f = sem_bar e := by
  obtain ⟨j, s⟩ := e
  obtain ⟨k, t⟩ := f
  simp only at h
  subst h
  cases s <;> cases t <;> simp [sem_bar]

theorem sem_W_and (hS : Strict n D) {x : Fin n} {e : ℕ × Bool} (he : e ∈ sem_W n D x) :
    tag D e.1 = true := by
  obtain ⟨hj, h1, h2⟩ := sem_mem_W.mp he
  by_contra ht
  rw [Bool.not_eq_true] at ht
  apply h2
  rw [sem_supp_or hS hj ht, Finset.mem_union]
  obtain ⟨j, s⟩ := e
  cases s
  · left; simpa [src] using h1
  · right; simpa [src] using h1

theorem sem_flow1 (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (x : Fin n) :
    (sem_W n D x).card + (merges n D (carrierT n D {x})).card =
      1 + surplusOn D (carrierT n D {x}) := by
  have h1 := carrier_flow_union h {x} (by rw [sem_supp_out hG hC]; simp)
  rwa [Finset.card_singleton] at h1

theorem sem_edge_slots (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {x y : Fin n}
    (hxy : G x y) : ∃ e, e ∈ sem_W n D x ∧ sem_bar e ∈ sem_W n D y ∧
      y ∉ supp n D (src D e) ∧ x ∉ supp n D (src D (sem_bar e)) ∧
      val D (sem_two x y) (n + e.1) = true := by
  obtain ⟨j, hj, -, hval, hju, hjv, s, h1, h2, h3, h4⟩ := sem_joint_meeting hG hS hC hxy
  exact ⟨(j, s), sem_mem_W.mpr ⟨hj, h1, hju⟩, sem_mem_W.mpr ⟨hj, h3, hjv⟩, h2, h4, hval⟩

theorem sem_cover_free (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x a b y : Fin n} (hab : ¬ G a b) (hxy : G x y) (hya : ¬ G y a) (hyb : ¬ G y b) :
    ∃ e, e ∈ sem_W n D x ∧ a ∉ supp n D (src D e) ∧ b ∉ supp n D (src D e) := by
  have hsym := hG.1
  have hirr := hG.2.1
  have hA : ∀ u ∈ ({a, b, y} : Finset (Fin n)), ∀ v ∈ ({a, b, y} : Finset (Fin n)),
      ¬ G u v := by
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> rw [hu, hv]
    · exact hirr a
    · exact hab
    · exact fun h => hya (hsym _ _ h)
    · exact fun h => hab (hsym _ _ h)
    · exact hirr b
    · exact fun h => hyb (hsym _ _ h)
    · exact hya
    · exact hyb
    · exact hirr y
  obtain ⟨j, s, hj, -, h1, h2, hd⟩ := sem_exposure hG hS hC {a, b, y} hA x ⟨y, by simp, hxy⟩
  exact ⟨(j, s), sem_mem_W.mpr ⟨hj, h1, h2⟩, fun h => Finset.disjoint_left.mp hd h (by simp),
    fun h => Finset.disjoint_left.mp hd h (by simp)⟩

end SemCodes

theorem sem_rtg_comparable {α : Type} {R : α → α → Prop}
    (hfun : ∀ a a' b, R a b → R a' b → a = a') {u v c : α}
    (hu : Relation.ReflTransGen R u c) (hv : Relation.ReflTransGen R v c) :
    Relation.ReflTransGen R u v ∨ Relation.ReflTransGen R v u := by
  induction hu with
  | refl => exact Or.inr hv
  | tail hab hbc ih =>
    rcases Relation.ReflTransGen.cases_tail hv with h | ⟨b', hvb', hb'c⟩
    · left
      rw [← h]
      exact Relation.ReflTransGen.tail hab hbc
    · have hbb : b' = _ := hfun _ _ _ hb'c hbc
      rw [hbb] at hvb'
      exact ih hvb'

def sem_MinBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v) ∧
    ∀ w, 2 ≤ fanout D w → v ∈ supp n D w → b v ≤ w

def sem_Arm (n : ℕ) (D : Dag) (X : Finset (Fin n)) (a b : ℕ) : Prop :=
  sem_step n D a b ∧ fanout D a = 1 ∧ ∀ x ∈ X, x ∈ supp n D a ∧ x ∈ supp n D b

section SemArms

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_rtg_le (hS : Strict n D) {R : ℕ → ℕ → Prop} (hR : ∀ a b, R a b → sem_step n D a b)
    {a b : ℕ} (h : Relation.ReflTransGen R a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans ih (le_of_lt (sem_step_lt hS (hR _ _ hbc)))

theorem sem_exists_minBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, sem_MinBranch n D b := by
  classical
  have h : ∀ v : Fin n, ∃ b, v ∈ eligSet n D →
      2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b ∧
        ∀ w, 2 ≤ fanout D w → v ∈ supp n D w → b ≤ w := by
    intro v
    by_cases hv : v ∈ eligSet n D
    · have hex : ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := mem_eligSet.mp hv
      obtain ⟨h1, h2⟩ := Nat.find_spec hex
      have hch : sem_Chain n D v.val (Nat.find hex) :=
        sem_carrier_chain hS v _ h2 (fun u hu huv => by
          have := Nat.find_min hex hu
          by_contra hc
          exact this ⟨by omega, huv⟩)
      exact ⟨Nat.find hex, fun _ => ⟨h1, Finset.Subset.antisymm
        (sem_dom_pure hG hS hC v _ (sem_chain_dom hS hch)) (Finset.singleton_subset_iff.mpr h2),
        hch, fun w hw1 hw2 => Nat.find_min' hex ⟨hw1, hw2⟩⟩⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose b hb using h
  exact ⟨b, fun v hv => hb v hv⟩

theorem sem_minBranch_pure {b : Fin n → ℕ} (hb : sem_MinBranch n D b) : PureBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1⟩

theorem sem_zm_gate (hS : Strict n D) {x : Fin n} (hM : merges n D (carrierT n D {x}) = ∅)
    {j : ℕ} (hj : j < D.length) (hx : x ∈ supp n D (n + j)) :
    tag D j = false ∧ ¬ (x ∈ supp n D (opA D j) ∧ x ∈ supp n D (opB D j)) := by
  have hnot : ¬ (x ∈ supp n D (opA D j) ∧ x ∈ supp n D (opB D j)) := by
    intro hc
    have hm : j ∈ merges n D (carrierT n D {x}) := by
      rw [merges, Finset.mem_filter, Finset.mem_range]
      exact ⟨hj, sem_mem_carrier1.mpr hx, sem_mem_carrier1.mpr hc.1, sem_mem_carrier1.mpr hc.2⟩
    rw [hM] at hm
    exact Finset.notMem_empty _ hm
  refine ⟨?_, hnot⟩
  by_contra ht
  rw [Bool.not_eq_false] at ht
  rw [sem_supp_and hS hj ht, Finset.mem_inter] at hx
  exact hnot hx

theorem sem_code_count (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) (x : Fin n) :
    (sem_W n D x).card + (merges n D (carrierT n D {x})).card =
      1 + (({x} : Finset (Fin n)) ∩ eligSet n D).card +
        ((residualUnits n D b).filter (fun u => x ∈ supp n D u.1)).card := by
  have h1 := sem_flow1 hG h hC x
  have h2 := surplus_carrierT_eq h.1 b hb {x}
  have h3 : (residualUnits n D b).filter (fun u => (supp n D u.1 ∩ {x}).Nonempty) =
      (residualUnits n D b).filter (fun u => x ∈ supp n D u.1) := by
    refine Finset.filter_congr (fun u _ => ?_)
    constructor
    · rintro ⟨y, hy⟩
      rw [Finset.mem_inter, Finset.mem_singleton] at hy
      exact hy.2 ▸ hy.1
    · intro hx
      exact ⟨x, Finset.mem_inter.mpr ⟨hx, Finset.mem_singleton_self x⟩⟩
  rw [h3] at h2
  omega

theorem sem_descent (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (X : Finset (Fin n)) (hX : X.Nonempty)
    (hM : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅) :
    ∀ c, (∀ x ∈ X, x ∈ supp n D c) →
      (∀ x ∈ X, ∀ w, c ≤ w → x ∈ supp n D w → fanout D w ≤ 1) →
      ∃ e : ℕ × Bool, (∀ x ∈ X, e ∈ sem_W n D x) ∧
        Relation.ReflTransGen (sem_Arm n D X) c (src D e) := by
  classical
  have hS := h.1
  obtain ⟨x0, hx0⟩ := hX
  intro c
  generalize hk : n + D.length - c = k
  induction k using Nat.strong_induction_on generalizing c with
  | _ k ih =>
    intro hc hlow
    have hclt := sem_supp_lt (hc x0 hx0)
    have hcne : c ≠ outW n D := by
      intro he
      have := hc x0 hx0
      rw [he, sem_supp_out hG hC] at this
      exact Finset.notMem_empty _ this
    have hf1 : 1 ≤ fanout D c := h.2.1 c (by unfold outW at hcne; omega)
    have hf : fanout D c = 1 := le_antisymm (hlow x0 hx0 c (le_refl c) (hc x0 hx0)) hf1
    obtain ⟨j, hjr⟩ := Finset.card_pos.mp hf1
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hjr
    obtain ⟨hj, hop⟩ := hjr
    obtain ⟨s, hs⟩ : ∃ s : Bool, src D (j, s) = c := by
      rcases hop with h1 | h1
      · exact ⟨false, by rw [sb_src_false]; exact h1⟩
      · exact ⟨true, by rw [sb_src_true]; exact h1⟩
    have hcj : c < n + j := hs ▸ sem_src_lt hS hj s
    by_cases hcar : ∃ x1 ∈ X, x1 ∈ supp n D (n + j)
    · obtain ⟨x1, hx1, hx1c⟩ := hcar
      have ht := (sem_zm_gate hS (hM x1 hx1) hj hx1c).1
      have hall : ∀ x ∈ X, x ∈ supp n D (n + j) := by
        intro x hx
        rw [sem_supp_or hS hj ht, Finset.mem_union]
        rcases hop with h1 | h1
        · left; rw [h1]; exact hc x hx
        · right; rw [h1]; exact hc x hx
      obtain ⟨e, he1, he2⟩ := ih (n + D.length - (n + j)) (by omega) (n + j) rfl hall
        (fun x hx w hw => hlow x hx w (by omega))
      refine ⟨e, he1, Relation.ReflTransGen.head ⟨?_, hf, fun x hx => ⟨hc x hx, hall x hx⟩⟩ he2⟩
      rw [← hs]
      exact sem_step_src hj s
    · refine ⟨(j, s), fun x hx => sem_mem_W.mpr ⟨hj, ?_, fun hc2 => hcar ⟨x, hx, hc2⟩⟩, ?_⟩
      · rw [hs]; exact hc x hx
      · rw [hs]

theorem sem_two_arms (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (X : Finset (Fin n)) (hX : X.Nonempty)
    (hM : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅) (r : ℕ)
    (hr : ∀ x ∈ X, x ∈ supp n D r) (hf : 2 ≤ fanout D r)
    (hlow : ∀ x ∈ X, ∀ w, r < w → x ∈ supp n D w → fanout D w ≤ 1) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧ ∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x := by
  classical
  have hS := h.1
  obtain ⟨x0, hx0⟩ := hX
  obtain ⟨j1, hj1, j2, hj2, hne⟩ := Finset.one_lt_card.mp (show 1 < (readers D r).card from hf)
  have hread : ∀ j ∈ readers D r, j < D.length ∧ r < n + j ∧ (opA D j = r ∨ opB D j = r) := by
    intro j hj
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hj
    have := hS j hj.1
    exact ⟨hj.1, by omega, hj.2⟩
  have hterm : ∀ j ∈ readers D r, ∃ e : ℕ × Bool, (∀ x ∈ X, e ∈ sem_W n D x) ∧
      ((e.1 = j ∧ src D e = r) ∨ Relation.ReflTransGen (sem_Arm n D X) (n + j) (src D e)) := by
    intro j hj
    obtain ⟨hjl, hrj, hop⟩ := hread j hj
    obtain ⟨s, hs⟩ : ∃ s : Bool, src D (j, s) = r := by
      rcases hop with h1 | h1
      · exact ⟨false, by rw [sb_src_false]; exact h1⟩
      · exact ⟨true, by rw [sb_src_true]; exact h1⟩
    by_cases hcar : ∃ x1 ∈ X, x1 ∈ supp n D (n + j)
    · obtain ⟨x1, hx1, hx1c⟩ := hcar
      have ht := (sem_zm_gate hS (hM x1 hx1) hjl hx1c).1
      have hall : ∀ x ∈ X, x ∈ supp n D (n + j) := by
        intro x hx
        rw [sem_supp_or hS hjl ht, Finset.mem_union]
        rcases hop with h1 | h1
        · left; rw [h1]; exact hr x hx
        · right; rw [h1]; exact hr x hx
      obtain ⟨e, he1, he2⟩ := sem_descent hG h hC X ⟨x0, hx0⟩ hM (n + j) hall
        (fun x hx w hw => hlow x hx w (by omega))
      exact ⟨e, he1, Or.inr he2⟩
    · exact ⟨(j, s), fun x hx => sem_mem_W.mpr ⟨hjl, by rw [hs]; exact hr x hx,
        fun hc2 => hcar ⟨x, hx, hc2⟩⟩, Or.inl ⟨rfl, hs⟩⟩
  have hRstep : ∀ a b, sem_Arm n D X a b → sem_step n D a b := fun _ _ hab => hab.1
  have hfun : ∀ a a' b, sem_Arm n D X a b → sem_Arm n D X a' b → a = a' := by
    intro a a' b h1 h2
    by_contra hne2
    obtain ⟨hb1, hb2, hba⟩ := h1.1
    obtain ⟨-, -, hba'⟩ := h2.1
    have hjb : b - n < D.length := by omega
    have hcarb : x0 ∈ supp n D (n + (b - n)) := by
      rw [Nat.add_sub_cancel' hb2]; exact (h1.2.2 x0 hx0).2
    apply (sem_zm_gate hS (hM x0 hx0) hjb hcarb).2
    have ha := (h1.2.2 x0 hx0).1
    have ha' := (h2.2.2 x0 hx0).1
    rcases hba with e1 | e1 <;> rcases hba' with e2 | e2
    · exact absurd (e1.symm.trans e2) hne2
    · rw [e1, e2]; exact ⟨ha, ha'⟩
    · rw [e1, e2]; exact ⟨ha', ha⟩
    · exact absurd (e1.symm.trans e2) hne2
  have hcross : ∀ ja ∈ readers D r, ∀ jb ∈ readers D r, ja ≠ jb →
      ¬ Relation.ReflTransGen (sem_Arm n D X) (n + ja) (n + jb) := by
    intro ja hja jb hjb hab hp
    obtain ⟨hjla, hrja, -⟩ := hread ja hja
    obtain ⟨hjlb, hrjb, hopb⟩ := hread jb hjb
    rcases Relation.ReflTransGen.cases_tail hp with heq | ⟨u, hu1, hu2⟩
    · exact hab (by omega)
    · have hle := sem_rtg_le hS hRstep hu1
      have hur : u = r := by
        by_contra hur
        obtain ⟨-, -, hbu⟩ := hu2.1
        rw [Nat.add_sub_cancel_left] at hbu
        apply (sem_zm_gate hS (hM x0 hx0) hjlb (hu2.2.2 x0 hx0).2).2
        have hu := (hu2.2.2 x0 hx0).1
        have hrr := hr x0 hx0
        rcases hbu with e1 | e1 <;> rcases hopb with e2 | e2
        · exact absurd (e1.symm.trans e2) hur
        · rw [e1, e2]; exact ⟨hu, hrr⟩
        · rw [e1, e2]; exact ⟨hrr, hu⟩
        · exact absurd (e1.symm.trans e2) hur
      omega
  obtain ⟨P, hP1, hP2⟩ := hterm j1 hj1
  obtain ⟨Q, hQ1, hQ2⟩ := hterm j2 hj2
  refine ⟨P, Q, fun hPQ => ?_, fun x hx => ⟨hP1 x hx, hQ1 x hx⟩⟩
  have hsame : Q = P := by
    rcases sem_same_gate hPQ with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨hjP, hxP, hnP⟩ := sem_mem_W.mp (hP1 x0 hx0)
      have hxQ := (sem_mem_W.mp (hQ1 x0 hx0)).2.1
      rw [h1] at hxQ
      apply hnP
      rw [sem_supp_and hS hjP (sem_W_and hS (hP1 x0 hx0)), Finset.mem_inter]
      obtain ⟨j, s⟩ := P
      cases s
      · exact ⟨by simpa [src] using hxP, by simpa [src, sem_bar] using hxQ⟩
      · exact ⟨by simpa [src, sem_bar] using hxQ, by simpa [src] using hxP⟩
  rw [hsame] at hQ2
  obtain ⟨-, hrj1, -⟩ := hread j1 hj1
  obtain ⟨-, hrj2, -⟩ := hread j2 hj2
  rcases hP2 with ⟨hPa, hPb⟩ | hPp <;> rcases hQ2 with ⟨hQa, hQb⟩ | hQp
  · exact hne (hPa.symm.trans hQa)
  · have := sem_rtg_le hS hRstep hQp
    omega
  · have := sem_rtg_le hS hRstep hPp
    omega
  · rcases sem_rtg_comparable hfun hPp hQp with h1 | h1
    · exact hcross j1 hj1 j2 hj2 hne h1
    · exact hcross j2 hj2 j1 hj1 (Ne.symm hne) h1

theorem sem_saturated (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {u0 : Σ _ : ℕ, ℕ}
    (hres : residualUnits n D b = {u0}) {x : Fin n} (hsat : 3 ≤ (sem_W n D x).card) :
    (sem_W n D x).card = 3 ∧ merges n D (carrierT n D {x}) = ∅ ∧ x ∈ eligSet n D ∧
      x ∈ supp n D u0.1 := by
  have h1 := sem_code_count hG h hC b hb x
  have h2 : (({x} : Finset (Fin n)) ∩ eligSet n D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have h3 := Finset.card_filter_le (residualUnits n D b) (fun u => x ∈ supp n D u.1)
  rw [hres, Finset.card_singleton] at h3
  rw [hres] at h1
  refine ⟨by omega, Finset.card_eq_zero.mp (by omega), ?_, ?_⟩
  · by_contra hx
    have h4 : ({x} : Finset (Fin n)) ∩ eligSet n D = ∅ := by
      rw [Finset.singleton_inter_of_notMem hx]
    rw [h4, Finset.card_empty] at h1
    omega
  · have h4 : 0 < (({u0} : Finset (Σ _ : ℕ, ℕ)).filter (fun u => x ∈ supp n D u.1)).card := by
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp h4
    rw [Finset.mem_filter, Finset.mem_singleton] at hu
    exact hu.1 ▸ hu.2

theorem sem_common_terminals (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : sem_MinBranch n D b) (hone : Bplus n D = (eligSet n D).card + 1)
    (X : Finset (Fin n)) (hX : X.Nonempty) (hsat : ∀ x ∈ X, 3 ≤ (sem_W n D x).card) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧ ∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x := by
  have hS := h.1
  have hbp := sem_minBranch_pure hb
  have hcard : (residualUnits n D b).card = 1 := by
    have := card_residual hS b hbp
    omega
  obtain ⟨u0, hres⟩ := Finset.card_eq_one.mp hcard
  have hu0 : u0 ∈ residualUnits n D b := by rw [hres]; exact Finset.mem_singleton_self _
  have hu0u : u0 ∈ units n D :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu0).1).1
  have hfr : 2 ≤ fanout D u0.1 := by
    have := (mem_units.mp hu0u).2
    omega
  refine sem_two_arms hG h hC X hX (fun x hx => (sem_saturated hG h hC b hbp hres (hsat x hx)).2.1)
    u0.1 (fun x hx => (sem_saturated hG h hC b hbp hres (hsat x hx)).2.2.2) hfr ?_
  intro x hx w hrw hxw
  obtain ⟨-, -, hxe, hxr⟩ := sem_saturated hG h hC b hbp hres (hsat x hx)
  by_contra hc
  have hw2 : 2 ≤ fanout D w := by omega
  have hwu : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus n D := by
    rw [unitsPlus, Finset.mem_filter, mem_units]
    exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)), by show 0 + 1 < fanout D w; omega⟩,
      ⟨x, hxw⟩⟩
  by_cases hwr : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits n D b
  · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hwr
    have hbv : b v = w := congrArg Sigma.fst hveq
    have hsv := (hb v hv).2.1
    rw [hbv] at hsv
    rw [hsv, Finset.mem_singleton] at hxw
    have hmin := (hb x hxe).2.2.2 u0.1 hfr hxr
    rw [hxw, hbv] at hmin
    omega
  · have hwres : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ residualUnits n D b :=
      Finset.mem_sdiff.mpr ⟨hwu, hwr⟩
    rw [hres, Finset.mem_singleton] at hwres
    have : w = u0.1 := congrArg Sigma.fst hwres
    omega

end SemArms

section SemPaths

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_ind_single (a : Fin n) : sem_ind ({a} : Finset (Fin n)) = single a := by
  funext k; simp [sem_ind, single]

theorem sem_val_gate_src (hS : Strict n D) (x : Fin n → Bool) {j : ℕ} (hj : j < D.length)
    (s : Bool) : val D x (n + j) =
      gop (tag D j) (val D x (src D (j, s))) (val D x (src D (j, !s))) := by
  rw [val_gate hS x j hj]
  cases s
  · simp [src]
  · cases tag D j <;> simp [src, Bool.and_comm, Bool.or_comm]

theorem sem_ins_ind_edge (hG : sem_Gr G) {i : Fin n} {S : Finset (Fin n)}
    (h : sem_Edge G (sem_ins i (sem_ind S))) :
    (∃ a ∈ S, G i a) ∨ ∃ a ∈ S, ∃ b ∈ S, G a b := by
  obtain ⟨u, v, huv, hu, hv⟩ := h
  simp only [sem_ins, sem_ind, Bool.or_eq_true, decide_eq_true_eq] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · rw [hu, hv] at huv; exact absurd huv (hG.2.1 i)
  · rw [hu] at huv; exact Or.inl ⟨v, hv, huv⟩
  · rw [hv] at huv; exact Or.inl ⟨u, hu, hG.1 _ _ huv⟩
  · exact Or.inr ⟨u, hu, v, hv, huv⟩

theorem sem_chain_dom_at (hS : Strict n D) {v b t : ℕ} (h : sem_Chain n D v b) (hbt : b ≤ t) :
    b = v ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | @head a c hstep hrest ih =>
    by_cases hba : b = a
    · exact Or.inl hba
    · right
      intro hp
      rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c', hs, hrest'⟩
      · have h1 := sem_step_lt hS hstep.1
        have h2 := sem_rtg_le hS (fun _ _ hab => hab.1) hrest
        omega
      · have hcc : c = c' := sem_step_unique hstep.1 hs.1 hstep.2
        subst hcc
        rcases ih with rfl | ih
        · exact hs.2 rfl
        · exact ih hrest'

theorem sem_dom_eq_at (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (b t : ℕ)
    (hdom : b = v.val ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v.val t)
    (hb : val D x b = val D y b) : val D x t = val D y t := by
  by_contra hne
  rcases hdom with rfl | hdom
  · rw [val_input D x _ v.isLt, val_input D y _ v.isLt] at hb
    have hxy2 : x = y := by
      funext k
      by_cases hk : k = v
      · rw [hk]; exact hb
      · exact hxy k hk
    exact hne (by rw [hxy2])
  · exact hdom (sem_rtg_mono
      (fun a c h => ⟨h.1, fun hc => h.2 (by rw [hc]; exact hb)⟩)
      (sem_changed_path hS x y v hxy _ hne))

theorem sem_chain_fork (hS : Strict n D) {a c q : ℕ} (hc : sem_Chain n D a c)
    (hq : Relation.ReflTransGen (sem_step n D) a q) :
    Relation.ReflTransGen (sem_step n D) c q ∨ (sem_Chain n D q c ∧ q ≠ c) := by
  revert hq
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hq => Or.inl hq
  | @head a a' hstep hrest ih =>
    intro hq
    rcases Relation.ReflTransGen.cases_head hq with heq | ⟨a'', hs, hrest'⟩
    · right
      have h1 := sem_step_lt hS hstep.1
      have h2 := sem_rtg_le hS (fun _ _ hab => hab.1) hrest
      refine ⟨?_, by omega⟩
      rw [← heq]
      exact Relation.ReflTransGen.head hstep hrest
    · have hcc : a' = a'' := sem_step_unique hstep.1 hs hstep.2
      subst hcc
      exact ih hrest'

theorem sem_sibling_indep (hS : Strict n D) (v : Fin n) {j : ℕ} (hj : j < D.length) (s : Bool)
    (hch : sem_Chain n D v.val (src D (j, !s))) (hf : fanout D (src D (j, !s)) = 1)
    (x y : Fin n → Bool) (hxy : ∀ k, k ≠ v → x k = y k) :
    val D x (src D (j, s)) = val D y (src D (j, s)) := by
  by_contra hne
  have hp : Relation.ReflTransGen (sem_step n D) v.val (src D (j, s)) :=
    sem_rtg_mono (fun _ _ h => h.1) (sem_changed_path hS x y v hxy _ hne)
  have hstepc : sem_step n D (src D (j, !s)) (n + j) := sem_step_src hj (!s)
  have hstepq : sem_step n D (src D (j, s)) (n + j) := sem_step_src hj s
  have hlt1 := sem_src_lt hS hj s
  have hlt2 := sem_src_lt hS hj (!s)
  rcases sem_chain_fork hS hch hp with h1 | ⟨h1, h2⟩
  · rcases Relation.ReflTransGen.cases_head h1 with heq | ⟨c', hs, hrest⟩
    · exact sem_src_ne hS hj s heq.symm
    · have hcc : n + j = c' := sem_step_unique hstepc hs hf
      subst hcc
      have := sem_rtg_le hS (fun _ _ h => h) hrest
      omega
  · rcases Relation.ReflTransGen.cases_head h1 with heq | ⟨q', hs, hrest⟩
    · exact h2 heq
    · have hcc : n + j = q' := sem_step_unique hstepq hs.1 hs.2
      subst hcc
      have := sem_rtg_le hS (fun _ _ h => h.1) hrest
      omega

theorem sem_dom_split (hS : Strict n D) (hC : sem_Comp n G D) (x : Fin n → Bool) (v : Fin n)
    (b : ℕ) (hdom : sem_Dom n D b v.val) (h0 : ¬ sem_Edge G x) (h1 : sem_Edge G (sem_ins v x)) :
    val D x b = false ∧ val D (sem_ins v x) b = true := by
  have hne : val D x b ≠ val D (sem_ins v x) b := by
    intro heq
    have h2 := sem_dom_eq hS x _ v (sem_ins_agree v x) b hdom heq
    exact h0 ((hC x).mp (by rw [h2]; exact (hC _).mpr h1))
  have hmono := val_mono hS x (sem_ins v x) (sem_ins_ge v x) b
  cases hx : val D x b
  · refine ⟨rfl, ?_⟩
    cases hy : val D (sem_ins v x) b
    · exact absurd (hx.trans hy.symm) hne
    · rfl
  · exact absurd (hx.trans (hmono hx).symm) hne

theorem sem_factor (hS : Strict n D) (i : Fin n) (w : ℕ) (hch : sem_Chain n D i.val w)
    (Bs N : Finset (Fin n)) (hN : N ⊆ Bs)
    (h0 : val D (sem_ins i (sem_ind (Bs \ N))) w = false)
    (h1 : ∀ a ∈ N, val D (sem_ins i (sem_ind {a})) w = true)
    (hz : ∀ a ∈ N, val D (sem_ind {a}) w = false) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ w ∧
      sem_Chain n D i.val (src D (j, !s)) ∧ supp n D (src D (j, s)) ∩ Bs = N := by
  have hJ : ∀ c, sem_Chain n D i.val c → (val D (sem_ins i (sem_ind (Bs \ N))) c = true ∨
      ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ c ∧ sem_Chain n D i.val (src D (j, !s)) ∧
        fanout D (src D (j, !s)) = 1 ∧ val D (sem_ind (Bs \ N)) (src D (j, s)) = false) := by
    intro c hc
    induction hc with
    | refl => left; rw [val_input D _ _ i.isLt]; exact sem_ins_self i _
    | tail hab hbc ih =>
      obtain ⟨j, s, hj, rfl, rfl⟩ := sem_step_iff.mp hbc.1
      have hlt := sem_src_lt hS hj s
      rcases ih with hy | ⟨j', s', hj', ht', hle, hc', hf', hv'⟩
      · cases ht : tag D j
        · left
          rw [sem_val_gate_src hS _ hj s, ht, gop_false, hy]
          rfl
        · by_cases hq : val D (sem_ins i (sem_ind (Bs \ N))) (src D (j, !s)) = true
          · left
            rw [sem_val_gate_src hS _ hj s, ht, gop_true, hy, hq]
            rfl
          · right
            refine ⟨j, !s, hj, ht, le_refl _, by rw [Bool.not_not]; exact hab,
              by rw [Bool.not_not]; exact hbc.2, ?_⟩
            by_contra hc2
            rw [Bool.not_eq_false] at hc2
            exact hq (val_mono hS _ _ (sem_ins_ge i _) _ hc2)
      · right
        exact ⟨j', s', hj', ht', by omega, hc', hf', hv'⟩
  rcases hJ w hch with hy | ⟨j, s, hj, ht, hle, hc, hf, hv⟩
  · rw [h0] at hy
    exact absurd hy Bool.false_ne_true
  · refine ⟨j, s, hj, ht, hle, hc, ?_⟩
    have hchg : sem_Chain n D i.val (n + j) :=
      Relation.ReflTransGen.tail hc ⟨sem_step_src hj (!s), hf⟩
    ext a
    rw [Finset.mem_inter]
    constructor
    · rintro ⟨ha1, ha2⟩
      by_contra haN
      have := sem_val_of_supp hS ha1 (x := sem_ind (Bs \ N))
        (by simp [sem_ind, ha2, haN])
      rw [hv] at this
      exact Bool.false_ne_true this
    · intro haN
      refine ⟨?_, hN haN⟩
      have hgne : val D (sem_ind {a}) (n + j) ≠ val D (sem_ins i (sem_ind {a})) (n + j) := by
        intro heq
        have h2 := sem_dom_eq_at hS _ _ i (sem_ins_agree i (sem_ind {a})) (n + j) w
          (sem_chain_dom_at hS hchg hle) heq
        rw [hz a haN, h1 a haN] at h2
        exact Bool.false_ne_true h2
      have hgy : val D (sem_ins i (sem_ind {a})) (n + j) = true := by
        by_contra hc2
        rw [Bool.not_eq_true] at hc2
        apply hgne
        rw [hc2]
        by_contra hc3
        rw [Bool.not_eq_false] at hc3
        rw [val_mono hS _ _ (sem_ins_ge i _) _ hc3] at hc2
        exact Bool.noConfusion hc2
      rw [sem_val_gate_src hS _ hj s, ht, gop_true, Bool.and_eq_true] at hgy
      have hind := sem_sibling_indep hS i hj s hc hf _ _ (sem_ins_agree i (sem_ind {a}))
      rw [hgy.1, sem_ind_single] at hind
      exact mem_supp.mpr hind

theorem sem_exact_at (hS : Strict n D) (i : Fin n) (w : ℕ) (hch : sem_Chain n D i.val w)
    (Bs : Finset (Fin n))
    (h0 : ∀ S : Finset (Fin n), S ⊆ Bs → (∀ a ∈ S, ¬ G i a) →
      val D (sem_ins i (sem_ind S)) w = false)
    (h1 : ∀ a ∈ Bs, G i a →
      val D (sem_ins i (sem_ind {a})) w = true ∧ val D (sem_ind {a}) w = false) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ w ∧
      sem_Chain n D i.val (src D (j, !s)) ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (j, s)) ↔ G i a) := by
  classical
  obtain ⟨j, s, hj, ht, hle, hc, hsupp⟩ := sem_factor hS i w hch Bs (Bs.filter (fun a => G i a))
    (Finset.filter_subset _ _)
    (h0 _ Finset.sdiff_subset (fun a ha hia => by
      rw [Finset.mem_sdiff, Finset.mem_filter] at ha
      exact ha.2 ⟨ha.1, hia⟩))
    (fun a ha => (h1 a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2).1)
    (fun a ha => (h1 a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2).2)
  refine ⟨j, s, hj, ht, hle, hc, fun a ha => ?_⟩
  constructor
  · intro has
    have : a ∈ supp n D (src D (j, s)) ∩ Bs := Finset.mem_inter.mpr ⟨has, ha⟩
    rw [hsupp, Finset.mem_filter] at this
    exact this.2
  · intro hia
    have : a ∈ Bs.filter (fun a => G i a) := Finset.mem_filter.mpr ⟨ha, hia⟩
    rw [← hsupp] at this
    exact (Finset.mem_inter.mp this).1

theorem sem_branch_empty (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {i : Fin n}
    (hi : i ∈ ineligSet n D) {b : ℕ} (hch : sem_Chain n D i.val b) (hf : 2 ≤ fanout D b) :
    supp n D b = ∅ := by
  have hsub := sem_dom_pure hG hS hC i b (sem_chain_dom hS hch)
  refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
  have h1 := hsub hx
  rw [Finset.mem_singleton] at h1
  have h2 := mem_ineligSet.mp hi b (h1 ▸ hx)
  omega

theorem sem_path_chain {a t : ℕ} (hp : Relation.ReflTransGen (sem_step n D) a t) :
    sem_Chain n D a t ∨ ∃ b, sem_Chain n D a b ∧ 2 ≤ fanout D b := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @head a a' hstep _ ih =>
    by_cases hf : fanout D a = 1
    · rcases ih with h1 | ⟨b, h1, h2⟩
      · exact Or.inl (Relation.ReflTransGen.head ⟨hstep, hf⟩ h1)
      · exact Or.inr ⟨b, Relation.ReflTransGen.head ⟨hstep, hf⟩ h1, h2⟩
    · have := sem_step_fanout hstep
      exact Or.inr ⟨a, Relation.ReflTransGen.refl, by omega⟩

theorem sem_inelig_reach (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {i : Fin n} (hi : i ∈ ineligSet n D) :
    sem_Chain n D i.val (outW n D) ∨
      ∃ b, sem_Chain n D i.val b ∧ 2 ≤ fanout D b ∧ supp n D b = ∅ := by
  have hlt : i.val < n + D.length := by have := i.isLt; omega
  have hp : Relation.ReflTransGen (sem_step n D) i.val (outW n D) := live_reaches_out h i.val hlt
  rcases sem_path_chain hp with h1 | ⟨b, h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨b, h1, h2, sem_branch_empty hG h.1 hC hi h1 h2⟩

theorem sem_bzero_mem (hS : Strict n D) {b : ℕ} (hf : 2 ≤ fanout D b) (he : supp n D b = ∅) :
    b ∈ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) :=
  Finset.mem_filter.mpr ⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := b) (by omega)),
    by rw [he]; exact Finset.not_nonempty_empty⟩

theorem sem_bzero_branch (hS : Strict n D) (hB0 : Bzero n D = 0) {b : ℕ} (hf : 2 ≤ fanout D b) :
    (supp n D b).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have h1 : fanout D b - 1 ≤ ∑ w ∈ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty),
      (fanout D w - 1) :=
    Finset.single_le_sum (f := fun w => fanout D w - 1) (fun _ _ => Nat.zero_le _)
      (sem_bzero_mem hS hf hne)
  unfold Bzero surplusOn at hB0
  omega

theorem sem_bzero_unique (hS : Strict n D) (hB0 : Bzero n D ≤ 1) {b b' : ℕ}
    (hf : 2 ≤ fanout D b) (he : supp n D b = ∅) (hf' : 2 ≤ fanout D b')
    (he' : supp n D b' = ∅) : b = b' := by
  by_contra hne
  have hsub : ({b, b'} : Finset ℕ) ⊆ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) := by
    intro c hc
    rw [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact sem_bzero_mem hS hf he
    · exact sem_bzero_mem hS hf' he'
  have h1 := Finset.sum_le_sum_of_subset (f := fun w => fanout D w - 1) hsub
  rw [Finset.sum_pair hne] at h1
  unfold Bzero surplusOn at hB0
  omega

theorem sem_noempty_unique (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D) {w : ℕ}
    (hp : Relation.ReflTransGen (sem_step n D) i.val w) : sem_Chain n D i.val w := by
  rcases sem_path_chain hp with h1 | ⟨b, h1, h2⟩
  · exact h1
  · have h3 := sem_bzero_branch h.1 hB0 h2
    rw [sem_branch_empty hG h.1 hC hi h1 h2] at h3
    exact absurd h3 Finset.not_nonempty_empty

theorem sem_noempty_chain_out (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D) :
    sem_Chain n D i.val (outW n D) :=
  sem_noempty_unique hG h hC hB0 hi
    (live_reaches_out h i.val (by have := i.isLt; omega))

theorem sem_exact_nbhd (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (Bs : Finset (Fin n)) (hBs : ∀ a ∈ Bs, ∀ b ∈ Bs, ¬ G a b) {i : Fin n}
    (hch : sem_Chain n D i.val (outW n D)) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ sem_Chain n D i.val (src D (j, !s)) ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (j, s)) ↔ G i a) := by
  obtain ⟨j, s, hj, ht, -, hc, hsupp⟩ := sem_exact_at (G := G) hS i (outW n D) hch Bs
    (fun S hS1 hS2 => by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      rcases sem_ins_ind_edge hG ((hC _).mp hc) with ⟨a, ha, hia⟩ | ⟨a, ha, b, hb, hab⟩
      · exact hS2 a ha hia
      · exact hBs a (hS1 ha) b (hS1 hb) hab)
    (fun a _ hia => by
      constructor
      · exact (hC _).mpr ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, sem_ind]⟩
      · by_contra hc
        rw [Bool.not_eq_false, sem_ind_single] at hc
        exact sem_single_no_edge hG a ((hC _).mp hc))
  exact ⟨j, s, hj, ht, hc, hsupp⟩

theorem sem_shared_exact (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (Bs : Finset (Fin n)) (hBs : ∀ a ∈ Bs, ∀ b ∈ Bs, ¬ G a b) {i j : Fin n} {w : ℕ}
    (hch : sem_Chain n D i.val w) (hdj : sem_Dom n D w j.val)
    (hnsub : ∃ a ∈ Bs, G j a ∧ ¬ G i a) :
    ∃ k s, k < D.length ∧ tag D k = true ∧ n + k ≤ w ∧
      sem_Chain n D i.val (src D (k, !s)) ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (k, s)) ↔ G i a) := by
  classical
  have hX0 : ¬ sem_Edge G (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a)))) := by
    intro hc
    rcases sem_ins_ind_edge hG hc with ⟨a, ha, hia⟩ | ⟨a, ha, b, hb, hab⟩
    · exact (Finset.mem_filter.mp ha).2 hia
    · exact hBs a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
  obtain ⟨a0, ha0, hja0, hia0⟩ := hnsub
  have hX1 : sem_Edge G (sem_ins j (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a))))) :=
    ⟨j, a0, hja0, sem_ins_self j _, by simp [sem_ins, sem_ind, ha0, hia0]⟩
  have hwX := (sem_dom_split hS hC _ j w hdj hX0 hX1).1
  refine sem_exact_at hS i w hch Bs (fun S hS1 hS2 => ?_) (fun a _ hia => ?_)
  · by_contra hc
    rw [Bool.not_eq_false] at hc
    have hmono := val_mono hS (sem_ins i (sem_ind S))
      (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a)))) (fun k hk => by
        simp only [sem_ins, sem_ind, Bool.or_eq_true, decide_eq_true_eq] at hk ⊢
        rcases hk with hk | hk
        · exact Or.inl hk
        · exact Or.inr (Finset.mem_filter.mpr ⟨hS1 hk, hS2 k hk⟩)) w hc
    rw [hwX] at hmono
    exact Bool.false_ne_true hmono
  · have h2 := sem_dom_split hS hC (sem_ind {a}) i w (sem_chain_dom hS hch)
      (by rw [sem_ind_single]; exact sem_single_no_edge hG a)
      ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, sem_ind]⟩
    exact ⟨h2.2, h2.1⟩

theorem sem_shared_empty (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D ≤ 1) (Bs : Finset (Fin n)) (hBs : ∀ a ∈ Bs, ∀ b ∈ Bs, ¬ G a b)
    {i j : Fin n} (hi : i ∈ ineligSet n D) (hj : j ∈ ineligSet n D)
    (hji : ∃ a ∈ Bs, G j a ∧ ¬ G i a) :
    (∃ k s, k < D.length ∧ tag D k = true ∧ sem_Chain n D i.val (src D (k, !s)) ∧
        ∀ a ∈ Bs, (a ∈ supp n D (src D (k, s)) ↔ G i a)) ∨
      (∃ k s, k < D.length ∧ tag D k = true ∧ sem_Chain n D j.val (src D (k, !s)) ∧
        ∀ a ∈ Bs, (a ∈ supp n D (src D (k, s)) ↔ G j a)) := by
  have hS := h.1
  rcases sem_inelig_reach hG h hC hi with h1 | ⟨b, hb1, hb2, hb3⟩
  · exact Or.inl (sem_exact_nbhd hG hS hC Bs hBs h1)
  · rcases sem_inelig_reach hG h hC hj with h1 | ⟨b', hb1', hb2', hb3'⟩
    · exact Or.inr (sem_exact_nbhd hG hS hC Bs hBs h1)
    · have hbb : b' = b := sem_bzero_unique hS hB0 hb2' hb3' hb2 hb3
      rw [hbb] at hb1'
      obtain ⟨k, s, hk, ht, -, hc, hsupp⟩ := sem_shared_exact hG hS hC Bs hBs hb1
        (sem_chain_dom hS hb1') hji
      exact Or.inl ⟨k, s, hk, ht, hc, hsupp⟩

end SemPaths

section SemDiff

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_mem_diff {x y : Fin n} {w : ℕ} :
    w ∈ carrierDiff n D x y ↔ x ∈ supp n D w ∧ y ∉ supp n D w := by
  simp only [carrierDiff, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨sem_supp_lt h.1, h⟩⟩

theorem sem_mem_exit_diff {x y : Fin n} {e : ℕ × Bool} :
    e ∈ exitArcs n D (carrierDiff n D x y) ↔ e.1 < D.length ∧
      (x ∈ supp n D (src D e) ∧ y ∉ supp n D (src D e)) ∧
      ¬ (x ∈ supp n D (n + e.1) ∧ y ∉ supp n D (n + e.1)) := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, sem_mem_diff]

theorem sem_surplus_diff (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    {x y : Fin n} (hxy : x ≠ y) (hx : x ∈ eligSet n D) :
    surplusOn D (carrierDiff n D x y) = 1 + ((residualUnits n D b).filter
      (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1)).card := by
  have h1 : surplusOn D (carrierDiff n D x y) =
      ((units n D).filter (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1)).card := by
    rw [sb_card_units_filter n D (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)]
    symm
    refine Finset.sum_subset (fun w hw => ?_) (fun w hw hnot => ?_)
    · rw [Finset.mem_filter] at hw
      exact sem_mem_diff.mpr hw.2
    · have hni : w ∉ inner n D := fun hc => hnot (Finset.mem_filter.mpr ⟨hc, sem_mem_diff.mp hw⟩)
      rw [sb_mem_inner] at hni
      simp [fanout_eq_zero_of_ge hS w (by omega)]
  have h2 : (units n D).filter (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1) =
      {(⟨b x, 0⟩ : Σ _ : ℕ, ℕ)} ∪ (residualUnits n D b).filter
        (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1) := by
    ext u
    have hsub := reserved_subset hS b hb
    simp only [residualUnits, unitsPlus, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_singleton]
    constructor
    · intro hu
      by_cases hr : u ∈ reservedUnits n D b
      · left
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
        have hxv := hu.2.1
        rw [(hb v hv).2, Finset.mem_singleton] at hxv
        rw [hxv]
      · exact Or.inr ⟨⟨⟨hu.1, ⟨x, hu.2.1⟩⟩, hr⟩, hu.2⟩
    · rintro (rfl | hu)
      · have hbx := hb x hx
        refine ⟨(Finset.mem_filter.mp (hsub (Finset.mem_image.mpr ⟨x, hx, rfl⟩))).1, ?_, ?_⟩
        · rw [hbx.2]; exact Finset.mem_singleton_self x
        · rw [hbx.2, Finset.mem_singleton]; exact fun hc => hxy hc.symm
      · exact ⟨hu.1.1.1, hu.2⟩
  have h3 : (⟨b x, 0⟩ : Σ _ : ℕ, ℕ) ∉ (residualUnits n D b).filter
      (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1) := by
    intro hc
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hc).1).2 (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  rw [h1, h2, Finset.singleton_union, Finset.card_insert_of_notMem h3]
  omega

theorem sem_first_joint (hS : Strict n D) {x y : Fin n} (hxy : x ≠ y) {w : ℕ}
    (hw : x ∈ supp n D w ∧ y ∈ supp n D w) :
    ∃ j s, j < D.length ∧ tag D j = false ∧ x ∈ supp n D (n + j) ∧ y ∈ supp n D (n + j) ∧
      x ∈ supp n D (src D (j, s)) ∧ y ∉ supp n D (src D (j, s)) ∧
      y ∈ supp n D (src D (j, !s)) ∧ x ∉ supp n D (src D (j, !s)) := by
  classical
  have hex : ∃ u, x ∈ supp n D u ∧ y ∈ supp n D u := ⟨w, hw⟩
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  have hmin : ∀ u, u < Nat.find hex → ¬ (x ∈ supp n D u ∧ y ∈ supp n D u) :=
    fun u hu => Nat.find_min hex hu
  generalize Nat.find hex = f at h1 h2 hmin
  have hlt := sem_supp_lt h1
  have hn : n ≤ f := by
    by_contra hc
    have hs : supp n D f = {⟨f, by omega⟩} := supp_input D ⟨f, by omega⟩
    rw [hs, Finset.mem_singleton] at h1 h2
    exact hxy (h1.trans h2.symm)
  obtain ⟨j, rfl⟩ : ∃ j, f = n + j := ⟨f - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hna := hmin _ ha
  have hnb := hmin _ hb
  cases ht : tag D j
  · have h1' := h1
    have h2' := h2
    rw [sem_supp_or hS hj ht, Finset.mem_union] at h1' h2'
    refine ⟨j, ?_⟩
    rcases h1' with hxa | hxb
    · have hya : y ∉ supp n D (opA D j) := fun hc => hna ⟨hxa, hc⟩
      have hyb : y ∈ supp n D (opB D j) := h2'.resolve_left hya
      exact ⟨false, hj, ht, h1, h2, by simpa [src] using hxa, by simpa [src] using hya,
        by simpa [src] using hyb, by simpa [src] using fun hc => hnb ⟨hc, hyb⟩⟩
    · have hyb : y ∉ supp n D (opB D j) := fun hc => hnb ⟨hxb, hc⟩
      have hya : y ∈ supp n D (opA D j) := h2'.resolve_right hyb
      exact ⟨true, hj, ht, h1, h2, by simpa [src] using hxb, by simpa [src] using hyb,
        by simpa [src] using hya, by simpa [src] using fun hc => hna ⟨hc, hya⟩⟩
  · exfalso
    rw [sem_supp_and hS hj ht, Finset.mem_inter] at h1 h2
    exact hna ⟨h1.1, h2.1⟩

theorem sem_diff_two_exits (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {x c z : Fin n} (hxc : x ≠ c)
    (hx : x ∈ eligSet n D)
    (hres : ∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → c ∈ supp n D u.1)
    {w : ℕ} (hw : x ∈ supp n D w ∧ c ∈ supp n D w) (hxz : G x z) (hcz : ¬ G c z) :
    surplusOn D (carrierDiff n D x c) = 1 ∧ merges n D (carrierDiff n D x c) = ∅ ∧
      (exitArcs n D (carrierDiff n D x c)).card = 2 ∧
      ∃ e ∈ exitArcs n D (carrierDiff n D x c), tag D e.1 = false ∧ c ∈ supp n D (n + e.1) := by
  have hS := h.1
  have hsur : surplusOn D (carrierDiff n D x c) = 1 := by
    rw [sem_surplus_diff hS b hb hxc hx, Finset.filter_eq_empty_iff.mpr
      (fun u hu hc => hc.2 (hres u hu hc.1)), Finset.card_empty]
  have hfl := carrier_flow_diff h x c hxc
    (by rw [sem_supp_out hG hC]; exact Finset.notMem_empty x)
  rw [hsur] at hfl
  obtain ⟨j1, s1, hj1, ht1, hx1, hc1, hxs1, hcs1, -, -⟩ := sem_first_joint hS hxc hw
  have he1 : (j1, s1) ∈ exitArcs n D (carrierDiff n D x c) :=
    sem_mem_exit_diff.mpr ⟨hj1, ⟨hxs1, hcs1⟩, fun hc => hc.2 hc1⟩
  have hA : ∀ u ∈ ({c, z} : Finset (Fin n)), ∀ v ∈ ({c, z} : Finset (Fin n)), ¬ G u v := by
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv]
    · exact hG.2.1 c
    · exact hcz
    · exact fun hc => hcz (hG.1 _ _ hc)
    · exact hG.2.1 z
  obtain ⟨j2, s2, hj2, -, hx2, hn2, hd2⟩ := sem_exposure hG hS hC {c, z} hA x ⟨z, by simp, hxz⟩
  have he2 : (j2, s2) ∈ exitArcs n D (carrierDiff n D x c) :=
    sem_mem_exit_diff.mpr ⟨hj2, ⟨hx2, fun hc => Finset.disjoint_left.mp hd2 hc (by simp)⟩,
      fun hc => hn2 hc.1⟩
  have hne : (j1, s1) ≠ (j2, s2) := by
    intro heq
    rw [Prod.mk.injEq] at heq
    exact hn2 (heq.1 ▸ hx1)
  have h2 : 2 ≤ (exitArcs n D (carrierDiff n D x c)).card :=
    Finset.one_lt_card.mpr ⟨_, he1, _, he2, hne⟩
  exact ⟨hsur, Finset.card_eq_zero.mp (by omega), by omega, (j1, s1), he1, ht1, hc1⟩

end SemDiff

def sup_Occ (n : ℕ) (D : Dag) (P M : Finset (Fin n)) : Prop := ∃ w, supp n D w ∩ P = M

def sup_big (n : ℕ) (D : Dag) (P : Finset (Fin n)) : Finset ℕ :=
  (merges n D (carrierT n D P)).filter (fun j => 2 ≤ (supp n D (n + j) ∩ P).card)

def sup_Wit (n : ℕ) (D : Dag) (P U : Finset (Fin n)) (f : Fin n) (e : ℕ × Bool) : Prop :=
  e.1 < D.length ∧ tag D e.1 = true ∧ f ∈ P ∧ f ∈ supp n D (src D e) ∧
    f ∉ supp n D (n + e.1) ∧ supp n D (src D e) ∩ P ⊆ U ∧ (supp n D (src D e) ∩ P).card ≤ 2

def sup_cost (n : ℕ) (D : Dag) (P : Finset (Fin n)) (e : ℕ × Bool) : (ℕ × Bool) ⊕ ℕ :=
  if supp n D (n + e.1) ∩ P = ∅ then Sum.inl e else Sum.inr e.1

def sup_CostOK (n : ℕ) (D : Dag) (P : Finset (Fin n)) (c : (ℕ × Bool) ⊕ ℕ) : Prop :=
  Sum.elim (fun e => e ∈ exitArcs n D (carrierT n D P) ∧ (supp n D (src D e) ∩ P).card ≤ 2)
    (fun j => j ∈ merges n D (carrierT n D P) ∧ (supp n D (n + j) ∩ P).card = 1) c

section SupMask

variable {n : ℕ} {D : Dag}

theorem sup_occ_wire (P : Finset (Fin n)) (w : ℕ) : sup_Occ n D P (supp n D w ∩ P) := ⟨w, rfl⟩

theorem sup_occ_sub {P M : Finset (Fin n)} (h : sup_Occ n D P M) : M ⊆ P := by
  obtain ⟨w, rfl⟩ := h
  exact Finset.inter_subset_right

theorem sup_mem_carrier {P : Finset (Fin n)} {w : ℕ} :
    w ∈ carrierT n D P ↔ (supp n D w ∩ P).Nonempty := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨v, hv⟩ := h
    exact ⟨sem_supp_lt (Finset.mem_inter.mp hv).1, v, hv⟩

theorem sup_occ_big (hS : Strict n D) {P M : Finset (Fin n)} (hM : 2 ≤ M.card)
    (h : sup_Occ n D P M) : ∃ j ∈ sup_big n D P, supp n D (n + j) ∩ P = M := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨j, -, -, hj, hmer, -, -⟩ := sem_first_mask hS P M hM w hw
  exact ⟨j, Finset.mem_filter.mpr ⟨hmer, by rw [hj]; exact hM⟩, hj⟩

theorem sup_card_le_big (hS : Strict n D) (P : Finset (Fin n)) (F : Finset (Finset (Fin n)))
    (hF : ∀ M ∈ F, 2 ≤ M.card ∧ sup_Occ n D P M) : F.card ≤ (sup_big n D P).card := by
  have hsub : F ⊆ (sup_big n D P).image (fun j => supp n D (n + j) ∩ P) := by
    intro M hM
    obtain ⟨j, hj, hjM⟩ := sup_occ_big hS (hF M hM).1 (hF M hM).2
    exact Finset.mem_image.mpr ⟨j, hj, hjM⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem sup_triple_parent (hS : Strict n D) {P T : Finset (Fin n)} (hP : P.card ≤ 7)
    (hT : T.card = 3) (h : sup_Occ n D P T) :
    (∃ A, sup_Occ n D P A ∧ A.card = 2 ∧ A ⊆ T) ∨
      (∃ A, sup_Occ n D P A ∧ A.card = 4 ∧ T ⊆ A) ∨
      (∃ A B, A ≠ B ∧ sup_Occ n D P A ∧ sup_Occ n D P B ∧ A.card = 5 ∧ B.card = 5 ∧
        T ⊆ A ∧ T ⊆ B ∧ A ∩ B = T) := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨j, hj, -, hjT, -, -, hpar⟩ := sem_first_mask hS P T (by omega) w hw
  have hoA : sup_Occ n D P (supp n D (opA D j) ∩ P) := sup_occ_wire P _
  have hoB : sup_Occ n D P (supp n D (opB D j) ∩ P) := sup_occ_wire P _
  rcases hpar with ⟨ht, hA, hB⟩ | ⟨-, hA, hB, hun, -, -⟩
  · have hAB : (supp n D (opA D j) ∩ P) ∩ (supp n D (opB D j) ∩ P) = T := by
      rw [← hjT, sem_supp_and hS hj ht]
      ext v
      simp only [Finset.mem_inter]
      tauto
    generalize supp n D (opA D j) ∩ P = A at hoA hA hAB
    generalize supp n D (opB D j) ∩ P = B at hoB hB hAB
    have hcA := Finset.card_lt_card hA
    have hcB := Finset.card_lt_card hB
    have hu : (A ∪ B).card ≤ 7 :=
      (Finset.card_le_card (Finset.union_subset (sup_occ_sub hoA) (sup_occ_sub hoB))).trans hP
    have hie := Finset.card_union_add_card_inter A B
    rw [hAB] at hie
    by_cases h4 : A.card = 4
    · exact Or.inr (Or.inl ⟨A, hoA, h4, hA.subset⟩)
    by_cases h4' : B.card = 4
    · exact Or.inr (Or.inl ⟨B, hoB, h4', hB.subset⟩)
    refine Or.inr (Or.inr ⟨A, B, ?_, hoA, hoB, by omega, by omega, hA.subset, hB.subset, hAB⟩)
    intro hEq
    rw [hEq, Finset.inter_self] at hAB
    rw [hAB] at hcB
    omega
  · generalize supp n D (opA D j) ∩ P = A at hoA hA hun
    generalize supp n D (opB D j) ∩ P = B at hoB hB hun
    have hcA := Finset.card_lt_card hA
    have hcB := Finset.card_lt_card hB
    have hc := Finset.card_union_le A B
    rw [hun] at hc
    by_cases h2 : A.card = 2
    · exact Or.inl ⟨A, hoA, h2, hA.subset⟩
    · exact Or.inl ⟨B, hoB, by omega, hB.subset⟩

theorem sup_pair_unique {T T' A : Finset (Fin n)} (hA : A.card = 2) (h1 : A ⊆ T)
    (h2 : A ⊆ T') (hint : T ≠ T' → (T ∩ T').card ≤ 1) : T = T' := by
  by_contra hne
  have h3 := Finset.card_le_card (Finset.subset_inter h1 h2)
  have h4 := hint hne
  omega

theorem sup_four_unique {T T' A : Finset (Fin n)} (hT : T.card = 3) (hT' : T'.card = 3)
    (hA : A.card = 4) (h1 : T ⊆ A) (h2 : T' ⊆ A) (hint : T ≠ T' → (T ∩ T').card ≤ 1) :
    T = T' := by
  by_contra hne
  have h3 := Finset.card_le_card (Finset.union_subset h1 h2)
  have h4 := Finset.card_union_add_card_inter T T'
  have h5 := hint hne
  omega

theorem sup_five_cap {T1 T2 T3 A : Finset (Fin n)} (h1 : T1.card = 3) (h2 : T2.card = 3)
    (h3 : T3.card = 3) (hA : A.card ≤ 5) (s1 : T1 ⊆ A) (s2 : T2 ⊆ A) (s3 : T3 ⊆ A)
    (i12 : (T1 ∩ T2).card ≤ 1) (i13 : (T1 ∩ T3).card ≤ 1) (i23 : (T2 ∩ T3).card ≤ 1) :
    False := by
  have hu := Finset.card_le_card (Finset.union_subset (Finset.union_subset s1 s2) s3)
  have e1 := Finset.card_union_add_card_inter T1 T2
  have e2 := Finset.card_union_add_card_inter (T1 ∪ T2) T3
  have e3 : ((T1 ∪ T2) ∩ T3).card ≤ (T1 ∩ T3).card + (T2 ∩ T3).card := by
    rw [Finset.union_inter_distrib_right]
    exact Finset.card_union_le _ _
  omega

theorem sup_aux_exists (hS : Strict n D) {P : Finset (Fin n)} (hP : P.card ≤ 7)
    (L : Finset (Finset (Fin n))) (h3 : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ T' ∈ L, T ≠ T' → (T ∩ T').card ≤ 1) :
    ∃ Aux : Finset (Finset (Fin n)), L.card ≤ Aux.card ∧ ∀ A ∈ Aux, sup_Occ n D P A ∧
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5) := by
  classical
  refine ⟨P.powerset.filter (fun A => sup_Occ n D P A ∧
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5)), ?_,
    fun A hA => (Finset.mem_filter.mp hA).2⟩
  generalize hAux : P.powerset.filter (fun A => sup_Occ n D P A ∧
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5)) = Aux
  have hmem : ∀ A, sup_Occ n D P A →
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5) → A ∈ Aux := by
    intro A h1 h2
    rw [← hAux]
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (sup_occ_sub h1), h1, h2⟩
  have hprop : ∀ A ∈ Aux, (A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5 := by
    intro A hA
    rw [← hAux] at hA
    exact (Finset.mem_filter.mp hA).2.2
  have hrow : ∀ T ∈ L, 2 ≤ ∑ A ∈ Aux,
      (if A.card = 5 then (if T ⊆ A then 1 else 0) else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) := by
    intro T hT
    rcases sup_triple_parent hS hP (h3 T hT).1 (h3 T hT).2 with
      ⟨A, ho, hc, hs⟩ | ⟨A, ho, hc, hs⟩ | ⟨A, B, hne, hoA, hoB, hcA, hcB, hsA, hsB, -⟩
    · refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (hmem A ho (Or.inl ⟨hc, T, hT, hs⟩)))
      simp [hc, hs]
    · refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (hmem A ho (Or.inr (Or.inl hc))))
      simp [hc, hs]
    · have hsub : ({A, B} : Finset (Finset (Fin n))) ⊆ Aux := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hmem _ hoA (Or.inr (Or.inr hcA))
        · exact hmem _ hoB (Or.inr (Or.inr hcB))
      refine le_trans ?_ (Finset.sum_le_sum_of_subset hsub)
      rw [Finset.sum_pair hne]
      simp [hcA, hcB, hsA, hsB]
  have hcol : ∀ A ∈ Aux, ∑ T ∈ L,
      (if A.card = 5 then (if T ⊆ A then 1 else 0) else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) ≤ 2 := by
    intro A hA
    by_cases h5 : A.card = 5
    · have hsum : ∑ T ∈ L, (if A.card = 5 then (if T ⊆ A then 1 else 0)
          else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) = (L.filter (fun T => T ⊆ A)).card := by
        rw [Finset.card_filter]
        exact Finset.sum_congr rfl (fun T _ => by simp [h5])
      rw [hsum]
      by_contra hgt
      obtain ⟨T1, T2, T3, m1, m2, m3, n12, n13, n23⟩ :=
        Finset.two_lt_card_iff.mp (show 2 < (L.filter (fun T => T ⊆ A)).card by omega)
      rw [Finset.mem_filter] at m1 m2 m3
      exact sup_five_cap (h3 _ m1.1).1 (h3 _ m2.1).1 (h3 _ m3.1).1 h5.le m1.2 m2.2 m3.2
        (hint _ m1.1 _ m2.1 n12) (hint _ m1.1 _ m3.1 n13) (hint _ m2.1 _ m3.1 n23)
    · have hsum : ∑ T ∈ L, (if A.card = 5 then (if T ⊆ A then 1 else 0)
          else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) =
          2 * (L.filter (fun T => A ⊆ T ∨ T ⊆ A)).card := by
        rw [Finset.card_filter, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun T _ => by simp [h5])
      rw [hsum]
      have hle : (L.filter (fun T => A ⊆ T ∨ T ⊆ A)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro T hT T' hT'
        rw [Finset.mem_filter] at hT hT'
        have c3 := (h3 T hT.1).1
        have c3' := (h3 T' hT'.1).1
        rcases hprop A hA with ⟨h2, -⟩ | h4 | h5'
        · have e1 : A ⊆ T := hT.2.resolve_right (fun h => by
            have := Finset.card_le_card h; omega)
          have e2 : A ⊆ T' := hT'.2.resolve_right (fun h => by
            have := Finset.card_le_card h; omega)
          exact sup_pair_unique h2 e1 e2 (hint T hT.1 T' hT'.1)
        · have e1 : T ⊆ A := hT.2.resolve_left (fun h => by
            have := Finset.card_le_card h; omega)
          have e2 : T' ⊆ A := hT'.2.resolve_left (fun h => by
            have := Finset.card_le_card h; omega)
          exact sup_four_unique c3 c3' h4 e1 e2 (hint T hT.1 T' hT'.1)
        · exact absurd h5' h5
      omega
  have h1 := Finset.card_nsmul_le_sum L _ 2 hrow
  have h2 := Finset.sum_le_card_nsmul Aux _ 2 hcol
  rw [Finset.sum_comm] at h1
  simp only [smul_eq_mul] at h1 h2
  omega

theorem sup_charge (hS : Strict n D) {P : Finset (Fin n)} (hP : P.card ≤ 7)
    (L : Finset (Finset (Fin n))) (h3 : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ T' ∈ L, T ≠ T' → (T ∩ T').card ≤ 1)
    (X : Finset (Finset (Fin n)))
    (hX : ∀ M ∈ X, sup_Occ n D P M ∧ 2 ≤ M.card ∧ M ∉ L ∧ M.card ≠ 4 ∧ M.card ≠ 5 ∧
      (M.card = 2 → ∀ T ∈ L, ¬ M ⊆ T)) :
    2 * L.card + X.card ≤ (sup_big n D P).card := by
  classical
  obtain ⟨Aux, hcard, hAux⟩ := sup_aux_exists hS hP L h3 hint
  have hd1 : Disjoint L Aux := by
    rw [Finset.disjoint_left]
    intro T hT hTA
    have := (h3 T hT).1
    rcases (hAux T hTA).2 with ⟨h, -⟩ | h | h <;> omega
  have hd2 : Disjoint (L ∪ Aux) X := by
    rw [Finset.disjoint_left]
    intro M hM hMX
    obtain ⟨-, -, hnL, hn4, hn5, hno⟩ := hX M hMX
    rcases Finset.mem_union.mp hM with h | h
    · exact hnL h
    · rcases (hAux M h).2 with ⟨h2, T, hT, hs⟩ | h4 | h5
      · exact hno h2 T hT hs
      · exact hn4 h4
      · exact hn5 h5
  have hle := sup_card_le_big hS P ((L ∪ Aux) ∪ X) (by
    intro M hM
    rcases Finset.mem_union.mp hM with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact ⟨by have := (h3 M h).1; omega, (h3 M h).2⟩
      · refine ⟨?_, (hAux M h).1⟩
        rcases (hAux M h).2 with ⟨h, -⟩ | h | h <;> omega
    · exact ⟨(hX M h).2.1, (hX M h).1⟩)
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1] at hle
  omega

theorem sup_wit_exists {G : Fin n → Fin n → Prop} (hG : sem_Gr G) (hS : Strict n D)
    (hC : sem_Comp n G D) {P U X : Finset (Fin n)} (hUP : U ⊆ P)
    (hU : U.card ≤ 2 ∨ (U.card = 3 ∧ ¬ sup_Occ n D P U))
    (hX : ∀ a ∈ X, ∀ b ∈ X, ¬ G a b) (hPX : P \ U ⊆ X) {f : Fin n} (hf : f ∈ U)
    (hnb : ∃ a ∈ X, G f a) : ∃ e, sup_Wit n D P U f e := by
  obtain ⟨j, s, hj, ht, h1, h2, hd⟩ := sem_exposure hG hS hC X hX f hnb
  have hsub : supp n D (src D (j, s)) ∩ P ⊆ U := by
    intro v hv
    rw [Finset.mem_inter] at hv
    by_contra hvU
    exact Finset.disjoint_left.mp hd hv.1 (hPX (Finset.mem_sdiff.mpr ⟨hv.2, hvU⟩))
  refine ⟨(j, s), hj, ht, hUP hf, h1, h2, hsub, ?_⟩
  rcases hU with hU | ⟨hU3, hmiss⟩
  · exact (Finset.card_le_card hsub).trans hU
  · have hne : supp n D (src D (j, s)) ∩ P ≠ U := fun h => hmiss ⟨_, h⟩
    have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    omega

theorem sup_wit_out (hS : Strict n D) {P U : Finset (Fin n)} {f : Fin n} {e : ℕ × Bool}
    (h : sup_Wit n D P U f e) :
    supp n D (n + e.1) ∩ P ⊆ (supp n D (src D e) ∩ P).erase f := by
  obtain ⟨hj, ht, -, -, h2, -, -⟩ := h
  intro v hv
  rw [Finset.mem_inter] at hv
  rw [Finset.mem_erase, Finset.mem_inter]
  exact ⟨fun hvf => h2 (hvf ▸ hv.1), sem_supp_and_sub hS hj ht e.2 hv.1, hv.2⟩

theorem sup_wit_single {P U : Finset (Fin n)} {f : Fin n} {e : ℕ × Bool}
    (h : sup_Wit n D P U f e)
    (hno : ∀ M, M ⊆ U → M.card = 2 → f ∈ M → ¬ sup_Occ n D P M) :
    supp n D (src D e) ∩ P = {f} := by
  obtain ⟨-, -, hfP, h1, -, hsub, hc⟩ := h
  have hfm : f ∈ supp n D (src D e) ∩ P := Finset.mem_inter.mpr ⟨h1, hfP⟩
  have hc2 : (supp n D (src D e) ∩ P).card ≠ 2 :=
    fun h2 => hno _ hsub h2 hfm (sup_occ_wire P _)
  exact (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hfm)
    (by rw [Finset.card_singleton]; omega)).symm

theorem sup_cost_inl {P : Finset (Fin n)} {e e0 : ℕ × Bool}
    (h : sup_cost n D P e = Sum.inl e0) : e = e0 ∧ supp n D (n + e.1) ∩ P = ∅ := by
  unfold sup_cost at h
  split_ifs at h with h0
  exact ⟨Sum.inl.inj h, h0⟩

theorem sup_cost_inr {P : Finset (Fin n)} {e : ℕ × Bool} {j : ℕ}
    (h : sup_cost n D P e = Sum.inr j) : e.1 = j ∧ (supp n D (n + e.1) ∩ P).Nonempty := by
  unfold sup_cost at h
  split_ifs at h with h0
  exact ⟨Sum.inr.inj h, Finset.nonempty_iff_ne_empty.mpr h0⟩

theorem sup_cost_ok (hS : Strict n D) {P U : Finset (Fin n)} {f : Fin n} {e : ℕ × Bool}
    (h : sup_Wit n D P U f e) : sup_CostOK n D P (sup_cost n D P e) := by
  have hout := sup_wit_out hS h
  obtain ⟨hj, ht, hfP, h1, -, -, hc⟩ := h
  have hfm : f ∈ supp n D (src D e) ∩ P := Finset.mem_inter.mpr ⟨h1, hfP⟩
  unfold sup_cost
  split_ifs with h0
  · show e ∈ exitArcs n D (carrierT n D P) ∧ (supp n D (src D e) ∩ P).card ≤ 2
    refine ⟨?_, hc⟩
    rw [exitArcs, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, Finset.mem_univ _⟩,
      sup_mem_carrier.mpr ⟨f, hfm⟩, ?_⟩
    rw [sup_mem_carrier, h0]
    exact Finset.not_nonempty_empty
  · show e.1 ∈ merges n D (carrierT n D P) ∧ (supp n D (n + e.1) ∩ P).card = 1
    have hne : (supp n D (n + e.1) ∩ P).Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
    have hle := Finset.card_le_card hout
    rw [Finset.card_erase_of_mem hfm] at hle
    have hpos := Finset.card_pos.mpr hne
    refine ⟨?_, by omega⟩
    obtain ⟨v, hv⟩ := hne
    rw [Finset.mem_inter] at hv
    have hA := sem_supp_and_sub hS hj ht false hv.1
    have hB := sem_supp_and_sub hS hj ht true hv.1
    rw [sb_src_false] at hA
    rw [sb_src_true] at hB
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, sup_mem_carrier.mpr ⟨v, Finset.mem_inter.mpr hv⟩,
      sup_mem_carrier.mpr ⟨v, Finset.mem_inter.mpr ⟨hA, hv.2⟩⟩,
      sup_mem_carrier.mpr ⟨v, Finset.mem_inter.mpr ⟨hB, hv.2⟩⟩⟩

theorem sup_wit_same_pos (hS : Strict n D) {P U U' : Finset (Fin n)} {f f' : Fin n}
    {e : ℕ × Bool} (h : sup_Wit n D P U f e) (h' : sup_Wit n D P U' f' e)
    (hne : (supp n D (n + e.1) ∩ P).Nonempty) : f = f' := by
  by_contra hff
  obtain ⟨q, hq⟩ := hne
  have h1 := sup_wit_out hS h hq
  have h2 := sup_wit_out hS h' hq
  rw [Finset.mem_erase] at h1 h2
  have hsub : ({q, f, f'} : Finset (Fin n)) ⊆ supp n D (src D e) ∩ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx <;> rw [hx]
    · exact h1.2
    · exact Finset.mem_inter.mpr ⟨h.2.2.2.1, h.2.2.1⟩
    · exact Finset.mem_inter.mpr ⟨h'.2.2.2.1, h'.2.2.1⟩
  have hc := Finset.card_le_card hsub
  have h3 : ({q, f, f'} : Finset (Fin n)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hff]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1.1, h2.1⟩
  have := h.2.2.2.2.2.2
  omega

theorem sup_cost_ne_of_single (hS : Strict n D) {P U U' : Finset (Fin n)} {f f' : Fin n}
    {e e' : ℕ × Bool} (h : sup_Wit n D P U f e) (h' : sup_Wit n D P U' f' e')
    (hs : supp n D (src D e) ∩ P = {f}) (hff : f ≠ f') :
    sup_cost n D P e ≠ sup_cost n D P e' := by
  intro heq
  have h0 : supp n D (n + e.1) ∩ P = ∅ := by
    have hout := sup_wit_out hS h
    rw [hs, Finset.erase_singleton] at hout
    exact Finset.subset_empty.mp hout
  have hc : sup_cost n D P e = Sum.inl e := by simp [sup_cost, h0]
  rw [hc] at heq
  have he := (sup_cost_inl heq.symm).1
  subst he
  have hm : f' ∈ supp n D (src D e') ∩ P := Finset.mem_inter.mpr ⟨h'.2.2.2.1, h'.2.2.1⟩
  rw [hs, Finset.mem_singleton] at hm
  exact hff hm.symm

theorem sup_fibre_le (hS : Strict n D) {P : Finset (Fin n)} (Lab : Finset (Fin n))
    (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) (c : (ℕ × Bool) ⊕ ℕ) :
    (Lab.filter (fun f => sup_cost n D P (wit f) = c)).card ≤ 2 := by
  rcases c with e0 | j0
  · by_cases hne : (Lab.filter (fun f => sup_cost n D P (wit f) = Sum.inl e0)).Nonempty
    · obtain ⟨f0, hf0⟩ := hne
      rw [Finset.mem_filter] at hf0
      have hcard := (hwit f0 hf0.1).2.2.2.2.2.2
      rw [(sup_cost_inl hf0.2).1] at hcard
      refine le_trans (Finset.card_le_card ?_) hcard
      intro f hf
      rw [Finset.mem_filter] at hf
      have hw := hwit f hf.1
      rw [(sup_cost_inl hf.2).1] at hw
      exact Finset.mem_inter.mpr ⟨hw.2.2.2.1, hw.2.2.1⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  · have hinj : Set.InjOn (fun f => (wit f).2)
        (Lab.filter (fun f => sup_cost n D P (wit f) = Sum.inr j0) : Set (Fin n)) := by
      intro f hf f' hf' hs
      rw [Finset.mem_coe, Finset.mem_filter] at hf hf'
      obtain ⟨h1, hn1⟩ := sup_cost_inr hf.2
      obtain ⟨h1', -⟩ := sup_cost_inr hf'.2
      have hee : wit f = wit f' := Prod.ext (h1.trans h1'.symm) hs
      have hw' := hwit f' hf'.1
      rw [← hee] at hw'
      exact sup_wit_same_pos hS (hwit f hf.1) hw' hn1
    have hle := Finset.card_le_card_of_injOn (t := (Finset.univ : Finset Bool))
      (fun f => (wit f).2) (fun _ _ => Finset.mem_univ _) hinj
    simpa using hle

theorem sup_wit_card (hS : Strict n D) {P : Finset (Fin n)} (Lab : Finset (Fin n))
    (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) :
    Lab.card ≤ 2 * (Lab.image (fun f => sup_cost n D P (wit f))).card :=
  Finset.card_le_mul_card_image Lab 2 (fun c _ => sup_fibre_le hS Lab U wit hwit c)

theorem sup_wit_card_single (hS : Strict n D) {P : Finset (Fin n)} (Lab S : Finset (Fin n))
    (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) (hSL : S ⊆ Lab)
    (hsing : ∀ f ∈ S, supp n D (src D (wit f)) ∩ P = {f}) :
    2 * S.card + (Lab \ S).card ≤
      2 * (Lab.image (fun f => sup_cost n D P (wit f))).card := by
  have h1 : (S.image (fun f => sup_cost n D P (wit f))).card = S.card :=
    Finset.card_image_of_injOn (fun f hf f' hf' heq => by
      by_contra hne
      exact sup_cost_ne_of_single hS (hwit f (hSL hf)) (hwit f' (hSL hf')) (hsing f hf) hne heq)
  have h2 := sup_wit_card hS (Lab \ S) U wit (fun f hf => hwit f (Finset.mem_sdiff.mp hf).1)
  have hd : Disjoint (S.image (fun f => sup_cost n D P (wit f)))
      ((Lab \ S).image (fun f => sup_cost n D P (wit f))) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hc1
    obtain ⟨f', hf', heq⟩ := Finset.mem_image.mp hc2
    rw [Finset.mem_sdiff] at hf'
    exact sup_cost_ne_of_single hS (hwit f (hSL hf)) (hwit f' hf'.1) (hsing f hf)
      (fun h => hf'.2 (h ▸ hf)) heq.symm
  have h3 : (S.image (fun f => sup_cost n D P (wit f)) ∪
      (Lab \ S).image (fun f => sup_cost n D P (wit f))).card ≤
      (Lab.image (fun f => sup_cost n D P (wit f))).card :=
    Finset.card_le_card (Finset.union_subset (Finset.image_subset_image hSL)
      (Finset.image_subset_image Finset.sdiff_subset))
  rw [Finset.card_union_of_disjoint hd, h1] at h3
  omega

theorem sup_master (P : Finset (Fin n)) (E : Finset (ℕ × Bool))
    (hE : ∀ e ∈ E, e ∈ exitArcs n D (carrierT n D P) ∧ 3 ≤ (supp n D (src D e) ∩ P).card)
    (C : Finset ((ℕ × Bool) ⊕ ℕ)) (hC : ∀ c ∈ C, sup_CostOK n D P c) :
    (sup_big n D P).card + E.card + C.card ≤
      (exitArcs n D (carrierT n D P)).card + (merges n D (carrierT n D P)).card := by
  have hl : ∀ e ∈ C.toLeft, e ∈ exitArcs n D (carrierT n D P) ∧
      (supp n D (src D e) ∩ P).card ≤ 2 := fun e he => hC _ (Finset.mem_toLeft.mp he)
  have hr : ∀ j ∈ C.toRight, j ∈ merges n D (carrierT n D P) ∧
      (supp n D (n + j) ∩ P).card = 1 := fun j hj => hC _ (Finset.mem_toRight.mp hj)
  have h1 : E.card + C.toLeft.card ≤ (exitArcs n D (carrierT n D P)).card := by
    rw [← Finset.card_union_of_disjoint]
    · refine Finset.card_le_card (fun e he => ?_)
      rcases Finset.mem_union.mp he with h | h
      · exact (hE e h).1
      · exact (hl e h).1
    · rw [Finset.disjoint_left]
      intro e h1 h2
      have a := (hE e h1).2
      have b := (hl e h2).2
      omega
  have h2 : (sup_big n D P).card + C.toRight.card ≤ (merges n D (carrierT n D P)).card := by
    rw [← Finset.card_union_of_disjoint]
    · refine Finset.card_le_card (fun j hj => ?_)
      rcases Finset.mem_union.mp hj with h | h
      · exact (Finset.mem_filter.mp h).1
      · exact (hr j h).1
    · rw [Finset.disjoint_left]
      intro j h1 h2
      have a := (Finset.mem_filter.mp h1).2
      have b := (hr j h2).2
      omega
  have h3 := Finset.card_toLeft_add_card_toRight (u := C)
  omega

theorem sup_count (hS : Strict n D) (P : Finset (Fin n)) (E : Finset (ℕ × Bool))
    (hE : ∀ e ∈ E, e ∈ exitArcs n D (carrierT n D P) ∧ 3 ≤ (supp n D (src D e) ∩ P).card)
    (Lab S : Finset (Fin n)) (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) (hSL : S ⊆ Lab)
    (hsing : ∀ f ∈ S, supp n D (src D (wit f)) ∩ P = {f}) :
    2 * ((sup_big n D P).card + E.card) + 2 * S.card + (Lab \ S).card ≤
      2 * ((exitArcs n D (carrierT n D P)).card + (merges n D (carrierT n D P)).card) := by
  have h1 := sup_wit_card_single hS Lab S U wit hwit hSL hsing
  have h2 := sup_master P E hE (Lab.image (fun f => sup_cost n D P (wit f))) (by
    intro c hc
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hc
    exact sup_cost_ok hS (hwit f hf))
  omega

theorem sup_assigned_exits {G : Fin n → Fin n → Prop} (hG : sem_Gr G) (h : StrictLive n D)
    (hC : sem_Comp n G D) (P I : Finset (Fin n))
    (hI : ∀ i ∈ I, i ∈ ineligSet n D ∧
      ∃ N : Finset (Fin n), N ⊆ P ∧ 3 ≤ N.card ∧ ∀ a ∈ N, G i a) :
    ∃ E : Finset (ℕ × Bool), E.card = I.card ∧ ∀ e ∈ E,
      e ∈ exitArcs n D (carrierT n D P) ∧ 3 ≤ (supp n D (src D e) ∩ P).card := by
  classical
  have hex : ∀ i : Fin n, ∃ e : ℕ × Bool, i ∈ I → e.1 < D.length ∧
      supp n D (src D e) = {i} ∧ supp n D (n + e.1) = ∅ ∧
      ∀ a, G i a → a ∈ supp n D (src D (e.1, !e.2)) := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨e, h1, -, h3, h4, h5, -, -⟩ := sem_inelig_consumer hG h hC (hI i hi).1
      exact ⟨e, fun _ => ⟨h1, h3, h4, h5⟩⟩
    · exact ⟨(0, false), fun hc => absurd hc hi⟩
  choose g hg using hex
  refine ⟨I.image (fun i => ((g i).1, !(g i).2)), ?_, ?_⟩
  · refine Finset.card_image_of_injOn (fun i hi i' hi' heq => ?_)
    rw [Prod.mk.injEq, Bool.not_inj_iff] at heq
    have he : g i = g i' := Prod.ext heq.1 heq.2
    have h1 := (hg i hi).2.1
    rw [he, (hg i' hi').2.1] at h1
    exact (Finset.singleton_injective h1).symm
  · intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hj, -, hout, hnb⟩ := hg i hi
    obtain ⟨N, hNP, hN3, hNG⟩ := (hI i hi).2
    have hsub : N ⊆ supp n D (src D ((g i).1, !(g i).2)) ∩ P :=
      fun a ha => Finset.mem_inter.mpr ⟨hnb a (hNG a ha), hNP ha⟩
    have hc := Finset.card_le_card hsub
    refine ⟨?_, by omega⟩
    rw [exitArcs, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, Finset.mem_univ _⟩,
      sup_mem_carrier.mpr (Finset.card_pos.mp (by omega)), ?_⟩
    rw [sup_mem_carrier, hout, Finset.empty_inter]
    exact Finset.not_nonempty_empty

end SupMask

section K4Generic

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem k4_mem_carrier {T : Finset (Fin n)} {w : ℕ} :
    w ∈ carrierT n D T ↔ (supp n D w ∩ T).Nonempty := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  rintro ⟨v, hv⟩
  exact sem_supp_lt (Finset.mem_inter.mp hv).1

theorem k4_mem_exit {T : Finset (Fin n)} {e : ℕ × Bool} : e ∈ exitArcs n D (carrierT n D T) ↔
    e.1 < D.length ∧ (supp n D (src D e) ∩ T).Nonempty ∧
      ¬ (supp n D (n + e.1) ∩ T).Nonempty := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, k4_mem_carrier]

def k4_Pos (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) (pos : Fin n → ℕ × Bool) : Prop :=
  (∀ i ∈ ineligSet n D, (pos i).1 < D.length ∧ supp n D (n + (pos i).1) = ∅ ∧
    (∀ a, G i a → a ∈ supp n D (src D (pos i))) ∧
    supp n D (src D ((pos i).1, !(pos i).2)) = {i}) ∧
  ∀ i ∈ ineligSet n D, ∀ i' ∈ ineligSet n D, pos i = pos i' → i = i'

theorem k4_assigned (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) :
    ∃ pos : Fin n → ℕ × Bool, k4_Pos n G D pos := by
  classical
  have hex : ∀ i : Fin n, ∃ e : ℕ × Bool, i ∈ ineligSet n D → (e.1 < D.length ∧
      supp n D (n + e.1) = ∅ ∧ (∀ a, G i a → a ∈ supp n D (src D e)) ∧
      supp n D (src D (e.1, !e.2)) = {i}) := by
    intro i
    by_cases hi : i ∈ ineligSet n D
    · obtain ⟨e, h1, -, h3, h4, h5, -, -⟩ := sem_inelig_consumer hG h hC hi
      exact ⟨(e.1, !e.2), fun _ => ⟨h1, h4, h5, by simpa using h3⟩⟩
    · exact ⟨(0, false), fun hc => absurd hc hi⟩
  choose pos hpos using hex
  refine ⟨pos, hpos, fun i hi i' hi' he => ?_⟩
  have h1 := (hpos i hi).2.2.2
  rw [he, (hpos i' hi').2.2.2] at h1
  exact (Finset.singleton_injective h1).symm

theorem k4_pos_exit {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) {i a : Fin n}
    {T : Finset (Fin n)} (hi : i ∈ ineligSet n D) (hia : G i a) (haT : a ∈ T) :
    pos i ∈ exitArcs n D (carrierT n D T) := by
  obtain ⟨h1, h2, h3, -⟩ := hpos.1 i hi
  rw [k4_mem_exit]
  refine ⟨h1, ⟨a, Finset.mem_inter.mpr ⟨h3 a hia, haT⟩⟩, ?_⟩
  rw [h2, Finset.empty_inter]
  exact Finset.not_nonempty_empty

theorem k4_exits_ge {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) (T J : Finset (Fin n))
    (hJ : ∀ i ∈ J, i ∈ ineligSet n D ∧ ∃ a ∈ T, G i a) :
    J.image pos ⊆ exitArcs n D (carrierT n D T) ∧ (J.image pos).card = J.card := by
  constructor
  · intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hi1, a, haT, hia⟩ := hJ i hi
    exact k4_pos_exit hpos hi1 hia haT
  · exact Finset.card_image_of_injOn
      (fun i hi i' hi' he => hpos.2 i (hJ i hi).1 i' (hJ i' hi').1 he)

theorem k4_budget (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (b : Fin n → ℕ)
    (hb : PureBranch n D b) (T : Finset (Fin n)) :
    (exitArcs n D (carrierT n D T)).card + (merges n D (carrierT n D T)).card +
      (eligSet n D).card ≤ 2 * T.card + Bplus n D := by
  have h1 := carrier_flow_union h T (by rw [sem_supp_out hG hC, Finset.empty_inter])
  have h2 := surplus_carrierT_le h.1 b hb T
  have h3 := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet n D ⊆ T)
  omega

theorem k4_mask_gate (hS : Strict n D) (T : Finset (Fin n)) (w : ℕ)
    (h2 : 2 ≤ (supp n D w ∩ T).card) :
    ∃ j ∈ merges n D (carrierT n D T), supp n D (n + j) ∩ T = supp n D w ∩ T := by
  obtain ⟨j, -, -, h3, h4, -, -⟩ := sem_first_mask hS T _ h2 w rfl
  exact ⟨j, h4, h3⟩

theorem k4_pair_merges (hS : Strict n D) {T : Finset (Fin n)} (hT : T.card = 3)
    {a b c : Fin n} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) {w1 w2 : ℕ} (h1a : a ∈ supp n D w1) (h1b : b ∈ supp n D w1)
    (h2a : a ∈ supp n D w2) (h2c : c ∈ supp n D w2) :
    2 ≤ (merges n D (carrierT n D T)).card := by
  have m1a : a ∈ supp n D w1 ∩ T := Finset.mem_inter.mpr ⟨h1a, ha⟩
  have m1b : b ∈ supp n D w1 ∩ T := Finset.mem_inter.mpr ⟨h1b, hb⟩
  have m2a : a ∈ supp n D w2 ∩ T := Finset.mem_inter.mpr ⟨h2a, ha⟩
  have m2c : c ∈ supp n D w2 ∩ T := Finset.mem_inter.mpr ⟨h2c, hc⟩
  have c1 : 2 ≤ (supp n D w1 ∩ T).card := Finset.one_lt_card.mpr ⟨a, m1a, b, m1b, hab⟩
  have c2 : 2 ≤ (supp n D w2 ∩ T).card := Finset.one_lt_card.mpr ⟨a, m2a, c, m2c, hac⟩
  obtain ⟨j1, hj1, e1⟩ := k4_mask_gate hS T w1 c1
  by_cases heq : supp n D w1 ∩ T = supp n D w2 ∩ T
  · have hfull : supp n D w1 ∩ T = T := by
      refine Finset.eq_of_subset_of_card_le Finset.inter_subset_right ?_
      rw [hT]
      exact Finset.two_lt_card.mpr
        ⟨a, m1a, b, m1b, c, by rw [heq]; exact m2c, hab, hac, hbc⟩
    obtain ⟨j, -, -, h3, h4, -, hcase⟩ := sem_first_mask hS T T (by omega) w1 hfull
    rcases hcase with ⟨-, hA, -⟩ | ⟨-, hA, hB, hU, -, -⟩
    · exact absurd rfl (Finset.ssubset_of_ssubset_of_subset hA Finset.inter_subset_right).ne
    · have hcard : 3 ≤ (supp n D (opA D j) ∩ T).card + (supp n D (opB D j) ∩ T).card := by
        have := Finset.card_union_le (supp n D (opA D j) ∩ T) (supp n D (opB D j) ∩ T)
        rw [hU, hT] at this
        exact this
      have key : ∀ w, supp n D w ∩ T ⊂ T → 2 ≤ (supp n D w ∩ T).card →
          2 ≤ (merges n D (carrierT n D T)).card := by
        intro w hss hc2
        obtain ⟨j', hj', e'⟩ := k4_mask_gate hS T w hc2
        refine Finset.one_lt_card.mpr ⟨j, h4, j', hj', fun hjj => ?_⟩
        rw [hjj, e'] at h3
        exact hss.ne h3
      by_cases hc2 : 2 ≤ (supp n D (opA D j) ∩ T).card
      · exact key _ hA hc2
      · exact key _ hB (by omega)
  · obtain ⟨j2, hj2, e2⟩ := k4_mask_gate hS T w2 c2
    exact Finset.one_lt_card.mpr ⟨j1, hj1, j2, hj2, fun hjj => heq (by rw [← e1, ← e2, hjj])⟩

end K4Generic

section L3Gen

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem cnt_main (hS : Strict n D) {P : Finset (Fin n)} (hP : P.card ≤ 7)
    (L : Finset (Finset (Fin n))) (h3 : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ T' ∈ L, T ≠ T' → (T ∩ T').card ≤ 1) (E : Finset (ℕ × Bool))
    (hE : ∀ e ∈ E, e ∈ exitArcs n D (carrierT n D P) ∧ 3 ≤ (supp n D (src D e) ∩ P).card)
    (Lab : Finset (Fin n)) (U : Fin n → Finset (Fin n))
    (hw : ∀ f ∈ Lab, ∃ e, sup_Wit n D P (U f) f e)
    (hUL : ∀ f ∈ Lab, ∀ T ∈ L, (U f ∩ T).card ≤ 1) :
    2 * L.card + E.card + Lab.card ≤
      (exitArcs n D (carrierT n D P)).card + (merges n D (carrierT n D P)).card := by
  classical
  choose! wit hwit using hw
  let S := Lab.filter (fun f => ∀ M, M ⊆ U f → M.card = 2 → f ∈ M → ¬ sup_Occ n D P M)
  have hSL : S ⊆ Lab := Finset.filter_subset _ _
  have hno : ∀ f ∈ Lab \ S, ∃ M, M ⊆ U f ∧ M.card = 2 ∧ f ∈ M ∧ sup_Occ n D P M := by
    intro f hf
    rw [Finset.mem_sdiff, Finset.mem_filter] at hf
    by_contra hc
    exact hf.2 ⟨hf.1, fun M h1 h2 h4 h5 => hc ⟨M, h1, h2, h4, h5⟩⟩
  choose! pr hpr using hno
  have hX := sup_charge hS hP L h3 hint ((Lab \ S).image pr) (by
    intro M hM
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hM
    obtain ⟨h1, h2, -, h4⟩ := hpr f hf
    refine ⟨h4, by omega, fun hL => by have := (h3 _ hL).1; omega, by omega, by omega,
      fun _ T hT hsub => ?_⟩
    have := Finset.card_le_card (Finset.subset_inter h1 hsub)
    have := hUL f (Finset.mem_sdiff.1 hf).1 T hT
    omega)
  have hcnt := sup_count hS P E hE Lab S U wit hwit hSL (fun f hf =>
    sup_wit_single (hwit f (hSL hf)) (Finset.mem_filter.1 hf).2)
  have hfib : (Lab \ S).card ≤ 2 * ((Lab \ S).image pr).card := by
    refine Finset.card_le_mul_card_image _ 2 (fun M _ => ?_)
    by_cases hne : ((Lab \ S).filter (fun f => pr f = M)).Nonempty
    · obtain ⟨g, hg⟩ := hne
      rw [Finset.mem_filter] at hg
      have hM2 : M.card = 2 := hg.2 ▸ (hpr g hg.1).2.1
      rw [← hM2]
      refine Finset.card_le_card (fun f hf => ?_)
      rw [Finset.mem_filter] at hf
      exact hf.2 ▸ (hpr f hf.1).2.2.1
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp
  have := Finset.card_sdiff_add_card_eq_card hSL
  omega

theorem tri_exits (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) (T J : Finset (Fin n))
    (A : Fin n → Finset (Fin n))
    (hJ : ∀ i ∈ J, i ∈ ineligSet n D ∧ (∃ a ∈ T, G i a) ∧ ∀ f ∈ T, ∃ a ∈ A f, G i a)
    (hA : ∀ f ∈ T, (∀ a ∈ A f, ∀ b ∈ A f, ¬ G a b) ∧ T.erase f ⊆ A f ∧ ∃ a ∈ A f, G f a) :
    J.card + T.card ≤ (exitArcs n D (carrierT n D T)).card := by
  classical
  obtain ⟨hsub, hcard⟩ := k4_exits_ge hpos T J (fun i hi => ⟨(hJ i hi).1, (hJ i hi).2.1⟩)
  have hex : ∀ f ∈ T, ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
      f ∈ supp n D (src D e) ∧ f ∉ supp n D (n + e.1) ∧ Disjoint (supp n D (src D e)) (A f) := by
    intro f hf
    obtain ⟨j, s, h1, h2, h4, h5, h6⟩ := sem_exposure hG hS hC (A f) (hA f hf).1 f (hA f hf).2.2
    exact ⟨(j, s), h1, h2, h4, h5, h6⟩
  choose! w hw using hex
  have hinj : Set.InjOn w T := by
    intro f hf g hg hfg
    by_contra hne
    exact Finset.disjoint_left.1 (hw f hf).2.2.2.2 (hfg ▸ (hw g hg).2.2.1)
      ((hA f hf).2.1 (Finset.mem_erase.2 ⟨fun h => hne h.symm, hg⟩))
  have hdis : Disjoint (J.image pos) (T.image w) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he1
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.1 he2
    obtain ⟨a, ha, hia⟩ := (hJ i hi).2.2 f hf
    exact Finset.disjoint_left.1 (hw f hf).2.2.2.2
      (hfe ▸ (hpos.1 i (hJ i hi).1).2.2.1 a hia) ha
  have hsub2 : T.image w ⊆ exitArcs n D (carrierT n D T) := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨h1, h2, h4, h5, h6⟩ := hw f hf
    refine k4_mem_exit.2 ⟨h1, ⟨f, Finset.mem_inter.2 ⟨h4, hf⟩⟩, ?_⟩
    rintro ⟨g, hg⟩
    rw [Finset.mem_inter] at hg
    have hgs : g ∈ supp n D (src D (w f)) := sem_supp_and_sub hS h1 h2 (w f).2 hg.1
    exact Finset.disjoint_left.1 h6 hgs
      ((hA f hf).2.1 (Finset.mem_erase.2 ⟨fun h => h5 (h ▸ hg.1), hg.2⟩))
  have := Finset.card_le_card (Finset.union_subset hsub hsub2)
  rw [Finset.card_union_of_disjoint hdis, hcard, Finset.card_image_of_injOn hinj] at this
  exact this

end L3Gen

section L3bGen

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem ri_gen (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (b : Fin n → ℕ)
    (hb : PureBranch n D b) {x c : Fin n} (hxc : x ≠ c) (hx : x ∈ eligSet n D)
    (hres : ∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → c ∈ supp n D u.1) {w : ℕ}
    (hw : x ∈ supp n D w ∧ c ∈ supp n D w) :
    ∃ e0, ∀ e ∈ sem_W n D x, e ≠ e0 → c ∈ supp n D (src D e) := by
  classical
  obtain ⟨z, hxz, hcz⟩ := hG.2.2.1 x c hxc
  obtain ⟨-, -, h2, e1, he1, ht1, -⟩ := sem_diff_two_exits hG h hC b hb hxc hx hres hw hxz hcz
  have hc1 : ((exitArcs n D (carrierDiff n D x c)).erase e1).card = 1 := by
    rw [Finset.card_erase_of_mem he1, h2]
  obtain ⟨e0, he0⟩ := Finset.card_eq_one.1 hc1
  refine ⟨e0, fun e he hne => ?_⟩
  by_contra hce
  obtain ⟨h1, h4, h5⟩ := sem_mem_W.1 he
  have hm : e ∈ (exitArcs n D (carrierDiff n D x c)).erase e1 :=
    Finset.mem_erase.2 ⟨fun heq => by
      have := sem_W_and h.1 he
      rw [heq, ht1] at this
      exact Bool.false_ne_true this, sem_mem_exit_diff.2 ⟨h1, ⟨h4, hce⟩, fun hc => h5 hc.1⟩⟩
  rw [he0, Finset.mem_singleton] at hm
  exact hne hm

end L3bGen

end DagTools

open DagTools

abbrev V := Fin 10

def neighbors (v : V) : Nat :=
  [50, 69, 138, 276, 521, 385, 770, 548, 104, 208].getD v.val 0

abbrev adj (u v : V) : Prop := (neighbors u).testBit v.val = true

def T : Finset V := {4, 5, 6}

def I : Finset V := {0, 8, 9}

def nb (v : V) : Finset V := T.filter (adj v)

def exposure (v : V) : Finset V :=
  if v = 4 then {3, 5, 6} else if v = 5 then {4, 6, 7} else {1, 4, 5}

lemma graph_ok : sem_Gr adj := by
  unfold sem_Gr
  decide +kernel

lemma T_card : T.card = 3 := by decide +kernel

lemma I_card : I.card = 3 := by decide +kernel

lemma T_independent : ∀ u ∈ T, ∀ v ∈ T, ¬ adj u v := by decide +kernel

lemma exposure_ok : ∀ f ∈ T,
    (∀ a ∈ exposure f, ∀ b ∈ exposure f, ¬ adj a b) ∧
      T.erase f ⊆ exposure f ∧ ∃ a ∈ exposure f, adj f a := by decide +kernel

lemma incidence_ok : ∀ i ∈ I,
    (∃ a ∈ T, adj i a) ∧ ∀ f ∈ T, ∃ a ∈ exposure f, adj i a := by decide +kernel

lemma nb_card : ∀ i ∈ I, (nb i).card = 2 := by decide +kernel

lemma nb_nonsub : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ¬ nb i ⊆ nb j := by decide +kernel

lemma directional_difference : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
    ∃ a ∈ T, adj j a ∧ ¬ adj i a := by decide +kernel

lemma third_vertex : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
    ∃ k ∈ I, k ≠ i ∧ k ≠ j := by decide +kernel

lemma exact_mask_of_witness {D : Dag} {i : V}
    (hw : ∃ k s, k < D.length ∧ tag D k = true ∧
      sem_Chain 10 D i.val (src D (k, !s)) ∧
      ∀ a ∈ T, (a ∈ supp 10 D (src D (k, s)) ↔ adj i a)) :
    sup_Occ 10 D T (nb i) := by
  obtain ⟨k, s, _, _, _, hs⟩ := hw
  refine ⟨src D (k, s), ?_⟩
  ext a
  simp only [nb, Finset.mem_inter, Finset.mem_filter]
  constructor
  · rintro ⟨ha, hat⟩
    exact ⟨hat, (hs a hat).mp ha⟩
  · rintro ⟨hat, ha⟩
    exact ⟨(hs a hat).mpr ha, hat⟩

lemma exact_mask_pair {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D ≤ 1) (hi : I ⊆ ineligSet 10 D)
    {i j : V} (hiI : i ∈ I) (hjI : j ∈ I) (hne : i ≠ j) :
    sup_Occ 10 D T (nb i) ∨ sup_Occ 10 D T (nb j) := by
  rcases sem_shared_empty graph_ok h hc hz T T_independent (hi hiI) (hi hjI)
    (directional_difference i hiI j hjI hne) with hw | hw
  · exact Or.inl (exact_mask_of_witness hw)
  · exact Or.inr (exact_mask_of_witness hw)

lemma two_exact_masks {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D ≤ 1) (hi : I ⊆ ineligSet 10 D) :
    ∃ i ∈ I, ∃ j ∈ I, i ≠ j ∧ sup_Occ 10 D T (nb i) ∧ sup_Occ 10 D T (nb j) := by
  have h08 := exact_mask_pair h hc hz hi (i := 0) (j := 8) (by decide) (by decide) (by decide)
  have h09 := exact_mask_pair h hc hz hi (i := 0) (j := 9) (by decide) (by decide) (by decide)
  have h89 := exact_mask_pair h hc hz hi (i := 8) (j := 9) (by decide) (by decide) (by decide)
  by_cases h0 : sup_Occ 10 D T (nb 0)
  · rcases h89 with h8 | h9
    · exact ⟨0, by decide, 8, by decide, by decide, h0, h8⟩
    · exact ⟨0, by decide, 9, by decide, by decide, h0, h9⟩
  · exact ⟨8, by decide, 9, by decide, by decide, h08.resolve_left h0, h09.resolve_left h0⟩

lemma three_merges {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D ≤ 1) (hi : I ⊆ ineligSet 10 D) :
    3 ≤ (merges 10 D (carrierT 10 D T)).card := by
  classical
  obtain ⟨i, hiI, j, hjI, hij, hiocc, hjocc⟩ := two_exact_masks h hc hz hi
  obtain ⟨k, hkI, hki, hkj⟩ := third_vertex i hiI j hjI hij
  obtain ⟨e, _, _, _, _, hneigh, _, _⟩ := sem_inelig_consumer graph_ok h hc (hi hkI)
  let M := supp 10 D (src D (e.1, !e.2)) ∩ T
  have hMocc : sup_Occ 10 D T M := ⟨src D (e.1, !e.2), rfl⟩
  have hkM : nb k ⊆ M := by
    intro a ha
    obtain ⟨hat, hka⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_inter.mpr ⟨hneigh a hka, hat⟩
  have hMcard : 2 ≤ M.card := by
    have := Finset.card_le_card hkM
    rw [nb_card k hkI] at this
    exact this
  have hMi : M ≠ nb i := by
    intro heq
    exact nb_nonsub k hkI i hiI hki (heq ▸ hkM)
  have hMj : M ≠ nb j := by
    intro heq
    exact nb_nonsub k hkI j hjI hkj (heq ▸ hkM)
  have hnij : nb i ≠ nb j := by
    intro heq
    exact nb_nonsub i hiI j hjI hij (heq ▸ Finset.Subset.refl (nb i))
  let F : Finset (Finset V) := {nb i, nb j, M}
  have hFcard : F.card = 3 := by simp [F, hnij, hMi.symm, hMj.symm]
  have hF : ∀ X ∈ F, 2 ≤ X.card ∧ sup_Occ 10 D T X := by
    intro X hX
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl | rfl
    · exact ⟨(nb_card i hiI).ge, hiocc⟩
    · exact ⟨(nb_card j hjI).ge, hjocc⟩
    · exact ⟨hMcard, hMocc⟩
  have hbig := sup_card_le_big h.1 T F hF
  have hsub : (sup_big 10 D T).card ≤ (merges 10 D (carrierT 10 D T)).card :=
    Finset.card_filter_le _ _
  omega

lemma six_exits {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hi : I ⊆ ineligSet 10 D) :
    6 ≤ (exitArcs 10 D (carrierT 10 D T)).card := by
  obtain ⟨pos, hpos⟩ := k4_assigned graph_ok h hc
  have hcount := tri_exits graph_ok h.1 hc hpos T I exposure
    (fun i hiI => ⟨hi hiI, incidence_ok i hiI⟩) exposure_ok
  rw [T_card, I_card] at hcount
  exact hcount

lemma exclude_two_residual {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D ≤ 1) (hi : I ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hr : (residualUnits 10 D b).card ≤ 2) : False := by
  have hmerge := three_merges h hc hz hi
  have hexit := six_exits h hc hi
  have hflow := carrier_flow_union h T (by rw [sem_supp_out graph_ok hc]; simp)
  have hsur := surplus_carrierT_eq h.1 b hb T
  have hcar : (T ∩ eligSet 10 D).card ≤ 3 := by
    have := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet 10 D ⊆ T)
    rwa [T_card] at this
  have hfilter := Finset.card_filter_le (residualUnits 10 D b)
    (fun u => (supp 10 D u.1 ∩ T).Nonempty)
  rw [T_card] at hflow
  omega

lemma all_exact_masks {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D) :
    ∀ i ∈ I, sup_Occ 10 D T (nb i) := by
  intro i hiI
  exact exact_mask_of_witness (sem_exact_nbhd graph_ok h.1 hc T T_independent
    (sem_noempty_chain_out graph_ok h hc hz (hi hiI)))

lemma tight_counts {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hr : (residualUnits 10 D b).card ≤ 3) :
    (merges 10 D (carrierT 10 D T)).card = 3 ∧
      (exitArcs 10 D (carrierT 10 D T)).card = 6 := by
  have hmerge := three_merges h hc (by omega) hi
  have hexit := six_exits h hc hi
  have hflow := carrier_flow_union h T (by rw [sem_supp_out graph_ok hc]; simp)
  have hsur := surplus_carrierT_eq h.1 b hb T
  have hcar : (T ∩ eligSet 10 D).card ≤ 3 := by
    have := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet 10 D ⊆ T)
    rwa [T_card] at this
  have hfilter := Finset.card_filter_le (residualUnits 10 D b)
    (fun u => (supp 10 D u.1 ∩ T).Nonempty)
  rw [T_card] at hflow
  omega

lemma no_full_mask {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3) :
    ∀ w, supp 10 D w ∩ T ≠ T := by
  classical
  intro w hw
  let F : Finset (Finset V) := {nb 0, nb 8, nb 9, T}
  have hFcard : F.card = 4 := by decide +kernel
  have hF : ∀ X ∈ F, 2 ≤ X.card ∧ sup_Occ 10 D T X := by
    intro X hX
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl | rfl | rfl
    · exact ⟨by decide, all_exact_masks h hc hz hi 0 (by decide)⟩
    · exact ⟨by decide, all_exact_masks h hc hz hi 8 (by decide)⟩
    · exact ⟨by decide, all_exact_masks h hc hz hi 9 (by decide)⟩
    · exact ⟨by decide, ⟨w, hw⟩⟩
  have hbig := sup_card_le_big h.1 T F hF
  have hsub : (sup_big 10 D T).card ≤ (merges 10 D (carrierT 10 D T)).card :=
    Finset.card_filter_le _ _
  omega

lemma proper_pair_split_disjoint {A B M : Finset V} (hM : M.card = 2)
    (hA : A ⊂ M) (hB : B ⊂ M) (hU : A ∪ B = M) : Disjoint A B := by
  have ha := Finset.card_lt_card hA
  have hb := Finset.card_lt_card hB
  have hcard := Finset.card_union_add_card_inter A B
  rw [hU, hM] at hcard
  apply Finset.disjoint_iff_inter_eq_empty.mpr
  exact Finset.card_eq_zero.mp (by omega)

lemma pair_creation {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3) :
    ∀ i ∈ I, ∃ j ∈ merges 10 D (carrierT 10 D T),
      supp 10 D (10 + j) ∩ T = nb i ∧ tag D j = false ∧
        Disjoint (supp 10 D (opA D j) ∩ T) (supp 10 D (opB D j) ∩ T) := by
  intro i hiI
  obtain ⟨w, hw⟩ := all_exact_masks h hc hz hi i hiI
  have hcard := nb_card i hiI
  obtain ⟨j, _, _, hjM, hjmerge, _, hcase⟩ := sem_first_mask h.1 T (nb i) hcard.ge w hw
  refine ⟨j, hjmerge, hjM, ?_⟩
  rcases hcase with hAnd | hOr
  · have hlt := Finset.card_lt_card hAnd.2.1
    have hfull : supp 10 D (opA D j) ∩ T = T :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [T_card]; omega)
    exact False.elim (no_full_mask h hc hz hi hm _ hfull)
  · exact ⟨hOr.1, proper_pair_split_disjoint hcard hOr.2.1 hOr.2.2.1 hOr.2.2.2.1⟩

lemma all_merges_or_disjoint {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3) :
    ∀ j ∈ merges 10 D (carrierT 10 D T), tag D j = false ∧
      Disjoint (supp 10 D (opA D j) ∩ T) (supp 10 D (opB D j) ∩ T) := by
  classical
  choose! g hg using pair_creation h hc hz hi hm
  have hinj : Set.InjOn g I := by
    intro i hiI j hjI heq
    by_contra hij
    have he : nb i = nb j := (hg i hiI).2.1.symm.trans (heq ▸ (hg j hjI).2.1)
    exact nb_nonsub i hiI j hjI hij (by rw [he])
  have hsub : I.image g ⊆ merges 10 D (carrierT 10 D T) := by
    intro j hj
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hj
    exact (hg i hiI).1
  have hcard : (I.image g).card = 3 := by
    rw [Finset.card_image_of_injOn hinj, I_card]
  have heq : I.image g = merges 10 D (carrierT 10 D T) :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro j hj
  rw [← heq] at hj
  obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hj
  exact (hg i hiI).2.2

lemma no_and_T_support {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3) :
    ∀ j < D.length, tag D j = true → supp 10 D (10 + j) ∩ T = ∅ := by
  intro j hj hop
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  obtain ⟨hxo, hxT⟩ := Finset.mem_inter.mp hx
  have hxa := sem_supp_and_sub h.1 hj hop false hxo
  have hxb := sem_supp_and_sub h.1 hj hop true hxo
  rw [sb_src_false] at hxa
  rw [sb_src_true] at hxb
  have hmj : j ∈ merges 10 D (carrierT 10 D T) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, ?_, ?_, ?_⟩
    · exact sup_mem_carrier.mpr ⟨x, Finset.mem_inter.mpr ⟨hxo, hxT⟩⟩
    · exact sup_mem_carrier.mpr ⟨x, Finset.mem_inter.mpr ⟨hxa, hxT⟩⟩
    · exact sup_mem_carrier.mpr ⟨x, Finset.mem_inter.mpr ⟨hxb, hxT⟩⟩
  have hfalse := (all_merges_or_disjoint h hc hz hi hm j hmj).1
  rw [hop] at hfalse
  contradiction

lemma no_singleton_T_merges {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3) :
    ∀ x ∈ T, merges 10 D (carrierT 10 D {x}) = ∅ := by
  intro x hxT
  apply Finset.eq_empty_of_forall_notMem
  intro j hj
  obtain ⟨hj, hxo, hxa, hxb⟩ := Finset.mem_filter.mp hj
  have hsub : carrierT 10 D {x} ⊆ carrierT 10 D T := by
    intro w hw
    exact sup_mem_carrier.mpr ⟨x, Finset.mem_inter.mpr ⟨sem_mem_carrier1.mp hw, hxT⟩⟩
  have hmj : j ∈ merges 10 D (carrierT 10 D T) :=
    Finset.mem_filter.mpr ⟨hj, hsub hxo, hsub hxa, hsub hxb⟩
  have hd := (all_merges_or_disjoint h hc hz hi hm j hmj).2
  exact Finset.disjoint_left.mp hd
    (Finset.mem_inter.mpr ⟨sem_mem_carrier1.mp hxa, hxT⟩)
    (Finset.mem_inter.mpr ⟨sem_mem_carrier1.mp hxb, hxT⟩)

lemma two_merges_unconditional {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hi : I ⊆ ineligSet 10 D) :
    2 ≤ (merges 10 D (carrierT 10 D T)).card := by
  obtain ⟨e0, _, _, _, _, h0, _, _⟩ := sem_inelig_consumer graph_ok h hc (hi (by decide : (0 : V) ∈ I))
  obtain ⟨e8, _, _, _, _, h8, _, _⟩ := sem_inelig_consumer graph_ok h hc (hi (by decide : (8 : V) ∈ I))
  exact k4_pair_merges h.1 T_card (a := (5 : V)) (b := (4 : V)) (c := (6 : V))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (h0 5 (by decide)) (h0 4 (by decide)) (h8 5 (by decide)) (h8 6 (by decide))

lemma residual_at_least_two {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hi : I ⊆ ineligSet 10 D) (b : V → ℕ) (hb : PureBranch 10 D b) :
    2 ≤ (residualUnits 10 D b).card := by
  have hmerge := two_merges_unconditional h hc hi
  have hexit := six_exits h hc hi
  have hflow := carrier_flow_union h T (by rw [sem_supp_out graph_ok hc]; simp)
  have hsur := surplus_carrierT_eq h.1 b hb T
  have hcar : (T ∩ eligSet 10 D).card ≤ 3 := by
    have := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet 10 D ⊆ T)
    rwa [T_card] at this
  have hfilter := Finset.card_filter_le (residualUnits 10 D b)
    (fun u => (supp 10 D u.1 ∩ T).Nonempty)
  rw [T_card] at hflow
  omega

lemma tight_budget {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hlen : D.length ≤ 19) (hi : ineligSet 10 D = I)
    (b : V → ℕ) (hb : PureBranch 10 D b) :
    Bplus 10 D = 10 ∧ Bzero 10 D = 0 ∧ (residualUnits 10 D b).card = 3 ∧ D.length = 19 := by
  have hsub : I ⊆ ineligSet 10 D := by rw [hi]
  have he : (eligSet 10 D).card = 7 := by
    have hsum : (ineligSet 10 D).card + (eligSet 10 D).card = 10 := by
      simpa only [ineligSet, Finset.card_univ, Fintype.card_fin] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (eligSet 10 D))
    rw [hi, I_card] at hsum
    omega
  have hres := card_residual h.1 b hb
  have hr2 := residual_at_least_two h hc hsub b hb
  have hsur := surplus_identity h
  rw [he] at hres
  rw [totalSurplus_split] at hsur
  have hz : Bzero 10 D ≤ 1 := by omega
  have hr3 : 3 ≤ (residualUnits 10 D b).card := by
    by_contra hlt
    exact exclude_two_residual h hc hz hsub b hb (by omega)
  omega

open DagTools

lemma tight_exit_cover {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hi : I ⊆ ineligSet 10 D)
    (hcard : (exitArcs 10 D (carrierT 10 D T)).card = 6) :
    ∃ pos wit : V → ℕ × Bool, k4_Pos 10 adj D pos ∧
      (∀ f ∈ T, (wit f).1 < D.length ∧ tag D (wit f).1 = true ∧
        f ∈ supp 10 D (src D (wit f)) ∧ f ∉ supp 10 D (10 + (wit f).1) ∧
        Disjoint (supp 10 D (src D (wit f))) (exposure f)) ∧
      exitArcs 10 D (carrierT 10 D T) = I.image pos ∪ T.image wit ∧
      (∀ e ∈ exitArcs 10 D (carrierT 10 D T),
        (∃ i ∈ I, e = pos i) ∨ ∃ f ∈ T, e = wit f) := by
  classical
  obtain ⟨pos, hpos⟩ := k4_assigned graph_ok h hc
  obtain ⟨hsub, hsize⟩ := k4_exits_ge hpos T I
    (fun i hiI => ⟨hi hiI, (incidence_ok i hiI).1⟩)
  have hex : ∀ f ∈ T, ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
      f ∈ supp 10 D (src D e) ∧ f ∉ supp 10 D (10 + e.1) ∧
      Disjoint (supp 10 D (src D e)) (exposure f) := by
    intro f hf
    obtain ⟨j, s, h1, h2, h4, h5, h6⟩ :=
      sem_exposure graph_ok h.1 hc (exposure f) (exposure_ok f hf).1 f
        (exposure_ok f hf).2.2
    exact ⟨(j, s), h1, h2, h4, h5, h6⟩
  choose! wit hw using hex
  have hinj : Set.InjOn wit T := by
    intro f hf g hg hfg
    by_contra hne
    exact Finset.disjoint_left.mp (hw f hf).2.2.2.2
      (hfg ▸ (hw g hg).2.2.1)
      ((exposure_ok f hf).2.1 (Finset.mem_erase.mpr ⟨fun h => hne h.symm, hg⟩))
  have hdis : Disjoint (I.image pos) (T.image wit) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp he1
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he2
    obtain ⟨a, ha, hia⟩ := (incidence_ok i hiI).2 f hf
    exact Finset.disjoint_left.mp (hw f hf).2.2.2.2
      (hfe ▸ (hpos.1 i (hi hiI)).2.2.1 a hia) ha
  have hsub2 : T.image wit ⊆ exitArcs 10 D (carrierT 10 D T) := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨h1, h2, h4, h5, h6⟩ := hw f hf
    refine k4_mem_exit.mpr ⟨h1, ⟨f, Finset.mem_inter.mpr ⟨h4, hf⟩⟩, ?_⟩
    rintro ⟨g, hg⟩
    rw [Finset.mem_inter] at hg
    have hgs := sem_supp_and_sub h.1 h1 h2 (wit f).2 hg.1
    exact Finset.disjoint_left.mp h6 hgs
      ((exposure_ok f hf).2.1 (Finset.mem_erase.mpr ⟨fun h => h5 (h ▸ hg.1), hg.2⟩))
  have hall : I.image pos ∪ T.image wit = exitArcs 10 D (carrierT 10 D T) := by
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset hsub hsub2)
    rw [Finset.card_union_of_disjoint hdis, hsize,
      Finset.card_image_of_injOn hinj, I_card, T_card, hcard]
  refine ⟨pos, wit, hpos, hw, hall.symm, ?_⟩
  intro e he
  rw [← hall, Finset.mem_union] at he
  rcases he with he | he
  · obtain ⟨i, hiI, he⟩ := Finset.mem_image.mp he
    exact Or.inl ⟨i, hiI, he.symm⟩
  · obtain ⟨f, hf, he⟩ := Finset.mem_image.mp he
    exact Or.inr ⟨f, hf, he.symm⟩

lemma exposure_T_single {D : Dag} {f : V} (hf : f ∈ T) {w : ℕ}
    (hw : f ∈ supp 10 D w) (hd : Disjoint (supp 10 D w) (exposure f)) :
    supp 10 D w ∩ T = {f} := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hxt⟩
    by_contra hne
    exact Finset.disjoint_left.mp hd hx
      ((exposure_ok f hf).2.1 (Finset.mem_erase.mpr ⟨hne, hxt⟩))
  · rintro rfl
    exact ⟨hw, hf⟩

lemma tight_exit_data {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hi : I ⊆ ineligSet 10 D)
    (hcard : (exitArcs 10 D (carrierT 10 D T)).card = 6) :
    ∃ pos wit : V → ℕ × Bool, k4_Pos 10 adj D pos ∧
      (∀ f ∈ T, wit f ∈ sem_W 10 D f ∧
        supp 10 D (src D (wit f)) ∩ T = {f} ∧
        Disjoint (supp 10 D (src D (wit f))) (exposure f)) ∧
      exitArcs 10 D (carrierT 10 D T) = I.image pos ∪ T.image wit := by
  obtain ⟨pos, wit, hpos, hw, heq, _⟩ := tight_exit_cover h hc hi hcard
  refine ⟨pos, wit, hpos, ?_, heq⟩
  intro f hf
  obtain ⟨h1, _, h2, h3, h4⟩ := hw f hf
  exact ⟨sem_mem_W.mpr ⟨h1, h2, h3⟩, exposure_T_single hf h2 h4, h4⟩

lemma chain_and_neighbors {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) {i : V} (hi : i ∈ ineligSet 10 D) {g : ℕ} {s : Bool}
    (hg : g < D.length) (ht : tag D g = true)
    (hch : sem_Chain 10 D i.val (src D (g, !s))) :
    ∀ a, adj i a → a ∈ supp 10 D (src D (g, s)) := by
  have hfpos := sem_step_fanout (sem_step_src (n := 10) (D := D) hg (!s))
  have hf : fanout D (src D (g, !s)) = 1 := by
    by_contra hne
    have htwo : 2 ≤ fanout D (src D (g, !s)) := by omega
    have hnon := sem_bzero_branch h.1 hz htwo
    rw [sem_branch_empty graph_ok h.1 hc hi hch htwo] at hnon
    exact Finset.not_nonempty_empty hnon
  have hgo : sem_Chain 10 D i.val (10 + g) :=
    Relation.ReflTransGen.tail hch ⟨sem_step_src hg (!s), hf⟩
  intro a hia
  have htruth := (sem_dom_split h.1 hc (single a) i (10 + g)
    (sem_chain_dom h.1 hgo) (sem_single_no_edge graph_ok a)
    ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, single]⟩).2
  rw [sem_val_gate_src h.1 _ hg s, ht, gop_true, Bool.and_eq_true] at htruth
  have hind := sem_sibling_indep h.1 i hg s hch hf
    (single a) (sem_ins i (single a)) (sem_ins_agree i (single a))
  exact mem_supp.mpr (hind.trans htruth.1)

lemma chain_and_assigned {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    {pos wit : V → ℕ × Bool} (hp : k4_Pos 10 adj D pos)
    (hw : ∀ f ∈ T, supp 10 D (src D (wit f)) ∩ T = {f})
    (he : exitArcs 10 D (carrierT 10 D T) = I.image pos ∪ T.image wit)
    {i : V} (hiI : i ∈ I) {g : ℕ} {s : Bool}
    (hg : g < D.length) (ht : tag D g = true)
    (hch : sem_Chain 10 D i.val (src D (g, !s))) : (g, s) = pos i := by
  classical
  have hnb := chain_and_neighbors h hc hz (hi hiI) hg ht hch
  have hsub : nb i ⊆ supp 10 D (src D (g, s)) ∩ T := by
    intro a ha
    obtain ⟨haT, hia⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_inter.mpr ⟨hnb a hia, haT⟩
  have htwo : 2 ≤ (supp 10 D (src D (g, s)) ∩ T).card := by
    have := Finset.card_le_card hsub
    rw [nb_card i hiI] at this
    exact this
  have hpure := sem_dom_pure graph_ok h.1 hc i (src D (g, !s)) (sem_chain_dom h.1 hch)
  have himiss : i ∉ T := by
    have hh : ∀ x ∈ I, x ∉ T := by decide +kernel
    exact hh i hiI
  have hexit : (g, s) ∈ exitArcs 10 D (carrierT 10 D T) := by
    refine k4_mem_exit.mpr ⟨hg, Finset.card_pos.mp (by omega), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨hxs, hxT⟩ := Finset.mem_inter.mp hx
    have hxi := Finset.mem_singleton.mp (hpure (sem_supp_and_sub h.1 hg ht (!s) hxs))
    exact himiss (hxi ▸ hxT)
  rw [he, Finset.mem_union] at hexit
  rcases hexit with hh | hh
  · obtain ⟨j, hjI, heq⟩ := Finset.mem_image.mp hh
    have hje := (hp.1 j (hi hjI)).2.2.2
    rw [heq] at hje
    have hjm : j ∈ supp 10 D (src D (g, !s)) := by rw [hje]; simp
    have hji := Finset.mem_singleton.mp (hpure hjm)
    simpa only [hji] using heq.symm
  · obtain ⟨f, hf, heq⟩ := Finset.mem_image.mp hh
    have hh := hw f hf
    rw [heq] at hh
    rw [hh, Finset.card_singleton] at htwo
    omega

lemma assigned_source_exact {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    {pos wit : V → ℕ × Bool} (hp : k4_Pos 10 adj D pos)
    (hw : ∀ f ∈ T, supp 10 D (src D (wit f)) ∩ T = {f})
    (he : exitArcs 10 D (carrierT 10 D T) = I.image pos ∪ T.image wit)
    {i : V} (hiI : i ∈ I) :
    ∀ a, a ∈ supp 10 D (src D (pos i)) ↔ adj i a := by
  intro a
  have hchain := sem_noempty_chain_out graph_ok h hc hz (hi hiI)
  obtain ⟨g, s, hg, ht, hch, hmask⟩ := sem_exact_nbhd graph_ok h.1 hc {a}
    (by simpa only [Finset.mem_singleton, forall_eq] using graph_ok.2.1 a) hchain
  have heq := chain_and_assigned h hc hz hi hp hw he hiI hg ht hch
  simpa only [heq] using hmask a (Finset.mem_singleton_self a)

lemma T_neighbors_card : ∀ x ∈ T, (I.filter (fun i => adj i x)).card = 2 := by
  decide +kernel

lemma assigned_T_mask {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3)
    (pos : V → ℕ × Bool) (hpos : k4_Pos 10 adj D pos) :
    ∀ i ∈ I, supp 10 D (src D (pos i)) ∩ T = nb i := by
  intro i hiI
  have hsub : nb i ⊆ supp 10 D (src D (pos i)) ∩ T := by
    intro a ha
    obtain ⟨hat, hia⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_inter.mpr ⟨(hpos.1 i (hi hiI)).2.2.1 a hia, hat⟩
  have hproper : supp 10 D (src D (pos i)) ∩ T ⊂ T :=
    Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.inter_subset_right, no_full_mask h hc hz hi hm _⟩
  have hcard := Finset.card_lt_card hproper
  rw [T_card] at hcard
  have heq : nb i = supp 10 D (src D (pos i)) ∩ T :=
    Finset.eq_of_subset_of_card_le hsub (by rw [nb_card i hiI]; omega)
  exact heq.symm

lemma W_to_T_exit {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3)
    {x : V} (hxT : x ∈ T) {e : ℕ × Bool} (he : e ∈ sem_W 10 D x) :
    e ∈ exitArcs 10 D (carrierT 10 D T) := by
  obtain ⟨hej, hxs, _⟩ := sem_mem_W.mp he
  apply k4_mem_exit.mpr
  refine ⟨hej, ⟨x, Finset.mem_inter.mpr ⟨hxs, hxT⟩⟩, ?_⟩
  rw [no_and_T_support h hc hz hi hm e.1 hej (sem_W_and h.1 he)]
  exact Finset.not_nonempty_empty

lemma T_codes_card_one_of_cover {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3)
    (helig : T ⊆ eligSet 10 D) (b : V → ℕ) (hb : PureBranch 10 D b)
    (pos wit : V → ℕ × Bool) (hpos : k4_Pos 10 adj D pos)
    (hwit : ∀ x ∈ T, wit x ∈ sem_W 10 D x ∧
      supp 10 D (src D (wit x)) ∩ T = {x} ∧
      Disjoint (supp 10 D (src D (wit x))) (exposure x))
    (hcover : exitArcs 10 D (carrierT 10 D T) = I.image pos ∪ T.image wit) :
    ∀ x ∈ T, ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).card = 1 := by
  classical
  intro x hxT
  let N := I.filter (fun i => adj i x)
  have hNcard : N.card = 2 := T_neighbors_card x hxT
  have hposmask := assigned_T_mask h hc hz hi hm pos hpos
  have hNimage : N.image pos ⊆ sem_W 10 D x := by
    intro e he
    obtain ⟨i, hiN, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hiI, hix⟩ := Finset.mem_filter.mp hiN
    obtain ⟨hij, hiempty, hineigh, _⟩ := hpos.1 i (hi hiI)
    apply sem_mem_W.mpr
    refine ⟨hij, hineigh x hix, ?_⟩
    rw [hiempty]
    exact Finset.notMem_empty x
  have hNinj : Set.InjOn pos N := by
    intro i hiN j hjN heq
    exact hpos.2 i (hi (Finset.mem_filter.mp hiN).1) j
      (hi (Finset.mem_filter.mp hjN).1) heq
  have hNimagecard : (N.image pos).card = 2 := by
    rw [Finset.card_image_of_injOn hNinj, hNcard]
  have hwit_not : wit x ∉ N.image pos := by
    intro hmem
    obtain ⟨i, hiN, heq⟩ := Finset.mem_image.mp hmem
    have hiI := (Finset.mem_filter.mp hiN).1
    obtain ⟨a, haA, hia⟩ := (incidence_ok i hiI).2 x hxT
    have has : a ∈ supp 10 D (src D (wit x)) := by
      rw [← heq]
      exact (hpos.1 i (hi hiI)).2.2.1 a hia
    exact Finset.disjoint_left.mp (hwit x hxT).2.2 has haA
  have hlow : 3 ≤ (sem_W 10 D x).card := by
    have hsub : insert (wit x) (N.image pos) ⊆ sem_W 10 D x :=
      Finset.insert_subset (hwit x hxT).1 hNimage
    have hcount := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hwit_not, hNimagecard] at hcount
    exact hcount
  have hupper : (sem_W 10 D x).card ≤ 3 := by
    have hsub : sem_W 10 D x ⊆ insert (wit x) (N.image pos) := by
      intro e he
      have hTe := W_to_T_exit h hc hz hi hm hxT he
      rw [hcover] at hTe
      rcases Finset.mem_union.mp hTe with hiPos | hiWit
      · obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hiPos
        have hxs := (sem_mem_W.mp he).2.1
        have hmask : x ∈ supp 10 D (src D (pos i)) ∩ T :=
          Finset.mem_inter.mpr ⟨hxs, hxT⟩
        rw [hposmask i hiI] at hmask
        have hix := (Finset.mem_filter.mp hmask).2
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨i, Finset.mem_filter.mpr ⟨hiI, hix⟩, rfl⟩)
      · obtain ⟨f, hfT, rfl⟩ := Finset.mem_image.mp hiWit
        have hxs := (sem_mem_W.mp he).2.1
        have hmask : x ∈ supp 10 D (src D (wit f)) ∩ T :=
          Finset.mem_inter.mpr ⟨hxs, hxT⟩
        rw [(hwit f hfT).2.1, Finset.mem_singleton] at hmask
        subst f
        exact Finset.mem_insert_self _ _
    have hcount := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hwit_not, hNimagecard] at hcount
    exact hcount
  have hWcard : (sem_W 10 D x).card = 3 := by omega
  have hcode := sem_code_count graph_ok h hc b hb x
  have hsingle : ({x} : Finset V) ∩ eligSet 10 D = {x} :=
    Finset.singleton_inter_of_mem (helig hxT)
  rw [hWcard, no_singleton_T_merges h hc hz hi hm x hxT,
    Finset.card_empty, hsingle, Finset.card_singleton] at hcode
  omega

lemma T_eligible_of_exact_I {D : Dag} (hi : ineligSet 10 D = I) : T ⊆ eligSet 10 D := by
  intro x hxT
  by_contra hx
  have hxI : x ∈ I := by
    rw [← hi]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
  have hdis : Disjoint I T := by decide +kernel
  exact Finset.disjoint_left.mp hdis hxI hxT

lemma residual_meets_T {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hr : (residualUnits 10 D b).card ≤ 3) :
    ∀ u ∈ residualUnits 10 D b, ∃ t ∈ T, t ∈ supp 10 D u.1 := by
  classical
  obtain ⟨hmerge, hexit⟩ := tight_counts h hc hz hi b hb hr
  have hflow := carrier_flow_union h T (by rw [sem_supp_out graph_ok hc]; simp)
  have hsur := surplus_carrierT_eq h.1 b hb T
  have hcar : (T ∩ eligSet 10 D).card ≤ 3 := by
    have := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet 10 D ⊆ T)
    rwa [T_card] at this
  let Q := (residualUnits 10 D b).filter (fun u => (supp 10 D u.1 ∩ T).Nonempty)
  have hfilter : Q.card ≤ (residualUnits 10 D b).card := Finset.card_filter_le _ _
  rw [T_card, hmerge, hexit] at hflow
  have hQ : Q = residualUnits 10 D b :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by dsimp [Q] at *; omega)
  intro u hu
  rw [← hQ] at hu
  obtain ⟨t, ht⟩ := (Finset.mem_filter.mp hu).2
  exact ⟨t, (Finset.mem_inter.mp ht).2, (Finset.mem_inter.mp ht).1⟩

lemma residual_has_singleton_code {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hr : (residualUnits 10 D b).card ≤ 3)
    (hcodes : ∀ t ∈ T,
      ((residualUnits 10 D b).filter (fun u => t ∈ supp 10 D u.1)).card = 1) :
    ∀ u ∈ residualUnits 10 D b, ∃ t ∈ T,
      (residualUnits 10 D b).filter (fun v => t ∈ supp 10 D v.1) = {u} := by
  classical
  intro u hu
  obtain ⟨t, htT, htu⟩ := residual_meets_T h hc hz hi b hb hr u hu
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (hcodes t htT)
  have hucode : u ∈ (residualUnits 10 D b).filter (fun v => t ∈ supp 10 D v.1) :=
    Finset.mem_filter.mpr ⟨hu, htu⟩
  rw [hv, Finset.mem_singleton] at hucode
  exact ⟨t, htT, hv.trans (congrArg (fun z => ({z} : Finset (Σ _ : ℕ, ℕ))) hucode.symm)⟩

namespace JointExit

open DagTools

lemma support_or_exit_of_path {n : ℕ} {D : Dag} (hS : Strict n D) (t : Fin n)
    (hAnd : ∀ j, j < D.length → tag D j = true → t ∉ supp n D (n + j))
    {a b : ℕ} (hp : Relation.ReflTransGen (sem_step n D) a b)
    (hta : t ∈ supp n D a) :
    (t ∈ supp n D b ∧ supp n D a ⊆ supp n D b) ∨
      ∃ e ∈ exitArcs n D (carrierT n D {t}), supp n D a ⊆ supp n D (src D e) := by
  induction hp with
  | refl => exact Or.inl ⟨hta, Finset.Subset.refl _⟩
  | @tail u v hp hstep ih =>
    rcases ih with ⟨htu, hsub⟩ | hexit
    · obtain ⟨j, side, hj, rfl, hsrc⟩ := sem_step_iff.mp hstep
      by_cases htout : t ∈ supp n D (n + j)
      · have hor : tag D j = false := Bool.eq_false_iff.mpr (fun hand => hAnd j hj hand htout)
        have hkeep : supp n D u ⊆ supp n D (n + j) := by
          rw [← hsrc, sem_supp_or hS hj hor]
          cases side
          · rw [sb_src_false]
            exact Finset.subset_union_left
          · rw [sb_src_true]
            exact Finset.subset_union_right
        exact Or.inl ⟨htout, hsub.trans hkeep⟩
      · refine Or.inr ⟨(j, side), sem_mem_exit1.mpr ⟨hj, ?_, htout⟩, ?_⟩
        · simpa only [hsrc] using htu
        · simpa only [hsrc] using hsub
    · exact Or.inr hexit

lemma support_subset_exit {n : ℕ} {D : Dag} (h : StrictLive n D) (t : Fin n)
    (hout : t ∉ supp n D (outW n D))
    (hAnd : ∀ j, j < D.length → tag D j = true → t ∉ supp n D (n + j))
    {w : ℕ} (ht : t ∈ supp n D w) :
    ∃ e ∈ exitArcs n D (carrierT n D {t}), supp n D w ⊆ supp n D (src D e) := by
  have hp : Relation.ReflTransGen (sem_step n D) w (outW n D) :=
    live_reaches_out h w (sem_supp_lt ht)
  rcases support_or_exit_of_path h.1 t hAnd hp ht with ⟨htout, _⟩ | hexit
  · exact False.elim (hout htout)
  · exact hexit

lemma joint_support_exit {n : ℕ} {D : Dag} (h : StrictLive n D) (t c : Fin n)
    (hout : t ∉ supp n D (outW n D))
    (hAnd : ∀ j, j < D.length → tag D j = true → t ∉ supp n D (n + j))
    {w : ℕ} (ht : t ∈ supp n D w) (hc : c ∈ supp n D w) :
    ∃ e ∈ exitArcs n D (carrierT n D {t}),
      t ∈ supp n D (src D e) ∧ c ∈ supp n D (src D e) := by
  obtain ⟨e, he, hsub⟩ := support_subset_exit h t hout hAnd ht
  exact ⟨e, he, hsub ht, hsub hc⟩

lemma no_joint_support_of_exit_exclusion {n : ℕ} {D : Dag} (h : StrictLive n D)
    (t c : Fin n) (hout : t ∉ supp n D (outW n D))
    (hAnd : ∀ j, j < D.length → tag D j = true → t ∉ supp n D (n + j))
    (hexit : ∀ e ∈ exitArcs n D (carrierT n D {t}), c ∉ supp n D (src D e)) :
    ∀ w, t ∈ supp n D w → c ∉ supp n D w := by
  intro w ht hc
  obtain ⟨e, he, _, hce⟩ := joint_support_exit h t c hout hAnd ht hc
  exact hexit e he hce


end JointExit
namespace Finish

open DagTools

section Generic
variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma sem_one_exit_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x : Fin n} {e : ℕ × Bool}
    (he : exitArcs n D (carrierT n D {x}) = {e}) :
    supp n D (src D e) = {x} := by
  have hex : e ∈ exitArcs n D (carrierT n D {x}) := by rw [he]; simp
  refine Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr (sem_mem_exit1.mp hex).2.1)
  intro y hy
  rw [Finset.mem_singleton]
  by_contra hyx
  obtain ⟨z, hxz, hyz⟩ := hG.2.2.1 x y (Ne.symm hyx)
  have hA : ∀ a ∈ ({y, z} : Finset (Fin n)), ∀ b ∈ ({y, z} : Finset (Fin n)), ¬ G a b := by
    intro a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hG.2.1 _
    · exact hyz
    · exact fun h => hyz (hG.1 _ _ h)
    · exact hG.2.1 _
  obtain ⟨j, s, hj, _, hxs, hxn, hd⟩ := sem_exposure hG hS hC {y, z} hA x ⟨z, by simp, hxz⟩
  have hje : (j, s) = e := by
    have hm := sem_mem_exit1.mpr ⟨hj, hxs, hxn⟩
    rwa [he, Finset.mem_singleton] at hm
  exact Finset.disjoint_left.mp hd (by simpa only [hje] using hy) (by simp)


lemma sem_two_exit_other_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x z : Fin n} (hxz : x ≠ z) (hz : z ∈ ineligSet n D)
    {e f : ℕ × Bool} {S : Finset (Fin n)}
    (hW : exitArcs n D (carrierT n D {x}) ⊆ {e, f})
    (hf : f ∈ exitArcs n D (carrierT n D {x}))
    (hSub : S ⊆ supp n D (src D e))
    (hsep : ∀ y, y ≠ z → y ≠ x → ∃ A : Finset (Fin n),
      (∀ a ∈ A, ∀ b ∈ A, ¬ G a b) ∧ y ∈ A ∧
      (∃ a ∈ A, a ∈ S) ∧ ∃ a ∈ A, G x a) :
    supp n D (src D f) = {x} := by
  have hxf := (sem_mem_exit1.mp hf).2.1
  refine Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr hxf)
  intro y hy
  rw [Finset.mem_singleton]
  by_contra hyx
  have hyz : y ≠ z := by
    intro hyz
    subst y
    have hp := sem_inelig_pure hG hS hC hz hy
    rw [hp, Finset.mem_singleton] at hxf
    exact hxz hxf
  obtain ⟨A, hA, hyA, ⟨a, haA, haS⟩, hnb⟩ := hsep y hyz hyx
  obtain ⟨j, s, hj, _, hxs, hxn, hd⟩ := sem_exposure hG hS hC A hA x hnb
  have heither := hW (sem_mem_exit1.mpr ⟨hj, hxs, hxn⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at heither
  rcases heither with he | he
  · exact Finset.disjoint_left.mp hd (by simpa only [he] using hSub haS) haA
  · exact Finset.disjoint_left.mp hd (by simpa only [he] using hy) hyA

lemma sem_nonpure_exit_card (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x y : Fin n} {e : ℕ × Bool}
    (he : e ∈ exitArcs n D (carrierT n D {x}))
    (hy : y ∈ supp n D (src D e)) (hyx : y ≠ x) :
    2 ≤ (exitArcs n D (carrierT n D {x})).card := by
  have hpos := Finset.card_pos.mpr ⟨e, he⟩
  by_contra hc
  have hone : (exitArcs n D (carrierT n D {x})).card = 1 := by omega
  obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hone
  have hef : e = f := by rwa [hf, Finset.mem_singleton] at he
  rw [hef, sem_one_exit_pure hG hS hC hf, Finset.mem_singleton] at hy
  exact hyx hy


lemma sem_two_exit_remaining_slot (hG : sem_Gr G) (hS : Strict n D)
    (hC : sem_Comp n G D) {x z : Fin n} {e f : ℕ × Bool}
    (hW : exitArcs n D (carrierT n D {x}) ⊆ {e, f})
    (hbar : supp n D (src D (e.1, !e.2)) = {z}) {y : Fin n}
    (hxy : G x y) (hyz : y ≠ z) :
    (f.1, !f.2) ∈ exitArcs n D (carrierT n D {y}) := by
  obtain ⟨j, hj, _, _, hxn, hyn, s, hxs, _, hys, _⟩ := sem_joint_meeting hG hS hC hxy
  have heither := hW (sem_mem_exit1.mpr ⟨hj, hxs, hxn⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at heither
  rcases heither with he | hf
  · have hy : y ∈ supp n D (src D (e.1, !e.2)) := by simpa only [← he] using hys
    rw [hbar, Finset.mem_singleton] at hy
    exact False.elim (hyz hy)
  · apply sem_mem_exit1.mpr
    simpa only [← hf] using And.intro hj (And.intro hys hyn)


end Generic

def M : Finset V := {1, 3, 7}

def center (x : V) : V := if x = 1 then 0 else if x = 3 then 8 else 9

def finishExposureMask (x y : V) : Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 104, 20, 36, 80, 208, 276, 548,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 50, 36, 0, 48, 36, 68, 208, 0, 548,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 50, 20, 104, 20, 48, 68, 0, 276, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0].getD
     (10 * x.val + y.val) 0

def finishExposure (x y : V) : Finset V :=
  Finset.univ.filter (fun a => (finishExposureMask x y).testBit a.val = true)

lemma finish_geometry : ∀ x ∈ M,
    center x ∈ I ∧ adj (center x) x ∧
    (∃ a : V, adj (center x) a ∧ a ≠ x) ∧
    adj x 2 ∧ (2 : V) ≠ center x ∧ x ≠ center x ∧ x ∉ T := by
  decide +kernel

lemma finish_exposure_ok : ∀ x ∈ M, ∀ y : V, y ≠ center x → y ≠ x →
    (∀ a ∈ finishExposure x y, ∀ b ∈ finishExposure x y, ¬ adj a b) ∧
    y ∈ finishExposure x y ∧
    (∃ a ∈ finishExposure x y, adj (center x) a) ∧
    ∃ a ∈ finishExposure x y, adj x a := by
  decide +kernel

lemma residual_outside_exits {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (b : V → ℕ) (hb : PureBranch 10 D b)
    (hr : ∀ u ∈ residualUnits 10 D b, supp 10 D u.1 ⊆ T)
    {x : V} (hx : x ∉ T) : (sem_W 10 D x).card ≤ 2 := by
  classical
  have hempty : (residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro u hu
    obtain ⟨hu, hxu⟩ := Finset.mem_filter.mp hu
    exact hx (hr u hu hxu)
  have count := sem_code_count graph_ok h hc b hb x
  rw [hempty, Finset.card_empty] at count
  have hone : (({x} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  omega

lemma two_exit_cover {α : Type*} [DecidableEq α] {S : Finset α} {e : α}
    (hc : S.card = 2) (he : e ∈ S) : ∃ f, f ∈ S ∧ S ⊆ {e, f} := by
  obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.mp hc
  rw [hS, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact ⟨b, by simp [hS], by simp [hS]⟩
  · exact ⟨a, by simp [hS], by simp [hS, Finset.pair_comm]⟩

lemma middle_second_exit {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hi : I ⊆ ineligSet 10 D) (b : V → ℕ) (hb : PureBranch 10 D b)
    (hr : ∀ u ∈ residualUnits 10 D b, supp 10 D u.1 ⊆ T)
    {x : V} (hx : x ∈ M) :
    ∃ e ∈ sem_W 10 D (2 : V), supp 10 D (src D (sem_bar e)) = {x} := by
  classical
  obtain ⟨hci, hcx, ⟨a, hca, hax⟩, hx2, h2c, hxc, hxT⟩ := finish_geometry x hx
  obtain ⟨q, hq, _, hp, hout, hn, _, _⟩ := sem_inelig_consumer graph_ok h hc (hi hci)
  let e := sem_bar q
  have he : e ∈ sem_W 10 D x := by
    apply sem_mem_W.mpr
    refine ⟨hq, hn x hcx, ?_⟩
    change x ∉ supp 10 D (10 + q.1)
    rw [hout]
    exact Finset.notMem_empty x
  have ha : a ∈ supp 10 D (src D e) := hn a hca
  have hlo := sem_nonpure_exit_card graph_ok h.1 hc he ha hax
  change 2 ≤ (sem_W 10 D x).card at hlo
  have hhi := residual_outside_exits h hc b hb hr hxT
  obtain ⟨f, hf, hcover⟩ := two_exit_cover (by omega : (sem_W 10 D x).card = 2) he
  have hbar : supp 10 D (src D (e.1, !e.2)) = {center x} := by
    change supp 10 D (src D (sem_bar (sem_bar q))) = {center x}
    rwa [sem_bar_bar]
  have hfp : supp 10 D (src D f) = {x} := by
    apply sem_two_exit_other_pure graph_ok h.1 hc hxc (hi hci) hcover hf
      (S := Finset.univ.filter (adj (center x)))
    · intro v hv
      exact hn v (Finset.mem_filter.mp hv).2
    · intro y hyc hyx
      obtain ⟨hA, hyA, ⟨v, hvA, hcv⟩, hnb⟩ := finish_exposure_ok x hx y hyc hyx
      exact ⟨finishExposure x y, hA, hyA, ⟨v, hvA, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcv⟩⟩, hnb⟩
  refine ⟨sem_bar f, sem_two_exit_remaining_slot graph_ok h.1 hc hcover hbar hx2 h2c, ?_⟩
  rwa [sem_bar_bar]

lemma residual_supported_on_T_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : I ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (hr : ∀ u ∈ residualUnits 10 D b, supp 10 D u.1 ⊆ T) : False := by
  classical
  obtain ⟨e1, h1, hp1⟩ := middle_second_exit h hc hi b hb hr (x := 1) (by decide)
  obtain ⟨e3, h3, hp3⟩ := middle_second_exit h hc hi b hb hr (x := 3) (by decide)
  obtain ⟨e7, h7, hp7⟩ := middle_second_exit h hc hi b hb hr (x := 7) (by decide)
  have h13 : e1 ≠ e3 := by
    intro he
    have : ({1} : Finset V) = {3} := hp1.symm.trans (he ▸ hp3)
    exact (by decide : (1 : V) ≠ 3) (Finset.singleton_injective this)
  have h17 : e1 ≠ e7 := by
    intro he
    have : ({1} : Finset V) = {7} := hp1.symm.trans (he ▸ hp7)
    exact (by decide : (1 : V) ≠ 7) (Finset.singleton_injective this)
  have h37 : e3 ≠ e7 := by
    intro he
    have : ({3} : Finset V) = {7} := hp3.symm.trans (he ▸ hp7)
    exact (by decide : (3 : V) ≠ 7) (Finset.singleton_injective this)
  have hlo : 3 ≤ (sem_W 10 D (2 : V)).card :=
    Finset.two_lt_card.mpr ⟨e1, h1, e3, h3, e7, h7, h13, h17, h37⟩
  have hhi := residual_outside_exits h hc b hb hr (x := 2) (by decide)
  omega

end Finish

def privateNeighbor (t : V) : V := if t = 4 then 3 else if t = 5 then 7 else 1

lemma private_geometry : ∀ t ∈ T,
    privateNeighbor t ∈ exposure t ∧
      (∀ c, adj t c → c ∈ I ∨ c = privateNeighbor t) ∧
      ∀ i ∈ I, adj i t → ¬ adj i (privateNeighbor t) := by
  decide +kernel

lemma residual_support_pair_of_separation {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hr : (residualUnits 10 D b).card ≤ 3)
    (hcodes : ∀ t ∈ T,
      ((residualUnits 10 D b).filter (fun u => t ∈ supp 10 D u.1)).card = 1)
    (hsep : ∀ t ∈ T, ∀ c, c ≠ t → ¬ adj t c →
      ¬ (∀ u ∈ residualUnits 10 D b, t ∈ supp 10 D u.1 → c ∈ supp 10 D u.1)) :
    ∀ u ∈ residualUnits 10 D b, ∃ t ∈ T, t ∈ supp 10 D u.1 ∧
      supp 10 D u.1 ⊆ {t, privateNeighbor t} := by
  classical
  intro u hu
  obtain ⟨t, htT, hcode⟩ := residual_has_singleton_code h hc hz hi b hb hr hcodes u hu
  have htu : t ∈ supp 10 D u.1 := by
    have hmem : u ∈ (residualUnits 10 D b).filter (fun v => t ∈ supp 10 D v.1) := by
      rw [hcode]
      exact Finset.mem_singleton_self u
    exact (Finset.mem_filter.mp hmem).2
  refine ⟨t, htT, htu, ?_⟩
  intro c hcU
  by_cases hct : c = t
  · rw [hct]
    simp
  · have hAdj : adj t c := by
      by_contra hnon
      apply hsep t htT c hct hnon
      intro v hv htv
      have hvc : v ∈ (residualUnits 10 D b).filter (fun z => t ∈ supp 10 D z.1) :=
        Finset.mem_filter.mpr ⟨hv, htv⟩
      rw [hcode, Finset.mem_singleton] at hvc
      simpa only [hvc] using hcU
    rcases (private_geometry t htT).2.1 c hAdj with hcI | hcp
    · have hfan : 2 ≤ fanout D u.1 := by
        have huUnits : u ∈ units 10 D :=
          (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).1
        have := (mem_units.mp huUnits).2
        omega
      have hlow := mem_ineligSet.mp (hi hcI) u.1 hcU
      omega
    · rw [hcp]
      simp

lemma private_neighbor_absent_at_exits {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3)
    (pos wit : V → ℕ × Bool) (hpos : k4_Pos 10 adj D pos)
    (hwit : ∀ f ∈ T, wit f ∈ sem_W 10 D f ∧
      supp 10 D (src D (wit f)) ∩ T = {f} ∧
      Disjoint (supp 10 D (src D (wit f))) (exposure f))
    (hcover : exitArcs 10 D (carrierT 10 D T) = I.image pos ∪ T.image wit) :
    ∀ t ∈ T, ∀ e ∈ sem_W 10 D t, privateNeighbor t ∉ supp 10 D (src D e) := by
  intro t htT e he hprivate
  have hEt := W_to_T_exit h hc hz hi hm htT he
  rw [hcover] at hEt
  rcases Finset.mem_union.mp hEt with hposE | hwitE
  · obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hposE
    have hExact := assigned_source_exact h hc hz hi hpos
      (fun f hf => (hwit f hf).2.1) hcover hiI
    have hit := (hExact t).mp (sem_mem_W.mp he).2.1
    have him := (hExact (privateNeighbor t)).mp hprivate
    exact (private_geometry t htT).2.2 i hiI hit him
  · obtain ⟨f, hfT, rfl⟩ := Finset.mem_image.mp hwitE
    have htmask : t ∈ supp 10 D (src D (wit f)) ∩ T :=
      Finset.mem_inter.mpr ⟨(sem_mem_W.mp he).2.1, htT⟩
    rw [(hwit f hfT).2.1, Finset.mem_singleton] at htmask
    subst f
    exact Finset.disjoint_left.mp (hwit t htT).2.2 hprivate (private_geometry t htT).1

lemma private_neighbor_no_joint {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : I ⊆ ineligSet 10 D)
    (hm : (merges 10 D (carrierT 10 D T)).card = 3)
    (pos wit : V → ℕ × Bool) (hpos : k4_Pos 10 adj D pos)
    (hwit : ∀ f ∈ T, wit f ∈ sem_W 10 D f ∧
      supp 10 D (src D (wit f)) ∩ T = {f} ∧
      Disjoint (supp 10 D (src D (wit f))) (exposure f))
    (hcover : exitArcs 10 D (carrierT 10 D T) = I.image pos ∪ T.image wit) :
    ∀ t ∈ T, ∀ w, t ∈ supp 10 D w → privateNeighbor t ∉ supp 10 D w := by
  intro t htT
  apply JointExit.no_joint_support_of_exit_exclusion h t (privateNeighbor t)
  · rw [sem_supp_out graph_ok hc]
    exact Finset.notMem_empty t
  · intro j hj hop htj
    have hmj : t ∈ supp 10 D (10 + j) ∩ T := Finset.mem_inter.mpr ⟨htj, htT⟩
    rw [no_and_T_support h hc hz hi hm j hj hop] at hmj
    exact Finset.notMem_empty t hmj
  · exact private_neighbor_absent_at_exits h hc hz hi hm pos wit hpos hwit hcover t htT

lemma extendable_I_impossible_of_separation {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hlen : D.length ≤ 19) (hi : ineligSet 10 D = I)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (hsep : ∀ t ∈ T, ∀ c, c ≠ t → ¬ adj t c →
      ¬ (∀ u ∈ residualUnits 10 D b, t ∈ supp 10 D u.1 → c ∈ supp 10 D u.1)) : False := by
  obtain ⟨_, hz, hr, _⟩ := tight_budget h hc hlen hi b hb
  have hsub : I ⊆ ineligSet 10 D := by rw [hi]
  obtain ⟨hm, he⟩ := tight_counts h hc hz hsub b hb hr.le
  obtain ⟨pos, wit, hpos, hwit, hcover⟩ := tight_exit_data h hc hsub he
  have hcodes := T_codes_card_one_of_cover h hc hz hsub hm
    (T_eligible_of_exact_I hi) b hb pos wit hpos hwit hcover
  have hpair := residual_support_pair_of_separation h hc hz hsub b hb hr.le hcodes hsep
  have hprivate := private_neighbor_no_joint h hc hz hsub hm pos wit hpos hwit hcover
  apply Finish.residual_supported_on_T_impossible h hc hsub b hb
  intro u hu c hcU
  obtain ⟨t, htT, htu, hsupport⟩ := hpair u hu
  have hwhich := hsupport hcU
  simp only [Finset.mem_insert, Finset.mem_singleton] at hwhich
  rcases hwhich with hct | hcp
  · exact hct ▸ htT
  · exact False.elim (hprivate t htT u.1 htu (hcp ▸ hcU))

def separationCenter (t c : V) : V :=
  if adj 0 t ∧ ¬ adj 0 c then 0 else if adj 8 t ∧ ¬ adj 8 c then 8 else 9

def separationMask (t c : V) : Nat :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 138, 548, 0, 0, 104, 104, 138, 770, 0, 0, 138, 276, 138, 208, 0, 208, 0, 0, 770, 521, 0, 548, 138, 50, 50, 0, 138, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List Nat).getD (10 * t.val + c.val) 0

def separationExposure (t c : V) : Finset V :=
  Finset.univ.filter (fun a => (separationMask t c).testBit a.val = true)

lemma separation_geometry : ∀ t ∈ T, ∀ c : V, c ≠ t → ¬ adj t c →
    separationCenter t c ∈ I ∧ adj (separationCenter t c) t ∧
      ¬ adj (separationCenter t c) c ∧
      (∀ a ∈ separationExposure t c, ∀ b ∈ separationExposure t c, ¬ adj a b) ∧
      c ∈ separationExposure t c ∧
      (∃ a ∈ separationExposure t c, adj (separationCenter t c) a) ∧
      ∃ a ∈ separationExposure t c, adj t a := by
  decide +kernel

lemma separation_from_exact_stars {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : I ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (helig : T ⊆ eligSet 10 D)
    (hnonempty : ∀ t ∈ T,
      ((residualUnits 10 D b).filter (fun u => t ∈ supp 10 D u.1)).Nonempty)
    (pos : V → ℕ × Bool) (hpos : k4_Pos 10 adj D pos)
    (hexact : ∀ i ∈ I, ∀ a, a ∈ supp 10 D (src D (pos i)) ↔ adj i a) :
    ∀ t ∈ T, ∀ c, c ≠ t → ¬ adj t c →
      ¬ (∀ u ∈ residualUnits 10 D b, t ∈ supp 10 D u.1 → c ∈ supp 10 D u.1) := by
  intro t htT c hct htc hres
  obtain ⟨u, hu⟩ := hnonempty t htT
  obtain ⟨huR, htu⟩ := Finset.mem_filter.mp hu
  have hcu := hres u huR htu
  obtain ⟨exception, hrest⟩ := ri_gen graph_ok h hc b hb hct.symm (helig htT) hres ⟨htu, hcu⟩
  obtain ⟨hiI, hit, hic, hA, hcA, ⟨a, haA, hia⟩, htnb⟩ :=
    separation_geometry t htT c hct htc
  let i := separationCenter t c
  have hstar : pos i ∈ sem_W 10 D t := by
    obtain ⟨hij, hio, hin, _⟩ := hpos.1 i (hi hiI)
    apply sem_mem_W.mpr
    refine ⟨hij, hin t hit, ?_⟩
    rw [hio]
    exact Finset.notMem_empty t
  have hstar_c : c ∉ supp 10 D (src D (pos i)) := fun hcs => hic ((hexact i hiI c).mp hcs)
  obtain ⟨j, side, hj, _, htj, htout, hdis⟩ :=
    sem_exposure graph_ok h.1 hc (separationExposure t c) hA t htnb
  have hexpose : (j, side) ∈ sem_W 10 D t := sem_mem_W.mpr ⟨hj, htj, htout⟩
  have hexpose_c : c ∉ supp 10 D (src D (j, side)) :=
    fun hcs => Finset.disjoint_left.mp hdis hcs hcA
  have hne : pos i ≠ (j, side) := by
    intro heq
    have has : a ∈ supp 10 D (src D (j, side)) := by
      rw [← heq]
      exact (hpos.1 i (hi hiI)).2.2.1 a hia
    exact Finset.disjoint_left.mp hdis has haA
  have hstar_exception : pos i = exception := by
    by_contra hnot
    exact hstar_c (hrest (pos i) hstar hnot)
  have hexpose_exception : (j, side) = exception := by
    by_contra hnot
    exact hexpose_c (hrest (j, side) hexpose hnot)
  exact hne (hstar_exception.trans hexpose_exception.symm)

lemma extendable_I_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hlen : D.length ≤ 19) (hi : ineligSet 10 D = I) : False := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  apply extendable_I_impossible_of_separation h hc hlen hi b hb
  obtain ⟨_, hz, hr, _⟩ := tight_budget h hc hlen hi b hb
  have hsub : I ⊆ ineligSet 10 D := by rw [hi]
  obtain ⟨hm, he⟩ := tight_counts h hc hz hsub b hb hr.le
  obtain ⟨pos, wit, hpos, hwit, hcover⟩ := tight_exit_data h hc hsub he
  have helig := T_eligible_of_exact_I hi
  have hcodes := T_codes_card_one_of_cover h hc hz hsub hm helig b hb pos wit hpos hwit hcover
  apply separation_from_exact_stars h hc hsub b hb helig ?_ pos hpos
    (fun i hiI => assigned_source_exact h hc hz hsub hpos
      (fun f hf => (hwit f hf).2.1) hcover hiI)
  intro t htT
  apply Finset.card_pos.mp
  rw [hcodes t htT]
  decide

lemma relabel_computes {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (σ : Equiv.Perm V) (hσ : ∀ u v, adj (σ u) (σ v) ↔ adj u v) :
    sem_Comp 10 adj (relabel σ D) := by
  intro x
  rw [relabel_out σ h.1 h.2.2]
  constructor
  · intro hx
    obtain ⟨u, v, huv, hu, hv⟩ := (hc _).mp hx
    exact ⟨σ u, σ v, (hσ u v).mpr huv, hu, hv⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    apply (hc _).mpr
    refine ⟨σ.symm u, σ.symm v, ?_, ?_, ?_⟩
    · apply (hσ _ _).mp
      simpa using huv
    · simpa using hu
    · simpa using hv

lemma canonicalize_three_ineligible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : (ineligSet 10 D).card = 3) :
    ∃ D' : Dag, StrictLive 10 D' ∧ sem_Comp 10 adj D' ∧ D'.length = D.length ∧
      (ineligSet 10 D' = ({1, 4, 5} : Finset V) ∨ ineligSet 10 D' = I) := by
  have hind : I3Geometry.Independent (ineligSet 10 D) := by
    intro u hu v hv huv
    rcases sem_elig_cover graph_ok h hc huv with hu' | hv'
    · exact (sem_mem_inelig.mp hu) hu'
    · exact (sem_mem_inelig.mp hv) hv'
  obtain ⟨σ, hσ, heq⟩ := I3Geometry.classify (ineligSet 10 D) hi hind
  refine ⟨relabel σ D, relabel_strictLive σ h, relabel_computes h hc σ hσ,
    relabel_length σ D, ?_⟩
  rw [relabel_ineligSet σ h.1]
  rcases heq with heq | heq
  · exact Or.inl (heq.trans I3Geometry.canonical_masks.1)
  · exact Or.inr (heq.trans I3Geometry.canonical_masks.2)

lemma reduce_three_to_neighborhood {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hlen : D.length ≤ 19)
    (hi : (ineligSet 10 D).card = 3) :
    ∃ D' : Dag, StrictLive 10 D' ∧ sem_Comp 10 adj D' ∧ D'.length = D.length ∧
      ineligSet 10 D' = ({1, 4, 5} : Finset V) := by
  obtain ⟨D', h', hc', hl, hN | hI⟩ := canonicalize_three_ineligible h hc hi
  · exact ⟨D', h', hc', hl, hN⟩
  · exact False.elim (extendable_I_impossible h' hc' (by omega) hI)

namespace NeighborCover

open DagTools Finish

section Generic
variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma sem_two_exit_remaining_neighbors (hG : sem_Gr G) (hS : Strict n D)
    (hC : sem_Comp n G D) {x z : Fin n} {e f : ℕ × Bool}
    (hW : exitArcs n D (carrierT n D {x}) ⊆ {e, f})
    (hbar : supp n D (src D (e.1, !e.2)) = {z}) :
    ∀ y, G x y → y ≠ z → y ∈ supp n D (src D (f.1, !f.2)) := by
  intro y hxy hyz
  obtain ⟨j, hj, _, _, hxn, _, s, hxs, _, hys, _⟩ := sem_joint_meeting hG hS hC hxy
  have heither := hW (sem_mem_exit1.mpr ⟨hj, hxs, hxn⟩)
  simp only [Finset.mem_insert, Finset.mem_singleton] at heither
  rcases heither with he | hf
  · have hy : y ∈ supp n D (src D (e.1, !e.2)) := by simpa only [← he] using hys
    rw [hbar, Finset.mem_singleton] at hy
    exact False.elim (hyz hy)
  · simpa only [← hf] using hys


end Generic

def J : Finset V := {1, 4, 5}

def C : Finset V := {2, 3, 6, 7, 8, 9}

def owner (x : V) : V :=
  if x = 2 ∨ x = 6 then 1 else if x = 3 ∨ x = 9 then 4 else 5

def exposureMask (x y : V) : Nat :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   9, 0, 0, 9, 208, 104, 72, 129, 385, 521, 5, 770, 5, 0, 0, 548, 69, 385, 257, 516,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   257, 0, 260, 521, 276, 548, 0, 385, 257, 513, 5, 770, 5, 521, 276, 0, 69, 0, 260, 513,
   9, 138, 69, 9, 208, 0, 65, 136, 0, 521, 65, 138, 69, 72, 0, 104, 65, 129, 385, 0].getD
     (10 * x.val + y.val) 0

def exposureSet (x y : V) : Finset V :=
  Finset.univ.filter (fun a => (exposureMask x y).testBit a.val = true)

def code (D : Dag) (b : V → ℕ) (x : V) : Finset (Σ _ : ℕ, ℕ) :=
  (residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)

lemma geometry : ∀ x ∈ C,
    owner x ∈ J ∧ adj (owner x) x ∧ adj (owner x) 0 ∧ (0 : V) ≠ x ∧ x ≠ owner x := by
  decide +kernel

lemma cycle_geometry : ∀ x ∈ C, ∀ y ∈ C, adj x y →
    y ≠ owner x ∧ x ≠ owner y ∧
      ∃ z ∈ C, adj x z ∧ z ≠ y ∧ z ≠ owner x := by
  decide +kernel

lemma exposure_ok : ∀ x ∈ C, ∀ y : V, y ≠ owner x → y ≠ x →
    (∀ a ∈ exposureSet x y, ∀ b ∈ exposureSet x y, ¬ adj a b) ∧
    y ∈ exposureSet x y ∧
    (∃ a ∈ exposureSet x y, adj (owner x) a) ∧
    ∃ a ∈ exposureSet x y, adj x a := by
  decide +kernel

lemma empty_code_exits_le_two {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (b : V → ℕ) (hb : PureBranch 10 D b)
    {x : V} (hx : code D b x = ∅) : (sem_W 10 D x).card ≤ 2 := by
  have count := sem_code_count graph_ok h hc b hb x
  change (sem_W 10 D x).card + (merges 10 D (carrierT 10 D {x})).card =
    1 + (({x} : Finset V) ∩ eligSet 10 D).card + (code D b x).card at count
  rw [hx, Finset.card_empty] at count
  have hone : (({x} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  omega

lemma empty_code_exits {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hi : J ⊆ ineligSet 10 D) (b : V → ℕ) (hb : PureBranch 10 D b)
    {x : V} (hx : x ∈ C) (hempty : code D b x = ∅) :
    ∃ e f : ℕ × Bool, sem_W 10 D x ⊆ {e, f} ∧
      supp 10 D (src D (sem_bar e)) = {owner x} ∧
      supp 10 D (src D f) = {x} := by
  classical
  obtain ⟨hoi, hox, ho0, h0x, hxo⟩ := geometry x hx
  obtain ⟨q, hq, _, hp, hout, hn, _, _⟩ := sem_inelig_consumer graph_ok h hc (hi hoi)
  let e := sem_bar q
  have he : e ∈ sem_W 10 D x := by
    apply sem_mem_W.mpr
    refine ⟨hq, hn x hox, ?_⟩
    change x ∉ supp 10 D (10 + q.1)
    rw [hout]
    exact Finset.notMem_empty x
  have ha : (0 : V) ∈ supp 10 D (src D e) := hn 0 ho0
  have hlo := sem_nonpure_exit_card graph_ok h.1 hc he ha h0x
  change 2 ≤ (sem_W 10 D x).card at hlo
  have hhi := empty_code_exits_le_two h hc b hb hempty
  obtain ⟨f, hf, hcover⟩ := two_exit_cover (by omega : (sem_W 10 D x).card = 2) he
  have hbar : supp 10 D (src D (sem_bar e)) = {owner x} := by
    change supp 10 D (src D (sem_bar (sem_bar q))) = {owner x}
    rwa [sem_bar_bar]
  refine ⟨e, f, hcover, hbar, ?_⟩
  apply sem_two_exit_other_pure graph_ok h.1 hc hxo (hi hoi) hcover hf
    (S := Finset.univ.filter (adj (owner x)))
  · intro v hv
    exact hn v (Finset.mem_filter.mp hv).2
  · intro y hyo hyx
    obtain ⟨hA, hyA, ⟨v, hvA, hov⟩, hnb⟩ := exposure_ok x hx y hyo hyx
    exact ⟨exposureSet x y, hA, hyA,
      ⟨v, hvA, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hov⟩⟩, hnb⟩

lemma no_adjacent_empty_codes {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : J ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) {x y : V}
    (hx : x ∈ C) (hy : y ∈ C) (hxy : adj x y)
    (hx0 : code D b x = ∅) (hy0 : code D b y = ∅) : False := by
  obtain ⟨ex, fx, hWx, hpex, hpfx⟩ := empty_code_exits h hc hi b hb hx hx0
  obtain ⟨ey, fy, hWy, hpey, hpfy⟩ := empty_code_exits h hc hi b hb hy hy0
  obtain ⟨hyo, hxo, z, hz, hxz, hzy, hzo⟩ := cycle_geometry x hx y hy hxy
  have hslot : sem_bar fx ∈ sem_W 10 D y :=
    sem_two_exit_remaining_slot graph_ok h.1 hc hWx hpex hxy hyo
  have hzslot : z ∈ supp 10 D (src D (sem_bar fx)) :=
    sem_two_exit_remaining_neighbors graph_ok h.1 hc hWx hpex z hxz hzo
  have heither := hWy hslot
  simp only [Finset.mem_insert, Finset.mem_singleton] at heither
  rcases heither with he | he
  · have heq : supp 10 D (src D fx) = {owner y} := by
      rw [← sem_bar_bar fx, he]
      exact hpey
    have heq2 : ({x} : Finset V) = {owner y} := hpfx.symm.trans heq
    exact hxo (Finset.singleton_injective heq2)
  · rw [he, hpfy, Finset.mem_singleton] at hzslot
    exact hzy hzslot

lemma finite_vertex_cover_bound (S : Finset V)
    (hcover : ∀ x ∈ C, ∀ y ∈ C, adj x y → x ∈ S ∨ y ∈ S) :
    3 ≤ (S ∩ C).card := by
  have h23 : ∃ a ∈ S ∩ C, a ∈ ({2, 3} : Finset V) := by
    rcases hcover 2 (by decide) 3 (by decide) (by decide) with h2 | h3
    · exact ⟨2, Finset.mem_inter.mpr ⟨h2, by decide⟩, by decide⟩
    · exact ⟨3, Finset.mem_inter.mpr ⟨h3, by decide⟩, by decide⟩
  have h68 : ∃ a ∈ S ∩ C, a ∈ ({6, 8} : Finset V) := by
    rcases hcover 6 (by decide) 8 (by decide) (by decide) with h6 | h8
    · exact ⟨6, Finset.mem_inter.mpr ⟨h6, by decide⟩, by decide⟩
    · exact ⟨8, Finset.mem_inter.mpr ⟨h8, by decide⟩, by decide⟩
  have h79 : ∃ a ∈ S ∩ C, a ∈ ({7, 9} : Finset V) := by
    rcases hcover 7 (by decide) 9 (by decide) (by decide) with h7 | h9
    · exact ⟨7, Finset.mem_inter.mpr ⟨h7, by decide⟩, by decide⟩
    · exact ⟨9, Finset.mem_inter.mpr ⟨h9, by decide⟩, by decide⟩
  obtain ⟨a, ha, ha23⟩ := h23
  obtain ⟨b, hb, hb68⟩ := h68
  obtain ⟨c, hc, hc79⟩ := h79
  have hdistinct : ∀ a ∈ ({2, 3} : Finset V), ∀ b ∈ ({6, 8} : Finset V),
      ∀ c ∈ ({7, 9} : Finset V), a ≠ b ∧ a ≠ c ∧ b ≠ c := by decide +kernel
  obtain ⟨hab, hac, hbc⟩ := hdistinct a ha23 b hb68 c hc79
  exact Finset.two_lt_card.mpr ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩

lemma three_cycle_vertices_in_residual_support {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : J ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) :
    3 ≤ (C.filter (fun x => (code D b x).Nonempty)).card := by
  classical
  let S := C.filter (fun x => (code D b x).Nonempty)
  have hcover : ∀ x ∈ C, ∀ y ∈ C, adj x y → x ∈ S ∨ y ∈ S := by
    intro x hx y hy hxy
    by_cases hxc : (code D b x).Nonempty
    · exact Or.inl (Finset.mem_filter.mpr ⟨hx, hxc⟩)
    · have hx0 := Finset.not_nonempty_iff_eq_empty.mp hxc
      by_cases hyc : (code D b y).Nonempty
      · exact Or.inr (Finset.mem_filter.mpr ⟨hy, hyc⟩)
      · exact False.elim (no_adjacent_empty_codes h hc hi b hb hx hy hxy hx0
          (Finset.not_nonempty_iff_eq_empty.mp hyc))
  have hbound := finite_vertex_cover_bound S hcover
  have hsub : S ⊆ C := Finset.filter_subset _ _
  rwa [Finset.inter_eq_left.mpr hsub] at hbound

lemma center_three_exits {D : Dag} (hi : J ⊆ ineligSet 10 D)
    {pos : V → ℕ × Bool} (hpos : k4_Pos 10 adj D pos) :
    J.image pos ⊆ sem_W 10 D (0 : V) ∧ (J.image pos).card = 3 := by
  obtain ⟨hsub, hcard⟩ := k4_exits_ge hpos ({0} : Finset V) J (by
    intro i hiJ
    refine ⟨hi hiJ, 0, Finset.mem_singleton_self 0, ?_⟩
    have hf : ∀ i ∈ J, adj i 0 := by decide +kernel
    exact hf i hiJ)
  have hJ : J.card = 3 := by decide +kernel
  exact ⟨hsub, hcard.trans hJ⟩

lemma one_center_code_data {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : J ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hcode : (code D b 0).card ≤ 1) :
    ∃ pos : V → ℕ × Bool, k4_Pos 10 adj D pos ∧
      sem_W 10 D 0 = J.image pos ∧
      merges 10 D (carrierT 10 D ({0} : Finset V)) = ∅ ∧
      (code D b 0).card = 1 := by
  classical
  obtain ⟨pos, hpos⟩ := k4_assigned graph_ok h hc
  obtain ⟨hsub, hcard⟩ := center_three_exits hi hpos
  have hlo : 3 ≤ (sem_W 10 D (0 : V)).card := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  have count := sem_code_count graph_ok h hc b hb (0 : V)
  change (sem_W 10 D (0 : V)).card + (merges 10 D (carrierT 10 D ({0} : Finset V))).card =
    1 + (({0} : Finset V) ∩ eligSet 10 D).card + (code D b 0).card at count
  have hone : (({0} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have hW : (sem_W 10 D (0 : V)).card = 3 := by omega
  refine ⟨pos, hpos, ?_, Finset.card_eq_zero.mp (by omega), by omega⟩
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

lemma one_center_code_no_and {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : J ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hcode : (code D b 0).card ≤ 1)
    {j : ℕ} (hj : j < D.length) (hand : tag D j = true) :
    (0 : V) ∉ supp 10 D (10 + j) := by
  obtain ⟨_, _, _, hmerge, _⟩ := one_center_code_data h hc hi b hb hcode
  intro hz
  have hor := (sem_zm_gate h.1 hmerge hj hz).1
  rw [hand] at hor
  exact Bool.false_ne_true hor.symm

lemma center_chain_assigned {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    {pos : V → ℕ × Bool} (hp : k4_Pos 10 adj D pos)
    (he : sem_W 10 D (0 : V) = J.image pos)
    {i : V} (hiJ : i ∈ J) {g : ℕ} {s : Bool}
    (hg : g < D.length) (ht : tag D g = true)
    (hch : sem_Chain 10 D i.val (src D (g, !s))) : (g, s) = pos i := by
  have hnb := chain_and_neighbors h hc hz (hi hiJ) hg ht hch
  have hpure := sem_dom_pure graph_ok h.1 hc i (src D (g, !s)) (sem_chain_dom h.1 hch)
  have hgeom : ∀ i ∈ J, adj i 0 ∧ i ≠ 0 := by decide +kernel
  have hslot : (g, s) ∈ sem_W 10 D (0 : V) := by
    refine sem_mem_W.mpr ⟨hg, hnb 0 (hgeom i hiJ).1, ?_⟩
    intro h0
    have h0i := Finset.mem_singleton.mp (hpure (sem_supp_and_sub h.1 hg ht (!s) h0))
    exact (hgeom i hiJ).2 h0i.symm
  rw [he] at hslot
  obtain ⟨j, hjJ, heq⟩ := Finset.mem_image.mp hslot
  have hje := (hp.1 j (hi hjJ)).2.2.2
  rw [heq] at hje
  have hjm : j ∈ supp 10 D (src D (g, !s)) := by rw [hje]; simp
  have hji := Finset.mem_singleton.mp (hpure hjm)
  simpa only [hji] using heq.symm

lemma one_center_code_stars_exact {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hcode : (code D b 0).card ≤ 1) :
    ∃ pos : V → ℕ × Bool, k4_Pos 10 adj D pos ∧
      ∀ i ∈ J, ∀ a, a ∈ supp 10 D (src D (pos i)) ↔ adj i a := by
  obtain ⟨pos, hp, he, _, _⟩ := one_center_code_data h hc hi b hb hcode
  refine ⟨pos, hp, ?_⟩
  intro i hiJ a
  have hchain := sem_noempty_chain_out graph_ok h hc hz (hi hiJ)
  obtain ⟨g, s, hg, ht, hch, hmask⟩ := sem_exact_nbhd graph_ok h.1 hc {a}
    (by simpa only [Finset.mem_singleton, forall_eq] using graph_ok.2.1 a) hchain
  have heq := center_chain_assigned h hc hz hi hp he hiJ hg ht hch
  simpa only [heq] using hmask a (Finset.mem_singleton_self a)

end NeighborCover

namespace NeighborCover

open DagTools

lemma assigned_below_target {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    {pos : V → ℕ × Bool} (hp : k4_Pos 10 adj D pos)
    (he : sem_W 10 D (0 : V) = J.image pos) {i : V} (hiJ : i ∈ J) :
    ∀ x : V → Bool, val D x (10 + (pos i).1) = true → sem_Edge adj x := by
  have hgate := (hp.1 i (hi hiJ)).1
  have hsource := (hp.1 i (hi hiJ)).2.2.2
  have hmem : i ∈ supp 10 D (src D (sem_bar (pos i))) := by
    rw [show sem_bar (pos i) = ((pos i).1, !(pos i).2) from rfl, hsource]
    exact Finset.mem_singleton_self i
  have hchain := sem_inelig_chain h.1 (hi hiJ) hmem
  have hreach : Relation.ReflTransGen (sem_step 10 D) i.val (10 + (pos i).1) :=
    Relation.ReflTransGen.tail (sem_rtg_mono (fun _ _ hp => hp.1) hchain)
      (sem_step_src hgate (!(pos i).2))
  have propagate : ∀ w, Relation.ReflTransGen (sem_step 10 D) (10 + (pos i).1) w →
      ∀ x : V → Bool, val D x (10 + (pos i).1) = true → val D x w = true := by
    intro w path x hval
    induction path with
    | refl => exact hval
    | @tail w v path step ih =>
      obtain ⟨g, s, hg, rfl, rfl⟩ := sem_step_iff.mp step
      have hor : tag D g = false := by
        by_contra bad
        have hand : tag D g = true := by
          rwa [Bool.not_eq_false] at bad
        have hchi := sem_noempty_unique graph_ok h hc hz (hi hiJ) (hreach.trans path)
        have hchi' : sem_Chain 10 D i.val (src D (g, !(!s))) := by simpa using hchi
        have heq := center_chain_assigned h hc hz hi hp he hiJ hg hand hchi'
        have hgeq : g = (pos i).1 := congrArg Prod.fst heq
        have hle := sem_rtg_le h.1 (fun _ _ ht => ht) path
        have hlt := sem_src_lt h.1 hg s
        omega
      rw [sem_val_gate_src h.1 x hg s, hor, gop_false, ih]
      rfl
  intro x hx
  exact (hc x).mp (propagate (outW 10 D) (live_reaches_out h _ (by omega)) x hx)

lemma one_center_code_stars_below_target {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hcode : (code D b 0).card ≤ 1) :
    ∃ pos : V → ℕ × Bool, k4_Pos 10 adj D pos ∧
      ∀ i ∈ J, ∀ x : V → Bool, val D x (10 + (pos i).1) = true → sem_Edge adj x := by
  obtain ⟨pos, hp, he, _, _⟩ := one_center_code_data h hc hi b hb hcode
  exact ⟨pos, hp, fun i hiJ => assigned_below_target h hc hz hi hp he hiJ⟩

end NeighborCover

namespace NeighborCover

open DagTools

lemma two_stars_omit : ∀ c : V, c ≠ 0 →
    ∃ i ∈ J, ∃ j ∈ J, i ≠ j ∧ ¬ adj i c ∧ ¬ adj j c := by
  decide +kernel

lemma sole_center_unit_pure {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hcode : (code D b 0).card ≤ 1)
    {u : Σ _ : ℕ, ℕ} (hu : u ∈ residualUnits 10 D b)
    (hu0 : (0 : V) ∈ supp 10 D u.1) : supp 10 D u.1 = {0} := by
  classical
  obtain ⟨_, _, _, _, hcard⟩ := one_center_code_data h hc hi b hb hcode
  have hum : u ∈ code D b 0 := Finset.mem_filter.mpr ⟨hu, hu0⟩
  obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
  have huq : u = q := by rwa [hq, Finset.mem_singleton] at hum
  have hsingle : code D b 0 = {u} := by rwa [huq]
  have huunit : u ∈ units 10 D :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu).1).1
  have hfan := (mem_units.mp huunit).2
  have h0elig : (0 : V) ∈ eligSet 10 D :=
    mem_eligSet.mpr ⟨u.1, by omega, hu0⟩
  obtain ⟨pos, hp, hexact⟩ := one_center_code_stars_exact h hc hz hi b hb hcode
  refine Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr hu0)
  intro c hcu
  rw [Finset.mem_singleton]
  by_contra hc0
  have hres : ∀ v ∈ residualUnits 10 D b, (0 : V) ∈ supp 10 D v.1 → c ∈ supp 10 D v.1 := by
    intro v hv hv0
    have hvm : v ∈ code D b 0 := Finset.mem_filter.mpr ⟨hv, hv0⟩
    rw [hsingle, Finset.mem_singleton] at hvm
    simpa only [hvm] using hcu
  obtain ⟨e0, he0⟩ := ri_gen graph_ok h hc b hb (Ne.symm hc0) h0elig hres ⟨hu0, hcu⟩
  obtain ⟨i, hiJ, j, hjJ, hij, hic, hjc⟩ := two_stars_omit c hc0
  obtain ⟨hsub, _⟩ := center_three_exits hi hp
  have he_i : pos i ∈ sem_W 10 D (0 : V) := hsub (Finset.mem_image.mpr ⟨i, hiJ, rfl⟩)
  have he_j : pos j ∈ sem_W 10 D (0 : V) := hsub (Finset.mem_image.mpr ⟨j, hjJ, rfl⟩)
  have hne : pos i ≠ pos j := fun he => hij (hp.2 i (hi hiJ) j (hi hjJ) he)
  by_cases hie : pos i = e0
  · have hje : pos j ≠ e0 := fun hje => hne (hie.trans hje.symm)
    exact hjc ((hexact j hjJ c).mp (he0 (pos j) he_j hje))
  · exact hic ((hexact i hiJ c).mp (he0 (pos i) he_i hie))

lemma center_positive_branch_pure {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hcode : (code D b 0).card ≤ 1)
    {w : ℕ} (hw : 2 ≤ fanout D w) (hw0 : (0 : V) ∈ supp 10 D w) :
    supp 10 D w = {0} := by
  classical
  let u : Σ _ : ℕ, ℕ := ⟨w, 0⟩
  have hinner : w ∈ inner 10 D := by
    rw [inner, Finset.mem_range]
    have hlt := lt_of_fanout_pos h.1 (show 1 ≤ fanout D w by omega)
    omega
  have huunit : u ∈ unitsPlus 10 D := Finset.mem_filter.mpr
    ⟨mem_units.mpr ⟨hinner, by change 0 + 1 < fanout D w; omega⟩, ⟨0, hw0⟩⟩
  by_cases hres : u ∈ residualUnits 10 D b
  · exact sole_center_unit_pure h hc hz hi b hb hcode hres hw0
  · have hreserved : u ∈ reservedUnits 10 D b := by
      by_contra bad
      exact hres (Finset.mem_sdiff.mpr ⟨huunit, bad⟩)
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hreserved
    have hvw : b v = w := congrArg Sigma.fst heq
    have hpure := (hb v hv).2
    rw [hvw] at hpure
    have h0v : (0 : V) = v := by rwa [hpure, Finset.mem_singleton] at hw0
    simpa only [← h0v] using hpure

end NeighborCover

def oneStarMask (i x c : V) : Nat :=
  let row : List Nat := match i.val, x.val with
    | 0, 1 => [0, 0, 0, 104, 0, 0, 0, 208, 276, 548]
    | 0, 4 => [0, 0, 548, 0, 0, 0, 104, 138, 770, 0]
    | 0, 5 => [0, 0, 276, 138, 0, 0, 208, 0, 0, 770]
    | 1, 0 => [0, 0, 0, 104, 0, 0, 0, 208, 276, 548]
    | 1, 2 => [0, 0, 0, 0, 208, 104, 0, 0, 385, 521]
    | 1, 6 => [0, 0, 0, 521, 276, 548, 0, 385, 0, 0]
    | 2, 1 => [0, 0, 0, 0, 208, 104, 0, 0, 385, 521]
    | 2, 3 => [385, 0, 0, 0, 0, 50, 208, 0, 0, 770]
    | 2, 7 => [521, 0, 0, 0, 50, 0, 104, 0, 770, 0]
    | 3, 2 => [385, 0, 0, 0, 0, 50, 208, 0, 0, 770]
    | 3, 4 => [0, 770, 0, 0, 0, 548, 69, 385, 0, 0]
    | 3, 8 => [69, 50, 0, 0, 0, 0, 0, 208, 0, 548]
    | 4, 0 => [0, 0, 548, 0, 0, 0, 104, 138, 770, 0]
    | 4, 3 => [0, 770, 0, 0, 0, 548, 69, 385, 0, 0]
    | 4, 9 => [0, 138, 69, 0, 0, 104, 0, 0, 385, 0]
    | 5, 0 => [0, 0, 276, 138, 0, 0, 208, 0, 0, 770]
    | 5, 7 => [0, 770, 0, 521, 276, 0, 69, 0, 0, 0]
    | 5, 8 => [0, 138, 69, 0, 208, 0, 0, 0, 0, 521]
    | 6, 1 => [0, 0, 0, 521, 276, 548, 0, 385, 0, 0]
    | 6, 8 => [521, 0, 548, 0, 50, 0, 0, 138, 0, 0]
    | 6, 9 => [385, 0, 276, 138, 0, 50, 0, 0, 0, 0]
    | 7, 2 => [521, 0, 0, 0, 50, 0, 104, 0, 770, 0]
    | 7, 5 => [0, 770, 0, 521, 276, 0, 69, 0, 0, 0]
    | 7, 9 => [69, 50, 0, 104, 0, 0, 0, 0, 276, 0]
    | 8, 3 => [69, 50, 0, 0, 0, 0, 0, 208, 0, 548]
    | 8, 5 => [0, 138, 69, 0, 208, 0, 0, 0, 0, 521]
    | 8, 6 => [521, 0, 548, 0, 50, 0, 0, 138, 0, 0]
    | 9, 4 => [0, 138, 69, 0, 0, 104, 0, 0, 385, 0]
    | 9, 6 => [385, 0, 276, 138, 0, 50, 0, 0, 0, 0]
    | 9, 7 => [69, 50, 0, 104, 0, 0, 0, 0, 276, 0]
    | _, _ => []
  row.getD c.val 0

def oneStarExposure (i x c : V) : Finset V :=
  Finset.univ.filter (fun a => (oneStarMask i x c).testBit a.val = true)

lemma one_star_exposure_geometry : ∀ i x c : V,
    adj i x → c ≠ x → ¬ adj x c → ¬ adj i c →
      (∀ a ∈ oneStarExposure i x c, ∀ d ∈ oneStarExposure i x c, ¬ adj a d) ∧
      c ∈ oneStarExposure i x c ∧
      (∃ a ∈ oneStarExposure i x c, adj i a) ∧
      ∃ a ∈ oneStarExposure i x c, adj x a := by
  decide +kernel

lemma code_separation_of_exit_and_exposure {n : ℕ} {G : Fin n → Fin n → Prop}
    {D : Dag} (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {x c : Fin n}
    (hcx : c ≠ x) (hx : x ∈ eligSet n D)
    (hnonempty : ((residualUnits n D b).filter (fun u => x ∈ supp n D u.1)).Nonempty)
    {e : ℕ × Bool} (he : e ∈ sem_W n D x) (hce : c ∉ supp n D (src D e))
    (A : Finset (Fin n)) (hA : ∀ a ∈ A, ∀ d ∈ A, ¬ G a d)
    (hcA : c ∈ A) (hxA : ∃ a ∈ A, G x a)
    (heA : ∃ a ∈ A, a ∈ supp n D (src D e)) :
    ¬ (∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → c ∈ supp n D u.1) := by
  intro hres
  obtain ⟨u, hu⟩ := hnonempty
  obtain ⟨huR, hxu⟩ := Finset.mem_filter.mp hu
  have hcu := hres u huR hxu
  obtain ⟨exception, hrest⟩ := ri_gen hG h hc b hb hcx.symm hx hres ⟨hxu, hcu⟩
  obtain ⟨j, side, hj, _, hxj, hxout, hdis⟩ := sem_exposure hG h.1 hc A hA x hxA
  have hexpose : (j, side) ∈ sem_W n D x := sem_mem_W.mpr ⟨hj, hxj, hxout⟩
  have hexpose_c : c ∉ supp n D (src D (j, side)) :=
    fun hcs => Finset.disjoint_left.mp hdis hcs hcA
  have hne : e ≠ (j, side) := by
    intro heq
    obtain ⟨a, haA, hae⟩ := heA
    rw [heq] at hae
    exact Finset.disjoint_left.mp hdis hae haA
  have he_exception : e = exception := by
    by_contra hnot
    exact hce (hrest e he hnot)
  have hexpose_exception : (j, side) = exception := by
    by_contra hnot
    exact hexpose_c (hrest (j, side) hexpose hnot)
  exact hne (he_exception.trans hexpose_exception.symm)

lemma one_exact_star_separates {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (b : V → ℕ) (hb : PureBranch 10 D b)
    {i x c : V} (hix : adj i x) (hcx : c ≠ x) (hxc : ¬ adj x c) (hic : ¬ adj i c)
    (hx : x ∈ eligSet 10 D)
    (hnonempty : ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).Nonempty)
    {e : ℕ × Bool} (he : e ∈ sem_W 10 D x)
    (hexact : ∀ a, a ∈ supp 10 D (src D e) ↔ adj i a) :
    ¬ (∀ u ∈ residualUnits 10 D b, x ∈ supp 10 D u.1 → c ∈ supp 10 D u.1) := by
  obtain ⟨hA, hcA, ⟨a, haA, hia⟩, hxA⟩ := one_star_exposure_geometry i x c hix hcx hxc hic
  exact code_separation_of_exit_and_exposure graph_ok h hc b hb hcx hx hnonempty he
    (fun hcs => hic ((hexact c).mp hcs)) (oneStarExposure i x c) hA hcA hxA
    ⟨a, haA, (hexact a).mpr hia⟩

lemma val_agrees_outside_support_of_false_exits {n : ℕ} {D : Dag}
    (hS : Strict n D) (z : Fin n) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true)
    (hagree : ∀ i, i ≠ z → x i = y i)
    (hexit : ∀ e ∈ sem_W n D z, val D y (n + e.1) = false) :
    ∀ w, z ∉ supp n D w → val D y w = val D x w := by
  have hfalse (w : ℕ) (hy : val D y w = false) : val D x w = false := by
    by_contra hx
    have hxtrue : val D x w = true := by rwa [Bool.not_eq_false] at hx
    have hytrue := val_mono hS x y hxy w hxtrue
    rw [hy] at hytrue
    contradiction
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · have hne : (⟨w, hn⟩ : Fin n) ≠ z := by
        intro heq
        apply hw
        rw [← heq]
        exact (supp_input D ⟨w, hn⟩).symm ▸ Finset.mem_singleton_self _
      rw [val_input D y w hn, val_input D x w hn]
      exact (hagree ⟨w, hn⟩ hne).symm
    · by_cases hbound : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, _⟩ := hS j hj
        have hexit_zero (s : Bool) (hs : z ∈ supp n D (src D (j, s))) :
            val D y (n + j) = val D x (n + j) := by
          have he : (j, s) ∈ sem_W n D z := sem_mem_W.mpr ⟨hj, hs, hw⟩
          have hy := hexit (j, s) he
          exact hy.trans (hfalse (n + j) hy).symm
        by_cases hzA : z ∈ supp n D (opA D j)
        · exact hexit_zero false (by simpa only [sb_src_false] using hzA)
        · by_cases hzB : z ∈ supp n D (opB D j)
          · exact hexit_zero true (by simpa only [sb_src_true] using hzB)
          · rw [val_gate hS y j hj, val_gate hS x j hj, ih _ ha hzA, ih _ hb hzB]
      · rw [val_ge D y w (by omega), val_ge D x w (by omega)]

lemma val_two_eq_single_of_false_exits {n : ℕ} {D : Dag}
    (hS : Strict n D) (z v : Fin n)
    (hexit : ∀ e ∈ sem_W n D z, val D (sem_two z v) (n + e.1) = false) :
    ∀ w, z ∉ supp n D w → val D (sem_two z v) w = val D (single v) w := by
  apply val_agrees_outside_support_of_false_exits hS z (single v) (sem_two z v) ?_ ?_ hexit
  · intro i hi
    simp only [sem_two, Bool.or_eq_true]
    exact Or.inr hi
  · intro i hi
    simp [single, sem_two, hi]

lemma two_support_of_false_exits {n : ℕ} {D : Dag}
    (hS : Strict n D) (z v : Fin n)
    (hexit : ∀ e ∈ sem_W n D z, val D (sem_two z v) (n + e.1) = false) (w : ℕ) :
    val D (sem_two z v) w = true ↔ z ∈ supp n D w ∨ v ∈ supp n D w := by
  by_cases hz : z ∈ supp n D w
  · have htrue : val D (sem_two z v) w = true := sem_val_of_supp hS hz (by simp [sem_two])
    simp only [htrue, hz, true_or]
  · rw [val_two_eq_single_of_false_exits hS z v hexit w hz]
    simp only [hz, false_or, mem_supp]

namespace NeighborCover

lemma center_exits_false_on_nonedge {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hcode : (code D b 0).card ≤ 1)
    (v : V) (hv : ¬ adj 0 v) :
    ∀ e ∈ sem_W 10 D (0 : V), val D (sem_two 0 v) (10 + e.1) = false := by
  have hind : ¬ sem_Edge adj (sem_two (0 : V) v) := by
    rintro ⟨a, c, hac, ha, hc⟩
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at ha hc
    rcases ha with ha | ha <;> rcases hc with hc | hc <;> rw [ha, hc] at hac
    · exact graph_ok.2.1 _ hac
    · exact hv hac
    · exact hv (graph_ok.1 _ _ hac)
    · exact graph_ok.2.1 _ hac
  obtain ⟨pos, hp, he, _, _⟩ := one_center_code_data h hc hi b hb hcode
  intro e heW
  rw [he] at heW
  obtain ⟨i, hiJ, rfl⟩ := Finset.mem_image.mp heW
  by_contra bad
  have htrue : val D (sem_two 0 v) (10 + (pos i).1) = true := by
    rwa [Bool.not_eq_false] at bad
  exact hind (assigned_below_target h hc hz hi hp he hiJ (sem_two 0 v) htrue)

lemma center_restriction_preserves_labels {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hcode : (code D b 0).card ≤ 1)
    (v : V) (hv : ¬ adj 0 v) (w : ℕ) (hw : (0 : V) ∉ supp 10 D w) :
    val D (sem_two 0 v) w = val D (single v) w :=
  val_two_eq_single_of_false_exits h.1 0 v
    (center_exits_false_on_nonedge h hc hz hi b hb hcode v hv) w hw

lemma center_restriction_support {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hcode : (code D b 0).card ≤ 1)
    (v : V) (hv : ¬ adj 0 v) (w : ℕ) :
    val D (sem_two 0 v) w = true ↔ (0 : V) ∈ supp 10 D w ∨ v ∈ supp 10 D w :=
  two_support_of_false_exits h.1 0 v
    (center_exits_false_on_nonedge h hc hz hi b hb hcode v hv) w

lemma center_restriction_carrier_true {D : Dag} (hS : Strict 10 D)
    {w : ℕ} (hw : (0 : V) ∈ supp 10 D w) (x : V → Bool) :
    val D (sem_ins 0 x) w = true :=
  sem_val_of_supp hS hw (sem_ins_self 0 x)

lemma center_restriction_C_labels {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) (hcode : (code D b 0).card ≤ 1) (w : ℕ) :
    C.filter (fun v => val D (sem_two 0 v) w = true) =
      if (0 : V) ∈ supp 10 D w then C else supp 10 D w ∩ C := by
  have hgeom : ∀ v ∈ C, ¬ adj 0 v := by decide +kernel
  ext v
  by_cases hv : v ∈ C
  · simp only [Finset.mem_filter, hv, true_and]
    rw [center_restriction_support h hc hz hi b hb hcode v (hgeom v hv) w]
    by_cases hw : (0 : V) ∈ supp 10 D w <;> simp [hw, hv]
  · by_cases hw : (0 : V) ∈ supp 10 D w <;> simp [hv, hw]

end NeighborCover

namespace I4Geometry

def witnesses (i j : V) : V × V × V × V × V :=
  [(0, 0, 0, 0, 0),
   (0, 0, 0, 0, 0),
   (5, 3, 6, 8, 9),
   (1, 8, 9, 6, 7),
   (0, 0, 0, 0, 0),
   (0, 0, 0, 0, 0),
   (4, 8, 2, 3, 7),
   (4, 2, 8, 3, 6),
   (1, 3, 7, 2, 9),
   (1, 7, 3, 2, 8),
   (0, 0, 0, 0, 0),
   (0, 0, 0, 0, 0),
   (0, 0, 0, 0, 0),
   (0, 8, 7, 5, 9),
   (2, 9, 5, 7, 8),
   (2, 8, 4, 3, 9),
   (0, 0, 0, 0, 0),
   (0, 9, 3, 4, 8),
   (0, 3, 9, 4, 7),
   (2, 4, 8, 3, 5),
   (3, 5, 6, 8, 9),
   (0, 0, 0, 0, 0),
   (0, 0, 0, 0, 0),
   (0, 0, 0, 0, 0),
   (7, 0, 8, 5, 6),
   (3, 0, 9, 4, 6),
   (3, 9, 0, 4, 5),
   (0, 0, 0, 0, 0),
   (1, 5, 4, 0, 9),
   (1, 4, 5, 0, 8),
   (8, 1, 9, 6, 7),
   (8, 0, 7, 5, 9),
   (0, 0, 0, 0, 0),
   (0, 0, 0, 0, 0),
   (0, 0, 0, 0, 0),
   (2, 0, 6, 1, 9),
   (4, 1, 5, 0, 7),
   (4, 5, 1, 0, 6),
   (0, 0, 0, 0, 0),
   (2, 6, 0, 1, 5),
   (0, 0, 0, 0, 0),
   (9, 2, 5, 7, 8),
   (0, 7, 8, 5, 6),
   (0, 0, 0, 0, 0),
   (0, 0, 0, 0, 0),
   (3, 7, 1, 2, 6),
   (3, 1, 7, 2, 5),
   (0, 2, 6, 1, 8),
   (0, 6, 2, 1, 7),
   (0, 0, 0, 0, 0),
   (0, 0, 0, 0, 0),
   (8, 2, 4, 3, 9),
   (0, 3, 9, 4, 6),
   (0, 2, 6, 1, 9),
   (7, 3, 1, 2, 6),
   (0, 0, 0, 0, 0),
   (7, 1, 3, 2, 4),
   (0, 0, 0, 0, 0),
   (0, 0, 0, 0, 0),
   (0, 6, 2, 1, 3),
   (8, 4, 2, 3, 7),
   (0, 0, 0, 0, 0),
   (9, 3, 0, 4, 5),
   (1, 4, 5, 0, 7),
   (1, 3, 7, 2, 5),
   (1, 7, 3, 2, 4),
   (0, 0, 0, 0, 0),
   (1, 5, 4, 0, 3),
   (0, 0, 0, 0, 0),
   (0, 0, 0, 0, 0),
   (2, 4, 8, 3, 6),
   (9, 0, 3, 4, 8),
   (0, 0, 0, 0, 0),
   (5, 4, 1, 0, 6),
   (2, 0, 6, 1, 8),
   (0, 0, 0, 0, 0),
   (5, 1, 4, 0, 3),
   (0, 0, 0, 0, 0),
   (2, 6, 0, 1, 4),
   (0, 0, 0, 0, 0),
   (3, 1, 7, 2, 9),
   (3, 0, 9, 4, 7),
   (5, 1, 4, 0, 9),
   (0, 0, 0, 0, 0),
   (6, 0, 2, 1, 7),
   (0, 0, 0, 0, 0),
   (0, 0, 0, 0, 0),
   (6, 2, 0, 1, 4),
   (0, 0, 0, 0, 0),
   (5, 4, 1, 0, 2),
   (7, 1, 3, 2, 8),
   (4, 2, 8, 3, 5),
   (4, 1, 5, 0, 8),
   (6, 2, 0, 1, 5),
   (0, 0, 0, 0, 0),
   (6, 0, 2, 1, 3),
   (0, 0, 0, 0, 0),
   (0, 0, 0, 0, 0),
   (4, 5, 1, 0, 2),
   (0, 0, 0, 0, 0)].getD
    (10 * i.val + j.val) (0, 0, 0, 0, 0)

def Good (I : Finset V) (i j : V) (w : V × V × V × V × V) : Prop :=
  let x := w.1
  let y := w.2.1
  let z := w.2.2.1
  let k := w.2.2.2.1
  let l := w.2.2.2.2
  x ∉ I ∧ y ∉ I ∧ z ∉ I ∧
    adj i x ∧ ¬ adj i y ∧ ¬ adj i z ∧
    adj j y ∧ ¬ adj j x ∧ ¬ adj j z ∧
    x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
    ¬ adj x y ∧ ¬ adj x z ∧ ¬ adj y z ∧
    k ∈ I ∧ l ∈ I ∧ k ≠ l ∧ adj k z ∧ adj l z

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma certificate : ∀ I : Finset V, I.card = 4 →
    (∀ a ∈ I, ∀ b ∈ I, ¬ adj a b) →
    ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Good I i j (witnesses i j) := by
  unfold Good
  decide +kernel

lemma clean_pair_geometry (I : Finset V) (hI : I.card = 4)
    (hInd : ∀ a ∈ I, ∀ b ∈ I, ¬ adj a b)
    {i j : V} (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) :
    ∃ x y z k l : V, x ∉ I ∧ y ∉ I ∧ z ∉ I ∧
      adj i x ∧ ¬ adj i y ∧ ¬ adj i z ∧
      adj j y ∧ ¬ adj j x ∧ ¬ adj j z ∧
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      ¬ adj x y ∧ ¬ adj x z ∧ ¬ adj y z ∧
      k ∈ I ∧ l ∈ I ∧ k ≠ l ∧ adj k z ∧ adj l z := by
  let w := witnesses i j
  exact ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2,
    certificate I hI hInd i hi j hj hij⟩

end I4Geometry

namespace I4Geometry

lemma two_clean_labels_need_three {α : Type*} [DecidableEq α]
    (U : Finset α) (F : V → Finset α) (I : Finset V)
    (hI : I.card = 4) (hInd : ∀ a ∈ I, ∀ b ∈ I, ¬ adj a b)
    (hsub : ∀ x, F x ⊆ U)
    (hne : ∀ z, z ∉ I → ∀ k ∈ I, ∀ l ∈ I, k ≠ l →
      adj k z → adj l z → (F z).Nonempty)
    {i j : V} (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j)
    (hsepi : ∀ x y, x ∉ I → y ∉ I → adj i x → ¬ adj i y →
      ¬ adj x y → ¬ F x ⊆ F y)
    (hsepj : ∀ x y, x ∉ I → y ∉ I → adj j x → ¬ adj j y →
      ¬ adj x y → ¬ F x ⊆ F y) : 3 ≤ U.card := by
  obtain ⟨x, y, z, k, l, hxI, hyI, hzI, hix, hiy, hiz, hjy, hjx, hjz,
    _, _, _, hxy, hxz, hyz, hkI, hlI, hkl, hkz, hlz⟩ := clean_pair_geometry I hI hInd hi hj hij
  exact PEqualNP.Outside.L_meta_2590_aux.I4Codes.two_incomparable_avoiding_nonempty_need_three
    U (F x) (F y) (F z) (hsub x) (hsub y) (hsub z)
    (hne z hzI k hkI l hlI hkl hkz hlz)
    (hsepi x y hxI hyI hix hiy hxy)
    (hsepj y x hyI hxI hjy hjx (fun h => hxy (graph_ok.1 _ _ h)))
    (hsepi x z hxI hzI hix hiz hxz) (hsepj y z hyI hzI hjy hjz hyz)

end I4Geometry

namespace NeighborCover

lemma center_eligible {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hi : J ⊆ ineligSet 10 D) : (0 : V) ∈ eligSet 10 D := by
  rcases sem_elig_cover graph_ok h hc (show adj 0 1 from by decide) with h0 | h1
  · exact h0
  · exact False.elim ((sem_mem_inelig.mp (hi (by decide : (1 : V) ∈ J))) h1)

lemma center_code_positive {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hi : J ⊆ ineligSet 10 D) (b : V → ℕ) (hb : PureBranch 10 D b) :
    1 ≤ (code D b 0).card := by
  obtain ⟨pos, hp⟩ := k4_assigned graph_ok h hc
  obtain ⟨hsub, hcard⟩ := center_three_exits hi hp
  have hW : 3 ≤ (sem_W 10 D (0 : V)).card := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  have count := sem_code_count graph_ok h hc b hb (0 : V)
  change (sem_W 10 D (0 : V)).card + (merges 10 D (carrierT 10 D {0})).card =
    1 + (({0} : Finset V) ∩ eligSet 10 D).card + (code D b 0).card at count
  have hone : (({0} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  omega

lemma neighborhood_budget {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hlen : D.length ≤ 19) (hi : ineligSet 10 D = J)
    (b : V → ℕ) (hb : PureBranch 10 D b) :
    (residualUnits 10 D b).card + Bzero 10 D + 16 = D.length ∧
    1 ≤ (code D b 0).card ∧
    (code D b 0).card ≤ (residualUnits 10 D b).card ∧
    (residualUnits 10 D b).card + Bzero 10 D ≤ 3 ∧ Bzero 10 D ≤ 2 := by
  have hJ : J.card = 3 := by decide +kernel
  have he : (eligSet 10 D).card = 7 := by
    have hs := inelig_card_add 10 D
    rw [hi, hJ] at hs
    omega
  have hres := card_residual h.1 b hb
  have hsur := surplus_identity h
  rw [he] at hres
  rw [totalSurplus_split] at hsur
  have hpositive := center_code_positive h hc (by rw [hi]) b hb
  have hsubset : (code D b 0).card ≤ (residualUnits 10 D b).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  omega

lemma at_least_two_residual_of_one_exact_star {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D) (hi : J ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    {i : V} (hiJ : i ∈ J) {e : ℕ × Bool} (he : e ∈ sem_W 10 D (0 : V))
    (hexact : ∀ a, a ∈ supp 10 D (src D e) ↔ adj i a) :
    2 ≤ (residualUnits 10 D b).card := by
  by_contra hsmall
  have hR : (residualUnits 10 D b).card ≤ 1 := by omega
  have hpositive := center_code_positive h hc hi b hb
  have hnonempty : (code D b 0).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨u, hu⟩ := hnonempty
  obtain ⟨huR, hu0⟩ := Finset.mem_filter.mp hu
  have unique (v) (hv : v ∈ residualUnits 10 D b) : v = u :=
    Finset.card_le_one.mp hR v hv u huR
  have hgeometry : ∀ i ∈ J, adj i 0 ∧ (C.filter (adj i)).card = 2 := by decide +kernel
  have hCgeometry : ∀ c ∈ C, c ≠ (0 : V) ∧ ¬ adj 0 c := by decide +kernel
  have hsub : C.filter (fun c => (code D b c).Nonempty) ⊆ C.filter (adj i) := by
    intro c hcm
    obtain ⟨hcC, v, hv⟩ := Finset.mem_filter.mp hcm
    obtain ⟨hvR, hvc⟩ := Finset.mem_filter.mp hv
    have huc : c ∈ supp 10 D u.1 := by simpa only [unique v hvR] using hvc
    refine Finset.mem_filter.mpr ⟨hcC, ?_⟩
    by_contra hic
    apply one_exact_star_separates h hc b hb (hgeometry i hiJ).1
      (hCgeometry c hcC).1 (hCgeometry c hcC).2 hic
      (center_eligible h hc hi) ⟨u, Finset.mem_filter.mpr ⟨huR, hu0⟩⟩ he hexact
    intro v hvR _
    simpa only [unique v hvR] using huc
  have hthree := three_cycle_vertices_in_residual_support h hc hi b hb
  have hbound := Finset.card_le_card hsub
  rw [(hgeometry i hiJ).2] at hbound
  omega

end NeighborCover

namespace CoStar
open DagTools

lemma sem_neighbor_exclusion_slot
    {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (i c : Fin n) (hci : ¬ G i c)
    (chain : sem_Chain n D i.val (outW n D))
    (N : Finset (Fin n)) (hN : ∀ a ∈ N, G i a) :
    ∃ e : Nat × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
      (∀ x ∈ N, e ∈ sem_W n D x) ∧ c ∉ supp n D (src D e) ∧
      N ⊆ supp n D (src D e) := by
  classical
  have hcN : c ∉ N := fun hc => hci (hN c hc)
  have diff : insert c N \ N = ({c} : Finset (Fin n)) := by
    ext a
    simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨h|h,hno⟩
      · exact h
      · exact False.elim (hno h)
    · rintro rfl
      exact ⟨Or.inl rfl,hcN⟩
  have hzero : val D (sem_ins i (sem_ind (insert c N \ N))) (outW n D) = false := by
    rw [diff]
    apply Bool.eq_false_iff.mpr
    intro hv
    rcases sem_ins_ind_edge hG ((hC _).mp hv) with ⟨a,ha,hia⟩ | ⟨a,ha,b,hb,hab⟩
    · have eq := Finset.mem_singleton.mp ha
      exact hci (eq ▸ hia)
    · have ea := Finset.mem_singleton.mp ha
      have eb := Finset.mem_singleton.mp hb
      subst a
      subst b
      exact hG.2.1 c hab
  have hone (a : Fin n) (ha : a ∈ N) :
      val D (sem_ins i (sem_ind {a})) (outW n D) = true :=
    (hC _).mpr ⟨i,a,hN a ha,sem_ins_self i _,by simp [sem_ins,sem_ind]⟩
  have hz (a : Fin n) (_ : a ∈ N) : val D (sem_ind {a}) (outW n D) = false := by
    apply Bool.eq_false_iff.mpr
    intro hv
    rw [sem_ind_single] at hv
    exact sem_single_no_edge hG a ((hC _).mp hv)
  obtain ⟨g,s,hg,ht,_,other,hs⟩ := sem_factor hS i (outW n D) chain
    (insert c N) N (Finset.subset_insert c N) hzero hone hz
  have has (x : Fin n) (hx : x ∈ N) : x ∈ supp n D (src D (g,s)) :=
    (Finset.mem_inter.mp (hs.symm ▸ hx)).1
  refine ⟨(g,s),hg,ht,fun x hx => ?_,?_,has⟩
  · apply sem_mem_W.mpr
    refine ⟨hg,has x hx,fun hxout => ?_⟩
    have ho := sem_supp_and_sub hS hg ht (!s) hxout
    have hp := sem_dom_pure hG hS hC i _ (sem_chain_dom hS other) ho
    have eq := Finset.mem_singleton.mp hp
    exact hG.2.1 i (eq ▸ hN x hx)
  · intro hcs
    have hc : c ∈ N := hs ▸ Finset.mem_inter.mpr ⟨hcs,Finset.mem_insert_self c N⟩
    exact hcN hc

lemma sem_neighbor_exclusion_slot_of_bzero
    {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag} [DecidableRel G]
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (zero : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D)
    (c : Fin n) (hci : ¬ G i c) :
    ∃ e : Nat × Bool, (∀ x, G i x → e ∈ sem_W n D x) ∧
      c ∉ supp n D (src D e) ∧ (∀ a, G i a → a ∈ supp n D (src D e)) := by
  classical
  let N := Finset.univ.filter (G i)
  have chain := sem_noempty_chain_out hG h hC zero hi
  obtain ⟨e,_,_,hW,hc,hs⟩ := sem_neighbor_exclusion_slot hG h.1 hC i c hci
    chain N
    (fun a ha => (Finset.mem_filter.mp ha).2)
  exact ⟨e,fun x hx => hW x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩),
    hc,fun a ha => hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩)⟩

end CoStar

lemma one_co_star_separates {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    {i x c : V} (hi : i ∈ ineligSet 10 D)
    (hix : adj i x) (hcx : c ≠ x) (hxc : ¬ adj x c) (hic : ¬ adj i c)
    (hx : x ∈ eligSet 10 D) (hnonempty : (NeighborCover.code D b x).Nonempty) :
    ¬ (∀ u ∈ residualUnits 10 D b, x ∈ supp 10 D u.1 → c ∈ supp 10 D u.1) := by
  obtain ⟨e, he, hce, hsource⟩ :=
    CoStar.sem_neighbor_exclusion_slot_of_bzero graph_ok h hc hz hi c hic
  obtain ⟨hA, hcA, ⟨a, haA, hia⟩, hxA⟩ :=
    one_star_exposure_geometry i x c hix hcx hxc hic
  exact code_separation_of_exit_and_exposure graph_ok h hc b hb hcx hx hnonempty
    (he x hix) hce (oneStarExposure i x c) hA hcA hxA ⟨a, haA, hsource a hia⟩

namespace NeighborCover

lemma center_code_separates {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) {c : V} (hcC : c ∈ C) :
    ¬ (code D b 0 ⊆ code D b c) := by
  have hgeometry : ∀ c ∈ C, c ≠ (0 : V) ∧ ¬ adj 0 c ∧
      ∃ i ∈ J, adj i 0 ∧ ¬ adj i c := by decide +kernel
  obtain ⟨hcn, hnc, i, hiJ, hi0, hic⟩ := hgeometry c hcC
  have hpositive := center_code_positive h hc hi b hb
  have hsep := one_co_star_separates h hc hz b hb (hi hiJ) hi0 hcn hnc hic
    (center_eligible h hc hi) (Finset.card_pos.mp (by omega))
  intro hsub
  apply hsep
  intro u hu hu0
  exact (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hu, hu0⟩))).2

lemma at_least_two_residual_of_bzero {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0)
    (hi : J ⊆ ineligSet 10 D) (b : V → ℕ) (hb : PureBranch 10 D b) :
    2 ≤ (residualUnits 10 D b).card := by
  by_contra hsmall
  have hR : (residualUnits 10 D b).card ≤ 1 := by omega
  have hthree := three_cycle_vertices_in_residual_support h hc hi b hb
  obtain ⟨c, hcm⟩ := Finset.nonempty_def.mp (Finset.card_pos.mp (by omega :
    0 < (C.filter (fun c => (code D b c).Nonempty)).card))
  obtain ⟨hcC, u, hu⟩ := Finset.mem_filter.mp hcm
  obtain ⟨huR, huc⟩ := Finset.mem_filter.mp hu
  apply center_code_separates h hc hz hi b hb hcC
  intro v hv
  obtain ⟨hvR, hv0⟩ := Finset.mem_filter.mp hv
  have hveq : v = u := Finset.card_le_one.mp hR v hvR u huR
  simpa only [hveq] using hu

end NeighborCover

namespace NeighborCover

lemma three_center_exits_data {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : J ⊆ ineligSet 10 D)
    (hW : (sem_W 10 D (0 : V)).card ≤ 3) :
    ∃ pos : V → ℕ × Bool, k4_Pos 10 adj D pos ∧ sem_W 10 D (0 : V) = J.image pos := by
  obtain ⟨pos, hp⟩ := k4_assigned graph_ok h hc
  obtain ⟨hsub, hcard⟩ := center_three_exits hi hp
  refine ⟨pos, hp, ?_⟩
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

lemma three_center_exits_stars_exact {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    (hW : (sem_W 10 D (0 : V)).card ≤ 3) :
    ∃ pos : V → ℕ × Bool, k4_Pos 10 adj D pos ∧ sem_W 10 D (0 : V) = J.image pos ∧
      ∀ i ∈ J, ∀ a, a ∈ supp 10 D (src D (pos i)) ↔ adj i a := by
  obtain ⟨pos, hp, he⟩ := three_center_exits_data h hc hi hW
  refine ⟨pos, hp, he, ?_⟩
  intro i hiJ a
  have hchain := sem_noempty_chain_out graph_ok h hc hz (hi hiJ)
  obtain ⟨g, s, hg, ht, hch, hmask⟩ := sem_exact_nbhd graph_ok h.1 hc {a}
    (by simpa only [Finset.mem_singleton, forall_eq] using graph_ok.2.1 a) hchain
  have heq := center_chain_assigned h hc hz hi hp he hiJ hg ht hch
  simpa only [heq] using hmask a (Finset.mem_singleton_self a)

lemma three_center_exits_stars_below_target {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    (hW : (sem_W 10 D (0 : V)).card ≤ 3) :
    ∃ pos : V → ℕ × Bool, k4_Pos 10 adj D pos ∧ sem_W 10 D (0 : V) = J.image pos ∧
      ∀ i ∈ J, ∀ x : V → Bool, val D x (10 + (pos i).1) = true → sem_Edge adj x := by
  obtain ⟨pos, hp, he⟩ := three_center_exits_data h hc hi hW
  exact ⟨pos, hp, he, fun i hiJ => assigned_below_target h hc hz hi hp he hiJ⟩

lemma three_center_exits_false_on_nonedge {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    (hW : (sem_W 10 D (0 : V)).card ≤ 3) (v : V) (hv : ¬ adj 0 v) :
    ∀ e ∈ sem_W 10 D (0 : V), val D (sem_two 0 v) (10 + e.1) = false := by
  have hind : ¬ sem_Edge adj (sem_two (0 : V) v) := by
    rintro ⟨a, c, hac, ha, hc⟩
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at ha hc
    rcases ha with ha | ha <;> rcases hc with hc | hc <;> rw [ha, hc] at hac
    · exact graph_ok.2.1 _ hac
    · exact hv hac
    · exact hv (graph_ok.1 _ _ hac)
    · exact graph_ok.2.1 _ hac
  obtain ⟨pos, hp, he, hbelow⟩ := three_center_exits_stars_below_target h hc hz hi hW
  intro e heW
  rw [he] at heW
  obtain ⟨i, hiJ, rfl⟩ := Finset.mem_image.mp heW
  by_contra bad
  have htrue : val D (sem_two 0 v) (10 + (pos i).1) = true := by
    rwa [Bool.not_eq_false] at bad
  exact hind (hbelow i hiJ (sem_two 0 v) htrue)

lemma three_center_exits_preserve_labels {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    (hW : (sem_W 10 D (0 : V)).card ≤ 3) (v : V) (hv : ¬ adj 0 v)
    (w : ℕ) (hw : (0 : V) ∉ supp 10 D w) :
    val D (sem_two 0 v) w = val D (single v) w :=
  val_two_eq_single_of_false_exits h.1 0 v
    (three_center_exits_false_on_nonedge h hc hz hi hW v hv) w hw

lemma three_center_exits_restriction_support {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    (hW : (sem_W 10 D (0 : V)).card ≤ 3) (v : V) (hv : ¬ adj 0 v) (w : ℕ) :
    val D (sem_two 0 v) w = true ↔ (0 : V) ∈ supp 10 D w ∨ v ∈ supp 10 D w :=
  two_support_of_false_exits h.1 0 v
    (three_center_exits_false_on_nonedge h hc hz hi hW v hv) w

lemma three_center_exits_C_labels {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    (hW : (sem_W 10 D (0 : V)).card ≤ 3) (w : ℕ) :
    C.filter (fun v => val D (sem_two 0 v) w = true) =
      if (0 : V) ∈ supp 10 D w then C else supp 10 D w ∩ C := by
  have hgeom : ∀ v ∈ C, ¬ adj 0 v := by decide +kernel
  ext v
  by_cases hv : v ∈ C
  · simp only [Finset.mem_filter, hv, true_and]
    rw [three_center_exits_restriction_support h hc hz hi hW v (hgeom v hv) w]
    by_cases hw : (0 : V) ∈ supp 10 D w <;> simp [hw, hv]
  · by_cases hw : (0 : V) ∈ supp 10 D w <;> simp [hv, hw]

-- These results allow AND gates whose output singleton support contains 0.
-- No claim that the center carrier has zero merges is used or established.
end NeighborCover

namespace NeighborCover

open DagTools

lemma cycle_center_geometry :
    (∀ x ∈ C, x ≠ 0 ∧ x ∉ J ∧ ¬ adj 0 x ∧ ¬ adj x 0 ∧ ∃ z ∈ C, adj x z) ∧
    (∀ x ∈ C, ∀ y ∈ C, y ≠ x → ∃ z ∈ C, adj x z ∧ ¬ adj y z) ∧
    (∀ v : V, v = 0 ∨ v ∈ J ∨ v ∈ C) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

lemma code_subset_center_private_exit {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hI : ineligSet 10 D = J)
    (b : V → ℕ) (hb : PureBranch 10 D b) {x : V} (hx : x ∈ C)
    (hinc : code D b x ⊆ code D b 0) :
    ∃ e, e ∈ sem_W 10 D x ∧ supp 10 D (src D e) = {x} ∧
      ∀ f ∈ sem_W 10 D x, (0 : V) ∉ supp 10 D (src D f) → f = e := by
  classical
  have hi : J ⊆ ineligSet 10 D := by rw [hI]
  obtain ⟨hx0, hxJ, _, _, z, hz, hxz⟩ := cycle_center_geometry.1 x hx
  have hxelig : x ∈ eligSet 10 D := by
    by_contra bad
    have hm : x ∈ ineligSet 10 D := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, bad⟩
    rw [hI] at hm
    exact hxJ hm
  obtain ⟨hoi, hox, ho0, _, _⟩ := geometry x hx
  obtain ⟨q, _, _, _, _, hn, _, _⟩ := sem_inelig_consumer graph_ok h hc (hi hoi)
  have hres : ∀ u ∈ residualUnits 10 D b, x ∈ supp 10 D u.1 → (0 : V) ∈ supp 10 D u.1 := by
    intro u hu hxu
    exact (Finset.mem_filter.mp (hinc (Finset.mem_filter.mpr ⟨hu, hxu⟩))).2
  obtain ⟨exception, hrest⟩ := ri_gen graph_ok h hc b hb hx0 hxelig hres ⟨hn x hox, hn 0 ho0⟩
  have hz0 := (cycle_center_geometry.1 z hz).2.2.2.1
  obtain ⟨e, he, he0, _⟩ := sem_cover_free graph_ok h.1 hc
    (x := x) (a := 0) (b := 0) (y := z) (graph_ok.2.1 0) hxz hz0 hz0
  have hexc : e = exception := by
    by_contra bad
    exact he0 (hrest e he bad)
  have huniq : ∀ f ∈ sem_W 10 D x, (0 : V) ∉ supp 10 D (src D f) → f = e := by
    intro f hf hf0
    have hfe : f = exception := by
      by_contra bad
      exact hf0 (hrest f hf bad)
    exact hfe.trans hexc.symm
  have hxe := (sem_mem_W.mp he).2.1
  refine ⟨e, he, ?_, huniq⟩
  refine Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr hxe)
  intro c hce
  rw [Finset.mem_singleton]
  by_contra hcx
  rcases cycle_center_geometry.2.2 c with hc0 | hcJ | hcC
  · subst c
    exact he0 hce
  · have hpure := sem_inelig_pure graph_ok h.1 hc (hi hcJ) hce
    rw [hpure, Finset.mem_singleton] at hxe
    exact hcx hxe.symm
  · obtain ⟨w, hw, hxw, hcw⟩ := cycle_center_geometry.2.1 x hx c hcC hcx
    have h0c := (cycle_center_geometry.1 c hcC).2.2.1
    have hw0 := (cycle_center_geometry.1 w hw).2.2.2.1
    obtain ⟨f, hf, hf0, hfc⟩ := sem_cover_free graph_ok h.1 hc
      (x := x) (a := 0) (b := c) (y := w) h0c hxw hw0
      (fun h => hcw (graph_ok.1 _ _ h))
    have hfe := huniq f hf hf0
    exact hfc (hfe ▸ hce)

end NeighborCover

namespace NeighborCover

def extraCenterHit (i c : V) : Finset V :=
  if i = 1 then
    if c = 3 ∨ c = 7 then {1,3,7} else {1,8,9}
  else if i = 4 then
    if c = 2 ∨ c = 8 then {4,2,8} else {4,6,7}
  else
    if c = 2 ∨ c = 9 then {5,2,9} else {5,3,6}

lemma extra_center_hit_geometry : ∀ i ∈ J, ∀ c ∈ C, ¬ adj i c →
    (∀ a ∈ extraCenterHit i c, ∀ d ∈ extraCenterHit i c, ¬ adj a d) ∧
    i ∈ extraCenterHit i c ∧ c ∈ extraCenterHit i c ∧
    ∀ j ∈ J, j ≠ i → ∃ a ∈ extraCenterHit i c, adj j a := by
  decide +kernel

lemma three_center_exits_stars_exact_unrestricted {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : J ⊆ ineligSet 10 D)
    (hW : (sem_W 10 D (0 : V)).card ≤ 3) :
    ∃ pos : V → ℕ × Bool, k4_Pos 10 adj D pos ∧ sem_W 10 D (0 : V) = J.image pos ∧
      ∀ i ∈ J, ∀ a, a ∈ supp 10 D (src D (pos i)) ↔ adj i a := by
  obtain ⟨pos, hp, he⟩ := three_center_exits_data h hc hi hW
  refine ⟨pos, hp, he, ?_⟩
  intro i hiJ c
  constructor
  · intro hcs
    by_contra hic
    have hgeom : ∀ i ∈ J, adj i 0 ∧ i ≠ 0 ∧
        ∀ c, ¬ adj i c → c ∈ J ∨ c ∈ C := by decide +kernel
    have hi0 := (hgeom i hiJ).1
    have h0s := (hp.1 i (hi hiJ)).2.2.1 0 hi0
    have hcC : c ∈ C := by
      rcases (hgeom i hiJ).2.2 c hic with hcJ | hcC
      · have hs := sem_inelig_pure graph_ok h.1 hc (hi hcJ) hcs
        rw [hs, Finset.mem_singleton] at h0s
        exact False.elim ((hgeom c hcJ).2.1 h0s.symm)
      · exact hcC
    obtain ⟨hA, hiA, hcA, hother⟩ := extra_center_hit_geometry i hiJ c hcC hic
    obtain ⟨g, s, hg, ht, h0g, h0out, hdis⟩ :=
      sem_exposure graph_ok h.1 hc (extraCenterHit i c) hA (0 : V)
        ⟨i, hiA, graph_ok.1 _ _ hi0⟩
    have heW : (g,s) ∈ sem_W 10 D (0 : V) := sem_mem_W.mpr ⟨hg,h0g,h0out⟩
    rw [he] at heW
    obtain ⟨j, hjJ, heq⟩ := Finset.mem_image.mp heW
    by_cases hji : j = i
    · subst j
      rw [heq] at hcs
      exact Finset.disjoint_left.mp hdis hcs hcA
    · obtain ⟨a, haA, hja⟩ := hother j hjJ hji
      have has := (hp.1 j (hi hjJ)).2.2.1 a hja
      rw [heq] at has
      exact Finset.disjoint_left.mp hdis has haA
  · exact (hp.1 i (hi hiJ)).2.2.1 c

lemma three_center_exits_residual_ge_two {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : J ⊆ ineligSet 10 D)
    (hW : (sem_W 10 D (0 : V)).card ≤ 3)
    (b : V → ℕ) (hb : PureBranch 10 D b) :
    2 ≤ (residualUnits 10 D b).card := by
  obtain ⟨pos, hp, he, hexact⟩ := three_center_exits_stars_exact_unrestricted h hc hi hW
  have h1J : (1 : V) ∈ J := by decide
  have he1 : pos 1 ∈ sem_W 10 D (0 : V) := by
    rw [he]
    exact Finset.mem_image.mpr ⟨1,h1J,rfl⟩
  exact at_least_two_residual_of_one_exact_star h hc hi b hb h1J he1 (hexact 1 h1J)

lemma residual_at_least_two_unrestricted {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hi : J ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) :
    2 ≤ (residualUnits 10 D b).card := by
  by_contra hsmall
  have hR : (residualUnits 10 D b).card ≤ 1 := by omega
  have hcode : (code D b 0).card ≤ 1 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans hR
  obtain ⟨pos, hp, he, hm, hcard⟩ := one_center_code_data h hc hi b hb hcode
  have hW : (sem_W 10 D (0 : V)).card ≤ 3 := by
    rw [he]
    exact (Finset.card_image_le).trans (by decide)
  have ht := three_center_exits_residual_ge_two h hc hi hW b hb
  omega

lemma neighborhood_bzero_le_one {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hlen : D.length ≤ 19) (hi : ineligSet 10 D = J)
    (b : V → ℕ) (hb : PureBranch 10 D b) : Bzero 10 D ≤ 1 := by
  have budget := neighborhood_budget h hc hlen hi b hb
  by_contra hnot
  have hR : (residualUnits 10 D b).card ≤ 1 := by omega
  have hcenter := sem_code_count graph_ok h hc b hb (0 : V)
  change (sem_W 10 D (0 : V)).card + (merges 10 D (carrierT 10 D {0})).card =
    1 + (({0} : Finset V) ∩ eligSet 10 D).card + (code D b 0).card at hcenter
  have hbase : (({0} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have hW : (sem_W 10 D (0 : V)).card ≤ 3 := by omega
  have ht := three_center_exits_residual_ge_two h hc (by rw [hi]) hW b hb
  omega

end NeighborCover

lemma val_two_eq_single_of_exit_controls {n : ℕ} {D : Dag}
    (hS : Strict n D) (z v : Fin n)
    (hcontrol : ∀ e ∈ sem_W n D z,
      z ∉ supp n D (src D (e.1, !e.2)) ∧ v ∉ supp n D (src D (e.1, !e.2))) :
    ∀ w, z ∉ supp n D w → val D (sem_two z v) w = val D (single v) w := by
  have hfalse (w : ℕ) (hy : val D (sem_two z v) w = false) :
      val D (single v) w = false := by
    by_contra hx
    have hxtrue : val D (single v) w = true := by rwa [Bool.not_eq_false] at hx
    have hytrue := val_mono hS (single v) (sem_two z v)
      (fun i hi => by simp only [sem_two, Bool.or_eq_true]; exact Or.inr hi) w hxtrue
    rw [hy] at hytrue
    contradiction
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · have hne : (⟨w, hn⟩ : Fin n) ≠ z := by
        intro heq
        apply hw
        rw [← heq]
        exact (supp_input D ⟨w, hn⟩).symm ▸ Finset.mem_singleton_self _
      rw [val_input D (sem_two z v) w hn, val_input D (single v) w hn]
      simp [single, sem_two, hne]
    · by_cases hbound : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, _⟩ := hS j hj
        have hexit_zero (s : Bool) (hs : z ∈ supp n D (src D (j, s))) :
            val D (sem_two z v) (n + j) = val D (single v) (n + j) := by
          have he : (j, s) ∈ sem_W n D z := sem_mem_W.mpr ⟨hj, hs, hw⟩
          obtain ⟨hcz, hcv⟩ := hcontrol (j,s) he
          have hcfalse : val D (single v) (src D (j,!s)) = false := by
            apply Bool.eq_false_iff.mpr
            intro hc
            exact hcv (by simpa only [mem_supp] using hc)
          have hyc : val D (sem_two z v) (src D (j,!s)) = false :=
            (ih _ (sem_src_lt hS hj (!s)) hcz).trans hcfalse
          have hy : val D (sem_two z v) (n+j) = false := by
            rw [sem_val_gate_src hS (sem_two z v) hj (!s), sem_W_and hS he,
              gop_true, hyc]
            rfl
          exact hy.trans (hfalse (n+j) hy).symm
        by_cases hzA : z ∈ supp n D (opA D j)
        · exact hexit_zero false (by simpa only [sb_src_false] using hzA)
        · by_cases hzB : z ∈ supp n D (opB D j)
          · exact hexit_zero true (by simpa only [sb_src_true] using hzB)
          · rw [val_gate hS (sem_two z v) j hj, val_gate hS (single v) j hj,
              ih _ ha hzA, ih _ hb hzB]
      · rw [val_ge D (sem_two z v) w (by omega), val_ge D (single v) w (by omega)]

namespace NeighborCover

lemma three_center_exits_preserve_labels_unrestricted {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D) (hi : J ⊆ ineligSet 10 D)
    (hW : (sem_W 10 D (0 : V)).card ≤ 3) (v : V) (hv : v ∈ C)
    (w : ℕ) (hw : (0 : V) ∉ supp 10 D w) :
    val D (sem_two 0 v) w = val D (single v) w := by
  obtain ⟨pos, hp, he⟩ := three_center_exits_data h hc hi hW
  have hgeom : ∀ i ∈ J, i ≠ (0 : V) ∧ ∀ v ∈ C, v ≠ i := by decide +kernel
  apply val_two_eq_single_of_exit_controls h.1 0 v ?_ w hw
  intro e heW
  rw [he] at heW
  obtain ⟨i, hiJ, rfl⟩ := Finset.mem_image.mp heW
  rw [(hp.1 i (hi hiJ)).2.2.2]
  simp only [Finset.mem_singleton]
  exact ⟨Ne.symm (hgeom i hiJ).1, (hgeom i hiJ).2 v hv⟩

lemma three_center_exits_C_labels_unrestricted {D : Dag}
    (h : StrictLive 10 D) (hc : sem_Comp 10 adj D) (hi : J ⊆ ineligSet 10 D)
    (hW : (sem_W 10 D (0 : V)).card ≤ 3) (w : ℕ) :
    C.filter (fun v => val D (sem_two 0 v) w = true) =
      if (0 : V) ∈ supp 10 D w then C else supp 10 D w ∩ C := by
  ext v
  by_cases hv : v ∈ C
  · simp only [Finset.mem_filter, hv, true_and]
    by_cases hw : (0 : V) ∈ supp 10 D w
    · have hval := sem_val_of_supp h.1 hw (by simp [sem_two] : sem_two (0 : V) v 0 = true)
      simp [hw, hv, hval]
    · rw [three_center_exits_preserve_labels_unrestricted h hc hi hW v hv w hw]
      simp only [mem_supp, hw, ↓reduceIte, Finset.mem_inter, hv, and_true]
  · by_cases hw : (0 : V) ∈ supp 10 D w <;> simp [hv, hw]

end NeighborCover

namespace NeighborCover

open DagTools

def avoidCarrier (n : ℕ) (D : Dag) (z x y : Fin n) : Finset ℕ :=
  (inner n D).filter (fun w => z ∈ supp n D w ∧ x ∉ supp n D w ∧ y ∉ supp n D w)

lemma first_joint_acquisition {n : ℕ} {D : Dag} (hS : Strict n D)
    {z x y : Fin n} (hM : merges n D (carrierT n D {z}) = ∅) (hxz : x ≠ z) :
    ∀ w, z ∈ supp n D w → x ∈ supp n D w → y ∉ supp n D w →
      ∃ e ∈ exitArcs n D (avoidCarrier n D z x y),
        z ∈ supp n D (n + e.1) ∧ x ∈ supp n D (n + e.1) ∧ y ∉ supp n D (n + e.1) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hzw hxw hyw
    by_cases hwn : w < n
    · have hs : supp n D w = {⟨w, hwn⟩} := supp_input D ⟨w, hwn⟩
      rw [hs, Finset.mem_singleton] at hzw hxw
      exact False.elim (hxz (hxw.trans hzw.symm))
    · by_cases hwlen : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        have hor := (sem_zm_gate hS hM hj hzw).1
        have hparents : z ∈ supp n D (opA D j) ∨ z ∈ supp n D (opB D j) := by
          rwa [sem_supp_or hS hj hor, Finset.mem_union] at hzw
        have hex : ∃ s : Bool, z ∈ supp n D (src D (j, s)) := by
          rcases hparents with ha | hb
          · exact ⟨false, by simpa only [sb_src_false] using ha⟩
          · exact ⟨true, by simpa only [sb_src_true] using hb⟩
        obtain ⟨s, hzs⟩ := hex
        have hless := sem_src_lt hS hj s
        have hys : y ∉ supp n D (src D (j, s)) := by
          intro hys
          apply hyw
          rw [sem_supp_or hS hj hor]
          cases s
          · exact Finset.mem_union_left _ (by simpa only [sb_src_false] using hys)
          · exact Finset.mem_union_right _ (by simpa only [sb_src_true] using hys)
        by_cases hxs : x ∈ supp n D (src D (j, s))
        · exact ih _ hless hzs hxs hys
        · refine ⟨(j, s), ?_, hzw, hxw, hyw⟩
          rw [exitArcs, Finset.mem_filter]
          refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, Finset.mem_univ s⟩, ?_, ?_⟩
          · apply Finset.mem_filter.mpr
            refine ⟨sb_mem_inner.mpr ?_, hzs, hxs, hys⟩
            omega
          · intro hout
            exact (Finset.mem_filter.mp hout).2.2.1 hxw
      · rw [supp_ge D w (by omega)] at hzw
        exact False.elim (Finset.notMem_empty _ hzw)

end NeighborCover

namespace NeighborCover

open DagTools

lemma avoidCarrier_comm {n : ℕ} (D : Dag) (z x y : Fin n) :
    avoidCarrier n D z x y = avoidCarrier n D z y x := by
  ext w
  simp only [avoidCarrier, Finset.mem_filter]
  tauto

lemma avoidCarrier_surplus_le_one {n : ℕ} {D : Dag}
    (b : Fin n → ℕ) (hb : PureBranch n D b) (z x y : Fin n)
    (hcover : ∀ u ∈ residualUnits n D b, z ∈ supp n D u.1 →
      x ∈ supp n D u.1 ∨ y ∈ supp n D u.1) :
    surplusOn D (avoidCarrier n D z x y) ≤ 1 := by
  classical
  unfold avoidCarrier
  rw [← sb_card_units_filter]
  have hsub : (units n D).filter (fun u => z ∈ supp n D u.1 ∧
      x ∉ supp n D u.1 ∧ y ∉ supp n D u.1) ⊆ {(⟨b z, 0⟩ : Σ _ : ℕ, ℕ)} := by
    intro u hu
    obtain ⟨huunit, hzu, hxu, hyu⟩ := Finset.mem_filter.mp hu
    by_cases hr : u ∈ reservedUnits n D b
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
      have hzv : z = v := by rwa [(hb v hv).2, Finset.mem_singleton] at hzu
      subst v
      exact Finset.mem_singleton_self _
    · have hup : u ∈ unitsPlus n D := Finset.mem_filter.mpr ⟨huunit, ⟨z, hzu⟩⟩
      have hur : u ∈ residualUnits n D b := Finset.mem_sdiff.mpr ⟨hup, hr⟩
      exact False.elim ((hcover u hur hzu).elim hxu hyu)
  exact (Finset.card_le_card hsub).trans (by simp)

lemma avoidCarrier_sources_le_one {n : ℕ} (D : Dag) (z x y : Fin n) :
    (sources n (avoidCarrier n D z x y)).card ≤ 1 := by
  have hsub : sources n (avoidCarrier n D z x y) ⊆ {z.val} := by
    intro w hw
    obtain ⟨hwK, hwn⟩ := Finset.mem_filter.mp hw
    have hzw := (Finset.mem_filter.mp hwK).2.1
    have hs : supp n D w = {⟨w, hwn⟩} := supp_input D ⟨w, hwn⟩
    rw [hs, Finset.mem_singleton] at hzw
    exact Finset.mem_singleton.mpr (congrArg Fin.val hzw).symm
  exact (Finset.card_le_card hsub).trans (by simp)

lemma avoidCarrier_exits_le_two {n : ℕ} {D : Dag} (h : StrictLive n D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) (z x y : Fin n)
    (hM : merges n D (carrierT n D {z}) = ∅)
    (hcover : ∀ u ∈ residualUnits n D b, z ∈ supp n D u.1 →
      x ∈ supp n D u.1 ∨ y ∈ supp n D u.1) :
    (exitArcs n D (avoidCarrier n D z x y)).card ≤ 2 := by
  have hpred : ∀ j, j < D.length → n + j ∈ avoidCarrier n D z x y →
      opA D j ∈ avoidCarrier n D z x y ∨ opB D j ∈ avoidCarrier n D z x y := by
    intro j hj hw
    obtain ⟨_, hz, hx, hy⟩ := Finset.mem_filter.mp hw
    have hor := (sem_zm_gate h.1 hM hj hz).1
    have hsubA : supp n D (opA D j) ⊆ supp n D (n + j) := by
      rw [sem_supp_or h.1 hj hor]
      exact Finset.subset_union_left
    have hsubB : supp n D (opB D j) ⊆ supp n D (n + j) := by
      rw [sem_supp_or h.1 hj hor]
      exact Finset.subset_union_right
    rw [sem_supp_or h.1 hj hor, Finset.mem_union] at hz
    obtain ⟨ha, hb, _⟩ := h.1 j hj
    rcases hz with hzA | hzB
    · exact Or.inl (Finset.mem_filter.mpr ⟨sb_mem_inner.mpr (by omega),
        hzA, fun hxA => hx (hsubA hxA), fun hyA => hy (hsubA hyA)⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨sb_mem_inner.mpr (by omega),
        hzB, fun hxB => hx (hsubB hxB), fun hyB => hy (hsubB hyB)⟩)
  have hflow := carrier_flow h (avoidCarrier n D z x y) (Finset.filter_subset _ _) hpred
  have hs := avoidCarrier_sources_le_one D z x y
  have hu := avoidCarrier_surplus_le_one b hb z x y hcover
  omega

lemma center_exits_hit_two_codes {n : ℕ} {D : Dag} (h : StrictLive n D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {z x y : Fin n}
    (hM : merges n D (carrierT n D {z}) = ∅) (hxz : x ≠ z) (hyz : y ≠ z)
    (hcover : ∀ u ∈ residualUnits n D b, z ∈ supp n D u.1 →
      x ∈ supp n D u.1 ∨ y ∈ supp n D u.1)
    {wx wy : ℕ} (hzx : z ∈ supp n D wx) (hxx : x ∈ supp n D wx) (hyx : y ∉ supp n D wx)
    (hzy : z ∈ supp n D wy) (hyy : y ∈ supp n D wy) (hxy : x ∉ supp n D wy) :
    ∀ e ∈ sem_W n D z, x ∈ supp n D (src D e) ∨ y ∈ supp n D (src D e) := by
  obtain ⟨ex, hex, hzxout, hxxout, hyxout⟩ := first_joint_acquisition h.1 hM hxz wx hzx hxx hyx
  obtain ⟨ey, hey, hzyout, hyyout, hxyout⟩ := first_joint_acquisition h.1 hM hyz wy hzy hyy hxy
  rw [← avoidCarrier_comm D z x y] at hey
  have hne : ex ≠ ey := by
    intro heq
    exact hxyout (heq ▸ hxxout)
  intro e he
  by_contra bad
  have hxsrc : x ∉ supp n D (src D e) := fun hx => bad (Or.inl hx)
  have hysrc : y ∉ supp n D (src D e) := fun hy => bad (Or.inr hy)
  obtain ⟨hj, hzsrc, hzout⟩ := sem_mem_W.mp he
  have heK : e ∈ exitArcs n D (avoidCarrier n D z x y) := by
    rw [exitArcs, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, Finset.mem_univ e.2⟩, ?_, ?_⟩
    · have hlt := sem_src_lt h.1 hj e.2
      apply Finset.mem_filter.mpr
      exact ⟨sb_mem_inner.mpr (by simpa only [Prod.mk.eta] using (show src D (e.1, e.2) + 1 < n + D.length by omega)),
        hzsrc, hxsrc, hysrc⟩
    · intro hout
      exact hzout (Finset.mem_filter.mp hout).2.1
  have hexne : e ≠ ex := by intro heq; exact hzout (heq.symm ▸ hzxout)
  have heyne : e ≠ ey := by intro heq; exact hzout (heq.symm ▸ hzyout)
  have hthree : 2 < (exitArcs n D (avoidCarrier n D z x y)).card :=
    Finset.two_lt_card.mpr ⟨e, heK, ex, hex, ey, hey, hexne, heyne, hne⟩
  have hbound := avoidCarrier_exits_le_two h b hb z x y hM hcover
  omega

lemma two_code_cover_no_center_merge_impossible {n : ℕ} {G : Fin n → Fin n → Prop}
    {D : Dag} (hG : sem_Gr G) (h : StrictLive n D) (hc : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {z x y : Fin n}
    (hM : merges n D (carrierT n D {z}) = ∅) (hxz : x ≠ z) (hyz : y ≠ z)
    (hcover : ∀ u ∈ residualUnits n D b, z ∈ supp n D u.1 →
      x ∈ supp n D u.1 ∨ y ∈ supp n D u.1)
    {wx wy : ℕ} (hzx : z ∈ supp n D wx) (hxx : x ∈ supp n D wx) (hyx : y ∉ supp n D wx)
    (hzy : z ∈ supp n D wy) (hyy : y ∈ supp n D wy) (hxy : x ∉ supp n D wy)
    (A : Finset (Fin n)) (hA : ∀ a ∈ A, ∀ c ∈ A, ¬ G a c)
    (hxA : x ∈ A) (hyA : y ∈ A) (hzA : ∃ a ∈ A, G z a) : False := by
  obtain ⟨j, s, hj, _, hzs, hzout, hdis⟩ := sem_exposure hG h.1 hc A hA z hzA
  have he : (j, s) ∈ sem_W n D z := sem_mem_W.mpr ⟨hj, hzs, hzout⟩
  rcases center_exits_hit_two_codes h b hb hM hxz hyz hcover hzx hxx hyx hzy hyy hxy (j, s) he with hx | hy
  · exact Finset.disjoint_left.mp hdis hx hxA
  · exact Finset.disjoint_left.mp hdis hy hyA

lemma center_code_not_two_covered {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (b : V → ℕ) (hb : PureBranch 10 D b)
    (hM : merges 10 D (carrierT 10 D {(0 : V)}) = ∅) (x y : V)
    (hnotx : ¬ code D b 0 ⊆ code D b x) (hnoty : ¬ code D b 0 ⊆ code D b y)
    (A : Finset V) (hA : ∀ a ∈ A, ∀ c ∈ A, ¬ adj a c)
    (hxA : x ∈ A) (hyA : y ∈ A) (h0A : ∃ a ∈ A, adj 0 a) :
    ¬ code D b 0 ⊆ code D b x ∪ code D b y := by
  intro hcover
  obtain ⟨u, hu0, huy⟩ := Finset.not_subset.mp hnoty
  obtain ⟨v, hv0, hvx⟩ := Finset.not_subset.mp hnotx
  have hux : u ∈ code D b x := (Finset.mem_union.mp (hcover hu0)).resolve_right huy
  have hvy : v ∈ code D b y := (Finset.mem_union.mp (hcover hv0)).resolve_left hvx
  obtain ⟨huR, hu0s⟩ := Finset.mem_filter.mp hu0
  obtain ⟨hvR, hv0s⟩ := Finset.mem_filter.mp hv0
  have hxus := (Finset.mem_filter.mp hux).2
  have hyvs := (Finset.mem_filter.mp hvy).2
  have hyus : y ∉ supp 10 D u.1 := fun hy => huy (Finset.mem_filter.mpr ⟨huR, hy⟩)
  have hxvs : x ∉ supp 10 D v.1 := fun hx => hvx (Finset.mem_filter.mpr ⟨hvR, hx⟩)
  have h0not : (0 : V) ∉ A := by
    intro h0
    obtain ⟨a, ha, h0a⟩ := h0A
    exact hA 0 h0 a ha h0a
  have hx0 : x ≠ (0 : V) := fun he => h0not (he ▸ hxA)
  have hy0 : y ≠ (0 : V) := fun he => h0not (he ▸ hyA)
  apply two_code_cover_no_center_merge_impossible graph_ok h hc b hb hM hx0 hy0
    ?_ hu0s hxus hyus hv0s hyvs hxvs A hA hxA hyA h0A
  intro w hw hw0
  have hm := Finset.mem_union.mp (hcover (Finset.mem_filter.mpr ⟨hw, hw0⟩))
  exact hm.elim (fun hx => Or.inl (Finset.mem_filter.mp hx).2)
    (fun hy => Or.inr (Finset.mem_filter.mp hy).2)

end NeighborCover

namespace NeighborCover

open DagTools

def avoidSetCarrier (n : ℕ) (D : Dag) (z : Fin n) (S : Finset (Fin n)) : Finset ℕ :=
  (inner n D).filter (fun w => z ∈ supp n D w ∧ Disjoint (supp n D w) S)

lemma first_set_acquisition {n : ℕ} {D : Dag} (hS : Strict n D)
    {z x : Fin n} {S : Finset (Fin n)} (hM : merges n D (carrierT n D {z}) = ∅)
    (hxz : x ≠ z) (hxS : x ∈ S) :
    ∀ w, z ∈ supp n D w → x ∈ supp n D w →
      (∀ a ∈ S, a ≠ x → a ∉ supp n D w) →
      ∃ e ∈ exitArcs n D (avoidSetCarrier n D z S),
        z ∈ supp n D (n + e.1) ∧ x ∈ supp n D (n + e.1) ∧
          ∀ a ∈ S, a ≠ x → a ∉ supp n D (n + e.1) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hzw hxw hother
    by_cases hwn : w < n
    · have hs : supp n D w = {⟨w, hwn⟩} := supp_input D ⟨w, hwn⟩
      rw [hs, Finset.mem_singleton] at hzw hxw
      exact False.elim (hxz (hxw.trans hzw.symm))
    · by_cases hwlen : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        have hor := (sem_zm_gate hS hM hj hzw).1
        have hparents : z ∈ supp n D (opA D j) ∨ z ∈ supp n D (opB D j) := by
          rwa [sem_supp_or hS hj hor, Finset.mem_union] at hzw
        have hex : ∃ s : Bool, z ∈ supp n D (src D (j, s)) := by
          rcases hparents with ha | hb
          · exact ⟨false, by simpa only [sb_src_false] using ha⟩
          · exact ⟨true, by simpa only [sb_src_true] using hb⟩
        obtain ⟨s, hzs⟩ := hex
        have hless := sem_src_lt hS hj s
        have hsub : supp n D (src D (j, s)) ⊆ supp n D (n + j) := by
          rw [sem_supp_or hS hj hor]
          cases s
          · simpa only [sb_src_false] using (Finset.subset_union_left :
              supp n D (opA D j) ⊆ supp n D (opA D j) ∪ supp n D (opB D j))
          · simpa only [sb_src_true] using (Finset.subset_union_right :
              supp n D (opB D j) ⊆ supp n D (opA D j) ∪ supp n D (opB D j))
        have hothers : ∀ a ∈ S, a ≠ x → a ∉ supp n D (src D (j, s)) :=
          fun a ha hax hm => hother a ha hax (hsub hm)
        by_cases hxs : x ∈ supp n D (src D (j, s))
        · exact ih _ hless hzs hxs hothers
        · refine ⟨(j, s), ?_, hzw, hxw, hother⟩
          rw [exitArcs, Finset.mem_filter]
          refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, Finset.mem_univ s⟩, ?_, ?_⟩
          · apply Finset.mem_filter.mpr
            refine ⟨sb_mem_inner.mpr (by omega), hzs, Finset.disjoint_left.mpr ?_⟩
            intro a has haS
            by_cases hax : a = x
            · exact hxs (hax ▸ has)
            · exact hothers a haS hax has
          · intro hout
            exact Finset.disjoint_left.mp (Finset.mem_filter.mp hout).2.2 hxw hxS
      · rw [supp_ge D w (by omega)] at hzw
        exact False.elim (Finset.notMem_empty _ hzw)

lemma avoidSet_surplus_le_one {n : ℕ} {D : Dag}
    (b : Fin n → ℕ) (hb : PureBranch n D b) (z : Fin n) (S : Finset (Fin n))
    (hcover : ∀ u ∈ residualUnits n D b, z ∈ supp n D u.1 →
      ∃ a ∈ S, a ∈ supp n D u.1) :
    surplusOn D (avoidSetCarrier n D z S) ≤ 1 := by
  classical
  unfold avoidSetCarrier
  rw [← sb_card_units_filter]
  have hsub : (units n D).filter (fun u => z ∈ supp n D u.1 ∧
      Disjoint (supp n D u.1) S) ⊆ {(⟨b z, 0⟩ : Σ _ : ℕ, ℕ)} := by
    intro u hu
    obtain ⟨huunit, hzu, hdis⟩ := Finset.mem_filter.mp hu
    by_cases hr : u ∈ reservedUnits n D b
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
      have hzv : z = v := by rwa [(hb v hv).2, Finset.mem_singleton] at hzu
      subst v
      exact Finset.mem_singleton_self _
    · have hup : u ∈ unitsPlus n D := Finset.mem_filter.mpr ⟨huunit, ⟨z, hzu⟩⟩
      have hur : u ∈ residualUnits n D b := Finset.mem_sdiff.mpr ⟨hup, hr⟩
      obtain ⟨a, haS, hau⟩ := hcover u hur hzu
      exact False.elim (Finset.disjoint_left.mp hdis hau haS)
  exact (Finset.card_le_card hsub).trans (by simp)

lemma avoidSet_sources_le_one {n : ℕ} (D : Dag) (z : Fin n) (S : Finset (Fin n)) :
    (sources n (avoidSetCarrier n D z S)).card ≤ 1 := by
  have hsub : sources n (avoidSetCarrier n D z S) ⊆ {z.val} := by
    intro w hw
    obtain ⟨hwK, hwn⟩ := Finset.mem_filter.mp hw
    have hzw := (Finset.mem_filter.mp hwK).2.1
    have hs : supp n D w = {⟨w, hwn⟩} := supp_input D ⟨w, hwn⟩
    rw [hs, Finset.mem_singleton] at hzw
    exact Finset.mem_singleton.mpr (congrArg Fin.val hzw).symm
  exact (Finset.card_le_card hsub).trans (by simp)

lemma avoidSet_exits_le_two {n : ℕ} {D : Dag} (h : StrictLive n D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) (z : Fin n) (S : Finset (Fin n))
    (hM : merges n D (carrierT n D {z}) = ∅)
    (hcover : ∀ u ∈ residualUnits n D b, z ∈ supp n D u.1 →
      ∃ a ∈ S, a ∈ supp n D u.1) :
    (exitArcs n D (avoidSetCarrier n D z S)).card ≤ 2 := by
  have hpred : ∀ j, j < D.length → n + j ∈ avoidSetCarrier n D z S →
      opA D j ∈ avoidSetCarrier n D z S ∨ opB D j ∈ avoidSetCarrier n D z S := by
    intro j hj hw
    obtain ⟨_, hz, hdis⟩ := Finset.mem_filter.mp hw
    have hor := (sem_zm_gate h.1 hM hj hz).1
    have hsubA : supp n D (opA D j) ⊆ supp n D (n + j) := by
      rw [sem_supp_or h.1 hj hor]
      exact Finset.subset_union_left
    have hsubB : supp n D (opB D j) ⊆ supp n D (n + j) := by
      rw [sem_supp_or h.1 hj hor]
      exact Finset.subset_union_right
    rw [sem_supp_or h.1 hj hor, Finset.mem_union] at hz
    obtain ⟨ha, hb, _⟩ := h.1 j hj
    rcases hz with hzA | hzB
    · exact Or.inl (Finset.mem_filter.mpr ⟨sb_mem_inner.mpr (by omega), hzA,
        Finset.disjoint_left.mpr (fun a haS ha => Finset.disjoint_left.mp hdis (hsubA haS) ha)⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨sb_mem_inner.mpr (by omega), hzB,
        Finset.disjoint_left.mpr (fun a haS ha => Finset.disjoint_left.mp hdis (hsubB haS) ha)⟩)
  have hflow := carrier_flow h (avoidSetCarrier n D z S) (Finset.filter_subset _ _) hpred
  have hs := avoidSet_sources_le_one D z S
  have hu := avoidSet_surplus_le_one b hb z S hcover
  omega

lemma directional_cover_card_le_two {n m : ℕ} {D : Dag} (h : StrictLive n D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) (z : Fin n) (label : Fin m → Fin n)
    (hM : merges n D (carrierT n D {z}) = ∅) (hnotz : ∀ i, label i ≠ z)
    (hcover : ∀ u ∈ residualUnits n D b, z ∈ supp n D u.1 →
      ∃ i, label i ∈ supp n D u.1)
    (w : Fin m → ℕ) (hw : ∀ i, z ∈ supp n D (w i) ∧ label i ∈ supp n D (w i) ∧
      ∀ j, j ≠ i → label j ∉ supp n D (w i)) : m ≤ 2 := by
  classical
  let S : Finset (Fin n) := Finset.univ.image label
  have hlabel : Function.Injective label := by
    intro i j heq
    by_contra hne
    exact (hw i).2.2 j (Ne.symm hne) (heq ▸ (hw i).2.1)
  have hmem (i : Fin m) : label i ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hex : ∀ i, ∃ e ∈ exitArcs n D (avoidSetCarrier n D z S),
      z ∈ supp n D (n + e.1) ∧ label i ∈ supp n D (n + e.1) ∧
      ∀ a ∈ S, a ≠ label i → a ∉ supp n D (n + e.1) := by
    intro i
    apply first_set_acquisition h.1 hM (hnotz i) (hmem i) (w i) (hw i).1 (hw i).2.1
    intro a ha hneq
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    exact (hw i).2.2 j (fun he => hneq (congrArg label he))
  choose e he hze hxe hother using hex
  have hinj : Function.Injective e := by
    intro i j heq
    by_contra hne
    have hlabels : label i ≠ label j := fun he => hne (hlabel he)
    exact hother j (label i) (hmem i) hlabels (heq ▸ hxe i)
  have hsub : Finset.univ.image e ⊆ exitArcs n D (avoidSetCarrier n D z S) := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact he i
  have hcard : m ≤ (exitArcs n D (avoidSetCarrier n D z S)).card := by
    have hc := Finset.card_le_card hsub
    simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] using hc
  have hbound := avoidSet_exits_le_two h b hb z S hM (by
    intro u hu hzu
    obtain ⟨i, hi⟩ := hcover u hu hzu
    exact ⟨label i, hmem i, hi⟩)
  omega

end NeighborCover

namespace NeighborCover
namespace R2Actual

open DagTools

abbrev Unit := Σ _ : ℕ, ℕ

def pick (u v : Unit) (q : Fin 2) : Unit := if q = 0 then u else v

def pairCode (D : Dag) (u v : Unit) (x : V) : Finset (Fin 2) :=
  Finset.univ.filter (fun q => x ∈ supp 10 D (pick u v q).1)

lemma mem_pairCode (D : Dag) (u v : Unit) (x : V) (q : Fin 2) :
    q ∈ pairCode D u v x ↔ x ∈ supp 10 D (pick u v q).1 := by
  simp only [pairCode, Finset.mem_filter, Finset.mem_univ, true_and]

lemma mem_pairCode_zero (D : Dag) (u v : Unit) (x : V) :
    (0 : Fin 2) ∈ pairCode D u v x ↔ x ∈ supp 10 D u.1 := by
  simp [mem_pairCode, pick]

lemma mem_pairCode_one (D : Dag) (u v : Unit) (x : V) :
    (1 : Fin 2) ∈ pairCode D u v x ↔ x ∈ supp 10 D v.1 := by
  simp [mem_pairCode, pick]

lemma pick_mem {D : Dag} {b : V → ℕ} {u v : Unit}
    (hpair : residualUnits 10 D b = {u, v}) (q : Fin 2) :
    pick u v q ∈ residualUnits 10 D b := by
  rw [hpair]
  unfold pick
  split_ifs <;> simp

lemma pairCode_nonempty_iff {D : Dag} {b : V → ℕ} {u v : Unit}
    (hpair : residualUnits 10 D b = {u, v}) (x : V) :
    (pairCode D u v x).Nonempty ↔ (code D b x).Nonempty := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨pick u v q, Finset.mem_filter.mpr ⟨pick_mem hpair q, (mem_pairCode D u v x q).mp hq⟩⟩
  · rintro ⟨w, hw⟩
    obtain ⟨hwR, hxw⟩ := Finset.mem_filter.mp hw
    rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hwR
    rcases hwR with hwu | hwv
    · subst w
      exact ⟨0, (mem_pairCode_zero D u v x).mpr hxw⟩
    · subst w
      exact ⟨1, (mem_pairCode_one D u v x).mpr hxw⟩

lemma pairCode_subset_iff {D : Dag} {b : V → ℕ} {u v : Unit}
    (hpair : residualUnits 10 D b = {u, v}) (x y : V) :
    pairCode D u v x ⊆ pairCode D u v y ↔
      ∀ w ∈ residualUnits 10 D b, x ∈ supp 10 D w.1 → y ∈ supp 10 D w.1 := by
  constructor
  · intro hsub w hw hxw
    rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hwu | hwv
    · subst w
      exact (mem_pairCode_zero D u v y).mp (hsub ((mem_pairCode_zero D u v x).mpr hxw))
    · subst w
      exact (mem_pairCode_one D u v y).mp (hsub ((mem_pairCode_one D u v x).mpr hxw))
  · intro hsub q hqx
    exact (mem_pairCode D u v y q).mpr
      (hsub (pick u v q) (pick_mem hpair q) ((mem_pairCode D u v x q).mp hqx))

def vertex (i : Fin 6) : V := ([2, 3, 8, 6, 9, 7] : List V).getD i.val 0

abbrev Conditions (center : Finset (Fin 2)) (f : Fin 6 → Finset (Fin 2)) : Prop :=
  center.Nonempty ∧
  (∀ i, ¬ center ⊆ f i) ∧
  (∀ i, (f i).Nonempty ∨ (f (i + 1)).Nonempty) ∧
  (∀ i j, i ≠ j → i.val % 2 = j.val % 2 → (f i).Nonempty → ¬ f i ⊆ f j)

lemma cycle_vertices : ∀ i : Fin 6,
    vertex i ∈ C ∧ vertex i ≠ 0 ∧ adj (vertex i) (vertex (i + 1)) := by
  decide +kernel

lemma parity_separation_geometry : ∀ i j : Fin 6, i ≠ j → i.val % 2 = j.val % 2 →
    vertex j ≠ vertex i ∧ ¬ adj (vertex i) (vertex j) ∧
      ∃ k ∈ J, adj k (vertex i) ∧ ¬ adj k (vertex j) := by
  decide +kernel

lemma eligible_of_code_nonempty {D : Dag} {b : V → ℕ} {x : V}
    (hx : (code D b x).Nonempty) : x ∈ eligSet 10 D := by
  obtain ⟨w, hw⟩ := hx
  obtain ⟨hwR, hxw⟩ := Finset.mem_filter.mp hw
  have hwunit : w ∈ units 10 D :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hwR).1).1
  have hfan := (mem_units.mp hwunit).2
  exact mem_eligSet.mpr ⟨w.1, by omega, hxw⟩

lemma pair_conditions {D : Dag} (h : StrictLive 10 D) (hc : sem_Comp 10 adj D)
    (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b) {u v : Unit}
    (hpair : residualUnits 10 D b = {u, v}) :
    Conditions (pairCode D u v 0) (fun i => pairCode D u v (vertex i)) := by
  have hcenter := center_code_positive h hc hi b hb
  refine ⟨(pairCode_nonempty_iff hpair 0).mpr (Finset.card_pos.mp (by omega)), ?_, ?_, ?_⟩
  · intro i hsub
    apply center_code_separates h hc hz hi b hb (cycle_vertices i).1
    intro w hw
    obtain ⟨hwR, hw0⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hwR, (pairCode_subset_iff hpair 0 (vertex i)).mp hsub w hwR hw0⟩
  · intro i
    by_cases hfirst : (pairCode D u v (vertex i)).Nonempty
    · exact Or.inl hfirst
    · by_cases hnext : (pairCode D u v (vertex (i + 1))).Nonempty
      · exact Or.inr hnext
      · have hi0 : code D b (vertex i) = ∅ := Finset.not_nonempty_iff_eq_empty.mp
          (fun hn => hfirst ((pairCode_nonempty_iff hpair (vertex i)).mpr hn))
        have hj0 : code D b (vertex (i + 1)) = ∅ := Finset.not_nonempty_iff_eq_empty.mp
          (fun hn => hnext ((pairCode_nonempty_iff hpair (vertex (i + 1))).mpr hn))
        exact False.elim (no_adjacent_empty_codes h hc hi b hb (cycle_vertices i).1
          (cycle_vertices (i + 1)).1 (cycle_vertices i).2.2 hi0 hj0)
  · intro i j hij hpar hn hsub
    obtain ⟨hji, hnon, k, hkJ, hki, hkj⟩ := parity_separation_geometry i j hij hpar
    have hiCode := (pairCode_nonempty_iff hpair (vertex i)).mp hn
    exact one_co_star_separates h hc hz b hb (hi hkJ) hki hji hnon hkj
      (eligible_of_code_nonempty hiCode) hiCode ((pairCode_subset_iff hpair (vertex i) (vertex j)).mp hsub)

end R2Actual
end NeighborCover

namespace NeighborCover
namespace R2Actual

open DagTools

lemma not_adj_of_bit_false {x y : V} (h : R2Profiles.edgeBit x y = false) : ¬ adj x y := by
  change ¬ R2Profiles.edgeBit x y = true
  rw [h]
  exact Bool.false_ne_true

lemma residual_two_no_center_merge_impossible {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (hR : (residualUnits 10 D b).card ≤ 2)
    (hM : merges 10 D (carrierT 10 D ({0} : Finset V)) = ∅) : False := by
  classical
  have htwo := at_least_two_residual_of_bzero h hc hz hi b hb
  obtain ⟨u, v, _, hpair⟩ := Finset.card_eq_two.mp
    (by omega : (residualUnits 10 D b).card = 2)
  have hcond := pair_conditions h hc hz hi b hb hpair
  obtain ⟨hcenter, k, i, j, _, h0k, hix, hjy, hind⟩ :=
    R2Profiles.independent_hit (pairCode D u v 0)
      (fun i => pairCode D u v (vertex i)) hcond
  let x := vertex i
  let y := vertex j
  change pairCode D u v x = {0} at hix
  change pairCode D u v y = {1} at hjy
  have hu0 : (0 : V) ∈ supp 10 D u.1 :=
    (mem_pairCode_zero D u v 0).mp (by rw [hcenter]; simp)
  have hv0 : (0 : V) ∈ supp 10 D v.1 :=
    (mem_pairCode_one D u v 0).mp (by rw [hcenter]; simp)
  have hux : x ∈ supp 10 D u.1 :=
    (mem_pairCode_zero D u v x).mp (by rw [hix]; simp)
  have hvy : y ∈ supp 10 D v.1 :=
    (mem_pairCode_one D u v y).mp (by rw [hjy]; simp)
  have hnxv : x ∉ supp 10 D v.1 := by
    intro hxv
    have hm := (mem_pairCode_one D u v x).mpr hxv
    rw [hix, Finset.mem_singleton] at hm
    exact (by decide : (1 : Fin 2) ≠ 0) hm
  have hnyu : y ∉ supp 10 D u.1 := by
    intro hyu
    have hm := (mem_pairCode_zero D u v y).mpr hyu
    rw [hjy, Finset.mem_singleton] at hm
    exact (by decide : (0 : Fin 2) ≠ 1) hm
  have hcover : ∀ w ∈ residualUnits 10 D b, (0 : V) ∈ supp 10 D w.1 →
      x ∈ supp 10 D w.1 ∨ y ∈ supp 10 D w.1 := by
    intro w hw _
    rw [hpair, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hwu | hwv
    · subst w
      exact Or.inl hux
    · subst w
      exact Or.inr hvy
  have htriple : R2Profiles.IndependentTriple k x y := hind
  obtain ⟨_, _, _, hkx, hxk, hky, hyk, hxy, hyx⟩ := htriple
  have hA : ∀ a ∈ ({k, x, y} : Finset V), ∀ c ∈ ({k, x, y} : Finset V), ¬ adj a c := by
    intro a ha c hca
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hca
    rcases ha with rfl | rfl | rfl <;> rcases hca with rfl | rfl | rfl
    · exact graph_ok.2.1 _
    · exact not_adj_of_bit_false hkx
    · exact not_adj_of_bit_false hky
    · exact not_adj_of_bit_false hxk
    · exact graph_ok.2.1 _
    · exact not_adj_of_bit_false hxy
    · exact not_adj_of_bit_false hyk
    · exact not_adj_of_bit_false hyx
    · exact graph_ok.2.1 _
  exact two_code_cover_no_center_merge_impossible graph_ok h hc b hb hM
    (cycle_vertices i).2.1 (cycle_vertices j).2.1 hcover hu0 hux hnyu hv0 hvy hnxv
    {k, x, y} hA (by simp [x, y]) (by simp [x, y]) ⟨k, by simp, h0k⟩

lemma no_center_merge_residual_at_least_three {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 adj D) (hz : Bzero 10 D = 0) (hi : J ⊆ ineligSet 10 D)
    (b : V → ℕ) (hb : PureBranch 10 D b)
    (hM : merges 10 D (carrierT 10 D ({0} : Finset V)) = ∅) :
    3 ≤ (residualUnits 10 D b).card := by
  by_contra hsmall
  exact residual_two_no_center_merge_impossible h hc hz hi b hb (by omega) hM

end R2Actual
end NeighborCover

end I3Branch

namespace ResidualFour

def initial : List Nat := [57, 131, 86, 164, 200, 189, 222, 236]

def target : Nat := 15

def pairs : List Nat → List Nat
  | [] => []
  | a :: rest => rest.flatMap (fun b => [a &&& b, a ||| b]) ++ pairs rest

def fresh (w : List Nat) : List Nat :=
  ((pairs w).filter (fun v => !(w.contains v))).eraseDups

def search : Nat → List Nat → Bool
  | 0, w => w.contains target
  | 1, w => w.contains target || (pairs w).contains target
  | k + 2, w => w.contains target || (fresh w).any (fun v => search (k + 1) (v :: w))

def combine (op : Bool) (a b : Nat) : Nat := if op then a ||| b else a &&& b

lemma combine_comm (op : Bool) (a b : Nat) : combine op a b = combine op b a := by
  cases op <;> simp [combine, Nat.land_comm, Nat.lor_comm]

lemma combine_self (op : Bool) (a : Nat) : combine op a a = a := by
  cases op <;> simp [combine]

lemma pair_or_existing (w : List Nat) (op : Bool) (a b : Nat)
    (ha : a ∈ w) (hb : b ∈ w) : combine op a b ∈ pairs w ∨ combine op a b ∈ w := by
  induction w with
  | nil => simp at ha
  | cons c rest ih =>
    rcases List.mem_cons.mp ha with rfl | har
    · rcases List.mem_cons.mp hb with rfl | hbr
      · exact Or.inr (by simp [combine_self])
      · apply Or.inl
        simp only [pairs, List.mem_append, List.mem_flatMap]
        apply Or.inl
        refine ⟨b, hbr, ?_⟩
        cases op <;> simp [combine]
    · rcases List.mem_cons.mp hb with rfl | hbr
      · apply Or.inl
        rw [combine_comm]
        simp only [pairs, List.mem_append, List.mem_flatMap]
        apply Or.inl
        refine ⟨a, har, ?_⟩
        cases op <;> simp [combine]
      · rcases ih har hbr with hp | hw
        · exact Or.inl (List.mem_append_right _ hp)
        · exact Or.inr (List.mem_cons_of_mem c hw)

lemma mem_fresh (w : List Nat) (v : Nat) :
    v ∈ fresh w ↔ v ∈ pairs w ∧ v ∉ w := by
  simp [fresh]

lemma search_of_mem (k : Nat) (w : List Nat) (h : target ∈ w) : search k w = true := by
  cases k with
  | zero => simpa [search] using h
  | succ k =>
    cases k with
    | zero => simp [search, h]
    | succ k => simp [search, h]

lemma search_mono (k : Nat) (w : List Nat) : search k w = true → search (k + 1) w = true := by
  induction k using Nat.twoStepInduction generalizing w with
  | zero =>
    intro h
    simp only [search, Bool.or_eq_true] at *
    exact Or.inl h
  | one =>
    intro h
    simp only [search, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · by_cases hm : target ∈ w
      · exact Or.inl (by simpa using hm)
      · apply Or.inr
        rw [List.any_eq_true]
        refine ⟨target, (mem_fresh w target).mpr ⟨by simpa using h, hm⟩, ?_⟩
        exact search_of_mem 1 (target :: w) List.mem_cons_self
  | more k ih0 ih1 =>
    intro h
    simp only [search, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · apply Or.inr
      rw [List.any_eq_true] at h ⊢
      obtain ⟨v, hv, hs⟩ := h
      exact ⟨v, hv, ih1 _ hs⟩

def CanMake : Nat → List Nat → Prop
  | 0, w => target ∈ w
  | k + 1, w => target ∈ w ∨
      ∃ op : Bool, ∃ a ∈ w, ∃ b ∈ w, CanMake k (combine op a b :: w)

lemma canMake_mono_list (k : Nat) (w z : List Nat) (hsub : w ⊆ z) :
    CanMake k w → CanMake k z := by
  induction k generalizing w z with
  | zero =>
    intro h
    exact hsub h
  | succ k ih =>
    intro h
    rcases h with h | ⟨op, a, ha, b, hb, h⟩
    · exact Or.inl (hsub h)
    · refine Or.inr ⟨op, a, hsub ha, b, hsub hb, ih _ _ ?_ h⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · simp
      · exact List.mem_cons_of_mem _ (hsub hv)

lemma search_complete (k : Nat) (w : List Nat) (h : CanMake k w) : search k w = true := by
  induction k using Nat.twoStepInduction generalizing w with
  | zero => exact search_of_mem 0 w h
  | one =>
    rcases h with h | ⟨op, a, ha, b, hb, h⟩
    · exact search_of_mem 1 w h
    · change target ∈ combine op a b :: w at h
      rcases List.mem_cons.mp h with he | h
      · rcases pair_or_existing w op a b ha hb with hp | hm
        · simp only [search, Bool.or_eq_true]
          exact Or.inr (by simpa using (he.symm ▸ hp : target ∈ pairs w))
        · exact search_of_mem 1 w (he ▸ hm)
      · exact search_of_mem 1 w h
  | more k ih0 ih1 =>
    rcases h with h | ⟨op, a, ha, b, hb, h⟩
    · exact search_of_mem _ w h
    · let v := combine op a b
      have hc : CanMake (k + 1) (v :: w) := h
      by_cases hm : v ∈ w
      · have hs : v :: w ⊆ w := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hm
          · exact hx
        exact search_mono _ _ (ih1 _ (canMake_mono_list _ _ _ hs hc))
      · have hp : v ∈ pairs w := (pair_or_existing w op a b ha hb).resolve_right hm
        simp only [search, Bool.or_eq_true]
        apply Or.inr
        rw [List.any_eq_true]
        exact ⟨v, (mem_fresh w v).mpr ⟨hp, hm⟩, ih1 _ hc⟩

def pack : List Bool → Nat
  | [] => 0
  | b :: bs => Nat.bit b (pack bs)

lemma pack_and (a b : List Bool) (hl : a.length = b.length) :
    pack (List.zipWith Bool.and a b) = pack a &&& pack b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons c cs => simp at hl
  | cons c cs ih =>
    cases b with
    | nil => simp at hl
    | cons d ds =>
      have ht : cs.length = ds.length := Nat.succ.inj hl
      simp [List.zipWith, pack, Nat.land_bit, ih ds ht]

lemma pack_or (a b : List Bool) (hl : a.length = b.length) :
    pack (List.zipWith Bool.or a b) = pack a ||| pack b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons c cs => simp at hl
  | cons c cs ih =>
    cases b with
    | nil => simp at hl
    | cons d ds =>
      have ht : cs.length = ds.length := Nat.succ.inj hl
      simp [List.zipWith, pack, Nat.lor_bit, ih ds ht]

def sample (r : Fin 8) (v : Fin 5) : Bool :=
  ([3, 6, 12, 17, 5, 9, 20, 26].getD r.val 0).testBit v.val

abbrev Func := (Fin 5 → Bool) → Bool

def word (f : Func) : Nat := pack (List.ofFn (fun r : Fin 8 => f (sample r)))

lemma word_and (f g : Func) : word (fun x => f x && g x) = word f &&& word g := by
  have hz : List.ofFn (fun r : Fin 8 => f (sample r) && g (sample r)) =
      List.zipWith Bool.and (List.ofFn (fun r : Fin 8 => f (sample r)))
        (List.ofFn (fun r : Fin 8 => g (sample r))) := rfl
  unfold word
  rw [hz]
  exact pack_and _ _ (by simp)

lemma word_or (f g : Func) : word (fun x => f x || g x) = word f ||| word g := by
  have hz : List.ofFn (fun r : Fin 8 => f (sample r) || g (sample r)) =
      List.zipWith Bool.or (List.ofFn (fun r : Fin 8 => f (sample r)))
        (List.ofFn (fun r : Fin 8 => g (sample r))) := rfl
  unfold word
  rw [hz]
  exact pack_or _ _ (by simp)

def fcombine (op : Bool) (f g : Func) : Func :=
  fun x => if op then f x || g x else f x && g x

lemma word_combine (op : Bool) (f g : Func) :
    word (fcombine op f g) = combine op (word f) (word g) := by
  cases op
  · exact word_and f g
  · exact word_or f g

def desired : Func := fun x =>
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4)

def inputs : List Func :=
  [fun x => x 0, fun x => x 1, fun x => x 2, fun x => x 3, fun x => x 4,
   fun x => x 0 || x 3, fun x => x 2 || x 4, fun x => x 3 || x 4]

lemma word_desired : word desired = target := by decide +kernel

lemma word_inputs : inputs.map word = initial := by decide +kernel

def FnCanMake : Nat → List Func → Prop
  | 0, w => desired ∈ w
  | k + 1, w => desired ∈ w ∨
      ∃ op : Bool, ∃ f ∈ w, ∃ g ∈ w, FnCanMake k (fcombine op f g :: w)

lemma word_simulation (k : Nat) (w : List Func) (h : FnCanMake k w) :
    CanMake k (w.map word) := by
  induction k generalizing w with
  | zero =>
    change target ∈ w.map word
    rw [← word_desired]
    exact List.mem_map.mpr ⟨desired, h, rfl⟩
  | succ k ih =>
    rcases h with h | ⟨op, f, hf, g, hg, h⟩
    · apply Or.inl
      rw [← word_desired]
      exact List.mem_map.mpr ⟨desired, h, rfl⟩
    · refine Or.inr ⟨op, word f, List.mem_map.mpr ⟨f, hf, rfl⟩,
        word g, List.mem_map.mpr ⟨g, hg, rfl⟩, ?_⟩
      simpa only [List.map_cons, word_combine] using ih _ h

lemma five_functions_suffice : FnCanMake 5 inputs := by
  let a : Func := fun x => x 0
  let b : Func := fun x => x 1
  let c : Func := fun x => x 2
  let q : Func := fun x => x 0 || x 3
  let r : Func := fun x => x 2 || x 4
  let s : Func := fun x => x 3 || x 4
  let t1 := fcombine true a c
  let t2 := fcombine false q r
  let t3 := fcombine false t2 s
  let t4 := fcombine true b t3
  let t5 := fcombine false t1 t4
  have he : t5 = desired := by
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
      cases h3 : x 3 <;> cases h4 : x 4 <;>
      simp [t5, t4, t3, t2, t1, a, b, c, q, r, s, fcombine, desired, h0, h1, h2, h3, h4]
  refine Or.inr ⟨true, a, ?_, c, ?_, ?_⟩
  · simp [a, inputs]
  · simp [c, inputs]
  change FnCanMake 4 (t1 :: inputs)
  refine Or.inr ⟨false, q, ?_, r, ?_, ?_⟩
  · simp [q, inputs]
  · simp [r, inputs]
  change FnCanMake 3 (t2 :: t1 :: inputs)
  refine Or.inr ⟨false, t2, List.mem_cons_self, s, ?_, ?_⟩
  · simp [s, inputs]
  change FnCanMake 2 (t3 :: t2 :: t1 :: inputs)
  refine Or.inr ⟨true, b, ?_, t3, List.mem_cons_self, ?_⟩
  · simp [b, inputs]
  change FnCanMake 1 (t4 :: t3 :: t2 :: t1 :: inputs)
  refine Or.inr ⟨false, t1, ?_, t4, List.mem_cons_self, ?_⟩
  · simp
  change desired ∈ t5 :: t4 :: t3 :: t2 :: t1 :: inputs
  exact List.mem_cons.mpr (Or.inl he.symm)

def zeroFunc : Func := fun _ => false

def oneFunc : Func := fun _ => true

lemma desired_ne_zero : desired ≠ zeroFunc := by
  intro h
  have hc := congrFun h (fun _ => true)
  simp [desired, zeroFunc] at hc

lemma desired_ne_one : desired ≠ oneFunc := by
  intro h
  have hc := congrFun h (fun _ => false)
  simp [desired, oneFunc] at hc

lemma fn_mono_list (k : Nat) (w z : List Func) (hsub : w ⊆ z) :
    FnCanMake k w → FnCanMake k z := by
  induction k generalizing w z with
  | zero =>
    intro h
    exact hsub h
  | succ k ih =>
    intro h
    rcases h with h | ⟨op, f, hf, g, hg, h⟩
    · exact Or.inl (hsub h)
    · refine Or.inr ⟨op, f, hsub hf, g, hsub hg, ih _ _ ?_ h⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hsub hv)

lemma fn_mono_budget (k : Nat) (w : List Func) : FnCanMake k w → FnCanMake (k + 1) w := by
  induction k generalizing w with
  | zero => exact Or.inl
  | succ k ih =>
    intro h
    rcases h with h | ⟨op, f, hf, g, hg, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨op, f, hf, g, hg, ih _ h⟩

lemma combine_zero_left (op : Bool) (g : Func) :
    fcombine op zeroFunc g = if op then g else zeroFunc := by
  cases op <;> funext x <;> simp [fcombine, zeroFunc]

lemma combine_one_left (op : Bool) (g : Func) :
    fcombine op oneFunc g = if op then oneFunc else g := by
  cases op <;> funext x <;> simp [fcombine, oneFunc]

lemma combine_zero_right (op : Bool) (f : Func) :
    fcombine op f zeroFunc = if op then f else zeroFunc := by
  cases op <;> funext x <;> simp [fcombine, zeroFunc]

lemma combine_one_right (op : Bool) (f : Func) :
    fcombine op f oneFunc = if op then oneFunc else f := by
  cases op <;> funext x <;> simp [fcombine, oneFunc]

lemma constant_combination (op : Bool) (f g : Func) (w : List Func)
    (hf : f ∈ zeroFunc :: oneFunc :: w) (hg : g ∈ zeroFunc :: oneFunc :: w)
    (hnot : ¬ (f ∈ w ∧ g ∈ w)) : fcombine op f g ∈ zeroFunc :: oneFunc :: w := by
  rcases List.mem_cons.mp hf with rfl | hf
  · rw [combine_zero_left]
    cases op
    · exact List.mem_cons_self
    · exact hg
  · rcases List.mem_cons.mp hf with rfl | hf
    · rw [combine_one_left]
      cases op
      · exact hg
      · exact List.mem_cons_of_mem _ List.mem_cons_self
    · have hf' : f ∈ zeroFunc :: oneFunc :: w :=
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf)
      rcases List.mem_cons.mp hg with rfl | hg
      · rw [combine_zero_right]
        cases op
        · exact List.mem_cons_self
        · exact hf'
      · rcases List.mem_cons.mp hg with rfl | hg
        · rw [combine_one_right]
          cases op
          · exact hf'
          · exact List.mem_cons_of_mem _ List.mem_cons_self
        · exact False.elim (hnot ⟨hf, hg⟩)

lemma remove_constants (k : Nat) (w : List Func) :
    FnCanMake k (zeroFunc :: oneFunc :: w) → FnCanMake k w := by
  induction k generalizing w with
  | zero =>
    intro h
    change desired ∈ zeroFunc :: oneFunc :: w at h
    change desired ∈ w
    simpa [desired_ne_zero, desired_ne_one] using h
  | succ k ih =>
    intro h
    rcases h with h | ⟨op, f, hf, g, hg, h⟩
    · exact Or.inl (by simpa [desired_ne_zero, desired_ne_one] using h)
    · by_cases hold : f ∈ w ∧ g ∈ w
      · refine Or.inr ⟨op, f, hold.1, g, hold.2, ih _ ?_⟩
        apply fn_mono_list _ _ _ ?_ h
        intro x hx
        simpa only [List.mem_cons, or_assoc, or_left_comm, or_comm] using hx
      · apply fn_mono_budget k w
        apply ih
        apply fn_mono_list _ _ _ ?_ h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact constant_combination op f g w hf hg hold
        · exact hx


def compatible (op : Bool) (a : Nat) : Bool :=
  if op then a ||| target == target else a &&& target == target

def terminal (w : List Nat) : Bool :=
  w.contains target ||
    (pairs (w.filter (compatible false))).contains target ||
    (pairs (w.filter (compatible true))).contains target

def fastSearch : Nat → List Nat → Bool
  | 0, w => w.contains target
  | 1, w => terminal w
  | k + 2, w => w.contains target || (fresh w).any (fun v => fastSearch (k + 1) (v :: w))

lemma mem_pairs (y : Nat) (w : List Nat) (hy : y ∈ pairs w) :
    ∃ op : Bool, ∃ a ∈ w, ∃ b ∈ w, y = combine op a b := by
  induction w with
  | nil => simp [pairs] at hy
  | cons a rest ih =>
    simp only [pairs, List.mem_append, List.mem_flatMap] at hy
    rcases hy with ⟨b, hb, h⟩ | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · exact ⟨false, a, List.mem_cons_self, b, List.mem_cons_of_mem _ hb, h⟩
      · exact ⟨true, a, List.mem_cons_self, b, List.mem_cons_of_mem _ hb, h⟩
    · obtain ⟨op, a, ha, b, hb, h⟩ := ih h
      exact ⟨op, a, List.mem_cons_of_mem _ ha, b, List.mem_cons_of_mem _ hb, h⟩

lemma compatible_of_combine (op : Bool) (a b : Nat) (h : combine op a b = target) :
    compatible op a = true := by
  cases op
  · change (a &&& target == target) = true
    apply beq_iff_eq.mpr
    change a &&& b = target at h
    rw [← h, ← Nat.land_assoc]
    simp
  · change (a ||| target == target) = true
    apply beq_iff_eq.mpr
    change a ||| b = target at h
    rw [← h, ← Nat.lor_assoc]
    simp

lemma terminal_complete (w : List Nat) (h : search 1 w = true) : terminal w = true := by
  simp only [search, Bool.or_eq_true] at h
  rcases h with h | h
  · simp only [terminal, Bool.or_eq_true]
    exact Or.inl (Or.inl h)
  · have hm : target ∈ pairs w := by simpa using h
    obtain ⟨op, a, ha, b, hb, he⟩ := mem_pairs target w hm
    have haa : a ∈ w.filter (compatible op) := List.mem_filter.mpr
      ⟨ha, compatible_of_combine op a b he.symm⟩
    have hbb : b ∈ w.filter (compatible op) := List.mem_filter.mpr
      ⟨hb, compatible_of_combine op b a (by rw [combine_comm]; exact he.symm)⟩
    rcases pair_or_existing _ op a b haa hbb with hh | hh
    · rw [← he] at hh
      cases op
      · have hh' : (pairs (w.filter (compatible false))).contains target = true := by
          simpa using hh
        simp only [terminal, Bool.or_eq_true]
        exact Or.inl (Or.inr hh')
      · have hh' : (pairs (w.filter (compatible true))).contains target = true := by
          simpa using hh
        simp only [terminal, Bool.or_eq_true]
        exact Or.inr hh'
    · rw [← he] at hh
      have hh' : w.contains target = true := by
        simpa using (List.mem_filter.mp hh).1
      simp only [terminal, Bool.or_eq_true]
      exact Or.inl (Or.inl hh')

lemma search_to_fast (k : Nat) (w : List Nat) :
    search k w = true → fastSearch k w = true := by
  induction k using Nat.twoStepInduction generalizing w with
  | zero => exact id
  | one => exact terminal_complete w
  | more k ih0 ih1 =>
    intro h
    simp only [search, fastSearch, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · apply Or.inr
      rw [List.any_eq_true] at h ⊢
      obtain ⟨v, hv, hh⟩ := h
      exact ⟨v, hv, ih1 _ hh⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_0 : fastSearch 3 (1 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_1 : fastSearch 3 (187 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_2 : fastSearch 3 (16 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_3 : fastSearch 3 (127 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_4 : fastSearch 3 (32 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_5 : fastSearch 3 (8 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_6 : fastSearch 3 (249 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_7 : fastSearch 3 (24 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_8 : fastSearch 3 (255 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_9 : fastSearch 3 (40 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_10 : fastSearch 3 (253 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_11 : fastSearch 3 (2 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_12 : fastSearch 3 (215 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_13 : fastSearch 3 (128 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_14 : fastSearch 3 (167 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_15 : fastSearch 3 (203 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_16 : fastSearch 3 (129 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_17 : fastSearch 3 (191 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_18 : fastSearch 3 (130 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_19 : fastSearch 3 (223 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_20 : fastSearch 3 (239 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_21 : fastSearch 3 (4 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_22 : fastSearch 3 (246 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_23 : fastSearch 3 (64 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_24 : fastSearch 3 (20 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_25 : fastSearch 3 (68 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_26 : fastSearch 3 (254 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_27 : fastSearch 3 (132 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_28 : fastSearch 3 (136 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_29 : fastSearch 3 (156 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_30 : fastSearch 3 (172 :: initial) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma first_31 : fastSearch 3 (204 :: initial) = false := by
  decide +kernel

lemma fast_four_false : fastSearch 4 initial = false := by
  have hinit : initial.contains target = false := by decide +kernel
  have hfresh : fresh initial = [1, 187, 16, 127, 32, 8, 249, 24, 255, 40, 253, 2, 215, 128, 167, 203, 129, 191, 130, 223, 239, 4, 246, 64, 20, 68, 254, 132, 136, 156, 172, 204] := by decide +kernel
  rw [fastSearch, hinit, hfresh]
  simp only [Nat.reduceAdd, List.any_cons, List.any_nil, first_0, first_1, first_2, first_3, first_4, first_5, first_6, first_7, first_8, first_9, first_10, first_11, first_12, first_13, first_14, first_15, first_16, first_17, first_18, first_19, first_20, first_21, first_22, first_23, first_24, first_25, first_26, first_27, first_28, first_29, first_30, first_31, Bool.false_or]

lemma no_four : ¬ CanMake 4 initial := by
  intro h
  have hc := search_to_fast 4 initial (search_complete 4 initial h)
  rw [fast_four_false] at hc
  exact Bool.false_ne_true hc

lemma no_four_functions : ¬ FnCanMake 4 inputs := by
  intro h
  apply no_four
  simpa only [word_inputs] using word_simulation 4 inputs h

lemma exact_five : ¬ FnCanMake 4 inputs ∧ FnCanMake 5 inputs :=
  ⟨no_four_functions, five_functions_suffice⟩

lemma no_four_with_constants : ¬ FnCanMake 4 (zeroFunc :: oneFunc :: inputs) := by
  intro h
  exact no_four_functions (remove_constants 4 inputs h)

lemma exact_five_with_constants :
    ¬ FnCanMake 4 (zeroFunc :: oneFunc :: inputs) ∧
      FnCanMake 5 (zeroFunc :: oneFunc :: inputs) := by
  refine ⟨no_four_with_constants, fn_mono_list 5 inputs _ ?_ five_functions_suffice⟩
  intro f hf
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gateFunction (w : List Func) (g : Gate) : Func :=
  fun x => g.op.eval (g.inputs.map fun i => (w.getD i zeroFunc) x)

def wireFunctions (gs : List Gate) (w : List Func) : List Func :=
  gs.foldl (fun z g => z ++ [gateFunction z g]) w

lemma get_function_mem (w : List Func) (i : Nat) :
    w.getD i zeroFunc ∈ zeroFunc :: oneFunc :: w := by
  induction w generalizing i with
  | nil => simp
  | cons f fs ih =>
    cases i with
    | zero => simp
    | succ i =>
      have h := ih i
      simp only [List.getD_cons_succ, List.mem_cons] at h ⊢
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))

lemma gate_as_pair (w : List Func) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hsize : g.inputs.length ≤ 2) :
    ∃ op : Bool, ∃ f ∈ zeroFunc :: oneFunc :: w,
      ∃ h ∈ zeroFunc :: oneFunc :: w, gateFunction w g = fcombine op f h := by
  rcases g with ⟨op, ins⟩
  change op = GateOp.and ∨ op = GateOp.or at hop
  cases ins with
  | nil =>
    rcases hop with rfl | rfl
    · refine ⟨false, oneFunc, by simp, oneFunc, by simp, ?_⟩
      rfl
    · refine ⟨true, zeroFunc, by simp, zeroFunc, by simp, ?_⟩
      rfl
  | cons a rest =>
    cases rest with
    | nil =>
      refine ⟨false, w.getD a zeroFunc, get_function_mem w a,
        w.getD a zeroFunc, get_function_mem w a, ?_⟩
      funext x
      rcases hop with rfl | rfl <;> simp [gateFunction, GateOp.eval, fcombine]
    | cons b rest =>
      cases rest with
      | cons c rest => simp at hsize
      | nil =>
        rcases hop with rfl | rfl
        · refine ⟨false, w.getD a zeroFunc, get_function_mem w a,
            w.getD b zeroFunc, get_function_mem w b, ?_⟩
          funext x
          simp [gateFunction, GateOp.eval, fcombine]
        · refine ⟨true, w.getD a zeroFunc, get_function_mem w a,
            w.getD b zeroFunc, get_function_mem w b, ?_⟩
          funext x
          simp [gateFunction, GateOp.eval, fcombine]

lemma functions_can_make (gs : List Gate) (w : List Func)
    (hmono : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hm : desired ∈ zeroFunc :: oneFunc :: wireFunctions gs w) :
    FnCanMake gs.length (zeroFunc :: oneFunc :: w) := by
  induction gs generalizing w with
  | nil => exact hm
  | cons g gs ih =>
    have hg := hmono g (List.mem_cons_self)
    obtain ⟨op, f, hf, h, hh, he⟩ := gate_as_pair w g hg.1 hg.2
    have ht := ih (w ++ [gateFunction w g])
      (fun g hg => hmono g (List.mem_cons_of_mem _ hg)) hm
    change FnCanMake (gs.length + 1) (zeroFunc :: oneFunc :: w)
    refine Or.inr ⟨op, f, hf, h, hh, fn_mono_list _ _ _ ?_ ht⟩
    intro a ha
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha ⊢
    rcases ha with rfl | rfl | ha | ha
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr ha))
    · exact Or.inl (ha.trans he)

lemma get_function_eval (w : List Func) (i : Nat) (x : Fin 5 → Bool) :
    (w.getD i zeroFunc) x = (w.map fun f => f x).getD i false := by
  induction w generalizing i with
  | nil => rfl
  | cons f fs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

lemma wire_functions_eval (gs : List Gate) (w : List Func) (x : Fin 5 → Bool) :
    (wireFunctions gs w).map (fun f => f x) =
      gs.foldl (fun z g => z ++ [g.op.eval (g.inputs.map fun i => z.getD i false)])
        (w.map fun f => f x) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [wireFunctions, List.foldl_cons]
    rw [← wireFunctions, ih]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil]
    congr 2
    simp only [gateFunction, get_function_eval]

lemma circuit_to_functions (C : Circuit) (hC : Monotone2 C)
    (hev : ∀ x, C.eval (inputs.map fun f => f x) = desired x) :
    FnCanMake C.size (zeroFunc :: oneFunc :: inputs) := by
  apply functions_can_make C.gates inputs hC
  have he : (wireFunctions C.gates inputs).getD C.output zeroFunc = desired := by
    funext x
    rw [get_function_eval, wire_functions_eval]
    exact hev x
  rw [← he]
  exact get_function_mem _ _

lemma circuit_lower_of_no_four
    (hn : ¬ FnCanMake 4 (zeroFunc :: oneFunc :: inputs))
    (C : Circuit) (hC : Monotone2 C)
    (hev : ∀ x, C.eval (inputs.map fun f => f x) = desired x) :
    5 ≤ C.size := by
  by_contra hsize
  have hle : C.size ≤ 4 := by omega
  have hmake := circuit_to_functions C hC hev
  have hmore : ∀ d, FnCanMake (C.size + d) (zeroFunc :: oneFunc :: inputs) := by
    intro d
    induction d with
    | zero => exact hmake
    | succ d ih => exact fn_mono_budget _ _ ih
  apply hn
  simpa only [Nat.add_sub_of_le hle] using hmore (4 - C.size)

def fiveCircuit : Circuit :=
  { gates := [⟨.or, [0, 2]⟩, ⟨.and, [5, 6]⟩, ⟨.and, [7, 9]⟩,
      ⟨.or, [1, 10]⟩, ⟨.and, [8, 11]⟩], output := 12 }

lemma fiveCircuit_monotone : Monotone2 fiveCircuit := by
  simp [Monotone2, fiveCircuit]

lemma fiveCircuit_size : fiveCircuit.size = 5 := rfl

lemma fiveCircuit_eval :
    ∀ x, fiveCircuit.eval (inputs.map fun f => f x) = desired x := by
  decide +kernel

lemma circuit_lower_bound (C : Circuit) (hC : Monotone2 C)
    (hev : ∀ x, C.eval (inputs.map fun f => f x) = desired x) :
    5 ≤ C.size := circuit_lower_of_no_four no_four_with_constants C hC hev

end ResidualFour

end PEqualNP.Outside.L_meta_2590_aux
