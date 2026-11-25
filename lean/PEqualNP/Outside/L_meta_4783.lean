import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4783_aux

def drun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem drun_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    drun (g :: gs) x = drun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

def ev (P : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => P.getD i false)

def tbl : List ℕ := [1408, 8832, 12544, 6272, 11264, 5632, 2816]

def adjB (a b : ℕ) : Bool := (tbl.getD a 0).testBit b

def isAdj (a b : ℕ) : Bool := adjB a b || adjB b a

def R (t y : ℕ) : Gate :=
  if y = 0 ∨ y = t then ⟨GateOp.and, [y]⟩
  else if isAdj y 0 = true then ⟨GateOp.and, [y, 0]⟩
  else if isAdj y t = true then ⟨GateOp.and, [y, t]⟩
  else ⟨GateOp.or, []⟩

def Rv (w : ℕ → Bool) (t y : ℕ) : Bool :=
  if y = 0 ∨ y = t then w y
  else if isAdj y 0 = true then (w y && w 0)
  else if isAdj y t = true then (w y && w t)
  else false

def T (t : ℕ) : Gate → Gate
  | ⟨GateOp.and, [a, b]⟩ =>
      if a = 14 ∧ b < 14 then R t b
      else if b = 14 ∧ a < 14 then R t a
      else if a < 14 ∧ b < 14 ∧ a ≠ b ∧ isAdj a b = false then ⟨GateOp.or, []⟩
      else ⟨GateOp.and, [a, b]⟩
  | g => g

theorem ev_R (A : List Bool) (t y : ℕ) : ev A (R t y) = Rv (fun i => A.getD i false) t y := by
  unfold R Rv
  split_ifs <;> simp [ev, GateOp.eval]

theorem Rv_congr (w w' : ℕ → Bool) (t y : ℕ) (ht : t < 14) (hy : y < 14)
    (h : ∀ i < 14, w i = w' i) : Rv w t y = Rv w' t y := by
  unfold Rv
  split_ifs <;> simp [h y hy, h 0 (by omega), h t ht]

theorem ev_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (A B : List Bool)
    (h : ∀ i ∈ g.inputs, A.getD i false = true → B.getD i false = true) :
    ev A g = true → ev B g = true := by
  unfold ev
  rcases hop with hop | hop <;> rw [hop]
  · simp only [GateOp.eval, List.all_eq_true]
    intro hall x hx
    rw [List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i hi (hall _ (List.mem_map_of_mem hi))
  · simp only [GateOp.eval, List.any_eq_true]
    rintro ⟨x, hx, hv⟩
    rw [List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨_, List.mem_map_of_mem hi, h i hi hv⟩

theorem Rv_le (w : ℕ → Bool) (t y : ℕ) (h : Rv w t y = true) : ((w 0 || w t) && w y) = true := by
  unfold Rv at h
  split_ifs at h with h1 h2 h3
  · rcases h1 with rfl | rfl <;> simp [h]
  · simp only [Bool.and_eq_true] at h
    simp [h.1, h.2]
  · simp only [Bool.and_eq_true] at h
    simp [h.1, h.2]

theorem T_le (t : ℕ) (ht : t < 14) (A B : List Bool) (h15 : ∀ i < 15, A.getD i false = B.getD i false)
    (h14 : B.getD 14 false = (B.getD 0 false || B.getD t false))
    (hle : ∀ i, A.getD i false = true → B.getD i false = true)
    (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2) :
    ev A (T t g) = true → ev B g = true := by
  obtain ⟨op, inputs⟩ := g
  simp only at hop hlen
  rcases hop with rfl | rfl
  · rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · exact ev_mono _ (Or.inl rfl) A B (fun i _ hi => hle i hi)
    · exact ev_mono _ (Or.inl rfl) A B (fun i _ hi => hle i hi)
    · simp only [T]
      split_ifs with h1 h2 h3
      · intro hv
        rw [ev_R, Rv_congr _ (fun i => B.getD i false) t b ht h1.2 (fun i hi => h15 i (by omega))] at hv
        have := Rv_le _ t b hv
        rw [← h14] at this
        simp only [ev, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true, h1.1]
        exact this
      · intro hv
        rw [ev_R, Rv_congr _ (fun i => B.getD i false) t a ht h2.2 (fun i hi => h15 i (by omega))] at hv
        have := Rv_le _ t a hv
        rw [← h14] at this
        simp only [ev, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true, h2.1]
        simp only [Bool.and_eq_true] at this ⊢
        exact ⟨this.2, this.1⟩
      · intro hv
        simp [ev, GateOp.eval] at hv
      · exact ev_mono _ (Or.inl rfl) A B (fun i _ hi => hle i hi)
    · simp at hlen
  · exact ev_mono ⟨GateOp.or, inputs⟩ (Or.inr rfl) A B (fun i _ hi => hle i hi)

theorem key1F : ∀ a : Fin 7, ∀ b : Fin 14, adjB a b = true → ∀ t : Fin 14, 7 ≤ (t : ℕ) → ∀ y : Fin 14,
    Rv (fun i => decide (i = (a : ℕ) ∨ i = (b : ℕ))) t y =
      ((decide (0 = (a : ℕ) ∨ 0 = (b : ℕ)) || decide ((t : ℕ) = a ∨ (t : ℕ) = b)) &&
        decide ((y : ℕ) = a ∨ (y : ℕ) = b)) := by
  decide +kernel

theorem key1 (a : ℕ) (ha : a < 7) (b : ℕ) (hb : b < 14) (hab : adjB a b = true) (t : ℕ) (ht : t < 14)
    (ht7 : 7 ≤ t) (y : ℕ) (hy : y < 14) :
    Rv (fun i => decide (i = a ∨ i = b)) t y =
      ((decide (0 = a ∨ 0 = b) || decide (t = a ∨ t = b)) && decide (y = a ∨ y = b)) :=
  key1F ⟨a, ha⟩ ⟨b, hb⟩ hab ⟨t, ht⟩ ht7 ⟨y, hy⟩

theorem key2F : ∀ a : Fin 7, ∀ b : Fin 14, adjB a b = true → ∀ u : Fin 14, ∀ v : Fin 14, (u : ℕ) ≠ v →
    isAdj u v = false → (decide ((u : ℕ) = a ∨ (u : ℕ) = b) && decide ((v : ℕ) = a ∨ (v : ℕ) = b)) = false := by
  decide +kernel

theorem key2 (a : ℕ) (ha : a < 7) (b : ℕ) (hb : b < 14) (hab : adjB a b = true) (u : ℕ) (hu : u < 14)
    (v : ℕ) (hv : v < 14) (huv : u ≠ v) (hadj : isAdj u v = false) :
    (decide (u = a ∨ u = b) && decide (v = a ∨ v = b)) = false :=
  key2F ⟨a, ha⟩ ⟨b, hb⟩ hab ⟨u, hu⟩ ⟨v, hv⟩ huv hadj

theorem adj_bounds (a b : ℕ) (h : adjB a b = true) : a < 7 ∧ b < 14 := by
  unfold adjB at h
  by_cases ha : a < 7
  · refine ⟨ha, ?_⟩
    by_contra hb
    have hlt : tbl.getD a 0 < 2 ^ b := by
      have : tbl.getD a 0 < 2 ^ 14 := by
        interval_cases a <;> decide
      exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt hlt] at h
    exact Bool.false_ne_true h
  · rw [List.getD_eq_default _ _ (by simp [tbl]; omega), Nat.zero_testBit] at h
    exact absurd h Bool.false_ne_true

theorem T_eq (t : ℕ) (ht7 : 7 ≤ t) (ht : t < 14) (a b : ℕ) (hab : adjB a b = true) (A : List Bool)
    (hA : ∀ i < 14, A.getD i false = decide (i = a ∨ i = b))
    (h14 : A.getD 14 false = (A.getD 0 false || A.getD t false))
    (g : Gate) : ev A (T t g) = ev A g := by
  obtain ⟨ha7, hb14⟩ := adj_bounds a b hab
  obtain ⟨op, inputs⟩ := g
  cases op with
  | and =>
    rcases inputs with _ | ⟨u, _ | ⟨v, _ | ⟨c, rest⟩⟩⟩
    · rfl
    · rfl
    · simp only [T]
      split_ifs with h1 h2 h3
      · rw [ev_R, Rv_congr _ (fun i => decide (i = a ∨ i = b)) t v ht h1.2 (fun i hi => hA i hi),
          key1 a ha7 b hb14 hab t ht ht7 v h1.2]
        simp only [ev, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true, h1.1, h14, hA 0 (by omega), hA t ht, hA v h1.2]
      · rw [ev_R, Rv_congr _ (fun i => decide (i = a ∨ i = b)) t u ht h2.2 (fun i hi => hA i hi),
          key1 a ha7 b hb14 hab t ht ht7 u h2.2]
        simp only [ev, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true, h2.1, h14, hA 0 (by omega), hA t ht, hA u h2.2]
        simp only [Bool.true_and, Bool.and_comm]
      · have k := key2 a ha7 b hb14 hab u h3.1 v h3.2.1 h3.2.2.1 h3.2.2.2
        simp only [ev, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          List.any_nil, id, Bool.and_true, hA u h3.1, hA v h3.2.1]
        rw [k]
      · rfl
    · rfl
  | or => rfl
  | not => rfl
  | mod m => rfl
  | maj => rfl

theorem run_le (t : ℕ) (ht : t < 14) (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ (A B : List Bool), A.length = B.length → 15 ≤ B.length →
      (∀ i < 15, A.getD i false = B.getD i false) →
      B.getD 14 false = (B.getD 0 false || B.getD t false) →
      (∀ i, A.getD i false = true → B.getD i false = true) →
      ∀ i, (drun (gs.map (T t)) A).getD i false = true → (drun gs B).getD i false = true := by
  induction gs with
  | nil => intro A B _ _ _ _ hle i; exact hle i
  | cons g gs ih =>
    intro A B hl h15l h15 h14 hle
    rw [List.map_cons, drun_cons, drun_cons]
    have hg := hgs g (by simp)
    apply ih (fun g2 hg2 => hgs g2 (by simp [hg2]))
    · simp only [List.length_append, List.length_singleton, hl]
    · simp only [List.length_append, List.length_singleton]; omega
    · intro i hi
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact h15 i hi
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega),
        List.getD_append _ _ _ _ (by omega)]
      exact h14
    · intro i hi
      rcases lt_trichotomy i B.length with h1 | h1 | h1
      · rw [List.getD_append _ _ _ _ (by omega)] at hi
        rw [List.getD_append _ _ _ _ h1]
        exact hle i hi
      · subst h1
        rw [List.getD_append_right _ _ _ _ (by omega), show B.length - A.length = 0 by omega,
          List.getD_cons_zero] at hi
        rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero]
        exact T_le t ht A B h15 h14 hle g hg.1 hg.2 hi
      · rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega)] at hi
        exact absurd hi Bool.false_ne_true

theorem run_eq (t : ℕ) (ht7 : 7 ≤ t) (ht : t < 14) (a b : ℕ) (hab : adjB a b = true) (gs : List Gate) :
    ∀ (A : List Bool), 15 ≤ A.length →
      (∀ i < 14, A.getD i false = decide (i = a ∨ i = b)) →
      A.getD 14 false = (A.getD 0 false || A.getD t false) →
      drun (gs.map (T t)) A = drun gs A := by
  induction gs with
  | nil => intro A _ _ _; rfl
  | cons g gs ih =>
    intro A hl hA h14
    rw [List.map_cons, drun_cons, drun_cons]
    have e : (T t g).op.eval ((T t g).inputs.map fun i => A.getD i false) =
        g.op.eval (g.inputs.map fun i => A.getD i false) := T_eq t ht7 ht a b hab A hA h14 g
    rw [e]
    apply ih
    · simp only [List.length_append, List.length_singleton]; omega
    · intro i hi
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hA i hi
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega),
        List.getD_append _ _ _ _ (by omega)]
      exact h14

def X1 (a b : ℕ) : Prop := (tbl.getD a 0).testBit b = true

def X2 (y : Fin 14 → Bool) : Prop := ∃ (a : Fin 14) (b : Fin 14), X1 (a : ℕ) (b : ℕ) ∧ y a = true ∧ y b = true

def X3 (y : Fin 14 → Bool) : Prop :=
  (X2 y ∧ ∀ v : Fin 14, y v = true → ¬ X2 (Function.update y v false)) ∨
    (¬ X2 y ∧ ∀ v : Fin 14, y v = false → X2 (Function.update y v true))

def X4 (C : Circuit) (t : Fin 14) : Prop :=
  Monotone2 C ∧ ∀ y : Fin 14 → Bool, X3 y →
    (C.eval (List.ofFn y ++ [GateOp.or.eval [y 0, y t]]) = true ↔ X2 y)

def X5 (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, g.op = GateOp.and →
    ((14 : ℕ) ∈ g.inputs → ∀ i ∈ g.inputs, (14 : ℕ) ≤ i) ∧
      ∀ (u v : ℕ), g.inputs = [u, v] → u < 14 → v < 14 → u ≠ v → X1 u v ∨ X1 v u

theorem min_true (y : Fin 14 → Bool) (h3 : X3 y) (h2 : X2 y) :
    ∃ (a b : Fin 14), X1 (a : ℕ) (b : ℕ) ∧ ∀ v : Fin 14, y v = decide (v = a ∨ v = b) := by
  rcases h3 with ⟨_, hmin⟩ | ⟨hn, _⟩
  · obtain ⟨a, b, hab, ha, hb⟩ := h2
    refine ⟨a, b, hab, fun v => ?_⟩
    by_cases hv : v = a ∨ v = b
    · rcases hv with rfl | rfl
      · simp [ha]
      · simp [hb]
    · rw [decide_eq_false hv]
      push_neg at hv
      by_contra hyv
      have hyv' : y v = true := by cases h : y v <;> simp_all
      apply hmin v hyv'
      refine ⟨a, b, hab, ?_, ?_⟩
      · rw [Function.update_of_ne hv.1.symm]; exact ha
      · rw [Function.update_of_ne hv.2.symm]; exact hb
  · exact absurd h2 hn

theorem T_shape (t : ℕ) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2) :
    (T t g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (T t g).inputs.length ≤ 2 := by
  obtain ⟨op, inputs⟩ := g
  simp only at hop hlen
  rcases hop with rfl | rfl
  · rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [T]
    · simp [T]
    · simp only [T]
      split_ifs <;> simp [R] <;> split_ifs <;> simp
    · simp at hlen
  · simp only [T]
    exact ⟨by simp, hlen⟩

theorem T_x5 (t : ℕ) (ht : t < 14) (g : Gate) (hlen : g.inputs.length ≤ 2) :
    (T t g).op = GateOp.and →
      ((14 : ℕ) ∈ (T t g).inputs → ∀ i ∈ (T t g).inputs, (14 : ℕ) ≤ i) ∧
        ∀ (u v : ℕ), (T t g).inputs = [u, v] → u < 14 → v < 14 → u ≠ v → X1 u v ∨ X1 v u := by
  obtain ⟨op, inputs⟩ := g
  simp only at hlen
  cases op with
  | and =>
    rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · intro _; simp [T]
    · intro _
      simp only [T, List.mem_singleton]
      refine ⟨fun h i hi => by rw [hi, ← h], fun u v h => by simp at h⟩
    · simp only [T]
      split_ifs with h1 h2 h3
      · unfold R
        split_ifs with k1 k2 k3
        · intro _
          refine ⟨fun h => by simp at h; omega, fun u v h => by simp at h⟩
        · intro _
          refine ⟨fun h => by simp at h; omega, fun u v h hu hv huv => ?_⟩
          simp only [List.cons.injEq, and_true] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [isAdj, Bool.or_eq_true] at k2
          rcases k2 with k | k
          · exact Or.inl k
          · exact Or.inr k
        · intro _
          refine ⟨fun h => by simp at h; omega, fun u v h hu hv huv => ?_⟩
          simp only [List.cons.injEq, and_true] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [isAdj, Bool.or_eq_true] at k3
          rcases k3 with k | k
          · exact Or.inl k
          · exact Or.inr k
        · intro h; simp at h
      · unfold R
        split_ifs with k1 k2 k3
        · intro _
          refine ⟨fun h => by simp at h; omega, fun u v h => by simp at h⟩
        · intro _
          refine ⟨fun h => by simp at h; omega, fun u v h hu hv huv => ?_⟩
          simp only [List.cons.injEq, and_true] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [isAdj, Bool.or_eq_true] at k2
          rcases k2 with k | k
          · exact Or.inl k
          · exact Or.inr k
        · intro _
          refine ⟨fun h => by simp at h; omega, fun u v h hu hv huv => ?_⟩
          simp only [List.cons.injEq, and_true] at h
          obtain ⟨rfl, rfl⟩ := h
          simp only [isAdj, Bool.or_eq_true] at k3
          rcases k3 with k | k
          · exact Or.inl k
          · exact Or.inr k
        · intro h; simp at h
      · intro h; simp at h
      · intro _
        refine ⟨fun h i hi => ?_, fun u v h hu hv huv => ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h hi
          rcases h with h | h <;> rcases hi with rfl | rfl <;> omega
        · simp only [List.cons.injEq, and_true] at h
          obtain ⟨hau, hbv⟩ := h
          have : isAdj a b = true := by
            by_contra hc
            exact h3 ⟨by omega, by omega, by omega, by simpa using hc⟩
          rw [← hau, ← hbv]
          simp only [isAdj, Bool.or_eq_true] at this
          rcases this with k | k
          · exact Or.inl k
          · exact Or.inr k
    · simp at hlen
  | or => intro h; simp [T] at h
  | not => intro h; simp [T] at h
  | mod m => intro h; simp [T] at h
  | maj => intro h; simp [T] at h

theorem main (C : Circuit) (t : Fin 14) (ht : 7 ≤ (t : ℕ)) (hC : X4 C t) :
    ∃ D : Circuit, D.size = C.size ∧ X4 D t ∧ X5 D := by
  obtain ⟨hmono, hcorr⟩ := hC
  have hgs : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨k1, k2⟩ := hmono g hg
    exact ⟨by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using k1, k2⟩
  have htl : (t : ℕ) < 14 := t.isLt
  refine ⟨{ gates := C.gates.map (T t), output := C.output }, by simp [Circuit.size], ⟨?_, ?_⟩, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact T_shape t g0 (hgs g0 hg0).1 (hgs g0 hg0).2
  · intro y hy
    have hL15 : 15 ≤ (List.ofFn y ++ [GateOp.or.eval [y 0, y t]]).length := by simp
    have e14 : (List.ofFn y ++ [GateOp.or.eval [y 0, y t]]).getD 14 false = (y 0 || y t) := by
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp [GateOp.eval]
    have e0 : (List.ofFn y ++ [GateOp.or.eval [y 0, y t]]).getD 0 false = y 0 := by
      rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
      simp
    have et : (List.ofFn y ++ [GateOp.or.eval [y 0, y t]]).getD t false = y t := by
      rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      try rfl
    have hL14 : (List.ofFn y ++ [GateOp.or.eval [y 0, y t]]).getD 14 false =
        ((List.ofFn y ++ [GateOp.or.eval [y 0, y t]]).getD 0 false ||
          (List.ofFn y ++ [GateOp.or.eval [y 0, y t]]).getD t false) := by
      rw [e14, e0, et]
    have hold := hcorr y hy
    constructor
    · intro hD
      by_contra hn
      have hfalse : C.eval (List.ofFn y ++ [GateOp.or.eval [y 0, y t]]) = false := by
        cases h : C.eval (List.ofFn y ++ [GateOp.or.eval [y 0, y t]])
        · rfl
        · exact absurd (hold.1 h) hn
      have := run_le t htl C.gates hgs _ _ rfl hL15 (fun _ _ => rfl) hL14 (fun _ h => h) C.output hD
      have e : C.eval (List.ofFn y ++ [GateOp.or.eval [y 0, y t]]) = true := this
      rw [hfalse] at e
      exact Bool.false_ne_true e
    · intro h2
      obtain ⟨a, b, hab, hyv⟩ := min_true y hy h2
      have hA : ∀ i < 14, (List.ofFn y ++ [GateOp.or.eval [y 0, y t]]).getD i false =
          decide (i = (a : ℕ) ∨ i = (b : ℕ)) := by
        intro i hi
        rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
          List.getElem_ofFn, hyv]
        simp [Fin.ext_iff]
      have heq := run_eq t ht htl a b hab C.gates _ hL15 hA hL14
      show (drun (C.gates.map (T t)) (List.ofFn y ++ [GateOp.or.eval [y 0, y t]])).getD C.output false = true
      rw [heq]
      exact hold.2 h2
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact T_x5 t htl g0 (hgs g0 hg0).2

end PEqualNP.Outside.L_meta_4783_aux

theorem PEqualNP.Outside.L_meta_4783 : have x1 : ℕ → ℕ → Prop := fun (x1 x2 : ℕ) => ([(1408 : ℕ), (8832 : ℕ), (12544 : ℕ), (6272 : ℕ), (11264 : ℕ), (5632 : ℕ), (2816 : ℕ)].getD x1 (0 : ℕ)).testBit x2 = Bool.true; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), x1 ↑x3 ↑x4 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Fin (14 : ℕ) → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Fin (14 : ℕ)) => PEqualNP.MetaComplexity.Monotone2 x4 ∧ ∀ (x6 : Fin (14 : ℕ) → Bool), x3 x6 → (x4.eval (List.ofFn x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x6 (0 : Fin (14 : ℕ)), x6 x5]]) = Bool.true ↔ x2 x6); have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x6 ∈ x5.gates, x6.op = PEqualNP.CircuitLowerBounds.GateOp.and → ((14 : ℕ) ∈ x6.inputs → ∀ x10 ∈ x6.inputs, (14 : ℕ) ≤ x10) ∧ ∀ (x9 x10 : ℕ), x6.inputs = [x9, x10] → x9 < (14 : ℕ) → x10 < (14 : ℕ) → x9 ≠ x10 → x1 x9 x10 ∨ x1 x10 x9; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Fin (14 : ℕ)), (7 : ℕ) ≤ ↑x7 → x4 x6 x7 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), x10.size = x6.size ∧ x4 x10 x7 ∧ x5 x10 := by
  dsimp only
  intro C t ht hC
  exact PEqualNP.Outside.L_meta_4783_aux.main C t ht hC
