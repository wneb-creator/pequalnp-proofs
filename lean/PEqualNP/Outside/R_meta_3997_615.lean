import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped BigOperators Sym2

-- Adapted from R_meta_3997_1 (Apache-2.0). The dense deletion and live-wire
-- premises are discharged using proofs from L_meta_1743 and L_meta_1975.
-- The latter credits the gate-deletion argument to L_meta_522.
-- The remaining premises are the sparse first pin and the near-cubic second pin.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_3997_615
    (sparse : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (f : (Fin n → Bool) → Bool) (C : Circuit),
      30 ≤ n → G.Colorable 2 → (∀ v, (G.neighborSet v).ncard = 3) →
      (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ x, f x = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) →
      circuitFun n C = f → IsMinimalCircuit n C → C.size + 1 < 2 * n →
      (∀ v : Fin n, let readers := C.gates.filter fun g =>
          (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
        readers.length ≤ 3 ∧ (readers.length = 3 → ∀ g ∈ readers, g.op = .or)) →
      (∃ v : Fin n, (C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length ≤ 1) →
      ∃ v t, t + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) t)
    (nextPin : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (z : Fin n) (T : Set (Fin n))
      (f : (Fin n → Bool) → Bool),
      30 ≤ n → Even n → H.Colorable 2 →
      (∀ v (w : H.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (H.neighborSet z).ncard = 0 → T.ncard = 3 → z ∉ T →
      (∀ a ∈ T, ∀ b ∈ T, a ≠ b → ∀ p : H.Walk a b, p.IsPath → 5 ≤ p.length) →
      (∀ v ∈ T, (H.neighborSet v).ncard = 2) →
      (∀ v, v ≠ z → v ∉ T → (H.neighborSet v).ncard = 3) →
      (∀ x, f x = true ↔ ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true) →
      ∀ s, s + 5 < 2 * n → HasCircuitSize n f s →
      ∃ v, v ≠ z ∧ v ∉ T ∧ ∃ t, t + 4 ≤ s ∧
        HasCircuitSize n (fun x => f (Function.update x v false)) t) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), (30 : ℕ) ≤ x1 → Even x1 → x2.Colorable (2 : ℕ) → (∀ (x7 : Fin x1), (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x3 x10 = Bool.true ↔ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), x11 + (1 : ℕ) < (2 : ℕ) * x1 → PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x11 → ∃ (x14 : Fin x1) (x15 : Fin x1), x14 ≠ x15 ∧ ¬x2.Adj x14 x15 ∧ ∃ (x16 : ℕ), x16 + (8 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x3 (Function.update (Function.update x17 x14 Bool.false) x15 Bool.false)) x16 := by
  classical
  have evAnd (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have evOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have evNot (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  have evMod (m : ℕ) (l : List Bool) : (GateOp.mod m).eval l = decide (l.count true % m = 0) := rfl
  have evMaj (l : List Bool) : GateOp.maj.eval l = decide (l.length ≤ 2 * l.count true) := rfl
  let W (gs : List Gate) (x : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

  have W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
      W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
    simp [W, List.foldl_append]

  have W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
    induction gs using List.reverseRecOn with
    | nil => simp [W]
    | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

  have W_inp (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
      (W gs x).getD i false = x.getD i false := by
    induction gs using List.reverseRecOn with
    | nil => simp [W]
    | append_singleton gs g ih =>
      rw [W_snoc, List.getD_append _ _ _ _ (by rw [W_len]; omega)]; exact ih

  have W_oob (gs : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + gs.length ≤ i) :
      (W gs x).getD i false = false := by
    apply List.getD_eq_default; rw [W_len]; exact hi

  have W_spec (gs : List Gate) (x : List Bool) : ∀ (k : ℕ) (g : Gate), gs[k]? = some g →
      (W gs x).getD (x.length + k) false =
        g.op.eval (g.inputs.map fun i =>
          if i < x.length + k then (W gs x).getD i false else false) := by
    induction gs using List.reverseRecOn with
    | nil => intro k g h; simp at h
    | append_singleton gs a ih =>
      intro k g h
      rw [W_snoc]
      rcases Nat.lt_or_ge k gs.length with hk | hk
      · rw [List.getElem?_append_left hk] at h
        rw [List.getD_append _ _ _ _ (by rw [W_len]; omega), ih k g h]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < x.length + k
        · simp only [hi, if_true]
          rw [List.getD_append _ _ _ _ (by rw [W_len]; omega)]
        · simp only [hi, if_false]
      · rcases Nat.lt_or_ge k (gs.length + 1) with hk1 | hk1
        · have hk2 : k = gs.length := by omega
          subst hk2
          have hag : a = g := by simpa using h
          subst hag
          rw [List.getD_append_right _ _ _ _ (by rw [W_len]), W_len]
          simp only [Nat.sub_self, List.getD_cons_zero]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hi : i < x.length + gs.length
          · simp only [hi, if_true]
            rw [List.getD_append _ _ _ _ (by rw [W_len]; omega)]
          · simp only [hi, if_false]
            exact W_oob gs x i (by omega)
        · rw [List.getElem?_eq_none (by simp; omega)] at h
          cases h

  let sh (p : ℕ) (i : ℕ) : ℕ := if p < i then i - 1 else i

  let up (p : ℕ) (m : ℕ) : ℕ := if m < p then m else m + 1

  let del (G : List Gate) (j : ℕ) (T : Gate → Gate) : List Gate :=
    G.take j ++ (G.drop (j + 1)).map T

  have del_len (G : List Gate) (j : ℕ) (T : Gate → Gate) (hj : j < G.length) :
      (del G j T).length + 1 = G.length := by
    simp [del]; omega

  have del_lt (G : List Gate) (j : ℕ) (T : Gate → Gate) (k : ℕ) (g : Gate) (hj : j < G.length)
      (hk : k < j) (h : (del G j T)[k]? = some g) : G[k]? = some g := by
    unfold del at h
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_take] at h
    simpa [hk] using h

  have del_ge (G : List Gate) (j : ℕ) (T : Gate → Gate) (k : ℕ) (g : Gate) (hj : j < G.length)
      (hk : j ≤ k) (h : (del G j T)[k]? = some g) : ∃ g0, G[k + 1]? = some g0 ∧ g = T g0 := by
    unfold del at h
    rw [List.getElem?_append_right (by simp; omega)] at h
    simp only [List.length_take, List.getElem?_map, List.getElem?_drop] at h
    have e : j + 1 + (k - min j G.length) = k + 1 := by
      rw [Nat.min_eq_left (by omega)]; omega
    rw [e] at h
    cases hg : G[k + 1]? with
    | none => rw [hg] at h; simp at h
    | some g0 => rw [hg] at h; exact ⟨g0, rfl, by simpa using h.symm⟩

  have sim (G : List Gate) (j : ℕ) (T : Gate → Gate) (x : List Bool) (n : ℕ) (hx : x.length = n)
      (hj : j < G.length)
      (hT : ∀ (k : ℕ) (g : Gate), j ≤ k → G[k + 1]? = some g → ∀ ρ ρ' : ℕ → Bool,
        (∀ i, i ≠ n + j → ρ' (sh (n + j) i) = ρ i) →
        ρ (n + j) = (W G x).getD (n + j) false →
        (∀ i, i < n + j → ρ i = (W G x).getD i false) →
        (∀ i, i < n → ρ' i = x.getD i false) →
        (∀ i, n + G.length ≤ i + 1 → ρ' i = false) →
        (T g).op.eval ((T g).inputs.map ρ') = g.op.eval (g.inputs.map ρ)) :
      ∀ m, (W (del G j T) x).getD m false = (W G x).getD (up (n + j) m) false := by
    subst hx
    have hlen := del_len G j T hj
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    rcases Nat.lt_or_ge m x.length with hm | hm
    · rw [W_inp _ _ _ hm, show up (x.length + j) m = m by simp only [up]; split_ifs <;> omega,
        W_inp _ _ _ hm]
    · obtain ⟨k, rfl⟩ : ∃ k, m = x.length + k := ⟨m - x.length, by omega⟩
      rcases Nat.lt_or_ge k (del G j T).length with hk | hk
      · have hg : (del G j T)[k]? = some (del G j T)[k] := List.getElem?_eq_getElem hk
        rw [W_spec _ _ k _ hg]
        rcases Nat.lt_or_ge k j with hkj | hkj
        · have hg0 := del_lt G j T k _ hj hkj hg
          rw [show up (x.length + j) (x.length + k) = x.length + k by
            simp only [up]; split_ifs <;> omega, W_spec _ _ k _ hg0]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hi : i < x.length + k
          · simp only [hi, if_true]
            rw [ih i hi, show up (x.length + j) i = i by simp only [up]; split_ifs <;> omega]
          · simp only [hi, if_false]
        · obtain ⟨g0, hg0, hgT⟩ := del_ge G j T k _ hj hkj hg
          rw [show up (x.length + j) (x.length + k) = x.length + (k + 1) by
            simp only [up]; split_ifs <;> omega, W_spec _ _ (k + 1) _ hg0, hgT]
          apply hT k g0 hkj hg0
          · intro i hi
            by_cases h1 : x.length + j < i
            · have e1 : sh (x.length + j) i = i - 1 := by simp only [sh]; split_ifs; rfl
              rw [e1]
              by_cases h2 : i < x.length + (k + 1)
              · have h3 : i - 1 < x.length + k := by omega
                simp only [h2, h3, if_true]
                rw [ih (i - 1) h3]
                congr 1
                simp only [up]; split_ifs <;> omega
              · have h3 : ¬ i - 1 < x.length + k := by omega
                simp only [h2, h3, if_false]
            · have e1 : sh (x.length + j) i = i := by simp only [sh]; split_ifs; rfl
              rw [e1]
              have h2 : i < x.length + (k + 1) := by omega
              have h3 : i < x.length + k := by omega
              simp only [h2, h3, if_true]
              rw [ih i h3]
              congr 1
              simp only [up]; split_ifs <;> omega
          · have h2 : x.length + j < x.length + (k + 1) := by omega
            simp only [h2, if_true]
          · intro i hi
            have h2 : i < x.length + (k + 1) := by omega
            simp only [h2, if_true]
          · intro i hi
            have h3 : i < x.length + k := by omega
            simp only [h3, if_true]
            exact W_inp _ _ _ hi
          · intro i hi
            have h3 : ¬ i < x.length + k := by omega
            simp only [h3, if_false]
      · rw [W_oob _ _ _ (by omega), W_oob _ _ _ (by simp only [up]; split_ifs <;> omega)]

  let Ts (p t : ℕ) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map fun i => if i = p then t else sh p i⟩

  have Ts_eval (p t : ℕ) (g : Gate) (ρ ρ' : ℕ → Bool)
      (h1 : ∀ i, i ≠ p → ρ' (sh p i) = ρ i) (hp : ρ' t = ρ p) :
      (Ts p t g).op.eval ((Ts p t g).inputs.map ρ') = g.op.eval (g.inputs.map ρ) := by
    simp only [Ts, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    by_cases hi : i = p
    · subst hi; simp only [Function.comp, if_true]; exact hp
    · simp only [Function.comp, hi, if_false]; exact h1 i hi

  have ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
      (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp

  let Rn (v B : ℕ) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map fun i => if i = v then B else i⟩

  have subst (G : List Gate) (n v : ℕ) (hv : v < n) (x y : List Bool) (hx : x.length = n)
      (hy : y.length = n)
      (hxy : ∀ i, i < n → i ≠ v → x.getD i false = y.getD i false)
      (hyv : y.getD v false = false) :
      ∀ m, m ≠ v →
        (W (G.map (Rn v (n + G.length))) x).getD m false = (W G y).getD m false := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro hmv
    rcases Nat.lt_or_ge m n with hm | hm
    · rw [W_inp (G.map (Rn v (n + G.length))) x m (by omega), W_inp G y m (by omega)]
      exact hxy m hm hmv
    · obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
      rcases Nat.lt_or_ge k G.length with hk | hk
      · have hg : G[k]? = some G[k] := List.getElem?_eq_getElem hk
        have hg1 : (G.map (Rn v (n + G.length)))[k]? = some (Rn v (n + G.length) G[k]) := by
          rw [List.getElem?_map, hg]; rfl
        have e1 := W_spec (G.map (Rn v (n + G.length))) x k _ hg1
        have e2 := W_spec G y k _ hg
        rw [hx] at e1
        rw [hy] at e2
        rw [e1, e2]
        simp only [Rn, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        simp only [Function.comp_apply]
        by_cases hi : i = v
        · have h1 : ¬ (n + G.length < n + k) := by omega
          have h2 : i < n + k := by omega
          rw [if_pos hi, if_neg h1, if_pos h2, hi, W_inp G y v (by omega)]
          exact hyv.symm
        · rw [if_neg hi]
          by_cases h2 : i < n + k
          · rw [if_pos h2, if_pos h2]; exact ih i h2 hi
          · rw [if_neg h2, if_neg h2]
      · rw [W_oob (G.map (Rn v (n + G.length))) x (n + k) (by rw [List.length_map]; omega),
          W_oob G y (n + k) (by omega)]

  let Tt (p : ℕ) (g : Gate) : Gate :=
    GateOp.rec (motive := fun _ => Gate)
      ⟨GateOp.and, (g.inputs.filter fun i => decide (i ≠ p)).map (sh p)⟩
      (if p ∈ g.inputs then ⟨GateOp.and, []⟩ else ⟨GateOp.or, g.inputs.map (sh p)⟩)
      (if g.inputs.head? = some p then ⟨GateOp.or, []⟩ else ⟨GateOp.not, g.inputs.map (sh p)⟩)
      (fun _ => g) g g.op

  have all_filter (p : ℕ) (ρ ρ' : ℕ → Bool) (h1 : ∀ i, i ≠ p → ρ' (sh p i) = ρ i)
      (hp : ρ p = true) (l : List ℕ) :
      ((((l.filter fun i => decide (i ≠ p)).map (sh p)).map ρ').all id) = ((l.map ρ).all id) := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      by_cases ha : a = p
      · have e : ((a :: l).filter fun i => decide (i ≠ p)) = (l.filter fun i => decide (i ≠ p)) := by
          simp [List.filter_cons, ha]
        rw [e, ih]
        simp [ha, hp]
      · have e : ((a :: l).filter fun i => decide (i ≠ p))
            = a :: (l.filter fun i => decide (i ≠ p)) := by
          simp [List.filter_cons, ha]
        rw [e]
        simp only [List.map_cons, List.all_cons]
        rw [ih, h1 a ha]

  have Tt_eval (p : ℕ) (g : Gate)
      (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (ρ ρ' : ℕ → Bool)
      (h1 : ∀ i, i ≠ p → ρ' (sh p i) = ρ i) (hp : ρ p = true) :
      (Tt p g).op.eval ((Tt p g).inputs.map ρ') = g.op.eval (g.inputs.map ρ) := by
    obtain ⟨op, inputs⟩ := g
    cases op with
    | and =>
      simp only [Tt, evAnd, evOr, evNot, evMod, evMaj]
      exact all_filter p ρ ρ' h1 hp inputs
    | or =>
      by_cases hm : p ∈ inputs
      · simp only [Tt, hm, if_true, evAnd, evOr, evNot, evMod, evMaj]
        simp only [List.map_nil, List.all_nil]
        symm
        rw [List.any_eq_true]
        exact ⟨true, List.mem_map.mpr ⟨p, hm, hp⟩, rfl⟩
      · simp only [Tt, hm, if_false, evAnd, evOr, evNot, evMod, evMaj, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact h1 i (fun h => hm (h ▸ hi))
    | not =>
      cases inputs with
      | nil => simp [Tt, evAnd, evOr, evNot, evMod, evMaj]
      | cons a l =>
        by_cases ha : a = p
        · subst ha; simp [Tt, evAnd, evOr, evNot, evMod, evMaj, hp]
        · simp [Tt, evAnd, evOr, evNot, evMod, evMaj, ha, h1 a ha]
    | mod m => simp at hop
    | maj => simp at hop

  have Tt_fan (p : ℕ) (g : Gate)
      (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      (Tt p g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        (Tt p g).inputs.length ≤ 2 := by
    obtain ⟨op, inputs⟩ := g
    obtain ⟨hop, hl⟩ := h
    cases op with
    | and =>
      refine ⟨by simp [Tt], ?_⟩
      simp only [Tt, List.length_map]
      exact le_trans (List.length_filter_le _ _) hl
    | or =>
      by_cases hm : p ∈ inputs
      · simp [Tt, hm]
      · refine ⟨by simp [Tt, hm], ?_⟩
        simp only [Tt, hm, if_false, List.length_map]
        exact hl
    | not =>
      by_cases hm : inputs.head? = some p
      · simp [Tt, hm]
      · refine ⟨by simp [Tt, hm], ?_⟩
        simp only [Tt, hm, if_false, List.length_map]
        exact hl
    | mod m => simp at hop
    | maj => simp at hop

  have Ts_fan (p t : ℕ) (g : Gate)
      (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      (Ts p t g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        (Ts p t g).inputs.length ≤ 2 := by
    refine ⟨h.1, ?_⟩
    simp only [Ts, List.length_map]
    exact h.2

  let FT (G : List Gate) : Prop :=
    ∀ g ∈ G, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

  let eff (g : Gate) : List ℕ :=
    g.inputs.take (bif g.op.eval [false] then 1 else 2)

  let Red (n : ℕ) (G : List Gate) (j : ℕ) : Prop :=
    (∃ b : Bool, ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD (n + j) false = b) ∨
    (∃ o, o < n + j ∧ ∀ x : Fin n → Bool,
      (W G (List.ofFn x)).getD (n + j) false = (W G (List.ofFn x)).getD o false)

  have fin2 (n : ℕ) (h : (Fin n → Bool) → Bool) (G : List Gate) (out : ℕ) (hF : FT G)
      (hf : ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD out false = h x)
      (j : ℕ) (hj : j < G.length) (T : Gate → Gate)
      (hTF : ∀ g ∈ G, (T g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        (T g).inputs.length ≤ 2)
      (hT : ∀ (x : Fin n → Bool) (k : ℕ) (g : Gate), j ≤ k → G[k + 1]? = some g →
        ∀ ρ ρ' : ℕ → Bool,
        (∀ i, i ≠ n + j → ρ' (sh (n + j) i) = ρ i) →
        ρ (n + j) = (W G (List.ofFn x)).getD (n + j) false →
        (∀ i, i < n + j → ρ i = (W G (List.ofFn x)).getD i false) →
        (∀ i, i < n → ρ' i = (List.ofFn x).getD i false) →
        (∀ i, n + G.length ≤ i + 1 → ρ' i = false) →
        (T g).op.eval ((T g).inputs.map ρ') = g.op.eval (g.inputs.map ρ))
      (ho : out = n + j → ∃ o, o < n + j ∧
        ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD o false = h x) :
      ∃ (G' : List Gate) (out' : ℕ), FT G' ∧ G'.length + 1 = G.length ∧
        (∀ x : Fin n → Bool, (W G' (List.ofFn x)).getD out' false = h x) ∧
        ∀ (x : Fin n → Bool) (m : ℕ), m < n + j →
          (W G' (List.ofFn x)).getD m false = (W G (List.ofFn x)).getD m false := by
    have key : ∀ (x : Fin n → Bool) (m : ℕ),
        (W (del G j T) (List.ofFn x)).getD m false
          = (W G (List.ofFn x)).getD (up (n + j) m) false := by
      intro x
      exact sim G j T (List.ofFn x) n (by simp) hj (fun k g hk hg => hT x k g hk hg)
    have hlen := del_len G j T hj
    have hFT : FT (del G j T) := by
      intro g hg
      unfold del at hg
      rcases List.mem_append.mp hg with h1 | h1
      · exact hF g (List.mem_of_mem_take h1)
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h1
        exact hTF g0 (List.mem_of_mem_drop hg0)
    have hlow : ∀ (x : Fin n → Bool) (m : ℕ), m < n + j →
        (W (del G j T) (List.ofFn x)).getD m false = (W G (List.ofFn x)).getD m false := by
      intro x m hm
      rw [key x m, show up (n + j) m = m by simp only [up]; split_ifs <;> omega]
    by_cases hout : out = n + j
    · obtain ⟨o, hon, hox⟩ := ho hout
      exact ⟨del G j T, o, hFT, hlen, fun x => by rw [hlow x o hon]; exact hox x, hlow⟩
    · refine ⟨del G j T, sh (n + j) out, hFT, hlen, ?_, hlow⟩
      intro x
      rw [key x, ← hf x]
      congr 1
      simp only [up, sh]
      split_ifs <;> omega

  have sdl (n : ℕ) (h : (Fin n → Bool) → Bool) (hnc : ∃ x y : Fin n → Bool, h x ≠ h y)
      (G : List Gate) (out : ℕ) (hF : FT G)
      (hf : ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD out false = h x)
      (j : ℕ) (hj : j < G.length) (hR : Red n G j) :
      ∃ (G' : List Gate) (out' : ℕ), FT G' ∧ G'.length + 1 = G.length ∧
        (∀ x : Fin n → Bool, (W G' (List.ofFn x)).getD out' false = h x) ∧
        ∀ (x : Fin n → Bool) (m : ℕ), m < n + j →
          (W G' (List.ofFn x)).getD m false = (W G (List.ofFn x)).getD m false := by
    rcases hR with ⟨b, hb⟩ | ⟨o, hoj, hoe⟩
    · have ho : out = n + j → ∃ o, o < n + j ∧
          ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD o false = h x := by
        intro hout
        exfalso
        obtain ⟨x, y, hxy⟩ := hnc
        apply hxy
        rw [← hf x, ← hf y, hout, hb x, hb y]
      cases b with
      | false =>
        refine fin2 n h G out hF hf j hj (Ts (n + j) (n + G.length))
          (fun g hg => Ts_fan _ _ g (hF g hg)) ?_ ho
        intro x k g _ _ ρ ρ' h1 h2 h5 h3 h4
        apply Ts_eval _ _ g ρ ρ' h1
        rw [h2, hb x]
        exact h4 _ (by omega)
      | true =>
        refine fin2 n h G out hF hf j hj (Tt (n + j))
          (fun g hg => Tt_fan _ g (hF g hg)) ?_ ho
        intro x k g _ hg ρ ρ' h1 h2 h5 h3 h4
        exact Tt_eval _ g (hF g (List.mem_of_getElem? hg)).1 ρ ρ' h1 (h2.trans (hb x))
    · refine fin2 n h G out hF hf j hj (Ts (n + j) o)
        (fun g hg => Ts_fan _ _ g (hF g hg)) ?_ ?_
      · intro x k g _ _ ρ ρ' h1 h2 h5 h3 h4
        apply Ts_eval _ _ g ρ ρ' h1
        have e : sh (n + j) o = o := by
          simp only [sh]; split_ifs <;> omega
        have a1 := h1 o (by omega)
        rw [e] at a1
        rw [a1, h5 o hoj, h2]
        exact (hoe x).symm
      · intro hout
        exact ⟨o, hoj, fun x => by rw [← hoe x, ← hout]; exact hf x⟩

  have iter (n : ℕ) (h : (Fin n → Bool) → Bool) (hnc : ∃ x y : Fin n → Bool, h x ≠ h y) :
      ∀ (k : ℕ) (S : Finset ℕ), S.card = k → ∀ (G : List Gate) (out : ℕ), FT G →
        (∀ x : Fin n → Bool, (W G (List.ofFn x)).getD out false = h x) →
        (∀ j ∈ S, j < G.length ∧ Red n G j) →
        ∃ (G' : List Gate) (out' : ℕ), FT G' ∧ G'.length + k = G.length ∧
          ∀ x : Fin n → Bool, (W G' (List.ofFn x)).getD out' false = h x := by
    intro k
    induction k with
    | zero =>
      intro S _ G out hF hf _
      exact ⟨G, out, hF, rfl, hf⟩
    | succ k ih =>
      intro S hS G out hF hf hR
      have hne : S.Nonempty := by
        rw [← Finset.card_pos]; omega
      obtain ⟨hj, hRj⟩ := hR (S.max' hne) (S.max'_mem hne)
      obtain ⟨G1, out1, hF1, hl1, hf1, hlow⟩ := sdl n h hnc G out hF hf (S.max' hne) hj hRj
      have hR1 : ∀ i ∈ S.erase (S.max' hne), i < G1.length ∧ Red n G1 i := by
        intro i hi
        have hlt : i < S.max' hne := Finset.lt_max'_of_mem_erase_max' S hne hi
        obtain ⟨_, hRi⟩ := hR i (Finset.mem_of_mem_erase hi)
        refine ⟨by omega, ?_⟩
        rcases hRi with ⟨b, hb⟩ | ⟨o, ho, hoe⟩
        · exact Or.inl ⟨b, fun x => by rw [hlow x _ (by omega)]; exact hb x⟩
        · exact Or.inr ⟨o, ho, fun x => by
            rw [hlow x _ (by omega), hlow x _ (by omega)]; exact hoe x⟩
      obtain ⟨G2, out2, hF2, hl2, hf2⟩ := ih (S.erase (S.max' hne))
        (by rw [Finset.card_erase_of_mem (S.max'_mem hne)]; omega) G1 out1 hF1 hf1 hR1
      exact ⟨G2, out2, hF2, by omega, hf2⟩

  have gl0 (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
      (hlen : g.inputs.length ≤ 2) (q : ℕ) (c : Bool) (hq : q ∈ eff g) :
      (∃ b : Bool, ∀ ρ : ℕ → Bool, ρ q = c → g.op.eval (g.inputs.map ρ) = b) ∨
      (∃ w : ℕ, ∀ ρ : ℕ → Bool, ρ q = c → g.op.eval (g.inputs.map ρ) = ρ w) := by
    obtain ⟨op, inputs⟩ := g
    cases op with
    | and =>
      rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp [eff, evAnd, evOr, evNot, evMod, evMaj] at hq
      · simp [eff, evAnd, evOr, evNot, evMod, evMaj] at hq
        subst hq
        exact Or.inl ⟨c, fun ρ hρ => by simp [evAnd, evOr, evNot, evMod, evMaj, hρ]⟩
      · simp [eff, evAnd, evOr, evNot, evMod, evMaj] at hq
        cases c with
        | false =>
          exact Or.inl ⟨false, fun ρ hρ => by
            rcases hq with rfl | rfl <;> simp [evAnd, evOr, evNot, evMod, evMaj, hρ]⟩
        | true =>
          rcases hq with rfl | rfl
          · exact Or.inr ⟨b, fun ρ hρ => by simp [evAnd, evOr, evNot, evMod, evMaj, hρ]⟩
          · exact Or.inr ⟨a, fun ρ hρ => by simp [evAnd, evOr, evNot, evMod, evMaj, hρ]⟩
      · simp at hlen
    | or =>
      rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp [eff, evAnd, evOr, evNot, evMod, evMaj] at hq
      · simp [eff, evAnd, evOr, evNot, evMod, evMaj] at hq
        subst hq
        exact Or.inl ⟨c, fun ρ hρ => by simp [evAnd, evOr, evNot, evMod, evMaj, hρ]⟩
      · simp [eff, evAnd, evOr, evNot, evMod, evMaj] at hq
        cases c with
        | true =>
          exact Or.inl ⟨true, fun ρ hρ => by
            rcases hq with rfl | rfl <;> simp [evAnd, evOr, evNot, evMod, evMaj, hρ]⟩
        | false =>
          rcases hq with rfl | rfl
          · exact Or.inr ⟨b, fun ρ hρ => by simp [evAnd, evOr, evNot, evMod, evMaj, hρ]⟩
          · exact Or.inr ⟨a, fun ρ hρ => by simp [evAnd, evOr, evNot, evMod, evMaj, hρ]⟩
      · simp at hlen
    | not =>
      rcases inputs with _ | ⟨a, l⟩
      · simp [eff, evAnd, evOr, evNot, evMod, evMaj] at hq
      · simp [eff, evAnd, evOr, evNot, evMod, evMaj] at hq
        subst hq
        exact Or.inl ⟨!c, fun ρ hρ => by simp [evAnd, evOr, evNot, evMod, evMaj, hρ]⟩
    | mod m => simp at hop
    | maj => simp at hop

  have gl (n : ℕ) (G : List Gate) (k : ℕ) (g : Gate) (hg : G[k]? = some g)
      (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
      (hlen : g.inputs.length ≤ 2) (q : ℕ) (c : Bool) (hq : q ∈ eff g)
      (hc : ∀ x : Fin n → Bool,
        (if q < n + k then (W G (List.ofFn x)).getD q false else false) = c) :
      Red n G k := by
    have key : ∀ x : Fin n → Bool, (W G (List.ofFn x)).getD (n + k) false =
        g.op.eval (g.inputs.map fun i =>
          if i < n + k then (W G (List.ofFn x)).getD i false else false) := by
      intro x
      have e := W_spec G (List.ofFn x) k g hg
      rw [List.length_ofFn] at e
      exact e
    rcases gl0 g hop hlen q c hq with ⟨b, hb⟩ | ⟨w, hw⟩
    · exact Or.inl ⟨b, fun x => by
        rw [key x]
        exact hb (fun i => if i < n + k then (W G (List.ofFn x)).getD i false else false) (hc x)⟩
    · by_cases hwk : w < n + k
      · exact Or.inr ⟨w, hwk, fun x => by
          rw [key x,
            hw (fun i => if i < n + k then (W G (List.ofFn x)).getD i false else false) (hc x)]
          exact if_pos hwk⟩
      · exact Or.inl ⟨false, fun x => by
          rw [key x,
            hw (fun i => if i < n + k then (W G (List.ofFn x)).getD i false else false) (hc x)]
          exact if_neg hwk⟩

  have gv0 (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
      (hnor : g.op ≠ GateOp.or) (q : ℕ) (hq : q ∈ eff g) :
      (g.op = GateOp.and ∧ ∀ ρ : ℕ → Bool, g.op.eval (g.inputs.map ρ) = true → ρ q = true) ∨
      (g.op = GateOp.not ∧ ∀ ρ : ℕ → Bool, g.op.eval (g.inputs.map ρ) = !ρ q) := by
    obtain ⟨op, inputs⟩ := g
    cases op with
    | and =>
      refine Or.inl ⟨rfl, ?_⟩
      intro ρ he
      have hq' : q ∈ inputs := List.mem_of_mem_take hq
      simp only [evAnd, evOr, evNot, evMod, evMaj] at he
      exact List.all_eq_true.mp he (ρ q) (List.mem_map.mpr ⟨q, hq', rfl⟩)
    | or => exact absurd rfl hnor
    | not =>
      rcases inputs with _ | ⟨a, l⟩
      · simp [eff, evAnd, evOr, evNot, evMod, evMaj] at hq
      · simp [eff, evAnd, evOr, evNot, evMod, evMaj] at hq
        subst hq
        exact Or.inr ⟨rfl, fun ρ => by simp [evAnd, evOr, evNot, evMod, evMaj]⟩
    | mod m => simp at hop
    | maj => simp at hop

  have gl2 (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
      (hlen : g.inputs.length ≤ 2) (v p : ℕ) (hvp : v ≠ p) (hv : v ∈ eff g) (hp : p ∈ eff g) :
      (∀ ρ : ℕ → Bool, g.op.eval (g.inputs.map ρ) = (ρ v && ρ p)) ∨
      (∀ ρ : ℕ → Bool, g.op.eval (g.inputs.map ρ) = (ρ v || ρ p)) := by
    obtain ⟨op, inputs⟩ := g
    cases op with
    | and =>
      rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp [eff, evAnd, evOr, evNot, evMod, evMaj] at hv
      · simp [eff, evAnd, evOr, evNot, evMod, evMaj] at hv hp
        omega
      · simp [eff, evAnd, evOr, evNot, evMod, evMaj] at hv hp
        left
        intro ρ
        rcases hv with rfl | rfl <;> rcases hp with rfl | rfl
        · exact absurd rfl hvp
        · simp [evAnd, evOr, evNot, evMod, evMaj]
        · simp [evAnd, evOr, evNot, evMod, evMaj, Bool.and_comm]
        · exact absurd rfl hvp
      · simp at hlen
    | or =>
      rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
      · simp [eff, evAnd, evOr, evNot, evMod, evMaj] at hv
      · simp [eff, evAnd, evOr, evNot, evMod, evMaj] at hv hp
        omega
      · simp [eff, evAnd, evOr, evNot, evMod, evMaj] at hv hp
        right
        intro ρ
        rcases hv with rfl | rfl <;> rcases hp with rfl | rfl
        · exact absurd rfl hvp
        · simp [evAnd, evOr, evNot, evMod, evMaj]
        · simp [evAnd, evOr, evNot, evMod, evMaj, Bool.or_comm]
        · exact absurd rfl hvp
      · simp at hlen
    | not =>
      rcases inputs with _ | ⟨a, l⟩
      · simp [eff, evAnd, evOr, evNot, evMod, evMaj] at hv
      · simp [eff, evAnd, evOr, evNot, evMod, evMaj] at hv hp
        omega
    | mod m => simp at hop
    | maj => simp at hop

  have Ts_dead (p t : ℕ) (g : Gate)
      (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
      (hlen : g.inputs.length ≤ 2) (hne : p ∉ eff g) (ρ ρ' : ℕ → Bool)
      (h1 : ∀ i, i ≠ p → ρ' (sh p i) = ρ i) :
      (Ts p t g).op.eval ((Ts p t g).inputs.map ρ') = g.op.eval (g.inputs.map ρ) := by
    obtain ⟨op, inputs⟩ := g
    cases op with
    | and =>
      have e : eff ⟨GateOp.and, inputs⟩ = inputs := List.take_of_length_le hlen
      rw [e] at hne
      simp only [Ts, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hip : i ≠ p := fun h => hne (h ▸ hi)
      simp only [Function.comp, hip, if_false]
      exact h1 i hip
    | or =>
      have e : eff ⟨GateOp.or, inputs⟩ = inputs := List.take_of_length_le hlen
      rw [e] at hne
      simp only [Ts, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hip : i ≠ p := fun h => hne (h ▸ hi)
      simp only [Function.comp, hip, if_false]
      exact h1 i hip
    | not =>
      rcases inputs with _ | ⟨a, l⟩
      · simp [Ts, evAnd, evOr, evNot, evMod, evMaj]
      · have ha : a ≠ p := by
          intro h
          apply hne
          simp [eff, evAnd, evOr, evNot, evMod, evMaj, h]
        simp [Ts, evAnd, evOr, evNot, evMod, evMaj, ha, h1 a ha]
    | mod m => simp at hop
    | maj => simp at hop

  have pos_set (l : List Gate) (p : Gate → Bool) :
      ∃ S : Finset ℕ, S.card = (l.filter p).length ∧
        ∀ i ∈ S, ∃ g, l[i]? = some g ∧ p g = true := by
    induction l using List.reverseRecOn with
    | nil => exact ⟨∅, by simp, by simp⟩
    | append_singleton l a ih =>
      obtain ⟨S, hS, hSp⟩ := ih
      have hlt : ∀ i ∈ S, i < l.length := by
        intro i hi
        obtain ⟨g, hg, _⟩ := hSp i hi
        by_contra hcon
        rw [List.getElem?_eq_none (by omega)] at hg
        cases hg
      by_cases hpa : p a = true
      · refine ⟨insert l.length S, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem (fun hm => by have := hlt _ hm; omega), hS]
          simp [List.filter_append, hpa]
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact ⟨a, by simp, hpa⟩
          · obtain ⟨g, hg, hpg⟩ := hSp i hi
            exact ⟨g, by rw [List.getElem?_append_left (hlt i hi)]; exact hg, hpg⟩
      · refine ⟨S, ?_, ?_⟩
        · rw [hS]; simp [List.filter_append, hpa]
        · intro i hi
          obtain ⟨g, hg, hpg⟩ := hSp i hi
          exact ⟨g, by rw [List.getElem?_append_left (hlt i hi)]; exact hg, hpg⟩

  have eff_Rn (v B : ℕ) (g : Gate) :
      eff (Rn v B g) = (eff g).map fun i => if i = v then B else i := by
    simp [eff, Rn, List.map_take]

  have core (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit) (v : Fin n)
      (hF : FT C.gates)
      (hf : ∀ x : Fin n → Bool, (W C.gates (List.ofFn x)).getD C.output false = f x)
      (hmin : ∀ (G' : List Gate) (out' : ℕ), FT G' →
        (∀ x : Fin n → Bool, (W G' (List.ofFn x)).getD out' false = f x) →
        C.gates.length ≤ G'.length)
      (hnc : ∃ x y : Fin n → Bool,
        f (Function.update x v false) ≠ f (Function.update y v false))
      (hR : 4 ≤ (C.gates.filter fun g => (eff g).contains v.val).length ∨
        (C.gates.filter fun g => (eff g).contains v.val).length = 3 ∧
          ∃ g ∈ C.gates.filter fun g => (eff g).contains v.val, g.op ≠ GateOp.or) :
      ∃ (G' : List Gate) (out' : ℕ), FT G' ∧ G'.length + 4 ≤ C.gates.length ∧
        ∀ x : Fin n → Bool,
          (W G' (List.ofFn x)).getD out' false = f (Function.update x v false) := by
    obtain ⟨B, hB⟩ : ∃ B, B = n + C.gates.length := ⟨_, rfl⟩
    obtain ⟨G1, hG1⟩ : ∃ G1, G1 = C.gates.map (Rn v.val B) := ⟨_, rfl⟩
    obtain ⟨o1, ho1⟩ : ∃ o1, o1 = if C.output = v.val then B else C.output := ⟨_, rfl⟩
    have hlen1 : G1.length = C.gates.length := by rw [hG1, List.length_map]
    have hS : ∀ x : Fin n → Bool, ∀ m, m ≠ v.val →
        (W G1 (List.ofFn x)).getD m false
          = (W C.gates (List.ofFn (Function.update x v false))).getD m false := by
      intro x
      rw [hG1, hB]
      apply subst C.gates n v.val v.isLt (List.ofFn x) (List.ofFn (Function.update x v false))
        (by simp) (by simp)
      · intro i hi hiv
        rw [ofFn_getD x i hi, ofFn_getD (Function.update x v false) i hi,
          Function.update_apply, if_neg (fun h => hiv (congrArg Fin.val h))]
      · rw [ofFn_getD (Function.update x v false) v.val v.isLt, Function.update_apply, if_pos rfl]
    have hC1 : ∀ x : Fin n → Bool,
        (W G1 (List.ofFn x)).getD o1 false = f (Function.update x v false) := by
      intro x
      rw [← hf (Function.update x v false)]
      by_cases ho : C.output = v.val
      · rw [ho1, if_pos ho, ho, W_oob G1 (List.ofFn x) B (by rw [List.length_ofFn]; omega),
          W_inp C.gates (List.ofFn (Function.update x v false)) v.val
            (by rw [List.length_ofFn]; exact v.isLt),
          ofFn_getD (Function.update x v false) v.val v.isLt, Function.update_apply, if_pos rfl]
      · rw [ho1, if_neg ho]
        exact hS x C.output ho
    have hF1 : FT G1 := by
      intro g hg
      rw [hG1] at hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      have h0 := hF g0 hg0
      exact ⟨h0.1, by simp only [Rn, List.length_map]; exact h0.2⟩
    have hncf : ∃ x y : Fin n → Bool, f x ≠ f y := by
      obtain ⟨x, y, hxy⟩ := hnc
      exact ⟨_, _, hxy⟩
    have hget1 : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → G1[k]? = some (Rn v.val B g) := by
      intro k g hg
      rw [hG1, List.getElem?_map, hg]; rfl
    have hklt : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → k < C.gates.length := by
      intro k g hg
      by_contra hcon
      rw [List.getElem?_eq_none (by omega)] at hg
      cases hg
    have hRn1 : ∀ g ∈ C.gates, (Rn v.val B g).op ∈
        ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ (Rn v.val B g).inputs.length ≤ 2 := by
      intro g hg
      have h0 := hF g hg
      exact ⟨h0.1, by simp only [Rn, List.length_map]; exact h0.2⟩
    have hA : ∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → v.val ∈ eff g → Red n G1 k := by
      intro k g hg hv
      have hm := hRn1 g (List.mem_of_getElem? hg)
      have hk := hklt k g hg
      refine gl n G1 k (Rn v.val B g) (hget1 k g hg) hm.1 hm.2 B false ?_ ?_
      · rw [eff_Rn]
        exact List.mem_map.mpr ⟨v.val, hv, if_pos rfl⟩
      · intro x
        exact if_neg (by omega)
    have hfin : ∀ S : Finset ℕ, 4 ≤ S.card → (∀ j ∈ S, j < G1.length ∧ Red n G1 j) →
        ∃ (G' : List Gate) (out' : ℕ), FT G' ∧ G'.length + 4 ≤ C.gates.length ∧
          ∀ x : Fin n → Bool,
            (W G' (List.ofFn x)).getD out' false = f (Function.update x v false) := by
      intro S hS4 hSR
      obtain ⟨G', out', hF', hl', hf'⟩ :=
        iter n (fun x => f (Function.update x v false)) hnc S.card S rfl G1 o1 hF1 hC1 hSR
      exact ⟨G', out', hF', by omega, hf'⟩
    obtain ⟨S, hScard, hSp⟩ := pos_set C.gates (fun g => (eff g).contains v.val)
    have hSv : ∀ i ∈ S, ∃ g, C.gates[i]? = some g ∧ v.val ∈ eff g := by
      intro i hi
      obtain ⟨g, hg, hpg⟩ := hSp i hi
      exact ⟨g, hg, by simpa using hpg⟩
    have hSR : ∀ i ∈ S, i < G1.length ∧ Red n G1 i := by
      intro i hi
      obtain ⟨g, hg, hv⟩ := hSv i hi
      exact ⟨by have := hklt i g hg; omega, hA i g hg hv⟩
    rcases hR with h4 | ⟨h3, g, hgm, hgor⟩
    · exact hfin S (by omega) hSR
    · obtain ⟨hgC, hgv0⟩ := List.mem_filter.mp hgm
      have hgv : v.val ∈ eff g := by simpa using hgv0
      obtain ⟨j, hj, hjg⟩ := List.getElem_of_mem hgC
      have hgj : C.gates[j]? = some g := by rw [List.getElem?_eq_getElem hj, hjg]
      have hgF := hF g hgC
      have hkeyj : ∀ x : Fin n → Bool, (W C.gates (List.ofFn x)).getD (n + j) false =
          g.op.eval (g.inputs.map fun i =>
            if i < n + j then (W C.gates (List.ofFn x)).getD i false else false) := by
        intro x
        have e := W_spec C.gates (List.ofFn x) j g hgj
        rw [List.length_ofFn] at e
        exact e
      have hkey1 : ∀ x : Fin n → Bool, (W G1 (List.ofFn x)).getD (n + j) false =
          (Rn v.val B g).op.eval ((Rn v.val B g).inputs.map fun i =>
            if i < n + j then (W G1 (List.ofFn x)).getD i false else false) := by
        intro x
        have e := W_spec G1 (List.ofFn x) j _ (hget1 j g hgj)
        rw [List.length_ofFn] at e
        exact e
      have hBeff : B ∈ eff (Rn v.val B g) := by
        rw [eff_Rn]
        exact List.mem_map.mpr ⟨v.val, hgv, if_pos rfl⟩
      have hBj : ¬ B < n + j := by omega
      obtain ⟨c, hc⟩ : ∃ c : Bool, ∀ x : Fin n → Bool,
          (W G1 (List.ofFn x)).getD (n + j) false = c := by
        rcases gv0 (Rn v.val B g) (hRn1 g hgC).1 hgor B hBeff with ⟨_, hand⟩ | ⟨_, hnot⟩
        · refine ⟨false, fun x => ?_⟩
          rw [hkey1 x]
          apply Bool.eq_false_iff.mpr
          intro he
          have h2 := hand _ he
          rw [if_neg hBj] at h2
          cases h2
        · refine ⟨true, fun x => ?_⟩
          rw [hkey1 x, hnot, if_neg hBj]
          rfl
      by_cases hAx : ∃ (k : ℕ) (h : Gate), C.gates[k]? = some h ∧ n + j ∈ eff h ∧ v.val ∉ eff h
      · obtain ⟨k, h, hk, hph, hvh⟩ := hAx
        have hkS : k ∉ S := by
          intro hkS
          obtain ⟨g', hg', hv'⟩ := hSv k hkS
          rw [hk] at hg'
          cases hg'
          exact hvh hv'
        have hm := hRn1 h (List.mem_of_getElem? hk)
        have hkR : Red n G1 k := by
          refine gl n G1 k (Rn v.val B h) (hget1 k h hk) hm.1 hm.2 (n + j)
            (if n + j < n + k then c else false) ?_ ?_
          · rw [eff_Rn]
            exact List.mem_map.mpr ⟨n + j, hph, if_neg (by have := v.isLt; omega)⟩
          · intro x
            rw [hc x]
        refine hfin (insert k S) ?_ ?_
        · rw [Finset.card_insert_of_notMem hkS]; omega
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact ⟨by have := hklt i h hk; omega, hkR⟩
          · exact hSR i hi
      · exfalso
        have hcontra : ∀ (G' : List Gate) (out' : ℕ), FT G' → G'.length + 1 = C.gates.length →
            (∀ x : Fin n → Bool, (W G' (List.ofFn x)).getD out' false = f x) → False := by
          intro G' out' hF' hl' hf'
          have := hmin G' out' hF' hf'
          omega
        by_cases hBx : ∃ (k : ℕ) (h : Gate), C.gates[k]? = some h ∧ n + j ∈ eff h
        · obtain ⟨k, h, hk, hph⟩ := hBx
          have hvh : v.val ∈ eff h := by
            by_contra hcon
            exact hAx ⟨k, h, hk, hph, hcon⟩
          have hhF := hF h (List.mem_of_getElem? hk)
          have hkl := hklt k h hk
          have hkR : Red n C.gates k := by
            rcases Nat.lt_or_ge j k with hjk | hjk
            · have hkeyk : ∀ x : Fin n → Bool, (W C.gates (List.ofFn x)).getD (n + k) false =
                  h.op.eval (h.inputs.map fun i =>
                    if i < n + k then (W C.gates (List.ofFn x)).getD i false else false) := by
                intro x
                have e := W_spec C.gates (List.ofFn x) k h hk
                rw [List.length_ofFn] at e
                exact e
              have hvk : v.val < n + k := by have := v.isLt; omega
              have hvj : v.val < n + j := by have := v.isLt; omega
              have hpk : n + j < n + k := by omega
              have hgval := gv0 g hgF.1 hgor v.val hgv
              rcases gl2 h hhF.1 hhF.2 v.val (n + j) (by have := v.isLt; omega) hvh hph with
                hand | hor
              · have e1 : ∀ x : Fin n → Bool, (W C.gates (List.ofFn x)).getD (n + k) false =
                    ((W C.gates (List.ofFn x)).getD v.val false &&
                      (W C.gates (List.ofFn x)).getD (n + j) false) := by
                  intro x
                  rw [hkeyk x, hand, if_pos hvk, if_pos hpk]
                rcases hgval with ⟨_, hg1⟩ | ⟨_, hg2⟩
                · refine Or.inr ⟨n + j, hpk, fun x => ?_⟩
                  rw [e1 x]
                  cases hw : (W C.gates (List.ofFn x)).getD (n + j) false with
                  | false => simp
                  | true =>
                    have h2 := hg1 _ ((hkeyj x).symm.trans hw)
                    rw [if_pos hvj] at h2
                    rw [h2]; rfl
                · refine Or.inl ⟨false, fun x => ?_⟩
                  rw [e1 x, hkeyj x, hg2, if_pos hvj]
                  cases (W C.gates (List.ofFn x)).getD v.val false <;> rfl
              · have e1 : ∀ x : Fin n → Bool, (W C.gates (List.ofFn x)).getD (n + k) false =
                    ((W C.gates (List.ofFn x)).getD v.val false ||
                      (W C.gates (List.ofFn x)).getD (n + j) false) := by
                  intro x
                  rw [hkeyk x, hor, if_pos hvk, if_pos hpk]
                rcases hgval with ⟨_, hg1⟩ | ⟨_, hg2⟩
                · refine Or.inr ⟨v.val, hvk, fun x => ?_⟩
                  rw [e1 x]
                  cases hw : (W C.gates (List.ofFn x)).getD (n + j) false with
                  | false => simp
                  | true =>
                    have h2 := hg1 _ ((hkeyj x).symm.trans hw)
                    rw [if_pos hvj] at h2
                    rw [h2]; rfl
                · refine Or.inl ⟨true, fun x => ?_⟩
                  rw [e1 x, hkeyj x, hg2, if_pos hvj]
                  cases (W C.gates (List.ofFn x)).getD v.val false <;> rfl
            · exact gl n C.gates k h hk hhF.1 hhF.2 (n + j) false hph
                (fun x => if_neg (by omega))
          obtain ⟨G', out', hF', hl', hf', _⟩ := sdl n f hncf C.gates C.output hF hf k hkl hkR
          exact hcontra G' out' hF' hl' hf'
        · by_cases hout : C.output = n + j
          · obtain ⟨x, y, hxy⟩ := hnc
            apply hxy
            have ho : o1 = n + j := by
              rw [ho1, if_neg (by have := v.isLt; omega), hout]
            rw [← hC1 x, ← hC1 y, ho, hc x, hc y]
          · obtain ⟨G', out', hF', hl', hf', _⟩ := fin2 n f C.gates C.output hF hf j hj
              (Ts (n + j) 0) (fun g' hg' => Ts_fan _ _ g' (hF g' hg')) (by
                intro x k g' _ hg' ρ ρ' h1 _ _ _ _
                have hg'F := hF g' (List.mem_of_getElem? hg')
                exact Ts_dead _ _ g' hg'F.1 hg'F.2
                  (fun hcon => hBx ⟨k + 1, g', hg', hcon⟩) ρ ρ' h1)
              (fun h => absurd h hout)
            exact hcontra G' out' hF' hl' hf'

  have dense : ∀ (x1 : ℕ) (x2 : (Fin x1 → Bool) → Bool) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin x1),   PEqualNP.MetaComplexity.FanInTwo x3 →     PEqualNP.MetaComplexity.circuitFun x1 x3 = x2 →       (∀ (x7 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x2 x7 → x3.size ≤ x7) →         (∃ (x8 : Fin x1 → Bool) (x9 : Fin x1 → Bool), x2 (Function.update x8 x4 Bool.false) ≠ x2 (Function.update x9 x4 Bool.false)) →           (have x9 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x9.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x9.inputs).contains ↑x4) x3.gates;             (4 : ℕ) ≤ x9.length ∨ x9.length = (3 : ℕ) ∧ ∃ x10 ∈ x9, x10.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) →             ∃ (x10 : ℕ), x10 + (4 : ℕ) ≤ x3.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x11 : Fin x1 → Bool) => x2 (Function.update x11 x4 Bool.false)) x10 := by
    intro n f C v hF hCf hmin hnc hR
    have hf : ∀ x : Fin n → Bool,
        (W C.gates (List.ofFn x)).getD C.output false = f x :=
      fun x => congrFun hCf x
    obtain ⟨G', out', hF', hl', hf'⟩ := core n f C v hF hf
      (fun G' out' hG' hfG' => hmin G'.length ⟨⟨G', out'⟩, hG', le_refl _, hfG'⟩) hnc hR
    exact ⟨G'.length, hl', ⟨⟨G', out'⟩, hF', le_refl _, hf'⟩⟩

  let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

  have wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

  have wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
      wiresFrom (g :: gs) w =
        wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

  have wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
      wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
    induction gs₁ generalizing w with
    | nil => rfl
    | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

  have wiresFrom_length (gs : List Gate) (w : List Bool) :
      (wiresFrom gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [wiresFrom]
    | cons g gs ih =>
      rw [wiresFrom_cons, ih]
      simp
      omega

  have getD_snoc_lt (l : List Bool) (x d : Bool) (i : ℕ) (hi : i < l.length) :
      (l ++ [x]).getD i d = l.getD i d := by
    simp [List.getD, List.getElem?_append_left hi]

  have getD_snoc_eq (l : List Bool) (x d : Bool) (i : ℕ) (hi : i = l.length) :
      (l ++ [x]).getD i d = x := by
    subst hi
    simp [List.getD]

  let OkGate (g : Gate) : Prop :=
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

  have wiresFrom_agree (gs : List Gate) (B : Set ℕ) (w₁ w₂ : List Bool)
      (hlen : w₁.length = w₂.length) (hB : ∀ b ∈ B, b < w₁.length)
      (hagree : ∀ i ∉ B, w₁.getD i false = w₂.getD i false)
      (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ B) :
      (wiresFrom gs w₁).length = (wiresFrom gs w₂).length ∧
      ∀ i ∉ B, (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
    induction gs generalizing w₁ w₂ with
    | nil => exact ⟨hlen, hagree⟩
    | cons g gs ih =>
      rw [wiresFrom_cons, wiresFrom_cons]
      have hmap : (g.inputs.map fun i => w₁.getD i false) =
          (g.inputs.map fun i => w₂.getD i false) := by
        apply List.map_congr_left
        intro i hi
        exact hagree i (hread g List.mem_cons_self i hi)
      rw [hmap]
      apply ih
      · simp [hlen]
      · intro b hb; simp; have := hB b hb; omega
      · intro i hi
        by_cases hlt : i < w₁.length
        · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ (by omega)]
          exact hagree i hi
        · by_cases heq : i = w₁.length
          · rw [getD_snoc_eq _ _ _ _ heq, getD_snoc_eq _ _ _ _ (by omega)]
          · rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp; omega)]
      · intro g' hg'
        exact hread g' (List.mem_cons_of_mem _ hg')

  have ofFn_getD_lt {m : ℕ} (f : Fin m → Bool) (d : Bool) (i : ℕ) (hi : i < m) :
      (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
    rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

  let substWire (k a i : ℕ) : ℕ :=
    if i < k then i else if i = k then a else i - 1

  let substGate (k a : ℕ) (g : Gate) : Gate :=
    ⟨g.op, g.inputs.map (substWire k a)⟩

  have substGate_ok (k a : ℕ) (g : Gate) (h : OkGate g) : OkGate (substGate k a g) :=
    ⟨h.1, by simp [substGate]; exact h.2⟩

  let deleteGate (m : ℕ) (C : Circuit) (j a : ℕ) : Circuit :=
    ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) a),
      substWire (m + j) a C.output⟩

  have deleteGate_ok (m : ℕ) (C : Circuit) (j a : ℕ)
      (hok : ∀ g ∈ C.gates, OkGate g) : ∀ g ∈ (deleteGate m C j a).gates, OkGate g := by
    intro g hg
    rcases List.mem_append.1 hg with h1 | h1
    · exact hok g (List.mem_of_mem_take h1)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
      exact substGate_ok _ _ g0 (hok g0 (List.mem_of_mem_drop hg0))


  have deleteGate_len (m : ℕ) (C : Circuit) (j a : ℕ) (hj : j < C.gates.length) :
      (deleteGate m C j a).gates.length = C.gates.length - 1 := by
    simp only [deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
    omega


  have deleteGate_dead_wires (m : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
      (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs)
      (x : List Bool) (hx : x.length = m) :
      ∀ i < m + C.gates.length, i ≠ m + j →
        ((deleteGate m C j 0).wires x).getD (substWire (m + j) 0 i) false =
          (C.wires x).getD i false := by
    have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
      have h1 := List.take_append_drop j C.gates
      have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
      rw [h2] at h1
      simpa only [List.append_assoc, List.singleton_append] using h1.symm
    show ∀ i < m + C.gates.length, i ≠ m + j →
        (wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) 0)) x).getD
            (substWire (m + j) 0 i) false =
          (wiresFrom C.gates x).getD i false
    set w₂ := wiresFrom (C.gates.take j) x with hw₂
    set w₁ := wiresFrom [C.gates[j]] w₂ with hw₁
    have hw₂_len : w₂.length = m + j := by
      rw [hw₂, wiresFrom_length, hx, List.length_take, Nat.min_eq_left (by omega)]
    have hw₁_len : w₁.length = m + j + 1 := by
      rw [hw₁, wiresFrom_length, hw₂_len]; simp
    have hno_drop : ∀ g ∈ C.gates.drop (j + 1), (m + j) ∉ g.inputs := by
      intro g hg
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
      rw [List.getElem_drop]
      exact hno (j + 1 + t) (by rw [List.length_drop] at ht; omega) (by omega)
    have haux : ∀ (gs : List Gate) (w₁' w₂' : List Bool),
        w₁'.length = w₂'.length + 1 → m + j ≤ w₂'.length →
        (∀ g ∈ gs, (m + j) ∉ g.inputs) →
        (∀ i < w₁'.length, i ≠ m + j → w₂'.getD (substWire (m + j) 0 i) false = w₁'.getD i false) →
        ∀ i < (wiresFrom gs w₁').length, i ≠ m + j →
          (wiresFrom (gs.map (substGate (m + j) 0)) w₂').getD (substWire (m + j) 0 i) false =
            (wiresFrom gs w₁').getD i false := by
      intro gs
      induction gs with
      | nil =>
        intro w₁' w₂' _ _ _ hag i hi hne
        exact hag i hi hne
      | cons g rest ih =>
        intro w₁' w₂' hlen' hk' hnod hag'
        rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
        have hmap : ((substGate (m + j) 0 g).inputs.map fun i => w₂'.getD i false) =
            (g.inputs.map fun i => w₁'.getD i false) := by
          simp only [substGate, List.map_map]
          apply List.map_congr_left
          intro i hi
          simp only [Function.comp_apply]
          have hne : i ≠ m + j := fun h => hnod g List.mem_cons_self (h ▸ hi)
          by_cases hlt : i < w₁'.length
          · exact hag' i hlt hne
          · have hge : w₂'.length ≤ substWire (m + j) 0 i := by
              unfold substWire; split_ifs <;> omega
            rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
        rw [hmap]
        apply ih _ _ (by simp [hlen']) (by simp; omega)
          (fun g' hg' => hnod g' (List.mem_cons_of_mem _ hg'))
        intro i hi hne
        simp only [List.length_append, List.length_singleton] at hi
        by_cases hlt : i < w₁'.length
        · have hsublt : substWire (m + j) 0 i < w₂'.length := by
            unfold substWire; split_ifs <;> omega
          rw [getD_snoc_lt _ _ _ _ hsublt, getD_snoc_lt _ _ _ _ hlt]
          exact hag' i hlt hne
        · have hieq : i = w₁'.length := by omega
          have hsubeq : substWire (m + j) 0 i = w₂'.length := by
            unfold substWire; split_ifs <;> omega
          rw [getD_snoc_eq _ _ _ _ hsubeq, getD_snoc_eq _ _ _ _ hieq]
    intro i hi hne
    rw [wiresFrom_append, ← hw₂]
    conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
    have hlen_rhs : (wiresFrom (C.gates.drop (j + 1)) w₁).length = m + C.gates.length := by
      rw [wiresFrom_length, hw₁_len, List.length_drop]; omega
    apply haux (C.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) hno_drop _ i (by omega) hne
    intro u hu hune
    have hlt : u < m + j := by omega
    simp only [substWire, hlt, ↓reduceIte]
    rw [hw₁, wiresFrom_cons, wiresFrom_nil, getD_snoc_lt _ _ _ _ (by omega)]

  have deleteDeadGate {m : ℕ} (C : Circuit) (hok : ∀ g ∈ C.gates, OkGate g)
      (j : ℕ) (hj : j < C.gates.length)
      (hout : C.output ≠ m + j)
      (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs) :
      HasCircuitSize m (circuitFun m C) (C.gates.length - 1) := by
    refine ⟨deleteGate m C j 0, deleteGate_ok m C j 0 hok,
      by show (deleteGate m C j 0).gates.length ≤ C.gates.length - 1; rw [deleteGate_len m C j 0 hj], ?_⟩
    intro x
    show ((deleteGate m C j 0).wires (List.ofFn x)).getD (substWire (m + j) 0 C.output) false =
      (C.wires (List.ofFn x)).getD C.output false
    by_cases hlt : C.output < m + C.gates.length
    · exact deleteGate_dead_wires m C j hj hno (List.ofFn x) (by simp) C.output hlt hout
    · have hge1 : (deleteGate m C j 0).gates.length + m ≤ substWire (m + j) 0 C.output := by
        rw [deleteGate_len m C j 0 hj]
        unfold substWire
        split_ifs <;> omega
      have h1 : ((deleteGate m C j 0).wires (List.ofFn x)).length =
          m + (deleteGate m C j 0).gates.length := by
        show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
      have h2 : (C.wires (List.ofFn x)).length = m + C.gates.length := by
        show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]


  -- Vertex-cover circuit construction adapted from the upstream L-meta-173 proof.


  have live (n : ℕ) (C : Circuit) (hm : IsMinimalCircuit n C) :
      ∀ j : ℕ, j < C.gates.length → n + j ∈ C.output :: C.gates.flatMap Gate.inputs := by
    intro j hj
    by_contra hn
    have hout : C.output ≠ n + j := fun e => hn (by simp [e])
    have hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' →
        n + j ∉ C.gates[j'].inputs := by
      intro j' hj' _ hh
      exact hn (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨_, List.getElem_mem hj', hh⟩))
    obtain ⟨D, hd, hs, he⟩ := deleteDeadGate C hm.1 j hj hout hno
    have hb := hm.2 D hd (funext he)
    change C.gates.length ≤ D.gates.length at hb
    change D.gates.length ≤ C.gates.length - 1 at hs
    omega
  intro n G f hn heven hcolor hdeg hgirth hedge hfun s hs hsize
  have sizes : ∃ m, HasCircuitSize n f m := ⟨s, hsize⟩
  obtain ⟨C, hfan, hsmall, hc⟩ := Nat.find_spec sizes
  have hcomp : circuitFun n C = f := funext hc
  have hmin (m : ℕ) (hm : HasCircuitSize n f m) : C.size ≤ m :=
    hsmall.trans (Nat.find_min' sizes hm)
  have hminimal : IsMinimalCircuit n C := by
    refine ⟨hfan, fun D hD heq => hmin D.size ⟨D, hD, le_rfl, ?_⟩⟩
    intro x
    exact congrFun (heq.trans hcomp) x
  have hbudget := hmin s hsize
  let reads (v : Fin n) := C.gates.filter fun g =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
  have nonconstant (z : Fin n) :
      ∃ x y, f (Function.update x z false) ≠ f (Function.update y z false) := by
    obtain ⟨a, b, hab⟩ := hedge
    obtain ⟨u, hu⟩ : ∃ u, u ≠ z := by
      by_cases ha : a = z
      · exact ⟨b, fun hb => hab.ne (ha.trans hb.symm)⟩
      · exact ⟨a, ha⟩
    obtain ⟨v, hv, huv⟩ : ∃ v, v ≠ z ∧ G.Adj u v := by
      by_contra h
      have sub : G.neighborSet u ⊆ ({z} : Set (Fin n)) := by
        intro w hw
        by_contra hwz
        exact h ⟨w, fun e => hwz (Set.mem_singleton_iff.mpr e), hw⟩
      have bound := Set.ncard_le_ncard sub
      rw [hdeg, Set.ncard_singleton] at bound
      omega
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    have one : f (Function.update (fun _ => true) z false) = true :=
      (hfun _).mpr ⟨u, v, huv, by simp [Function.update_of_ne hu], by
        simp [Function.update_of_ne hv]⟩
    rw [one]
    intro h
    obtain ⟨i, _, _, hi, _⟩ := (hfun _).mp h
    by_cases hix : i = z
    · simp [hix] at hi
    · simp [Function.update_of_ne hix] at hi
  have fewReaders : ∃ v : Fin n, (reads v).length ≤ 1 := by
    by_contra none
    have atLeastTwo (v : Fin n) : 2 ≤ (reads v).length := by
      have h : ¬ (reads v).length ≤ 1 := fun h => none ⟨v, h⟩
      omega
    let gateReads (v : ℕ) (g : Gate) :=
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v
    have filterCount (v : ℕ) (gs : List Gate) :
        (gs.filter (gateReads v)).length ≤ (gs.flatMap Gate.inputs).count v := by
      induction gs with
      | nil => simp
      | cons g gs ih =>
        simp only [List.flatMap_cons, List.count_append, List.filter_cons]
        split
        next hv =>
          have mem : v ∈ g.inputs :=
            List.mem_of_mem_take (List.contains_iff_mem.mp hv)
          have positive := List.count_pos_iff.mpr mem
          simp only [List.length_cons]
          omega
        next => omega
    have gateSlots (gs : List Gate) (good : ∀ g ∈ gs, g.inputs.length ≤ 2) :
        (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
      induction gs with
      | nil => simp
      | cons g gs ih =>
        have gh := good g List.mem_cons_self
        have th := ih (fun e he => good e (List.mem_cons_of_mem g he))
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        omega
    have sumCount (xs : List ℕ) (S : Finset ℕ) : ∑ i ∈ S, xs.count i ≤ xs.length := by
      induction xs with
      | nil => simp
      | cons a xs ih =>
        simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
        by_cases ha : a ∈ S <;> simp [ha, Finset.sum_ite_eq] <;> omega
    let slots := C.output :: C.gates.flatMap Gate.inputs
    have inputUse : 2 * n ≤ ∑ i ∈ Finset.range n, slots.count i := by
      calc
        2 * n = ∑ _i ∈ Finset.range n, (2 : ℕ) := by simp [Nat.mul_comm]
        _ ≤ ∑ i ∈ Finset.range n, slots.count i := by
          apply Finset.sum_le_sum
          intro i hi
          have hf := filterCount i C.gates
          have hr := atLeastTwo ⟨i, Finset.mem_range.mp hi⟩
          change 2 ≤ (C.gates.filter (gateReads i)).length at hr
          simp only [slots, List.count_cons]
          omega
    have gateUse : C.gates.length ≤ ∑ i ∈ Finset.range C.gates.length, slots.count (n + i) := by
      calc
        C.gates.length = ∑ _i ∈ Finset.range C.gates.length, (1 : ℕ) := by simp
        _ ≤ ∑ i ∈ Finset.range C.gates.length, slots.count (n + i) := by
          apply Finset.sum_le_sum
          intro i hi
          exact List.count_pos_iff.mpr (live n C hminimal i (Finset.mem_range.mp hi))
    have countTotal := sumCount slots (Finset.range (n + C.gates.length))
    rw [Finset.sum_range_add] at countTotal
    have slotLength : slots.length = (C.gates.flatMap Gate.inputs).length + 1 := rfl
    rw [slotLength] at countTotal
    have lengthBound := gateSlots C.gates (fun g hg => (hfan g hg).2)
    change C.gates.length ≤ s at hbudget
    omega
  have firstPin : ∃ v k, k + 4 ≤ C.size ∧
      HasCircuitSize n (fun x => f (Function.update x v false)) k := by
    by_cases ht : ∃ v : Fin n, 4 ≤ (reads v).length ∨
        (reads v).length = 3 ∧ ∃ g ∈ reads v, g.op ≠ .or
    · obtain ⟨v, hv⟩ := ht
      obtain ⟨t, ht, hb⟩ := dense n f C v hfan hcomp hmin (nonconstant v) hv
      exact ⟨v, t, ht, hb⟩
    · apply sparse n G f C hn hcolor hdeg hgirth hfun hcomp hminimal (by omega)
      · intro v
        change (reads v).length ≤ 3 ∧ ((reads v).length = 3 → ∀ g ∈ reads v, g.op = .or)
        constructor
        · by_contra h
          exact ht ⟨v, Or.inl (by omega)⟩
        · intro h g hg
          by_contra he
          exact ht ⟨v, Or.inr ⟨h, g, hg, he⟩⟩
      · exact fewReaders
  obtain ⟨z, k, hk, hfirst⟩ := firstPin
  let H := G.deleteEdges (G.incidenceSet z)
  let T := G.neighborSet z
  let cofactor := fun x : Fin n → Bool => f (Function.update x z false)
  have hAdj (a b : Fin n) : H.Adj a b ↔ G.Adj a b ∧ a ≠ z ∧ b ≠ z :=
    SimpleGraph.deleteIncidenceSet_adj
  have hsub : H ≤ G := SimpleGraph.deleteEdges_le _
  have hcycles (v : Fin n) (w : H.Walk v v) (cyc : w.IsCycle) : 7 ≤ w.length := by
    simpa using hgirth v (w.mapLe hsub) (cyc.mapLe hsub)
  have hzero : (H.neighborSet z).ncard = 0 := by
    have eq : H.neighborSet z = ∅ := by
      ext b
      change H.Adj z b ↔ False
      simp [hAdj]
    rw [eq]
    exact Set.ncard_empty (Fin n)
  have hneighbors (v : Fin n) (hv : v ≠ z) :
      H.neighborSet v = G.neighborSet v \ {z} := by
    ext b
    change H.Adj v b ↔ G.Adj v b ∧ b ∉ ({z} : Set (Fin n))
    simp [hAdj, hv]
  have hzn : z ∉ T := G.irrefl
  have avoids {a b : Fin n} (p : H.Walk a b) : a ≠ z → z ∉ p.support := by
    induction p with
    | nil =>
      intro ha
      simp [Ne.symm ha]
    | @cons a b c adj rest ih =>
      intro _
      obtain ⟨_, ha, hb⟩ := (hAdj a b).mp adj
      simpa [SimpleGraph.Walk.support_cons, Ne.symm ha] using ih hb
  have separated (a : Fin n) (ha : a ∈ T) (b : Fin n) (hb : b ∈ T)
      (hab : a ≠ b) (p : H.Walk a b) (hp : p.IsPath) : 5 ≤ p.length := by
    have haz : a ≠ z := fun h => hzn (h ▸ ha)
    have hza : G.Adj z a := ha
    have hzb : G.Adj z b := hb
    have missing : z ∉ (p.mapLe hsub).support := by
      rw [SimpleGraph.Walk.support_mapLe_eq_support]
      exact avoids p haz
    let q := (p.mapLe hsub).concat hzb.symm
    have qpath : q.IsPath := (hp.mapLe hsub).concat missing hzb.symm
    have edgeAbsent : s(z,a) ∉ q.edges := by
      change s(z,a) ∉ ((p.mapLe hsub).concat hzb.symm).edges
      rw [SimpleGraph.Walk.edges_concat, List.concat_eq_append]
      intro hm
      rcases List.mem_append.mp hm with old | last
      · exact missing ((p.mapLe hsub).fst_mem_support_of_mem_edges old)
      · have e := (Sym2.mk_eq_mk_iff (p := (z,a)) (q := (b,z))).mp (List.mem_singleton.mp last)
        rcases e with same | swapped
        · have bz : b = z := (congrArg Prod.fst same).symm
          exact hzn (bz ▸ hb)
        · exact hab (congrArg Prod.snd swapped)
    have cycle := (SimpleGraph.Walk.cons_isCycle_iff q hza).mpr ⟨qpath, edgeAbsent⟩
    have hlen := hgirth z _ cycle
    change 7 ≤ (SimpleGraph.Walk.cons hza ((p.mapLe hsub).concat hzb.symm)).length at hlen
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_concat,
      SimpleGraph.Walk.length_mapLe] at hlen
    omega
  have hdegreeTwo (v : Fin n) (hv : v ∈ T) : (H.neighborSet v).ncard = 2 := by
    have ne : v ≠ z := fun eq => hzn (eq ▸ hv)
    have mem : z ∈ G.neighborSet v := G.adj_symm hv
    rw [hneighbors v ne, Set.ncard_sdiff_singleton_of_mem mem, hdeg v]
  have hdegreeThree (v : Fin n) (hv : v ≠ z) (hvn : v ∉ T) :
      (H.neighborSet v).ncard = 3 := by
    have eq : G.neighborSet v \ {z} = G.neighborSet v := by
      ext b
      change (G.Adj v b ∧ b ∉ ({z} : Set (Fin n))) ↔ G.Adj v b
      refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
      intro hb
      have e : b = z := Set.mem_singleton_iff.mp hb
      subst b
      exact hvn h.symm
    rw [hneighbors v hv, eq, hdeg v]
  have hcofactor (x : Fin n → Bool) :
      cofactor x = true ↔ ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true := by
    change f (Function.update x z false) = true ↔ _
    rw [hfun]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      have haz : a ≠ z := by
        rintro rfl
        simp at ha
      have hbz : b ≠ z := by
        rintro rfl
        simp at hb
      exact ⟨a, b, (hAdj a b).2 ⟨hab, haz, hbz⟩,
        by simpa only [Function.update_of_ne haz] using ha,
        by simpa only [Function.update_of_ne hbz] using hb⟩
    · rintro ⟨a, b, hab, ha, hb⟩
      obtain ⟨hab, haz, hbz⟩ := (hAdj a b).1 hab
      exact ⟨a, b, hab, by simpa only [Function.update_of_ne haz] using ha,
        by simpa only [Function.update_of_ne hbz] using hb⟩
  obtain ⟨v, hv, hvn, t, ht, hnext⟩ := nextPin n H z T cofactor hn heven
    (hcolor.mono_left hsub) hcycles hzero (hdeg z) hzn separated hdegreeTwo hdegreeThree hcofactor
    k (by omega) hfirst
  refine ⟨z, v, hv.symm, hvn, t, by omega, ?_⟩
  have exchange : (fun x => cofactor (Function.update x v false)) =
      (fun x => f (Function.update (Function.update x z false) v false)) := by
    funext x
    change f (Function.update (Function.update x v false) z false) = _
    rw [Function.update_comm hv.symm]
  exact exchange ▸ hnext
