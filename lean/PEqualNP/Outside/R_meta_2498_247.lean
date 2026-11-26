import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The wire compaction follows the accepted reduction R-meta-2498-1.
set_option maxRecDepth 6000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_2498_247
    (minor : ∀ s : ℕ, HasCircuitSize 8 (fun y : Fin 8 → Bool =>
      ([(0,1),(1,2),(2,3),(0,4),(1,5),(2,6),(3,7),(4,6),(5,7),(7,4)] : List (Fin 8 × Fin 8)).any
        (fun e => y e.1 && y e.2)) s → 13 ≤ s)
    (forced01 : ∀ D : Circuit, FanInTwo D → D.size = 13 →
      (∀ y : Fin 8 → Bool, (D.wires (List.ofFn y)).getD 8 false = (y 0 || y 1)) →
      circuitFun 8 D = (fun y : Fin 8 → Bool => ([(0,1),(1,2),(2,3),(0,4),(1,5),(2,6),(3,7),(4,6),(5,7),(7,4)] : List (Fin 8 × Fin 8)).any fun e => y e.1 && y e.2) → False)
    (forced12 : ∀ D : Circuit, FanInTwo D → D.size = 13 →
      (∀ y : Fin 8 → Bool, (D.wires (List.ofFn y)).getD 8 false = (y 1 || y 2)) →
      circuitFun 8 D = (fun y : Fin 8 → Bool => ([(0,1),(1,2),(2,3),(0,4),(1,5),(2,6),(3,7),(4,6),(5,7),(7,4)] : List (Fin 8 × Fin 8)).any fun e => y e.1 && y e.2) → False)
    (tight : ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool =>
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
          x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) →
      (∀ v : Fin 9, ∀ S : Finset ℕ,
        (∀ j ∈ S, j < C.size ∧
          let w (x : Fin 9 → Bool) (i : ℕ) := (C.wires (List.ofFn x)).getD i false
          ((∃ b : Bool, ∀ x, x v = false → w x (9+j) = b) ∨
            ∃ i < 9+j, ∀ x, x v = false → w x (9+j) = w x i)) →
        S.card ≤ if v ∈ ([4,6,7] : List (Fin 9)) then 1 else 3) → 16 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ x5 ∈ [(0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))], ∀ (x7 : Finset ℕ), (∀ x8 ∈ x7, x8 < x1.size ∧ ((∃ (x10 : Bool), ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = x10) ∨ ∃ x10 < (9 : ℕ) + x8, ∀ (x11 : Fin (9 : ℕ) → Bool), x11 x5 = Bool.false → (x1.wires (List.ofFn x11)).getD ((9 : ℕ) + x8) Bool.false = (x1.wires (List.ofFn x11)).getD x10 Bool.false)) → x7.card ≤ (3 : ℕ)) → (16 : ℕ) ≤ x1.size := by
  intro C hC first correct fewDeg3
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have evalAnd (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have evalOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have evalNot (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  let H : (Fin 8 → Bool) → Bool := (fun y : Fin 8 → Bool =>
    ([(0,1),(1,2),(2,3),(0,4),(1,5),(2,6),(3,7),(4,6),(5,7),(7,4)] : List (Fin 8 × Fin 8)).any
      (fun e => y e.1 && y e.2))
  let F : (Fin 9 → Bool) → Bool := (fun x : Fin 9 → Bool =>
    ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
      List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2))
  have same : circuitFun 9 C = F := correct
  by_contra! small
  have encoded : circuitFun 9 C = (fun x : Fin 9 → Bool =>
      ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
        x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) := by
    rw [same]
    rfl
  refine absurd (tight C hC first encoded ?elim) (by omega)
  intro v S hS
  by_cases hv : v ∈ ([4,6,7] : List (Fin 9))
  · rw [ite_eq_left hv]
    by_contra! big
    have hv0 : v ≠ 0 := by
      intro h
      subst v
      exact (by decide : (0 : Fin 9) ∉ ([4,6,7] : List (Fin 9))) hv
    have hv1 : v ≠ 1 := by
      intro h
      subst v
      exact (by decide : (1 : Fin 9) ∉ ([4,6,7] : List (Fin 9))) hv
    obtain ⟨τ, hτ, hpair⟩ : ∃ τ : Fin 9 → Fin 8,
        (∀ y : Fin 8 → Bool, F (fun i => if i = v then false else y (τ i)) = H y) ∧
          ((τ 0 = 0 ∧ τ 1 = 1) ∨ (τ 0 = 1 ∧ τ 1 = 0) ∨ (τ 0 = 1 ∧ τ 1 = 2)) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact ⟨![0,1,2,3,0,4,5,6,7], by decide +kernel, by decide⟩
      · exact ⟨![1,0,4,7,5,2,0,6,3], by decide +kernel, by decide⟩
      · exact ⟨![1,2,3,7,5,0,6,0,4], by decide +kernel, by decide⟩
    have hne : τ 0 ≠ τ 1 := by
      rcases hpair with ⟨h0,h1⟩ | ⟨h0,h1⟩ | ⟨h0,h1⟩ <;> rw [h0,h1] <;> decide
    let X : (Fin 8 → Bool) → Fin 9 → Bool := fun y i => if i = v then false else y (τ i)
    have hXv (y) : X y v = false := by simp [X]
    have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
        (gs.foldl step w).getD i false = w.getD i false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        · simp [step]; omega
    have lengthOf (gs : List Gate) (w : List Bool) :
        (gs.foldl step w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons, ih]
        simp [step]; omega
    have last (w : List Bool) (b : Bool) (n : ℕ) (hn : w.length = n) :
        (w ++ [b]).getD n false = b := by
      subst hn
      simp [List.getD_eq_getElem?_getD]
    have beyond (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
    have getOf (n : ℕ) (y : Fin n → Bool) (m : Fin n) : (List.ofFn y).getD m.val false = y m := by
      simp [List.getD_eq_getElem?_getD]
    let W : (Fin 8 → Bool) → List Bool := fun y => C.wires (List.ofFn (X y))
    let N : List Gate → (Fin 8 → Bool) → List Bool := fun gs y => gs.foldl step (List.ofFn y)
    have hNlen (gs y) : (N gs y).length = 8 + gs.length := by simp [N, lengthOf]
    have hWlen (y) : (W y).length = 9 + C.gates.length := by
      change (C.gates.foldl step (List.ofFn (X y))).length = _
      simp [lengthOf]
    have keepN (gs : List Gate) (g : Gate) (i : ℕ) (hi : i < 8 + gs.length) (y) :
        (N (gs ++ [g]) y).getD i false = (N gs y).getD i false := by
      simp only [N, List.foldl_append]
      exact keep [g] _ i (by simpa [lengthOf] using hi)
    have newN (gs : List Gate) (g : Gate) (y) :
        (N (gs ++ [g]) y).getD (8 + gs.length) false =
          g.op.eval (g.inputs.map fun i => (N gs y).getD i false) := by
      simp only [N, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact last _ _ _ (by simp [lengthOf])
    have gateW (k : ℕ) (hk : k < C.gates.length) (y) :
        (W y).getD (9 + k) false =
          (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i =>
            if i < 9 + k then (W y).getD i false else false) := by
      have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by simp
      let P := (C.gates.take k).foldl step (List.ofFn (X y))
      have hP : P.length = 9 + k := by simp [P, lengthOf]; omega
      have hW : W y = (C.gates.drop (k + 1)).foldl step (step P C.gates[k]) := by
        change C.gates.foldl step (List.ofFn (X y)) = _
        conv_lhs => rw [hsplit]
        rw [List.foldl_append, List.foldl_cons]
      have hlow (i : ℕ) (hi : i < 9 + k) : (W y).getD i false = P.getD i false := by
        rw [hW, keep _ _ _ (by simp [step]; omega)]
        simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left (hP ▸ hi)]
      rw [hW, keep _ _ _ (by simp [step]; omega)]
      have h1 : (step P C.gates[k]).getD (9 + k) false =
          (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i => P.getD i false) :=
        last _ _ _ hP
      rw [h1, ← hW]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with hi
      · exact (hlow i hi).symm
      · exact beyond _ _ (by omega)
    let Good : List Gate → ℕ → Prop := fun gs i =>
      (∃ b : Bool, ∀ y, (W y).getD i false = b) ∨
      (∃ i' < 8 + gs.length, ∀ y, (W y).getD i false = (N gs y).getD i' false)
    have wFirst (y : Fin 8 → Bool) : (W y).getD 9 false = (y (τ 0) || y (τ 1)) := by
      change (C.wires (List.ofFn (X y))).getD 9 false = _
      rw [first (X y)]
      simp [X, Ne.symm hv0, Ne.symm hv1]
    have headEssential : ¬ Good [] 9 := by
      rintro (⟨b,hb⟩ | ⟨i,hi,he⟩)
      · have h0 : false = b := (wFirst (fun _ => false)).symm.trans (hb (fun _ => false))
        have h1 : true = b := (wFirst (fun _ => true)).symm.trans (hb (fun _ => true))
        exact Bool.noConfusion (h0.trans h1.symm)
      · have hi' : i < 8 := by simpa using hi
        let p : Fin 8 := ⟨i, hi'⟩
        have he' (y : Fin 8 → Bool) : (y (τ 0) || y (τ 1)) = y p := by
          rw [← wFirst, he]
          exact getOf 8 y p
        by_cases hp : p = τ 0
        · have h := he' (fun j => decide (j = τ 1))
          simp [hp, hne] at h
        · have h := he' (fun j => decide (j = τ 0))
          simp [hp] at h
    let Head (gs : List Gate) : Prop := 0 < gs.length ∧
      ∀ y : Fin 8 → Bool, (N gs y).getD 8 false = (W y).getD 9 false
    have main (k : ℕ) (hk : k ≤ C.gates.length) : ∃ gs : List Gate,
        (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          g.inputs.length ≤ 2) ∧
        gs.length + (S.filter (· < k)).card ≤ k ∧ (∀ i < 9 + k, Good gs i) ∧
        (0 < k → Head gs) := by
      induction k with
      | zero =>
        refine ⟨[], by simp, by simp, (fun i hi => ?_), by omega⟩
        have hi9 : i < 9 := by omega
        have hval (y) : (W y).getD i false = X y ⟨i, hi9⟩ := by
          change (C.gates.foldl step (List.ofFn (X y))).getD i false = _
          rw [keep _ _ _ (by simpa using hi9)]
          exact getOf 9 (X y) ⟨i, hi9⟩
        by_cases hiv : (⟨i, hi9⟩ : Fin 9) = v
        · exact Or.inl ⟨false, fun y => by rw [hval, hiv, hXv]⟩
        · refine Or.inr ⟨(τ ⟨i, hi9⟩).val, by simp, fun y => ?_⟩
          rw [hval]
          simp only [N, List.foldl_nil, getOf, X, ite_eq_right hiv]
      | succ k ih =>
        have hk' : k < C.gates.length := by omega
        obtain ⟨gs, hfan, hcount, hgood, hhead⟩ := ih (by omega)
        have hfilter : (S.filter (· < k + 1)).card ≤ (S.filter (· < k)).card + 1 := by
          have hsub : S.filter (· < k + 1) ⊆ insert k (S.filter (· < k)) := by
            intro a ha
            simp only [Finset.mem_filter, Finset.mem_insert] at ha ⊢
            rcases Nat.lt_succ_iff_lt_or_eq.mp ha.2 with h | h
            · exact Or.inr ⟨ha.1, h⟩
            · exact Or.inl h
          exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
        by_cases hG : Good gs (9 + k)
        · have hkpos : 0 < k := by
            by_contra! h
            have hk0 : k = 0 := by omega
            subst k
            have hnil : gs = [] := List.length_eq_zero_iff.mp (by omega)
            subst gs
            exact headEssential hG
          refine ⟨gs, hfan, by omega, (fun i hi => ?_), fun _ => hhead hkpos⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < (9 + k) + 1 by omega) with h | h
          · exact hgood i h
          · exact h ▸ hG
        have notConst (b : Bool) : ¬ ∀ y, (W y).getD (9 + k) false = b :=
          fun h => hG (Or.inl ⟨b, h⟩)
        have notAlias (i : ℕ) (hi : i < 9 + k) :
            ¬ ∀ y, (W y).getD (9 + k) false = (W y).getD i false := by
          intro h
          rcases hgood i hi with ⟨b, hb⟩ | ⟨i', hi', hb⟩
          · exact hG (Or.inl ⟨b, fun y => (h y).trans (hb y)⟩)
          · exact hG (Or.inr ⟨i', hi', fun y => (h y).trans (hb y)⟩)
        have hkS : k ∉ S := by
          intro hmem
          rcases (hS k hmem).2 with ⟨b, hb⟩ | ⟨i, hi, hb⟩
          · exact notConst b fun y => hb (X y) (hXv y)
          · exact notAlias i hi fun y => hb (X y) (hXv y)
        have hfilter' : S.filter (· < k + 1) = S.filter (· < k) := by
          ext a
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨h1, ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | h
            · exact h
            · exact absurd (h ▸ h1) hkS
          · rintro ⟨h1, h2⟩
            exact ⟨h1, by omega⟩
        let val : ℕ → (Fin 8 → Bool) → Bool := fun i y =>
          if i < 9 + k then (W y).getD i false else false
        have valCases (i : ℕ) : (∃ b : Bool, ∀ y, val i y = b) ∨
            (i < 9 + k ∧ ∃ i' < 8 + gs.length, ∀ y, val i y = (N gs y).getD i' false) := by
          by_cases hi : i < 9 + k
          · rcases hgood i hi with ⟨b, hb⟩ | ⟨i', hi', hb⟩
            · exact Or.inl ⟨b, fun y => by simp only [val, ite_eq_left hi]; exact hb y⟩
            · exact Or.inr ⟨hi, i', hi', fun y => by simp only [val, ite_eq_left hi]; exact hb y⟩
          · exact Or.inl ⟨false, fun y => by simp only [val, ite_eq_right hi]⟩
        have notVal (i : ℕ) : ¬ ∀ y, (W y).getD (9 + k) false = val i y := by
          intro h
          by_cases hi : i < 9 + k
          · exact notAlias i hi fun y => by rw [h y]; simp only [val, ite_eq_left hi]
          · exact notConst false fun y => by rw [h y]; simp only [val, ite_eq_right hi]
        have build : ∃ g : Gate, (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
            g.inputs.length ≤ 2) ∧ ∀ y, (W y).getD (9 + k) false =
              g.op.eval (g.inputs.map fun i => (N gs y).getD i false) := by
          have hgate := gateW k hk'
          obtain ⟨hop, hlen⟩ := hC _ (List.getElem_mem hk')
          generalize C.gates[k] = g at hgate hop hlen
          obtain ⟨op, ins⟩ := g
          have hg (y) : (W y).getD (9 + k) false = op.eval (ins.map fun i => val i y) := hgate y
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩
          · exact absurd (fun y => hg y) (notConst (op.eval []))
          · rcases hop with rfl | rfl | rfl
            · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot]) (notVal a)
            · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot]) (notVal a)
            · rcases valCases a with ⟨b, hb⟩ | ⟨_, a', _, ha'⟩
              · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notConst (!b))
              · exact ⟨⟨.not, [a']⟩, by simp, fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, ha']⟩
          · rcases hop with rfl | rfl | rfl
            · rcases valCases a with ⟨b, hb⟩ | ⟨_, a', _, ha'⟩
              · cases b
                · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notConst false)
                · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notVal c)
              rcases valCases c with ⟨b, hb⟩ | ⟨_, c', _, hc'⟩
              · cases b
                · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notConst false)
                · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notVal a)
              exact ⟨⟨.and, [a', c']⟩, by simp, fun y => by
                rw [hg y]; simp [evalAnd, evalOr, evalNot, ha', hc']⟩
            · rcases valCases a with ⟨b, hb⟩ | ⟨_, a', _, ha'⟩
              · cases b
                · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notVal c)
                · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notConst true)
              rcases valCases c with ⟨b, hb⟩ | ⟨_, c', _, hc'⟩
              · cases b
                · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notVal a)
                · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notConst true)
              exact ⟨⟨.or, [a', c']⟩, by simp, fun y => by
                rw [hg y]; simp [evalAnd, evalOr, evalNot, ha', hc']⟩
            · rcases valCases a with ⟨b, hb⟩ | ⟨_, a', _, ha'⟩
              · exact absurd (fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, hb]) (notConst (!b))
              · exact ⟨⟨.not, [a']⟩, by simp, fun y => by rw [hg y]; simp [evalAnd, evalOr, evalNot, ha']⟩
          · simp at hlen
        obtain ⟨g, hgfan, hgval⟩ := build
        refine ⟨gs ++ [g], ?_, ?_, (fun i hi => ?_), ?_⟩
        · intro g' hg'
          rcases List.mem_append.mp hg' with h | h
          · exact hfan g' h
          · rw [List.mem_singleton.mp h]; exact hgfan
        · rw [hfilter']; simp; omega
        · rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < (9 + k) + 1 by omega) with h | h
          · rcases hgood i h with ⟨b, hb⟩ | ⟨i', hi', hb⟩
            · exact Or.inl ⟨b, hb⟩
            · exact Or.inr ⟨i', by simp; omega, fun y => by rw [keepN gs g i' hi', hb y]⟩
          · subst h
            exact Or.inr ⟨8 + gs.length, by simp, fun y => by rw [newN, hgval y]⟩
        · intro _
          refine ⟨by simp, ?_⟩
          intro y
          by_cases hkpos : 0 < k
          · have hprev := hhead hkpos
            exact (keepN gs g 8 (by omega) y).trans (hprev.2 y)
          · have hk0 : k = 0 := by omega
            have hlen : gs.length = 0 := by omega
            have he := (newN gs g y).trans (hgval y).symm
            simpa [hk0, hlen] using he
    obtain ⟨gs, hfan, hcount, hgood, hhead⟩ := main C.gates.length le_rfl
    have hall : S.filter (· < C.gates.length) = S :=
      Finset.filter_true_of_mem fun j hj => (hS j hj).1
    rw [hall] at hcount
    have hout (y) : (W y).getD C.output false = H y := by
      rw [← hτ y]
      exact congrFun same (X y)
    have nonconst (b : Bool) : ¬ ∀ y, (W y).getD C.output false = b := by
      intro h
      have h0 : H (fun _ => false) = b := (hout fun _ => false).symm.trans (h fun _ => false)
      have h1 : H (fun _ => true) = b := (hout fun _ => true).symm.trans (h fun _ => true)
      have h2 : H (fun _ => false) = false := by decide
      have h3 : H (fun _ => true) = true := by decide
      rw [h2] at h0
      rw [h3] at h1
      exact absurd (h0.trans h1.symm) (by decide)
    have hsize : C.size = C.gates.length := rfl
    by_cases ho : C.output < 9 + C.gates.length
    · rcases hgood C.output ho with ⟨b, hb⟩ | ⟨o, _, hb⟩
      · exact nonconst b hb
      · let D : Circuit := ⟨gs,o⟩
        have hD : circuitFun 8 D = H := funext fun y => (hb y).symm.trans (hout y)
        have hfD : FanInTwo D := hfan
        have hmin := minor gs.length ⟨D,hfD,le_rfl,congrFun hD⟩
        have h13 : D.size = 13 := by
          change gs.length = 13
          omega
        have hlen : 0 < C.gates.length := by
          by_contra! hzero
          let y : Fin 8 → Bool := fun _ => true
          have h0 := beyond (W y) 9 (by rw [hWlen]; omega)
          rw [wFirst y] at h0
          simp [y] at h0
        have hf (y : Fin 8 → Bool) :
            (D.wires (List.ofFn y)).getD 8 false = (y (τ 0) || y (τ 1)) :=
          ((hhead hlen).2 y).trans (wFirst y)
        rcases hpair with ⟨h0,h1⟩ | ⟨h0,h1⟩ | ⟨h0,h1⟩
        · exact forced01 D hfD h13 (fun y => by simpa [h0,h1] using hf y) hD
        · exact forced01 D hfD h13 (fun y => by simpa [h0,h1,Bool.or_comm] using hf y) hD
        · exact forced12 D hfD h13 (fun y => by simpa [h0,h1] using hf y) hD
    · exact nonconst false fun y => beyond _ _ (by rw [hWlen]; omega)
  · rw [ite_eq_right hv]
    have hh : v ∈ ([0,1,2,3,5,8] : List (Fin 9)) := by
      have h : ∀ z : Fin 9, z ∉ ([4,6,7] : List (Fin 9)) →
          z ∈ ([0,1,2,3,5,8] : List (Fin 9)) := by decide
      exact h v hv
    exact fewDeg3 v hh S hS
