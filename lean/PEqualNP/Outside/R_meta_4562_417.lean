import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The elimination argument is adapted from R_meta_2498_1 (Apache 2.0).
theorem PEqualNP.Outside.R_meta_4562_417
    (minor : ∀ s : ℕ, HasCircuitSize 7 (fun y : Fin 7 → Bool =>
      ([(0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1)] : List (Fin 7 × Fin 7)).any (fun e => y e.1 && y e.2)) s → 11 ≤ s)
    (rigid : ∀ (ls : List Gate) (a b : ℕ) (C : Circuit),
      C = ⟨ls ++ [⟨GateOp.and, [a, b]⟩], 8 + ls.length⟩ → FanInTwo C → ls.length ≤ 12 →
      8 ≤ a → a < b → b < 8 + ls.length →
      (∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (([(0,1),(1,2),(2,3),(0,4),(1,5),(2,6),(3,7),(4,6),(5,7),(7,4)] : List (Fin 8 × Fin 8)).any fun e => x e.1 && x e.2)) →
      (∀ v ∈ ([0, 3, 5, 6] : List (Fin 8)), ∀ S : Finset ℕ,
        (∀ j ∈ S, j < C.size ∧
          ((∃ b : Bool, ∀ x : Fin 8 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (8 + j) false = b) ∨
          (∃ i < 8 + j, ∀ x : Fin 8 → Bool, x v = false →
            (C.wires (List.ofFn x)).getD (8 + j) false =
              (C.wires (List.ofFn x)).getD i false))) → S.card ≤ 2) →
      False) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   x1.length ≤ (12 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (8 : ℕ) ≤ x2 →         x2 < x3 →           x3 < (8 : ℕ) + x1.length →             ∃ (x9 : Fin (8 : ℕ) → Bool),               have x10 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9);               (x10.getD x2 Bool.false && x10.getD x3 Bool.false) ≠ (fun (x11 : Fin (8 : ℕ) → Bool) => x11 (0 : Fin (8 : ℕ)) && x11 (1 : Fin (8 : ℕ)) || x11 (1 : Fin (8 : ℕ)) && x11 (2 : Fin (8 : ℕ)) || x11 (2 : Fin (8 : ℕ)) && x11 (3 : Fin (8 : ℕ)) || x11 (0 : Fin (8 : ℕ)) && x11 (4 : Fin (8 : ℕ)) || x11 (1 : Fin (8 : ℕ)) && x11 (5 : Fin (8 : ℕ)) || x11 (2 : Fin (8 : ℕ)) && x11 (6 : Fin (8 : ℕ)) || x11 (3 : Fin (8 : ℕ)) && x11 (7 : Fin (8 : ℕ)) || x11 (4 : Fin (8 : ℕ)) && x11 (6 : Fin (8 : ℕ)) || x11 (5 : Fin (8 : ℕ)) && x11 (7 : Fin (8 : ℕ)) || x11 (7 : Fin (8 : ℕ)) && x11 (4 : Fin (8 : ℕ))) x9 := by
  intro ls a b hlen hfan0 ha hab hb
  by_contra hno
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have evalAnd (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have evalOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have evalNot (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  let H : (Fin 7 → Bool) → Bool := (fun y : Fin 7 → Bool =>
      ([(0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1)] : List (Fin 7 × Fin 7)).any (fun e => y e.1 && y e.2))
  let F : (Fin 8 → Bool) → Bool := fun x => (([(0,1),(1,2),(2,3),(0,4),(1,5),(2,6),(3,7),(4,6),(5,7),(7,4)] : List (Fin 8 × Fin 8)).any fun e => x e.1 && x e.2)
  let C : Circuit := ⟨ls ++ [⟨GateOp.and, [a, b]⟩], 8 + ls.length⟩
  have hC : FanInTwo C := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hfan0 g h
    · rw [List.mem_singleton.mp h]
      simp
  have hFold (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]; omega
  have same : circuitFun 8 C = F := by
    funext x
    have h : ((ls.foldl step (List.ofFn x)).getD a false &&
        (ls.foldl step (List.ofFn x)).getD b false) = F x := by
      by_contra hx
      refine hno ⟨x, fun he => hx (he.trans ?_)⟩
      simp [F, Bool.or_assoc]
    change ((ls ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]).foldl step (List.ofFn x)).getD (8 + ls.length) false = F x
    rw [List.foldl_append, ← h]
    have hl : (ls.foldl step (List.ofFn x)).length = 8 + ls.length := by simp [hFold]
    simp only [List.foldl_cons, List.foldl_nil]
    generalize ls.foldl step (List.ofFn x) = w at hl
    simp [step, List.getD_eq_getElem?_getD, ← hl, evalAnd]
  refine rigid ls a b C rfl hC hlen ha hab hb (fun x => congrFun same x) ?elim
  case elim =>
    have small : C.size ≤ 13 := by
      change (ls ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]).length ≤ 13
      simp; omega
    intro v hv S hS
    by_contra! big
    obtain ⟨τ, hτ⟩ : ∃ τ : Fin 8 → Fin 7, ∀ y : Fin 7 → Bool,
        F (fun i => if i = v then false else y (τ i)) = H y := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact ⟨![0, 3, 0, 2, 6, 4, 5, 1], by decide +kernel⟩
      · exact ⟨![2, 0, 3, 0, 1, 5, 4, 6], by decide +kernel⟩
      · exact ⟨![3, 4, 1, 6, 0, 0, 2, 5], by decide +kernel⟩
      · exact ⟨![3, 0, 5, 6, 4, 2, 0, 1], by decide +kernel⟩
    let X : (Fin 7 → Bool) → Fin 8 → Bool := fun y i => if i = v then false else y (τ i)
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
    let W : (Fin 7 → Bool) → List Bool := fun y => C.wires (List.ofFn (X y))
    let N : List Gate → (Fin 7 → Bool) → List Bool := fun gs y => gs.foldl step (List.ofFn y)
    have hNlen (gs y) : (N gs y).length = 7 + gs.length := by simp [N, lengthOf]
    have hWlen (y) : (W y).length = 8 + C.gates.length := by
      change (C.gates.foldl step (List.ofFn (X y))).length = _
      simp [lengthOf]
    have keepN (gs : List Gate) (g : Gate) (i : ℕ) (hi : i < 7 + gs.length) (y) :
        (N (gs ++ [g]) y).getD i false = (N gs y).getD i false := by
      simp only [N, List.foldl_append]
      exact keep [g] _ i (by simpa [lengthOf] using hi)
    have newN (gs : List Gate) (g : Gate) (y) :
        (N (gs ++ [g]) y).getD (7 + gs.length) false =
          g.op.eval (g.inputs.map fun i => (N gs y).getD i false) := by
      simp only [N, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact last _ _ _ (by simp [lengthOf])
    have gateW (k : ℕ) (hk : k < C.gates.length) (y) :
        (W y).getD (8 + k) false =
          (C.gates[k]).op.eval ((C.gates[k]).inputs.map fun i =>
            if i < 8 + k then (W y).getD i false else false) := by
      have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by simp
      let P := (C.gates.take k).foldl step (List.ofFn (X y))
      have hP : P.length = 8 + k := by simp [P, lengthOf]; omega
      have hW : W y = (C.gates.drop (k + 1)).foldl step (step P C.gates[k]) := by
        change C.gates.foldl step (List.ofFn (X y)) = _
        conv_lhs => rw [hsplit]
        rw [List.foldl_append, List.foldl_cons]
      have hlow (i : ℕ) (hi : i < 8 + k) : (W y).getD i false = P.getD i false := by
        rw [hW, keep _ _ _ (by simp [step]; omega)]
        simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left (hP ▸ hi)]
      rw [hW, keep _ _ _ (by simp [step]; omega)]
      have h1 : (step P C.gates[k]).getD (8 + k) false =
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
      (∃ i' < 7 + gs.length, ∀ y, (W y).getD i false = (N gs y).getD i' false)
    have main (k : ℕ) (hk : k ≤ C.gates.length) : ∃ gs : List Gate,
        (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
          g.inputs.length ≤ 2) ∧
        gs.length + (S.filter (· < k)).card ≤ k ∧ ∀ i < 8 + k, Good gs i := by
      induction k with
      | zero =>
        refine ⟨[], by simp, by simp, fun i hi => ?_⟩
        have hi9 : i < 8 := by omega
        have hval (y) : (W y).getD i false = X y ⟨i, hi9⟩ := by
          change (C.gates.foldl step (List.ofFn (X y))).getD i false = _
          rw [keep _ _ _ (by simpa using hi9)]
          exact getOf 8 (X y) ⟨i, hi9⟩
        by_cases hiv : (⟨i, hi9⟩ : Fin 8) = v
        · exact Or.inl ⟨false, fun y => by rw [hval, hiv, hXv]⟩
        · refine Or.inr ⟨(τ ⟨i, hi9⟩).val, by simp, fun y => ?_⟩
          rw [hval]
          simp only [N, List.foldl_nil, getOf, X, if_neg hiv]
      | succ k ih =>
        have hk' : k < C.gates.length := by omega
        obtain ⟨gs, hfan, hcount, hgood⟩ := ih (by omega)
        have hfilter : (S.filter (· < k + 1)).card ≤ (S.filter (· < k)).card + 1 := by
          have hsub : S.filter (· < k + 1) ⊆ insert k (S.filter (· < k)) := by
            intro a ha
            simp only [Finset.mem_filter, Finset.mem_insert] at ha ⊢
            rcases Nat.lt_succ_iff_lt_or_eq.mp ha.2 with h | h
            · exact Or.inr ⟨ha.1, h⟩
            · exact Or.inl h
          exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
        by_cases hG : Good gs (8 + k)
        · refine ⟨gs, hfan, by omega, fun i hi => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < (8 + k) + 1 by omega) with h | h
          · exact hgood i h
          · exact h ▸ hG
        have notConst (b : Bool) : ¬ ∀ y, (W y).getD (8 + k) false = b :=
          fun h => hG (Or.inl ⟨b, h⟩)
        have notAlias (i : ℕ) (hi : i < 8 + k) :
            ¬ ∀ y, (W y).getD (8 + k) false = (W y).getD i false := by
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
        let val : ℕ → (Fin 7 → Bool) → Bool := fun i y =>
          if i < 8 + k then (W y).getD i false else false
        have valCases (i : ℕ) : (∃ b : Bool, ∀ y, val i y = b) ∨
            (i < 8 + k ∧ ∃ i' < 7 + gs.length, ∀ y, val i y = (N gs y).getD i' false) := by
          by_cases hi : i < 8 + k
          · rcases hgood i hi with ⟨b, hb⟩ | ⟨i', hi', hb⟩
            · exact Or.inl ⟨b, fun y => by simp only [val, if_pos hi]; exact hb y⟩
            · exact Or.inr ⟨hi, i', hi', fun y => by simp only [val, if_pos hi]; exact hb y⟩
          · exact Or.inl ⟨false, fun y => by simp only [val, if_neg hi]⟩
        have notVal (i : ℕ) : ¬ ∀ y, (W y).getD (8 + k) false = val i y := by
          intro h
          by_cases hi : i < 8 + k
          · exact notAlias i hi fun y => by rw [h y]; simp only [val, if_pos hi]
          · exact notConst false fun y => by rw [h y]; simp only [val, if_neg hi]
        have build : ∃ g : Gate, (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
            g.inputs.length ≤ 2) ∧ ∀ y, (W y).getD (8 + k) false =
              g.op.eval (g.inputs.map fun i => (N gs y).getD i false) := by
          have hgate := gateW k hk'
          obtain ⟨hop, hlen⟩ := hC _ (List.getElem_mem hk')
          generalize C.gates[k] = g at hgate hop hlen
          obtain ⟨op, ins⟩ := g
          have hg (y) : (W y).getD (8 + k) false = op.eval (ins.map fun i => val i y) := hgate y
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
        refine ⟨gs ++ [g], ?_, ?_, fun i hi => ?_⟩
        · intro g' hg'
          rcases List.mem_append.mp hg' with h | h
          · exact hfan g' h
          · rw [List.mem_singleton.mp h]; exact hgfan
        · rw [hfilter']; simp; omega
        · rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < (8 + k) + 1 by omega) with h | h
          · rcases hgood i h with ⟨b, hb⟩ | ⟨i', hi', hb⟩
            · exact Or.inl ⟨b, hb⟩
            · exact Or.inr ⟨i', by simp; omega, fun y => by rw [keepN gs g i' hi', hb y]⟩
          · subst h
            exact Or.inr ⟨7 + gs.length, by simp, fun y => by rw [newN, hgval y]⟩
    obtain ⟨gs, hfan, hcount, hgood⟩ := main C.gates.length le_rfl
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
    by_cases ho : C.output < 8 + C.gates.length
    · rcases hgood C.output ho with ⟨b, hb⟩ | ⟨o, _, hb⟩
      · exact nonconst b hb
      · have := minor gs.length ⟨⟨gs, o⟩, hfan, le_rfl, fun y =>
          (hb y).symm.trans (hout y)⟩
        omega
    · exact nonconst false fun y => beyond _ _ (by rw [hWlen]; omega)
