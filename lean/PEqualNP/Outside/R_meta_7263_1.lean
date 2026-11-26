import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_7263_1
    (hT1 : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ))));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),
        PEqualNP.MetaComplexity.FanInTwo x2 →
          (16 : ℕ) ≤ x2.size → x2.size ≤ (17 : ℕ) →
          (10 : ℕ) ≤ x3 → x3 < (10 : ℕ) + x2.size →
          (10 : ℕ) ≤ x4 → x4 < (10 : ℕ) + x2.size → x3 ≠ x4 →
          (∀ (x5 : Fin (10 : ℕ)), (15 : ℕ) + List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => (cond (x6.op.eval [Bool.false]) (x6.inputs.take (1 : ℕ)) x6.inputs).contains x5.val) x2.gates ≤ x2.size) →
          have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false;
          have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x7 x8 x3 && x7 x8 x4;
          (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x3 = Bool.true ∧ x7 x9 x4 = Bool.false) →
          (∃ (x10 : Fin (10 : ℕ) → Bool), x7 x10 x3 = Bool.false ∧ x7 x10 x4 = Bool.true) →
          (∀ (x11 : Fin (10 : ℕ) → Bool), x1 x11 = Bool.false ∨ List.count Bool.true (List.ofFn x11) ≤ (2 : ℕ) → x8 x11 = x1 x11) →
          ∃ (x12 : Equiv.Perm (Fin (10 : ℕ))) (x13 : Bool) (x14 : PEqualNP.CircuitLowerBounds.Circuit),
            (∀ (x15 : Fin (10 : ℕ) → Bool), x1 (x15 ∘ ⇑x12) = x1 x15) ∧
            PEqualNP.MetaComplexity.FanInTwo x14 ∧
            (x14.size ≤ if x13 = Bool.true then (10 : ℕ) else (15 : ℕ)) ∧
            ∀ (x15 : Fin (9 : ℕ) → Bool), x14.eval (List.ofFn x15) = x8 ((fun (x16 : Fin ((9 : ℕ) + (1 : ℕ))) => Fin.lastCases x13 x15 x16) ∘ ⇑x12))
    (hT2 : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ))));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),
        PEqualNP.MetaComplexity.FanInTwo x2 →
          x2.size = (18 : ℕ) →
          (10 : ℕ) ≤ x3 → x3 < (10 : ℕ) + x2.size →
          (10 : ℕ) ≤ x4 → x4 < (10 : ℕ) + x2.size → x3 ≠ x4 →
          (∀ (x5 : PEqualNP.CircuitLowerBounds.Gate), x5 ∈ x2.gates → x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
          (∀ (x5 : Fin (10 : ℕ)), List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.inputs.contains x5.val) x2.gates ≤ (3 : ℕ)) →
          have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false;
          have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x7 x8 x3 && x7 x8 x4;
          (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x3 = Bool.true ∧ x7 x9 x4 = Bool.false) →
          (∃ (x10 : Fin (10 : ℕ) → Bool), x7 x10 x3 = Bool.false ∧ x7 x10 x4 = Bool.true) →
          (∀ (x11 : Fin (10 : ℕ) → Bool), x1 x11 = Bool.false ∨ List.count Bool.true (List.ofFn x11) ≤ (2 : ℕ) → x8 x11 = x1 x11) →
          ∃ (x12 : Equiv.Perm (Fin (10 : ℕ))) (x13 : Bool) (x14 : PEqualNP.CircuitLowerBounds.Circuit),
            (∀ (x15 : Fin (10 : ℕ) → Bool), x1 (x15 ∘ ⇑x12) = x1 x15) ∧
            PEqualNP.MetaComplexity.FanInTwo x14 ∧
            (x14.size ≤ if x13 = Bool.true then (10 : ℕ) else (15 : ℕ)) ∧
            ∀ (x15 : Fin (9 : ℕ) → Bool), x14.eval (List.ofFn x15) = x8 ((fun (x16 : Fin ((9 : ℕ) + (1 : ℕ))) => Fin.lastCases x13 x15 x16) ∘ ⇑x12))
    (hT3 : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ))));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),
        PEqualNP.MetaComplexity.FanInTwo x2 →
          x2.size = (18 : ℕ) →
          (10 : ℕ) ≤ x3 → x3 < (10 : ℕ) + x2.size →
          (10 : ℕ) ≤ x4 → x4 < (10 : ℕ) + x2.size → x3 ≠ x4 →
          (∃ (x5 : PEqualNP.CircuitLowerBounds.Gate), x5 ∈ x2.gates ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
          (∀ (x5 : Fin (10 : ℕ)), List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => (cond (x6.op.eval [Bool.false]) (x6.inputs.take (1 : ℕ)) x6.inputs).contains x5.val) x2.gates ≤ (3 : ℕ)) →
          have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false;
          have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x7 x8 x3 && x7 x8 x4;
          (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x3 = Bool.true ∧ x7 x9 x4 = Bool.false) →
          (∃ (x10 : Fin (10 : ℕ) → Bool), x7 x10 x3 = Bool.false ∧ x7 x10 x4 = Bool.true) →
          (∀ (x11 : Fin (10 : ℕ) → Bool), x1 x11 = Bool.false ∨ List.count Bool.true (List.ofFn x11) ≤ (2 : ℕ) → x8 x11 = x1 x11) →
          ∃ (x12 : Equiv.Perm (Fin (10 : ℕ))) (x13 : Bool) (x14 : PEqualNP.CircuitLowerBounds.Circuit),
            (∀ (x15 : Fin (10 : ℕ) → Bool), x1 (x15 ∘ ⇑x12) = x1 x15) ∧
            PEqualNP.MetaComplexity.FanInTwo x14 ∧
            (x14.size ≤ if x13 = Bool.true then (10 : ℕ) else (15 : ℕ)) ∧
            ∀ (x15 : Fin (9 : ℕ) → Bool), x14.eval (List.ofFn x15) = x8 ((fun (x16 : Fin ((9 : ℕ) + (1 : ℕ))) => Fin.lastCases x13 x15 x16) ∘ ⇑x12)) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (18 : ℕ) → have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false; have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x7 x8 x3 && x7 x8 x4; (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x3 = Bool.true ∧ x7 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x7 x10 x3 = Bool.false ∧ x7 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x1 x11 = Bool.false ∨ List.count Bool.true (List.ofFn x11) ≤ (2 : ℕ) → x8 x11 = x1 x11) → ∃ (x12 : Equiv.Perm (Fin (10 : ℕ))) (x13 : Bool) (x14 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x15 : Fin (10 : ℕ) → Bool), x1 (x15 ∘ ⇑x12) = x1 x15) ∧ PEqualNP.MetaComplexity.FanInTwo x14 ∧ (x14.size ≤ if x13 = Bool.true then (10 : ℕ) else (15 : ℕ)) ∧ ∀ (x15 : Fin (9 : ℕ) → Bool), x14.eval (List.ofFn x15) = x8 ((fun (x16 : Fin ((9 : ℕ) + (1 : ℕ))) => Fin.lastCases x13 x15 x16) ∘ ⇑x12) := by
  dsimp only at hT1 hT2 hT3 ⊢
  intro C a b hfan hsize h1 h2 h3
  let fP : (Fin 10 → Bool) → Bool := fun x => (List.finRange 5).any fun i : Fin 5 =>
    x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1)) ||
    x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
    x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))
  let f10 : (Fin 10 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  have hfP_eq : ∀ x : Fin 10 → Bool, f10 x = fP x := by
    intro x
    dsimp only [f10, fP]
    have hfr5 : List.finRange 5 = [0, 1, 2, 3, 4] := by decide
    rw [hfr5]
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    change _ = ((x 0 && x 1 || x 0 && x 5 || x 5 && x 7) ||
      ((x 1 && x 2 || x 1 && x 6 || x 6 && x 8) ||
      ((x 2 && x 3 || x 2 && x 7 || x 7 && x 9) ||
      ((x 3 && x 4 || x 3 && x 8 || x 8 && x 5) ||
      (x 4 && x 0 || x 4 && x 9 || x 9 && x 6)))))
    ac_rfl
  let edgeList : List (Fin 10 × Fin 10) :=
    [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
     (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
     (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]
  have hfP_edges : ∀ x : Fin 10 → Bool, fP x = edgeList.any (fun e => x e.1 && x e.2) := by
    intro x
    rw [← hfP_eq]
    dsimp [f10, edgeList]
    simp only [Bool.or_false, Bool.or_assoc]
  have hedge_pres : ∀ (f g : Fin 10 → Fin 10),
      (edgeList.all (fun e => edgeList.any (fun e' => (f e.1 == e'.1 && f e.2 == e'.2) || (f e.1 == e'.2 && f e.2 == e'.1)))) = true →
      (edgeList.all (fun e => edgeList.any (fun e' => (g e.1 == e'.1 && g e.2 == e'.2) || (g e.1 == e'.2 && g e.2 == e'.1)))) = true →
      (∀ k : Fin 10, f (g k) = k) →
      ∀ x : Fin 10 → Bool, fP (x ∘ f) = fP x := by
    intro f g hf hg hfg x
    rw [hfP_edges, hfP_edges]
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      rw [List.any_eq_true] at h ⊢
      rcases h with ⟨e, he, hev⟩
      rw [List.all_eq_true] at hf
      have he1 := hf e he
      rw [List.any_eq_true] at he1
      rcases he1 with ⟨e', he', heq⟩
      refine ⟨e', he', ?_⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at heq hev ⊢
      rcases heq with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · exact ⟨h1' ▸ hev.1, h2' ▸ hev.2⟩
      · exact ⟨h2' ▸ hev.2, h1' ▸ hev.1⟩
    · intro h
      rw [List.any_eq_true] at h ⊢
      rcases h with ⟨e', he', hev⟩
      rw [List.all_eq_true] at hg
      have he1 := hg e' he'
      rw [List.any_eq_true] at he1
      rcases he1 with ⟨e, he, heq⟩
      refine ⟨e, he, ?_⟩
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at heq hev ⊢
      rcases heq with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · exact ⟨by change x (f e.1) = true; rw [← h1', hfg e'.1]; exact hev.1,
               by change x (f e.2) = true; rw [← h2', hfg e'.2]; exact hev.2⟩
      · exact ⟨by change x (f e.1) = true; rw [← h2', hfg e'.2]; exact hev.2,
               by change x (f e.2) = true; rw [← h1', hfg e'.1]; exact hev.1⟩
  let sigma9Tbl : List (List (Fin 10)) :=
    [[9, 4, 0, 1, 6, 7, 3, 5, 2, 8],
     [4, 9, 6, 1, 0, 3, 7, 8, 2, 5],
     [0, 4, 9, 6, 1, 5, 3, 7, 8, 2],
     [0, 1, 6, 9, 4, 5, 2, 8, 7, 3],
     [4, 0, 1, 6, 9, 3, 5, 2, 8, 7],
     [4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
     [0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
     [0, 1, 6, 8, 5, 4, 2, 9, 3, 7],
     [0, 1, 2, 7, 5, 4, 6, 3, 9, 8],
     [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]
  let sigma9InvTbl : List (List (Fin 10)) :=
    [[2, 3, 8, 6, 1, 7, 4, 5, 9, 0],
     [4, 3, 8, 5, 0, 9, 2, 6, 7, 1],
     [0, 4, 9, 6, 1, 5, 3, 7, 8, 2],
     [0, 1, 6, 9, 4, 5, 2, 8, 7, 3],
     [1, 2, 7, 5, 0, 6, 3, 9, 8, 4],
     [1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
     [0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
     [0, 1, 6, 8, 5, 4, 2, 9, 3, 7],
     [0, 1, 2, 7, 5, 4, 6, 3, 9, 8],
     [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]
  let tblAt : List (List (Fin 10)) → Fin 10 → Fin 10 → Fin 10 := fun tbl r k =>
    (tbl.getD r.val []).getD k.val 0
  let sigma9 := tblAt sigma9Tbl
  let sigma9Inv := tblAt sigma9InvTbl
  have hs9_pres : ∀ r : Fin 10, (edgeList.all (fun e => edgeList.any (fun e' => (sigma9 r e.1 == e'.1 && sigma9 r e.2 == e'.2) || (sigma9 r e.1 == e'.2 && sigma9 r e.2 == e'.1)))) = true := by
    dsimp only [sigma9, tblAt, sigma9Tbl, edgeList]; decide
  have hs9i_pres : ∀ r : Fin 10, (edgeList.all (fun e => edgeList.any (fun e' => (sigma9Inv r e.1 == e'.1 && sigma9Inv r e.2 == e'.2) || (sigma9Inv r e.1 == e'.2 && sigma9Inv r e.2 == e'.1)))) = true := by
    dsimp only [sigma9Inv, tblAt, sigma9InvTbl, edgeList]; decide
  have hs9_inv1 : ∀ r k : Fin 10, sigma9 r (sigma9Inv r k) = k := by
    dsimp only [sigma9, sigma9Inv, tblAt, sigma9Tbl, sigma9InvTbl]; decide
  have hs9_inv2 : ∀ r k : Fin 10, sigma9Inv r (sigma9 r k) = k := by
    dsimp only [sigma9, sigma9Inv, tblAt, sigma9Tbl, sigma9InvTbl]; decide
  have hfP_sigma9 : ∀ r : Fin 10, ∀ x : Fin 10 → Bool, fP (x ∘ sigma9 r) = fP x :=
    fun r x => hedge_pres (sigma9 r) (sigma9Inv r) (hs9_pres r) (hs9i_pres r) (hs9_inv1 r) x
  have hs9_self : ∀ r : Fin 10, sigma9 r r = 9 := by
    dsimp only [sigma9, tblAt, sigma9Tbl]; decide
  let wiresFrom : List Gate → List Bool → List Bool := fun gs w =>
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
  have hwiresFrom_append : ∀ gs gs' w, wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
    intro gs gs' w; simp [wiresFrom, List.foldl_append]
  have hwiresFrom_prefix : ∀ gs w, ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
      have : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
      rw [this, ht]; simp
  have hlength_wiresFrom : ∀ gs w, (wiresFrom gs w).length = w.length + gs.length := by
    intro gs w
    obtain ⟨t, ht, hl⟩ := hwiresFrom_prefix gs w
    rw [ht]; simp [hl]
  have hgetD_snoc_ne : ∀ {α : Type} (L : List α) (S d : α) (j : ℕ), j ≠ L.length →
      (L ++ [S]).getD j d = L.getD j d := by
    intro α L S d j hj
    by_cases hlt : j < L.length
    · exact List.getD_append _ _ _ _ hlt
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have hgetD_snoc_eq : ∀ {α : Type} (L : List α) (S d : α), (L ++ [S]).getD L.length d = S := by
    intro α L S d; simp
  have hwire_input : ∀ (C0 : Circuit) (x : Fin 10 → Bool) (i : Fin 10),
      (C0.wires (List.ofFn x)).getD i.val false = x i := by
    intro C0 x i
    obtain ⟨t, ht, _⟩ := hwiresFrom_prefix C0.gates (List.ofFn x)
    change C0.wires (List.ofFn x) = _ at ht
    rw [ht, List.getD_append _ _ _ _ (by simp),
      List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have hwire_outside : ∀ (C0 : Circuit) (x : Fin 10 → Bool) (i : ℕ),
      10 + C0.size ≤ i → (C0.wires (List.ofFn x)).getD i false = false := by
    intro C0 x i hi
    obtain ⟨t, ht, hlen⟩ := hwiresFrom_prefix C0.gates (List.ofFn x)
    change C0.wires (List.ofFn x) = _ at ht
    rw [ht]
    apply List.getD_eq_default
    rw [List.length_append, List.length_ofFn, hlen]
    exact hi
  -- Step A: Eliminate out-of-range and equal wires
  have hab : a ≠ b := by
    intro heq
    subst heq
    obtain ⟨x9, hx9a, hx9b⟩ := h1
    rw [hx9a] at hx9b
    cases hx9b
  have ha_hi : a < 10 + C.size := by
    by_contra! hge
    obtain ⟨x9, hx9a, _⟩ := h1
    rw [hwire_outside C x9 a hge] at hx9a
    cases hx9a
  have hb_hi : b < 10 + C.size := by
    by_contra! hge
    obtain ⟨x10, _, hx10b⟩ := h2
    rw [hwire_outside C x10 b hge] at hx10b
    cases hx10b
  have hedge_avoid : ∀ i : Fin 10, ∃ u v : Fin 10,
      u ≠ i ∧ v ≠ i ∧
      fP (fun k => decide (k = u ∨ k = v)) = true ∧
      List.count true (List.ofFn (fun k : Fin 10 => decide (k = u ∨ k = v))) ≤ 2 := by
    have he01 : fP (fun k => decide (k = 0 ∨ k = 1)) = true := by dsimp only [fP]; decide
    have hw01 : List.count true (List.ofFn (fun k : Fin 10 => decide (k = 0 ∨ k = 1))) ≤ 2 := by decide
    have he23 : fP (fun k => decide (k = 2 ∨ k = 3)) = true := by dsimp only [fP]; decide
    have hw23 : List.count true (List.ofFn (fun k : Fin 10 => decide (k = 2 ∨ k = 3))) ≤ 2 := by decide
    intro i
    by_cases hi : i = 0 ∨ i = 1
    · exact ⟨2, 3, by omega, by omega, he23, hw23⟩
    · exact ⟨0, 1, fun h => hi (Or.inl h.symm), fun h => hi (Or.inr h.symm), he01, hw01⟩
  have ha_lo : 10 ≤ a := by
    by_contra! hlt
    let i : Fin 10 := ⟨a, hlt⟩
    obtain ⟨u, v, hui, hvi, hfp, hwt⟩ := hedge_avoid i
    let x : Fin 10 → Bool := fun k => decide (k = u ∨ k = v)
    have hmatch := h3 x (Or.inr hwt)
    have hwa : (C.wires (List.ofFn x)).getD a false = false := by
      have hi := hwire_input C x i
      simpa [i, x, hui.symm, hvi.symm] using hi
    change ((C.wires (List.ofFn x)).getD a false && (C.wires (List.ofFn x)).getD b false) = fP x at hmatch
    rw [hwa, Bool.false_and, hfp] at hmatch
    cases hmatch
  have hb_lo : 10 ≤ b := by
    by_contra! hlt
    let i : Fin 10 := ⟨b, hlt⟩
    obtain ⟨u, v, hui, hvi, hfp, hwt⟩ := hedge_avoid i
    let x : Fin 10 → Bool := fun k => decide (k = u ∨ k = v)
    have hmatch := h3 x (Or.inr hwt)
    have hwb : (C.wires (List.ofFn x)).getD b false = false := by
      have hi := hwire_input C x i
      simpa [i, x, hui.symm, hvi.symm] using hi
    change ((C.wires (List.ofFn x)).getD a false && (C.wires (List.ofFn x)).getD b false) = fP x at hmatch
    rw [hwb, Bool.and_false, hfp] at hmatch
    cases hmatch
  -- Step B: Every input variable v : Fin 10 is effectively read by at least 1 gate
  let effInputs : Gate → List ℕ := fun g => cond (g.op.eval [false]) (g.inputs.take 1) g.inputs
  let fanOK : Gate → Prop := fun g => (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2
  have hcomp_init_Agree : ∀ (w1 w2 : List Bool) (gs : List Gate) (B : ℕ → Prop) (uOut : ℕ),
      w1.length = w2.length →
      ¬ B uOut →
      (∀ i, ¬ B i → w1.getD i false = w2.getD i false) →
      (∀ g ∈ gs, ∀ i ∈ effInputs g, ¬ B i) →
      (∀ g ∈ gs, fanOK g) →
      (wiresFrom gs w1).getD uOut false = (wiresFrom gs w2).getD uOut false := by
    intro w1 w2 gs
    induction gs generalizing w1 w2 with
    | nil =>
      intro B uOut _ hBu hinit _ _
      exact hinit uOut hBu
    | cons g gs ih =>
      intro B uOut hlen hBu hinit hnoB hfan_gs
      change (wiresFrom gs (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)])).getD uOut false =
        (wiresFrom gs (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)])).getD uOut false
      apply ih _ _ B uOut (by simp [hlen]) hBu
      · intro i hi
        by_cases hil : i < w1.length
        · rw [List.getD_append _ _ _ _ hil, List.getD_append _ _ _ _ (by omega)]
          exact hinit i hi
        · by_cases hieq : i = w1.length
          · subst hieq
            rw [hgetD_snoc_eq, hlen, hgetD_snoc_eq]
            cases g
            rename_i op ins
            rcases (hfan_gs ⟨op, ins⟩ List.mem_cons_self).1 with rfl | rfl | rfl
            · have hmap : ins.map (fun j => w1.getD j false) = ins.map (fun j => w2.getD j false) := by
                apply List.map_congr_left
                intro j hj
                exact hinit j (hnoB ⟨GateOp.and, ins⟩ List.mem_cons_self j hj)
              rw [hmap]
            · have hmap : ins.map (fun j => w1.getD j false) = ins.map (fun j => w2.getD j false) := by
                apply List.map_congr_left
                intro j hj
                exact hinit j (hnoB ⟨GateOp.or, ins⟩ List.mem_cons_self j hj)
              rw [hmap]
            · cases ins with
              | nil => rfl
              | cons a0 t =>
                have ha0 : ¬ B a0 := hnoB ⟨GateOp.not, a0 :: t⟩ List.mem_cons_self a0 (by change a0 ∈ [a0]; simp)
                change Bool.not ((w1.getD a0 false :: t.map _).headD false) = Bool.not ((w2.getD a0 false :: t.map _).headD false)
                rw [List.headD_cons, List.headD_cons, hinit a0 ha0]
          · rw [List.getD_eq_default _ false (by simp; omega),
              List.getD_eq_default _ false (by simp; omega)]
      · intro g' hg'
        exact hnoB g' (List.mem_cons_of_mem _ hg')
      · intro g' hg'
        exact hfan_gs g' (List.mem_cons_of_mem _ hg')
  let nbr : Fin 10 → Fin 10 := fun v =>
    if v = 0 then 1 else if v = 1 then 0 else if v = 2 then 1 else if v = 3 then 2
    else if v = 4 then 3 else if v = 5 then 0 else if v = 6 then 1 else if v = 7 then 2
    else if v = 8 then 3 else 4
  have hedge_inc : ∀ v : Fin 10,
      nbr v ≠ v ∧
      fP (fun k => decide (k = v ∨ k = nbr v)) = true ∧
      fP (fun k => decide (k = nbr v)) = false ∧
      List.count true (List.ofFn (fun k : Fin 10 => decide (k = v ∨ k = nbr v))) ≤ 2 := by
    dsimp only [fP, nbr]; decide
  have hdeg_pos : ∀ v : Fin 10, 1 ≤ C.gates.countP (fun g => (effInputs g).contains v.val) := by
    intro v
    by_contra! hlt
    have hzero : C.gates.countP (fun g => (effInputs g).contains v.val) = 0 := by omega
    rw [List.countP_eq_zero] at hzero
    obtain ⟨huv, hfp1, hfp0, hwt1⟩ := hedge_inc v
    let u := nbr v
    let x1 : Fin 10 → Bool := fun k => decide (k = v ∨ k = u)
    let x0 : Fin 10 → Bool := fun k => decide (k = u)
    have hagree_init : ∀ i : ℕ, i ≠ v.val → (List.ofFn x1).getD i false = (List.ofFn x0).getD i false := by
      intro i hi
      by_cases hi10 : i < 10
      · rw [List.getD_eq_getElem _ _ (by simpa using hi10), List.getElem_ofFn,
          List.getD_eq_getElem _ _ (by simpa using hi10), List.getElem_ofFn]
        have hne : (⟨i, hi10⟩ : Fin 10) ≠ v := fun he => hi (congrArg Fin.val he)
        simp [x1, x0, hne]
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi10),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi10)]
    have hnoB : ∀ g ∈ C.gates, ∀ i ∈ effInputs g, i ≠ v.val := by
      intro g hg i hi heq
      have hc := hzero g hg
      rw [← heq] at hc
      simp only [List.contains_eq_mem, decide_eq_true_eq] at hc
      exact hc hi
    have ha_eq : (C.wires (List.ofFn x1)).getD a false = (C.wires (List.ofFn x0)).getD a false :=
      hcomp_init_Agree (List.ofFn x1) (List.ofFn x0) C.gates (fun i => i = v.val) a
        (by simp) (by have := v.isLt; omega) hagree_init hnoB hfan
    have hb_eq : (C.wires (List.ofFn x1)).getD b false = (C.wires (List.ofFn x0)).getD b false :=
      hcomp_init_Agree (List.ofFn x1) (List.ofFn x0) C.gates (fun i => i = v.val) b
        (by simp) (by have := v.isLt; omega) hagree_init hnoB hfan
    have hm1 := h3 x1 (Or.inr hwt1)
    have hm0 := h3 x0 (Or.inl hfp0)
    change ((C.wires (List.ofFn x1)).getD a false && (C.wires (List.ofFn x1)).getD b false) = fP x1 at hm1
    change ((C.wires (List.ofFn x0)).getD a false && (C.wires (List.ofFn x0)).getD b false) = fP x0 at hm0
    rw [ha_eq, hb_eq, hm0, hfp0, hfp1] at hm1
    cases hm1
  -- Step C: Constant-propagation gate elimination and hDegElim
  have andEval : ∀ xs : List Bool, GateOp.and.eval xs = xs.all id := fun _ => rfl
  have orEval : ∀ xs : List Bool, GateOp.or.eval xs = xs.any id := fun _ => rfl
  have notEval : ∀ xs : List Bool, GateOp.not.eval xs = !(xs.headD false) := fun _ => rfl
  have circuitSize : ∀ C0 : Circuit, C0.size = C0.gates.length := fun _ => rfl
  have circuitEval : ∀ (C0 : Circuit) (xs : List Bool), C0.eval xs = (C0.wires xs).getD C0.output false := fun _ _ => rfl
  have circuitWires : ∀ (C0 : Circuit) (xs : List Bool), C0.wires xs = wiresFrom C0.gates xs := fun _ _ => rfl
  let Stat := Sum Bool ℕ
  let statVal : List Bool → Stat → Bool := fun w s =>
    Sum.casesOn (motive := fun _ => Bool) s (fun c => c) (fun j => w.getD j false)
  let statValid : ℕ → Stat → Prop := fun m s =>
    Sum.casesOn (motive := fun _ => Prop) s (fun _ => True) (fun j => j < m)
  let simpNot (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
    List.casesOn (motive := fun _ => Option Gate × Stat) ins (none, Sum.inl true) fun a _ =>
      Sum.casesOn (motive := fun _ => Option Gate × Stat) a
        (fun c => (none, Sum.inl (!c)))
        (fun j => (some ⟨GateOp.not, [j]⟩, Sum.inr m))
  let simpAnd (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
    List.casesOn (motive := fun _ => Option Gate × Stat) ins (none, Sum.inl true) fun a t =>
      List.casesOn (motive := fun _ => Option Gate × Stat) t
        (Sum.casesOn (motive := fun _ => Option Gate × Stat) a
          (fun c => (none, Sum.inl c))
          (fun j => (none, Sum.inr j)))
        fun b r =>
          List.casesOn (motive := fun _ => Option Gate × Stat) r
            (Sum.casesOn (motive := fun _ => Option Gate × Stat) a
              (fun c => Sum.casesOn (motive := fun _ => Option Gate × Stat) b
                (fun d => (none, Sum.inl (c && d)))
                (fun j => (none, bif c then Sum.inr j else Sum.inl false)))
              (fun j => Sum.casesOn (motive := fun _ => Option Gate × Stat) b
                (fun c => (none, bif c then Sum.inr j else Sum.inl false))
                (fun k => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m))))
            (fun _ _ => (none, Sum.inl false))
  let simpOr (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
    List.casesOn (motive := fun _ => Option Gate × Stat) ins (none, Sum.inl false) fun a t =>
      List.casesOn (motive := fun _ => Option Gate × Stat) t
        (Sum.casesOn (motive := fun _ => Option Gate × Stat) a
          (fun c => (none, Sum.inl c))
          (fun j => (none, Sum.inr j)))
        fun b r =>
          List.casesOn (motive := fun _ => Option Gate × Stat) r
            (Sum.casesOn (motive := fun _ => Option Gate × Stat) a
              (fun c => Sum.casesOn (motive := fun _ => Option Gate × Stat) b
                (fun d => (none, Sum.inl (c || d)))
                (fun j => (none, bif c then Sum.inl true else Sum.inr j)))
              (fun j => Sum.casesOn (motive := fun _ => Option Gate × Stat) b
                (fun c => (none, bif c then Sum.inl true else Sum.inr j))
                (fun k => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m))))
            (fun _ _ => (none, Sum.inl false))
  let simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
    GateOp.casesOn (motive := fun _ => Option Gate × Stat) op
      (simpAnd m ins) (simpOr m ins) (simpNot m ins) (fun _ => (none, Sum.inl false)) (none, Sum.inl false)
  have hsimplify_ok : ∀ (op : GateOp) (m : ℕ) (ins : List Stat),
      ∀ g ∈ (simplify op m ins).1, fanOK g := by
    intro op m ins g hg
    cases op
    · rcases ins with _ | ⟨a0, _ | ⟨b0, _ | ⟨c0, l0⟩⟩⟩
      · exact (Option.not_mem_none g hg).elim
      · cases a0 <;> exact (Option.not_mem_none g hg).elim
      · cases a0 <;> cases b0
        · exact (Option.not_mem_none g hg).elim
        · rename_i ba wb; cases ba <;> exact (Option.not_mem_none g hg).elim
        · rename_i wa bb; cases bb <;> exact (Option.not_mem_none g hg).elim
        · rename_i wa wb
          dsimp only [simplify, simpAnd] at hg
          rw [Option.mem_def, Option.some.injEq] at hg
          subst hg
          exact ⟨Or.inl rfl, by simp⟩
      · exact (Option.not_mem_none g hg).elim
    · rcases ins with _ | ⟨a0, _ | ⟨b0, _ | ⟨c0, l0⟩⟩⟩
      · exact (Option.not_mem_none g hg).elim
      · cases a0 <;> exact (Option.not_mem_none g hg).elim
      · cases a0 <;> cases b0
        · exact (Option.not_mem_none g hg).elim
        · rename_i ba wb; cases ba <;> exact (Option.not_mem_none g hg).elim
        · rename_i wa bb; cases bb <;> exact (Option.not_mem_none g hg).elim
        · rename_i wa wb
          dsimp only [simplify, simpOr] at hg
          rw [Option.mem_def, Option.some.injEq] at hg
          subst hg
          exact ⟨Or.inr (Or.inl rfl), by simp⟩
      · exact (Option.not_mem_none g hg).elim
    · rcases ins with _ | ⟨a0, l0⟩
      · exact (Option.not_mem_none g hg).elim
      · cases a0
        · exact (Option.not_mem_none g hg).elim
        · dsimp only [simplify, simpNot] at hg
          rw [Option.mem_def, Option.some.injEq] at hg
          subst hg
          exact ⟨Or.inr (Or.inr rfl), by simp⟩
    · exact (Option.not_mem_none g hg).elim
    · exact (Option.not_mem_none g hg).elim
  have hsimplify_sound : ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) →
      ∀ (w : List Bool) (ins : List Stat), ins.length ≤ 2 →
      (∀ s ∈ ins, statValid w.length s) →
      statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
      statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
        = op.eval (ins.map (statVal w)) := by
    intro op hop w ins hlen hv
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a0, _ | ⟨b0, _ | ⟨d0, l0⟩⟩⟩
      · exact ⟨trivial, rfl⟩
      · cases a0 with
        | inl c0 => exact ⟨trivial, by cases c0 <;> rfl⟩
        | inr j0 =>
          have hj : j0 < w.length := hv (Sum.inr j0) (by simp)
          refine ⟨hj, ?_⟩
          rw [andEval]
          dsimp only [simplify, simpAnd, statVal, List.map, List.all, wiresFrom]
          simp
      · have ha0 := hv a0 (by simp)
        have hb0 := hv b0 (by simp)
        cases a0 with
        | inl ba =>
          cases b0 with
          | inl bb => exact ⟨trivial, by cases ba <;> cases bb <;> rfl⟩
          | inr wb =>
            cases ba
            · exact ⟨trivial, rfl⟩
            · refine ⟨hb0, ?_⟩
              rw [andEval]
              dsimp only [simplify, simpAnd, cond, statVal, wiresFrom]
              simp
        | inr wa =>
          cases b0 with
          | inl bb =>
            cases bb
            · refine ⟨trivial, ?_⟩
              rw [andEval]
              dsimp only [simplify, simpAnd, cond, statVal, wiresFrom]
              simp
            · refine ⟨ha0, ?_⟩
              rw [andEval]
              dsimp only [simplify, simpAnd, cond, statVal, wiresFrom]
              simp
          | inr wb =>
            rw [andEval]
            dsimp only [simplify, simpAnd, Option.toList, statValid, statVal, wiresFrom,
              List.foldl, List.map, List.all, List.length]
            refine ⟨by omega, ?_⟩
            rw [andEval]
            exact hgetD_snoc_eq w _ false
      · simp at hlen
    · rcases ins with _ | ⟨a0, _ | ⟨b0, _ | ⟨d0, l0⟩⟩⟩
      · exact ⟨trivial, rfl⟩
      · cases a0 with
        | inl c0 => exact ⟨trivial, by cases c0 <;> rfl⟩
        | inr j0 =>
          have hj : j0 < w.length := hv (Sum.inr j0) (by simp)
          refine ⟨hj, ?_⟩
          rw [orEval]
          dsimp only [simplify, simpOr, statVal, wiresFrom]
          simp
      · have ha0 := hv a0 (by simp)
        have hb0 := hv b0 (by simp)
        cases a0 with
        | inl ba =>
          cases b0 with
          | inl bb => exact ⟨trivial, by cases ba <;> cases bb <;> rfl⟩
          | inr wb =>
            cases ba
            · refine ⟨hb0, ?_⟩
              rw [orEval]
              dsimp only [simplify, simpOr, cond, statVal, wiresFrom]
              simp
            · exact ⟨trivial, rfl⟩
        | inr wa =>
          cases b0 with
          | inl bb =>
            cases bb
            · refine ⟨ha0, ?_⟩
              rw [orEval]
              dsimp only [simplify, simpOr, cond, statVal, wiresFrom]
              simp
            · refine ⟨trivial, ?_⟩
              rw [orEval]
              dsimp only [simplify, simpOr, cond, statVal, wiresFrom]
              simp
          | inr wb =>
            rw [orEval]
            dsimp only [simplify, simpOr, Option.toList, statValid, statVal, wiresFrom,
              List.foldl, List.map, List.any, List.length]
            refine ⟨by omega, ?_⟩
            rw [orEval]
            exact hgetD_snoc_eq w _ false
      · simp at hlen
    · rcases ins with _ | ⟨a0, l0⟩
      · exact ⟨trivial, rfl⟩
      · cases a0 with
        | inl c0 => exact ⟨trivial, rfl⟩
        | inr j0 =>
          have hj : j0 < w.length := hv (Sum.inr j0) (by simp)
          rw [notEval]
          dsimp only [simplify, simpNot, Option.toList, statValid, statVal, wiresFrom,
            List.foldl, List.map, List.headD, List.length]
          refine ⟨by omega, ?_⟩
          rw [notEval]
          exact hgetD_snoc_eq w _ false
  let elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
    (acc.1 ++ [(simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
      acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)
  let elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
    gs.foldl (elimStep n) acc
  have helim_ok : ∀ (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate),
      (∀ g ∈ acc.2, fanOK g) → ∀ g ∈ (elim n gs acc).2, fanOK g := by
    intro n gs
    induction gs with
    | nil => intro acc h; exact h
    | cons g gs ih =>
      intro acc h
      apply ih (elimStep n acc g)
      intro g' hg'
      rcases List.mem_append.1 hg' with h1' | h1'
      · exact h g' h1'
      · exact hsimplify_ok _ _ _ g' (by simpa using h1')
  have hstat_valid_mono : ∀ {m m' : ℕ} (h : m ≤ m') (s : Stat), statValid m s → statValid m' s := by
    intro m m' h s hs
    cases s with
    | inl _ => trivial
    | inr j => exact lt_of_lt_of_le hs h
  have hstat_val_append : ∀ (w t : List Bool) (s : Stat), statValid w.length s →
      statVal (w ++ t) s = statVal w s := by
    intro w t s hs
    cases s with
    | inl _ => rfl
    | inr j => exact List.getD_append _ _ _ _ hs
  let Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
    acc.1.length = w.length ∧ ∀ i : ℕ,
      statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
      statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false
  have hinv_elim : ∀ (n : ℕ) (y : List Bool), y.length = n →
      ∀ (gs : List Gate) (w : List Bool) (acc : List Stat × List Gate),
      (∀ g ∈ gs, fanOK g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
    intro n y hy gs
    induction gs with
    | nil => intro w acc _ h; exact h
    | cons g gs ih =>
      intro w acc hok h
      apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
        (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      obtain ⟨hl, hi⟩ := h
      set w' := wiresFrom acc.2 y with hw'
      have lw' : w'.length = n + acc.2.length := by rw [hw', hlength_wiresFrom, hy]
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := hsimplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a0, _, rfl⟩ := List.mem_map.1 hs
          rw [lw']; exact (hi a0).1)
      rw [lw'] at hs
      set r := simplify g.op (n + acc.2.length) ins with hr
      have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
        rw [hins, List.map_map]
        apply List.map_congr_left
        intro a0 _
        exact (hi a0).2
      have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
        rw [hwiresFrom_append]
      obtain ⟨t, ht, htl⟩ := hwiresFrom_prefix r.1.toList w'
      refine ⟨by simp [elimStep, hl], ?_⟩
      intro i
      change statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
        statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) =
        ((w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false)
      rw [hnew, List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil
        rw [hgetD_snoc_eq, hl, hgetD_snoc_eq]
        exact ⟨hs.1, by rw [hs.2, hvals]⟩
      · rw [hgetD_snoc_ne _ _ _ _ hil, hgetD_snoc_ne _ _ _ _ (by omega)]
        refine ⟨hstat_valid_mono (by omega) _ (hi i).1, ?_⟩
        rw [ht, hstat_val_append _ _ _ (by rw [lw']; exact (hi i).1)]
        exact (hi i).2
  have hsimplify_eff_none : ∀ (g : Gate) (m : ℕ) (env : List Stat) (isZ : ℕ → Bool),
      fanOK g →
      (∀ w, isZ w = true → ∃ c, env.getD w (Sum.inl false) = Sum.inl c) →
      (effInputs g).any isZ = true →
      (simplify g.op m (g.inputs.map fun i => env.getD i (Sum.inl false))).1 = none := by
    intro g m env isZ hg hZ hrz
    cases g
    rename_i op ins
    rcases hg with ⟨hop, hilen⟩
    rcases hop with rfl | rfl | rfl
    · have hrz' : ins.any isZ = true := hrz
      rw [List.any_eq_true] at hrz'
      obtain ⟨w0, hw0m, hw0z⟩ := hrz'
      obtain ⟨c0, hc0⟩ := hZ w0 hw0z
      rcases ins with _ | ⟨a0, _ | ⟨b0, _ | ⟨d0, l0⟩⟩⟩
      · simp at hw0m
      · simp only [List.mem_singleton] at hw0m; subst hw0m
        dsimp only [simplify, simpAnd, List.map]
        rw [hc0]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw0m
        rcases hw0m with rfl | rfl
        · dsimp only [simplify, simpAnd, List.map]
          rw [hc0]
          cases c0 <;> cases env.getD b0 (Sum.inl false) with
          | inl db => cases db <;> rfl
          | inr _ => rfl
        · dsimp only [simplify, simpAnd, List.map]
          rw [hc0]
          cases env.getD a0 (Sum.inl false) with
          | inl da => cases da <;> cases c0 <;> rfl
          | inr _ => cases c0 <;> rfl
      · simp at hilen
    · have hrz' : ins.any isZ = true := hrz
      rw [List.any_eq_true] at hrz'
      obtain ⟨w0, hw0m, hw0z⟩ := hrz'
      obtain ⟨c0, hc0⟩ := hZ w0 hw0z
      rcases ins with _ | ⟨a0, _ | ⟨b0, _ | ⟨d0, l0⟩⟩⟩
      · simp at hw0m
      · simp only [List.mem_singleton] at hw0m; subst hw0m
        dsimp only [simplify, simpOr, List.map]
        rw [hc0]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw0m
        rcases hw0m with rfl | rfl
        · dsimp only [simplify, simpOr, List.map]
          rw [hc0]
          cases c0 <;> cases env.getD b0 (Sum.inl false) with
          | inl db => cases db <;> rfl
          | inr _ => rfl
        · dsimp only [simplify, simpOr, List.map]
          rw [hc0]
          cases env.getD a0 (Sum.inl false) with
          | inl da => cases da <;> cases c0 <;> rfl
          | inr _ => cases c0 <;> rfl
      · simp at hilen
    · have hrz' : (ins.take 1).any isZ = true := hrz
      rcases ins with _ | ⟨a0, t0⟩
      · simp at hrz'
      · simp only [List.take_succ_cons, List.take_zero, List.any_cons, List.any_nil, Bool.or_false] at hrz'
        obtain ⟨c0, hc0⟩ := hZ a0 hrz'
        dsimp only [simplify, simpNot, List.map]
        rw [hc0]
  have helim_count : ∀ (n boundW : ℕ) (isZ : ℕ → Bool),
      (∀ w, isZ w = true → w < boundW) →
      ∀ (gs : List Gate) (acc : List Stat × List Gate),
      boundW ≤ acc.1.length →
      (∀ w, isZ w = true → ∃ c, acc.1.getD w (Sum.inl false) = Sum.inl c) →
      (∀ g ∈ gs, fanOK g) →
      (elim n gs acc).2.length + gs.countP (fun g => (effInputs g).any isZ) ≤ acc.2.length + gs.length := by
    intro n boundW isZ hisZ gs
    induction gs with
    | nil => intro acc _ _ _; simp [elim]
    | cons g gs ih =>
      intro acc hbd hZ hgs
      have hg := hgs g List.mem_cons_self
      let acc1 := elimStep n acc g
      have hbd1 : boundW ≤ acc1.1.length := by
        dsimp [acc1, elimStep]; simp; omega
      have hZ1 : ∀ w, isZ w = true → ∃ c, acc1.1.getD w (Sum.inl false) = Sum.inl c := by
        intro w hw
        have hlt : w < acc.1.length := lt_of_lt_of_le (hisZ w hw) hbd
        dsimp [acc1, elimStep]
        rw [List.getD_append _ _ _ _ hlt]
        exact hZ w hw
      have htail := ih acc1 hbd1 hZ1 (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
      have hfold : elim n (g :: gs) acc = elim n gs acc1 := rfl
      rw [hfold, List.countP_cons, List.length_cons]
      by_cases hrz : (effInputs g).any isZ = true
      · have hnone := hsimplify_eff_none g (n + acc.2.length) acc.1 isZ hg hZ hrz
        have hlen1 : acc1.2.length = acc.2.length := by
          dsimp [acc1, elimStep]; rw [hnone]; simp
        simp only [hrz, ↓reduceIte]
        omega
      · have hlen1 : acc1.2.length ≤ acc.2.length + 1 := by
          dsimp [acc1, elimStep]
          cases (simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;> simp
        simp only [hrz, Bool.false_eq_true, ↓reduceIte]
        omega
  by_cases hdeg_bound : ∀ v : Fin 10, 15 + C.gates.countP (fun g => (effInputs g).contains v.val) ≤ C.size
  · -- Step D: Dispatch to T1, T2, T3
    have h16 : 16 ≤ C.size := by
      have h0 := hdeg_bound 0
      have hp := hdeg_pos 0
      omega
    by_cases h17 : C.size ≤ 17
    · exact hT1 C a b hfan h16 h17 ha_lo ha_hi hb_lo hb_hi hab hdeg_bound h1 h2 h3
    · have h18 : C.size = 18 := by omega
      by_cases hnot : ∃ g ∈ C.gates, g.op = GateOp.not
      · have hdeg3 : ∀ v : Fin 10, C.gates.countP (fun g => (effInputs g).contains v.val) ≤ 3 := by
          intro v
          have hv := hdeg_bound v
          omega
        exact hT3 C a b hfan h18 ha_lo ha_hi hb_lo hb_hi hab hnot hdeg3 h1 h2 h3
      · have hno_not : ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
          intro g hg heq
          exact hnot ⟨g, hg, heq⟩
        have hdeg3 : ∀ v : Fin 10, C.gates.countP (fun g => g.inputs.contains v.val) ≤ 3 := by
          intro v
          have hv := hdeg_bound v
          have hcongr : C.gates.countP (fun g => g.inputs.contains v.val) =
              C.gates.countP (fun g => (effInputs g).contains v.val) := by
            apply List.countP_congr
            intro g hg
            have hnn := hno_not g hg
            rcases (hfan g hg).1 with hop | hop | hop
            · have handFalse : GateOp.and.eval [false] = false := rfl
              dsimp only [effInputs]; rw [hop, handFalse]; rfl
            · have horFalse : GateOp.or.eval [false] = false := rfl
              dsimp only [effInputs]; rw [hop, horFalse]; rfl
            · exact (hnn hop).elim
          rw [hcongr]
          omega
        exact hT2 C a b hfan h18 ha_lo ha_hi hb_lo hb_hi hab hno_not hdeg3 h1 h2 h3
  · obtain ⟨v, hv_not⟩ := Classical.not_forall.mp hdeg_bound
    have hv : C.size < 15 + C.gates.countP (fun g => (effInputs g).contains v.val) := Nat.lt_of_not_le hv_not
    let σ : Equiv.Perm (Fin 10) := ⟨sigma9 v, sigma9Inv v, hs9_inv2 v, hs9_inv1 v⟩
    have hfP_perm : ∀ x : Fin 10 → Bool, fP (x ∘ ⇑σ) = fP x := hfP_sigma9 v
    let env0 : List Stat := List.ofFn (fun i : Fin 10 =>
      if i = v then Sum.inl false else Sum.inr (sigma9 v i).val)
    let isZ : ℕ → Bool := fun w => decide (w = v.val)
    have hisZ_bd : ∀ w, isZ w = true → w < 10 := by
      intro w hw
      simp only [isZ, decide_eq_true_eq] at hw
      rw [hw]; exact v.isLt
    have hZ0 : ∀ w, isZ w = true → ∃ c, env0.getD w (Sum.inl false) = Sum.inl c := by
      intro w hw
      simp only [isZ, decide_eq_true_eq] at hw
      subst hw
      refine ⟨false, ?_⟩
      rw [List.getD_eq_getElem _ _ (by simp [env0]), List.getElem_ofFn]
      simp
    let res := elim 9 C.gates (env0, [])
    have hres_ok : ∀ g ∈ res.2, fanOK g := helim_ok 9 C.gates (env0, []) (by simp)
    have hcnt_eq : C.gates.countP (fun g => (effInputs g).any isZ) =
        C.gates.countP (fun g => (effInputs g).contains v.val) := by
      apply List.countP_congr
      intro g _
      simp [isZ, List.any_eq_true, List.contains_eq_mem]
    have hres_len : res.2.length ≤ 14 := by
      have hc := helim_count 9 10 isZ hisZ_bd C.gates (env0, []) (by simp [env0]) hZ0 hfan
      rw [hcnt_eq] at hc
      change res.2.length + _ ≤ [].length + C.size at hc
      simp only [List.length_nil, Nat.zero_add] at hc
      omega
    have hres_inv : ∀ y : Fin 9 → Bool,
        Inv 9 (List.ofFn y) (C.wires (List.ofFn ((fun k : Fin (9 + 1) => Fin.lastCases false y k) ∘ ⇑σ))) res := by
      intro y
      let x_in : Fin 10 → Bool := (fun k : Fin (9 + 1) => Fin.lastCases false y k) ∘ ⇑σ
      have hinv0 : Inv 9 (List.ofFn y) (List.ofFn x_in) (env0, []) := by
        refine ⟨by simp [env0], ?_⟩
        intro i
        by_cases hi10 : i < 10
        · have he : env0.getD i (Sum.inl false) =
              if (⟨i, hi10⟩ : Fin 10) = v then Sum.inl false else Sum.inr (sigma9 v ⟨i, hi10⟩).val := by
            rw [List.getD_eq_getElem _ _ (by simpa [env0] using hi10), List.getElem_ofFn]
          have hx : (List.ofFn x_in).getD i false = x_in ⟨i, hi10⟩ := by
            rw [List.getD_eq_getElem _ _ (by simpa using hi10), List.getElem_ofFn]
          rw [he, hx]
          by_cases hik : (⟨i, hi10⟩ : Fin 10) = v
          · simp only [hik, ↓reduceIte, statValid, statVal]
            refine ⟨trivial, ?_⟩
            dsimp [x_in, σ]
            rw [hs9_self v]
            change false = Fin.lastCases false y (Fin.last 9)
            rw [Fin.lastCases_last]
          · simp only [hik, ↓reduceIte, statValid, statVal]
            have hne9 : sigma9 v ⟨i, hi10⟩ ≠ 9 := by
              intro h9
              apply hik
              have := congrArg (sigma9Inv v) h9
              rw [hs9_inv2 v] at this
              have h9v : sigma9Inv v 9 = v := by rw [← hs9_self v, hs9_inv2 v]
              exact this.trans h9v
            have hlt9 : (sigma9 v ⟨i, hi10⟩).val < 9 := by
              have := (sigma9 v ⟨i, hi10⟩).isLt
              have : (sigma9 v ⟨i, hi10⟩).val ≠ 9 := fun h => hne9 (Fin.ext h)
              omega
            refine ⟨by simpa using hlt9, ?_⟩
            change (List.ofFn y).getD (sigma9 v ⟨i, hi10⟩).val false = x_in ⟨i, hi10⟩
            rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hlt9), List.getElem_ofFn]
            dsimp [x_in, σ]
            have hcast : sigma9 v ⟨i, hi10⟩ = Fin.castSucc ⟨(sigma9 v ⟨i, hi10⟩).val, hlt9⟩ := by
              ext; rfl
            conv_rhs => rw [hcast, Fin.lastCases_castSucc]
        · have hge : 10 ≤ i := Nat.le_of_not_gt hi10
          rw [List.getD_eq_default _ _ (by simpa [env0] using hge),
            List.getD_eq_default _ _ (by simpa using hge)]
          exact ⟨trivial, rfl⟩
      exact hinv_elim 9 (List.ofFn y) (by simp) C.gates (List.ofFn x_in) (env0, []) hfan hinv0
    let sa := res.1.getD a (Sum.inl false)
    let sb := res.1.getD b (Sum.inl false)
    have hval_a : ∀ y : Fin 9 → Bool,
        statVal (wiresFrom res.2 (List.ofFn y)) sa =
        (C.wires (List.ofFn ((fun k => Fin.lastCases false y k) ∘ ⇑σ))).getD a false :=
      fun y => ((hres_inv y).2 a).2
    have hval_b : ∀ y : Fin 9 → Bool,
        statVal (wiresFrom res.2 (List.ofFn y)) sb =
        (C.wires (List.ofFn ((fun k => Fin.lastCases false y k) ∘ ⇑σ))).getD b false :=
      fun y => ((hres_inv y).2 b).2
    cases hsa : sa with
    | inl ba =>
      cases ba
      · refine ⟨σ, false, ⟨[], 9⟩, hfP_perm, by intro g hg; simp at hg, by rw [circuitSize]; decide, ?_⟩
        intro y
        have ha' := hval_a y
        rw [hsa] at ha'
        change false = _ at ha'
        rw [← ha', Bool.false_and]
        rw [circuitEval, circuitWires]
        dsimp only [wiresFrom, List.foldl]
        rw [List.getD_eq_default _ _ (by simp)]
      · cases hsb : sb with
        | inl bb =>
          cases bb
          · refine ⟨σ, false, ⟨[], 9⟩, hfP_perm, by intro g hg; simp at hg, by rw [circuitSize]; decide, ?_⟩
            intro y
            have hb' := hval_b y
            rw [hsb] at hb'
            change false = _ at hb'
            rw [← hb', Bool.and_false]
            rw [circuitEval, circuitWires]
            dsimp only [wiresFrom, List.foldl]
            rw [List.getD_eq_default _ _ (by simp)]
          · refine ⟨σ, false, ⟨[⟨GateOp.not, [9]⟩], 9⟩, hfP_perm, ?_, by rw [circuitSize]; decide, ?_⟩
            · intro g hg; simp at hg; subst hg; exact ⟨Or.inr (Or.inr rfl), by simp⟩
            · intro y
              have ha' := hval_a y; have hb' := hval_b y
              rw [hsa] at ha'; rw [hsb] at hb'
              change true = _ at ha'; change true = _ at hb'
              rw [← ha', ← hb']
              rw [circuitEval, circuitWires]
              dsimp only [wiresFrom, List.foldl, List.map]
              rw [List.getD_eq_default (List.ofFn y) false (by rw [List.length_ofFn]), notEval]
              dsimp only [List.headD]
              have hget := hgetD_snoc_eq (List.ofFn y) (!false) false
              rw [List.length_ofFn] at hget
              rw [hget]
              rfl
        | inr wb =>
          refine ⟨σ, false, ⟨res.2, wb⟩, hfP_perm, hres_ok, by rw [circuitSize]; exact Nat.le_trans hres_len (by decide), ?_⟩
          intro y
          have ha' := hval_a y; have hb' := hval_b y
          rw [hsa] at ha'; rw [hsb] at hb'
          change true = _ at ha'
          rw [← ha', ← hb', Bool.true_and]
          rfl
    | inr wa =>
      cases hsb : sb with
      | inl bb =>
        cases bb
        · refine ⟨σ, false, ⟨[], 9⟩, hfP_perm, by intro g hg; simp at hg, by rw [circuitSize]; decide, ?_⟩
          intro y
          have hb' := hval_b y
          rw [hsb] at hb'
          change false = _ at hb'
          rw [← hb', Bool.and_false]
          rw [circuitEval, circuitWires]
          dsimp only [wiresFrom, List.foldl]
          rw [List.getD_eq_default _ _ (by simp)]
        · refine ⟨σ, false, ⟨res.2, wa⟩, hfP_perm, hres_ok, by rw [circuitSize]; exact Nat.le_trans hres_len (by decide), ?_⟩
          intro y
          have ha' := hval_a y; have hb' := hval_b y
          rw [hsa] at ha'; rw [hsb] at hb'
          change true = _ at hb'
          rw [← ha', ← hb', Bool.and_true]
          rfl
      | inr wb =>
        let E : Circuit := ⟨res.2 ++ [⟨GateOp.and, [wa, wb]⟩], 9 + res.2.length⟩
        have hfanE : FanInTwo E := by
          intro g hg
          rw [List.mem_append, List.mem_singleton] at hg
          rcases hg with hg | rfl
          · exact hres_ok g hg
          · exact ⟨Or.inl rfl, by simp⟩
        have hszE : E.size ≤ if false = true then 10 else 15 := by
          rw [circuitSize]
          dsimp only [E]
          rw [List.length_append, List.length_singleton]
          change res.2.length + 1 ≤ 15
          omega
        refine ⟨σ, false, E, hfP_perm, hfanE, hszE, ?_⟩
        intro y
        have ha' := hval_a y; have hb' := hval_b y
        rw [hsa] at ha'; rw [hsb] at hb'
        rw [← ha', ← hb']
        change (wiresFrom (res.2 ++ [⟨GateOp.and, [wa, wb]⟩]) (List.ofFn y)).getD (9 + res.2.length) false = _
        rw [hwiresFrom_append]
        have hlenw : (wiresFrom res.2 (List.ofFn y)).length = 9 + res.2.length := by
          rw [hlength_wiresFrom, List.length_ofFn]
        change (wiresFrom res.2 (List.ofFn y) ++ [GateOp.and.eval [(wiresFrom res.2 (List.ofFn y)).getD wa false, (wiresFrom res.2 (List.ofFn y)).getD wb false]]).getD (9 + res.2.length) false = _
        rw [← hlenw, hgetD_snoc_eq, andEval]
        simp [statVal]
