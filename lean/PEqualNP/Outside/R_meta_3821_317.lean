import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_3821_317
    (hMono : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 19 →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x) ≠
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any fun e =>
          x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
    (hSize17 :
      let G := fun x : Fin 10 → Bool =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any fun e =>
          x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin 17),
        let W := fun (x : Fin 10 → Bool) (i : Fin 17) => (D.wires (List.ofFn x)).getD (10 + i.val) false
        let U := fun x : Fin 10 → Bool => W x a || W x b
        (((PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = 17) ∧
          (a ≠ b ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 10 D)) ∧
         (((∀ g ∈ D.gates, g.inputs.length = cond (g.op.eval [false]) 1 2) ∧
           (∃ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not)) ∧
          ((∀ v : Fin 10, (D.gates.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
              cond (g.inputs.contains v.val) (cond (g.op.eval [true, false]) (1 : ℕ) 2) 0).sum ≤ 2) ∧
           ((∃ x, W x a && !W x b) ∧ (∃ x, !W x a && W x b) ∧
            (∀ x, G x = false ∨ (List.ofFn x).count true ≤ 2 → U x = G x))))) →
        ∃ (s : Equiv.Perm (Fin 10)) (v : Bool) (E : PEqualNP.CircuitLowerBounds.Circuit),
          (∀ x, G (x ∘ s) = G x) ∧ PEqualNP.MetaComplexity.FanInTwo E ∧
          E.size ≤ (if v then 10 else 15) ∧
          ∀ y : Fin 9 → Bool, E.eval (List.ofFn y) = U ((Fin.lastCases v y : Fin 10 → Bool) ∘ s))
    (hSize18 :
      let G := fun x : Fin 10 → Bool =>
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85] : List ℕ).any fun e =>
          x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin 18),
        let W := fun (x : Fin 10 → Bool) (i : Fin 18) => (D.wires (List.ofFn x)).getD (10 + i.val) false
        let U := fun x : Fin 10 → Bool => W x a || W x b
        (((PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = 18) ∧
          (a ≠ b ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 10 D)) ∧
         (((∀ g ∈ D.gates, g.inputs.length = cond (g.op.eval [false]) 1 2) ∧
           (∃ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not)) ∧
          ((∀ v : Fin 10, (D.gates.map fun g : PEqualNP.CircuitLowerBounds.Gate =>
              cond (g.inputs.contains v.val) (cond (g.op.eval [true, false]) (1 : ℕ) 2) 0).sum ≤ 3) ∧
           ((∃ x, W x a && !W x b) ∧ (∃ x, !W x a && W x b) ∧
            (∀ x, G x = false ∨ (List.ofFn x).count true ≤ 2 → U x = G x))))) →
        ∃ (s : Equiv.Perm (Fin 10)) (v : Bool) (E : PEqualNP.CircuitLowerBounds.Circuit),
          (∀ x, G (x ∘ s) = G x) ∧ PEqualNP.MetaComplexity.FanInTwo E ∧
          E.size ≤ (if v then 10 else 15) ∧
          ∀ y : Fin 9 → Bool, E.eval (List.ofFn y) = U ((Fin.lastCases v y : Fin 10 → Bool) ∘ s)) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (18 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (10 : ℕ) → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false;       have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x7 x8 x3 || x7 x8 x4;       (∃ (x9 : Fin (10 : ℕ) → Bool), x7 x9 x3 = Bool.true ∧ x7 x9 x4 = Bool.false) → (∃ (x10 : Fin (10 : ℕ) → Bool), x7 x10 x3 = Bool.false ∧ x7 x10 x4 = Bool.true) → (∀ (x11 : Fin (10 : ℕ) → Bool), x1 x11 = Bool.false ∨ List.count Bool.true (List.ofFn x11) ≤ (2 : ℕ) → x8 x11 = x1 x11) → ∃ (x12 : Equiv.Perm (Fin (10 : ℕ))) (x13 : Bool) (x14 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x15 : Fin (10 : ℕ) → Bool), x1 (x15 ∘ ⇑x12) = x1 x15) ∧ PEqualNP.MetaComplexity.FanInTwo x14 ∧ (x14.size ≤ if x13 = Bool.true then (10 : ℕ) else (15 : ℕ)) ∧ ∀ (x15 : Fin (9 : ℕ) → Bool), x14.eval (List.ofFn x15) = x8 ((fun (x16 : Fin ((9 : ℕ) + (1 : ℕ))) => Fin.lastCases x13 x15 x16) ∘ ⇑x12) := by
  classical
  dsimp only
  let G1 : (Fin 10 → Bool) → Bool := fun x =>
    (List.finRange 5).any fun i : Fin 5 =>
      x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1)) ||
      x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) ||
      x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))
  let edgeCodes : List ℕ := [1, 12, 23, 34, 40, 5, 16, 27, 38, 49, 57, 79, 96, 68, 85]
  let G2 : (Fin 10 → Bool) → Bool := fun x =>
    edgeCodes.any fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))
  have hG_eq : ∀ x : Fin 10 → Bool, G1 x = G2 x := by
    intro x
    change (((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) ||
      (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) ||
      (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) ||
      (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) ||
      (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) || false))))) =
      ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) ||
      ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) ||
      ((x 3 && x 8) || ((x 4 && x 9) || ((x 5 && x 7) || ((x 7 && x 9) ||
      ((x 9 && x 6) || ((x 6 && x 8) || ((x 8 && x 5) || false)))))))))))))))
    simp only [Bool.or_false]
    ac_rfl
  have G1_empty : G1 (fun _ => false) = false := by decide
  have G1_single : ∀ v : Fin 10, G1 (fun k => decide (k = v)) = false := by decide
  let nbr : Fin 10 → Fin 10 := ![1, 2, 3, 4, 0, 0, 1, 2, 3, 4]
  have G1_nbr : ∀ v : Fin 10, nbr v ≠ v ∧ G1 (fun k => decide (k = nbr v ∨ k = v)) = true := by
    decide
  have G1_distinguish : ∀ u w : Fin 10, u ≠ w →
      ∃ z : Fin 10, z ≠ u ∧ z ≠ w ∧
        G1 (fun k => decide (k = u ∨ k = z)) = true ∧
        G1 (fun k => decide (k = w ∨ k = z)) = false := by
    decide
  have G1_sub_edge : ∀ v : Fin 10,
      ∃ u w : Fin 10, u ≠ v ∧ w ≠ v ∧ u ≠ w ∧ G1 (fun k => decide (k = u ∨ k = w)) = true := by
    decide
  have count_le_two : ∀ u w : Fin 10,
      (List.ofFn fun k : Fin 10 => decide (k = u ∨ k = w)).count true ≤ 2 := by
    decide
  let permTable : Fin 10 → Fin 10 → Fin 10 :=
    ![![9, 6, 8, 5, 7, 4, 1, 3, 0, 2],
      ![6, 9, 7, 5, 8, 1, 4, 2, 0, 3],
      ![5, 7, 9, 6, 8, 0, 2, 4, 1, 3],
      ![5, 8, 6, 9, 7, 0, 3, 1, 4, 2],
      ![6, 8, 5, 7, 9, 1, 3, 0, 2, 4],
      ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
      ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
      ![1, 0, 4, 3, 2, 6, 5, 9, 8, 7],
      ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]
  have permTable_inj : ∀ v : Fin 10, Function.Injective (permTable v) := by
    intro v a b
    revert v a b
    decide
  have permTable_last : ∀ v : Fin 10, permTable v v = 9 := by decide
  let permEquiv (v : Fin 10) : Equiv.Perm (Fin 10) :=
    Equiv.ofBijective (permTable v) (Finite.injective_iff_bijective.mp (permTable_inj v))
  let adj (u w : Fin 10) : Bool :=
    edgeCodes.any fun e =>
      (u.val == e / 10 && w.val == e % 10) || (w.val == e / 10 && u.val == e % 10)
  have adj_perm : ∀ v u w : Fin 10, adj (permTable v u) (permTable v w) = adj u w := by decide
  have G2_iff : ∀ x : Fin 10 → Bool,
      G2 x = true ↔ ∃ u w : Fin 10, adj u w = true ∧ x u = true ∧ x w = true := by
    intro x
    constructor
    · intro h
      simp only [G2, List.any_eq_true, Bool.and_eq_true] at h
      obtain ⟨e, he, hu, hw⟩ := h
      refine ⟨Fin.ofNat 10 (e / 10), Fin.ofNat 10 (e % 10), ?_, hu, hw⟩
      have ha : ∀ e ∈ edgeCodes, adj (Fin.ofNat 10 (e / 10)) (Fin.ofNat 10 (e % 10)) = true := by
        decide
      exact ha e he
    · rintro ⟨u, w, hadj, hu, hw⟩
      simp only [adj, List.any_eq_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hadj
      obtain ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hadj
      · simp only [G2, List.any_eq_true, Bool.and_eq_true]
        refine ⟨e, he, ?_, ?_⟩
        · have : Fin.ofNat 10 (e / 10) = u := by
            apply Fin.ext
            simp [Fin.ofNat, Nat.mod_eq_of_lt (h1 ▸ u.isLt), h1]
          rwa [this]
        · have : Fin.ofNat 10 (e % 10) = w := by
            apply Fin.ext
            simp [Fin.ofNat, Nat.mod_eq_of_lt (h2 ▸ w.isLt), h2]
          rwa [this]
      · simp only [G2, List.any_eq_true, Bool.and_eq_true]
        refine ⟨e, he, ?_, ?_⟩
        · have : Fin.ofNat 10 (e / 10) = w := by
            apply Fin.ext
            simp [Fin.ofNat, Nat.mod_eq_of_lt (h1 ▸ w.isLt), h1]
          rwa [this]
        · have : Fin.ofNat 10 (e % 10) = u := by
            apply Fin.ext
            simp [Fin.ofNat, Nat.mod_eq_of_lt (h2 ▸ u.isLt), h2]
          rwa [this]
  have G1_perm : ∀ (v : Fin 10) (x : Fin 10 → Bool), G1 (x ∘ permEquiv v) = G1 x := by
    intro v x
    rw [hG_eq, hG_eq]
    apply Bool.eq_iff_iff.mpr
    rw [G2_iff, G2_iff]
    constructor
    · rintro ⟨u, w, hadj, hu, hw⟩
      refine ⟨permEquiv v u, permEquiv v w, ?_, hu, hw⟩
      simpa [permEquiv, adj_perm] using hadj
    · rintro ⟨u, w, hadj, hu, hw⟩
      obtain ⟨u', rfl⟩ := (permEquiv v).surjective u
      obtain ⟨w', rfl⟩ := (permEquiv v).surjective w
      refine ⟨u', w', ?_, hu, hw⟩
      simpa [permEquiv, adj_perm] using hadj

  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w
  have eval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have eval_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
  have eval_not : ∀ l : List Bool, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  have wires_eq : ∀ (C : Circuit) (w : List Bool), C.wires w = run C.gates w := fun _ _ => rfl
  have gateAt_eq : ∀ (C : Circuit) (j : ℕ), gateAt C j = C.gates.getD j ⟨GateOp.or, []⟩ := fun _ _ => rfl
  have run_nil : ∀ w, run [] w = w := fun _ => rfl
  have run_cons : ∀ g gs w, run (g :: gs) w = run gs (step w g) := fun _ _ _ => rfl
  have run_append : ∀ gs1 gs2 w, run (gs1 ++ gs2) w = run gs2 (run gs1 w) := by
    intro gs1 gs2 w; simp [run, List.foldl_append]
  have run_length : ∀ gs w, (run gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [run]
    | cons g gs ih => intro w; rw [run_cons, ih]; simp [step]; omega
  have run_getD_lt : ∀ gs w i, i < w.length → (run gs w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [run_cons, ih (step w g) i (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have run_getD_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
      (run gs w).getD (w.length + j) false =
        gs[j].op.eval (gs[j].inputs.map fun i => (run (gs.take j) w).getD i false) ∧
      ∀ i, (run (gs.take j) w).getD i false =
        if i < w.length + j then (run gs w).getD i false else false := by
    intro gs w j hj
    have hsp : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
      rw [List.cons_getElem_drop_succ, List.take_append_drop]
    have hlen : (run (gs.take j) w).length = w.length + j := by
      rw [run_length, List.length_take]; omega
    have hw : run gs w = run (gs.drop (j + 1)) (step (run (gs.take j) w) gs[j]) := by
      conv_lhs => rw [hsp]
      rw [run_append, run_cons]
    have hpre : ∀ i < w.length + j + 1,
        (run gs w).getD i false = (step (run (gs.take j) w) gs[j]).getD i false := by
      intro i hi
      rw [hw, run_getD_lt _ _ _ (by simp [step, hlen]; omega)]
    refine ⟨?_, ?_⟩
    · rw [hpre _ (by omega)]
      simp only [step, ← hlen]
      simp
    · intro i
      split_ifs with hi
      · rw [hpre i (by omega)]
        exact (List.getD_append _ _ _ _ (by omega)).symm
      · exact List.getD_eq_default _ _ (by omega)

  have mono_eval : ∀ (gs : List Gate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ i, w1.getD i false = true → w2.getD i false = true) →
      ∀ i, (run gs w1).getD i false = true → (run gs w2).getD i false = true := by
    intro gs hm
    induction gs with
    | nil => intro w1 w2 _ hle i hi; exact hle i hi
    | cons g gs ih =>
      intro w1 w2 hlen hle
      apply ih (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg')) (step w1 g) (step w2 g)
      · simp [step, hlen]
      · intro i hi
        by_cases hlt : i < w1.length
        · rw [List.getD_append _ _ _ _ hlt] at hi
          rw [List.getD_append _ _ _ _ (by omega)]
          exact hle i hi
        · by_cases heq : i = w1.length
          · subst heq
            simp only [step] at hi ⊢
            rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self] at hi
            rw [hlen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
            simp only [List.getD_cons_zero] at hi ⊢
            have hg := (hm g List.mem_cons_self).1
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
            rcases hg with hop | hop
            · rw [hop] at hi ⊢
              simp only [eval_and, List.all_eq_true, List.mem_map, id_eq] at hi ⊢
              rintro b ⟨k, hk, rfl⟩
              exact hle k (hi _ ⟨k, hk, rfl⟩)
            · rw [hop] at hi ⊢
              simp only [eval_or, List.any_eq_true, List.mem_map, id_eq] at hi ⊢
              obtain ⟨b, ⟨k, hk, rfl⟩, hb⟩ := hi
              exact ⟨_, ⟨k, hk, rfl⟩, hle k hb⟩
          · rw [List.getD_eq_default _ _ (by simp [step]; omega)] at hi
            cases hi

  let evalSym (w : List Bool) (s : Bool ⊕ ℕ) : Bool := Sum.elim id (fun k => w.getD k false) s
  let symBound (n : ℕ) (s : Bool ⊕ ℕ) : Prop := Sum.elim (fun _ => True) (fun k => k < n) s
  let simpGate (st : List (Bool ⊕ ℕ)) (outLen : ℕ) (g : Gate) : (Bool ⊕ ℕ) × Option Gate :=
    let look (i : ℕ) : Bool ⊕ ℕ := st.getD i (.inl false)
    GateOp.casesOn (motive := fun _ => (Bool ⊕ ℕ) × Option Gate) g.op
      (List.casesOn (motive := fun _ => (Bool ⊕ ℕ) × Option Gate) g.inputs (.inl true, none) fun i r1 =>
        List.casesOn (motive := fun _ => (Bool ⊕ ℕ) × Option Gate) r1 (look i, none) fun j _ =>
          Sum.elim
            (fun bi => if bi then (look j, none) else (.inl false, none))
            (fun wi => Sum.elim
              (fun bj => if bj then (.inr wi, none) else (.inl false, none))
              (fun wj => if wi = wj then (.inr wi, none) else (.inr outLen, some ⟨.and, [wi, wj]⟩))
              (look j))
            (look i))
      (List.casesOn (motive := fun _ => (Bool ⊕ ℕ) × Option Gate) g.inputs (.inl false, none) fun i r1 =>
        List.casesOn (motive := fun _ => (Bool ⊕ ℕ) × Option Gate) r1 (look i, none) fun j _ =>
          Sum.elim
            (fun bi => if bi then (.inl true, none) else (look j, none))
            (fun wi => Sum.elim
              (fun bj => if bj then (.inl true, none) else (.inr wi, none))
              (fun wj => if wi = wj then (.inr wi, none) else (.inr outLen, some ⟨.or, [wi, wj]⟩))
              (look j))
            (look i))
      (List.casesOn (motive := fun _ => (Bool ⊕ ℕ) × Option Gate) g.inputs (.inl true, none) fun i _ =>
        Sum.elim (fun b => (.inl (!b), none)) (fun w => (.inr outLen, some ⟨.not, [w]⟩)) (look i))
      (fun _ => (.inl false, none))
      (.inl false, none)

  have simpGate_props : ∀ (st : List (Bool ⊕ ℕ)) (outLen : ℕ) (g : Gate),
      (∀ s ∈ st, symBound outLen s) →
      (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      let r := simpGate st outLen g
      Option.elim r.2 (symBound outLen r.1) (fun g' =>
        r.1 = .inr outLen ∧
        g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g'.inputs.length ≤ 2 ∧
        (∀ i ∈ g'.inputs, i < outLen) ∧
        g'.inputs.length = (if g'.op.eval [false] then 1 else 2) ∧
        (g'.op ≠ GateOp.not → g'.inputs.Nodup)) := by
    intro st outLen g hst hg
    have hlook : ∀ i, symBound outLen (st.getD i (.inl false)) := by
      intro i
      rw [List.getD_eq_getElem?_getD]
      cases h : st[i]? with
      | none => trivial
      | some s => exact hst s (List.mem_of_getElem? h)
    rcases g with ⟨op, ins⟩
    rcases hg with ⟨hop, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨i, _ | ⟨j, l⟩⟩
      · simp [simpGate, symBound]
      · simpa [simpGate] using hlook i
      · have hli := hlook i; have hlj := hlook j
        simp only [simpGate]
        cases hi : st.getD i (.inl false) with
        | inl bi =>
          cases bi
          · simp [symBound]
          · simpa [symBound] using hlj
        | inr wi =>
          rw [hi] at hli
          cases hj : st.getD j (.inl false) with
          | inl bj =>
            cases bj
            · simp [symBound]
            · simpa [symBound] using hli
          | inr wj =>
            rw [hj] at hlj
            by_cases heq : wi = wj
            · simpa [heq, symBound] using hli
            · simp only [heq, ↓reduceIte, Sum.elim_inr, Option.elim_some, true_and, eval_and,
                List.length_cons, List.length_nil, Set.mem_insert_iff, Set.mem_singleton_iff,
                true_or, Nat.reduceLeDiff, List.mem_cons, List.not_mem_nil, or_false,
                forall_eq_or_imp, forall_eq, List.nodup_cons, List.nodup_nil, not_false_eq_true,
                and_true]
              exact ⟨⟨hli, hlj⟩, rfl, fun _ => trivial⟩
    · rcases ins with _ | ⟨i, _ | ⟨j, l⟩⟩
      · simp [simpGate, symBound]
      · simpa [simpGate] using hlook i
      · have hli := hlook i; have hlj := hlook j
        simp only [simpGate]
        cases hi : st.getD i (.inl false) with
        | inl bi =>
          cases bi
          · simpa [symBound] using hlj
          · simp [symBound]
        | inr wi =>
          rw [hi] at hli
          cases hj : st.getD j (.inl false) with
          | inl bj =>
            cases bj
            · simpa [symBound] using hli
            · simp [symBound]
          | inr wj =>
            rw [hj] at hlj
            by_cases heq : wi = wj
            · simpa [heq, symBound] using hli
            · simp only [heq, ↓reduceIte, Sum.elim_inr, Option.elim_some, true_and, eval_or,
                List.length_cons, List.length_nil, Set.mem_insert_iff, Set.mem_singleton_iff,
                true_or, or_true, Nat.reduceLeDiff, List.mem_cons, List.not_mem_nil, or_false,
                forall_eq_or_imp, forall_eq, List.nodup_cons, List.nodup_nil, not_false_eq_true,
                and_true]
              exact ⟨⟨hli, hlj⟩, rfl, fun _ => trivial⟩
    · rcases ins with _ | ⟨i, l⟩
      · simp [simpGate, symBound]
      · have hli := hlook i
        simp only [simpGate]
        cases hi : st.getD i (.inl false) with
        | inl bi => simp [symBound]
        | inr wi =>
          rw [hi] at hli
          simp only [Sum.elim_inr, Option.elim_some, true_and, eval_not, List.length_cons,
            List.length_nil, Set.mem_insert_iff, Set.mem_singleton_iff, or_true, Nat.reduceLeDiff,
            List.mem_singleton, forall_eq, ne_eq, not_true_eq_false, IsEmpty.forall_iff, and_true]
          exact ⟨hli, rfl⟩

  have simpGate_sound : ∀ (st : List (Bool ⊕ ℕ)) (wOld wNew : List Bool) (g : Gate),
      (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ i, wOld.getD i false = evalSym wNew (st.getD i (.inl false))) →
      let r := simpGate st wNew.length g
      g.op.eval (g.inputs.map fun i => wOld.getD i false) =
        Option.elim r.2 (evalSym wNew r.1) (fun g' => evalSym (step wNew g') r.1) := by
    intro st wOld wNew g hg heq
    rcases g with ⟨op, ins⟩
    rcases hg with ⟨hop, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
      · simp [simpGate, eval_and, evalSym]
      · simp only [simpGate, eval_and, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, Option.elim_none]
        exact heq i
      · simp only [simpGate, eval_and, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, heq]
        cases st.getD i (.inl false) with
        | inl bi =>
          cases bi with
          | false => simp [evalSym]
          | true => simp [evalSym]
        | inr wi =>
          cases st.getD j (.inl false) with
          | inl bj => cases bj <;> simp [evalSym]
          | inr wj =>
            by_cases h : wi = wj
            · simp [h, evalSym]
            · simp [h, evalSym, step, eval_and]
      · simp at hlen
    · rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
      · simp [simpGate, eval_or, evalSym]
      · simp only [simpGate, eval_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, Option.elim_none]
        exact heq i
      · simp only [simpGate, eval_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, heq]
        cases st.getD i (.inl false) with
        | inl bi =>
          cases bi with
          | true => simp [evalSym]
          | false => simp [evalSym]
        | inr wi =>
          cases st.getD j (.inl false) with
          | inl bj => cases bj <;> simp [evalSym]
          | inr wj =>
            by_cases h : wi = wj
            · simp [h, evalSym]
            · simp [h, evalSym, step, eval_or]
      · simp at hlen
    · rcases ins with _ | ⟨i, l⟩
      · simp [simpGate, eval_not, evalSym]
      · simp only [simpGate, eval_not, List.map_cons, List.headD_cons, heq]
        cases st.getD i (.inl false) with
        | inl bi => simp [evalSym]
        | inr wi => simp [evalSym, step, eval_not]

  let compStep (ov : ℕ → Option (Bool ⊕ ℕ)) (m : ℕ)
      (acc : List (Bool ⊕ ℕ) × List Gate × ℕ) (g : Gate) :
      List (Bool ⊕ ℕ) × List Gate × ℕ :=
    let st := acc.1
    let gs := acc.2.1
    let j := acc.2.2
    Option.elim (ov j)
      (let res := simpGate st (m + gs.length) g
       Option.elim res.2 (st ++ [res.1], gs, j + 1) (fun g' => (st ++ [res.1], gs ++ [g'], j + 1)))
      (Sum.elim (fun b => (st ++ [.inl b], gs, j + 1))
                (fun k => (st ++ [st.getD k (.inl false)], gs, j + 1)))

  let compile (ov : ℕ → Option (Bool ⊕ ℕ)) (m : ℕ) (init : List (Bool ⊕ ℕ)) (gs : List Gate) :=
    gs.foldl (compStep ov m) (init, [], 0)

  have compStep_prefix : ∀ ov m acc g,
      ∃ s, (compStep ov m acc g).1 = acc.1 ++ [s] ∧
        ((compStep ov m acc g).2.1 = acc.2.1 ∨ ∃ g', (compStep ov m acc g).2.1 = acc.2.1 ++ [g']) ∧
        (compStep ov m acc g).2.2 = acc.2.2 + 1 := by
    intro ov m acc g
    simp only [compStep]
    cases ov acc.2.2 with
    | none =>
      cases (simpGate acc.1 (m + acc.2.1.length) g).2 with
      | none => exact ⟨_, rfl, Or.inl rfl, rfl⟩
      | some g' => exact ⟨_, rfl, Or.inr ⟨g', rfl⟩, rfl⟩
    | some o =>
      cases o with
      | inl b => exact ⟨_, rfl, Or.inl rfl, rfl⟩
      | inr k => exact ⟨_, rfl, Or.inl rfl, rfl⟩

  have compile_fold_inv : ∀ (ov : ℕ → Option (Bool ⊕ ℕ)) (m : ℕ) (gs : List Gate)
      (st0 : List (Bool ⊕ ℕ)) (out0 : List Gate) (j0 : ℕ),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ s ∈ st0, symBound (m + out0.length) s) →
      FanInTwo ⟨out0, 0⟩ →
      ReadsBack m ⟨out0, 0⟩ →
      (∀ g ∈ out0, g.inputs.length = (if g.op.eval [false] then 1 else 2) ∧ (g.op ≠ GateOp.not → g.inputs.Nodup)) →
      let res := gs.foldl (compStep ov m) (st0, out0, j0)
      res.1.length = st0.length + gs.length ∧
      (∀ i < st0.length, res.1.getD i (.inl false) = st0.getD i (.inl false)) ∧
      res.2.1.length ≤ out0.length + gs.length ∧
      res.2.2 = j0 + gs.length ∧
      (∀ s ∈ res.1, symBound (m + res.2.1.length) s) ∧
      FanInTwo ⟨res.2.1, 0⟩ ∧
      ReadsBack m ⟨res.2.1, 0⟩ ∧
      (∀ g ∈ res.2.1, g.inputs.length = (if g.op.eval [false] then 1 else 2) ∧ (g.op ≠ GateOp.not → g.inputs.Nodup)) := by
    intro ov m gs
    induction gs with
    | nil =>
      intro st0 out0 j0 _ hst hfan hrb hcl
      exact ⟨by simp, fun _ _ => rfl, by simp, by simp, hst, hfan, hrb, hcl⟩
    | cons g gs ih =>
      intro st0 out0 j0 hgs hst hfan hrb hcl
      have hg := hgs g List.mem_cons_self
      have htail : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
      have hlook : ∀ i, symBound (m + out0.length) (st0.getD i (.inl false)) := by
        intro i
        rw [List.getD_eq_getElem?_getD]
        cases h : st0[i]? with
        | none => trivial
        | some s => exact hst s (List.mem_of_getElem? h)
      have hmonoB : ∀ (n1 n2 : ℕ) (s : Bool ⊕ ℕ), n1 ≤ n2 → symBound n1 s → symBound n2 s := by
        intro n1 n2 s hle hs; cases s <;> simp [symBound] at hs ⊢; omega
      have hstep : ∃ s, (compStep ov m (st0, out0, j0) g).1 = st0 ++ [s] ∧
          (compStep ov m (st0, out0, j0) g).2.1.length ≤ out0.length + 1 ∧
          (compStep ov m (st0, out0, j0) g).2.2 = j0 + 1 ∧
          (∀ s' ∈ (compStep ov m (st0, out0, j0) g).1, symBound (m + (compStep ov m (st0, out0, j0) g).2.1.length) s') ∧
          FanInTwo ⟨(compStep ov m (st0, out0, j0) g).2.1, 0⟩ ∧
          ReadsBack m ⟨(compStep ov m (st0, out0, j0) g).2.1, 0⟩ ∧
          (∀ g' ∈ (compStep ov m (st0, out0, j0) g).2.1,
            g'.inputs.length = (if g'.op.eval [false] then 1 else 2) ∧ (g'.op ≠ GateOp.not → g'.inputs.Nodup)) := by
        cases hov : ov j0 with
        | some o =>
          cases o with
          | inl b =>
            simp only [compStep, hov, Option.elim_some, Sum.elim_inl]
            refine ⟨.inl b, rfl, by omega, trivial, ?_, hfan, hrb, hcl⟩
            intro s' hs'
            rcases List.mem_append.mp hs' with h1 | h1
            · exact hst s' h1
            · simp only [List.mem_singleton] at h1; subst h1; trivial
          | inr k =>
            simp only [compStep, hov, Option.elim_some, Sum.elim_inr]
            refine ⟨st0.getD k (.inl false), rfl, by omega, trivial, ?_, hfan, hrb, hcl⟩
            intro s' hs'
            rcases List.mem_append.mp hs' with h1 | h1
            · exact hst s' h1
            · simp only [List.mem_singleton] at h1; subst h1; exact hlook k
        | none =>
          have hp := simpGate_props st0 (m + out0.length) g hst hg
          dsimp only at hp
          cases h2 : (simpGate st0 (m + out0.length) g).2 with
          | none =>
            rw [h2] at hp
            simp only [Option.elim_none] at hp
            simp only [compStep, hov, h2, Option.elim_none]
            refine ⟨_, rfl, by omega, trivial, ?_, hfan, hrb, hcl⟩
            intro s' hs'
            rcases List.mem_append.mp hs' with h1 | h1
            · exact hst s' h1
            · simp only [List.mem_singleton] at h1; subst h1; exact hp
          | some g' =>
            rw [h2] at hp
            simp only [Option.elim_some] at hp
            obtain ⟨hr1, hop', hlen', hlt', hcl1, hcl2⟩ := hp
            simp only [compStep, hov, h2, Option.elim_none, Option.elim_some]
            refine ⟨_, rfl, by simp, trivial, ?_, ?_, ?_, ?_⟩
            · intro s' hs'
              rcases List.mem_append.mp hs' with h1 | h1
              · exact hmonoB _ _ s' (by simp) (hst s' h1)
              · simp only [List.mem_singleton] at h1; subst h1
                rw [hr1]; simp [symBound]
            · intro g1 hg1
              rcases List.mem_append.mp hg1 with h1 | h1
              · exact hfan g1 h1
              · simp only [List.mem_singleton] at h1; subst h1; exact ⟨hop', hlen'⟩
            · intro idx hidx i hi
              simp only [List.length_append, List.length_singleton] at hidx
              by_cases hlt : idx < out0.length
              · have hga : gateAt ⟨out0 ++ [g'], 0⟩ idx = gateAt ⟨out0, 0⟩ idx := by
                  rw [gateAt_eq, gateAt_eq]; exact List.getD_append _ _ _ _ hlt
                rw [hga] at hi
                exact hrb idx hlt i hi
              · have heq : idx = out0.length := by omega
                subst heq
                have hga : gateAt ⟨out0 ++ [g'], 0⟩ out0.length = g' := by
                  simp [gateAt_eq]
                rw [hga] at hi
                exact hlt' i hi
            · intro g1 hg1
              rcases List.mem_append.mp hg1 with h1 | h1
              · exact hcl g1 h1
              · simp only [List.mem_singleton] at h1; subst h1; exact ⟨hcl1, hcl2⟩
      obtain ⟨s, h1, h2, h3, h4, h5, h6, h7⟩ := hstep
      set nxt := compStep ov m (st0, out0, j0) g
      have hrec := ih nxt.1 nxt.2.1 nxt.2.2 htail h4 h5 h6 h7
      have heta : (nxt.1, nxt.2.1, nxt.2.2) = nxt := rfl
      rw [heta] at hrec
      dsimp only at hrec
      refine ⟨?_, ?_, ?_, ?_, hrec.2.2.2.2.1, hrec.2.2.2.2.2.1, hrec.2.2.2.2.2.2.1, hrec.2.2.2.2.2.2.2⟩
      · change (gs.foldl (compStep ov m) nxt).1.length = _
        rw [hrec.1, h1]; simp; omega
      · intro i hi
        change (gs.foldl (compStep ov m) nxt).1.getD i (.inl false) = _
        rw [hrec.2.1 i (by rw [h1]; simp; omega), h1, List.getD_append _ _ _ _ hi]
      · change (gs.foldl (compStep ov m) nxt).2.1.length ≤ _
        have hr := hrec.2.2.1; simp only [List.length_cons]; omega
      · change (gs.foldl (compStep ov m) nxt).2.2 = _
        rw [hrec.2.2.2.1, h3]; simp only [List.length_cons]; omega

  have compile_sound_gen : ∀ (ov : ℕ → Option (Bool ⊕ ℕ)) (m : ℕ) (gs : List Gate)
      (st0 : List (Bool ⊕ ℕ)) (out0 : List Gate) (j0 : ℕ) (wOld wNew : List Bool),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ s ∈ st0, symBound (m + out0.length) s) →
      wOld.length = st0.length →
      wNew.length = m + out0.length →
      (∀ i, wOld.getD i false = evalSym wNew (st0.getD i (.inl false))) →
      (∀ k (hk : k < gs.length), Option.elim (ov (j0 + k)) True
        (Sum.elim (fun b => (run gs wOld).getD (wOld.length + k) false = b)
                  (fun idx => (run gs wOld).getD (wOld.length + k) false = (run gs wOld).getD idx false ∧ idx < wOld.length + k))) →
      let res := gs.foldl (compStep ov m) (st0, out0, j0)
      ∀ i, (run gs wOld).getD i false =
        evalSym (run (res.2.1.drop out0.length) wNew) (res.1.getD i (.inl false)) := by
    intro ov m gs
    induction gs with
    | nil =>
      intro st0 out0 j0 wOld wNew _ _ _ _ heq _
      dsimp only
      intro i
      simpa [run] using heq i
    | cons g gs ih =>
      intro st0 out0 j0 wOld wNew hgs hst hwo hwn heq hov
      dsimp only
      have hg := hgs g List.mem_cons_self
      have htail : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
      have hov0 := hov 0 (Nat.zero_lt_succ _)
      simp only [Nat.add_zero] at hov0
      have hgate0 : (run (g :: gs) wOld).getD wOld.length false =
          g.op.eval (g.inputs.map fun i => wOld.getD i false) := by
        rw [run_cons, run_getD_lt _ _ _ (by simp [step])]
        simp [step]
      have hovTail : ∀ k (hk : k < gs.length), Option.elim (ov (j0 + 1 + k)) True
          (Sum.elim (fun b => (run gs (step wOld g)).getD ((step wOld g).length + k) false = b)
                    (fun idx => (run gs (step wOld g)).getD ((step wOld g).length + k) false =
                      (run gs (step wOld g)).getD idx false ∧ idx < (step wOld g).length + k)) := by
        intro k hk
        have h := hov (k + 1) (Nat.succ_lt_succ hk)
        have h1 : j0 + (k + 1) = j0 + 1 + k := by omega
        have h2 : wOld.length + (k + 1) = (step wOld g).length + k := by simp [step]; omega
        rw [h1, h2] at h
        simpa [run_cons] using h
      have heq_ext : ∀ (s : Bool ⊕ ℕ) (wNew' : List Bool)
          (hpre : ∀ i < wNew.length, wNew'.getD i false = wNew.getD i false)
          (hval : g.op.eval (g.inputs.map fun i => wOld.getD i false) = evalSym wNew' s),
          ∀ i, (step wOld g).getD i false = evalSym wNew' ((st0 ++ [s]).getD i (.inl false)) := by
        intro s wNew' hpre hval i
        by_cases hi : i < st0.length
        · rw [List.getD_append _ _ _ _ (by omega : i < wOld.length),
            List.getD_append _ _ _ _ hi, heq i]
          have hs : symBound (m + out0.length) (st0.getD i (.inl false)) := by
            rw [List.getD_eq_getElem?_getD]
            cases h : st0[i]? with
            | none => trivial
            | some x => exact hst x (List.mem_of_getElem? h)
          cases hx : st0.getD i (.inl false) with
          | inl b => rfl
          | inr k =>
            rw [hx] at hs
            simp only [symBound, Sum.elim_inr] at hs
            simp only [evalSym, Sum.elim_inr]
            exact (hpre k (by omega)).symm
        · by_cases heqi : i = st0.length
          · subst heqi
            rw [show (step wOld g).getD st0.length false = g.op.eval (g.inputs.map fun k => wOld.getD k false) by
              simp [step, ← hwo]]
            rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
            exact hval
          · rw [List.getD_eq_default _ _ (by simp [step]; omega),
              List.getD_eq_default _ _ (by simp; omega)]
            rfl
      have hstep_drop : ∀ (st1 : List (Bool ⊕ ℕ)) (out1 : List Gate) (wNew1 : List Bool),
          (compStep ov m (st0, out0, j0) g) = (st1, out1, j0 + 1) →
          (∀ s ∈ st1, symBound (m + out1.length) s) →
          (step wOld g).length = st1.length →
          wNew1.length = m + out1.length →
          (∀ i, (step wOld g).getD i false = evalSym wNew1 (st1.getD i (.inl false))) →
          (∀ l : List Gate, run (out1.drop out0.length ++ l) wNew = run l wNew1) →
          ∀ i, (run (g :: gs) wOld).getD i false =
            evalSym (run (((g :: gs).foldl (compStep ov m) (st0, out0, j0)).2.1.drop out0.length) wNew)
              (((g :: gs).foldl (compStep ov m) (st0, out0, j0)).1.getD i (.inl false)) := by
        intro st1 out1 wNew1 hcs hst1 hwo1 hwn1 heq1 hrun1 i
        rw [List.foldl_cons, hcs]
        have hih := ih st1 out1 (j0 + 1) (step wOld g) wNew1 htail hst1 hwo1 hwn1 heq1 hovTail i
        rw [run_cons, hih]
        have hpreOut : ∀ (gs' : List Gate) (st' : List (Bool ⊕ ℕ)) (o' : List Gate) (j' : ℕ),
            ∃ t, (gs'.foldl (compStep ov m) (st', o', j')).2.1 = o' ++ t := by
          intro gs'
          induction gs' with
          | nil => intro _ _ _; exact ⟨[], by simp⟩
          | cons gx gxs ihx =>
            intro st' o' j'
            obtain ⟨_, _, h2 | ⟨g', h2⟩, _⟩ := compStep_prefix ov m (st', o', j') gx
            · obtain ⟨t, ht⟩ := ihx _ _ _
              refine ⟨t, ?_⟩; rw [List.foldl_cons, ht, h2]
            · obtain ⟨t, ht⟩ := ihx _ _ _
              refine ⟨g' :: t, ?_⟩; rw [List.foldl_cons, ht, h2, List.append_assoc]; rfl
        obtain ⟨t, ht⟩ := hpreOut gs st1 out1 (j0 + 1)
        have hsub : out0.length ≤ out1.length := by
          obtain ⟨_, _, h2 | ⟨g', h2⟩, _⟩ := compStep_prefix ov m (st0, out0, j0) g
          · rw [hcs] at h2; simp at h2; rw [h2]
          · rw [hcs] at h2; simp at h2; rw [h2]; simp
        have hdrop : (out1 ++ t).drop out0.length = out1.drop out0.length ++ t :=
          List.drop_append_of_le_length hsub
        have hdrop1 : (out1 ++ t).drop out1.length = t := by
          rw [List.drop_append_of_le_length le_rfl, List.drop_length, List.nil_append]
        change evalSym (run ((gs.foldl (compStep ov m) (st1, out1, j0 + 1)).2.1.drop out1.length) wNew1) _ =
          evalSym (run ((gs.foldl (compStep ov m) (st1, out1, j0 + 1)).2.1.drop out0.length) wNew) _
        rw [ht, hdrop, hdrop1, hrun1 t]
      cases hovj : ov j0 with
      | some o =>
        rw [hovj] at hov0
        cases o with
        | inl b =>
          simp only [Option.elim_some, Sum.elim_inl] at hov0
          apply hstep_drop (st0 ++ [.inl b]) out0 wNew (by simp [compStep, hovj])
          · intro s hs; rcases List.mem_append.mp hs with h | h
            · exact hst s h
            · simp at h; subst h; trivial
          · simp [step, hwo]
          · exact hwn
          · exact heq_ext (.inl b) wNew (fun _ _ => rfl) (by rw [← hgate0]; exact hov0)
          · intro l; simp [run]
        | inr k =>
          simp only [Option.elim_some, Sum.elim_inr] at hov0
          have hkl : k < st0.length := by omega
          have hvalk : g.op.eval (g.inputs.map fun i => wOld.getD i false) =
              evalSym wNew (st0.getD k (.inl false)) := by
            rw [← hgate0, hov0.1, run_cons, run_getD_lt _ _ _ (by simp [step]; omega),
              List.getD_append _ _ _ _ (by omega), heq k]
          apply hstep_drop (st0 ++ [st0.getD k (.inl false)]) out0 wNew (by simp [compStep, hovj])
          · intro s hs; rcases List.mem_append.mp hs with h | h
            · exact hst s h
            · simp at h; subst h
              cases hq : st0[k]? with
              | none => trivial
              | some x => exact hst x (List.mem_of_getElem? hq)
          · simp [step, hwo]
          · exact hwn
          · exact heq_ext _ wNew (fun _ _ => rfl) hvalk
          · intro l; simp [run]
      | none =>
        have hp := simpGate_props st0 (m + out0.length) g hst hg
        have hsnd := simpGate_sound st0 wOld wNew g hg heq
        rw [hwn] at hsnd
        dsimp only at hp hsnd
        cases hsg : (simpGate st0 (m + out0.length) g).2 with
        | none =>
          rw [hsg] at hp hsnd
          simp only [Option.elim_none] at hp hsnd
          apply hstep_drop (st0 ++ [(simpGate st0 (m + out0.length) g).1]) out0 wNew
            (by simp [compStep, hovj, hsg])
          · intro s hs; rcases List.mem_append.mp hs with h | h
            · exact hst s h
            · simp at h; subst h; exact hp
          · simp [step, hwo]
          · exact hwn
          · exact heq_ext _ wNew (fun _ _ => rfl) hsnd
          · intro l; simp [run]
        | some g' =>
          rw [hsg] at hp hsnd
          simp only [Option.elim_some] at hp hsnd
          apply hstep_drop (st0 ++ [(simpGate st0 (m + out0.length) g).1]) (out0 ++ [g'])
            (step wNew g') (by simp [compStep, hovj, hsg])
          · intro s hs; rcases List.mem_append.mp hs with h | h
            · have hs' := hst s h; cases s <;> simp [symBound] at hs' ⊢; omega
            · simp at h; subst h; rw [hp.1]; simp [symBound]
          · simp [step, hwo]
          · simp [step, hwn]; omega
          · exact heq_ext _ (step wNew g') (fun i hi => List.getD_append _ _ _ _ hi) hsnd
          · intro l
            rw [List.drop_append_of_le_length le_rfl, List.drop_length, List.nil_append,
              List.singleton_append, run_cons]

  have compile_elim_count : ∀ (m : ℕ) (init : List (Bool ⊕ ℕ)) (gs : List Gate),
      let acc (k : ℕ) := (gs.take k).foldl (compStep (fun _ => none) m) (init, [], 0)
      (∀ k ≤ gs.length, (acc k).1.length = init.length + k) ∧
      (∀ k ≤ gs.length, ∀ i < init.length + k,
        (acc k).1.getD i (.inl false) = (acc gs.length).1.getD i (.inl false)) ∧
      (∀ S : Finset ℕ,
        (∀ k ∈ S, ∃ hk : k < gs.length, (simpGate (acc k).1 (m + (acc k).2.1.length) gs[k]).2 = none) →
        (acc gs.length).2.1.length + S.card ≤ gs.length) := by
    intro m init gs
    dsimp only
    let acc (k : ℕ) := (gs.take k).foldl (compStep (fun _ => none) m) (init, [], 0)
    have hacc_step : ∀ k (hk : k < gs.length),
        acc (k + 1) = compStep (fun _ => none) m (acc k) gs[k] := by
      intro k hk
      simp only [acc, List.take_succ_eq_append_getElem hk, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
    have hlen : ∀ k ≤ gs.length, (acc k).1.length = init.length + k := by
      intro k hk
      induction k with
      | zero => simp [acc]
      | succ k ih =>
        rw [hacc_step k (by omega)]
        obtain ⟨s, hs, _, _⟩ := compStep_prefix (fun _ => none) m (acc k) gs[k]
        rw [hs]; simp [ih (by omega)]; omega
    have hpref : ∀ k1 k2, k1 ≤ k2 → k2 ≤ gs.length → ∀ i < init.length + k1,
        (acc k1).1.getD i (.inl false) = (acc k2).1.getD i (.inl false) := by
      intro k1 k2 h12 h2
      induction k2 with
      | zero =>
        have : k1 = 0 := by omega
        subst this; intro _ _; rfl
      | succ k2 ih =>
        by_cases h : k1 = k2 + 1
        · subst h; intro _ _; rfl
        · intro i hi
          rw [ih (by omega) (by omega) i hi, hacc_step k2 (by omega)]
          obtain ⟨s, hs, _, _⟩ := compStep_prefix (fun _ => none) m (acc k2) gs[k2]
          rw [hs, List.getD_append _ _ _ _ (by rw [hlen k2 (by omega)]; omega)]
    have hcnt : ∀ n (hn : n ≤ gs.length),
        (acc n).2.1.length + ((Finset.range n).filter fun k =>
          if h : k < gs.length then (simpGate (acc k).1 (m + (acc k).2.1.length) gs[k]).2.isNone
          else false).card = n := by
      intro n hn
      induction n with
      | zero => simp [acc]
      | succ n ih =>
        rw [Finset.range_add_one, Finset.filter_insert, hacc_step n (by omega)]
        simp only [compStep, Option.elim_none, dif_pos (show n < gs.length by omega)]
        have hnm : n ∉ (Finset.range n).filter (fun k =>
            if h : k < gs.length then (simpGate (acc k).1 (m + (acc k).2.1.length) gs[k]).2.isNone
            else false) := by simp
        cases h2 : (simpGate (acc n).1 (m + (acc n).2.1.length) gs[n]).2 with
        | none =>
          simp only [Option.elim_none, Option.isNone_none, ↓reduceIte, Finset.card_insert_of_notMem hnm]
          have := ih (by omega); omega
        | some g' =>
          simp only [Option.elim_some, Option.isNone_some, Bool.false_eq_true, ↓reduceIte, List.length_append,
            List.length_singleton]
          have := ih (by omega); omega
    refine ⟨hlen, fun k hk i hi => hpref k gs.length hk le_rfl i hi, ?_⟩
    intro S hS
    have hsub : S ⊆ (Finset.range gs.length).filter fun k =>
        if h : k < gs.length then (simpGate (acc k).1 (m + (acc k).2.1.length) gs[k]).2.isNone
        else false := by
      intro k hk
      obtain ⟨hlt, hnone⟩ := hS k hk
      have hnone' : (simpGate (acc k).1 (m + (acc k).2.1.length) gs[k]).2 = none := hnone
      simp [Finset.mem_filter, Finset.mem_range, hlt, hnone']
    have hc := Finset.card_le_card hsub
    have heq := hcnt gs.length le_rfl
    change (acc gs.length).2.1.length + S.card ≤ gs.length
    omega

  have drop_gate : ∀ (D : Circuit) (a b j0 : ℕ),
      FanInTwo D → ReadsBack 10 D → j0 < D.gates.length →
      10 + j0 ≠ a → 10 + j0 ≠ b →
      (∀ k (hk : k < D.gates.length), j0 < k → 10 + j0 ∉ D.gates[k].inputs) →
      ∃ (D' : Circuit) (a' b' : ℕ),
        FanInTwo D' ∧ D'.size < D.size ∧
        (∀ x : Fin 10 → Bool,
          (D'.wires (List.ofFn x)).getD a' false = (D.wires (List.ofFn x)).getD a false ∧
          (D'.wires (List.ofFn x)).getD b' false = (D.wires (List.ofFn x)).getD b false) := by
    intro D a b j0 hfan hrb hj0 ha hb hunused
    let sh (i : ℕ) : ℕ := if i < 10 + j0 then i else i - 1
    let shG (g : Gate) : Gate := ⟨g.op, g.inputs.map sh⟩
    let gs' : List Gate := D.gates.take j0 ++ (D.gates.drop (j0 + 1)).map shG
    refine ⟨⟨gs', 0⟩, sh a, sh b, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with h | h
      · exact hfan g (List.mem_of_mem_take h)
      · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h
        have := hfan g0 (List.mem_of_mem_drop hg0)
        simpa [shG] using this
    · show gs'.length < D.gates.length
      simp only [gs', List.length_append, List.length_take, List.length_map, List.length_drop]
      omega
    · intro x
      have hsplit : D.gates = D.gates.take j0 ++ D.gates[j0] :: D.gates.drop (j0 + 1) := by
        rw [List.cons_getElem_drop_succ, List.take_append_drop]
      set w0 := run (D.gates.take j0) (List.ofFn x)
      have hw0 : w0.length = 10 + j0 := by rw [run_length, List.length_ofFn, List.length_take]; omega
      have hsync : ∀ (t : ℕ) (ht : j0 + 1 + t ≤ D.gates.length),
          ∀ i, i ≠ 10 + j0 →
            (run (D.gates.take j0 ++ ((D.gates.drop (j0 + 1)).take t).map shG) (List.ofFn x)).getD (sh i) false =
              (run (D.gates.take (j0 + 1 + t)) (List.ofFn x)).getD i false := by
        intro t ht
        induction t with
        | zero =>
          intro i hi
          simp only [List.take_zero, List.map_nil, List.append_nil, Nat.add_zero]
          have htk : D.gates.take (j0 + 1) = D.gates.take j0 ++ [D.gates[j0]] :=
            List.take_succ_eq_append_getElem hj0
          rw [htk, run_append, run_cons, run_nil]
          by_cases hlt : i < 10 + j0
          · simp only [sh, if_pos hlt]
            rw [List.getD_append _ _ _ _ (by rw [hw0]; exact hlt)]
          · have hgt : 10 + j0 < i := by omega
            simp only [sh, if_neg hlt]
            rw [List.getD_eq_default _ _ (by rw [hw0]; omega),
              List.getD_eq_default _ _ (by simp only [step, List.length_append, List.length_singleton]; rw [hw0]; omega)]
        | succ t ih =>
          intro i hi
          have hk : j0 + 1 + t < D.gates.length := by omega
          have htk1 : D.gates.take (j0 + 1 + (t + 1)) = D.gates.take (j0 + 1 + t) ++ [D.gates[j0 + 1 + t]] := by
            rw [show j0 + 1 + (t + 1) = (j0 + 1 + t) + 1 by omega]
            exact List.take_succ_eq_append_getElem hk
          have htk2 : (D.gates.drop (j0 + 1)).take (t + 1) =
              (D.gates.drop (j0 + 1)).take t ++ [D.gates[j0 + 1 + t]] := by
            have hlt : t < (D.gates.drop (j0 + 1)).length := by simp; omega
            rw [List.take_succ_eq_append_getElem hlt]
            simp [List.getElem_drop]
          rw [htk1, htk2, List.map_append, List.map_singleton, ← List.append_assoc]
          conv_lhs => rw [run_append, run_cons, run_nil]
          conv_rhs => rw [run_append, run_cons, run_nil]
          set g := D.gates[j0 + 1 + t]
          set wOld := run (D.gates.take (j0 + 1 + t)) (List.ofFn x)
          set wNew := run (D.gates.take j0 ++ ((D.gates.drop (j0 + 1)).take t).map shG) (List.ofFn x)
          have hlO : wOld.length = 10 + j0 + 1 + t := by
            rw [run_length, List.length_ofFn, List.length_take]; omega
          have hlN : wNew.length = 10 + j0 + t := by
            rw [run_length, List.length_ofFn, List.length_append, List.length_take,
              List.length_map, List.length_take, List.length_drop]; omega
          have hgeval : (shG g).op.eval ((shG g).inputs.map fun k => wNew.getD k false) =
              g.op.eval (g.inputs.map fun k => wOld.getD k false) := by
            simp only [shG, List.map_map]
            congr 1
            apply List.map_congr_left
            intro k hk'
            have hne : k ≠ 10 + j0 := fun heq => hunused (j0 + 1 + t) hk (by omega) (heq ▸ hk')
            exact ih (by omega) k hne
          by_cases hlt : i < 10 + j0 + 1 + t
          · have hlt' : sh i < 10 + j0 + t := by simp only [sh]; split_ifs <;> omega
            rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
            exact ih (by omega) i hi
          · by_cases heq : i = 10 + j0 + 1 + t
            · subst heq
              have hsh : sh (10 + j0 + 1 + t) = 10 + j0 + t := by simp only [sh]; split_ifs <;> omega
              rw [hsh]
              simp only [step]
              conv_lhs => rw [← hlN, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
              conv_rhs => rw [← hlO, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
              exact hgeval
            · have hgt : 10 + j0 + t + 1 ≤ sh i := by simp only [sh]; split_ifs <;> omega
              rw [List.getD_eq_default _ _ (by simp only [step, List.length_append, List.length_singleton, hlN]; omega),
                List.getD_eq_default _ _ (by simp only [step, List.length_append, List.length_singleton, hlO]; omega)]
      have hfull := hsync (D.gates.length - (j0 + 1)) (by omega)
      have heq1 : D.gates.take (j0 + 1 + (D.gates.length - (j0 + 1))) = D.gates := by
        rw [show j0 + 1 + (D.gates.length - (j0 + 1)) = D.gates.length by omega, List.take_length]
      have heq2 : (D.gates.drop (j0 + 1)).take (D.gates.length - (j0 + 1)) = D.gates.drop (j0 + 1) := by
        rw [List.take_of_length_le (by simp)]
      rw [heq1, heq2] at hfull
      exact ⟨hfull a ha.symm, hfull b hb.symm⟩

  have countP_fin : ∀ (gs : List Gate) (p : Gate → Bool),
      gs.countP p = (Finset.univ.filter fun j : Fin gs.length => p (gs.get j)).card := by
    intro gs p
    induction gs with
    | nil => simp
    | cons g gs ih =>
      rw [List.countP_cons, ih]
      have hbij : (Finset.univ.filter fun j : Fin (g :: gs).length => p ((g :: gs).get j)).card =
          (if p g then 1 else 0) + (Finset.univ.filter fun j : Fin gs.length => p (gs.get j)).card := by
        have hunion : (Finset.univ.filter fun j : Fin (g :: gs).length => p ((g :: gs).get j)) =
            (if p g then {(0 : Fin (g :: gs).length)} else ∅) ∪
            ((Finset.univ.filter fun j : Fin gs.length => p (gs.get j)).image Fin.succ) := by
          ext j
          refine Fin.cases ?_ ?_ j
          · cases hp : p g <;> simp [hp]
          · intro k; cases hp : p g <;> simp [hp]
        rw [hunion, Finset.card_union_of_disjoint]
        · rw [Finset.card_image_of_injective _ (Fin.succ_injective _)]
          cases p g <;> simp
        · rw [Finset.disjoint_left]
          intro j hj1 hj2
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hj2
          obtain ⟨k, _, rfl⟩ := hj2
          cases hp : p g <;> simp [hp] at hj1
      rw [hbij]; omega

  have filter_len_countP : ∀ (gs : List Gate) (p q : Gate → Bool),
      (gs.filter p).length = gs.countP p ∧
      (gs.filter p).countP q = gs.countP (fun g => p g && q g) := by
    intro gs p q
    constructor
    · exact (List.countP_eq_length_filter ..).symm
    · induction gs with
      | nil => simp
      | cons g gs ih =>
        cases hp : p g <;> simp [List.filter_cons, List.countP_cons, hp, ih]

  suffices hMain : ∀ n : ℕ, n ≤ 18 → ∀ (D : Circuit) (a b : ℕ),
      FanInTwo D → D.size = n →
      (∃ x : Fin 10 → Bool, (D.wires (List.ofFn x)).getD a false = true ∧ (D.wires (List.ofFn x)).getD b false = false) →
      (∃ x : Fin 10 → Bool, (D.wires (List.ofFn x)).getD a false = false ∧ (D.wires (List.ofFn x)).getD b false = true) →
      (∀ x : Fin 10 → Bool, G1 x = false ∨ (List.ofFn x).count true ≤ 2 →
        ((D.wires (List.ofFn x)).getD a false || (D.wires (List.ofFn x)).getD b false) = G1 x) →
      ∃ (s : Equiv.Perm (Fin 10)) (v : Bool) (E : Circuit),
        (∀ x, G1 (x ∘ s) = G1 x) ∧ FanInTwo E ∧
        E.size ≤ (if v then 10 else 15) ∧
        ∀ y : Fin 9 → Bool, E.eval (List.ofFn y) =
          ((D.wires (List.ofFn ((Fin.lastCases v y : Fin 10 → Bool) ∘ s))).getD a false ||
           (D.wires (List.ofFn ((Fin.lastCases v y : Fin 10 → Bool) ∘ s))).getD b false) by
    intro D a b hfan hsize hA hB hAg
    exact hMain D.size hsize D a b hfan rfl hA hB hAg

  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn D a b hfan hsize hA hB hAg
    let W (x : Fin 10 → Bool) (i : ℕ) : Bool := (D.wires (List.ofFn x)).getD i false
    let U (x : Fin 10 → Bool) : Bool := W x a || W x b

    let init10 : List (Bool ⊕ ℕ) := (List.range 10).map Sum.inr
    have hinit10_len : init10.length = 10 := by simp [init10]
    have hinit10_b : ∀ s ∈ init10, symBound (10 + ([] : List Gate).length) s := by
      intro s hs
      simp only [init10, List.mem_map, List.mem_range] at hs
      obtain ⟨i, hi, rfl⟩ := hs
      simpa [symBound] using hi
    have hinv1 := compile_fold_inv (fun _ => none) 10 D.gates init10 [] 0 hfan hinit10_b
      (fun _ h => by simp at h) (fun j hj => by simp at hj) (fun _ h => by simp at h)
    set res1 := compile (fun _ => none) 10 init10 D.gates
    have hsnd1 : ∀ x : Fin 10 → Bool, ∀ i,
        W x i = evalSym (run res1.2.1 (List.ofFn x)) (res1.1.getD i (.inl false)) := by
      intro x i
      apply compile_sound_gen (fun _ => none) 10 D.gates init10 [] 0 (List.ofFn x) (List.ofFn x)
        hfan hinit10_b (by simp [hinit10_len]) (by simp)
      · intro k
        by_cases hk : k < 10
        · simp [init10, List.getD_eq_getElem?_getD, hk, evalSym]
        · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp [init10]; omega)]
          rfl
      · intro k _; trivial
    have hsym_nonconst : ∀ (w : ℕ), (∃ x, W x w = true) → (∃ x, W x w = false) →
        ∃ w' : ℕ, res1.1.getD w (.inl false) = .inr w' ∧ w' < 10 + res1.2.1.length := by
      rintro w ⟨x1, hx1⟩ ⟨x0, hx0⟩
      have hb : symBound (10 + res1.2.1.length) (res1.1.getD w (.inl false)) := by
        rw [List.getD_eq_getElem?_getD]
        cases hq : res1.1[w]? with
        | none => trivial
        | some s => exact hinv1.2.2.2.2.1 s (List.mem_of_getElem? hq)
      cases hr : res1.1.getD w (.inl false) with
      | inl c =>
        have e1 := hsnd1 x1 w; rw [hr] at e1
        have e0 := hsnd1 x0 w; rw [hr] at e0
        rw [hx1] at e1; rw [hx0] at e0
        cases c <;> simp [evalSym] at e1 e0
      | inr w' =>
        rw [hr] at hb
        exact ⟨w', rfl, hb⟩
    have ha_ex : (∃ x, W x a = true) ∧ (∃ x, W x a = false) := by
      obtain ⟨x, hx, _⟩ := hA; obtain ⟨y, hy, _⟩ := hB; exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hb_ex : (∃ x, W x b = true) ∧ (∃ x, W x b = false) := by
      obtain ⟨x, _, hx⟩ := hB; obtain ⟨y, _, hy⟩ := hA; exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    obtain ⟨a1, ha1_eq, ha1_lt⟩ := hsym_nonconst a ha_ex.1 ha_ex.2
    obtain ⟨b1, hb1_eq, hb1_lt⟩ := hsym_nonconst b hb_ex.1 hb_ex.2
    let D1 : Circuit := ⟨res1.2.1, 0⟩
    have hW1_a : ∀ x : Fin 10 → Bool, (D1.wires (List.ofFn x)).getD a1 false = W x a := by
      intro x; have := hsnd1 x a; rw [ha1_eq] at this; exact this.symm
    have hW1_b : ∀ x : Fin 10 → Bool, (D1.wires (List.ofFn x)).getD b1 false = W x b := by
      intro x; have := hsnd1 x b; rw [hb1_eq] at this; exact this.symm
    have hD1_le : D1.size ≤ n := by
      change res1.2.1.length ≤ n
      have h1len : res1.2.1.length ≤ 0 + D.gates.length := hinv1.2.2.1
      change D.gates.length = n at hsize
      omega
    by_cases hlt1 : D1.size < n
    · obtain ⟨s, v, E, hs, hE, hsz, hev⟩ := ih D1.size hlt1 (by omega) D1 a1 b1
        hinv1.2.2.2.2.2.1 rfl
        (by obtain ⟨x, hx1, hx2⟩ := hA; exact ⟨x, by rw [hW1_a]; exact hx1, by rw [hW1_b]; exact hx2⟩)
        (by obtain ⟨x, hx1, hx2⟩ := hB; exact ⟨x, by rw [hW1_a]; exact hx1, by rw [hW1_b]; exact hx2⟩)
        (by intro x hx; simpa only [hW1_a, hW1_b] using hAg x hx)
      exact ⟨s, v, E, hs, hE, hsz, fun y => by simpa only [hW1_a, hW1_b] using hev y⟩
    have hD1_eq : D1.size = n := by omega
    have hD1_fan : FanInTwo D1 := hinv1.2.2.2.2.2.1
    have hD1_rb : ReadsBack 10 D1 := hinv1.2.2.2.2.2.2.1
    have hD1_cl : ∀ g ∈ D1.gates, g.inputs.length = (if g.op.eval [false] then 1 else 2) ∧
        (g.op ≠ GateOp.not → g.inputs.Nodup) := hinv1.2.2.2.2.2.2.2
    let W1 (x : Fin 10 → Bool) (i : ℕ) : Bool := (D1.wires (List.ofFn x)).getD i false
    have hA1 : ∃ x, W1 x a1 = true ∧ W1 x b1 = false := by
      obtain ⟨x, hx1, hx2⟩ := hA; exact ⟨x, by rw [show W1 x a1 = W x a from hW1_a x]; exact hx1,
        by rw [show W1 x b1 = W x b from hW1_b x]; exact hx2⟩
    have hB1 : ∃ x, W1 x a1 = false ∧ W1 x b1 = true := by
      obtain ⟨x, hx1, hx2⟩ := hB; exact ⟨x, by rw [show W1 x a1 = W x a from hW1_a x]; exact hx1,
        by rw [show W1 x b1 = W x b from hW1_b x]; exact hx2⟩
    have hAg1 : ∀ x, G1 x = false ∨ (List.ofFn x).count true ≤ 2 → (W1 x a1 || W1 x b1) = G1 x := by
      intro x hx; simpa only [show W1 x a1 = W x a from hW1_a x, show W1 x b1 = W x b from hW1_b x] using hAg x hx
    have hU_eq : ∀ x, (W1 x a1 || W1 x b1) = U x := fun x => by
      simp only [U, show W1 x a1 = W x a from hW1_a x, show W1 x b1 = W x b from hW1_b x]

    have hge10 : ∀ w : ℕ, (∀ x, G1 x = false → W1 x w = false) → 10 ≤ w := by
      intro w hw
      by_contra hlt
      push_neg at hlt
      let v : Fin 10 := ⟨w, hlt⟩
      let xv : Fin 10 → Bool := fun k => decide (k = v)
      have h0 := hw xv (G1_single v)
      have h1 : W1 xv w = true := by
        simp only [W1, wires_eq]
        rw [run_getD_lt _ _ _ (by simp [hlt]), List.getD_eq_getElem _ _ (by simp [hlt]),
          List.getElem_ofFn]
        simp [xv, v]
      rw [h1] at h0; cases h0
    have ha1_ge : 10 ≤ a1 := hge10 a1 (fun x hx => by
      have h := hAg1 x (Or.inl hx); rw [hx] at h
      cases h1 : W1 x a1
      · rfl
      · rw [h1, Bool.true_or] at h; cases h)
    have hb1_ge : 10 ≤ b1 := hge10 b1 (fun x hx => by
      have h := hAg1 x (Or.inl hx); rw [hx] at h
      cases h1 : W1 x b1
      · rfl
      · rw [h1, Bool.or_true] at h; cases h)
    have hab1_ne : a1 ≠ b1 := by
      intro heq; subst heq; obtain ⟨x, h1, h2⟩ := hA1; rw [h1] at h2; cases h2

    by_cases hconst : ∃ (j0 : ℕ) (c : Bool), j0 < D1.gates.length ∧ ∀ x, W1 x (10 + j0) = c
    · obtain ⟨j0, c, hj0, hc⟩ := hconst
      let ov (j : ℕ) : Option (Bool ⊕ ℕ) := if j = j0 then some (.inl c) else none
      have hinv2 := compile_fold_inv ov 10 D1.gates init10 [] 0 hD1_fan hinit10_b
        (fun _ h => by simp at h) (fun j hj => by simp at hj) (fun _ h => by simp at h)
      set res2 := compile ov 10 init10 D1.gates
      have hlen2 : res2.2.1.length < D1.gates.length := by
        have hsp : D1.gates = D1.gates.take j0 ++ D1.gates[j0] :: D1.gates.drop (j0 + 1) := by
          rw [List.cons_getElem_drop_succ, List.take_append_drop]
        have h1 := compile_fold_inv ov 10 (D1.gates.take j0) init10 [] 0
          (fun g hg => hD1_fan g (List.mem_of_mem_take hg)) hinit10_b
          (fun _ h => by simp at h) (fun j hj => by simp at hj) (fun _ h => by simp at h)
        set acc0 := (D1.gates.take j0).foldl (compStep ov 10) (init10, [], 0)
        have hj0_eq : acc0.2.2 = j0 := by rw [h1.2.2.2.1, List.length_take]; omega
        have hstep0 : compStep ov 10 acc0 D1.gates[j0] = (acc0.1 ++ [.inl c], acc0.2.1, j0 + 1) := by
          simp [compStep, ov, hj0_eq]
        have h2 := compile_fold_inv ov 10 (D1.gates.drop (j0 + 1)) (acc0.1 ++ [.inl c]) acc0.2.1 (j0 + 1)
          (fun g hg => hD1_fan g (List.mem_of_mem_drop hg))
          (fun s hs => by
            rcases List.mem_append.mp hs with h | h
            · exact h1.2.2.2.2.1 s h
            · simp at h; subst h; trivial)
          h1.2.2.2.2.2.1 h1.2.2.2.2.2.2.1 h1.2.2.2.2.2.2.2
        have heqr : res2 = (D1.gates.drop (j0 + 1)).foldl (compStep ov 10) (acc0.1 ++ [.inl c], acc0.2.1, j0 + 1) := by
          simp only [res2, compile]
          conv_lhs => rw [hsp]
          rw [List.foldl_append, List.foldl_cons, hstep0]
        rw [heqr]
        have h2a := h2.2.2.1
        have h1a := h1.2.2.1
        simp only [List.length_nil, Nat.zero_add, List.length_take, List.length_drop] at h2a h1a
        omega
      have hsnd2 : ∀ x : Fin 10 → Bool, ∀ i,
          W1 x i = evalSym (run res2.2.1 (List.ofFn x)) (res2.1.getD i (.inl false)) := by
        intro x i
        apply compile_sound_gen ov 10 D1.gates init10 [] 0 (List.ofFn x) (List.ofFn x)
          hD1_fan hinit10_b (by simp [hinit10_len]) (by simp)
        · intro k
          by_cases hk : k < 10
          · simp [init10, List.getD_eq_getElem?_getD, hk, evalSym]
          · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp [init10]; omega)]
            rfl
        · intro k hk
          simp only [Nat.zero_add, ov]
          split_ifs with hkj
          · subst hkj; simpa [W1, wires_eq] using hc x
          · trivial
      have hsym2 : ∀ (w : ℕ), (∃ x, W1 x w = true) → (∃ x, W1 x w = false) →
          ∃ w' : ℕ, res2.1.getD w (.inl false) = .inr w' := by
        rintro w ⟨x1, hx1⟩ ⟨x0, hx0⟩
        cases hr : res2.1.getD w (.inl false) with
        | inl b' =>
          have e1 := hsnd2 x1 w; rw [hr, hx1] at e1
          have e0 := hsnd2 x0 w; rw [hr, hx0] at e0
          cases b' <;> simp [evalSym] at e1 e0
        | inr w' => exact ⟨w', rfl⟩
      obtain ⟨a2, ha2⟩ := hsym2 a1 (by obtain ⟨x, h, _⟩ := hA1; exact ⟨x, h⟩) (by obtain ⟨x, h, _⟩ := hB1; exact ⟨x, h⟩)
      obtain ⟨b2, hb2⟩ := hsym2 b1 (by obtain ⟨x, _, h⟩ := hB1; exact ⟨x, h⟩) (by obtain ⟨x, _, h⟩ := hA1; exact ⟨x, h⟩)
      let D2 : Circuit := ⟨res2.2.1, 0⟩
      have hW2a : ∀ x, (D2.wires (List.ofFn x)).getD a2 false = W1 x a1 := fun x => by
        have := hsnd2 x a1; rw [ha2] at this; exact this.symm
      have hW2b : ∀ x, (D2.wires (List.ofFn x)).getD b2 false = W1 x b1 := fun x => by
        have := hsnd2 x b1; rw [hb2] at this; exact this.symm
      have hD2_lt : D2.size < n := by
        change res2.2.1.length < n; change D1.gates.length = n at hD1_eq; omega
      obtain ⟨s, v, E, hs, hE, hsz, hev⟩ := ih D2.size hD2_lt (by omega)
        D2 a2 b2 hinv2.2.2.2.2.2.1 rfl
        (by obtain ⟨x, h1, h2⟩ := hA1; exact ⟨x, by rw [hW2a]; exact h1, by rw [hW2b]; exact h2⟩)
        (by obtain ⟨x, h1, h2⟩ := hB1; exact ⟨x, by rw [hW2a]; exact h1, by rw [hW2b]; exact h2⟩)
        (by intro x hx; simpa only [hW2a, hW2b] using hAg1 x hx)
      exact ⟨s, v, E, hs, hE, hsz, fun y => by rw [hev y, hW2a, hW2b, hU_eq]⟩

    by_cases hdup : ∃ (i0 j0 : ℕ), j0 < D1.gates.length ∧ i0 < 10 + j0 ∧ ∀ x, W1 x (10 + j0) = W1 x i0
    · obtain ⟨i0, j0, hj0, hi0, heqw⟩ := hdup
      let ov (j : ℕ) : Option (Bool ⊕ ℕ) := if j = j0 then some (.inr i0) else none
      have hinv2 := compile_fold_inv ov 10 D1.gates init10 [] 0 hD1_fan hinit10_b
        (fun _ h => by simp at h) (fun j hj => by simp at hj) (fun _ h => by simp at h)
      set res2 := compile ov 10 init10 D1.gates
      have hlen2 : res2.2.1.length < D1.gates.length := by
        have hsp : D1.gates = D1.gates.take j0 ++ D1.gates[j0] :: D1.gates.drop (j0 + 1) := by
          rw [List.cons_getElem_drop_succ, List.take_append_drop]
        have h1 := compile_fold_inv ov 10 (D1.gates.take j0) init10 [] 0
          (fun g hg => hD1_fan g (List.mem_of_mem_take hg)) hinit10_b
          (fun _ h => by simp at h) (fun j hj => by simp at hj) (fun _ h => by simp at h)
        set acc0 := (D1.gates.take j0).foldl (compStep ov 10) (init10, [], 0)
        have hj0_eq : acc0.2.2 = j0 := by rw [h1.2.2.2.1, List.length_take]; omega
        have hstep0 : compStep ov 10 acc0 D1.gates[j0] =
            (acc0.1 ++ [acc0.1.getD i0 (.inl false)], acc0.2.1, j0 + 1) := by
          simp [compStep, ov, hj0_eq]
        have h2 := compile_fold_inv ov 10 (D1.gates.drop (j0 + 1))
          (acc0.1 ++ [acc0.1.getD i0 (.inl false)]) acc0.2.1 (j0 + 1)
          (fun g hg => hD1_fan g (List.mem_of_mem_drop hg))
          (fun s hs => by
            rcases List.mem_append.mp hs with h | h
            · exact h1.2.2.2.2.1 s h
            · simp at h; subst h
              cases hq : acc0.1[i0]? with
              | none => trivial
              | some x => exact h1.2.2.2.2.1 x (List.mem_of_getElem? hq))
          h1.2.2.2.2.2.1 h1.2.2.2.2.2.2.1 h1.2.2.2.2.2.2.2
        have heqr : res2 = (D1.gates.drop (j0 + 1)).foldl (compStep ov 10)
            (acc0.1 ++ [acc0.1.getD i0 (.inl false)], acc0.2.1, j0 + 1) := by
          simp only [res2, compile]
          conv_lhs => rw [hsp]
          rw [List.foldl_append, List.foldl_cons, hstep0]
        rw [heqr]
        have h2a := h2.2.2.1
        have h1a := h1.2.2.1
        simp only [List.length_nil, Nat.zero_add, List.length_take, List.length_drop] at h2a h1a
        omega
      have hsnd2 : ∀ x : Fin 10 → Bool, ∀ i,
          W1 x i = evalSym (run res2.2.1 (List.ofFn x)) (res2.1.getD i (.inl false)) := by
        intro x i
        apply compile_sound_gen ov 10 D1.gates init10 [] 0 (List.ofFn x) (List.ofFn x)
          hD1_fan hinit10_b (by simp [hinit10_len]) (by simp)
        · intro k
          by_cases hk : k < 10
          · simp [init10, List.getD_eq_getElem?_getD, hk, evalSym]
          · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp [init10]; omega)]
            rfl
        · intro k hk
          simp only [Nat.zero_add, ov]
          split_ifs with hkj
          · subst hkj; exact ⟨by simpa [W1, wires_eq] using heqw x, by simp; exact hi0⟩
          · trivial
      have hsym2 : ∀ (w : ℕ), (∃ x, W1 x w = true) → (∃ x, W1 x w = false) →
          ∃ w' : ℕ, res2.1.getD w (.inl false) = .inr w' := by
        rintro w ⟨x1, hx1⟩ ⟨x0, hx0⟩
        cases hr : res2.1.getD w (.inl false) with
        | inl b' =>
          have e1 := hsnd2 x1 w; rw [hr, hx1] at e1
          have e0 := hsnd2 x0 w; rw [hr, hx0] at e0
          cases b' <;> simp [evalSym] at e1 e0
        | inr w' => exact ⟨w', rfl⟩
      obtain ⟨a2, ha2⟩ := hsym2 a1 (by obtain ⟨x, h, _⟩ := hA1; exact ⟨x, h⟩) (by obtain ⟨x, h, _⟩ := hB1; exact ⟨x, h⟩)
      obtain ⟨b2, hb2⟩ := hsym2 b1 (by obtain ⟨x, _, h⟩ := hB1; exact ⟨x, h⟩) (by obtain ⟨x, _, h⟩ := hA1; exact ⟨x, h⟩)
      let D2 : Circuit := ⟨res2.2.1, 0⟩
      have hW2a : ∀ x, (D2.wires (List.ofFn x)).getD a2 false = W1 x a1 := fun x => by
        have := hsnd2 x a1; rw [ha2] at this; exact this.symm
      have hW2b : ∀ x, (D2.wires (List.ofFn x)).getD b2 false = W1 x b1 := fun x => by
        have := hsnd2 x b1; rw [hb2] at this; exact this.symm
      have hD2_lt : D2.size < n := by
        change res2.2.1.length < n; change D1.gates.length = n at hD1_eq; omega
      obtain ⟨s, v, E, hs, hE, hsz, hev⟩ := ih D2.size hD2_lt (by omega)
        D2 a2 b2 hinv2.2.2.2.2.2.1 rfl
        (by obtain ⟨x, h1, h2⟩ := hA1; exact ⟨x, by rw [hW2a]; exact h1, by rw [hW2b]; exact h2⟩)
        (by obtain ⟨x, h1, h2⟩ := hB1; exact ⟨x, by rw [hW2a]; exact h1, by rw [hW2b]; exact h2⟩)
        (by intro x hx; simpa only [hW2a, hW2b] using hAg1 x hx)
      exact ⟨s, v, E, hs, hE, hsz, fun y => by rw [hev y, hW2a, hW2b, hU_eq]⟩

    by_cases hdead : ∃ j0 : ℕ, j0 < D1.gates.length ∧ 10 + j0 ≠ a1 ∧ 10 + j0 ≠ b1 ∧
        ∀ k (hk : k < D1.gates.length), j0 < k → 10 + j0 ∉ D1.gates[k].inputs
    · obtain ⟨j0, hj0, ha', hb', hun⟩ := hdead
      obtain ⟨D2, a2, b2, hfan2, hsz2, heq2⟩ := drop_gate D1 a1 b1 j0 hD1_fan hD1_rb hj0 ha' hb' hun
      obtain ⟨s, v, E, hs, hE, hsz, hev⟩ := ih D2.size (by omega) (by omega) D2 a2 b2 hfan2 rfl
        (by obtain ⟨x, h1, h2⟩ := hA1; exact ⟨x, by rw [(heq2 x).1]; exact h1, by rw [(heq2 x).2]; exact h2⟩)
        (by obtain ⟨x, h1, h2⟩ := hB1; exact ⟨x, by rw [(heq2 x).1]; exact h1, by rw [(heq2 x).2]; exact h2⟩)
        (by intro x hx; simpa only [(heq2 x).1, (heq2 x).2] using hAg1 x hx)
      exact ⟨s, v, E, hs, hE, hsz, fun y => by rw [hev y, (heq2 _).1, (heq2 _).2, hU_eq]⟩

    by_cases hhasNot : ∃ g ∈ D1.gates, g.op = GateOp.not
    · have hallRead : ∀ v : Fin 10, ∃ j : Fin D1.gates.length, v.val ∈ (D1.gates.get j).inputs := by
        intro v
        by_contra hno
        push_neg at hno
        let x0 : Fin 10 → Bool := fun k => decide (k = nbr v)
        let x1 : Fin 10 → Bool := fun k => decide (k = nbr v ∨ k = v)
        have hagree_wires : ∀ (t : ℕ) (ht : t ≤ D1.gates.length),
            ∀ i, i ≠ v.val → (run (D1.gates.take t) (List.ofFn x0)).getD i false =
              (run (D1.gates.take t) (List.ofFn x1)).getD i false := by
          intro t ht
          induction t with
          | zero =>
            intro i hi
            by_cases hi10 : i < 10
            · rw [List.take_zero, run_nil, run_nil,
                List.getD_eq_getElem _ _ (by simp [hi10]), List.getD_eq_getElem _ _ (by simp [hi10]),
                List.getElem_ofFn, List.getElem_ofFn]
              have : (⟨i, hi10⟩ : Fin 10) ≠ v := fun h => hi (congrArg Fin.val h)
              simp [x0, x1, this]
            · rw [List.take_zero, run_nil, run_nil,
                List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
          | succ t iht =>
            intro i hi
            have ht' : t < D1.gates.length := by omega
            rw [List.take_succ_eq_append_getElem ht', run_append, run_cons, run_nil,
              run_append, run_cons, run_nil]
            have hge : D1.gates[t].op.eval (D1.gates[t].inputs.map fun k =>
                  (run (D1.gates.take t) (List.ofFn x0)).getD k false) =
                D1.gates[t].op.eval (D1.gates[t].inputs.map fun k =>
                  (run (D1.gates.take t) (List.ofFn x1)).getD k false) := by
              congr 1
              apply List.map_congr_left
              intro k hk
              have hkv : k ≠ v.val := fun heq => hno ⟨t, ht'⟩ (by simpa [List.get_eq_getElem, heq] using hk)
              exact iht (by omega) k hkv
            have hl0 : (run (D1.gates.take t) (List.ofFn x0)).length = 10 + t := by
              rw [run_length, List.length_ofFn, List.length_take]; omega
            have hl1 : (run (D1.gates.take t) (List.ofFn x1)).length = 10 + t := by
              rw [run_length, List.length_ofFn, List.length_take]; omega
            by_cases hlt : i < 10 + t
            · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
              exact iht (by omega) i hi
            · by_cases heq : i = 10 + t
              · subst heq
                simp only [step]
                conv_lhs => rw [← hl0, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
                conv_rhs => rw [← hl1, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
                exact hge
              · rw [List.getD_eq_default _ _ (by simp only [step, List.length_append, List.length_singleton, hl0]; omega),
                  List.getD_eq_default _ _ (by simp only [step, List.length_append, List.length_singleton, hl1]; omega)]
        have hf := hagree_wires D1.gates.length le_rfl
        rw [List.take_length] at hf
        have hwa : W1 x0 a1 = W1 x1 a1 := hf a1 (by omega)
        have hwb : W1 x0 b1 = W1 x1 b1 := hf b1 (by omega)
        have hu0 : (W1 x0 a1 || W1 x0 b1) = false := by
          rw [hAg1 x0 (Or.inl (G1_single (nbr v))), G1_single]
        have hu1 : (W1 x1 a1 || W1 x1 b1) = true := by
          rw [hAg1 x1 (Or.inr (count_le_two (nbr v) v)), (G1_nbr v).2]
        rw [hwa, hwb, hu1] at hu0
        cases hu0

      have no_read_both : ∀ (v : Fin 10) (j k : Fin D1.gates.length),
          v.val ∈ (D1.gates.get j).inputs → (D1.gates.get j).op ≠ GateOp.or →
          v.val ∈ (D1.gates.get k).inputs → 10 + j.val ∈ (D1.gates.get k).inputs → False := by
        intro v j k hjv hjop hkv hkj
        have hgj_fan := hD1_fan (D1.gates.get j) (List.get_mem _ _)
        have hgk_fan := hD1_fan (D1.gates.get k) (List.get_mem _ _)
        have hgj_cl := hD1_cl (D1.gates.get j) (List.get_mem _ _)
        have hgk_cl := hD1_cl (D1.gates.get k) (List.get_mem _ _)
        have hj_lt_k : j.val < k.val := by
          have := hD1_rb k.val k.isLt (10 + j.val) (by simpa [gateAt_eq, List.getD_eq_getElem, k.isLt] using hkj)
          omega
        have hk_not_not : (D1.gates.get k).op ≠ GateOp.not := by
          intro hnot
          have hlen1 : (D1.gates.get k).inputs.length = 1 := by
            have := hgk_cl.1; rw [hnot] at this; exact this
          rcases hli : (D1.gates.get k).inputs with _ | ⟨x, _ | ⟨y, l⟩⟩
          · rw [hli] at hlen1; simp at hlen1
          · rw [hli] at hkv hkj
            simp only [List.mem_singleton] at hkv hkj
            omega
          · rw [hli] at hlen1; simp at hlen1
        have hgk_len2 : (D1.gates.get k).inputs.length = 2 := by
          have := hgk_cl.1
          have hop := hgk_fan.1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
          rcases hop with h | h | h
          · rw [h] at this; exact this
          · rw [h] at this; exact this
          · exact absurd h hk_not_not
        have hgk_val : ∀ x : Fin 10 → Bool,
            W1 x (10 + k.val) = (D1.gates.get k).op.eval [W1 x v.val, W1 x (10 + j.val)] ∨
            W1 x (10 + k.val) = (D1.gates.get k).op.eval [W1 x (10 + j.val), W1 x v.val] := by
          intro x
          obtain ⟨hval, hpre⟩ := run_getD_gate D1.gates (List.ofFn x) k.val k.isLt
          simp only [List.length_ofFn] at hval hpre
          rcases hli : (D1.gates.get k).inputs with _ | ⟨u1, _ | ⟨u2, _ | ⟨u3, l⟩⟩⟩
          · rw [hli] at hgk_len2; simp at hgk_len2
          · rw [hli] at hgk_len2; simp at hgk_len2
          · have hrb1 := hD1_rb k.val k.isLt u1 (by simp [gateAt_eq, k.isLt, ← List.get_eq_getElem, hli])
            have hrb2 := hD1_rb k.val k.isLt u2 (by simp [gateAt_eq, k.isLt, ← List.get_eq_getElem, hli])
            have hW : W1 x (10 + k.val) = (D1.gates.get k).op.eval [W1 x u1, W1 x u2] := by
              change (run D1.gates (List.ofFn x)).getD (10 + k.val) false = _
              rw [hval]
              simp only [← List.get_eq_getElem, hli, List.map_cons, List.map_nil, hpre,
                if_pos hrb1, if_pos hrb2]
              rfl
            rw [hli] at hkv hkj
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hkv hkj
            rcases hkv with rfl | rfl <;> rcases hkj with heq | heq
            · omega
            · subst heq; exact Or.inl hW
            · subst heq; exact Or.inr hW
            · omega
          · rw [hli] at hgk_len2; simp at hgk_len2
        have hgj_op : (D1.gates.get j).op = GateOp.and ∨ (D1.gates.get j).op = GateOp.not := by
          have := hgj_fan.1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
          rcases this with h | h | h
          · exact Or.inl h
          · exact absurd h hjop
          · exact Or.inr h
        have hgk_op : (D1.gates.get k).op = GateOp.and ∨ (D1.gates.get k).op = GateOp.or := by
          have := hgk_fan.1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
          rcases this with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h hk_not_not
        rcases hgj_op with hjand | hjnot
        · have hj_le_v : ∀ x : Fin 10 → Bool, W1 x v.val = false → W1 x (10 + j.val) = false := by
            intro x hxv
            obtain ⟨hval, hpre⟩ := run_getD_gate D1.gates (List.ofFn x) j.val j.isLt
            simp only [List.length_ofFn] at hval hpre
            change (run D1.gates (List.ofFn x)).getD (10 + j.val) false = false
            rw [hval, show D1.gates[j.val] = D1.gates.get j from rfl, hjand]
            simp only [eval_and, List.all_eq_false, List.mem_map, id_eq]
            refine ⟨false, ⟨v.val, hjv, ?_⟩, Bool.false_ne_true⟩
            rw [hpre, if_pos (by omega)]
            exact hxv
          rcases hgk_op with hkand | hkor
          · apply hdup
            refine ⟨10 + j.val, k.val, k.isLt, by omega, fun x => ?_⟩
            rcases hgk_val x with h | h <;> rw [hkand] at h
            · simp only [eval_and, List.all_cons, List.all_nil, id_eq, Bool.and_true] at h
              cases hxv : W1 x v.val
              · rw [hxv] at h; rw [hj_le_v x hxv]; simpa using h
              · rw [hxv] at h; simpa using h
            · simp only [eval_and, List.all_cons, List.all_nil, id_eq, Bool.and_true] at h
              cases hxv : W1 x v.val
              · rw [hxv] at h; rw [hj_le_v x hxv]; simpa using h
              · rw [hxv] at h; simpa using h
          · apply hdup
            refine ⟨v.val, k.val, k.isLt, by omega, fun x => ?_⟩
            rcases hgk_val x with h | h <;> rw [hkor] at h
            · simp only [eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false] at h
              cases hxv : W1 x v.val
              · rw [hxv, hj_le_v x hxv] at h; simpa using h
              · rw [hxv] at h; simpa using h
            · simp only [eval_or, List.any_cons, List.any_nil, id_eq, Bool.or_false] at h
              cases hxv : W1 x v.val
              · rw [hxv, hj_le_v x hxv] at h; simpa using h
              · rw [hxv] at h; simpa using h
        · have hj_not : ∀ x : Fin 10 → Bool, W1 x (10 + j.val) = !(W1 x v.val) := by
            intro x
            obtain ⟨hval, hpre⟩ := run_getD_gate D1.gates (List.ofFn x) j.val j.isLt
            simp only [List.length_ofFn] at hval hpre
            have hlen1 : (D1.gates.get j).inputs.length = 1 := by
              have := hgj_cl.1; rw [hjnot] at this; exact this
            rcases hli : (D1.gates.get j).inputs with _ | ⟨u, _ | ⟨u2, l⟩⟩
            · rw [hli] at hlen1; simp at hlen1
            · rw [hli] at hjv; simp only [List.mem_singleton] at hjv; subst hjv
              change (run D1.gates (List.ofFn x)).getD (10 + j.val) false = _
              rw [hval, show D1.gates[j.val] = D1.gates.get j from rfl, hjnot, hli]
              simp only [eval_not, List.map_cons, List.map_nil, List.headD_cons, hpre,
                if_pos (show v.val < 10 + j.val by omega)]
              rfl
            · rw [hli] at hlen1; simp at hlen1
          rcases hgk_op with hkand | hkor
          · apply hconst
            refine ⟨k.val, false, k.isLt, fun x => ?_⟩
            rcases hgk_val x with h | h <;> rw [hkand, hj_not x] at h <;>
              cases W1 x v.val <;> simpa [eval_and] using h
          · apply hconst
            refine ⟨k.val, true, k.isLt, fun x => ?_⟩
            rcases hgk_val x with h | h <;> rw [hkor, hj_not x] at h <;>
              cases W1 x v.val <;> simpa [eval_or] using h

      by_cases helim : ∃ v : Fin 10,
          let r := D1.gates.filter fun g => g.inputs.contains v.val
          n < r.length + r.countP (fun g => !g.op.eval [true, false]) + 15
      · obtain ⟨v, hv⟩ := helim
        let Cgs : List Gate := D1.gates ++ [⟨GateOp.or, [a1, b1]⟩]
        have hCgs_fan : ∀ g ∈ Cgs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
            g.inputs.length ≤ 2 := by
          intro g hg
          rcases List.mem_append.mp hg with h | h
          · exact hD1_fan g h
          · simp at h; subst h; simp
        let initV : List (Bool ⊕ ℕ) :=
          List.ofFn fun i : Fin 10 => if i = v then .inl false else .inr (permEquiv v i).val
        have hinitV_len : initV.length = 10 := by simp [initV]
        have hinitV_b : ∀ s ∈ initV, symBound (9 + ([] : List Gate).length) s := by
          intro s hs
          simp only [initV, List.mem_ofFn] at hs
          obtain ⟨i, rfl⟩ := hs
          by_cases hiv : i = v
          · simp [hiv, symBound]
          · simp only [if_neg hiv, symBound, Sum.elim_inr, List.length_nil, Nat.add_zero]
            have hne9 : permEquiv v i ≠ 9 := by
              intro h9
              have : permEquiv v i = permEquiv v v := by
                rw [h9]; exact (permTable_last v).symm
              exact hiv ((permEquiv v).injective this)
            have hlt10 := (permEquiv v i).isLt
            have hne9' : (permEquiv v i).val ≠ 9 := fun h => hne9 (Fin.ext h)
            omega
        have hinvV := compile_fold_inv (fun _ => none) 9 Cgs initV [] 0 hCgs_fan hinitV_b
          (fun _ h => by simp at h) (fun j hj => by simp at hj) (fun _ h => by simp at h)
        set resV := compile (fun _ => none) 9 initV Cgs
        have hC_eval : ∀ x : Fin 10 → Bool,
            (run Cgs (List.ofFn x)).getD (10 + D1.gates.length) false = U x := by
          intro x
          rw [show Cgs = D1.gates ++ [⟨GateOp.or, [a1, b1]⟩] from rfl, run_append, run_cons, run_nil]
          have hlenD : (run D1.gates (List.ofFn x)).length = 10 + D1.gates.length := by
            rw [run_length, List.length_ofFn]
          simp only [step, ← hlenD]
          rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          simp only [eval_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            id_eq, Bool.or_false]
          exact hU_eq x
        have hsndV : ∀ y : Fin 9 → Bool,
            U ((fun k : Fin (9 + 1) => Fin.lastCases false y k) ∘ permEquiv v) =
              evalSym (run resV.2.1 (List.ofFn y)) (resV.1.getD (10 + D1.gates.length) (.inl false)) := by
          intro y
          let x : Fin 10 → Bool := (fun k : Fin (9 + 1) => Fin.lastCases false y k) ∘ permEquiv v
          rw [← hC_eval x]
          apply compile_sound_gen (fun _ => none) 9 Cgs initV [] 0 (List.ofFn x) (List.ofFn y)
            hCgs_fan hinitV_b (by simp [hinitV_len]) (by simp)
          · intro k
            by_cases hk : k < 10
            · rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn,
                List.getD_eq_getElem _ _ (by simp [initV, hk]), List.getElem_ofFn]
              let ik : Fin 10 := ⟨k, hk⟩
              change Fin.lastCases false y (permEquiv v ik) =
                evalSym (List.ofFn y) (if ik = v then .inl false else .inr (permEquiv v ik).val)
              by_cases hiv : ik = v
              · rw [if_pos hiv, hiv]
                have hp9 : permEquiv v v = Fin.last 9 := by
                  apply Fin.ext; exact congrArg Fin.val (permTable_last v)
                rw [hp9, Fin.lastCases_last]; rfl
              · simp only [if_neg hiv, evalSym, Sum.elim_inr]
                have hne9 : permEquiv v ik ≠ Fin.last 9 := by
                  intro h9
                  have : permEquiv v ik = permEquiv v v := by
                    rw [h9]; apply Fin.ext; exact (congrArg Fin.val (permTable_last v)).symm
                  exact hiv ((permEquiv v).injective this)
                have hlt9 : (permEquiv v ik).val < 9 := by
                  have := (permEquiv v ik).isLt
                  have : (permEquiv v ik).val ≠ 9 := fun h => hne9 (Fin.ext h)
                  omega
                have hcast : permEquiv v ik = Fin.castSucc ⟨(permEquiv v ik).val, hlt9⟩ := by
                  apply Fin.ext; rfl
                rw [hcast, Fin.lastCases_castSucc,
                  List.getD_eq_getElem _ _ (by simp [hlt9]), List.getElem_ofFn]; rfl
            · rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp [initV]; omega)]
              rfl
          · intro k _; trivial
        have htop_not_const : ∀ c : Bool, resV.1.getD (10 + D1.gates.length) (.inl false) ≠ .inl c := by
          intro c hc
          have h0 : U ((fun k : Fin (9 + 1) => Fin.lastCases false (fun _ => false) k) ∘ permEquiv v) = false := by
            have hfx : (fun k : Fin (9 + 1) => Fin.lastCases false (fun _ => false) k) ∘ permEquiv v =
                fun _ => false := by
              funext k
              simp only [Function.comp_apply]
              refine Fin.lastCases (motive := fun i => Fin.lastCases false (fun _ => false) i = false)
                Fin.lastCases_last (fun _ => Fin.lastCases_castSucc _) (permEquiv v k)
            rw [hfx, ← hU_eq, hAg1 _ (Or.inl G1_empty), G1_empty]
          obtain ⟨u, w, huv, hwv, huw, hedge⟩ := G1_sub_edge v
          let xE : Fin 10 → Bool := fun k => decide (k = u ∨ k = w)
          let yE : Fin 9 → Bool := fun j => xE ((permEquiv v).symm j.castSucc)
          have hfxE : (fun k : Fin (9 + 1) => Fin.lastCases false yE k) ∘ permEquiv v = xE := by
            funext k
            simp only [Function.comp_apply]
            by_cases hkv : k = v
            · rw [hkv]
              have hp9 : permEquiv v v = Fin.last 9 := by
                apply Fin.ext; exact congrArg Fin.val (permTable_last v)
              rw [hp9, Fin.lastCases_last]
              simp [xE, huv.symm, hwv.symm]
            · have hne9 : permEquiv v k ≠ Fin.last 9 := by
                intro h9
                have : permEquiv v k = permEquiv v v := by
                  rw [h9]; apply Fin.ext; exact (congrArg Fin.val (permTable_last v)).symm
                exact hkv ((permEquiv v).injective this)
              have hlt9 : (permEquiv v k).val < 9 := by
                have := (permEquiv v k).isLt
                have : (permEquiv v k).val ≠ 9 := fun h => hne9 (Fin.ext h)
                omega
              have hcast : permEquiv v k = Fin.castSucc ⟨(permEquiv v k).val, hlt9⟩ := by
                apply Fin.ext; rfl
              rw [hcast, Fin.lastCases_castSucc]
              simp only [yE, ← hcast, Equiv.symm_apply_apply]
          have h1 : U ((fun k : Fin (9 + 1) => Fin.lastCases false yE k) ∘ permEquiv v) = true := by
            rw [hfxE, ← hU_eq, hAg1 xE (Or.inr (count_le_two u w)), hedge]
          have e0 := hsndV (fun _ => false); rw [h0, hc] at e0
          have e1 := hsndV yE; rw [h1, hc] at e1
          cases c <;> simp [evalSym] at e0 e1
        cases houtV : resV.1.getD (10 + D1.gates.length) (.inl false) with
        | inl c => exact absurd houtV (htop_not_const c)
        | inr outIdx =>
          let acc (k : ℕ) := (Cgs.take k).foldl (compStep (fun _ => none) 9) (initV, [], 0)
          have hacc_all := compile_elim_count 9 initV Cgs
          change (∀ k ≤ Cgs.length, (acc k).1.length = initV.length + k) ∧
            (∀ k ≤ Cgs.length, ∀ i < initV.length + k,
              (acc k).1.getD i (.inl false) = (acc Cgs.length).1.getD i (.inl false)) ∧
            (∀ S : Finset ℕ,
              (∀ k ∈ S, ∃ hk : k < Cgs.length, (simpGate (acc k).1 (9 + (acc k).2.1.length) Cgs[k]).2 = none) →
              (acc Cgs.length).2.1.length + S.card ≤ Cgs.length) at hacc_all
          obtain ⟨hacc_len, hacc_pref, hacc_cnt⟩ := hacc_all
          have hacc_full : acc Cgs.length = resV := by
            simp [acc, resV, compile, List.take_length]
          have hst_v : resV.1.getD v.val (.inl false) = .inl false := by
            rw [← hacc_full, ← hacc_pref 0 (Nat.zero_le _) v.val (by simp [hinitV_len])]
            simp only [acc, List.take_zero, List.foldl_nil]
            rw [List.getD_eq_getElem _ _ (by simp [initV, v.isLt])]
            simp only [initV, List.getElem_ofFn, Fin.eta, ↓reduceIte]
          have helim_of_inl : ∀ (k : ℕ) (hk : k < Cgs.length) (i : ℕ) (b : Bool),
              i < 10 + k → i ∈ Cgs[k].inputs →
              resV.1.getD i (.inl false) = .inl b →
              (simpGate (acc k).1 (9 + (acc k).2.1.length) Cgs[k]).2 = none ∧
              (Cgs[k].op = GateOp.not → resV.1.getD (10 + k) (.inl false) = .inl (!b)) ∧
              (Cgs[k].op = GateOp.and → b = false → resV.1.getD (10 + k) (.inl false) = .inl false) ∧
              (Cgs[k].op = GateOp.or → b = true → resV.1.getD (10 + k) (.inl false) = .inl true) ∧
              ((∀ i' ∈ Cgs[k].inputs, ∃ b', i' < 10 + k ∧ resV.1.getD i' (.inl false) = .inl b') →
                ∃ c, resV.1.getD (10 + k) (.inl false) = .inl c) := by
            intro k hk i b hi hmem hinl
            have hli : (acc k).1.getD i (.inl false) = .inl b := by
              rw [hacc_pref k (le_of_lt hk) i (by rw [hinitV_len]; exact hi), hacc_full, hinl]
            have hst_next : resV.1.getD (10 + k) (.inl false) =
                (simpGate (acc k).1 (9 + (acc k).2.1.length) Cgs[k]).1 := by
              have h1 := hacc_pref (k + 1) hk (10 + k) (by rw [hinitV_len]; omega)
              rw [hacc_full] at h1
              rw [← h1]
              have hstep : acc (k + 1) = compStep (fun _ => none) 9 (acc k) Cgs[k] := by
                simp only [acc, List.take_succ_eq_append_getElem hk, List.foldl_append,
                  List.foldl_cons, List.foldl_nil]
              rw [hstep]
              have hl : (acc k).1.length = 10 + k := by
                rw [hacc_len k (le_of_lt hk), hinitV_len]
              simp only [compStep, Option.elim_none]
              cases (simpGate (acc k).1 (9 + (acc k).2.1.length) Cgs[k]).2 <;>
                simp [Option.elim_none, Option.elim_some, ← hl]
            have hgc := hCgs_fan Cgs[k] (List.getElem_mem hk)
            have hlen_exact : Cgs[k].inputs.length = if Cgs[k].op.eval [false] then 1 else 2 := by
              by_cases hlt : k < D1.gates.length
              · have heq : Cgs[k] = D1.gates[k] := List.getElem_append_left hlt
                rw [heq]; exact (hD1_cl _ (List.getElem_mem hlt)).1
              · have heq : k = D1.gates.length := by simp [Cgs] at hk; omega
                have hcg : Cgs[k] = ⟨GateOp.or, [a1, b1]⟩ := by
                  simp [Cgs, heq]
                rw [hcg]; rfl
            rcases hgf : Cgs[k] with ⟨op, ins⟩
            rw [hgf] at hgc hmem hlen_exact hst_next
            have hop := hgc.1
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
            rcases hop with rfl | rfl | rfl
            · rcases ins with _ | ⟨u1, _ | ⟨u2, _ | ⟨u3, l⟩⟩⟩
              · simp [eval_and] at hlen_exact
              · simp [eval_and] at hlen_exact
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
                rcases hmem with rfl | rfl
                · cases b with
                  | false =>
                    simp only [simpGate, hli, Sum.elim_inl, Bool.false_eq_true, ↓reduceIte] at hst_next ⊢
                    exact ⟨trivial, (fun h => GateOp.noConfusion h), fun _ _ => hst_next, (fun h => GateOp.noConfusion h), fun _ => ⟨false, hst_next⟩⟩
                  | true =>
                    simp only [simpGate, hli, Sum.elim_inl, ↓reduceIte] at hst_next ⊢
                    refine ⟨trivial, (fun h => GateOp.noConfusion h), (fun _ h => Bool.noConfusion h), (fun h => GateOp.noConfusion h), fun hall => ?_⟩
                    obtain ⟨b2, hu2, hb2⟩ := hall u2 (by simp)
                    have hlu2 : (acc k).1.getD u2 (.inl false) = .inl b2 := by
                      rw [hacc_pref k (le_of_lt hk) u2 (by rw [hinitV_len]; exact hu2), hacc_full, hb2]
                    rw [hlu2] at hst_next
                    exact ⟨b2, hst_next⟩
                · cases b with
                  | false =>
                    simp only [simpGate, hli] at hst_next ⊢
                    refine ⟨by cases (acc k).1.getD u1 (.inl false) with | inl bx => cases bx <;> rfl | inr _ => rfl,
                      (fun h => GateOp.noConfusion h), fun _ _ => ?_, (fun h => GateOp.noConfusion h), fun _ => ⟨false, ?_⟩⟩
                    · rw [hst_next]; cases (acc k).1.getD u1 (.inl false) with | inl bx => cases bx <;> rfl | inr _ => rfl
                    · rw [hst_next]; cases (acc k).1.getD u1 (.inl false) with | inl bx => cases bx <;> rfl | inr _ => rfl
                  | true =>
                    simp only [simpGate, hli] at hst_next ⊢
                    refine ⟨by cases (acc k).1.getD u1 (.inl false) with | inl bx => cases bx <;> rfl | inr _ => rfl,
                      (fun h => GateOp.noConfusion h), (fun _ h => Bool.noConfusion h), (fun h => GateOp.noConfusion h), fun hall => ?_⟩
                    obtain ⟨b1', hu1, hb1'⟩ := hall u1 (by simp)
                    have hlu1 : (acc k).1.getD u1 (.inl false) = .inl b1' := by
                      rw [hacc_pref k (le_of_lt hk) u1 (by rw [hinitV_len]; exact hu1), hacc_full, hb1']
                    rw [hlu1] at hst_next
                    cases b1' <;> exact ⟨_, hst_next⟩
              · simp [eval_and] at hlen_exact
            · rcases ins with _ | ⟨u1, _ | ⟨u2, _ | ⟨u3, l⟩⟩⟩
              · simp [eval_or] at hlen_exact
              · simp [eval_or] at hlen_exact
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
                rcases hmem with rfl | rfl
                · cases b with
                  | true =>
                    simp only [simpGate, hli, Sum.elim_inl, ↓reduceIte] at hst_next ⊢
                    exact ⟨trivial, (fun h => GateOp.noConfusion h), (fun h => GateOp.noConfusion h), fun _ _ => hst_next, fun _ => ⟨true, hst_next⟩⟩
                  | false =>
                    simp only [simpGate, hli, Sum.elim_inl, Bool.false_eq_true, ↓reduceIte] at hst_next ⊢
                    refine ⟨trivial, (fun h => GateOp.noConfusion h), (fun h => GateOp.noConfusion h), (fun _ h => False.elim h), fun hall => ?_⟩
                    obtain ⟨b2, hu2, hb2⟩ := hall u2 (by simp)
                    have hlu2 : (acc k).1.getD u2 (.inl false) = .inl b2 := by
                      rw [hacc_pref k (le_of_lt hk) u2 (by rw [hinitV_len]; exact hu2), hacc_full, hb2]
                    rw [hlu2] at hst_next
                    exact ⟨b2, hst_next⟩
                · cases b with
                  | true =>
                    simp only [simpGate, hli] at hst_next ⊢
                    refine ⟨by cases (acc k).1.getD u1 (.inl false) with | inl bx => cases bx <;> rfl | inr _ => rfl,
                      (fun h => GateOp.noConfusion h), (fun h => GateOp.noConfusion h), fun _ _ => ?_, fun _ => ⟨true, ?_⟩⟩
                    · rw [hst_next]; cases (acc k).1.getD u1 (.inl false) with | inl bx => cases bx <;> rfl | inr _ => rfl
                    · rw [hst_next]; cases (acc k).1.getD u1 (.inl false) with | inl bx => cases bx <;> rfl | inr _ => rfl
                  | false =>
                    simp only [simpGate, hli] at hst_next ⊢
                    refine ⟨by cases (acc k).1.getD u1 (.inl false) with | inl bx => cases bx <;> rfl | inr _ => rfl,
                      (fun h => GateOp.noConfusion h), (fun h => GateOp.noConfusion h), (fun _ h => Bool.noConfusion h), fun hall => ?_⟩
                    obtain ⟨b1', hu1, hb1'⟩ := hall u1 (by simp)
                    have hlu1 : (acc k).1.getD u1 (.inl false) = .inl b1' := by
                      rw [hacc_pref k (le_of_lt hk) u1 (by rw [hinitV_len]; exact hu1), hacc_full, hb1']
                    rw [hlu1] at hst_next
                    cases b1' <;> exact ⟨_, hst_next⟩
              · simp [eval_or] at hlen_exact
            · rcases ins with _ | ⟨u1, _ | ⟨u2, l⟩⟩
              · simp [eval_not] at hlen_exact
              · simp only [List.mem_singleton] at hmem; subst hmem
                simp only [simpGate, hli, Sum.elim_inl] at hst_next ⊢
                exact ⟨trivial, fun _ => hst_next, (fun h => GateOp.noConfusion h), (fun h => GateOp.noConfusion h), fun _ => ⟨!b, hst_next⟩⟩
              · simp [eval_not] at hlen_exact

          let R : Finset ℕ := (Finset.range D1.gates.length).filter fun j =>
            if h : j < D1.gates.length then D1.gates[j].inputs.contains v.val else false
          let K : Finset ℕ := (Finset.range D1.gates.length).filter fun j =>
            if h : j < D1.gates.length then
              D1.gates[j].inputs.contains v.val && !D1.gates[j].op.eval [true, false]
            else false
          have hR_card : R.card = (D1.gates.filter fun g => g.inputs.contains v.val).length := by
            rw [(filter_len_countP D1.gates _ (fun _ => true)).1, countP_fin]
            apply Finset.card_bij (fun (j : ℕ) (hj : j ∈ R) =>
              (⟨j, (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)⟩ : Fin D1.gates.length))
            · intro j hj
              have h1 := (Finset.mem_filter.mp hj).1
              have h2 := (Finset.mem_filter.mp hj).2
              simp [Finset.mem_range.mp h1] at h2
              simp [List.get_eq_getElem, h2]
            · intro j1 _ j2 _ heq; exact congrArg Fin.val heq
            · intro j hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.get_eq_getElem,
                List.contains_iff_mem] at hj
              exact ⟨j.val, by simp [R, j.isLt, hj], rfl⟩
          have hK_card : K.card = (D1.gates.filter fun g => g.inputs.contains v.val).countP
              (fun g => !g.op.eval [true, false]) := by
            rw [(filter_len_countP D1.gates _ _).2, countP_fin]
            apply Finset.card_bij (fun (j : ℕ) (hj : j ∈ K) =>
              (⟨j, (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)⟩ : Fin D1.gates.length))
            · intro j hj
              have h1 := (Finset.mem_filter.mp hj).1
              have h2 := (Finset.mem_filter.mp hj).2
              simp [Finset.mem_range.mp h1] at h2
              simp [List.get_eq_getElem, h2]
            · intro j1 _ j2 _ heq; exact congrArg Fin.val heq
            · intro j hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.get_eq_getElem,
                Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at hj
              exact ⟨j.val, by simp [K, j.isLt, hj.1, hj.2], rfl⟩
          have hRK_bound : n < R.card + K.card + 15 := by
            rw [hR_card, hK_card]; exact hv
          have hK_sub_R : K ⊆ R := by
            intro j hj
            simp only [K, R, Finset.mem_filter, Finset.mem_range] at hj ⊢
            obtain ⟨hlt, hb⟩ := hj
            simp only [dif_pos hlt, Bool.and_eq_true, List.contains_iff_mem] at hb
            exact ⟨hlt, by simp [hlt, hb.1]⟩
          have hR_elim : ∀ j ∈ R, ∃ hk : j < Cgs.length,
              (simpGate (acc j).1 (9 + (acc j).2.1.length) Cgs[j]).2 = none := by
            intro j hj
            simp only [R, Finset.mem_filter, Finset.mem_range] at hj
            obtain ⟨hlt, hmem⟩ := hj
            simp only [dif_pos hlt, List.contains_iff_mem] at hmem
            have hk : j < Cgs.length := by simp [Cgs]; omega
            refine ⟨hk, (helim_of_inl j hk v.val false (by omega) ?_ hst_v).1⟩
            rwa [List.getElem_append_left hlt]
          have hK_const : ∀ j ∈ K, ∃ (hlt : j < D1.gates.length) (c : Bool),
              D1.gates[j].op ≠ GateOp.or ∧ resV.1.getD (10 + j) (.inl false) = .inl c := by
            intro j hj
            simp only [K, Finset.mem_filter, Finset.mem_range] at hj
            obtain ⟨hlt, hb⟩ := hj
            simp only [dif_pos hlt, Bool.and_eq_true, List.contains_iff_mem,
              Bool.not_eq_true'] at hb
            have hneOr : D1.gates[j].op ≠ GateOp.or := by
              intro hor; rw [hor] at hb; simp [eval_or] at hb
            have hk : j < Cgs.length := by simp [Cgs]; omega
            have hmemC : v.val ∈ Cgs[j].inputs := by rw [List.getElem_append_left hlt]; exact hb.1
            have hp := helim_of_inl j hk v.val false (by omega) hmemC hst_v
            have hop := (hD1_fan D1.gates[j] (List.getElem_mem hlt)).1
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
            rcases hop with hand | hor | hnot
            · refine ⟨hlt, false, hneOr, hp.2.2.1 (by rwa [List.getElem_append_left hlt]) rfl⟩
            · exact absurd hor hneOr
            · refine ⟨hlt, true, hneOr, hp.2.1 (by rwa [List.getElem_append_left hlt])⟩
          have hliveC : ∀ j (hj : j < D1.gates.length),
              ∃ (h : ℕ) (hh : h < Cgs.length), j < h ∧ 10 + j ∈ Cgs[h].inputs := by
            intro j hj
            by_cases ha_eq : 10 + j = a1
            · refine ⟨D1.gates.length, by simp [Cgs], hj, ?_⟩
              simp [Cgs, ha_eq]
            · by_cases hb_eq : 10 + j = b1
              · refine ⟨D1.gates.length, by simp [Cgs], hj, ?_⟩
                simp [Cgs, hb_eq]
              · by_contra hno
                push_neg at hno
                apply hdead
                refine ⟨j, hj, ha_eq, hb_eq, fun k hk hjk => ?_⟩
                have := hno k (by simp [Cgs]; omega) hjk
                rwa [List.getElem_append_left hk] at this
          have hC_disj_R : ∀ j ∈ K, ∀ (h : ℕ) (hh : h < Cgs.length), j < h → 10 + j ∈ Cgs[h].inputs → h ∉ R := by
            intro j hj h hh hjh hmem hR
            obtain ⟨hjlt, _, hneOr, _⟩ := hK_const j hj
            simp only [R, Finset.mem_filter, Finset.mem_range] at hR
            obtain ⟨hlt, hvmem⟩ := hR
            simp only [dif_pos hlt, List.contains_iff_mem] at hvmem
            have hjm : v.val ∈ (D1.gates.get ⟨j, hjlt⟩).inputs := by
              have := hK_sub_R hj
              simp only [R, Finset.mem_filter, Finset.mem_range, dif_pos hjlt,
                List.contains_iff_mem] at this
              exact this.2
            rw [List.getElem_append_left hlt] at hmem
            exact no_read_both v ⟨j, hjlt⟩ ⟨h, hlt⟩ hjm hneOr hvmem hmem

          have hS_ex : ∃ S : Finset ℕ, n + 1 ≤ S.card + 15 ∧
              ∀ k ∈ S, ∃ hk : k < Cgs.length,
                (simpGate (acc k).1 (9 + (acc k).2.1.length) Cgs[k]).2 = none := by
            by_cases hK0 : K.card = 0
            · exact ⟨R, by omega, hR_elim⟩
            · by_cases hR3 : n + 1 ≤ R.card + 1 + 15
              · obtain ⟨j, hj⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hK0)
                obtain ⟨hjlt, c, _, hc⟩ := hK_const j hj
                obtain ⟨h, hhc, hjh, hmem⟩ := hliveC j hjlt
                have hnotR : h ∉ R := hC_disj_R j hj h hhc hjh hmem
                refine ⟨insert h R, by rw [Finset.card_insert_of_notMem hnotR]; omega, ?_⟩
                intro k hk
                rcases Finset.mem_insert.mp hk with hkh | hkR
                · rw [hkh]; exact ⟨hhc, (helim_of_inl h hhc (10 + j) c (by omega) hmem hc).1⟩
                · exact hR_elim k hkR
              · have hK2 : 2 ≤ K.card := by omega
                have hR2 : R.card = 2 := by
                  have := Finset.card_le_card hK_sub_R; omega
                have hKeqR : K = R := Finset.eq_of_subset_of_card_le hK_sub_R (by omega)
                obtain ⟨j1, j2, hj12, hReq⟩ := Finset.card_eq_two.mp hR2
                have hj1K : j1 ∈ K := by rw [hKeqR, hReq]; simp
                have hj2K : j2 ∈ K := by rw [hKeqR, hReq]; simp
                obtain ⟨hj1lt, c1, _, hc1⟩ := hK_const j1 hj1K
                obtain ⟨hj2lt, c2, _, hc2⟩ := hK_const j2 hj2K
                let H : Finset ℕ := (Finset.range Cgs.length).filter fun h =>
                  if hh : h < Cgs.length then
                    (j1 < h && Cgs[h].inputs.contains (10 + j1)) ||
                    (j2 < h && Cgs[h].inputs.contains (10 + j2))
                  else false
                have hH_disj : Disjoint R H := by
                  rw [Finset.disjoint_left]
                  intro h hR hH
                  simp only [H, Finset.mem_filter, Finset.mem_range] at hH
                  obtain ⟨hhc, hb⟩ := hH
                  simp only [dif_pos hhc, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
                    List.contains_iff_mem] at hb
                  rcases hb with ⟨h1, hm1⟩ | ⟨h2, hm2⟩
                  · exact hC_disj_R j1 hj1K h hhc h1 hm1 hR
                  · exact hC_disj_R j2 hj2K h hhc h2 hm2 hR
                have hH_elim : ∀ h ∈ H, ∃ hk : h < Cgs.length,
                    (simpGate (acc h).1 (9 + (acc h).2.1.length) Cgs[h]).2 = none := by
                  intro h hh
                  simp only [H, Finset.mem_filter, Finset.mem_range] at hh
                  obtain ⟨hhc, hb⟩ := hh
                  simp only [dif_pos hhc, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
                    List.contains_iff_mem] at hb
                  rcases hb with ⟨h1, hm1⟩ | ⟨h2, hm2⟩
                  · exact ⟨hhc, (helim_of_inl h hhc (10 + j1) c1 (by omega) hm1 hc1).1⟩
                  · exact ⟨hhc, (helim_of_inl h hhc (10 + j2) c2 (by omega) hm2 hc2).1⟩
                by_cases hH2 : 2 ≤ H.card
                · refine ⟨R ∪ H, by rw [Finset.card_union_of_disjoint hH_disj]; omega, ?_⟩
                  intro k hk
                  rcases Finset.mem_union.mp hk with hkR | hkH
                  · exact hR_elim k hkR
                  · exact hH_elim k hkH
                · obtain ⟨h1, hh1c, hj1h1, hm1⟩ := hliveC j1 hj1lt
                  obtain ⟨h2, hh2c, hj2h2, hm2⟩ := hliveC j2 hj2lt
                  have hh1H : h1 ∈ H := by
                    simp [H, hh1c, hj1h1, hm1]
                  have hh2H : h2 ∈ H := by
                    simp [H, hh2c, hj2h2, hm2]
                  have hh12 : h1 = h2 := by
                    by_contra hne
                    have : 2 ≤ ({h1, h2} : Finset ℕ).card := by
                      rw [Finset.card_pair hne]
                    have hsub : ({h1, h2} : Finset ℕ) ⊆ H := by
                      intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
                    have := Finset.card_le_card hsub; omega
                  subst hh12
                  have hall_inl : ∀ i' ∈ Cgs[h1].inputs, ∃ b', i' < 10 + h1 ∧
                      resV.1.getD i' (.inl false) = .inl b' := by
                    have hlen2 := (hCgs_fan Cgs[h1] (List.getElem_mem hh1c)).2
                    rcases hins : Cgs[h1].inputs with _ | ⟨u1, _ | ⟨u2, _ | ⟨u3, l⟩⟩⟩
                    · simp [hins] at hm1
                    · rw [hins] at hm1 hm2; simp at hm1 hm2; omega
                    · rw [hins] at hm1 hm2; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1 hm2
                      intro i' hi'
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
                      rcases hm1 with rfl | rfl <;> rcases hm2 with heq | heq
                      · omega
                      · subst heq; rcases hi' with rfl | rfl
                        · exact ⟨c1, by omega, hc1⟩
                        · exact ⟨c2, by omega, hc2⟩
                      · subst heq; rcases hi' with rfl | rfl
                        · exact ⟨c2, by omega, hc2⟩
                        · exact ⟨c1, by omega, hc1⟩
                      · omega
                    · simp [hins] at hlen2
                  obtain ⟨ch1, hch1⟩ := (helim_of_inl h1 hh1c (10 + j1) c1 (by omega) hm1 hc1).2.2.2.2 hall_inl
                  have hh1_lt : h1 < D1.gates.length := by
                    have hle : h1 ≤ D1.gates.length := by simp [Cgs] at hh1c; omega
                    rcases Nat.lt_or_eq_of_le hle with hlt | heq
                    · exact hlt
                    · subst heq; exact absurd hch1 (htop_not_const ch1)
                  obtain ⟨k, hkc, hh1k, hmk⟩ := hliveC h1 hh1_lt
                  have hk_notR : k ∉ R := by
                    rw [hReq]; simp; omega
                  have hk_ne_h1 : k ≠ h1 := by omega
                  have hh1_notR : h1 ∉ R := Finset.disjoint_right.mp hH_disj hh1H
                  refine ⟨insert k (insert h1 R), ?_, ?_⟩
                  · rw [Finset.card_insert_of_notMem (by simp [hk_ne_h1, hk_notR]),
                      Finset.card_insert_of_notMem hh1_notR]; omega
                  · intro x hx
                    rcases Finset.mem_insert.mp hx with hxk | hx
                    · rw [hxk]; exact ⟨hkc, (helim_of_inl k hkc (10 + h1) ch1 (by omega) hmk hch1).1⟩
                    · rcases Finset.mem_insert.mp hx with hxh1 | hx
                      · rw [hxh1]; exact hH_elim h1 hh1H
                      · exact hR_elim x hx
          obtain ⟨S, hScard, hSelim⟩ := hS_ex
          have hEsz : resV.2.1.length ≤ 15 := by
            have hc := hacc_cnt S hSelim
            rw [hacc_full] at hc
            have hC_len : Cgs.length = n + 1 := by
              simp only [Cgs, List.length_append, List.length_singleton]
              change D1.gates.length = n at hD1_eq; omega
            omega
          refine ⟨permEquiv v, false, ⟨resV.2.1, outIdx⟩, G1_perm v, hinvV.2.2.2.2.2.1,
            hEsz, ?_⟩
          intro y
          have h := hsndV y
          rw [houtV] at h
          exact h.symm

      push_neg at helim
      have hdeg_all : ∀ v : Fin 10,
          let r := D1.gates.filter fun g => g.inputs.contains v.val
          1 ≤ r.length ∧ r.length + r.countP (fun g => !g.op.eval [true, false]) + 15 ≤ n := by
        intro v
        refine ⟨?_, by have := helim v; dsimp only at this; omega⟩
        obtain ⟨j, hj⟩ := hallRead v
        have hmem : D1.gates.get j ∈ D1.gates.filter (fun g => g.inputs.contains v.val) :=
          List.mem_filter.mpr ⟨List.get_mem _ _, List.contains_iff_mem.mpr hj⟩
        exact List.length_pos_of_mem hmem
      by_cases hn15 : n ≤ 15
      · have h := hdeg_all 0; dsimp only at h; omega
      · by_cases hn16 : n = 16
        · have hlen_pos : 0 < D1.gates.length := by change D1.gates.length = n at hD1_eq; omega
          have h0_rb : ∀ i ∈ D1.gates[0].inputs, i < 10 := by
            intro i hi
            exact hD1_rb 0 hlen_pos i (by simpa [gateAt_eq, List.getD_eq_getElem, hlen_pos] using hi)
          have h0_nonempty : D1.gates[0].inputs ≠ [] := by
            have := (hD1_cl D1.gates[0] (List.getElem_mem hlen_pos)).1
            intro hemp; rw [hemp] at this; split_ifs at this <;> simp at this
          obtain ⟨u0, l0, h0_cons⟩ := List.exists_cons_of_ne_nil h0_nonempty
          have hu0_lt : u0 < 10 := h0_rb u0 (by rw [h0_cons]; simp)
          let uFin : Fin 10 := ⟨u0, hu0_lt⟩
          have hu_deg := hdeg_all uFin
          change 1 ≤ (D1.gates.filter fun g => g.inputs.contains u0).length ∧
            (D1.gates.filter fun g => g.inputs.contains u0).length +
            (D1.gates.filter fun g => g.inputs.contains u0).countP (fun g => !g.op.eval [true, false]) + 15 ≤ n at hu_deg
          have h0_is_or : D1.gates[0].op = GateOp.or := by
            have hop := (hD1_fan D1.gates[0] (List.getElem_mem hlen_pos)).1
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
            by_contra hne
            have hcnt_pos : 1 ≤ (D1.gates.filter fun g => g.inputs.contains u0).countP
                (fun g => !g.op.eval [true, false]) := by
              have hmem : D1.gates[0] ∈ D1.gates.filter (fun g => g.inputs.contains u0) := by
                simp [List.mem_filter, List.getElem_mem hlen_pos, h0_cons]
              have hne_ev : !D1.gates[0].op.eval [true, false] = true := by
                rcases hop with h | h | h
                · rw [h]; rfl
                · exact absurd h hne
                · rw [h]; rfl
              rw [List.countP_eq_length_filter]
              exact List.length_pos_of_mem (List.mem_filter.mpr ⟨hmem, hne_ev⟩)
            omega
          have h0_len2 : D1.gates[0].inputs.length = 2 := by
            have := (hD1_cl D1.gates[0] (List.getElem_mem hlen_pos)).1
            rw [h0_is_or] at this; exact this
          have h0_nd : D1.gates[0].inputs.Nodup :=
            (hD1_cl D1.gates[0] (List.getElem_mem hlen_pos)).2 (by rw [h0_is_or]; intro hc; cases hc)
          rcases l0 with _ | ⟨w0, _ | ⟨z0, l0'⟩⟩
          · rw [h0_cons] at h0_len2; simp at h0_len2
          · have hw0_lt : w0 < 10 := h0_rb w0 (by rw [h0_cons]; simp)
            let wFin : Fin 10 := ⟨w0, hw0_lt⟩
            have huw_ne : uFin ≠ wFin := by
              rw [h0_cons] at h0_nd; simp only [List.nodup_cons, List.mem_singleton] at h0_nd
              intro heq; exact h0_nd.1 (congrArg Fin.val heq)
            have hno_later : ∀ (v' : Fin 10), v' = uFin ∨ v' = wFin →
                ∀ k (hk : k < D1.gates.length), 0 < k → v'.val ∉ D1.gates[k].inputs := by
              intro v' hv' k hk hk0 hmem
              have hv_deg := hdeg_all v'
              dsimp only at hv_deg
              have h0m : v'.val ∈ D1.gates[0].inputs := by
                rcases hv' with rfl | rfl <;> simp [h0_cons, uFin, wFin]
              have hcard2 : 2 ≤ (Finset.univ.filter fun j : Fin D1.gates.length =>
                  (D1.gates.get j).inputs.contains v'.val).card := by
                have hsub : ({(⟨0, hlen_pos⟩ : Fin D1.gates.length), ⟨k, hk⟩} : Finset (Fin D1.gates.length)) ⊆
                    Finset.univ.filter (fun j : Fin D1.gates.length => (D1.gates.get j).inputs.contains v'.val) := by
                  intro j hj; simp at hj
                  rcases hj with rfl | rfl
                  · simp [List.get_eq_getElem, h0m]
                  · simp [List.get_eq_getElem, hmem]
                have hne0k : (⟨0, hlen_pos⟩ : Fin D1.gates.length) ≠ ⟨k, hk⟩ := by
                  intro h; have : (0 : ℕ) = k := congrArg Fin.val h; omega
                have := Finset.card_le_card hsub
                rw [Finset.card_pair hne0k] at this
                exact this
              have hlen2 : 2 ≤ (D1.gates.filter fun g => g.inputs.contains v'.val).length := by
                rw [(filter_len_countP D1.gates _ (fun _ => true)).1, countP_fin]
                convert hcard2
              omega
            obtain ⟨z, hzu, hzw, hGuz, hGwz⟩ := G1_distinguish uFin wFin huw_ne
            let x1 : Fin 10 → Bool := fun k => decide (k = uFin ∨ k = z)
            let x2 : Fin 10 → Bool := fun k => decide (k = wFin ∨ k = z)
            have hsame : ∀ (t : ℕ) (ht : t ≤ D1.gates.length), 1 ≤ t →
                ∀ i, i ≠ u0 → i ≠ w0 →
                  (run (D1.gates.take t) (List.ofFn x1)).getD i false =
                    (run (D1.gates.take t) (List.ofFn x2)).getD i false := by
              intro t ht ht1
              induction t with
              | zero => omega
              | succ t iht =>
                by_cases ht0 : t = 0
                · subst ht0
                  intro i hiu hiw
                  have htk : D1.gates.take 1 = [D1.gates[0]] := by
                    rw [List.take_succ_eq_append_getElem hlen_pos]; simp
                  rw [htk, run_cons, run_nil, run_cons, run_nil]
                  by_cases hi10 : i < 10
                  · rw [List.getD_append _ _ _ _ (by simp [hi10]),
                      List.getD_append _ _ _ _ (by simp [hi10]),
                      List.getD_eq_getElem _ _ (by simp [hi10]),
                      List.getD_eq_getElem _ _ (by simp [hi10]),
                      List.getElem_ofFn, List.getElem_ofFn]
                    have hne1 : (⟨i, hi10⟩ : Fin 10) ≠ uFin := fun h => hiu (congrArg Fin.val h)
                    have hne2 : (⟨i, hi10⟩ : Fin 10) ≠ wFin := fun h => hiw (congrArg Fin.val h)
                    simp [x1, x2, hne1, hne2]
                  · by_cases hi10' : i = 10
                    · subst hi10'
                      simp only [step]
                      rw [List.getD_append_right _ _ _ _ (by simp : (List.ofFn x1).length ≤ 10),
                        List.getD_append_right _ _ _ _ (by simp : (List.ofFn x2).length ≤ 10)]
                      simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
                      rw [h0_is_or, h0_cons]
                      simp only [eval_or, List.map_cons, List.map_nil, List.any_cons,
                        List.any_nil, id_eq, Bool.or_false]
                      rw [List.getD_eq_getElem _ _ (by simp [hu0_lt]),
                        List.getD_eq_getElem _ _ (by simp [hw0_lt]),
                        List.getD_eq_getElem _ _ (by simp [hu0_lt]),
                        List.getD_eq_getElem _ _ (by simp [hw0_lt]),
                        List.getElem_ofFn, List.getElem_ofFn, List.getElem_ofFn, List.getElem_ofFn]
                      simp [x1, x2, uFin, wFin]
                    · rw [List.getD_eq_default _ _ (by simp [step]; omega),
                        List.getD_eq_default _ _ (by simp [step]; omega)]
                · intro i hiu hiw
                  have ht' : t < D1.gates.length := by omega
                  rw [List.take_succ_eq_append_getElem ht', run_append, run_cons, run_nil,
                    run_append, run_cons, run_nil]
                  have hge : D1.gates[t].op.eval (D1.gates[t].inputs.map fun k =>
                        (run (D1.gates.take t) (List.ofFn x1)).getD k false) =
                      D1.gates[t].op.eval (D1.gates[t].inputs.map fun k =>
                        (run (D1.gates.take t) (List.ofFn x2)).getD k false) := by
                    congr 1
                    apply List.map_congr_left
                    intro k hk
                    have hku : k ≠ u0 := fun heq => hno_later uFin (Or.inl rfl) t ht' (by omega) (by simpa [uFin, ← heq] using hk)
                    have hkw : k ≠ w0 := fun heq => hno_later wFin (Or.inr rfl) t ht' (by omega) (by simpa [wFin, ← heq] using hk)
                    exact iht (by omega) (by omega) k hku hkw
                  have hl1 : (run (D1.gates.take t) (List.ofFn x1)).length = 10 + t := by
                    rw [run_length, List.length_ofFn, List.length_take]; omega
                  have hl2 : (run (D1.gates.take t) (List.ofFn x2)).length = 10 + t := by
                    rw [run_length, List.length_ofFn, List.length_take]; omega
                  by_cases hlt : i < 10 + t
                  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
                    exact iht (by omega) (by omega) i hiu hiw
                  · by_cases heq : i = 10 + t
                    · subst heq
                      simp only [step]
                      conv_lhs => rw [← hl1, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
                      conv_rhs => rw [← hl2, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
                      exact hge
                    · rw [List.getD_eq_default _ _ (by simp only [step, List.length_append, List.length_singleton, hl1]; omega),
                        List.getD_eq_default _ _ (by simp only [step, List.length_append, List.length_singleton, hl2]; omega)]
            have hfull := hsame D1.gates.length le_rfl (by omega)
            rw [List.take_length] at hfull
            have hwa : W1 x1 a1 = W1 x2 a1 := hfull a1 (by omega) (by omega)
            have hwb : W1 x1 b1 = W1 x2 b1 := hfull b1 (by omega) (by omega)
            have h1 : (W1 x1 a1 || W1 x1 b1) = true := by
              rw [hAg1 x1 (Or.inr (count_le_two uFin z)), hGuz]
            have h2 : (W1 x2 a1 || W1 x2 b1) = false := by
              rw [hAg1 x2 (Or.inl hGwz), hGwz]
            rw [hwa, hwb, h2] at h1
            cases h1
          · rw [h0_cons] at h0_len2; simp at h0_len2
        · have ha1_lt' : a1 < 10 + n := by change res1.2.1.length = n at hD1_eq; omega
          have hb1_lt' : b1 < 10 + n := by change res1.2.1.length = n at hD1_eq; omega
          have map_sum_deg : ∀ (gs : List Gate) (p q : Gate → Bool),
              (gs.map fun g => cond (p g) (cond (q g) (1 : ℕ) 2) 0).sum =
                (gs.filter p).length + (gs.filter p).countP (fun g => !q g) := by
            intro gs p q
            induction gs with
            | nil => rfl
            | cons g gs ih =>
              simp only [List.map_cons, List.sum_cons, List.filter_cons, ih]
              cases hp : p g <;> cases hq : q g <;> simp [hq, List.countP_cons] <;> omega
          have h1718 : n = 17 ∨ n = 18 := by omega
          rcases h1718 with hn17 | hn18
          · subst hn17
            let aF : Fin 17 := ⟨a1 - 10, by omega⟩
            let bF : Fin 17 := ⟨b1 - 10, by omega⟩
            have haF : 10 + aF.val = a1 := Nat.add_sub_of_le ha1_ge
            have hbF : 10 + bF.val = b1 := Nat.add_sub_of_le hb1_ge
            have habF : aF ≠ bF := fun h => hab1_ne (by rw [← haF, ← hbF, h])
            obtain ⟨s, v, E, hs, hE, hsz, hev⟩ := hSize17 D1 aF bF
              ⟨⟨⟨hD1_fan, hD1_eq⟩, ⟨habF, hD1_rb⟩⟩,
               ⟨⟨fun g hg => by have := (hD1_cl g hg).1; cases h : g.op.eval [false] <;> simpa [h] using this, hhasNot⟩,
                ⟨fun v => by
                  rw [map_sum_deg D1.gates (fun g => g.inputs.contains v.val) (fun g => g.op.eval [true, false])]
                  have := (hdeg_all v).2; omega,
                 ⟨by obtain ⟨x, h1, h2⟩ := hA1; exact ⟨x, by change (W1 x (10 + aF.val) && !W1 x (10 + bF.val)) = true; rw [haF, hbF, h1, h2]; rfl⟩,
                  by obtain ⟨x, h1, h2⟩ := hB1; exact ⟨x, by change (!W1 x (10 + aF.val) && W1 x (10 + bF.val)) = true; rw [haF, hbF, h1, h2]; rfl⟩,
                  by intro x hx; change G2 x = false ∨ _ at hx; change (W1 x (10 + aF.val) || W1 x (10 + bF.val)) = G2 x; rw [← hG_eq] at hx ⊢; rw [haF, hbF]; exact hAg1 x hx⟩⟩⟩⟩
            exact ⟨s, v, E, fun x => by rw [hG_eq, hG_eq]; exact hs x, hE, hsz,
              fun y => by rw [hev y]; change (W1 _ (10 + aF.val) || W1 _ (10 + bF.val)) = _; rw [haF, hbF]; exact hU_eq _⟩
          · subst hn18
            let aF : Fin 18 := ⟨a1 - 10, by omega⟩
            let bF : Fin 18 := ⟨b1 - 10, by omega⟩
            have haF : 10 + aF.val = a1 := Nat.add_sub_of_le ha1_ge
            have hbF : 10 + bF.val = b1 := Nat.add_sub_of_le hb1_ge
            have habF : aF ≠ bF := fun h => hab1_ne (by rw [← haF, ← hbF, h])
            obtain ⟨s, v, E, hs, hE, hsz, hev⟩ := hSize18 D1 aF bF
              ⟨⟨⟨hD1_fan, hD1_eq⟩, ⟨habF, hD1_rb⟩⟩,
               ⟨⟨fun g hg => by have := (hD1_cl g hg).1; cases h : g.op.eval [false] <;> simpa [h] using this, hhasNot⟩,
                ⟨fun v => by
                  rw [map_sum_deg D1.gates (fun g => g.inputs.contains v.val) (fun g => g.op.eval [true, false])]
                  have := (hdeg_all v).2; omega,
                 ⟨by obtain ⟨x, h1, h2⟩ := hA1; exact ⟨x, by change (W1 x (10 + aF.val) && !W1 x (10 + bF.val)) = true; rw [haF, hbF, h1, h2]; rfl⟩,
                  by obtain ⟨x, h1, h2⟩ := hB1; exact ⟨x, by change (!W1 x (10 + aF.val) && W1 x (10 + bF.val)) = true; rw [haF, hbF, h1, h2]; rfl⟩,
                  by intro x hx; change G2 x = false ∨ _ at hx; change (W1 x (10 + aF.val) || W1 x (10 + bF.val)) = G2 x; rw [← hG_eq] at hx ⊢; rw [haF, hbF]; exact hAg1 x hx⟩⟩⟩⟩
            exact ⟨s, v, E, fun x => by rw [hG_eq, hG_eq]; exact hs x, hE, hsz,
              fun y => by rw [hev y]; change (W1 _ (10 + aF.val) || W1 _ (10 + bF.val)) = _; rw [haF, hbF]; exact hU_eq _⟩
    · push_neg at hhasNot
      let Cmono : Circuit := ⟨D1.gates ++ [⟨GateOp.or, [a1, b1]⟩], 10 + D1.gates.length⟩
      have hCmono_m : Monotone2 Cmono := by
        intro g hg
        rcases List.mem_append.mp hg with h | h
        · have hfg := hD1_fan g h
          have hnn := hhasNot g h
          refine ⟨?_, hfg.2⟩
          have hop := hfg.1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
          rcases hop with h1 | h1 | h1
          · exact Or.inl h1
          · exact Or.inr h1
          · exact absurd h1 hnn
        · simp at h; subst h; simp
      have hCmono_sz : Cmono.size ≤ 19 := by
        change Cmono.gates.length ≤ 19
        simp only [Cmono, List.length_append, List.length_singleton]
        change D1.gates.length = n at hD1_eq
        omega
      have hCmono_eval : ∀ x : Fin 10 → Bool, Cmono.eval (List.ofFn x) = G2 x := by
        intro x
        have heqU : Cmono.eval (List.ofFn x) = (W1 x a1 || W1 x b1) := by
          change (run (D1.gates ++ [⟨GateOp.or, [a1, b1]⟩]) (List.ofFn x)).getD (10 + D1.gates.length) false =
            (W1 x a1 || W1 x b1)
          rw [run_append, run_cons, run_nil]
          have hl : (run D1.gates (List.ofFn x)).length = 10 + D1.gates.length := by
            rw [run_length, List.length_ofFn]
          simp only [step, ← hl]
          rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          simp [eval_or, W1, wires_eq]
        rw [← hG_eq x]
        cases hgx : G1 x with
        | false =>
          rw [heqU, hAg1 x (Or.inl hgx), hgx]
        | true =>
          rw [hG_eq x, G2_iff] at hgx
          obtain ⟨u, w, hadj, hu, hw⟩ := hgx
          let xe : Fin 10 → Bool := fun k => decide (k = u ∨ k = w)
          have hGxe : G1 xe = true := by
            rw [hG_eq xe, G2_iff]
            exact ⟨u, w, hadj, by simp [xe], by simp [xe]⟩
          have hCxe : Cmono.eval (List.ofFn xe) = true := by
            rw [show Cmono.eval (List.ofFn xe) = (W1 xe a1 || W1 xe b1) by
              change (run (D1.gates ++ [⟨GateOp.or, [a1, b1]⟩]) (List.ofFn xe)).getD (10 + D1.gates.length) false =
                (W1 xe a1 || W1 xe b1)
              rw [run_append, run_cons, run_nil]
              have hl : (run D1.gates (List.ofFn xe)).length = 10 + D1.gates.length := by
                rw [run_length, List.length_ofFn]
              simp only [step, ← hl]
              rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
              simp [eval_or, W1, wires_eq]]
            rw [hAg1 xe (Or.inr (count_le_two u w)), hGxe]
          exact mono_eval Cmono.gates hCmono_m (List.ofFn xe) (List.ofFn x) (by simp)
            (fun i hi => by
              by_cases hi10 : i < 10
              · rw [List.getD_eq_getElem _ _ (by simp [hi10]), List.getElem_ofFn] at hi ⊢
                simp only [xe, decide_eq_true_eq] at hi
                rcases hi with h | h <;> rw [h] <;> assumption
              · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; cases hi)
            Cmono.output hCxe
      obtain ⟨x, hx⟩ := hMono Cmono hCmono_m hCmono_sz
      exact absurd (hCmono_eval x) hx
