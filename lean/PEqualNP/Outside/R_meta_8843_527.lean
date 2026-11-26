import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_8843_527
    (beforeAnd : let I := fun p l : Fin 13 => p - l = 0 ∨ p - l = 1 ∨ p - l = 3 ∨ p - l = 9
    let row := fun P L : Finset (Fin 13) =>
      Fin.append (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L))
    let seed := fun (g : Gate) (x : Fin 26 → Bool) =>
      let w := List.ofFn x
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    ∀ (g : Gate) (D : Circuit), g.op = GateOp.and → g.inputs.length ≤ 2 →
      Monotone2 D → D.size ≤ 62 →
      (∀ p l : Fin 13, I p l → D.eval (seed g
        (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l))) = true) →
      (∀ P : Finset (Fin 13), P.card = 4 →
        (∀ l, (P.filter fun p => I p l).card ≤ 2) →
        D.eval (seed g (row P (Finset.univ.filter fun l => ∀ p ∈ P, ¬ I p l))) = false) →
      (∀ L : Finset (Fin 13), L.card = 4 →
        (∀ p, (L.filter fun l => I p l).card ≤ 2) →
        D.eval (seed g (row (Finset.univ.filter fun p => ∀ l ∈ L, ¬ I p l) L)) = false) → False)
    (beforeOr : let I := fun p l : Fin 13 => p - l = 0 ∨ p - l = 1 ∨ p - l = 3 ∨ p - l = 9
    let row := fun P L : Finset (Fin 13) =>
      Fin.append (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L))
    let seed := fun (g : Gate) (x : Fin 26 → Bool) =>
      let w := List.ofFn x
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    ∀ (g : Gate) (D : Circuit), g.op = GateOp.or → g.inputs.length ≤ 2 →
      Monotone2 D → D.size ≤ 62 →
      (∀ p l : Fin 13, I p l → D.eval (seed g
        (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l))) = true) →
      (∀ P : Finset (Fin 13), P.card = 4 →
        (∀ l, (P.filter fun p => I p l).card ≤ 2) →
        D.eval (seed g (row P (Finset.univ.filter fun l => ∀ p ∈ P, ¬ I p l))) = false) →
      (∀ L : Finset (Fin 13), L.card = 4 →
        (∀ p, (L.filter fun l => I p l).card ≤ 2) →
        D.eval (seed g (row (Finset.univ.filter fun p => ∀ l ∈ L, ¬ I p l) L)) = false) → False) :
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) → ∃ (x6 : Finset (Fin (13 : ℕ))) (x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x6, ∀ x10 ∈ x7, ¬x1 x8 x10) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x6 | x1 x9 x8}.card ≤ (2 : ℕ)) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x7 | x1 x8 x9}.card ≤ (2 : ℕ)) ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 (Fin.append (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x6)) fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x7)) = Bool.true) := by
  let Inc (p l : Fin 13) : Prop :=
    p - l = 0 ∨ p - l = 1 ∨ p - l = 3 ∨ p - l = 9

  letI incDecidable : DecidableRel Inc := fun p l => by
    unfold Inc
    infer_instance

  have inc_iff_add (p l : Fin 13) :
      Inc p l ↔ p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9 := by
    simp [Inc, sub_eq_iff_eq_add, add_comm]

  let PointArc (P : Finset (Fin 13)) : Prop :=
    ∀ l : Fin 13, (P.filter fun p => Inc p l).card ≤ 2

  let LineArc (L : Finset (Fin 13)) : Prop :=
    ∀ p : Fin 13, (L.filter fun l => Inc p l).card ≤ 2

  let avoidLines (P : Finset (Fin 13)) : Finset (Fin 13) :=
    Finset.univ.filter fun l => ∀ p ∈ P, ¬ Inc p l

  let avoidPoints (L : Finset (Fin 13)) : Finset (Fin 13) :=
    Finset.univ.filter fun p => ∀ l ∈ L, ¬ Inc p l

  have mem_avoidLines {P : Finset (Fin 13)} {l : Fin 13} :
      l ∈ avoidLines P ↔ ∀ p ∈ P, ¬ Inc p l := by
    simp [avoidLines]

  have mem_avoidPoints {L : Finset (Fin 13)} {p : Fin 13} :
      p ∈ avoidPoints L ↔ ∀ l ∈ L, ¬ Inc p l := by
    simp [avoidPoints]

  have pointDegree : ∀ p : Fin 13, (Finset.univ.filter (Inc p)).card = 4 := by
    decide +kernel

  have lineDegree : ∀ l : Fin 13, (Finset.univ.filter fun p => Inc p l).card = 4 := by
    decide +kernel

  have shift_inc (p l a : Fin 13) :
      Inc (p+a) (l+a) ↔ Inc p l := by
    simp only [Inc, add_sub_add_right_eq_sub]

  have joinPointsZero : ∀ q : Fin 13, ∃ l : Fin 13, Inc 0 l ∧ Inc q l := by
    decide

  have joinLinesZero : ∀ m : Fin 13, ∃ p : Fin 13, Inc p 0 ∧ Inc p m := by
    decide

  have joinPoints (p q : Fin 13) : ∃ l : Fin 13, Inc p l ∧ Inc q l := by
    obtain ⟨l, h₁, h₂⟩ := joinPointsZero (q-p)
    refine ⟨l+p, ?_, ?_⟩
    · simpa using (shift_inc 0 l p).mpr h₁
    · simpa using (shift_inc (q-p) l p).mpr h₂

  have joinLines (l m : Fin 13) : ∃ p : Fin 13, Inc p l ∧ Inc p m := by
    obtain ⟨p, h₁, h₂⟩ := joinLinesZero (m-l)
    refine ⟨p+l, ?_, ?_⟩
    · simpa using (shift_inc p 0 l).mpr h₁
    · simpa using (shift_inc p (m-l) l).mpr h₂

  have arcMissCore {α β : Type} [DecidableEq β]
      (I : α → β → Prop) (P : Finset α) (L : Finset β) (through : α → Finset β)
      (memThrough : ∀ p j, j ∈ through p ↔ I p j)
      (memMiss : ∀ j, j ∈ L ↔ ∀ p ∈ P, ¬ I p j)
      (degree : ∀ p, (through p).card = 4)
      (join : ∀ p q, ∃ j, I p j ∧ I q j)
      (size : 3 ≤ P.card)
      (notCollinear : ∀ j, (∀ p ∈ P, I p j) → P.card ≤ 2) :
      ∀ p, (L ∩ through p).card ≤ 2 := by
    intro p
    let hit := (through p).filter fun j => j ∉ L
    have interEq : L ∩ through p = (through p).filter fun j => j ∈ L := by
      ext j
      simp only [Finset.mem_inter, Finset.mem_filter]
      exact and_comm
    have split : (L ∩ through p).card + hit.card = (through p).card := by
      rw [interEq]
      exact Finset.card_filter_add_card_filter_not (fun j => j ∈ L)
    by_contra! excess
    have d := degree p
    have small : hit.card ≤ 1 := by omega
    have joinHit (q : α) (hq : q ∈ P) : ∃ j ∈ hit, I q j := by
      obtain ⟨j, hj, hqj⟩ := join p q
      exact ⟨j, Finset.mem_filter.mpr
        ⟨(memThrough p j).mpr hj, fun h => (memMiss j).mp h q hq hqj⟩, hqj⟩
    obtain ⟨q,hq⟩ := Finset.card_pos.mp (show 0 < P.card by omega)
    obtain ⟨j,hj,_⟩ := joinHit q hq
    exact (by omega : ¬ P.card ≤ 2) (notCollinear j (by
      intro r hr
      obtain ⟨m,hm,inc⟩ := joinHit r hr
      exact ((Finset.card_le_one.mp small) m hm j hj) ▸ inc))

  have arcMiss_lines (P : Finset (Fin 13)) (hcard : 3 ≤ P.card) (hArc : PointArc P) :
      LineArc (avoidLines P) := by
    intro p
    let through (q : Fin 13) := Finset.univ.filter (Inc q)
    have mem (q l : Fin 13) : l ∈ through q ↔ Inc q l := by simp [through]
    have no (l : Fin 13) (allOn : ∀ q ∈ P, Inc q l) : P.card ≤ 2 := by
      have bound := hArc l
      rwa [Finset.filter_eq_self.mpr allOn] at bound
    have h := @arcMissCore (Fin 13) (Fin 13) _ Inc P (avoidLines P) through
      mem (fun l => mem_avoidLines (P := P) (l := l)) pointDegree joinPoints hcard no p
    have eq : (avoidLines P).filter (Inc p) = avoidLines P ∩ through p := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_inter, mem]
    rw [eq]
    exact h

  have arcMiss_points (L : Finset (Fin 13)) (hcard : 3 ≤ L.card) (hArc : LineArc L) :
      PointArc (avoidPoints L) := by
    intro l
    let through (m : Fin 13) := Finset.univ.filter fun p => Inc p m
    have mem (m p : Fin 13) : p ∈ through m ↔ Inc p m := by simp [through]
    have no (p : Fin 13) (allOn : ∀ m ∈ L, Inc p m) : L.card ≤ 2 := by
      have bound := hArc p
      rwa [Finset.filter_eq_self.mpr allOn] at bound
    have h := @arcMissCore (Fin 13) (Fin 13) _ (fun m p => Inc p m) L (avoidPoints L) through
      mem (fun p => mem_avoidPoints (L := L) (p := p)) lineDegree joinLines hcard no l
    have eq : ((avoidPoints L).filter fun p => Inc p l) = avoidPoints L ∩ through l := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_inter, mem]
    rw [eq]
    exact h

  -- The incidence predicate above is the difference test in L-meta-2059.

  let row (P L : Finset (Fin 13)) : Fin 26 → Bool :=
    Fin.append (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L))

  let seeded (g : Gate) (x : Fin 26 → Bool) : List Bool :=
    let bits := List.ofFn x
    bits ++ [g.op.eval (g.inputs.map fun i => bits.getD i false)]

  let SuffixCase (op : GateOp) : Prop :=
    ∀ (g : Gate) (D : Circuit), g.op = op → g.inputs.length ≤ 2 →
      Monotone2 D → D.size ≤ 62 →
      (∀ p l : Fin 13, Inc p l → D.eval (seeded g
        (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l))) = true) →
      (∀ P : Finset (Fin 13), P.card = 4 → PointArc P →
        D.eval (seeded g (row P (avoidLines P))) = false) →
      (∀ L : Finset (Fin 13), L.card = 4 → LineArc L →
        D.eval (seeded g (row (avoidPoints L) L)) = false) → False

  have noZero (C : Circuit) (zero : C.gates = [])
      (positive : ∀ p l : Fin 13, Inc p l →
        circuitFun 26 C (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) :
      False := by
    have atDiag (p : Fin 13) :
        (List.ofFn fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 p)).getD
          C.output false = true := by
      have edge : Inc p p := by simp [Inc]
      have h := positive p p edge
      change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 p))).getD
        C.output false = true at h
      simpa only [zero, List.foldl_nil] using h
    have h0 := atDiag 0
    have h1 := atDiag 1
    by_cases ht : C.output < 26
    · have getDiag (p : Fin 13) :
          (List.ofFn fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 p)).getD
            C.output false = decide ((⟨C.output, ht⟩ : Fin 26) = Fin.castAdd 13 p ∨
              (⟨C.output, ht⟩ : Fin 26) = Fin.natAdd 13 p) := by
        rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_ofFn]
      rw [getDiag 0, decide_eq_true_eq] at h0
      rw [getDiag 1, decide_eq_true_eq] at h1
      exact (show ∀ i : Fin 26, ¬ ((i = Fin.castAdd 13 (0 : Fin 13) ∨
        i = Fin.natAdd 13 (0 : Fin 13)) ∧ (i = Fin.castAdd 13 (1 : Fin 13) ∨
        i = Fin.natAdd 13 (1 : Fin 13))) by decide +kernel) ⟨C.output, ht⟩ ⟨h0,h1⟩
    · have hx : (List.ofFn fun i : Fin 26 =>
          decide (i = Fin.castAdd 13 (0 : Fin 13) ∨ i = Fin.natAdd 13 (0 : Fin 13))).length ≤ C.output := by
        simpa using Nat.le_of_not_gt ht
      rw [List.getD_eq_default _ _ hx] at h0
      exact Bool.false_ne_true h0

  have withSuffixCases (andCase : SuffixCase .and) (orCase : SuffixCase .or)
      (C : Circuit) (legal : Monotone2 C) (small : C.size ≤ 63)
      (positive : ∀ p l : Fin 13, Inc p l →
        circuitFun 26 C (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) :
      ∃ P L : Finset (Fin 13), (∀ p ∈ P, ∀ l ∈ L, ¬ Inc p l) ∧
        PointArc P ∧ LineArc L ∧ circuitFun 26 C (row P L) = true := by
    classical
    by_contra noWitness
    have reject (P L : Finset (Fin 13)) (hP : PointArc P) (hL : LineArc L)
        (off : ∀ p ∈ P, ∀ l ∈ L, ¬ Inc p l) :
        circuitFun 26 C (row P L) = false := by
      cases e : circuitFun 26 C (row P L) with
      | false => rfl
      | true => exact (noWitness ⟨P, L, off, hP, hL, e⟩).elim
    cases hg : C.gates with
    | nil =>
      exact noZero C hg positive
    | cons g gs =>
      let D : Circuit := ⟨gs, C.output⟩
      have hMember : g ∈ C.gates := by simp [hg]
      have hGate : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using legal g hMember
      have evalD (x : Fin 26 → Bool) : D.eval (seeded g x) = circuitFun 26 C x := by
        change (gs.foldl (fun w k => w ++ [k.op.eval (k.inputs.map fun i => w.getD i false)])
          (seeded g x)).getD C.output false =
          (C.gates.foldl (fun w k => w ++ [k.op.eval (k.inputs.map fun i => w.getD i false)])
            (List.ofFn x)).getD C.output false
        rw [hg]
        rfl
      have monoD : Monotone2 D := fun k hk => legal k (by
        rw [hg]
        exact List.mem_cons_of_mem _ hk)
      have smallD : D.size ≤ 62 := by
        change gs.length ≤ 62
        change C.gates.length ≤ 63 at small
        rw [hg, List.length_cons] at small
        omega
      have pass (p l : Fin 13) (h : Inc p l) :
          D.eval (seeded g (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l))) = true := by
        rw [evalD]
        exact positive p l h
      have missP (P : Finset (Fin 13)) (hcard : P.card = 4) (hArc : PointArc P) :
          D.eval (seeded g (row P (avoidLines P))) = false := by
        rw [evalD]
        exact reject P (avoidLines P) hArc (arcMiss_lines P (by omega) hArc)
          (fun p hp l hl => mem_avoidLines.mp hl p hp)
      have missL (L : Finset (Fin 13)) (hcard : L.card = 4) (hArc : LineArc L) :
          D.eval (seeded g (row (avoidPoints L) L)) = false := by
        rw [evalD]
        exact reject (avoidPoints L) L (arcMiss_points L (by omega) hArc) hArc
          (fun p hp l hl => mem_avoidPoints.mp hp l hl)
      rcases hGate.1 with hand | hor
      · exact andCase g D hand hGate.2 monoD smallD pass missP missL
      · exact orCase g D hor hGate.2 monoD smallD pass missP missL
  have andCase : SuffixCase GateOp.and := beforeAnd
  have orCase : SuffixCase GateOp.or := beforeOr
  intro I C legal small pos
  have accept (p l : Fin 13) (on : Inc p l) :
      circuitFun 26 C (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true :=
    pos p l ((inc_iff_add p l).mp on)
  obtain ⟨P, L, misses, pointArc, lineArc, accepted⟩ := withSuffixCases andCase orCase C legal small accept
  refine ⟨P, L, ?_, ?_, ?_, accepted⟩
  · simpa [I, ← inc_iff_add] using misses
  · simpa [I, PointArc, ← inc_iff_add] using pointArc
  · simpa [I, LineArc, ← inc_iff_add] using lineArc
