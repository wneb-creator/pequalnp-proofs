import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_6011_714
    (extend : let D : Finset (Fin 13) := {0, 1, 3, 9}
      ∀ a b u v : Fin 13, a-u ∉ D → a-v ∉ D → b-u ∉ D → b-v ∉ D →
        ∃ Q : Finset (Fin 13), (Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter fun p => p-l ∈ D).card ≤ 2) ∧
          a ∈ Q ∧ b ∈ Q ∧ (∀ z ∈ Q, z-u ∉ D) ∧ (∀ z ∈ Q, z-v ∉ D))
    (sparse : let D : Finset (Fin 13) := {0, 1, 3, 9}
      ∀ (C : Circuit) (a b : ℕ), Monotone2 C → NestedCover.ReadsBack 26 C →
        let value := fun (p q u v : Fin 13) (w : ℕ) =>
          (C.wires ((List.ofFn fun x : Fin 13 => decide (x = p ∨ x = q)) ++
            List.ofFn fun y : Fin 13 => decide (y = u ∨ y = v))).getD w false
        (∀ p q u v, (value p q u v a || value p q u v b) =
          decide (p-u ∈ D ∨ p-v ∈ D ∨ q-u ∈ D ∨ q-v ∈ D)) →
        (∃ p l, value p p l l a = true ∧ value p p l l b = false) →
        (∃ p l, value p p l l b = true ∧ value p p l l a = false) →
        63 ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           (∀ x8 ∈ x1.gates, x2 ∉ x8.inputs ∧ x3 ∉ x8.inputs) →             have x9 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};             have x10 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x10 x11 : Fin (13 : ℕ)) => (List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x10)) ++ List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x11);             have x11 : Finset (Fin (13 : ℕ)) → List Bool := fun (x11 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 ∈ x11)) ++ List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (∀ x13 ∈ x11, x13 - x12 ∉ x9);             have x12 : Finset (Fin (13 : ℕ)) → Prop := fun (x12 : Finset (Fin (13 : ℕ))) => x12.card = (4 : ℕ) ∧ ∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x12 | x14 - x13 ∈ x9}.card ≤ (2 : ℕ);             have x13 : ℕ → List Bool → Bool := fun (x13 : ℕ) (x14 : List Bool) => (x1.wires x14).getD x13 Bool.false;             (∀ (x14 x15 : Fin (13 : ℕ)), x14 - x15 ∈ x9 → x13 x2 (x10 x14 x15) = Bool.true ∨ x13 x3 (x10 x14 x15) = Bool.true) → (∀ (x15 : Finset (Fin (13 : ℕ))), x12 x15 → x13 x2 (x11 x15) = Bool.false ∧ x13 x3 (x11 x15) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x9 ∧ x13 x2 (x10 x16 x17) = Bool.true ∧ x13 x3 (x10 x16 x17) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 - x18 ∈ x9 ∧ x13 x3 (x10 x17 x18) = Bool.true ∧ x13 x2 (x10 x17 x18) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intro C a b mono back _ha _hb _sink
  dsimp only
  intro pos neg leftOnly rightOnly
  let D : Finset (Fin 13) := {0, 1, 3, 9}
  let R := fun x y : Bool => x = true → y = true
  have readMono {x y : List Bool} (rel : List.Forall₂ R x y) (i : ℕ) :
      R (x.getD i false) (y.getD i false) := by
    induction rel generalizing i with
    | nil => simp [List.getD, R]
    | cons h _ ih => cases i with
      | zero => exact h
      | succ j => exact ih j
  have block (f g : Fin 13 → Prop) [DecidablePred f] [DecidablePred g]
      (sub : ∀ z, f z → g z) :
      List.Forall₂ R (List.ofFn fun z => decide (f z)) (List.ofFn fun z => decide (g z)) := by
    apply List.forall₂_of_length_eq_of_get (by simp)
    intro i hi hj
    have bound : i < 13 := by simpa using hi
    simpa only [R, List.get_eq_getElem, List.getElem_ofFn, decide_eq_true_eq] using sub ⟨i, bound⟩
  let appendGate := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldMono (gs : List Gate) (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      {x y : List Bool} (rel : List.Forall₂ R x y) :
      List.Forall₂ R (gs.foldl appendGate x) (gs.foldl appendGate y) := by
    induction gs generalizing x y with
    | nil => exact rel
    | cons g gs ih =>
      apply ih (fun k hk => ops k (List.mem_cons_of_mem _ hk))
      apply List.rel_append rel
      apply List.Forall₂.cons _ List.Forall₂.nil
      rcases ops g (by simp) with hand | hor
      · rw [hand]
        change (g.inputs.map (fun i => x.getD i false)).all id = true →
          (g.inputs.map (fun i => y.getD i false)).all id = true
        simp only [List.all_map, Function.comp_def, List.all_eq_true, id_eq]
        intro hx i hi
        exact readMono rel i (hx i hi)
      · rw [hor]
        change (g.inputs.map (fun i => x.getD i false)).any id = true →
          (g.inputs.map (fun i => y.getD i false)).any id = true
        simp only [List.any_map, Function.comp_def, List.any_eq_true, id_eq]
        rintro ⟨i, hi, hx⟩
        exact ⟨i, hi, readMono rel i hx⟩
  have wire {x y : List Bool} (rel : List.Forall₂ R x y) (w : ℕ) :
      R ((C.wires x).getD w false) ((C.wires y).getD w false) :=
    readMono (foldMono C.gates (fun g hg => by simpa using (mono g hg).1) rel) w
  apply sparse C a b mono back
  · intro p q u v
    let x := (List.ofFn fun z : Fin 13 => decide (z = p ∨ z = q)) ++
             List.ofFn fun z : Fin 13 => decide (z = u ∨ z = v)
    change ((C.wires x).getD a false || (C.wires x).getD b false) =
      decide (p-u ∈ D ∨ p-v ∈ D ∨ q-u ∈ D ∨ q-v ∈ D)
    by_cases hit : p-u ∈ D ∨ p-v ∈ D ∨ q-u ∈ D ∨ q-v ∈ D
    · rw [decide_eq_true hit, Bool.or_eq_true]
      have lift (i j : Fin 13) (hp : i = p ∨ i = q) (hu : j = u ∨ j = v) (edge : i-j ∈ D) :
          (C.wires x).getD a false = true ∨ (C.wires x).getD b false = true := by
        have rel := List.rel_append (block (fun z => z = i) (fun z => z = p ∨ z = q)
          (fun _ h => h ▸ hp)) (block (fun z => z = j) (fun z => z = u ∨ z = v) (fun _ h => h ▸ hu))
        exact (pos i j edge).imp (wire rel a) (wire rel b)
      rcases hit with h | h | h | h
      · exact lift p u (Or.inl rfl) (Or.inl rfl) h
      · exact lift p v (Or.inl rfl) (Or.inr rfl) h
      · exact lift q u (Or.inr rfl) (Or.inl rfl) h
      · exact lift q v (Or.inr rfl) (Or.inr rfl) h
    · obtain ⟨Q, hQ, hp, hq, hu, hv⟩ := extend p q u v (fun h => hit (.inl h))
        (fun h => hit (.inr (.inl h))) (fun h => hit (.inr (.inr (.inl h))))
        (fun h => hit (.inr (.inr (.inr h))))
      have rel := List.rel_append (block (fun z => z = p ∨ z = q) (fun z => z ∈ Q)
        (by rintro z (rfl|rfl) <;> assumption))
        (block (fun z => z = u ∨ z = v) (fun z => ∀ t ∈ Q, t-z ∉ D)
        (by rintro z (rfl|rfl) <;> assumption))
      obtain ⟨noA, noB⟩ := neg Q hQ
      rw [decide_eq_false hit, Bool.or_eq_false_iff]
      exact ⟨Bool.eq_false_iff.mpr (fun h => Bool.noConfusion ((wire rel a h).symm.trans noA)),
        Bool.eq_false_iff.mpr (fun h => Bool.noConfusion ((wire rel b h).symm.trans noB))⟩
  · obtain ⟨p, l, _, h⟩ := leftOnly
    exact ⟨p, l, by simpa only [or_self] using h⟩
  · obtain ⟨p, l, _, h⟩ := rightOnly
    exact ⟨p, l, by simpa only [or_self] using h⟩
