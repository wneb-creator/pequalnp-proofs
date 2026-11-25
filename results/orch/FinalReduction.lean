import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3178_52
    (binaryBound : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
       x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
       x 6 && x 8 || x 8 && x 5)) →
      13 ≤ C.gates.countP (fun g => !(GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op)))
    (oneNotSearch : ∀ j : Fin 9, j ≠ 0 → ∀ C : Circuit,
      FanInTwo C → C.size ≤ 13 →
      C.gates.countP (fun g => GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op) ≤ 1 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x 0 || x j]) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
       x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
       x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 < (10 : ℕ)) →       (0 : ℕ) ∈ x1 ∨ (9 : ℕ) ∈ x1 →         (¬∀ x5 ∈ x1, x5 = (0 : ℕ) ∨ x5 = (9 : ℕ)) ∧ (0 : ℕ) ∈ x1 →           ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),             PEqualNP.MetaComplexity.FanInTwo x6 →               x6.size ≤ (13 : ℕ) →                 ∃ (x9 : Fin (9 : ℕ) → Bool),                   have x10 : List Bool := List.ofFn x9 ++ [!x9 (0 : Fin (9 : ℕ))];                   x6.eval (x10 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x11 : ℕ) => x10.getD x11 Bool.false) x1)]) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  intro pins hlen hlt _ hspec C hfan hsize
  let F (x : Fin 9 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  have hget : ∀ (x : Fin 9 → Bool) (k : Fin 9),
      (List.ofFn x ++ [!x 0]).getD k.val false = x k := by
    intro x k
    fin_cases k <;> rfl
  have hget0 : ∀ (x : Fin 9 → Bool),
      (List.ofFn x ++ [!x 0]).getD 0 false = x 0 := fun _ => rfl
  obtain ⟨j, hj0, hpair⟩ : ∃ j : Fin 9, j ≠ 0 ∧ ∀ x : Fin 9 → Bool,
      GateOp.or.eval (pins.map fun i => (List.ofFn x ++ [!x 0]).getD i false) =
        (x 0 || x j) := by
    obtain ⟨hnotall, h0mem⟩ := hspec
    obtain ⟨u, w, rfl⟩ := List.length_eq_two.mp hlen
    by_cases hu : u = 0
    · subst hu
      have hw0 : w ≠ 0 := fun hw => hnotall (by subst hw; simp)
      have hw9 : w ≠ 9 := fun hw => hnotall (by subst hw; simp)
      have hw10 : w < 10 := hlt w (by simp)
      have hwlt : w < 9 := by omega
      refine ⟨⟨w, hwlt⟩, fun h => hw0 (congrArg Fin.val h), fun x => ?_⟩
      change ((List.ofFn x ++ [!x 0]).getD 0 false ||
        ((List.ofFn x ++ [!x 0]).getD w false || false)) =
          (x 0 || x ⟨w, hwlt⟩)
      rw [Bool.or_false, hget0 x, hget x ⟨w, hwlt⟩]
    · have hw : w = 0 := by simp at h0mem; omega
      subst hw
      have hu9 : u ≠ 9 := fun hu9' => hnotall (by subst hu9'; simp)
      have hu10 : u < 10 := hlt u (by simp)
      have hult : u < 9 := by omega
      refine ⟨⟨u, hult⟩, fun h => hu (congrArg Fin.val h), fun x => ?_⟩
      change ((List.ofFn x ++ [!x 0]).getD u false ||
        ((List.ofFn x ++ [!x 0]).getD 0 false || false)) =
          (x 0 || x ⟨u, hult⟩)
      rw [Bool.or_false, hget x ⟨u, hult⟩, hget0 x, Bool.or_comm]
  change ∃ x, C.eval ((List.ofFn x ++ [!x 0]) ++
    [GateOp.or.eval (pins.map fun i => (List.ofFn x ++ [!x 0]).getD i false)]) ≠ F x
  simp_rw [hpair, List.append_assoc, List.cons_append, List.nil_append]
  by_contra! computes
  let g0 : Gate := ⟨.not, [0]⟩
  let g1 : Gate := ⟨.or, [0, j.val]⟩
  let full : Circuit := ⟨g0 :: g1 :: C.gates, C.output⟩
  have fullFan : FanInTwo full := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨by simp [g0], by simp [g0]⟩
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨by simp [g1], by simp [g1]⟩
      · exact hfan g hg
  have fullEval (x : Fin 9 → Bool) :
      full.eval (List.ofFn x) = C.eval (List.ofFn x ++ [!x 0, x 0 || x j]) := by
    change C.eval ((List.ofFn x ++ [!x 0]) ++
      [(List.ofFn x ++ [!x 0]).getD 0 false ||
        ((List.ofFn x ++ [!x 0]).getD j.val false || false)]) = _
    rw [Bool.or_false, hget0 x, hget x j]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have fullComputes : ∀ x : Fin 9 → Bool, full.eval (List.ofFn x) = F x := by
    intro x
    rw [fullEval]
    exact computes x
  let isNot (g : Gate) : Bool := GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op
  have lower := binaryBound full fullFan fullComputes
  have prefixCount : full.gates.countP (fun g => !isNot g) =
      1 + C.gates.countP (fun g => !isNot g) := by
    simp [full, g0, g1, isNot, Nat.add_comm]
  change 13 ≤ full.gates.countP (fun g => !isNot g) at lower
  rw [prefixCount] at lower
  have partition (gs : List Gate) :
      gs.countP (fun g => !isNot g) + gs.countP isNot = gs.length := by
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.countP_cons, List.length_cons]
      cases h : isNot g <;> simp <;> omega
  have total := partition C.gates
  have notCount : C.gates.countP isNot ≤ 1 := by
    change C.gates.length ≤ 13 at hsize
    omega
  obtain ⟨x, hx⟩ := oneNotSearch j hj0 C hfan hsize notCount
  exact hx (computes x)
