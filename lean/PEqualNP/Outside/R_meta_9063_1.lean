import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_9063_1
    (hleft : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      C.size ≤ 28 ∧ 27 ≤ C.output ∧ C.output < 27 + C.size ∧
      PEqualNP.TopForm.IsAO2 27 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      ∀ x : Fin 26 → Bool,
        C.eval (List.ofFn x ++ [x 1 || x 2]) = true ↔
          ∃ p l : Fin 13, l ∈ ([0, 2, 5, 6, 11, 12] : List (Fin 13)) ∧
            (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
    (hright : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      C.size ≤ 29 ∧ 27 ≤ C.output ∧ C.output < 27 + C.size ∧
      PEqualNP.TopForm.IsAO2 27 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      ∀ x : Fin 26 → Bool,
        C.eval (List.ofFn x ++ [x 1 || x 2]) = true ↔
          ∃ p l : Fin 13, l ∈ ([3, 4, 7, 8, 9, 10] : List (Fin 13)) ∧
            (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) :
    have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), x3 ≠ (1 : Fin (13 : ℕ)) ∧ (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ))) ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (58 : ℕ) ∧ (27 : ℕ) ≤ x2.output ∧ x2.output < (27 : ℕ) + x2.size ∧ PEqualNP.TopForm.IsAO2 (27 : ℕ) x2 ∧ (∀ x3 ∈ x2.gates, x3.inputs.Nodup) ∧ ∀ (x3 : Fin (26 : ℕ) → Bool), Minimal x1 x3 ∨ Maximal (fun (x4 : Fin (26 : ℕ) → Bool) => ¬x1 x4) x3 → (x2.eval (List.ofFn x3 ++ [x3 (1 : Fin (26 : ℕ)) || x3 (2 : Fin (26 : ℕ))]) = Bool.true ↔ x1 x3) := by
  classical
  let legal (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) :=
    ∀ i (hi : i < gs.length), let g := gs[i]
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup ∧
        ∀ u ∈ g.inputs, u < n + i
  have legal_iff (C : PEqualNP.CircuitLowerBounds.Circuit) (n : ℕ) :
      legal n C.gates ↔ PEqualNP.TopForm.IsAO2 n C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) := by
    have atG (i : ℕ) (hi : i < C.gates.length) :
        PEqualNP.MetaComplexity.NestedCover.gateAt C i = C.gates[i] :=
      List.getD_eq_getElem _ _ hi
    constructor
    · intro h
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · intro g hg
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
        exact (h i hi).1
      · intro i hi u hu
        rw [atG i hi] at hu
        exact (h i hi).2.2.2 u hu
      · intro g hg
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
        exact (h i hi).2.1
      · intro g hg
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
        exact (h i hi).2.2.1
    · rintro ⟨h, nd⟩ i hi
      have m := List.getElem_mem hi
      exact ⟨h.1 _ m, h.2.2 _ m, nd _ m, fun u hu => h.2.1 i hi u (by rwa [atG i hi])⟩
  have appendLegal {n : ℕ} {p q : List PEqualNP.CircuitLowerBounds.Gate}
      (hp : legal n p) (hq : legal (n + p.length) q) : legal n (p ++ q) := by
    intro i hi
    by_cases hl : i < p.length
    · simpa only [List.getElem_append_left hl] using hp i hl
    · have hr : i - p.length < q.length := by simp only [List.length_append] at hi; omega
      have add : n + p.length + (i - p.length) = n + i := by omega
      simpa only [List.getElem_append_right (by omega : p.length ≤ i), add]
        using hq (i - p.length) hr
  obtain ⟨A, As, Alo, Ahi, Aa, An, Af⟩ := hleft
  obtain ⟨B, Bs, Blo, Bhi, Ba, Bn, Bf⟩ := hright
  change A.gates.length ≤ 28 at As
  change B.gates.length ≤ 29 at Bs
  change A.output < 27 + A.gates.length at Ahi
  change B.output < 27 + B.gates.length at Bhi
  let offset := A.gates.length
  let shift (i : ℕ) := if i < 27 then i else i + offset
  let move (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
    ⟨g.op, g.inputs.map shift⟩
  have inj : Function.Injective shift := by
    intro i j h
    dsimp only [shift] at h
    split at h <;> split at h <;> omega
  have moved : legal (27 + A.gates.length) (B.gates.map move) := by
    intro i hi
    have h : i < B.gates.length := by simpa using hi
    have q := ((legal_iff B 27).mpr ⟨Ba, Bn⟩) i h
    simp only [List.getElem_map, move, List.length_map, List.mem_map]
    refine ⟨q.1, q.2.1, List.Nodup.map inj q.2.2.1, ?_⟩
    rintro _ ⟨j, hj, rfl⟩
    have bound := q.2.2.2 j hj
    dsimp only [shift, offset]
    split <;> omega
  have bout : shift B.output = B.output + offset := ite_eq_right (by omega)
  have distinct : A.output ≠ shift B.output := by rw [bout]; dsimp [offset]; omega
  let baseGates := A.gates ++ B.gates.map move
  let root : PEqualNP.CircuitLowerBounds.Gate := ⟨.or, [A.output, shift B.output]⟩
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨baseGates ++ [root], 27 + baseGates.length⟩
  have pn : baseGates.length = A.gates.length + B.gates.length := by simp [baseGates]
  have rootLegal : legal (27 + baseGates.length) [root] := by
    intro i hi
    have eq : i = 0 := by simpa using hi
    subst i
    refine ⟨Or.inr rfl, rfl, by simp [root, distinct], ?_⟩
    intro u hu
    change u ∈ [A.output, shift B.output] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · rw [pn]; omega
    · rw [pn, bout]; dsimp [offset]; omega
  have dl : PEqualNP.TopForm.IsAO2 27 D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) :=
    (legal_iff D 27).mp (appendLegal (appendLegal ((legal_iff A 27).mpr ⟨Aa, An⟩) moved) rootLegal)
  refine ⟨D, ?_, ?_, ?_, dl.1, dl.2, ?_⟩
  · change (baseGates ++ [root]).length ≤ 58
    simp only [List.length_append, List.length_cons, List.length_nil, pn]
    omega
  · change 27 ≤ 27 + baseGates.length
    omega
  · change 27 + baseGates.length < 27 + (baseGates ++ [root]).length
    simp
  intro x _
  let u := List.ofFn x ++ [x 1 || x 2]
  have ul : u.length = 27 := by simp [u]
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have trace (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
      ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp, rfl⟩
    | cons g gs ih =>
      obtain ⟨t, ht, hn⟩ := ih (step w g)
      exact ⟨_ :: t, by simpa only [List.foldl_cons, step, List.append_assoc,
        List.cons_append, List.nil_append] using ht, by simp [hn]⟩
  obtain ⟨mid, hm, ml⟩ := trace A.gates u
  have rd (t : List Bool) (i : ℕ) :
      (u ++ t).getD i false = ((u ++ mid) ++ t).getD (shift i) false := by
    by_cases hi : i < 27
    · simp only [shift, ite_eq_left hi]
      have hu : i < u.length := by omega
      have hum : i < (u ++ mid).length := by simp only [List.length_append]; omega
      calc
        (u ++ t).getD i false = u.getD i false := List.getD_append u t false i hu
        _ = (u ++ mid).getD i false := (List.getD_append u mid false i hu).symm
        _ = ((u ++ mid) ++ t).getD i false := (List.getD_append (u ++ mid) t false i hum).symm
    · simp only [shift, ite_eq_right hi]
      rw [List.getD_append_right _ _ _ _ (by omega : u.length ≤ i),
        List.getD_append_right _ _ _ _ (by simp only [List.length_append, ul, ml, offset]; omega)]
      simp only [List.length_append, ul, ml, offset]
      congr 1
      omega
  have simulate (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List Bool) :
      ∃ t : List Bool, gs.foldl step (u ++ acc) = u ++ t ∧
        (gs.map move).foldl step ((u ++ mid) ++ acc) = (u ++ mid) ++ t ∧
        t.length = acc.length + gs.length := by
    induction gs generalizing acc with
    | nil => exact ⟨acc, rfl, rfl, by simp⟩
    | cons g gs ih =>
      let bit := g.op.eval (g.inputs.map fun i => (u ++ acc).getD i false)
      have bitEq : (move g).op.eval ((move g).inputs.map fun i => ((u ++ mid) ++ acc).getD i false) = bit := by
        simp only [move, List.map_map, bit]
        congr 1
        apply List.map_congr_left
        intro i _
        exact (rd acc i).symm
      obtain ⟨t, hs, hp, ht⟩ := ih (acc ++ [bit])
      refine ⟨t, ?_, ?_, ?_⟩
      · simpa only [List.foldl_cons, step, List.append_assoc, bit] using hs
      · change (gs.map move).foldl step (((u ++ mid) ++ acc) ++ [_]) = _
        rw [bitEq, List.append_assoc]
        exact hp
      · simp only [List.length_append, List.length_cons, List.length_nil] at ht ⊢
        omega
  obtain ⟨tail, hs, hp, tl⟩ := simulate B.gates []
  simp only [List.append_nil, List.length_nil, Nat.zero_add] at hs hp tl
  have pEval : baseGates.foldl step u = (u ++ mid) ++ tail := by
    simpa only [baseGates, List.foldl_append, hm] using hp
  have pLen : ((u ++ mid) ++ tail).length = 27 + baseGates.length :=
    by simp [ul, ml, tl, pn]
  have Aval : ((u ++ mid) ++ tail).getD A.output false = A.eval u := by
    change ((u ++ mid) ++ tail).getD A.output false = (A.gates.foldl step u).getD A.output false
    rw [hm, List.getD_append _ _ _ _ (by simp only [List.length_append, ul, ml]; exact Ahi)]
  have Bval : ((u ++ mid) ++ tail).getD (shift B.output) false = B.eval u := by
    change ((u ++ mid) ++ tail).getD (shift B.output) false =
      (B.gates.foldl step u).getD B.output false
    rw [hs, rd]
  have Deval : D.eval u = (A.eval u || B.eval u) := by
    change ((baseGates ++ [root]).foldl step u).getD (27 + baseGates.length) false = _
    rw [List.foldl_append, pEval]
    change (((u ++ mid) ++ tail) ++ [((u ++ mid) ++ tail).getD A.output false ||
      (((u ++ mid) ++ tail).getD (shift B.output) false || false)]).getD (27 + baseGates.length) false = _
    rw [List.getD_append_right _ _ _ _ (by omega), pLen, Nat.sub_self]
    rw [Aval, Bval]
    simp
  have splitLines (l : Fin 13) :
      l ≠ 1 ↔ l ∈ ([0, 2, 5, 6, 11, 12] : List (Fin 13)) ∨
               l ∈ ([3, 4, 7, 8, 9, 10] : List (Fin 13)) := by
    fin_cases l <;> decide
  change D.eval u = true ↔ _
  rw [Deval, Bool.or_eq_true, Af x, Bf x]
  constructor
  · rintro (⟨p, l, hl, hI, hP, hL⟩ | ⟨p, l, hl, hI, hP, hL⟩)
    · exact ⟨p, l, (splitLines l).mpr (Or.inl hl), hI, hP, hL⟩
    · exact ⟨p, l, (splitLines l).mpr (Or.inr hl), hI, hP, hL⟩
  · rintro ⟨p, l, hl, hI, hP, hL⟩
    rcases (splitLines l).mp hl with ha | hb
    · exact Or.inl ⟨p, l, ha, hI, hP, hL⟩
    · exact Or.inr ⟨p, l, hb, hI, hP, hL⟩
