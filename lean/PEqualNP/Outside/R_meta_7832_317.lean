import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7832_317
    (search :
      let rows : List (ℕ × ℕ) := [(1, 1), (2, 1), (0, 8191), (1, 3054), (3, 972), (5, 2984), (7, 904), (11, 832), (13, 2848), (19, 708), (21, 2720), (25, 2656), (29, 2592), (37, 2440), (39, 392), (41, 2370), (71, 896), (83, 644), (85, 2688), (101, 2432), (133, 808), (135, 776), (141, 800), (161, 266), (207, 768), (349, 2560), (1917, 2048), (8191, 0)]
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (j u v : ℕ),
        C.size ≤ 64 ∧ PEqualNP.TopForm.IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        C.output = 26 + j ∧
        C.gates[j]? = some {op := .and, inputs := [u, v]} ∧
        ∀ (r : Fin 28) (k : Fin 3) (b : Fin 13),
          let T := rows.getD r.val (0, 0)
          let read (n : ℕ) (i : Fin 13) := n.testBit (((if k = 0 then (1 : Fin 13) else if k = 1 then 3 else 9) * i + b).val)
          let w := PEqualNP.BlindGate.wireValue C 26 (Fin.append (read T.1) (read T.2))
          if r.val < 2 then w u = true ∧ w v = true
          else w (if read T.2 0 = true then u else v) = false)
    (cover :
      let rows : List (ℕ × ℕ) := [(0, 8191), (1, 3054), (3, 972), (5, 2984), (7, 904), (11, 832), (13, 2848), (19, 708), (21, 2720), (25, 2656), (29, 2592), (37, 2440), (39, 392), (41, 2370), (71, 896), (83, 644), (85, 2688), (101, 2432), (133, 808), (135, 776), (141, 800), (161, 266), (207, 768), (349, 2560), (1917, 2048), (8191, 0)]
      ∀ m : ℕ, m < 8192 →
        let y (i : Fin 13) := m.testBit i.val
        let z (l : Fin 13) := !(y l || y (l + 1) || y (l + 3) || y (l + 9))
        (∀ i : Fin 13, y i = false →
          ∃ l : Fin 13, (i = l ∨ i = l+1 ∨ i = l+3 ∨ i = l+9) ∧ z l = true) →
        ∃ (r : Fin 26) (k : Fin 3) (b : Fin 13),
          let T := rows.getD r.val (0, 0)
          let read (n : ℕ) (i : Fin 13) := n.testBit (((if k = 0 then (1 : Fin 13) else if k = 1 then 3 else 9) * i + b).val)
          ∀ i : Fin 13, y i = read T.1 i ∧ z i = read T.2 i) :
    (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),   x3.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧         x3.output = (26 : ℕ) + x4 ∧           x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧             (∀ (x7 x8 : Fin (13 : ℕ)),                 x1 x7 x8 →                   have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                   PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧               ∀ (x7 : Fin (13 : ℕ) → Bool), (∀ (x8 : Fin (13 : ℕ)), x7 x8 = Bool.false → ∃ (x10 : Fin (13 : ℕ)), x1 x8 x10 ∧ x2 x7 x10 = Bool.true) → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) (Fin.append x7 (x2 x7)) (if x2 x7 (0 : Fin (13 : ℕ)) = Bool.true then x5 else x6) = Bool.false) := by
  let neg : List (ℕ × ℕ) := [(0, 8191), (1, 3054), (3, 972), (5, 2984), (7, 904), (11, 832), (13, 2848), (19, 708), (21, 2720), (25, 2656), (29, 2592), (37, 2440), (39, 392), (41, 2370), (71, 896), (83, 644), (85, 2688), (101, 2432), (133, 808), (135, 776), (141, 800), (161, 266), (207, 768), (349, 2560), (1917, 2048), (8191, 0)]
  let rows : List (ℕ × ℕ) := (1, 1) :: (2, 1) :: neg
  let read (k : Fin 3) (b : Fin 13) (n : ℕ) (i : Fin 13) :=
    n.testBit (((if k = 0 then (1 : Fin 13) else if k = 1 then 3 else 9) * i + b).val)
  let probe (r : ℕ) (k : Fin 3) (b : Fin 13) : Fin 26 → Bool :=
    Fin.append (read k b (rows.getD r (0, 0)).1) (read k b (rows.getD r (0, 0)).2)
  let present (r : ℕ) (k : Fin 3) (b : Fin 13) := read k b (rows.getD r (0, 0)).2 0
  let Z (y : Fin 13 → Bool) (l : Fin 13) := !(y l || y (l+1) || y (l+3) || y (l+9))
  let E (p l : Fin 13) := p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
  have positive : ∀ p l : Fin 13, E p l →
      ∃ (r : Fin 2) (k : Fin 3) (b : Fin 13), ∀ i : Fin 26,
        probe r.val k b i = decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l) := by
    dsimp only [E, probe, rows, neg, read]
    decide +kernel
  obtain ⟨C, j, u, v, hs, hC, hn, ho, hj, tests⟩ := search
  change ∀ (r : Fin 28) (k : Fin 3) (b : Fin 13),
    if r.val < 2 then PEqualNP.BlindGate.wireValue C 26 (probe r.val k b) u = true ∧
      PEqualNP.BlindGate.wireValue C 26 (probe r.val k b) v = true
    else PEqualNP.BlindGate.wireValue C 26 (probe r.val k b)
      (if present r.val k b = true then u else v) = false at tests
  refine ⟨C, j, u, v, hs, hC, hn, ho, hj, ?_, ?_⟩
  · intro p l h
    obtain ⟨r, k, b, hr⟩ := positive p l h
    have check := tests ⟨r.val, by omega⟩ k b
    rw [if_pos r.isLt] at check
    simpa only [funext hr] using check
  · intro y hy
    let word := BitVec.ofBoolListLE (List.ofFn y)
    have small : word.toNat < 8192 := by
      simpa [word] using word.isLt
    let m : Fin 8192 := ⟨word.toNat, small⟩
    have bits (i : Fin 13) : m.val.testBit i.val = y i := by
      change word.getLsbD i.val = y i
      rw [show word = BitVec.ofBoolListLE (List.ofFn y) from rfl, BitVec.getLsbD_ofBoolListLE]
      have hi : i.val < (List.ofFn y).length := by simpa only [List.length_ofFn] using i.isLt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      exact List.getElem_ofFn hi
    have h := cover m.val m.isLt
    change (∀ i : Fin 13, m.val.testBit i.val = false →
        ∃ l : Fin 13, E i l ∧ Z (fun a : Fin 13 => m.val.testBit a.val) l = true) →
      ∃ (r : Fin 26) (k : Fin 3) (b : Fin 13), ∀ i : Fin 13,
        m.val.testBit i.val = read k b (neg.getD r.val (0, 0)).1 i ∧
        Z (fun a : Fin 13 => m.val.testBit a.val) i = read k b (neg.getD r.val (0, 0)).2 i at h
    simp only [bits] at h
    obtain ⟨r, k, b, hr⟩ := h hy
    let i : Fin 28 := ⟨r.val + 2, by omega⟩
    have check := tests i k b
    rw [if_neg (show ¬ i.val < 2 by dsimp [i]; omega)] at check
    have row : rows.getD i.val (0, 0) = neg.getD r.val (0, 0) := rfl
    have points : read k b (neg.getD r.val (0, 0)).1 = y := funext fun a => (hr a).1.symm
    have lines : read k b (neg.getD r.val (0, 0)).2 = Z y := funext fun a => (hr a).2.symm
    simpa only [probe, present, row, points, lines, Z] using check
