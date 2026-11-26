import Mathlib
import PEqualNP.Defs

-- Cut: with b = false the single OR reader of wire 6 is a copy, so the rest is a circuit for the
-- 10-edge function z; z needs 13 gates (h1), so only the exact-13 case (h3) is left.
theorem PEqualNP.Outside.R_meta_4163_288
    (h1 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 8
      (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
        (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (h2 :
      let read : PEqualNP.CircuitLowerBounds.Gate → Bool := fun g =>
        (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).any (fun i => decide (i = 6))
      let input : Bool → (Fin 8 → Bool) → List Bool := fun b x =>
        [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D →
        1 ≤ D.gates.countP read →
        (∃ x : Fin 8 → Bool, D.eval (input false x) = false) →
        ∃ R : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo R ∧ R.size + 1 ≤ D.size ∧
          ∀ x : Fin 8 → Bool, R.eval (List.ofFn x) = D.eval (input false x))
    (h3 : let t := fun (x : Fin 8 → Bool) =>
      let n := PEqualNP.MetaComplexity.tableIndex x
      ([18369897887404062920, 18446740762289764600, 18446744073709551560,
        18446744073709551608] : List Nat).getD (n / 64) 0 |>.testBit (n % 64)
    let args := fun (b : Bool) (x : Fin 8 → Bool) =>
      [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]
    let used := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
      if g.op.eval [false,false] then g.inputs.take 1 else g.inputs
    ∀ (p s : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (o : Nat),
    let c : PEqualNP.CircuitLowerBounds.Circuit := ⟨p ++ g :: s, o⟩
    PEqualNP.MetaComplexity.FanInTwo c → p.length + s.length = 13 →
    (∀ h ∈ p ++ s, (used h).any (fun j => decide (j = 6)) = false) →
    (used g).any (fun j => decide (j = 6)) = true → g.op = .or →
    (p.filter (fun g => (used g).contains 9)).length +
      (s.filter (fun g => (used g).contains 9 || (used g).contains (10 + p.length))).length ≤ 3 →
    ¬ ((∀ x, c.eval (args false x) = t x) ∧ (∀ x, c.eval (args true x) = (t x || x 0 || x 3)))) :
have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) =>   have x2 : ℕ := PEqualNP.MetaComplexity.tableIndex x1;   ([(18369897887404062920 : ℕ), (18446740762289764600 : ℕ), (18446744073709551560 : ℕ), (18446744073709551608 : ℕ)].getD (x2 / (64 : ℕ)) (0 : ℕ)).testBit (x2 % (64 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => if x3.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x3.inputs else x3.inputs; ∀ (x4 x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : ℕ),   have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x4 ++ x6 :: x5, output := x7 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x8 → x4.length + x5.length ≤ (13 : ℕ) → (∀ x11 ∈ x4 ++ x5, ((x3 x11).any fun (x13 : ℕ) => Decidable.decide (x13 = (6 : ℕ))) = Bool.false) → ((x3 x6).any fun (x12 : ℕ) => Decidable.decide (x12 = (6 : ℕ))) = Bool.true → x6.op = PEqualNP.CircuitLowerBounds.GateOp.or → (10 : ℕ) ≤ x4.length + x5.length - ((List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (x3 x14).contains (9 : ℕ)) x4).length + (List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (x3 x14).contains (9 : ℕ) || (x3 x14).contains ((10 : ℕ) + x4.length)) x5).length) → ¬((∀ (x15 : Fin (8 : ℕ) → Bool), x8.eval (x2 Bool.false x15) = x1 x15) ∧ ∀ (x15 : Fin (8 : ℕ) → Bool), x8.eval (x2 Bool.true x15) = (x1 x15 || x15 (0 : Fin (8 : ℕ)) || x15 (3 : Fin (8 : ℕ)))) := by
  dsimp only at h2 h3 ⊢
  intro p s g o hfan hsize hnone hraw hor hcount hboth
  obtain ⟨hzero, hone⟩ := hboth
  by_cases h13 : p.length + s.length = 13
  · exact h3 p s g o hfan h13 hnone hraw hor (by omega) ⟨hzero, hone⟩
  · have unpack : ∀ x : Fin 8 → Bool,
        (([18369897887404062920, 18446740762289764600, 18446744073709551560,
          18446744073709551608] : List Nat).getD (PEqualNP.MetaComplexity.tableIndex x / 64) 0).testBit
          (PEqualNP.MetaComplexity.tableIndex x % 64) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
          (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) := by
      decide +kernel
    have hpos : 1 ≤ (p ++ g :: s).countP (fun g : PEqualNP.CircuitLowerBounds.Gate =>
        (if g.op.eval [false, false] then g.inputs.take 1 else g.inputs).any
          (fun i => decide (i = 6))) :=
      List.countP_pos_iff.mpr ⟨g, by simp, hraw⟩
    obtain ⟨R, hR, hsz, heq⟩ := h2 ⟨p ++ g :: s, o⟩ hfan hpos
      ⟨fun _ => false, (hzero (fun _ => false)).trans ((unpack (fun _ => false)).trans rfl)⟩
    apply h1
    refine ⟨R, hR, ?_, fun x => ?_⟩
    · change R.size + 1 ≤ (p ++ g :: s).length at hsz
      simp only [List.length_append, List.length_cons] at hsz
      omega
    · exact (heq x).trans ((hzero x).trans (unpack x))
