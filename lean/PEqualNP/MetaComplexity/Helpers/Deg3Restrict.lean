import PEqualNP.MetaComplexity.Helpers.LineDegTest
import PEqualNP.Defs.MetaComplexityLgpMono
import PEqualNP.Defs.MetaComplexityMinimal

/-!
# Theorem A at line-degree 3: card 02 (monotonicity) and card 03 (Lemma RESTRICT, padded)

Card 02: every wire of an AND/OR circuit is monotone in the input.

Card 03 as stated in the plan is false when the incidence is empty: a circuit whose output gate
reads a later wire is constant false and so computes the empty edge function, while the wires `a`
and `b` it reads may be constant true (`card03_restrict_false`). Two repairs are proved: with both
reads below the output (`card03_restrict_of_lt`), and with a nonempty incidence
(`card03_restrict_of_edge`), which implies the first.
-/

namespace PEqualNP.MetaComplexity.Deg3

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.LineDegTest

/-- CARD 02 (monotonicity). Every wire of an AND/OR circuit is monotone in the input. -/
theorem card02_mono : ∀ (n : ℕ) (C : Circuit) (o : ℕ), IsMonotoneCircuit C →
    ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      (C.wires (List.ofFn x)).getD o false = true → (C.wires (List.ofFn y)).getD o false = true := by
  intro n C o hm x y hxy h
  refine W_mono C.gates hm (List.ofFn x) (List.ofFn y) (by simp) ?_ o h
  intro i hi
  rw [ofFn_getD] at hi ⊢
  by_cases hin : i < n
  · rw [dif_pos hin] at hi ⊢; exact hxy _ hi
  · rw [dif_neg hin] at hi; exact absurd hi (by simp)

/-- The wires after `gs` extend the starting list. -/
theorem d3r_W_prefix (gs : List Gate) (y : List Bool) : ∃ r, W gs y = y ++ r := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨[], by simp [W]⟩
  | append_singleton gs g ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨r ++ [g.op.eval (g.inputs.map fun i => (W gs y).getD i false)], by rw [W_snoc, hr]; simp⟩

theorem d3r_W_append (gs hs : List Gate) (y : List Bool) : W (gs ++ hs) y = W hs (W gs y) := by
  simp [W, List.foldl_append]

theorem d3r_getD_prefix (l r : List Bool) (t : ℕ) (h : t < l.length) :
    (l ++ r).getD t false = l.getD t false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem d3r_getD_ge (l : List Bool) (t : ℕ) (h : l.length ≤ t) : l.getD t false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- Output factorization (the content of card 01, kept under its own name here). -/
theorem d3r_out_and (n : ℕ) (C : Circuit) (a b : ℕ) (hout : n ≤ C.output)
    (hgate : C.gates[C.output - n]? = some { op := GateOp.and, inputs := [a, b] })
    (z : Fin n → Bool) :
    circuitFun n C z = true ↔
      (a < C.output ∧ circuitFun n ⟨C.gates, a⟩ z = true) ∧
      (b < C.output ∧ circuitFun n ⟨C.gates, b⟩ z = true) := by
  set j := C.output - n with hj
  have hjl : j < C.gates.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hgate; exact absurd hgate (by simp)
  have hgj : C.gates[j] = { op := GateOp.and, inputs := [a, b] } := by
    rw [List.getElem?_eq_getElem hjl] at hgate; exact Option.some.inj hgate
  have hsplit : C.gates = (C.gates.take j ++ [C.gates[j]]) ++ C.gates.drop (j + 1) := by
    rw [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hjl,
      List.take_append_drop]
  set x := List.ofFn z
  have hxl : x.length = n := by simp [x]
  set V := W (C.gates.take j) x
  have hVl : V.length = C.output := by
    simp only [V, W_length, hxl, List.length_take]; omega
  obtain ⟨r, hr⟩ := d3r_W_prefix (C.gates.drop (j + 1)) (W (C.gates.take j ++ [C.gates[j]]) x)
  obtain ⟨r1, hr1⟩ := d3r_W_prefix [C.gates[j]] V
  have hall : C.wires x = V ++ (r1 ++ r) := by
    show W C.gates x = _
    rw [hsplit, d3r_W_append, hr, d3r_W_append, hr1, List.append_assoc]
  have hread : ∀ t, t < C.output → (C.wires x).getD t false = V.getD t false := by
    intro t ht; rw [hall]; exact d3r_getD_prefix _ _ _ (by omega)
  have hoV : (C.wires x).getD C.output false =
      GateOp.and.eval ([a, b].map fun i => V.getD i false) := by
    have h2 : C.wires x = (V ++ [GateOp.and.eval ([a, b].map fun i => V.getD i false)]) ++ r := by
      show W C.gates x = _
      rw [hsplit, d3r_W_append, hr, W_snoc, hgj]
    rw [h2, d3r_getD_prefix _ _ _ (by simp [hVl]), getD_snoc, if_neg (by omega),
      if_pos hVl.symm]
  have hval : ∀ t, (V.getD t false = true) ↔ (t < C.output ∧ (C.wires x).getD t false = true) := by
    intro t
    constructor
    · intro h
      have ht : t < C.output := by have := getD_false_lt h; omega
      exact ⟨ht, by rw [hread t ht]; exact h⟩
    · rintro ⟨ht, h⟩; rwa [hread t ht] at h
  have hC : circuitFun n C z = (C.wires x).getD C.output false := rfl
  have hA : circuitFun n ⟨C.gates, a⟩ z = (C.wires x).getD a false := rfl
  have hB : circuitFun n ⟨C.gates, b⟩ z = (C.wires x).getD b false := rfl
  rw [hC, hA, hB, hoV, ← hval a, ← hval b]
  simp [GateOp.eval]

/-- The plan's statement of card 03, as a proposition. -/
def Card03Stmt : Prop := ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (a b : ℕ) (w : Fin N) (T : Finset (Fin N)),
    Monotone2 C → N + N ≤ C.output →
    C.gates[C.output - (N + N)]? = some { op := GateOp.and, inputs := [a, b] } →
    (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    (∀ p ∈ T, ¬ I p w) →
    circuitFun (N + N) ⟨C.gates, b⟩
      (Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ T)) (fun l => decide (l = w))) = true →
    ∀ x : Fin (N + N) → Bool,
      circuitFun (N + N) ⟨C.gates, a⟩ (fun i => ((Fin.addCases (motive := fun _ => Option Bool)
          (fun p => if p ∈ T then some true else if I p w then some false else none)
          (fun l => if l = w then some true else if ∃ p' ∈ T, I p' l then some false else none)) i).getD (x i))
        = true ↔
      ∃ p l : Fin N, (I p l ∧ p ∉ T ∧ ¬ I p w ∧ l ≠ w ∧ ¬ ∃ p' ∈ T, I p' l) ∧
        x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true

/-- CARD 03 AS STATED IN THE PLAN IS FALSE. Witness: one point, one line, no incidence; gates
`AND [3, 3]` (wire 2, the output) and `AND []` (wire 3, constant true). The output reads a later
wire, so the circuit is constant false and computes the empty edge function; `a = b = 3` is true
everywhere, so the left side holds and the right side (an incident pair) fails. -/
theorem card03_restrict_false : ¬ Card03Stmt := by
  intro h
  have := @h 1 (fun _ _ => False) (fun _ _ => instDecidableFalse)
    ⟨[{ op := GateOp.and, inputs := [3, 3] }, { op := GateOp.and, inputs := [] }], 2⟩ 3 3 0 ∅
    (by intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp)
    (by decide) rfl
    (by intro z; simp [circuitFun, Circuit.eval, Circuit.wires, GateOp.eval])
    (by simp)
    (by simp [circuitFun, Circuit.eval, Circuit.wires, GateOp.eval]) (fun _ => true)
  have h2 := this.1 (by simp [circuitFun, Circuit.eval, Circuit.wires, GateOp.eval])
  simp at h2

/-- CARD 03 (Lemma RESTRICT, padded), repaired: both reads of the output gate below the output. -/
theorem card03_restrict_of_lt : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (a b : ℕ) (w : Fin N) (T : Finset (Fin N)),
    Monotone2 C → N + N ≤ C.output →
    C.gates[C.output - (N + N)]? = some { op := GateOp.and, inputs := [a, b] } →
    a < C.output → b < C.output →
    (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    (∀ p ∈ T, ¬ I p w) →
    circuitFun (N + N) ⟨C.gates, b⟩
      (Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ T)) (fun l => decide (l = w))) = true →
    ∀ x : Fin (N + N) → Bool,
      circuitFun (N + N) ⟨C.gates, a⟩ (fun i => ((Fin.addCases (motive := fun _ => Option Bool)
          (fun p => if p ∈ T then some true else if I p w then some false else none)
          (fun l => if l = w then some true else if ∃ p' ∈ T, I p' l then some false else none)) i).getD (x i))
        = true ↔
      ∃ p l : Fin N, (I p l ∧ p ∉ T ∧ ¬ I p w ∧ l ≠ w ∧ ¬ ∃ p' ∈ T, I p' l) ∧
        x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true := by
  intro N I _ C a b w T hmono hout hgate ha hb hcorr hT hbT x
  set z : Fin (N + N) → Bool := fun i => ((Fin.addCases (motive := fun _ => Option Bool)
          (fun p => if p ∈ T then some true else if I p w then some false else none)
          (fun l => if l = w then some true else if ∃ p' ∈ T, I p' l then some false else none)) i).getD (x i)
    with hz
  have hzp : ∀ p : Fin N, z (Fin.castAdd N p) =
      (if p ∈ T then true else if I p w then false else x (Fin.castAdd N p)) := by
    intro p; simp only [hz, Fin.addCases_left]; split_ifs <;> rfl
  have hzl : ∀ l : Fin N, z (Fin.natAdd N l) =
      (if l = w then true else if ∃ p' ∈ T, I p' l then false else x (Fin.natAdd N l)) := by
    intro l; simp only [hz, Fin.addCases_right]; split_ifs <;> rfl
  have hfac := d3r_out_and (N + N) C a b hout hgate z
  constructor
  · intro haz
    -- the degree-1 factor is true at z by monotonicity
    have hle : ∀ i, (Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ T))
        (fun l => decide (l = w))) i = true → z i = true := by
      intro i
      induction i using Fin.addCases with
      | left p =>
        rw [Fin.addCases_left, hzp]; intro h; simp only [decide_eq_true_eq] at h; simp [h]
      | right l =>
        rw [Fin.addCases_right, hzl]; intro h; simp only [decide_eq_true_eq] at h; simp [h]
    have hmono' : IsMonotoneCircuit C := fun g hg => by
      have := (hmono g hg).1
      simpa using this
    have hbz : circuitFun (N + N) ⟨C.gates, b⟩ z = true :=
      card02_mono (N + N) C b hmono' _ z hle hbT
    have hCz := hfac.2 ⟨⟨ha, haz⟩, ⟨hb, hbz⟩⟩
    obtain ⟨p, l, hpl, hp, hl⟩ := (hcorr z).1 hCz
    rw [hzp] at hp
    rw [hzl] at hl
    have hlw : l ≠ w := by
      rintro rfl
      by_cases hpT : p ∈ T
      · exact hT p hpT hpl
      · rw [if_neg hpT, if_pos hpl] at hp; exact absurd hp (by simp)
    rw [if_neg hlw] at hl
    have hlT : ¬ ∃ p' ∈ T, I p' l := by
      intro hh; rw [if_pos hh] at hl; exact absurd hl (by simp)
    rw [if_neg hlT] at hl
    have hpT : p ∉ T := fun h => hlT ⟨p, h, hpl⟩
    rw [if_neg hpT] at hp
    have hpw : ¬ I p w := by intro h; rw [if_pos h] at hp; exact absurd hp (by simp)
    rw [if_neg hpw] at hp
    exact ⟨p, l, ⟨hpl, hpT, hpw, hlw, hlT⟩, hp, hl⟩
  · rintro ⟨p, l, ⟨hpl, hpT, hpw, hlw, hlT⟩, hp, hl⟩
    have hCz : circuitFun (N + N) C z = true := (hcorr z).2 ⟨p, l, hpl,
      by rw [hzp, if_neg hpT, if_neg hpw]; exact hp,
      by rw [hzl, if_neg hlw, if_neg hlT]; exact hl⟩
    exact ((hfac.1 hCz).1).2

/-- CARD 03 (Lemma RESTRICT, padded), repaired: a nonempty incidence. -/
theorem card03_restrict_of_edge : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (a b : ℕ) (w : Fin N) (T : Finset (Fin N)),
    (∃ p l : Fin N, I p l) →
    Monotone2 C → N + N ≤ C.output →
    C.gates[C.output - (N + N)]? = some { op := GateOp.and, inputs := [a, b] } →
    (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    (∀ p ∈ T, ¬ I p w) →
    circuitFun (N + N) ⟨C.gates, b⟩
      (Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ T)) (fun l => decide (l = w))) = true →
    ∀ x : Fin (N + N) → Bool,
      circuitFun (N + N) ⟨C.gates, a⟩ (fun i => ((Fin.addCases (motive := fun _ => Option Bool)
          (fun p => if p ∈ T then some true else if I p w then some false else none)
          (fun l => if l = w then some true else if ∃ p' ∈ T, I p' l then some false else none)) i).getD (x i))
        = true ↔
      ∃ p l : Fin N, (I p l ∧ p ∉ T ∧ ¬ I p w ∧ l ≠ w ∧ ¬ ∃ p' ∈ T, I p' l) ∧
        x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true := by
  intro N I _ C a b w T hedge hmono hout hgate hcorr hT hbT
  obtain ⟨p, l, hpl⟩ := hedge
  have hC := (hcorr (fun _ => true)).2 ⟨p, l, hpl, rfl, rfl⟩
  have hf := (d3r_out_and (N + N) C a b hout hgate _).1 hC
  exact card03_restrict_of_lt N I C a b w T hmono hout hgate hf.1.1 hf.2.1 hcorr hT hbT

end PEqualNP.MetaComplexity.Deg3
