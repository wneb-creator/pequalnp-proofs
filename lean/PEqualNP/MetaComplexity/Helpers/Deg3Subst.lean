import PEqualNP.MetaComplexity.Helpers.Deg3R1
import PEqualNP.MetaComplexity.Helpers.Deg3Restrict
import PEqualNP.MetaComplexity.Helpers.Deg3Assembly

/-!
# Theorem A at line-degree 3: card 04 (substitution of fixed inputs), conjecture until checked

Fixing some inputs to constants is realized by a circuit on the same inputs, no larger, AND/OR of
fan-in at most two, of no larger line-degree. Gate by gate: an AND reading an input fixed false
becomes the constant-false gate `OR []`; otherwise its reads of inputs fixed true are dropped. An
OR reading an input fixed true becomes the constant-true gate `AND []`; otherwise its reads of
inputs fixed false are dropped. Reads of gate wires, of free inputs and of later or missing
wires are kept: they read the same value (false, degree 0 for a later or missing wire) in both
circuits. If the output is itself a fixed input, the new circuit is one constant gate.
-/

namespace PEqualNP.MetaComplexity.Deg3

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.LineDegTest

/-- The fixed value of wire `t`, if `t` is an input fixed by `fx`. -/
def d3sFv (n : ℕ) (fx : Fin n → Option Bool) (t : ℕ) : Option Bool :=
  if h : t < n then fx ⟨t, h⟩ else none

/-- The gate rewrite. -/
def d3sGate (fv : ℕ → Option Bool) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and =>
    if g.inputs.any (fun i => decide (fv i = some false)) then ⟨GateOp.or, []⟩
    else ⟨GateOp.and, g.inputs.filter (fun i => (fv i).isNone)⟩
  | GateOp.or =>
    if g.inputs.any (fun i => decide (fv i = some true)) then ⟨GateOp.and, []⟩
    else ⟨GateOp.or, g.inputs.filter (fun i => (fv i).isNone)⟩
  | _ => g

theorem d3s_gate_mono (fv : ℕ → Option Bool) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (d3sGate fv g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      (d3sGate fv g).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl
  · simp only [d3sGate]
    split_ifs
    · simp
    · refine ⟨by simp, le_trans (List.length_filter_le _ _) hlen⟩
  · simp only [d3sGate]
    split_ifs
    · simp
    · refine ⟨by simp, le_trans (List.length_filter_le _ _) hlen⟩

theorem d3s_gate_eval (fv : ℕ → Option Bool) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (f F : ℕ → Bool) (hfix : ∀ i ∈ g.inputs, ∀ b, fv i = some b → F i = b)
    (hfree : ∀ i ∈ g.inputs, fv i = none → f i = F i) :
    (d3sGate fv g).op.eval ((d3sGate fv g).inputs.map f) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hfix hfree
  rcases hop with rfl | rfl
  · simp only [d3sGate]
    split_ifs with h
    · simp only [List.any_eq_true, decide_eq_true_eq] at h
      obtain ⟨i, hi, hfi⟩ := h
      have := hfix i hi false hfi
      symm
      simp only [GateOp.eval, List.map_nil, List.any_nil]
      rw [List.all_eq_false]
      exact ⟨F i, List.mem_map.2 ⟨i, hi, rfl⟩, by simp [this]⟩
    · simp only [List.any_eq_true, decide_eq_true_eq, not_exists, not_and] at h
      simp only [GateOp.eval]
      apply Bool.eq_iff_iff.2
      simp only [List.all_eq_true, List.mem_map, List.mem_filter, forall_exists_index, and_imp,
        Option.isNone_iff_eq_none, id_eq]
      constructor
      · rintro hall _ i hi rfl
        cases hfv : fv i with
        | none => rw [← hfree i hi hfv]; exact hall _ i hi hfv rfl
        | some b =>
          rw [hfix i hi b hfv]
          cases b
          · exact absurd hfv (h i hi)
          · rfl
      · rintro hall _ i hi hfv rfl
        rw [hfree i hi hfv]; exact hall _ i hi rfl
  · simp only [d3sGate]
    split_ifs with h
    · simp only [List.any_eq_true, decide_eq_true_eq] at h
      obtain ⟨i, hi, hfi⟩ := h
      have := hfix i hi true hfi
      symm
      simp only [GateOp.eval, List.map_nil, List.all_nil]
      rw [List.any_eq_true]
      exact ⟨F i, List.mem_map.2 ⟨i, hi, rfl⟩, by simp [this]⟩
    · simp only [List.any_eq_true, decide_eq_true_eq, not_exists, not_and] at h
      simp only [GateOp.eval]
      apply Bool.eq_iff_iff.2
      simp only [List.any_eq_true, List.mem_map, List.mem_filter, Option.isNone_iff_eq_none, id_eq]
      constructor
      · rintro ⟨_, ⟨i, ⟨hi, hfv⟩, rfl⟩, hv⟩
        exact ⟨F i, ⟨i, hi, rfl⟩, by rw [← hfree i hi hfv]; exact hv⟩
      · rintro ⟨_, ⟨i, hi, rfl⟩, hv⟩
        cases hfv : fv i with
        | none => exact ⟨f i, ⟨i, ⟨hi, hfv⟩, rfl⟩, by rw [hfree i hi hfv]; exact hv⟩
        | some b =>
          rw [hfix i hi b hfv] at hv
          subst hv
          exact absurd hfv (h i hi)

theorem d3s_sum_filter (l : List ℕ) (p : ℕ → Bool) (d' d : ℕ → ℕ) (h : ∀ i ∈ l, d' i ≤ d i) :
    ((l.filter p).map d').sum ≤ (l.map d).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have ih' := ih (fun i hi => h i (by simp [hi]))
    rw [List.filter_cons]
    split_ifs <;> simp <;> omega

theorem d3s_max_filter (l : List ℕ) (p : ℕ → Bool) (d' d : ℕ → ℕ) (h : ∀ i ∈ l, d' i ≤ d i) :
    ((l.filter p).map d').foldr max 0 ≤ (l.map d).foldr max 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have ih' := ih (fun i hi => h i (by simp [hi]))
    rw [List.filter_cons]
    split_ifs <;> simp <;> omega

theorem d3s_gate_deg (fv : ℕ → Option Bool) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (d' d : ℕ → ℕ) (h : ∀ i ∈ g.inputs, d' i ≤ d i) :
    d3r1DegOp (d3sGate fv g).op ((d3sGate fv g).inputs.map d') ≤
      d3r1DegOp g.op (g.inputs.map d) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop h
  have hne : GateOp.or ≠ GateOp.and := fun e => GateOp.noConfusion e
  rcases hop with rfl | rfl
  · simp only [d3sGate]
    split_ifs
    · simp [d3r1DegOp, hne]
    · simp only [d3r1DegOp, if_pos rfl]; exact d3s_sum_filter _ _ _ _ h
  · simp only [d3sGate]
    split_ifs
    · simp [d3r1DegOp]
    · simp only [d3r1DegOp, if_neg hne]; exact d3s_max_filter _ _ _ _ h

/-- The invariant of the rewrite, gate prefix by gate prefix. -/
theorem d3s_inv (n : ℕ) (fx : Fin n → Option Bool) (x : Fin n → Bool) (init : List ℕ)
    (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    (∀ t, d3sFv n fx t = none →
      (d3r1Fold false GateOp.eval (gs.map (d3sGate (d3sFv n fx))) (List.ofFn x)).getD t false =
      (d3r1Fold false GateOp.eval gs (List.ofFn (fun i => (fx i).getD (x i)))).getD t false) ∧
    (∀ t, (d3r1Fold 0 d3r1DegOp (gs.map (d3sGate (d3sFv n fx))) init).getD t 0 ≤
      (d3r1Fold 0 d3r1DegOp gs init).getD t 0) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨fun t ht => ?_, fun t => le_refl _⟩
    simp only [List.map_nil, d3r1Fold, List.foldl_nil, ofFn_getD]
    by_cases h : t < n
    · rw [dif_pos h, dif_pos h]
      simp only [d3sFv, dif_pos h] at ht
      rw [ht]; rfl
    · rw [dif_neg h, dif_neg h]
  | append_singleton gs g ih =>
    have hgs' : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or :=
      fun g' hg' => hgs g' (List.mem_append_left _ hg')
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hgs g (by simp)
    obtain ⟨iha, ihb⟩ := ih hgs'
    rw [List.map_append, List.map_singleton]
    set y : Fin n → Bool := fun i => (fx i).getD (x i)
    set V' := d3r1Fold false GateOp.eval (gs.map (d3sGate (d3sFv n fx))) (List.ofFn x)
    set V := d3r1Fold false GateOp.eval gs (List.ofFn y)
    set E' := d3r1Fold 0 d3r1DegOp (gs.map (d3sGate (d3sFv n fx))) init
    set E := d3r1Fold 0 d3r1DegOp gs init
    have hV'l : V'.length = n + gs.length := by simp [V', d3r1Fold_length]
    have hVl : V.length = n + gs.length := by simp [V, d3r1Fold_length]
    have hE'l : E'.length = E.length := by simp [E', E, d3r1Fold_length]
    refine ⟨fun t ht => ?_, fun t => ?_⟩
    · rw [d3r1Fold_snoc, d3r1Fold_snoc, getD_snoc, getD_snoc, hV'l, hVl]
      by_cases h1 : t < n + gs.length
      · rw [if_pos h1, if_pos h1]; exact iha t ht
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : t = n + gs.length
        · rw [if_pos h2, if_pos h2]
          apply d3s_gate_eval _ g hg
          · intro i _ b hb
            have hin : i < n := by
              unfold d3sFv at hb; split_ifs at hb with hh
              · exact hh
            have hlt : i < (List.ofFn y).length := by simp [hin]
            show V.getD i false = b
            rw [d3r1Fold_lt _ _ _ _ _ hlt, ofFn_getD, dif_pos hin]
            simp only [d3sFv, dif_pos hin] at hb
            simp [y, hb]
          · intro i _ hi; exact iha i hi
        · rw [if_neg h2, if_neg h2]
    · rw [d3r1Fold_snoc, d3r1Fold_snoc, getD_snoc, getD_snoc, hE'l]
      by_cases h1 : t < E.length
      · rw [if_pos h1, if_pos h1]; exact ihb t
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : t = E.length
        · rw [if_pos h2, if_pos h2]
          exact d3s_gate_deg _ g hg _ _ (fun i _ => ihb i)
        · rw [if_neg h2, if_neg h2]

/-- CARD 04 (substitution of fixed inputs). -/
theorem card04_subst : ∀ (n : ℕ) (marked : Finset ℕ) (C : Circuit) (D : ℕ) (fx : Fin n → Option Bool),
    Monotone2 C → 0 < C.size → HasLineDegree n marked C D →
    ∃ C' : Circuit, Monotone2 C' ∧ C'.size ≤ C.size ∧ HasLineDegree n marked C' D ∧
      ∀ x : Fin n → Bool, circuitFun n C' x = circuitFun n C (fun i => (fx i).getD (x i)) := by
  intro n marked C D fx hm hpos hdeg
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hm g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  cases hout : d3sFv n fx C.output with
  | some b =>
    have hon : C.output < n := by
      unfold d3sFv at hout; split_ifs at hout with hh
      · exact hh
    refine ⟨⟨[⟨if b then GateOp.and else GateOp.or, []⟩], n⟩, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      cases b <;> simp
    · show 1 ≤ C.gates.length; exact hpos
    · show (Circuit.lineDegrees _ n marked).getD n 0 ≤ D
      rw [d3r1_lineDegrees_eq]
      have h0 := d3r1Fold_gate 0 d3r1DegOp [⟨if b then GateOp.and else GateOp.or, []⟩]
        ((List.range n).map fun i => if i ∈ marked then 1 else 0) 0 (by simp)
      simp only [List.length_map, List.length_range, Nat.add_zero] at h0
      rw [h0]
      cases b <;> simp [d3r1DegOp]
    · intro x
      show (Circuit.wires _ (List.ofFn x)).getD n false =
        (C.wires (List.ofFn fun i => (fx i).getD (x i))).getD C.output false
      rw [d3r1_wires_eq, d3r1_wires_eq]
      have h0 := d3r1Fold_gate false GateOp.eval [⟨if b then GateOp.and else GateOp.or, []⟩]
        (List.ofFn x) 0 (by simp)
      simp only [List.length_ofFn, Nat.add_zero] at h0
      rw [h0, d3r1Fold_lt _ _ _ _ _ (by simp [hon]), ofFn_getD, dif_pos hon]
      simp only [d3sFv, dif_pos hon] at hout
      cases b <;> simp [hout, GateOp.eval]
  | none =>
    have hinv := fun x => d3s_inv n fx x ((List.range n).map fun i => if i ∈ marked then 1 else 0)
      C.gates hops
    refine ⟨⟨C.gates.map (d3sGate (d3sFv n fx)), C.output⟩, ?_, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
      exact d3s_gate_mono _ g0 (hm g0 hg0)
    · show (C.gates.map _).length ≤ C.gates.length; simp
    · show (Circuit.lineDegrees _ n marked).getD C.output 0 ≤ D
      rw [d3r1_lineDegrees_eq]
      exact le_trans ((hinv (fun _ => false)).2 C.output) hdeg
    · intro x
      show (Circuit.wires _ (List.ofFn x)).getD C.output false =
        (C.wires (List.ofFn fun i => (fx i).getD (x i))).getD C.output false
      rw [d3r1_wires_eq, d3r1_wires_eq]
      exact (hinv x).1 C.output hout

/-- Card 01 in the filed form: the output wire given as `n + k`. -/
theorem card01_rec : ∀ (n : ℕ) (C : Circuit) (a b k : ℕ), C.output = n + k →
    C.gates[k]? = some { op := GateOp.and, inputs := [a, b] } →
    ∀ z : Fin n → Bool, circuitFun n C z = true ↔
      (a < C.output ∧ circuitFun n ⟨C.gates, a⟩ z = true) ∧
      (b < C.output ∧ circuitFun n ⟨C.gates, b⟩ z = true) := by
  intro n C a b k hout hgate z
  have hle : n ≤ C.output := by omega
  have hg : C.gates[C.output - n]? = some { op := GateOp.and, inputs := [a, b] } := by
    rw [hout, Nat.add_sub_cancel_left]; exact hgate
  exact card01_out n C a b hle hg z

/-- Card 05 in the filed form: the two truncated differences named. -/
theorem card05_rec : ∀ (N q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (w : Fin N)
    (T : Finset (Fin N)),
    (∀ p p2 l l2 : Fin N, p ≠ p2 → l ≠ l2 → ¬ (I p l ∧ I p l2 ∧ I p2 l ∧ I p2 l2)) →
    (∀ l3 : Fin N, (Finset.univ.filter (fun p3 : Fin N => I p3 l3)).card = q) →
    (∀ p4 : Fin N, (Finset.univ.filter (fun l4 : Fin N => I p4 l4)).card ≤ q) →
    ∀ (M r : ℕ), M + 1 + q * T.card = N → r + 1 = q →
    M * r ≤ (Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ e.1 ∉ T ∧ ¬ I e.1 w ∧ e.2 ≠ w ∧ ¬ ∃ t ∈ T, I t e.2)).card := by
  intro N q I _ w T hI hl hp M r hM hr
  have h := card05_count N q I w T hI hl hp
  have e1 : N - 1 - q * T.card = M := by omega
  have e2 : q - 1 = r := by omega
  rw [e1, e2] at h
  exact h

end PEqualNP.MetaComplexity.Deg3
