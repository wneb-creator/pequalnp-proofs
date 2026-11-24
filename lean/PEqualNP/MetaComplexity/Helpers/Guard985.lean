import PEqualNP.MetaComplexity.Helpers.Deg3Subst
import PEqualNP.MetaComplexity.L963

/-!
# The symmetric guard lemma (L-meta-985), conjecture until checked

Two copies of one AND/OR circuit with some inputs fixed (the substitution of card 04 of the
line-degree-3 chain, gate by gate), the second copy placed after the first with its gate wires
renamed, then a tail of `2 J` gates: for each pair an AND of the two chosen wires, one read in
each copy, and an OR chain over the pairs. The result is fed to the checked count at line-degree
2 for a circuit below the incidence function.
-/

namespace PEqualNP.MetaComplexity.G985

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.LineDegTest
  PEqualNP.MetaComplexity.Deg3

/-! ## A renamed copy of a substituted circuit -/

/-- Renaming of wire indices for a copy placed `off` gates later: inputs stay, gate wires move. -/
def sh (n off i : ℕ) : ℕ := if i < n then i else i + off

/-- A gate with its reads renamed. -/
def shGate (n off : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sh n off)⟩

/-- The substituted copy, renamed. -/
def copyG (n off : ℕ) (fv : ℕ → Option Bool) (gs : List Gate) : List Gate :=
  gs.map (fun g => shGate n off (d3sGate fv g))

theorem copyG_snoc (n off : ℕ) (fv : ℕ → Option Bool) (gs : List Gate) (g : Gate) :
    copyG n off fv (gs ++ [g]) = copyG n off fv gs ++ [shGate n off (d3sGate fv g)] := by
  simp [copyG]

theorem copyG_length (n off : ℕ) (fv : ℕ → Option Bool) (gs : List Gate) :
    (copyG n off fv gs).length = gs.length := by simp [copyG]

theorem d3s_free (fv : ℕ → Option Bool) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ i ∈ (d3sGate fv g).inputs, fv i = none := by
  obtain ⟨op, ins⟩ := g
  simp only at hop
  rcases hop with rfl | rfl
  · simp only [d3sGate]
    split_ifs
    · simp
    · intro i hi
      exact Option.isNone_iff_eq_none.1 (List.mem_filter.1 hi).2
  · simp only [d3sGate]
    split_ifs
    · simp
    · intro i hi
      exact Option.isNone_iff_eq_none.1 (List.mem_filter.1 hi).2

theorem fv_lt {n : ℕ} {fx : Fin n → Option Bool} {i : ℕ} {b : Bool} (h : d3sFv n fx i = some b) :
    i < n := by
  unfold d3sFv at h
  split_ifs at h with hh
  exact hh

theorem fv_eq {n : ℕ} (fx : Fin n → Option Bool) {i : ℕ} (h : i < n) :
    d3sFv n fx i = fx ⟨i, h⟩ := by
  simp [d3sFv, h]

theorem fold_append {α : Type} (δ : α) (Φ : GateOp → List α → α) (gs hs : List Gate)
    (init : List α) : d3r1Fold δ Φ (gs ++ hs) init = d3r1Fold δ Φ hs (d3r1Fold δ Φ gs init) := by
  simp [d3r1Fold, List.foldl_append]

/-- Values of the renamed copy. -/
theorem copy_val (n off : ℕ) (fx : Fin n → Option Bool) (x : Fin n → Bool)
    (L : List Bool) (hLl : L.length = n + off) (hLx : ∀ i (h : i < n), L.getD i false = x ⟨i, h⟩)
    (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ t, n ≤ t →
      (d3r1Fold false GateOp.eval (copyG n off (d3sFv n fx) gs) L).getD (t + off) false =
      (d3r1Fold false GateOp.eval gs (List.ofFn (fun i => (fx i).getD (x i)))).getD t false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro t ht
    simp only [copyG, List.map_nil, d3r1Fold, List.foldl_nil]
    rw [List.getD_eq_default _ _ (by rw [hLl]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
  | append_singleton gs g ih =>
    have hgs' : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or :=
      fun g' hg' => hgs g' (List.mem_append_left _ hg')
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hgs g (by simp)
    have iha := ih hgs'
    intro t ht
    rw [copyG_snoc]
    set y : Fin n → Bool := fun i => (fx i).getD (x i)
    set fv := d3sFv n fx
    set V' := d3r1Fold false GateOp.eval (copyG n off fv gs) L
    set V := d3r1Fold false GateOp.eval gs (List.ofFn y)
    have hV'l : V'.length = n + off + gs.length := by
      simp [V', d3r1Fold_length, copyG_length, hLl]
    have hVl : V.length = n + gs.length := by simp [V, d3r1Fold_length]
    rw [d3r1Fold_snoc, d3r1Fold_snoc, getD_snoc, getD_snoc, hV'l, hVl]
    by_cases h1 : t < n + gs.length
    · rw [if_pos (by omega), if_pos h1]; exact iha t ht
    · rw [if_neg (by omega), if_neg h1]
      by_cases h2 : t = n + gs.length
      · rw [if_pos (by omega), if_pos h2]
        simp only [shGate, List.map_map]
        apply d3s_gate_eval fv g hg
        · intro i _ b hb
          have hin : i < n := fv_lt hb
          show V.getD i false = b
          rw [d3r1Fold_lt _ _ _ _ _ (by simp [hin]), ofFn_getD, dif_pos hin]
          have hb' : fx ⟨i, hin⟩ = some b := by rw [← fv_eq fx hin]; exact hb
          simp [y, hb']
        · intro i _ hi
          show V'.getD (sh n off i) false = V.getD i false
          by_cases hin : i < n
          · simp only [sh, if_pos hin]
            rw [d3r1Fold_lt _ _ _ _ _ (by omega), hLx i hin,
              d3r1Fold_lt _ _ _ _ _ (by simp [hin]), ofFn_getD, dif_pos hin]
            have hi' : fx ⟨i, hin⟩ = none := by rw [← fv_eq fx hin]; exact hi
            simp [y, hi']
          · simp only [sh, if_neg hin]
            exact iha i (by omega)
      · rw [if_neg (by omega), if_neg h2]

/-- Line-degrees of the renamed copy, against any starting degrees `D0` that bound the free
inputs. -/
theorem copy_deg (n off : ℕ) (fx : Fin n → Option Bool)
    (Ld D0 : List ℕ) (hLdl : Ld.length = n + off) (hD0l : D0.length = n)
    (hLd : ∀ i (h : i < n), fx ⟨i, h⟩ = none → Ld.getD i 0 ≤ D0.getD i 0)
    (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ t, n ≤ t → (d3r1Fold 0 d3r1DegOp (copyG n off (d3sFv n fx) gs) Ld).getD (t + off) 0 ≤
      (d3r1Fold 0 d3r1DegOp gs D0).getD t 0 := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro t ht
    simp only [copyG, List.map_nil, d3r1Fold, List.foldl_nil]
    rw [List.getD_eq_default _ _ (by rw [hLdl]; omega)]
    exact Nat.zero_le _
  | append_singleton gs g ih =>
    have hgs' : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or :=
      fun g' hg' => hgs g' (List.mem_append_left _ hg')
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hgs g (by simp)
    have ihb := ih hgs'
    intro t ht
    rw [copyG_snoc]
    set fv := d3sFv n fx
    set E' := d3r1Fold 0 d3r1DegOp (copyG n off fv gs) Ld
    set E := d3r1Fold 0 d3r1DegOp gs D0
    have hE'l : E'.length = n + off + gs.length := by
      simp [E', d3r1Fold_length, copyG_length, hLdl]
    have hEl : E.length = n + gs.length := by simp [E, d3r1Fold_length, hD0l]
    rw [d3r1Fold_snoc, d3r1Fold_snoc, getD_snoc, getD_snoc, hE'l, hEl]
    by_cases h1 : t < n + gs.length
    · rw [if_pos (by omega), if_pos h1]; exact ihb t ht
    · rw [if_neg (by omega), if_neg h1]
      by_cases h2 : t = n + gs.length
      · rw [if_pos (by omega), if_pos h2]
        simp only [shGate, List.map_map]
        have hfr := d3s_free fv g hg
        let d' : ℕ → ℕ := fun i => if fv i = none then E'.getD (sh n off i) 0 else 0
        have heq : (d3sGate fv g).inputs.map ((fun i => E'.getD i 0) ∘ sh n off) =
            (d3sGate fv g).inputs.map d' := by
          apply List.map_congr_left
          intro i hi
          simp [d', hfr i hi]
        rw [heq]
        apply d3s_gate_deg fv g hg d' (fun i => E.getD i 0)
        intro i _
        by_cases hfi : fv i = none
        · simp only [d', if_pos hfi]
          by_cases hin : i < n
          · simp only [sh, if_pos hin]
            rw [d3r1Fold_lt _ _ _ _ _ (by omega), d3r1Fold_lt _ _ _ _ _ (by omega)]
            apply hLd i hin
            rw [← fv_eq fx hin]; exact hfi
          · simp only [sh, if_neg hin]; exact ihb i (by omega)
        · simp only [d', if_neg hfi]; exact Nat.zero_le _
      · rw [if_neg (by omega), if_neg h2]

/-- Degrees from all-zero starting degrees stay zero. -/
theorem fold_zero (gs : List Gate) (Z : List ℕ) (hZ : ∀ i, Z.getD i 0 = 0) :
    ∀ t, (d3r1Fold 0 d3r1DegOp gs Z).getD t 0 = 0 := by
  induction gs using List.reverseRecOn with
  | nil => intro t; simpa [d3r1Fold] using hZ t
  | append_singleton gs g ih =>
    intro t
    rw [d3r1Fold_snoc, getD_snoc]
    split_ifs
    · exact ih t
    · have hm : g.inputs.map (fun i => (d3r1Fold 0 d3r1DegOp gs Z).getD i 0) =
          g.inputs.map (fun _ => 0) := List.map_congr_left (fun i _ => ih i)
      rw [hm]
      have h0 : ∀ l : List ℕ, (l.map (fun _ => (0 : ℕ))).sum = 0 ∧
          (l.map (fun _ => (0 : ℕ))).foldr max 0 = 0 := by
        intro l; induction l with
        | nil => simp
        | cons a l ih' =>
          simp only [List.map_cons, List.sum_cons, List.foldr_cons, ih'.1, ih'.2]
          simp
      unfold d3r1DegOp
      split_ifs
      · exact (h0 _).1
      · exact (h0 _).2
    · rfl

/-! ## References from the tail into the two copies -/

/-- Where the tail reads wire `t` of the copy placed `off` gates after the inputs: a fixed-true
input is no read at all (`none`), a fixed-false input or a missing wire is the index `F0` (beyond
every wire), a free input is itself, a gate wire is renamed. -/
def refW (n s off F0 : ℕ) (fx : Fin n → Option Bool) (t : ℕ) : Option ℕ :=
  if t < n then
    (match d3sFv n fx t with
     | some true => none
     | some false => some F0
     | none => some t)
  else if t < n + s then some (t + off) else some F0

/-- The value read through a reference (`true` for no read). -/
def rv (L : List Bool) : Option ℕ → Bool
  | none => true
  | some u => L.getD u false

/-- The degree read through a reference (`0` for no read). -/
def rd (L : List ℕ) : Option ℕ → ℕ
  | none => 0
  | some u => L.getD u 0

theorem ref_val (n s off F0 : ℕ) (fx : Fin n → Option Bool) (x : Fin n → Bool) (gs : List Gate)
    (hs : gs.length = s) (L : List Bool)
    (h1 : ∀ t, n ≤ t → t < n + s → L.getD (t + off) false =
      (d3r1Fold false GateOp.eval gs (List.ofFn (fun i => (fx i).getD (x i)))).getD t false)
    (h2 : ∀ i (h : i < n), L.getD i false = x ⟨i, h⟩) (h3 : L.getD F0 false = false) (t : ℕ) :
    rv L (refW n s off F0 fx t) =
      (d3r1Fold false GateOp.eval gs (List.ofFn (fun i => (fx i).getD (x i)))).getD t false := by
  unfold refW
  by_cases ht : t < n
  · rw [if_pos ht, d3r1Fold_lt _ _ _ _ _ (by simp [ht]), ofFn_getD, dif_pos ht, fv_eq fx ht]
    cases hf : fx ⟨t, ht⟩ with
    | none => simp only [rv, Option.getD]; exact h2 t ht
    | some b => cases b <;> simp only [rv, Option.getD] <;> exact h3
  · rw [if_neg ht]
    by_cases ht2 : t < n + s
    · rw [if_pos ht2]; exact h1 t (by omega) ht2
    · rw [if_neg ht2, d3r1Fold_ge _ _ _ _ _ (by simp [hs]; omega)]
      simp only [rv]; exact h3

theorem ref_deg (n s off F0 : ℕ) (fx : Fin n → Option Bool) (gs : List Gate)
    (hs : gs.length = s) (Ld D0 : List ℕ) (hD0l : D0.length = n)
    (h1 : ∀ t, n ≤ t → t < n + s → Ld.getD (t + off) 0 ≤ (d3r1Fold 0 d3r1DegOp gs D0).getD t 0)
    (h2 : ∀ i (h : i < n), fx ⟨i, h⟩ = none → Ld.getD i 0 ≤ D0.getD i 0)
    (h3 : Ld.getD F0 0 = 0) (t : ℕ) :
    rd Ld (refW n s off F0 fx t) ≤ (d3r1Fold 0 d3r1DegOp gs D0).getD t 0 := by
  unfold refW
  by_cases ht : t < n
  · rw [if_pos ht, d3r1Fold_lt _ _ _ _ _ (by rw [hD0l]; exact ht), fv_eq fx ht]
    cases hf : fx ⟨t, ht⟩ with
    | none => simpa [rd] using h2 t ht hf
    | some b => cases b <;> simp only [rd, h3] <;> exact Nat.zero_le _
  · rw [if_neg ht]
    by_cases ht2 : t < n + s
    · rw [if_pos ht2]; exact h1 t (by omega) ht2
    · rw [if_neg ht2]
      simp only [rd, h3]; exact Nat.zero_le _

/-! ## The tail: one AND per pair and an OR chain -/

/-- The two gates of pair `k`, after `b` wires: the AND of the two reads, then the OR with the
previous OR (with the always-false index `b + 2 J` for the first pair). -/
def tG (b J : ℕ) (rB rA : ℕ → Option ℕ) (k : ℕ) : List Gate :=
  [⟨GateOp.and, (rB k).toList ++ (rA k).toList⟩,
   ⟨GateOp.or, [b + 2 * k, if k = 0 then b + 2 * J else b + 2 * k - 1]⟩]

/-- The tail for the first `k` pairs. -/
def tail (b J : ℕ) (rB rA : ℕ → Option ℕ) (k : ℕ) : List Gate :=
  (List.range k).flatMap (tG b J rB rA)

theorem tail_succ (b J : ℕ) (rB rA : ℕ → Option ℕ) (k : ℕ) :
    tail b J rB rA (k + 1) = tail b J rB rA k ++ tG b J rB rA k := by
  simp [tail, List.range_succ, List.flatMap_append]

theorem tail_length (b J : ℕ) (rB rA : ℕ → Option ℕ) (k : ℕ) :
    (tail b J rB rA k).length = 2 * k := by
  induction k with
  | zero => simp [tail]
  | succ k ih => rw [tail_succ, List.length_append, ih]; simp [tG]; omega

theorem fold_two {α : Type} (δ : α) (Φ : GateOp → List α → α) (g1 g2 : Gate) (W : List α) :
    d3r1Fold δ Φ [g1, g2] W =
      (W ++ [Φ g1.op (g1.inputs.map fun i => W.getD i δ)]) ++
        [Φ g2.op (g2.inputs.map fun i => (W ++ [Φ g1.op (g1.inputs.map fun i => W.getD i δ)]).getD i δ)] := by
  rfl

theorem getD_snoc_ne {α : Type} (l : List α) (a d : α) (p : ℕ) (h : p ≠ l.length) :
    (l ++ [a]).getD p d = l.getD p d := by
  rw [getD_snoc]
  by_cases h1 : p < l.length
  · rw [if_pos h1]
  · rw [if_neg h1, if_neg h, List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  rw [getD_snoc, if_neg (lt_irrefl _), if_pos rfl]

theorem and_val (r1 r2 : Option ℕ) (L : List Bool) :
    GateOp.eval GateOp.and ((r1.toList ++ r2.toList).map fun i => L.getD i false) =
      (rv L r1 && rv L r2) := by
  cases r1 <;> cases r2 <;> simp [GateOp.eval, rv]

theorem and_deg (r1 r2 : Option ℕ) (L : List ℕ) :
    d3r1DegOp GateOp.and ((r1.toList ++ r2.toList).map fun i => L.getD i 0) = rd L r1 + rd L r2 := by
  cases r1 <;> cases r2 <;> simp [d3r1DegOp, rd]

theorem or_deg (a c : ℕ) : d3r1DegOp GateOp.or [a, c] = max a c := by
  simp [d3r1DegOp]

theorem tail_val (b J : ℕ) (rB rA : ℕ → Option ℕ) (P : List Bool) (hP : P.length = b)
    (vb va : ℕ → Bool)
    (hr : ∀ L : List Bool, (∀ i < b, L.getD i false = P.getD i false) →
      L.getD (b + 2 * J) false = false → ∀ k, k < J → rv L (rB k) = vb k ∧ rv L (rA k) = va k) :
    ∀ k, k ≤ J → (d3r1Fold false GateOp.eval (tail b J rB rA k) P).length = b + 2 * k ∧
      (∀ i < b, (d3r1Fold false GateOp.eval (tail b J rB rA k) P).getD i false = P.getD i false) ∧
      (d3r1Fold false GateOp.eval (tail b J rB rA k) P).getD
        (if k = 0 then b + 2 * J else b + 2 * k - 1) false =
        decide (∃ j < k, vb j = true ∧ va j = true) := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : d3r1Fold false GateOp.eval (tail b J rB rA 0) P = P := rfl
    rw [h0, if_pos rfl]
    refine ⟨by rw [hP]; rfl, fun i _ => rfl, ?_⟩
    rw [List.getD_eq_default _ _ (by omega)]
    simp
  | succ k ih =>
    intro hk
    obtain ⟨hl, hpre, hv⟩ := ih (by omega)
    rw [tail_succ, fold_append]
    set W := d3r1Fold false GateOp.eval (tail b J rB rA k) P
    have hW := hr W hpre (List.getD_eq_default _ _ (by omega)) k (by omega)
    unfold tG
    rw [fold_two]
    simp only [List.map_cons, List.map_nil]
    rw [and_val, hW.1, hW.2]
    refine ⟨by simp [hl]; omega, fun i hi => ?_, ?_⟩
    · rw [getD_snoc_ne _ _ _ _ (by simp [hl]; omega), getD_snoc_ne _ _ _ _ (by omega), hpre i hi]
    · rw [if_neg (Nat.succ_ne_zero k)]
      have hlen : (W ++ [vb k && va k]).length = b + 2 * (k + 1) - 1 := by simp [hl]; omega
      rw [← hlen, getD_snoc_eq]
      rw [show b + 2 * k = W.length by omega, getD_snoc_eq, getD_snoc_ne _ _ _ _ (by split_ifs <;> omega)]
      rw [show W.length = b + 2 * k by omega, hv]
      have e : (∃ j < k + 1, vb j = true ∧ va j = true) ↔
          (vb k = true ∧ va k = true) ∨ ∃ j < k, vb j = true ∧ va j = true := by
        constructor
        · rintro ⟨j, hj, h⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact Or.inr ⟨j, hj, h⟩
          · exact Or.inl h
        · rintro (h | ⟨j, hj, h⟩)
          · exact ⟨k, by omega, h⟩
          · exact ⟨j, by omega, h⟩
      simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact e.symm

theorem tail_deg (b J : ℕ) (rB rA : ℕ → Option ℕ) (Pd : List ℕ) (hP : Pd.length = b)
    (hr : ∀ L : List ℕ, (∀ i < b, L.getD i 0 = Pd.getD i 0) → L.getD (b + 2 * J) 0 = 0 →
      ∀ k, k < J → rd L (rB k) + rd L (rA k) ≤ 2) :
    ∀ k, k ≤ J → (d3r1Fold 0 d3r1DegOp (tail b J rB rA k) Pd).length = b + 2 * k ∧
      (∀ i < b, (d3r1Fold 0 d3r1DegOp (tail b J rB rA k) Pd).getD i 0 = Pd.getD i 0) ∧
      (∀ i, b ≤ i → (d3r1Fold 0 d3r1DegOp (tail b J rB rA k) Pd).getD i 0 ≤ 2) := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : d3r1Fold 0 d3r1DegOp (tail b J rB rA 0) Pd = Pd := rfl
    rw [h0]
    refine ⟨by rw [hP]; rfl, fun i _ => rfl, fun i hi => ?_⟩
    rw [List.getD_eq_default _ _ (by omega)]
    omega
  | succ k ih =>
    intro hk
    obtain ⟨hl, hpre, hv⟩ := ih (by omega)
    rw [tail_succ, fold_append]
    set W := d3r1Fold 0 d3r1DegOp (tail b J rB rA k) Pd
    have hW := hr W hpre (List.getD_eq_default _ _ (by omega)) k (by omega)
    unfold tG
    rw [fold_two]
    simp only [List.map_cons, List.map_nil]
    rw [and_deg]
    set dT := rd W (rB k) + rd W (rA k)
    have h1 : ∀ i, b ≤ i → (W ++ [dT]).getD i 0 ≤ 2 := by
      intro i hi
      rw [getD_snoc]
      split_ifs
      · exact hv i hi
      · exact hW
      · omega
    refine ⟨by simp [hl]; omega, fun i hi => ?_, fun i hi => ?_⟩
    · rw [getD_snoc_ne _ _ _ _ (by simp [hl]; omega), getD_snoc_ne _ _ _ _ (by omega), hpre i hi]
    · rw [getD_snoc]
      by_cases hi1 : i < (W ++ [dT]).length
      · rw [if_pos hi1]; exact h1 i hi
      · rw [if_neg hi1]
        by_cases hi2 : i = (W ++ [dT]).length
        · rw [if_pos hi2, or_deg]
          refine max_le (h1 _ (by omega)) (h1 _ ?_)
          by_cases hk0 : k = 0
          · rw [if_pos hk0]; omega
          · rw [if_neg hk0]; omega
        · rw [if_neg hi2]; omega

/-! ## The guarded circuit -/

/-- The tail's read of the first factor of pair `k` (in the first copy). -/
def rB (n s J : ℕ) (fxB : Fin n → Option Bool) (fb : ℕ → ℕ) (k : ℕ) : Option ℕ :=
  refW n s 0 (n + 2 * s + 2 * J) fxB (fb k)

/-- The tail's read of the second factor of pair `k` (in the second copy). -/
def rA (n s J : ℕ) (fxA : Fin n → Option Bool) (fa : ℕ → ℕ) (k : ℕ) : Option ℕ :=
  refW n s s (n + 2 * s + 2 * J) fxA (fa k)

/-- The guarded circuit: the copy with `fxB` fixed, the copy with `fxA` fixed, the tail. -/
def star (n J : ℕ) (fxB fxA : Fin n → Option Bool) (fa fb : ℕ → ℕ) (gs : List Gate) : Circuit :=
  ⟨copyG n 0 (d3sFv n fxB) gs ++ copyG n gs.length (d3sFv n fxA) gs ++
    tail (n + 2 * gs.length) J (rB n gs.length J fxB fb) (rA n gs.length J fxA fa) J,
   n + 2 * gs.length + 2 * J - 1⟩

theorem star_size (n J : ℕ) (fxB fxA : Fin n → Option Bool) (fa fb : ℕ → ℕ) (gs : List Gate) :
    (star n J fxB fxA fa fb gs).size = 2 * gs.length + 2 * J := by
  simp only [star, Circuit.size, List.length_append, copyG_length, tail_length]
  omega

theorem star_mono (n J : ℕ) (fxB fxA : Fin n → Option Bool) (fa fb : ℕ → ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    Monotone2 (star n J fxB fxA fa fb gs) := by
  intro g hg
  simp only [star, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    have := d3s_gate_mono (d3sFv n fxB) g0 (hgs g0 hg0)
    simpa [shGate] using this
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    have := d3s_gate_mono (d3sFv n fxA) g0 (hgs g0 hg0)
    simpa [shGate] using this
  · obtain ⟨k, _, hk⟩ := List.mem_flatMap.1 hg
    simp only [tG, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · refine ⟨by simp, ?_⟩
      simp only [List.length_append]
      have h1 : ∀ r : Option ℕ, r.toList.length ≤ 1 := fun r => by cases r <;> simp
      have := h1 (rB n gs.length J fxB fb k)
      have := h1 (rA n gs.length J fxA fa k)
      omega
    · exact ⟨by simp, by simp⟩

theorem star_val (n J : ℕ) (fxB fxA : Fin n → Option Bool) (fa fb : ℕ → ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (hJ : 1 ≤ J) (x : Fin n → Bool) :
    circuitFun n (star n J fxB fxA fa fb gs) x = decide (∃ j < J,
      (d3r1Fold false GateOp.eval gs (List.ofFn (fun i => (fxB i).getD (x i)))).getD (fb j) false
        = true ∧
      (d3r1Fold false GateOp.eval gs (List.ofFn (fun i => (fxA i).getD (x i)))).getD (fa j) false
        = true) := by
  unfold circuitFun Circuit.eval
  rw [d3r1_wires_eq]
  simp only [star]
  rw [fold_append, fold_append]
  set s := gs.length with hs
  set PB := d3r1Fold false GateOp.eval (copyG n 0 (d3sFv n fxB) gs) (List.ofFn x)
  set PA := d3r1Fold false GateOp.eval (copyG n s (d3sFv n fxA) gs) PB
  have hPB : PB.length = n + s := by simp [PB, d3r1Fold_length, copyG_length, s]
  have hPA : PA.length = n + 2 * s := by
    simp only [PA, d3r1Fold_length, copyG_length, hPB]; omega
  have hPBx : ∀ i (h : i < n), PB.getD i false = x ⟨i, h⟩ := by
    intro i h; rw [d3r1Fold_lt _ _ _ _ _ (by simp [h]), ofFn_getD, dif_pos h]
  have hPAx : ∀ i (h : i < n), PA.getD i false = x ⟨i, h⟩ := by
    intro i h; rw [d3r1Fold_lt _ _ _ _ _ (by omega), hPBx]
  have hcB := copy_val n 0 fxB x (List.ofFn x) (by simp)
    (fun i h => by rw [ofFn_getD, dif_pos h]) gs hgs
  have hcA := copy_val n s fxA x PB hPB hPBx gs hgs
  have ht := tail_val (n + 2 * s) J (rB n s J fxB fb) (rA n s J fxA fa) PA hPA
    (fun k => (d3r1Fold false GateOp.eval gs
      (List.ofFn (fun i => (fxB i).getD (x i)))).getD (fb k) false)
    (fun k => (d3r1Fold false GateOp.eval gs
      (List.ofFn (fun i => (fxA i).getD (x i)))).getD (fa k) false) ?_ J le_rfl
  · rw [if_neg (by omega)] at ht
    exact ht.2.2
  · intro L hL hF k _
    constructor
    · refine ref_val n s 0 _ fxB x gs rfl L (fun t ht1 ht2 => ?_) (fun i h => ?_) hF (fb k)
      · rw [hL _ (by omega), d3r1Fold_lt _ _ _ _ _ (by omega)]
        exact hcB t ht1
      · rw [hL _ (by omega)]; exact hPAx i h
    · refine ref_val n s s _ fxA x gs rfl L (fun t ht1 ht2 => ?_) (fun i h => ?_) hF (fa k)
      · rw [hL _ (by omega)]
        exact hcA t ht1
      · rw [hL _ (by omega)]; exact hPAx i h

theorem star_deg (n J : ℕ) (marked : Finset ℕ) (fxB fxA : Fin n → Option Bool) (fa fb : ℕ → ℕ)
    (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (hJ : 1 ≤ J)
    (hB : ∀ i (h : i < n), fxB ⟨i, h⟩ = none → i ∉ marked)
    (hA : ∀ k < J, (d3r1Fold 0 d3r1DegOp gs
      ((List.range n).map fun i => if i ∈ marked then 1 else 0)).getD (fa k) 0 ≤ 2) :
    HasLineDegree n marked (star n J fxB fxA fa fb gs) 2 := by
  unfold HasLineDegree Circuit.lineDeg
  rw [d3r1_lineDegrees_eq]
  simp only [star]
  rw [fold_append, fold_append]
  set s := gs.length with hs
  set init := (List.range n).map fun i => if i ∈ marked then 1 else 0
  have hinit : init.length = n := by simp [init]
  have hinitg : ∀ i (h : i < n), init.getD i 0 = if i ∈ marked then 1 else 0 := by
    intro i h; simp [init, h]
  set Z := List.replicate n (0 : ℕ)
  have hZl : Z.length = n := by simp [Z]
  have hZ : ∀ i, Z.getD i 0 = 0 := by
    intro i; rw [List.getD_eq_getElem?_getD]; simp only [Z, List.getElem?_replicate]
    split_ifs <;> rfl
  have hB0 : ∀ i (h : i < n), fxB ⟨i, h⟩ = none → init.getD i 0 = 0 := by
    intro i h hf; rw [hinitg i h, if_neg (hB i h hf)]
  set PdB := d3r1Fold 0 d3r1DegOp (copyG n 0 (d3sFv n fxB) gs) init
  set PdA := d3r1Fold 0 d3r1DegOp (copyG n s (d3sFv n fxA) gs) PdB
  have hPB : PdB.length = n + s := by simp [PdB, d3r1Fold_length, copyG_length, s, hinit]
  have hPA : PdA.length = n + 2 * s := by
    simp only [PdA, d3r1Fold_length, copyG_length, hPB]; omega
  have hPBi : ∀ i, i < n → PdB.getD i 0 = init.getD i 0 := by
    intro i h; rw [d3r1Fold_lt _ _ _ _ _ (by omega)]
  have hPAi : ∀ i, i < n → PdA.getD i 0 = init.getD i 0 := by
    intro i h; rw [d3r1Fold_lt _ _ _ _ _ (by omega), hPBi i h]
  have hcB := copy_deg n 0 fxB init Z (by simp [hinit]) hZl
    (fun i h hf => by rw [hB0 i h hf]; exact Nat.zero_le _) gs hgs
  have hcA := copy_deg n s fxA PdB init hPB hinit
    (fun i h _ => le_of_eq (hPBi i h)) gs hgs
  have ht := tail_deg (n + 2 * s) J (rB n s J fxB fb) (rA n s J fxA fa) PdA hPA ?_ J le_rfl
  · exact ht.2.2 _ (by omega)
  · intro L hL hF k hk
    have e1 := ref_deg n s 0 _ fxB gs rfl L Z hZl (fun t ht1 ht2 => ?_) (fun i h hf => ?_) hF (fb k)
    · have e2 := ref_deg n s s _ fxA gs rfl L init hinit (fun t ht1 ht2 => ?_)
        (fun i h _ => ?_) hF (fa k)
      · rw [fold_zero gs Z hZ] at e1
        have := hA k hk
        simp only [rB, rA]
        omega
      · rw [hL _ (by omega)]
        exact hcA t ht1
      · rw [hL _ (by omega), hPAi i h]
    · rw [hL _ (by omega), d3r1Fold_lt _ _ _ _ _ (by omega)]
      exact hcB t ht1
    · rw [hL _ (by omega), hPAi i h, hB0 i h hf]; exact Nat.zero_le _

/-! ## The guard lemma -/

/-- The fixing of the first copy: points on a line of `Wz` off, every line fixed to `Wz`. -/
def fxB (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Wz : Finset (Fin N)) :
    Fin (N + N) → Option Bool :=
  Fin.addCases (fun p => if ∀ uu ∈ Wz, ¬ I p uu then none else some false)
    (fun l => some (decide (l ∈ Wz)))

/-- The fixing of the second copy: points on a line of `Wz` off, the lines of `Wz` off. -/
def fxA (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Wz : Finset (Fin N)) :
    Fin (N + N) → Option Bool :=
  Fin.addCases (fun p => if ∀ uu ∈ Wz, ¬ I p uu then none else some false)
    (fun l => if l ∈ Wz then some false else none)

theorem cn_ne {N : ℕ} (q w : Fin N) : Fin.castAdd N q ≠ Fin.natAdd N w := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
  omega

theorem ca_inj {N : ℕ} {q p : Fin N} (h : Fin.castAdd N q = Fin.castAdd N p) : q = p := by
  have := congrArg Fin.val h
  simp only [Fin.coe_castAdd] at this
  exact Fin.ext this

theorem na_inj {N : ℕ} {q p : Fin N} (h : Fin.natAdd N q = Fin.natAdd N p) : q = p := by
  have := congrArg Fin.val h
  simp only [Fin.coe_natAdd] at this
  exact Fin.ext (by omega)

theorem inB_eq {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (Wz : Finset (Fin N))
    (p w : Fin N) (hg : ∀ uu ∈ Wz, ¬ I p uu) :
    (fun i => (fxB N I Wz i).getD (decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N w))) =
      (fun vv : Fin (N + N) => if vv = Fin.castAdd N p then true else
        decide (∃ ww ∈ Wz, vv = Fin.natAdd N ww)) := by
  funext vv
  induction vv using Fin.addCases with
  | left q =>
    simp only [fxB, Fin.addCases_left]
    by_cases hq : q = p
    · subst hq
      rw [if_pos hg, if_pos rfl]
      simp
    · have h1 : Fin.castAdd N q ≠ Fin.castAdd N p := fun h => hq (ca_inj h)
      have h2 := cn_ne q w
      rw [if_neg h1]
      have hx : decide (Fin.castAdd N q = Fin.castAdd N p ∨ Fin.castAdd N q = Fin.natAdd N w) =
          false := decide_eq_false (fun h => h.elim h1 h2)
      have hy : decide (∃ ww ∈ Wz, Fin.castAdd N q = Fin.natAdd N ww) = false :=
        decide_eq_false (fun ⟨ww, _, h⟩ => cn_ne q ww h)
      rw [hx, hy]
      split_ifs <;> rfl
  | right l =>
    simp only [fxB, Fin.addCases_right, Option.getD_some]
    have h1 : Fin.natAdd N l ≠ Fin.castAdd N p := fun h => cn_ne p l h.symm
    rw [if_neg h1]
    exact decide_eq_decide.2 ⟨fun h => ⟨l, h, rfl⟩, fun ⟨ww, hw, h⟩ => (na_inj h) ▸ hw⟩

theorem inA_eq {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (Wz : Finset (Fin N))
    (p w : Fin N) (hg : ∀ uu ∈ Wz, ¬ I p uu) (hw : w ∉ Wz) :
    (fun i => (fxA N I Wz i).getD (decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N w))) =
      (fun vq : Fin (N + N) => if vq = Fin.castAdd N p then true else
        if vq = Fin.natAdd N w then true else false) := by
  funext vv
  induction vv using Fin.addCases with
  | left q =>
    simp only [fxA, Fin.addCases_left]
    by_cases hq : q = p
    · subst hq
      rw [if_pos hg, if_pos rfl]
      simp
    · have h1 : Fin.castAdd N q ≠ Fin.castAdd N p := fun h => hq (ca_inj h)
      have h2 := cn_ne q w
      rw [if_neg h1, if_neg h2]
      have hx : decide (Fin.castAdd N q = Fin.castAdd N p ∨ Fin.castAdd N q = Fin.natAdd N w) =
          false := decide_eq_false (fun h => h.elim h1 h2)
      rw [hx]
      split_ifs <;> rfl
  | right l =>
    simp only [fxA, Fin.addCases_right]
    have h1 : Fin.natAdd N l ≠ Fin.castAdd N p := fun h => cn_ne p l h.symm
    rw [if_neg h1]
    by_cases hl : l = w
    · subst hl
      rw [if_neg hw, if_pos rfl]
      simp
    · have h2 : Fin.natAdd N l ≠ Fin.natAdd N w := fun h => hl (na_inj h)
      rw [if_neg h2]
      have hx : decide (Fin.natAdd N l = Fin.castAdd N p ∨ Fin.natAdd N l = Fin.natAdd N w) =
          false := decide_eq_false (fun h => h.elim h1 h2)
      rw [hx]
      split_ifs <;> rfl

theorem guard : ∀ (N Jn : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit) (fa fb : Fin Jn → ℕ) (Wz : Finset (Fin N)), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → (∀ jd : Fin Jn, (Ckt.lineDegrees (N + N) (Finset.Ico N (N + N))).getD (fa jd) 0 ≤ 2) → (∀ (jb : Fin Jn) (zz : Fin (N + N) → Bool), (Ckt.wires (List.ofFn zz)).getD (fa jb) false = true → (Ckt.wires (List.ofFn zz)).getD (fb jb) false = true → ∃ (pa lb : Fin N), I pa lb ∧ zz (Fin.castAdd N pa) = true ∧ zz (Fin.natAdd N lb) = true) → (Finset.univ.filter (fun e2 : Fin N × Fin N => I e2.1 e2.2 ∧ e2.2 ∉ Wz ∧ (∀ uu ∈ Wz, ¬ I e2.1 uu) ∧ ∃ jc : Fin Jn, (Ckt.wires (List.ofFn (fun vv : Fin (N + N) => if vv = Fin.castAdd N e2.1 then true else decide (∃ ww ∈ Wz, vv = Fin.natAdd N ww)))).getD (fb jc) false = true ∧ (Ckt.wires (List.ofFn (fun vq : Fin (N + N) => if vq = Fin.castAdd N e2.1 then true else if vq = Fin.natAdd N e2.2 then true else false))).getD (fa jc) false = true)).card ≤ 48 * (2 * Ckt.size + 2 * Jn) + 2 * N := by
  intro N Jn I _ Ckt fa fb Wz hI hmono hdeg hsnd
  rcases Nat.eq_zero_or_pos Jn with hJ0 | hJ
  · subst hJ0
    rw [Finset.card_eq_zero.2 ?_]
    · exact Nat.zero_le _
    · apply Finset.filter_false_of_mem
      intro e _ h
      obtain ⟨_, _, _, jc, _⟩ := h
      exact jc.elim0
  · classical
    let fa' : ℕ → ℕ := fun k => if h : k < Jn then fa ⟨k, h⟩ else 0
    let fb' : ℕ → ℕ := fun k => if h : k < Jn then fb ⟨k, h⟩ else 0
    have hfa : ∀ k (h : k < Jn), fa' k = fa ⟨k, h⟩ := fun k h => dif_pos h
    have hfb : ∀ k (h : k < Jn), fb' k = fb ⟨k, h⟩ := fun k h => dif_pos h
    let A := star (N + N) Jn (fxB N I Wz) (fxA N I Wz) fa' fb' Ckt.gates
    let I' : Fin N → Fin N → Prop := fun p l => I p l ∧ (∀ uu ∈ Wz, ¬ I p uu) ∧ l ∉ Wz
    have hops : ∀ g ∈ Ckt.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      have := (hmono g hg).1
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    have hIM : IsMonotoneCircuit Ckt := hops
    have hI' : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
        ¬ (I' p l ∧ I' p l' ∧ I' p' l ∧ I' p' l') := by
      intro p p' l l' hp hl h
      exact hI p p' l l' hp hl ⟨h.1.1, h.2.1.1, h.2.2.1.1, h.2.2.2.1⟩
    have hmA : Monotone2 A := star_mono _ _ _ _ _ _ _ hmono
    have hdA : HasLineDegree (N + N) (Finset.Ico N (N + N)) A 2 := by
      apply star_deg _ _ _ _ _ _ _ _ hops hJ
      · intro i h hf hm
        have hiN : N ≤ i := (Finset.mem_Ico.1 hm).1
        have he : (⟨i, h⟩ : Fin (N + N)) = Fin.natAdd N ⟨i - N, by omega⟩ :=
          Fin.ext (by simp; omega)
        rw [he, fxB, Fin.addCases_right] at hf
        exact absurd hf (by simp)
      · intro k hk
        have := hdeg ⟨k, hk⟩
        rw [d3r1_lineDegrees_eq] at this
        rw [hfa k hk]
        exact this
    have hsA : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) A z = true →
        ∃ p l : Fin N, I' p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
      intro z hz
      rw [star_val _ _ _ _ _ _ _ hops hJ] at hz
      obtain ⟨j, hj, h1, h2⟩ := of_decide_eq_true hz
      let Y : Fin (N + N) → Bool := fun v =>
        (fxB N I Wz v).getD (z v) || (fxA N I Wz v).getD (z v)
      have m1 := card02_mono (N + N) Ckt (fb' j) hIM (fun i => (fxB N I Wz i).getD (z i)) Y
        (fun i hi => by
          show ((fxB N I Wz i).getD (z i) || (fxA N I Wz i).getD (z i)) = true
          rw [hi, Bool.true_or]) (by rw [d3r1_wires_eq]; exact h1)
      have m2 := card02_mono (N + N) Ckt (fa' j) hIM (fun i => (fxA N I Wz i).getD (z i)) Y
        (fun i hi => by
          show ((fxB N I Wz i).getD (z i) || (fxA N I Wz i).getD (z i)) = true
          rw [hi, Bool.or_true]) (by rw [d3r1_wires_eq]; exact h2)
      rw [hfb j hj] at m1
      rw [hfa j hj] at m2
      obtain ⟨pa, lb, hIpl, hYp, hYl⟩ := hsnd ⟨j, hj⟩ Y m2 m1
      have hgp : ∀ uu ∈ Wz, ¬ I pa uu := by
        by_contra hg
        simp only [Y, fxB, fxA, Fin.addCases_left, if_neg hg] at hYp
        simp at hYp
      have hzp : z (Fin.castAdd N pa) = true := by
        simp only [Y, fxB, fxA, Fin.addCases_left, if_pos hgp, Option.getD_none,
          Bool.or_self] at hYp
        exact hYp
      have hlb : lb ∉ Wz := fun hl => hgp lb hl hIpl
      have hzl : z (Fin.natAdd N lb) = true := by
        simp only [Y, fxB, fxA, Fin.addCases_right, if_neg hlb, Option.getD_none,
          Option.getD_some, decide_eq_false hlb, Bool.false_or] at hYl
        exact hYl
      exact ⟨pa, lb, ⟨hIpl, hgp, hlb⟩, hzp, hzl⟩
    have hcount := PEqualNP.MetaComplexity.L963 N I' A hI' hmA hdA hsA
    rw [star_size] at hcount
    refine le_trans (Finset.card_le_card ?_) hcount
    intro e he
    obtain ⟨hIe, hw, hgp, jc, hb, ha⟩ := (Finset.mem_filter.1 he).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hIe, hgp, hw⟩, ?_⟩
    rw [star_val _ _ _ _ _ _ _ hops hJ]
    apply decide_eq_true
    refine ⟨jc.val, jc.isLt, ?_, ?_⟩
    · rw [hfb _ jc.isLt, inB_eq I Wz e.1 e.2 hgp, ← d3r1_wires_eq]
      exact hb
    · rw [hfa _ jc.isLt, inA_eq I Wz e.1 e.2 hgp hw, ← d3r1_wires_eq]
      exact ha

end PEqualNP.MetaComplexity.G985
