import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3787_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

lemma foldl_length (gs : List Gate) : ∀ W : List Bool,
    (gs.foldl stp W).length = W.length + gs.length := by
  induction gs with
  | nil => intro W; simp
  | cons g gs ih =>
    intro W
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp [stp]
    omega

lemma getD_snoc_eq (W : List Bool) (v : Bool) : (W ++ [v]).getD W.length false = v := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (h : i < m) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

def rho (a b : ℕ) (σ : ℕ → ℕ) (i : ℕ) : ℕ := if i < a then σ i else i - a + b

def relG (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

lemma getD_rho (ID Inew rest : List Bool) (σ : ℕ → ℕ)
    (hσ : ∀ i, i < ID.length → σ i < Inew.length ∧ ID.getD i false = Inew.getD (σ i) false)
    (i : ℕ) :
    (Inew ++ rest).getD (rho ID.length Inew.length σ i) false = (ID ++ rest).getD i false := by
  unfold rho
  by_cases h : i < ID.length
  · rw [if_pos h, List.getD_append _ _ _ _ (hσ i h).1, List.getD_append _ _ _ _ h]
    exact (hσ i h).2.symm
  · rw [if_neg h]
    have h1 : ID.length ≤ i := Nat.le_of_not_lt h
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ h1]
    congr 1
    omega

lemma relabel_spec (ID Inew : List Bool) (σ : ℕ → ℕ)
    (hσ : ∀ i, i < ID.length → σ i < Inew.length ∧ ID.getD i false = Inew.getD (σ i) false)
    (gs : List Gate) :
    ∀ rest : List Bool, ∃ rest' : List Bool,
      (gs.map (relG (rho ID.length Inew.length σ))).foldl stp (Inew ++ rest) = Inew ++ rest' ∧
        gs.foldl stp (ID ++ rest) = ID ++ rest' := by
  induction gs with
  | nil => intro rest; exact ⟨rest, rfl, rfl⟩
  | cons g gs ih =>
    intro rest
    obtain ⟨rest', h1, h2⟩ :=
      ih (rest ++ [g.op.eval (g.inputs.map fun i => (ID ++ rest).getD i false)])
    refine ⟨rest', ?_, ?_⟩
    · rw [← h1]
      simp only [List.map_cons, List.foldl_cons]
      congr 1
      simp only [stp, relG, List.map_map]
      have : ((fun i => (Inew ++ rest).getD i false) ∘ rho ID.length Inew.length σ)
          = fun i => (ID ++ rest).getD i false := by
        funext i
        exact getD_rho ID Inew rest σ hσ i
      rw [this]
      simp
    · rw [← h2]
      simp only [List.foldl_cons]
      congr 1
      simp [stp]


def addTerms : List (ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ → ℕ → List Gate
  | [], _, _ => []
  | (c, a, b, d, e) :: ts, L, acc =>
    ⟨GateOp.or, [a, b]⟩ :: ⟨GateOp.or, [d, e]⟩ ::
      ⟨GateOp.or, [L, L + 1]⟩ :: ⟨GateOp.and, [c, L + 2]⟩ ::
      ⟨GateOp.or, [acc, L + 3]⟩ :: addTerms ts (L + 5) (L + 4)

def finalAcc : List (ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ → ℕ → ℕ
  | [], _, acc => acc
  | _ :: ts, L, _ => finalAcc ts (L + 5) (L + 4)

lemma addTerms_length : ∀ (ts : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (L acc : ℕ),
    (addTerms ts L acc).length = 5 * ts.length := by
  intro ts
  induction ts with
  | nil => intro L acc; simp [addTerms]
  | cons τ ts ih =>
    intro L acc
    obtain ⟨c, a, b, d, e⟩ := τ
    simp only [addTerms, List.length_cons, ih]
    omega

lemma addTerms_ok : ∀ (ts : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (L acc : ℕ),
    ∀ g ∈ addTerms ts L acc,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro ts
  induction ts with
  | nil => intro L acc g hg; simp [addTerms] at hg
  | cons τ ts ih =>
    intro L acc g hg
    obtain ⟨c, a, b, d, e⟩ := τ
    simp only [addTerms, List.mem_cons] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | hg
    · simp
    · simp
    · simp
    · simp
    · simp
    · exact ih _ _ g hg

def termValue (W : List Bool) (τ : ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  W.getD τ.1 false &&
    ((W.getD τ.2.1 false || W.getD τ.2.2.1 false) ||
      (W.getD τ.2.2.2.1 false || W.getD τ.2.2.2.2 false))

def termBound (W : List Bool) (τ : ℕ × ℕ × ℕ × ℕ × ℕ) : Prop :=
  τ.1 < W.length ∧ τ.2.1 < W.length ∧ τ.2.2.1 < W.length ∧
    τ.2.2.2.1 < W.length ∧ τ.2.2.2.2 < W.length

lemma addTerms_spec : ∀ (ts : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (W : List Bool) (acc : ℕ),
    acc < W.length → (∀ τ ∈ ts, termBound W τ) →
    (((addTerms ts W.length acc).foldl stp W).getD (finalAcc ts W.length acc) false = true ↔
      W.getD acc false = true ∨ ∃ τ ∈ ts, termValue W τ = true) := by
  intro ts
  induction ts with
  | nil => intro W acc _ _; simp [addTerms, finalAcc]
  | cons τ ts ih =>
    intro W acc hacc hts
    obtain ⟨c, a, b, d, e⟩ := τ
    obtain ⟨hc, ha, hb, hd, he⟩ := hts (c, a, b, d, e) (by simp)
    dsimp only at hc ha hb hd he
    let v1 := W.getD a false || W.getD b false
    let v2 := W.getD d false || W.getD e false
    let v3 := v1 || v2
    let v4 := W.getD c false && v3
    let v5 := W.getD acc false || v4
    have s1 : stp W ⟨GateOp.or, [a, b]⟩ = W ++ [v1] := by
      simp [stp, GateOp.eval, v1]
    have s2 : stp (W ++ [v1]) ⟨GateOp.or, [d, e]⟩ = W ++ [v1] ++ [v2] := by
      simp only [stp, List.map_cons, List.map_nil]
      rw [List.getD_append _ _ _ _ hd, List.getD_append _ _ _ _ he]
      simp [GateOp.eval, v2]
    have hlen1 : (W ++ [v1]).length = W.length + 1 := by simp
    have hlen2 : (W ++ [v1] ++ [v2]).length = W.length + 2 := by simp
    have hlen3 : (W ++ [v1] ++ [v2] ++ [v3]).length = W.length + 3 := by simp
    have hlen4 : (W ++ [v1] ++ [v2] ++ [v3] ++ [v4]).length = W.length + 4 := by simp
    have s3 : stp (W ++ [v1] ++ [v2]) ⟨GateOp.or, [W.length, W.length + 1]⟩
        = W ++ [v1] ++ [v2] ++ [v3] := by
      simp only [stp, List.map_cons, List.map_nil]
      rw [List.getD_append (W ++ [v1]) [v2] false W.length (by simp),
        getD_snoc_eq, ← hlen1, getD_snoc_eq]
      simp [GateOp.eval, v3]
    have s4 : stp (W ++ [v1] ++ [v2] ++ [v3]) ⟨GateOp.and, [c, W.length + 2]⟩
        = W ++ [v1] ++ [v2] ++ [v3] ++ [v4] := by
      simp only [stp, List.map_cons, List.map_nil]
      rw [List.getD_append (W ++ [v1] ++ [v2]) [v3] false c (by simp; omega),
        List.getD_append (W ++ [v1]) [v2] false c (by simp; omega),
        List.getD_append W [v1] false c hc,
        ← hlen2, getD_snoc_eq]
      simp [GateOp.eval, v4]
    have s5 : stp (W ++ [v1] ++ [v2] ++ [v3] ++ [v4])
        ⟨GateOp.or, [acc, W.length + 3]⟩
        = W ++ [v1] ++ [v2] ++ [v3] ++ [v4] ++ [v5] := by
      simp only [stp, List.map_cons, List.map_nil]
      rw [List.getD_append (W ++ [v1] ++ [v2] ++ [v3]) [v4] false acc (by simp; omega),
        List.getD_append (W ++ [v1] ++ [v2]) [v3] false acc (by simp; omega),
        List.getD_append (W ++ [v1]) [v2] false acc (by simp; omega),
        List.getD_append W [v1] false acc hacc,
        ← hlen3, getD_snoc_eq]
      simp [GateOp.eval, v5]
    simp only [addTerms, finalAcc, List.foldl_cons]
    rw [s1, s2, s3, s4, s5]
    generalize hW' : W ++ [v1] ++ [v2] ++ [v3] ++ [v4] ++ [v5] = W'
    have hlen' : W'.length = W.length + 5 := by rw [← hW']; simp
    have hpre : ∀ i, i < W.length → W'.getD i false = W.getD i false := by
      intro i hi
      rw [← hW', List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
      exact List.getD_append _ _ _ _ hi
    have hlast : W'.getD (W.length + 4) false = v5 := by
      rw [← hW', ← hlen4]
      exact getD_snoc_eq _ _
    have hts' : ∀ τ ∈ ts, termBound W' τ := by
      intro τ hτ
      obtain ⟨hc, ha, hb, hd, he⟩ := hts τ (by simp [hτ])
      exact ⟨by omega, by omega, by omega, by omega, by omega⟩
    have hval : ∀ τ ∈ ts, termValue W' τ = termValue W τ := by
      intro τ hτ
      obtain ⟨hc, ha, hb, hd, he⟩ := hts τ (by simp [hτ])
      simp only [termValue, hpre _ hc, hpre _ ha, hpre _ hb, hpre _ hd, hpre _ he]
    have key := ih W' (W.length + 4) (by omega) hts'
    rw [hlen'] at key
    rw [key, hlast]
    have hhead : v4 = termValue W (c, a, b, d, e) := rfl
    change ((W.getD acc false || v4) = true ∨ ∃ τ ∈ ts, termValue W' τ = true) ↔ _
    rw [Bool.or_eq_true, hhead]
    simp only [List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((h | h) | ⟨τ, hτ, hv⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨τ, hτ, (hval τ hτ) ▸ hv⟩)
    · rintro (h | h | ⟨τ, hτ, hv⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨τ, hτ, (hval τ hτ).symm ▸ hv⟩

def extC (a b : ℕ) (σ : ℕ → ℕ) (D : Circuit) (ts : List (ℕ × ℕ × ℕ × ℕ × ℕ)) : Circuit :=
  ⟨D.gates.map (relG (rho a b σ)) ++ addTerms ts (b + D.gates.length) (rho a b σ D.output),
    finalAcc ts (b + D.gates.length) (rho a b σ D.output)⟩

lemma extC_mono (a b : ℕ) (σ : ℕ → ℕ) (D : Circuit) (ts : List (ℕ × ℕ × ℕ × ℕ × ℕ))
    (hF : Monotone2 D) : Monotone2 (extC a b σ D ts) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have := hF g0 hg0
    exact ⟨this.1, by simpa [relG] using this.2⟩
  · exact addTerms_ok _ _ _ g hg

lemma extC_size (a b : ℕ) (σ : ℕ → ℕ) (D : Circuit) (ts : List (ℕ × ℕ × ℕ × ℕ × ℕ)) :
    (extC a b σ D ts).size = D.size + 5 * ts.length := by
  show (D.gates.map _ ++ addTerms ts _ _).length = D.gates.length + 5 * ts.length
  rw [List.length_append, List.length_map, addTerms_length]

lemma extC_eval (D : Circuit) (ID Inew : List Bool) (σ : ℕ → ℕ)
    (ts : List (ℕ × ℕ × ℕ × ℕ × ℕ))
    (hout : D.output < ID.length + D.gates.length)
    (hσ : ∀ i, i < ID.length → σ i < Inew.length ∧ ID.getD i false = Inew.getD (σ i) false)
    (hts : ∀ τ ∈ ts, τ.1 < Inew.length ∧ τ.2.1 < Inew.length ∧
      τ.2.2.1 < Inew.length ∧ τ.2.2.2.1 < Inew.length ∧ τ.2.2.2.2 < Inew.length) :
    ((extC ID.length Inew.length σ D ts).eval Inew = true ↔
      (D.eval ID = true ∨ ∃ τ ∈ ts, Inew.getD τ.1 false = true ∧
        ((Inew.getD τ.2.1 false = true ∨ Inew.getD τ.2.2.1 false = true) ∨
          (Inew.getD τ.2.2.2.1 false = true ∨ Inew.getD τ.2.2.2.2 false = true)))) := by
  obtain ⟨rest', h1, h2⟩ := relabel_spec ID Inew σ hσ D.gates []
  rw [List.append_nil] at h1 h2
  have hrl : rest'.length = D.gates.length := by
    have := foldl_length D.gates ID
    rw [h2] at this
    simp at this
    omega
  have hWlen : (Inew ++ rest').length = Inew.length + D.gates.length := by simp [hrl]
  have hev : (extC ID.length Inew.length σ D ts).eval Inew
      = ((addTerms ts (Inew ++ rest').length (rho ID.length Inew.length σ D.output)).foldl stp
          (Inew ++ rest')).getD
          (finalAcc ts (Inew ++ rest').length (rho ID.length Inew.length σ D.output)) false := by
    rw [hWlen]
    simp only [Circuit.eval, wires_eq, extC, List.foldl_append, h1]
  have hDev : D.eval ID = (ID ++ rest').getD D.output false := by
    simp only [Circuit.eval, wires_eq, h2]
  have hacc : (Inew ++ rest').getD (rho ID.length Inew.length σ D.output) false = D.eval ID := by
    rw [hDev]
    exact getD_rho ID Inew rest' σ hσ D.output
  have hcond : rho ID.length Inew.length σ D.output < (Inew ++ rest').length := by
    rw [hWlen]
    unfold rho
    split_ifs with h3
    · have := (hσ _ h3).1
      omega
    · omega
  have hts' : ∀ τ ∈ ts, τ.1 < (Inew ++ rest').length ∧ τ.2.1 < (Inew ++ rest').length ∧
      τ.2.2.1 < (Inew ++ rest').length ∧ τ.2.2.2.1 < (Inew ++ rest').length ∧
      τ.2.2.2.2 < (Inew ++ rest').length := by
    intro τ hτ
    obtain ⟨a1, a2, a3, a4, a5⟩ := hts τ hτ
    rw [hWlen]
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  rw [hev, addTerms_spec ts (Inew ++ rest') _ hcond hts', hacc]
  simp only [termValue, Bool.and_eq_true, Bool.or_eq_true]
  apply or_congr Iff.rfl
  apply exists_congr
  intro τ
  apply and_congr_right
  intro hτ
  obtain ⟨a1, a2, a3, a4, a5⟩ := hts τ hτ
  rw [List.getD_append _ _ _ _ a1, List.getD_append _ _ _ _ a2,
    List.getD_append _ _ _ _ a3, List.getD_append _ _ _ _ a4, List.getD_append _ _ _ _ a5]

def selected : List (Fin 26) :=
  [2,4,5,6,7,8,10,11,12,14,15,16,17,18,19,20,21,22,23,24,25]

def sigma (i : ℕ) : ℕ := (selected.getD i 0).val

def rows : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(0,13,14,16,22),(1,13,15,21,25),(3,13,19,23,24),(9,13,17,18,20)]

def input26 (A B : Finset (Fin 13)) (i : Fin 26) : Bool :=
  if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ A) else decide (Fin.ofNat 13 i.val ∈ B)

lemma sigma_spec (f : Fin 26 → Bool) :
    ∀ i, i < (selected.map f).length → sigma i < (List.ofFn f).length ∧
      (selected.map f).getD i false = (List.ofFn f).getD (sigma i) false := by
  intro i hi
  have hi' : i < 21 := by simpa [selected] using hi
  interval_cases i <;> simp [sigma, selected, List.getD_eq_getElem?_getD]

lemma rows_bound (f : Fin 26 → Bool) :
    ∀ τ ∈ rows, termBound (List.ofFn f) τ := by
  intro τ hτ
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hτ
  rcases hτ with rfl | rfl | rfl | rfl <;> simp [termBound]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
lemma rows_spec (A B : Finset (Fin 13)) :
    (∃ τ ∈ rows, termValue (List.ofFn (input26 A B)) τ = true) ↔
    ∃ i ∈ A, i.val ∈ [0,1,3,9] ∧ ∃ j ∈ B, (i.val + j.val) % 13 ∈ [0,1,3,9] := by
  simp [rows, termValue, input26, List.getD_eq_getElem?_getD, Fin.exists_fin_succ]
  tauto

lemma full (C : Circuit) (hC : Monotone2 C) (hout : C.output < 21 + C.size) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size + 20 ∧
      ∀ A B : Finset (Fin 13),
        D.eval (List.ofFn (input26 A B)) = true ↔
          C.eval (selected.map (input26 A B)) = true ∨
            ∃ i ∈ A, i.val ∈ [0,1,3,9] ∧ ∃ j ∈ B, (i.val + j.val) % 13 ∈ [0,1,3,9] := by
  refine ⟨extC 21 26 sigma C rows, extC_mono _ _ _ _ _ hC, ?_, ?_⟩
  · simp [extC_size, rows]
  · intro A B
    have he := extC_eval C (selected.map (input26 A B)) (List.ofFn (input26 A B)) sigma rows
      (by simpa [selected, Circuit.size] using hout) (sigma_spec _) (rows_bound _)
    simp only [List.length_map, List.length_ofFn] at he
    change (extC 21 26 sigma C rows).eval (List.ofFn (input26 A B)) = true ↔ _ at he
    rw [← rows_spec]
    simpa only [termValue, Bool.and_eq_true, Bool.or_eq_true] using he

end PEqualNP.Outside.L_meta_3787_aux

theorem PEqualNP.Outside.L_meta_3787 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.output < (21 : ℕ) + x1.size →       ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.Monotone2 x4 ∧           x4.size ≤ x1.size + (20 : ℕ) ∧             have x5 : List (Fin (26 : ℕ)) := [(2 : Fin (26 : ℕ)), (4 : Fin (26 : ℕ)), (5 : Fin (26 : ℕ)), (6 : Fin (26 : ℕ)), (7 : Fin (26 : ℕ)), (8 : Fin (26 : ℕ)), (10 : Fin (26 : ℕ)), (11 : Fin (26 : ℕ)), (12 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)), (16 : Fin (26 : ℕ)), (17 : Fin (26 : ℕ)), (18 : Fin (26 : ℕ)), (19 : Fin (26 : ℕ)), (20 : Fin (26 : ℕ)), (21 : Fin (26 : ℕ)), (22 : Fin (26 : ℕ)), (23 : Fin (26 : ℕ)), (24 : Fin (26 : ℕ)), (25 : Fin (26 : ℕ))];             have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);             have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x7 x8 : Fin (13 : ℕ)) => (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             ∀ (x8 x9 : Finset (Fin (13 : ℕ))), x4.eval (List.ofFn (x6 x8 x9)) = Bool.true ↔ x1.eval (List.map (x6 x8 x9) x5) = Bool.true ∨ ∃ x10 ∈ x8, ↑x10 ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ∃ x11 ∈ x9, x7 x10 x11 := by
  exact PEqualNP.Outside.L_meta_3787_aux.full
