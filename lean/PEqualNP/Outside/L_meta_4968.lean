import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4968

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]


def ext (n s : ℕ) (vn wn : ℕ → ℕ) : ℕ → List Gate
  | 0 => [⟨GateOp.and, [vn 0, wn 0]⟩]
  | k + 1 => ext n s vn wn k ++
      [⟨GateOp.and, [vn (k + 1), wn (k + 1)]⟩, ⟨GateOp.or, [n + s + 2 * k, n + s + 2 * k + 1]⟩]

lemma ext_length (n s : ℕ) (vn wn : ℕ → ℕ) : ∀ k, (ext n s vn wn k).length = 2 * k + 1 := by
  intro k
  induction k with
  | zero => simp [ext]
  | succ k ih => simp [ext, ih]; omega

lemma ext_mono (n s : ℕ) (vn wn : ℕ → ℕ) : ∀ k, ∀ g ∈ ext n s vn wn k,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro k
  induction k with
  | zero =>
    intro g hg
    simp only [ext, List.mem_singleton] at hg
    subst hg
    simp
  | succ k ih =>
    intro g hg
    simp only [ext, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | hg | hg
    · exact ih g hg
    · subst hg; simp
    · subst hg; simp

lemma key (n s : ℕ) (vn wn : ℕ → ℕ) (Wc : List Bool) (hlen : Wc.length = n + s)
    (hv : ∀ i, vn i < n + s) (hw : ∀ i, wn i < n + s) : ∀ k,
    ((wiresFrom (ext n s vn wn k) Wc).getD (n + s + 2 * k) false = true ↔
      ∃ i, i ≤ k ∧ Wc.getD (vn i) false = true ∧ Wc.getD (wn i) false = true) := by
  intro k
  induction k with
  | zero =>
    have h1 : wiresFrom (ext n s vn wn 0) Wc =
        Wc ++ [Wc.getD (vn 0) false && Wc.getD (wn 0) false] := by
      simp [wiresFrom, ext, GateOp.eval]
    have h2 : (Wc ++ [Wc.getD (vn 0) false && Wc.getD (wn 0) false]).getD (n + s + 2 * 0) false =
        (Wc.getD (vn 0) false && Wc.getD (wn 0) false) := by
      have : n + s + 2 * 0 = Wc.length := by omega
      rw [this]
      simp
    rw [h1, h2]
    constructor
    · intro h
      rw [Bool.and_eq_true] at h
      exact ⟨0, le_refl 0, h.1, h.2⟩
    · rintro ⟨i, hi, ha, hb⟩
      have : i = 0 := by omega
      subst this
      rw [Bool.and_eq_true]
      exact ⟨ha, hb⟩
  | succ k ih =>
    have hWl : (wiresFrom (ext n s vn wn k) Wc).length = n + s + 2 * k + 1 := by
      rw [length_wiresFrom, ext_length, hlen]; omega
    have hva : (wiresFrom (ext n s vn wn k) Wc).getD (vn (k + 1)) false = Wc.getD (vn (k + 1)) false :=
      getD_wiresFrom_lt _ _ _ (by rw [hlen]; exact hv _)
    have hwa : (wiresFrom (ext n s vn wn k) Wc).getD (wn (k + 1)) false = Wc.getD (wn (k + 1)) false :=
      getD_wiresFrom_lt _ _ _ (by rw [hlen]; exact hw _)
    have hstep : wiresFrom (ext n s vn wn (k + 1)) Wc =
        (wiresFrom (ext n s vn wn k) Wc ++
          [Wc.getD (vn (k + 1)) false && Wc.getD (wn (k + 1)) false]) ++
          [(wiresFrom (ext n s vn wn k) Wc).getD (n + s + 2 * k) false ||
            (Wc.getD (vn (k + 1)) false && Wc.getD (wn (k + 1)) false)] := by
      have e0 : ext n s vn wn (k + 1) = ext n s vn wn k ++
          [⟨GateOp.and, [vn (k + 1), wn (k + 1)]⟩, ⟨GateOp.or, [n + s + 2 * k, n + s + 2 * k + 1]⟩] := rfl
      rw [e0, wiresFrom_append]
      generalize hW : wiresFrom (ext n s vn wn k) Wc = W at hWl hva hwa
      have g1 : (W ++ [Wc.getD (vn (k + 1)) false && Wc.getD (wn (k + 1)) false]).getD
          (n + s + 2 * k) false = W.getD (n + s + 2 * k) false := by
        rw [List.getD_append _ _ _ _ (by omega)]
      have g2 : (W ++ [Wc.getD (vn (k + 1)) false && Wc.getD (wn (k + 1)) false]).getD
          (n + s + 2 * k + 1) false = (Wc.getD (vn (k + 1)) false && Wc.getD (wn (k + 1)) false) := by
        rw [← hWl]
        simp
      simp only [wiresFrom, List.foldl_cons, List.foldl_nil, GateOp.eval, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, List.any_cons, List.any_nil, id, Bool.and_true, Bool.or_false,
        hva, hwa, g1, g2]
    rw [hstep]
    have hidx : n + s + 2 * (k + 1) =
        (wiresFrom (ext n s vn wn k) Wc ++
          [Wc.getD (vn (k + 1)) false && Wc.getD (wn (k + 1)) false]).length := by
      rw [List.length_append, hWl]; simp; omega
    rw [hidx]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_concat_length, Option.getD_some]
    rw [Bool.or_eq_true, Bool.and_eq_true]
    simp only [List.getD_eq_getElem?_getD] at ih
    rw [ih]
    constructor
    · rintro (⟨i, hi, ha, hb⟩ | ⟨ha, hb⟩)
      · exact ⟨i, by omega, ha, hb⟩
      · exact ⟨k + 1, le_refl _, ha, hb⟩
    · rintro ⟨i, hi, ha, hb⟩
      rcases Nat.lt_or_ge i (k + 1) with h | h
      · exact Or.inl ⟨i, by omega, ha, hb⟩
      · have : i = k + 1 := by omega
        subst this
        exact Or.inr ⟨ha, hb⟩

end PEqualNP.Outside.L_meta_4968

theorem PEqualNP.Outside.L_meta_4968 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (x2 + (1 : ℕ)) → Fin x1) (x5 : Fin (x2 + (1 : ℕ)) → ℕ), PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin (x2 + (1 : ℕ))), x5 x7 < x1 + x3.size) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size = x3.size + (2 : ℕ) * x2 + (1 : ℕ) ∧ x8.output < x1 + x8.size ∧ (∀ (x9 : Fin x1 → Bool), ∀ x10 < x1 + x3.size, (x8.wires (List.ofFn x9)).getD x10 Bool.false = (x3.wires (List.ofFn x9)).getD x10 Bool.false) ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = Bool.true ↔ ∃ (x10 : Fin (x2 + (1 : ℕ))), x9 (x4 x10) = Bool.true ∧ (x3.wires (List.ofFn x9)).getD (x5 x10) Bool.false = Bool.true := by
  intro n m C v w hC hw
  have hsz : C.size = C.gates.length := rfl
  let s := C.gates.length
  let vn : ℕ → ℕ := fun i => if h : i < m + 1 then (v ⟨i, h⟩).val else 0
  let wn : ℕ → ℕ := fun i => if h : i < m + 1 then w ⟨i, h⟩ else 0
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) (v 0).isLt
  have hvn : ∀ i, vn i < n := by
    intro i
    by_cases h : i < m + 1
    · simp only [vn, dif_pos h]; exact (v ⟨i, h⟩).isLt
    · simp only [vn, dif_neg h]; exact hn
  have hwn : ∀ i, wn i < n + s := by
    intro i
    by_cases h : i < m + 1
    · simp only [wn, dif_pos h]; exact hw ⟨i, h⟩
    · simp only [wn, dif_neg h]; omega
  have hEl := PEqualNP.Outside.L_meta_4968.ext_length n s vn wn m
  have hWc : ∀ x : Fin n → Bool, (PEqualNP.Outside.L_meta_4968.wiresFrom C.gates (List.ofFn x)).length = n + s := by
    intro x
    rw [PEqualNP.Outside.L_meta_4968.length_wiresFrom]; simp [s]
  have hsplit : ∀ x : Fin n → Bool,
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.gates ++ PEqualNP.Outside.L_meta_4968.ext n s vn wn m, n + s + 2 * m⟩ (List.ofFn x)) =
        PEqualNP.Outside.L_meta_4968.wiresFrom (PEqualNP.Outside.L_meta_4968.ext n s vn wn m) (PEqualNP.Outside.L_meta_4968.wiresFrom C.gates (List.ofFn x)) := by
    intro x
    exact PEqualNP.Outside.L_meta_4968.wiresFrom_append C.gates _ _
  refine ⟨⟨C.gates ++ PEqualNP.Outside.L_meta_4968.ext n s vn wn m, n + s + 2 * m⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hC g h
    · exact PEqualNP.Outside.L_meta_4968.ext_mono n s vn wn m g h
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append, hEl]; omega
  · simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_append, hEl]; omega
  · intro x j hj
    rw [hsplit x]
    exact PEqualNP.Outside.L_meta_4968.getD_wiresFrom_lt _ _ j (by rw [hWc x]; exact hj)
  · intro x
    have hk := PEqualNP.Outside.L_meta_4968.key n s vn wn (PEqualNP.Outside.L_meta_4968.wiresFrom C.gates (List.ofFn x)) (hWc x)
      (fun i => Nat.lt_of_lt_of_le (hvn i) (Nat.le_add_right n s)) hwn m
    have hin : ∀ i, (PEqualNP.Outside.L_meta_4968.wiresFrom C.gates (List.ofFn x)).getD (vn i) false = x ⟨vn i, hvn i⟩ := by
      intro i
      rw [PEqualNP.Outside.L_meta_4968.getD_wiresFrom_lt _ _ _ (by simp; exact hvn i)]
      simp [List.getD_eq_getElem?_getD, hvn i]
    show (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨C.gates ++ PEqualNP.Outside.L_meta_4968.ext n s vn wn m, n + s + 2 * m⟩ (List.ofFn x)).getD (n + s + 2 * m) false = true ↔ _
    rw [hsplit x, hk]
    constructor
    · rintro ⟨i, hi, ha, hb⟩
      have hi' : i < m + 1 := by omega
      refine ⟨⟨i, hi'⟩, ?_, ?_⟩
      · rw [hin i] at ha
        have : (⟨vn i, hvn i⟩ : Fin n) = v ⟨i, hi'⟩ := Fin.ext (by simp only [vn, dif_pos hi'])
        rw [← this]; exact ha
      · have : wn i = w ⟨i, hi'⟩ := by simp only [wn, dif_pos hi']
        rw [← this]; exact hb
    · rintro ⟨i, ha, hb⟩
      refine ⟨i.val, by omega, ?_, ?_⟩
      · rw [hin i.val]
        have : (⟨vn i.val, hvn i.val⟩ : Fin n) = v i := Fin.ext (by simp only [vn, dif_pos i.isLt])
        rw [this]; exact ha
      · have : wn i.val = w i := by simp only [wn, dif_pos i.isLt]
        rw [this]; exact hb
