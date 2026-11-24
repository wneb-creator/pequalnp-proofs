import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3787

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
  · rw [ite_eq_left h, List.getD_append _ _ _ _ (hσ i h).1, List.getD_append _ _ _ _ h]
    exact (hσ i h).2.symm
  · rw [ite_eq_right h]
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

def input26 (A B : Finset (Fin 13)) (i : Fin 26) : Bool :=
  if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ A)
  else decide (Fin.ofNat 13 i.val ∈ B)

def rows (x : Fin 26 → Bool) : Bool :=
  (x 0 && ((x 13 || x 14) || (x 16 || x 22))) ||
  (x 1 && ((x 13 || x 15) || (x 21 || x 25))) ||
  (x 3 && ((x 13 || x 19) || (x 23 || x 24))) ||
  (x 9 && ((x 13 || x 17) || (x 18 || x 20)))

set_option maxRecDepth 2000 in
set_option maxHeartbeats 2000000 in
lemma rows_correct (A B : Finset (Fin 13)) :
    rows (input26 A B) = true ↔
      ∃ p ∈ A, p.val ∈ [0, 1, 3, 9] ∧
        ∃ q ∈ B, (p.val + q.val) % 13 ∈ [0, 1, 3, 9] := by
  simp [rows, input26, Fin.exists_fin_succ]
  tauto

def front : List Gate :=
  [⟨GateOp.or, [13, 14]⟩,
   ⟨GateOp.or, [16, 22]⟩,
   ⟨GateOp.or, [26, 27]⟩,
   ⟨GateOp.and, [0, 28]⟩,
   ⟨GateOp.or, [13, 15]⟩,
   ⟨GateOp.or, [21, 25]⟩,
   ⟨GateOp.or, [30, 31]⟩,
   ⟨GateOp.and, [1, 32]⟩,
   ⟨GateOp.or, [13, 19]⟩,
   ⟨GateOp.or, [23, 24]⟩,
   ⟨GateOp.or, [34, 35]⟩,
   ⟨GateOp.and, [3, 36]⟩,
   ⟨GateOp.or, [13, 17]⟩,
   ⟨GateOp.or, [18, 20]⟩,
   ⟨GateOp.or, [38, 39]⟩,
   ⟨GateOp.and, [9, 40]⟩,
   ⟨GateOp.or, [29, 33]⟩,
   ⟨GateOp.or, [42, 37]⟩,
   ⟨GateOp.or, [43, 41]⟩]

lemma fold_getD (gs : List Gate) (W : List Bool) (i : ℕ) (hi : i < W.length) :
    (gs.foldl stp W).getD i false = W.getD i false := by
  induction gs generalizing W with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [stp]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma front_length (x : Fin 26 → Bool) :
    (front.foldl stp (List.ofFn x)).length = 45 := by
  rw [foldl_length]
  simp [front]

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma front_correct (x : Fin 26 → Bool) :
    (front.foldl stp (List.ofFn x)).getD 44 false = rows x := by
  simp [front, stp, GateOp.eval, rows, List.ofFn_succ]

lemma front_ok : ∀ g ∈ front,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [front]


def selected : List (Fin 26) :=
  [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

def sigma (i : ℕ) : ℕ := (selected.getD i 0).val

def renamed (C : Circuit) : List Gate := C.gates.map (relG (rho 21 45 sigma))

def assembled (C : Circuit) : Circuit :=
  ⟨front ++ renamed C ++ [⟨GateOp.or, [rho 21 45 sigma C.output, 44]⟩], 45 + C.size⟩

lemma selected_length : selected.length = 21 := rfl

lemma mapped_inputs (x : Fin 26 → Bool) (i : ℕ) (hi : i < (selected.map x).length) :
    sigma i < (front.foldl stp (List.ofFn x)).length ∧
      (selected.map x).getD i false =
        (front.foldl stp (List.ofFn x)).getD (sigma i) false := by
  have hs : i < selected.length := by simpa using hi
  have hsig : sigma i = (selected[i]).val := by
    unfold sigma
    rw [List.getD_eq_getElem _ _ hs]
  have hv := (selected[i]).isLt
  rw [hsig]
  refine ⟨by rw [front_length]; omega, ?_⟩
  rw [List.getD_eq_getElem _ _ hi, List.getElem_map,
    fold_getD front _ _ (by simpa using hv), getD_ofFn _ _ hv]

lemma renamed_eval (C : Circuit) (x : Fin 26 → Bool) :
    ((renamed C).foldl stp (front.foldl stp (List.ofFn x))).getD
        (rho 21 45 sigma C.output) false = C.eval (selected.map x) := by
  obtain ⟨rest, hnew, hold⟩ := relabel_spec (selected.map x)
    (front.foldl stp (List.ofFn x)) sigma (mapped_inputs x) C.gates []
  simp only [List.length_map, selected_length, front_length, List.append_nil] at hnew hold
  change ((C.gates.map (relG (rho 21 45 sigma))).foldl stp
    (front.foldl stp (List.ofFn x))).getD _ false = _
  rw [hnew]
  have hread := getD_rho (selected.map x) (front.foldl stp (List.ofFn x))
    rest sigma (mapped_inputs x) C.output
  simp only [List.length_map, selected_length, front_length] at hread
  rw [hread, ← hold]
  rfl

lemma assembled_size (C : Circuit) : (assembled C).size = C.size + 20 := by
  simp [assembled, Circuit.size, renamed, front]

lemma assembled_ok (C : Circuit) (hC : Monotone2 C) : Monotone2 (assembled C) := by
  intro g hg
  simp only [assembled, List.mem_append, List.mem_singleton] at hg
  rcases hg with (hf | hr) | rfl
  · exact front_ok g hf
  · obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hr
    have h := hC old ho
    exact ⟨h.1, by simpa [relG] using h.2⟩
  · simp

lemma assembled_eval (C : Circuit) (x : Fin 26 → Bool) :
    (assembled C).eval (List.ofFn x) = (C.eval (selected.map x) || rows x) := by
  let W := (renamed C).foldl stp (front.foldl stp (List.ofFn x))
  have hlen : W.length = 45 + C.size := by
    change ((renamed C).foldl stp (front.foldl stp (List.ofFn x))).length = _
    rw [foldl_length, front_length]
    simp [renamed, Circuit.size]
  have h44 : W.getD 44 false = rows x := by
    rw [fold_getD (renamed C) _ _ (by rw [front_length]; omega), front_correct]
  have houtput : W.getD (rho 21 45 sigma C.output) false = C.eval (selected.map x) :=
    renamed_eval C x
  change ((front ++ renamed C ++ ([⟨GateOp.or, [rho 21 45 sigma C.output, 44]⟩] : List Gate)).foldl
    stp (List.ofFn x)).getD (45 + C.size) false = _
  rw [List.foldl_append, List.foldl_append]
  change (stp W ⟨GateOp.or, [rho 21 45 sigma C.output, 44]⟩).getD (45 + C.size) false = _
  rw [← hlen]
  simp only [stp, getD_snoc_eq, GateOp.eval, List.map_cons, List.map_nil,
    List.any_cons, List.any_nil, id, Bool.or_false, houtput, h44]

end PEqualNP.Outside.L_meta_3787

open PEqualNP.Outside.L_meta_3787

theorem PEqualNP.Outside.L_meta_3787 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.output < (21 : ℕ) + x1.size →       ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.Monotone2 x4 ∧           x4.size ≤ x1.size + (20 : ℕ) ∧             have x5 : List (Fin (26 : ℕ)) := [(2 : Fin (26 : ℕ)), (4 : Fin (26 : ℕ)), (5 : Fin (26 : ℕ)), (6 : Fin (26 : ℕ)), (7 : Fin (26 : ℕ)), (8 : Fin (26 : ℕ)), (10 : Fin (26 : ℕ)), (11 : Fin (26 : ℕ)), (12 : Fin (26 : ℕ)), (14 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)), (16 : Fin (26 : ℕ)), (17 : Fin (26 : ℕ)), (18 : Fin (26 : ℕ)), (19 : Fin (26 : ℕ)), (20 : Fin (26 : ℕ)), (21 : Fin (26 : ℕ)), (22 : Fin (26 : ℕ)), (23 : Fin (26 : ℕ)), (24 : Fin (26 : ℕ)), (25 : Fin (26 : ℕ))];             have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);             have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x7 x8 : Fin (13 : ℕ)) => (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             ∀ (x8 x9 : Finset (Fin (13 : ℕ))), x4.eval (List.ofFn (x6 x8 x9)) = Bool.true ↔ x1.eval (List.map (x6 x8 x9) x5) = Bool.true ∨ ∃ x10 ∈ x8, ↑x10 ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ∃ x11 ∈ x9, x7 x10 x11 := by
  intro C hC _
  refine ⟨assembled C, assembled_ok C hC, le_of_eq (assembled_size C), ?_⟩
  dsimp only
  intro A B
  change (assembled C).eval (List.ofFn (input26 A B)) = true ↔
    C.eval (selected.map (input26 A B)) = true ∨ _
  rw [assembled_eval, Bool.or_eq_true, rows_correct]
