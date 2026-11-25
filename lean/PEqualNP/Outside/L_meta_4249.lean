import Mathlib
import PEqualNP.Defs

-- A special case of the general re-wiring lemma proved first.
-- Put the OR of the two chosen inputs in front as one new gate and renumber every wire
-- the old gates read: the replaced input becomes the new gate, the other inputs follow
-- the given map, and old gate wires shift up by one. The old and new circuits then agree
-- wire by wire.
namespace PEqualNP.Outside.L_meta_4249
open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma W_length (gs : List Gate) : ∀ x : List Bool, (W gs x).length = x.length + gs.length := by
  induction gs with
  | nil => intro x; simp [W]
  | cons g gs ih =>
    intro x
    rw [W_cons, ih]
    simp
    omega

lemma getD_snoc (l : List Bool) (v : Bool) (i : Nat) :
    (l ++ [v]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  · rw [List.getD_eq_default]
    simp
    omega

lemma ofFn_getD {k : Nat} (f : Fin k → Bool) (i : Nat) :
    (List.ofFn f).getD i false = if h : i < k then f ⟨i, h⟩ else false := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default]
    simpa using h

def rho (n m z : ℕ) (s : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < n then (if i = z then m else s i) else m + 1 + (i - n)

def mapG (n m z : ℕ) (s : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho n m z s)⟩

lemma rho_lt (n m z : ℕ) (s : ℕ → ℕ) (hs : ∀ i, i < n → s i < m) (k j : ℕ) (hj : j < n + k) :
    rho n m z s j < m + 1 + k := by
  unfold rho
  split_ifs with a b
  · omega
  · have := hs j a
    omega
  · omega

lemma sim (n m z : ℕ) (s : ℕ → ℕ) (hs : ∀ i, i < n → s i < m) (gs : List Gate) :
    ∀ (k : ℕ) (w w' : List Bool), w.length = n + k → w'.length = m + 1 + k →
      (∀ i, i < n + k → w.getD i false = w'.getD (rho n m z s i) false) →
      (∀ t (ht : t < gs.length), ∀ i ∈ (gs[t]).inputs, i < n + k + t) →
      ∀ i, i < n + k + gs.length →
        (W gs w).getD i false = (W (gs.map (mapG n m z s)) w').getD (rho n m z s i) false := by
  induction gs with
  | nil =>
    intro k w w' _ _ h _ i hi
    exact h i (by simpa using hi)
  | cons g gs ih =>
    intro k w w' hl hl' h hr i hi
    rw [List.map_cons, W_cons, W_cons]
    have hg : ∀ j ∈ g.inputs, j < n + k := fun j hj => by
      have := hr 0 (by simp) j (by simpa using hj)
      omega
    have hv : (mapG n m z s g).op.eval ((mapG n m z s g).inputs.map fun j => w'.getD j false) =
        g.op.eval (g.inputs.map fun j => w.getD j false) := by
      simp only [mapG, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j hj
      exact (h j (hg j hj)).symm
    rw [hv]
    refine ih (k + 1) _ _ (by simp [hl]; omega) (by simp [hl']; omega) ?_ ?_ i
      (by simp only [List.length_cons] at hi; omega)
    · intro j hj
      rw [getD_snoc, getD_snoc, hl, hl']
      by_cases h1 : j < n + k
      · rw [if_pos h1, if_pos (rho_lt n m z s hs k j h1)]
        exact h j h1
      · have hj' : j = n + k := by omega
        have hr' : rho n m z s j = m + 1 + k := by
          unfold rho
          rw [if_neg (by omega)]
          omega
        rw [if_neg h1, if_pos hj', hr', if_neg (by omega), if_pos rfl]
    · intro t ht j hj
      have := hr (t + 1) (by simp only [List.length_cons]; omega) j (by simpa using hj)
      omega

def ext (n m : ℕ) (σ : Fin n → Fin m) (i : ℕ) : ℕ := if h : i < n then (σ ⟨i, h⟩).val else 0

lemma ext_eq (n m : ℕ) (σ : Fin n → Fin m) (i : ℕ) (hi : i < n) :
    ext n m σ i = (σ ⟨i, hi⟩).val := by
  unfold ext
  rw [dif_pos hi]

open PEqualNP.MetaComplexity.NestedCover in
theorem main : ∀ (x1 x2 : ℕ) (x3 : Fin x1) (x4 x5 : Fin x2) (x6 : Fin x1 → Fin x2) (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x7 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x10 ∧ x10.size ≤ x7.size + (1 : ℕ) ∧ ∀ (x11 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x10 x11 = PEqualNP.MetaComplexity.circuitFun x1 x7 fun (x12 : Fin x1) => if x12 = x3 then x11 x4 || x11 x5 else x11 (x6 x12) := by
  intro n m z a b σ C hmono hrb
  have hs : ∀ i, i < n → ext n m σ i < m := by
    intro i hi
    rw [ext_eq n m σ i hi]
    exact (σ ⟨i, hi⟩).isLt
  have hgate : ∀ k (hk : k < C.gates.length), gateAt C k = C.gates[k] := by
    intro k hk
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hk]
  refine ⟨⟨(⟨GateOp.or, [a.val, b.val]⟩ : Gate) ::
      C.gates.map (mapG n m z.val (ext n m σ)),
    rho n m z.val (ext n m σ) C.output⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.mem_map] at hg
    rcases hg with rfl | ⟨g0, hg0, rfl⟩
    · exact ⟨by simp, by simp⟩
    · have h0 := hmono g0 hg0
      exact ⟨h0.1, by simpa [mapG] using h0.2⟩
  · intro j hj i hi
    cases j with
    | zero =>
      have hi' : i = a.val ∨ i = b.val := by simpa [gateAt] using hi
      rcases hi' with rfl | rfl
      · have := a.isLt; omega
      · have := b.isLt; omega
    | succ k =>
      have hk : k < C.gates.length := by simpa using hj
      have e : gateAt (⟨(⟨GateOp.or, [a.val, b.val]⟩ : Gate) ::
          C.gates.map (mapG n m z.val (ext n m σ)),
          rho n m z.val (ext n m σ) C.output⟩ : Circuit)
          (k + 1) = mapG n m z.val (ext n m σ)
            (C.gates[k]) := by
        unfold gateAt
        rw [List.getD_cons_succ, List.getD_eq_getElem _ _ (by simpa using hk)]
        simp
      rw [e] at hi
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
      have h0 : i0 < n + k := hrb k hk i0 (by rw [hgate k hk]; exact hi0)
      have := rho_lt n m z.val _ hs k i0 h0
      omega
  · show ((⟨GateOp.or, [a.val, b.val]⟩ : Gate) :: C.gates.map _).length ≤ C.gates.length + 1
    simp
  · intro y
    have base : ∀ i, i < n + 0 →
        (List.ofFn fun i : Fin n => if i = z then y a || y b else y (σ i)).getD i false =
        (List.ofFn y ++ [y a || y b]).getD
          (rho n m z.val (ext n m σ) i) false := by
      intro i hi
      have hi' : i < n := by omega
      rw [ofFn_getD, dif_pos hi']
      by_cases hz : i = z.val
      · have hρ : rho n m z.val (ext n m σ) i = m := by
          unfold rho
          rw [if_pos hi', if_pos hz]
        have hx : (⟨i, hi'⟩ : Fin n) = z := Fin.ext hz
        rw [if_pos hx, hρ, getD_snoc, List.length_ofFn, if_neg (Nat.lt_irrefl m), if_pos rfl]
      · have hρ : rho n m z.val (ext n m σ) i = ext n m σ i := by
          unfold rho
          rw [if_pos hi', if_neg hz]
        have hx : (⟨i, hi'⟩ : Fin n) ≠ z := fun h => hz (congrArg Fin.val h)
        rw [if_neg hx, hρ, getD_snoc, List.length_ofFn, if_pos (hs i hi'), ofFn_getD,
          dif_pos (hs i hi')]
        exact congrArg y (Fin.ext (ext_eq n m σ i hi').symm)
    have key := sim n m z.val _ hs C.gates 0 _ _ (by simp) (by simp) base
      (fun t ht i hi => by
        have := hrb t ht i (by rw [hgate t ht]; exact hi)
        omega)
    have hfirst : GateOp.or.eval ([a.val, b.val].map fun j => (List.ofFn y).getD j false) =
        (y a || y b) := by
      simp only [List.map_cons, List.map_nil, ofFn_getD, dif_pos a.isLt, dif_pos b.isLt]
      cases y a <;> cases y b <;> rfl
    show (W (C.gates.map (mapG n m z.val (ext n m σ)))
      (List.ofFn y ++ [GateOp.or.eval ([a.val, b.val].map fun j =>
        (List.ofFn y).getD j false)])).getD
        (rho n m z.val (ext n m σ) C.output) false =
      (W C.gates (List.ofFn fun i : Fin n => if i = z then y a || y b else y (σ i))).getD
        C.output false
    rw [hfirst]
    by_cases ho : C.output < n + 0 + C.gates.length
    · exact (key C.output ho).symm
    · have h1 : (W C.gates (List.ofFn fun i : Fin n =>
          if i = z then y a || y b else y (σ i))).length ≤ C.output := by
        rw [W_length, List.length_ofFn]
        omega
      have h2 : (W (C.gates.map (mapG n m z.val
          (ext n m σ)))
          (List.ofFn y ++ [y a || y b])).length ≤
          rho n m z.val (ext n m σ) C.output := by
        rw [W_length]
        simp only [List.length_append, List.length_ofFn, List.length_singleton, List.length_map]
        unfold rho
        rw [if_neg (by omega)]
        omega
      rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]

end PEqualNP.Outside.L_meta_4249

theorem PEqualNP.Outside.L_meta_4249 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 : ℕ) x1 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (17 : ℕ) x4 ∧ x4.size ≤ x1.size + (1 : ℕ) ∧ ∀ (x5 : Fin (17 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (17 : ℕ) x4 x5 = PEqualNP.MetaComplexity.circuitFun (16 : ℕ) x1 fun (x6 : Fin (16 : ℕ)) => if ↑x6 = (10 : ℕ) then x5 (10 : Fin (17 : ℕ)) || x5 (15 : Fin (17 : ℕ)) else if ↑x6 = (15 : ℕ) then x5 (16 : Fin (17 : ℕ)) else x5 x6.castSucc := by
  intro C hmono hrb
  obtain ⟨D, h1, h2, h3, h4⟩ := PEqualNP.Outside.L_meta_4249.main 16 17 10 10 15
    (fun i : Fin 16 => if i.val = 15 then (16 : Fin 17) else ⟨i.val, by omega⟩) C hmono hrb
  refine ⟨D, h1, h2, h3, fun y => ?_⟩
  rw [h4 y]
  congr 1
  funext i
  by_cases h10 : i = 10
  · subst h10
    rfl
  · have h10' : ¬ (i.val = 10) := fun h => h10 (Fin.ext h)
    rw [if_neg h10, if_neg h10']
    by_cases h15 : i.val = 15
    · rw [if_pos h15, if_pos h15]
    · rw [if_neg h15, if_neg h15]
      rfl
