import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4934_aux

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def reGate (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

def rho (m N : ℕ) (σ : Fin m → Fin N) (k : ℕ) : ℕ :=
  if h : k < m then (σ ⟨k, h⟩).val else N + (k - m)

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma fold_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma getD_rho {m N : ℕ} (W y T : List Bool) (σ : Fin m → Fin N) (hW : W.length = N)
    (hy : y.length = m) (hyv : ∀ k (h : k < m), y.getD k false = W.getD (σ ⟨k, h⟩) false)
    (k : ℕ) : (W ++ T).getD (rho m N σ k) false = (y ++ T).getD k false := by
  unfold rho
  split_ifs with h
  · have := (σ ⟨k, h⟩).isLt
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega), hyv k h]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

lemma fold_rel {m N : ℕ} (W y : List Bool) (σ : Fin m → Fin N) (hW : W.length = N)
    (hy : y.length = m) (hyv : ∀ k (h : k < m), y.getD k false = W.getD (σ ⟨k, h⟩) false)
    (gs : List Gate) : ∀ T : List Bool, ∃ R : List Bool,
      (gs.map (reGate (rho m N σ))).foldl stepW (W ++ T) = W ++ R ∧
      gs.foldl stepW (y ++ T) = y ++ R := by
  induction gs with
  | nil => intro T; exact ⟨T, rfl, rfl⟩
  | cons g gs ih =>
    intro T
    have hm : (g.inputs.map (rho m N σ)).map (fun i => (W ++ T).getD i false)
        = g.inputs.map (fun i => (y ++ T).getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => getD_rho W y T σ hW hy hyv i)
    have e1 : stepW (W ++ T) (reGate (rho m N σ) g)
        = W ++ (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)]) := by
      show (W ++ T) ++ [g.op.eval ((g.inputs.map (rho m N σ)).map fun i => (W ++ T).getD i false)] = _
      rw [hm, List.append_assoc]
    have e2 : stepW (y ++ T) g
        = y ++ (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)]) := by
      show (y ++ T) ++ _ = _
      rw [List.append_assoc]
    obtain ⟨R, h1, h2⟩ := ih (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)])
    refine ⟨R, ?_, ?_⟩
    · rw [List.map_cons, List.foldl_cons, e1, h1]
    · rw [List.foldl_cons, e2, h2]

end PEqualNP.Outside.L_meta_4934_aux
namespace PEqualNP.Outside.L_meta_4934_aux

open PEqualNP.CircuitLowerBounds

def sig (n : ℕ) (σ : Fin n → Fin n) (k : Fin (n + 1)) : Fin (n + 1) :=
  if h : k.val < n then ⟨(σ ⟨k.val, h⟩).val, by omega⟩ else k

lemma hyv_lem (n : ℕ) (σ : Fin n → Fin n) (x : Fin n → Bool) (b : Bool) :
    ∀ k (h : k < n + 1), (List.ofFn (x ∘ σ) ++ [b]).getD k false
      = (List.ofFn x ++ [b]).getD (sig n σ ⟨k, h⟩) false := by
  intro k h
  unfold sig
  by_cases hk : k < n
  · have := (σ ⟨k, hk⟩).isLt
    simp only [hk, dite_true]
    rw [List.getD_append _ _ _ _ (by simp [hk]), List.getD_append _ _ _ _ (by simpa using this)]
    simp [List.getD_eq_getElem?_getD, hk, this]
  · simp only [hk, dite_false]
    have hk' : k = n := by omega
    subst hk'
    rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
    simp

end PEqualNP.Outside.L_meta_4934_aux

namespace PEqualNP.Outside.L_meta_4934_aux

open PEqualNP.CircuitLowerBounds

def rc (σ : Fin 10 → Fin 10) (k : ℕ) : ℕ := min (rho 11 11 (sig 10 σ) k) 29

lemma getD_cap (L : List Bool) (k : ℕ) (hL : L.length ≤ 29) :
    L.getD (min k 29) false = L.getD k false := by
  rcases le_total k 29 with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

lemma fold_rel2 (σ : Fin 10 → Fin 10) (W y : List Bool) (hW : W.length = 11)
    (hy : y.length = 11)
    (hyv : ∀ k (h : k < 11), y.getD k false = W.getD (sig 10 σ ⟨k, h⟩) false)
    (gs : List Gate) : ∀ T : List Bool, T.length + gs.length ≤ 18 → ∃ R : List Bool,
      (gs.map (reGate (rc σ))).foldl stepW (W ++ T) = W ++ R ∧
      gs.foldl stepW (y ++ T) = y ++ R := by
  induction gs with
  | nil => intro T _; exact ⟨T, rfl, rfl⟩
  | cons g gs ih =>
    intro T hT
    simp only [List.length_cons] at hT
    have hm : (g.inputs.map (rc σ)).map (fun i => (W ++ T).getD i false)
        = g.inputs.map (fun i => (y ++ T).getD i false) := by
      rw [List.map_map]
      refine List.map_congr_left (fun i _ => ?_)
      show (W ++ T).getD (min _ 29) false = _
      rw [getD_cap _ _ (by simp [hW]; omega)]
      exact getD_rho W y T (sig 10 σ) hW hy hyv i
    have e1 : stepW (W ++ T) (reGate (rc σ) g)
        = W ++ (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)]) := by
      show (W ++ T) ++ [g.op.eval ((g.inputs.map (rc σ)).map fun i => (W ++ T).getD i false)] = _
      rw [hm, List.append_assoc]
    have e2 : stepW (y ++ T) g
        = y ++ (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)]) := by
      show (y ++ T) ++ _ = _
      rw [List.append_assoc]
    obtain ⟨R, h1, h2⟩ := ih (T ++ [g.op.eval (g.inputs.map fun i => (y ++ T).getD i false)])
      (by simp; omega)
    refine ⟨R, ?_, ?_⟩
    · rw [List.map_cons, List.foldl_cons, e1, h1]
    · rw [List.foldl_cons, e2, h2]

end PEqualNP.Outside.L_meta_4934_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_4934_aux in
theorem PEqualNP.Outside.L_meta_4934 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x1.size ∧ x5.output ≤ (29 : ℕ) ∧ (∀ x6 ∈ x5.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (29 : ℕ)) ∧ ∀ (x6 : Fin (10 : ℕ) → Bool) (x7 : Bool), x5.eval (List.ofFn x6 ++ [x7]) = x1.eval (List.ofFn (x6 ∘ x2) ++ [x7]) := by
  intro C σ hC hs
  have hsz : C.gates.length ≤ 18 := by simpa [Circuit.size] using hs
  refine ⟨⟨C.gates.map (reGate (rc σ)), rc σ C.output⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    have := hC g' hg'
    simpa [reGate] using this
  · simp [Circuit.size]
  · exact min_le_right _ _
  · intro g hg i hi
    simp only [List.mem_map] at hg
    obtain ⟨g', _, rfl⟩ := hg
    simp only [reGate, List.mem_map] at hi
    obtain ⟨a, _, rfl⟩ := hi
    exact min_le_right _ _
  · intro x b
    have hW : (List.ofFn x ++ [b]).length = 11 := by simp
    have hy : (List.ofFn (x ∘ σ) ++ [b]).length = 11 := by simp
    obtain ⟨R, h1, h2⟩ := fold_rel2 σ _ _ hW hy (hyv_lem 10 σ x b) C.gates [] (by simpa using hsz)
    simp only [List.append_nil] at h1 h2
    have hl := fold_len C.gates (List.ofFn (x ∘ σ) ++ [b])
    rw [h2] at hl
    show (List.foldl stepW _ _).getD _ false = (List.foldl stepW _ _).getD _ false
    rw [h1, h2]
    show (List.ofFn x ++ [b] ++ R).getD (min _ 29) false = _
    rw [getD_cap _ _ (by simp at hl ⊢; omega)]
    exact getD_rho _ _ R (sig 10 σ) hW hy (hyv_lem 10 σ x b) _
