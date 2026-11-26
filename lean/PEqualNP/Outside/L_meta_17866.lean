import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17866
open PEqualNP.CircuitLowerBounds

abbrev T := (Fin 10 → Bool) → Bool

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len_foldl (hs : List Gate) (a b : List Bool) (h : a.length = b.length) :
    (hs.foldl stepF a).length = (hs.foldl stepF b).length := by
  induction hs generalizing a b with
  | nil => simpa using h
  | cons g hs ih =>
    apply ih
    simp [stepF, h]

theorem key (L : List T) (S0 : Set T) (R : ℕ → Set T → Prop)
    (hf : (fun _ => false) ∈ S0) (hL : ∀ f ∈ L, f ∈ S0) (h0 : R 0 S0)
    (hstep : ∀ (k : ℕ) (S : Set T) (op : GateOp) (l : List T), R k S →
      op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not → l.length ≤ 2 → (∀ f ∈ l, f ∈ S) →
      (fun x => op.eval (l.map fun f => f x)) ∉ S →
      R (k + 1) (Insert.insert (fun x => op.eval (l.map fun f => f x)) S)) :
    ∀ gs : List Gate, (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) →
    ∃ k ≤ gs.length, ∃ S, R k S ∧ S0 ⊆ S ∧
      ∀ i, (fun x => (gs.foldl stepF (L.map fun f => f x)).getD i false) ∈ S := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨0, le_refl _, S0, h0, subset_refl _, fun i => ?_⟩
    by_cases hi : i < L.length
    · have : (fun x => (L.map fun f => f x).getD i false) = L[i] := by
        funext x
        simp [List.getD_eq_getElem?_getD, hi]
      simp only [List.foldl_nil]
      rw [this]
      exact hL _ (List.getElem_mem hi)
    · have : (fun x => (L.map fun f => f x).getD i false) = fun _ => false := by
        funext x
        rw [List.getD_eq_default]
        simp; omega
      simp only [List.foldl_nil]
      rw [this]
      exact hf
  | append_singleton gs g ih =>
    intro hgs
    obtain ⟨k, hk, S, hR, hS0, hw⟩ := ih (fun g' hg' => hgs g' (List.mem_append_left _ hg'))
    have hg := hgs g (List.mem_append_right _ (List.mem_singleton_self _))
    set W : (Fin 10 → Bool) → List Bool := fun x => gs.foldl stepF (L.map fun f => f x) with hW
    have hlen : ∀ x y, (W x).length = (W y).length := by
      intro x y
      apply len_foldl; simp
    let l : List T := g.inputs.map fun i => fun x => (W x).getD i false
    let F : T := fun x => g.op.eval (l.map fun f => f x)
    have hF : (fun x => g.op.eval (g.inputs.map fun i => (W x).getD i false)) = F := by
      funext x
      simp [F, l, List.map_map, Function.comp_def]
    have hlS : ∀ f ∈ l, f ∈ S := by
      intro f hf'
      simp only [l, List.mem_map] at hf'
      obtain ⟨i, _, rfl⟩ := hf'
      exact hw i
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
      have := hg.1
      simpa using this
    have hll : l.length ≤ 2 := by simp [l, hg.2]
    have hnew : ∀ S', S ⊆ S' → F ∈ S' → ∀ i,
        (fun x => ((gs ++ [g]).foldl stepF (L.map fun f => f x)).getD i false) ∈ S' := by
      intro S' hSS' hFS' i
      have e : ∀ x, (gs ++ [g]).foldl stepF (L.map fun f => f x) = W x ++
          [g.op.eval (g.inputs.map fun i => (W x).getD i false)] := by
        intro x
        simp [List.foldl_append, stepF, W]
      simp only [e]
      rcases Nat.lt_trichotomy i (W (fun _ => false)).length with h | h | h
      · have : (fun x => (W x ++ [g.op.eval (g.inputs.map fun i => (W x).getD i false)]).getD i
            false) = fun x => (W x).getD i false := by
          funext x
          rw [List.getD_append]
          rw [hlen x]; exact h
        rw [this]; exact hSS' (hw i)
      · have : (fun x => (W x ++ [g.op.eval (g.inputs.map fun i => (W x).getD i false)]).getD i
            false) = fun x => g.op.eval (g.inputs.map fun i => (W x).getD i false) := by
          funext x
          rw [List.getD_append_right]
          · rw [h, hlen x (fun _ => false)]; simp
          · rw [h, hlen x (fun _ => false)]
        rw [this, hF]; exact hFS'
      · have : (fun x => (W x ++ [g.op.eval (g.inputs.map fun i => (W x).getD i false)]).getD i
            false) = fun _ => false := by
          funext x
          rw [List.getD_eq_default]
          simp [hlen x (fun _ => false)]; omega
        rw [this]; exact hSS' (hS0 hf)
    by_cases hFS : F ∈ S
    · exact ⟨k, by simp; omega, S, hR, hS0, hnew S (subset_refl _) hFS⟩
    · refine ⟨k + 1, by simp; omega, Insert.insert F S, hstep k S g.op l hR hop hll hlS hFS,
        hS0.trans (Set.subset_insert _ _), hnew _ (Set.subset_insert _ _) (Set.mem_insert _ _)⟩

end PEqualNP.Outside.L_meta_17866

theorem PEqualNP.Outside.L_meta_17866 : (let x1 : Type := (Fin (10 : ℕ) → Bool) → Bool; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List x1) (x4 : Set x1) (x5 : ℕ → Set x1 → Prop), PEqualNP.MetaComplexity.FanInTwo x2 → (fun (x7 : Fin (10 : ℕ) → Bool) => Bool.false) ∈ x4 → (∀ x8 ∈ x3, x8 ∈ x4) → x5 (0 : ℕ) x4 → (∀ (x10 : ℕ) (x11 : Set x1) (x12 : PEqualNP.CircuitLowerBounds.GateOp) (x13 : List x1), x5 x10 x11 → x12 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x12 = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x12 = PEqualNP.CircuitLowerBounds.GateOp.not → x13.length ≤ (2 : ℕ) → (∀ x17 ∈ x13, x17 ∈ x11) → (fun (x18 : Fin (10 : ℕ) → Bool) => x12.eval (List.map (fun (x19 : x1) => x19 x18) x13)) ∉ x11 → x5 (x10 + (1 : ℕ)) (Insert.insert (fun (x19 : Fin (10 : ℕ) → Bool) => x12.eval (List.map (fun (x20 : x1) => x20 x19) x13)) x11)) → ∃ (x11 : ℕ) (x12 : Set x1), x11 ≤ x2.size ∧ x5 x11 x12 ∧ (fun (x13 : Fin (10 : ℕ) → Bool) => x2.eval (List.map (fun (x14 : x1) => x14 x13) x3)) ∈ x12) := by
  intro x1 C L S0 R hC hf hL h0 hstep
  obtain ⟨k, hk, S, hR, -, hw⟩ :=
    PEqualNP.Outside.L_meta_17866.key L S0 R hf hL h0 hstep C.gates hC
  exact ⟨k, S, hk, hR, hw C.output⟩
