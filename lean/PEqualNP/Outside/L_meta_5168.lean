import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5168

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edge (x : Fin 9 → Bool) :=
  ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
    List (Fin 9 × Fin 9)).any fun e => x e.1 && x e.2

def swap : Fin 9 → Fin 9 := ![0,5,8,3,4,1,7,6,2]

def representatives : List Nat := [1,2,3,4,6,11,12,13,14,15,16,17,21,22,24,25,26,31,33,42,61]

lemma orbits : ∀ a b : Fin 9, a < b → 9*a.val+b.val ∈ representatives ∨
    9*(min (swap a) (swap b)).val+(max (swap a) (swap b)).val ∈ representatives := by decide +kernel

lemma preserves (x : Fin 9 → Bool) : edge (x ∘ swap) = edge x := by
  simp only [edge,List.any_cons,List.any_nil,Bool.or_false,Function.comp_apply]
  change ((x 0 && x 5) || ((x 5 && x 8) || ((x 8 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 1) || ((x 5 && x 7) || ((x 8 && x 6) || ((x 3 && x 2) || ((x 1 && x 6) || ((x 7 && x 2) || (x 2 && x 1)))))))))))) = ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 5 && x 7) || ((x 6 && x 8) || (x 8 && x 5))))))))))))
  ac_rfl

lemma relabel (C : Circuit) (mono : FanInTwo C) (p : Fin 9 → Fin 9) :
    ∃ B : Circuit, FanInTwo B ∧ B.size = C.size ∧ ∀ (x : Fin 9 → Bool) (a b : Bool),
      B.eval (List.ofFn x ++ [a,b]) = C.eval (List.ofFn (x ∘ p) ++ [a,b]) := by
  let mapGate (σ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map σ⟩
  let rewired (σ : ℕ → ℕ) (C : Circuit) : Circuit := ⟨C.gates.map (mapGate σ),σ C.output⟩

  have fan {C : Circuit} (σ : ℕ → ℕ) (h : FanInTwo C) : FanInTwo (rewired σ C) := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact ⟨(h a ha).1,by simpa [mapGate] using (h a ha).2⟩

  have run {cut : ℕ} (σ : ℕ → ℕ) (raw : ∀ i<cut, σ i<cut) (later : ∀ i, cut ≤ i → σ i=i)
      (gs : List Gate) (x y : List Bool) (len : x.length=y.length) (lo : cut ≤ x.length)
      (agree : ∀ i, y.getD (σ i) false = x.getD i false) :
      ∀ i, ((Circuit.mk (gs.map (mapGate σ)) 0).wires y).getD (σ i) false =
        ((Circuit.mk gs 0).wires x).getD i false := by
    induction gs generalizing x y with
    | nil => exact agree
    | cons g gs ih =>
      let b := g.op.eval (g.inputs.map (fun i => x.getD i false))
      have same : (mapGate σ g).op.eval ((mapGate σ g).inputs.map (fun i => y.getD i false)) = b := by
        simp only [b,mapGate,List.map_map,Function.comp_def,agree]
      change ∀ i, ((Circuit.mk (gs.map (mapGate σ)) 0).wires (y++[_])).getD (σ i) false =
        ((Circuit.mk gs 0).wires (x++[b])).getD i false
      rw [same]
      apply ih _ _ (by simp [len]) (by simp; omega)
      intro i
      by_cases hi : i<x.length
      · have hsi : σ i<y.length := by
          by_cases hr : i<cut
          · have := raw i hr; omega
          · rw [later i (by omega)]; omega
        rw [List.getD_append _ _ _ _ hsi, List.getD_append _ _ _ _ hi]
        exact agree i
      · rw [later i (by omega), List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), len]

  have evalMap {cut : ℕ} (σ : ℕ → ℕ) (raw : ∀ i<cut, σ i<cut) (later : ∀ i, cut ≤ i → σ i=i)
      (C : Circuit) (x y : List Bool) (len : x.length=y.length) (lo : cut ≤ x.length)
      (agree : ∀ i, y.getD (σ i) false = x.getD i false) :
      (rewired σ C).eval y = C.eval x :=
    run σ raw later C.gates x y len lo agree C.output

  let rawMap (p : Fin 9 → Fin 9) (i : ℕ) := if h : i < 9 then (p ⟨i,h⟩).val else i
  let σ := rawMap p
  refine ⟨rewired σ C,fan σ mono,?_,?_⟩
  · change (C.gates.map (mapGate σ)).length = C.gates.length
    exact List.length_map (mapGate σ)
  · intro x a b
    have small (i : ℕ) (hi : i<9) : σ i < 9 := by simp [σ,rawMap,hi]
    have late (i : ℕ) (hi : 9 ≤ i) : σ i=i := by simp [σ,rawMap,Nat.not_lt.mpr hi]
    apply evalMap σ small late C _ _ (by simp) (by simp)
    intro i
    by_cases h : i<9
    · have h1 : σ i < (List.ofFn x).length := by simpa using small i h
      have h2 : i < (List.ofFn (x ∘ p)).length := by simpa using h
      rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2,
        List.getD_eq_getElem _ _ h1,List.getD_eq_getElem _ _ h2]
      simp only [List.getElem_ofFn,Function.comp_apply]
      congr 1
      apply Fin.ext
      exact dite_eq_left h
    · have hn : 9 ≤ i := by omega
      rw [late i hn, List.getD_append_right _ _ _ _ (by simpa using hn),
        List.getD_append_right _ _ _ _ (by simpa using hn)]
      simp
lemma reorder (x : Fin 9 → Bool) (a b : Fin 9) :
    (x (min a b) || x (max a b)) = (x a || x b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h,max_eq_right h]
  · rw [min_eq_right h,max_eq_left h,Bool.or_comm]

end PEqualNP.Outside.L_meta_5168

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_5168

theorem PEqualNP.Outside.L_meta_5168 :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; have x2 : Fin (9 : ℕ) → Fin (9 : ℕ) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x5 ++ [!x5 (0 : Fin (9 : ℕ)), x5 x2 || x5 x3]) = x1 x5; ∀ (x3 x4 : Fin (9 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), x3 < x4 → PEqualNP.MetaComplexity.FanInTwo x5 → x5.size ≤ (13 : ℕ) → x2 x3 x4 x5 → ∃ (x10 : Fin (9 : ℕ)) (x11 : Fin (9 : ℕ)) (x12 : PEqualNP.CircuitLowerBounds.Circuit), (9 : ℕ) * ↑x10 + ↑x11 ∈ [(1 : ℕ), (2 : ℕ), (3 : ℕ), (4 : ℕ), (6 : ℕ), (11 : ℕ), (12 : ℕ), (13 : ℕ), (14 : ℕ), (15 : ℕ), (16 : ℕ), (17 : ℕ), (21 : ℕ), (22 : ℕ), (24 : ℕ), (25 : ℕ), (26 : ℕ), (31 : ℕ), (33 : ℕ), (42 : ℕ), (61 : ℕ)] ∧ PEqualNP.MetaComplexity.FanInTwo x12 ∧ x12.size ≤ (13 : ℕ) ∧ x2 x10 x11 x12 := by
  change ∀ (a b : Fin 9) (C : Circuit), a < b → FanInTwo C → C.size ≤ 13 →
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0,x a || x b]) = edge x) →
    ∃ (a' b' : Fin 9) (D : Circuit), 9*a'.val+b'.val ∈ representatives ∧ FanInTwo D ∧ D.size ≤ 13 ∧
      ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0,x a' || x b']) = edge x
  intro a b C ab fan size correct
  rcases orbits a b ab with ok | ok
  · exact ⟨a,b,C,ok,fan,size,correct⟩
  obtain ⟨D,df,ds,sim⟩ := relabel C fan swap
  refine ⟨min (swap a) (swap b),max (swap a) (swap b),D,ok,df,ds.trans_le size,?_⟩
  intro x
  rw [reorder,sim]
  change C.eval (List.ofFn (x ∘ swap) ++ [!(x ∘ swap) 0,(x ∘ swap) a || (x ∘ swap) b]) = edge x
  exact (correct (x ∘ swap)).trans (preserves x)
