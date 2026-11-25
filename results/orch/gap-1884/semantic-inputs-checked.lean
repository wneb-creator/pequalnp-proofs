import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884.Semantic
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def neighbor (i : Fin 10) : Fin 10 :=
  ([1,0,1,2,3,7,9,5,6,7] : List (Fin 10)).getD i.val 0

def lowProbe (i : Fin 10) : Fin 10 → Bool := fun v => decide (v=neighbor i)
def highProbe (i : Fin 10) : Fin 10 → Bool := fun v => decide (v=neighbor i ∨ v=i)

lemma probe_values : ∀ i : Fin 10, target (lowProbe i)=false ∧ target (highProbe i)=true := by
  decide +kernel

lemma probe_agreement (i v : Fin 10) (h : v≠i) : lowProbe i v=highProbe i v := by
  simp [lowProbe,highProbe,h]

lemma map_covers_nonzero (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (hcompute : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)])=target x) :
    ∀ i : Fin 10,i≠0 → ∃ j,σ j=i := by
  intro i hi
  by_contra hn
  have hmap : ∀ j,σ j≠i := by simpa using hn
  have hfn : lowProbe i ∘ σ=highProbe i ∘ σ := by
    funext j
    exact probe_agreement i (σ j) (hmap j)
  have h0 := probe_agreement i 0 (Ne.symm hi)
  have he : C.eval (List.ofFn (lowProbe i ∘ σ) ++ [u (lowProbe i 0)]) =
      C.eval (List.ofFn (highProbe i ∘ σ) ++ [u (highProbe i 0)]) := by rw [hfn,h0]
  rw [hcompute,hcompute,(probe_values i).1,(probe_values i).2] at he
  cases he

lemma map_surjective_or_missing_zero (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (hcompute : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)])=target x) :
    Function.Surjective σ ∨ ∀ j,σ j≠0 := by
  by_cases hz : ∃ j,σ j=0
  · left
    intro i
    by_cases hi : i=0
    · simpa [hi] using hz
    · exact map_covers_nonzero C σ u hcompute i hi
  · right
    simpa using hz

lemma missing_zero_unary_nonconstant (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (hcompute : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)])=target x)
    (hmissing : ∀ j,σ j≠0) : u false≠u true := by
  intro hu
  have hfn : lowProbe 0 ∘ σ=highProbe 0 ∘ σ := by
    funext j
    exact probe_agreement 0 (σ j) (hmissing j)
  have hlo : lowProbe 0 0=false := by decide
  have hhi : highProbe 0 0=true := by decide
  have he : C.eval (List.ofFn (lowProbe 0 ∘ σ) ++ [u (lowProbe 0 0)]) =
      C.eval (List.ofFn (highProbe 0 ∘ σ) ++ [u (highProbe 0 0)]) := by
    rw [hfn,hlo,hhi,hu]
  rw [hcompute,hcompute,(probe_values 0).1,(probe_values 0).2] at he
  cases he

lemma nonconstant_unary (u : Bool → Bool) (h : u false≠u true) :
    u=id ∨ u=Bool.not := by
  cases h0 : u false <;> cases h1 : u true
  · exact (h (h0.trans h1.symm)).elim
  · left
    funext b
    cases b <;> assumption
  · right
    funext b
    cases b <;> assumption
  · exact (h (h0.trans h1.symm)).elim

lemma input_classification (C : Circuit) (σ : Fin 10 → Fin 10) (u : Bool → Bool)
    (hcompute : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)])=target x) :
    Function.Surjective σ ∨ ((∀ j,σ j≠0) ∧ (u=id ∨ u=Bool.not)) := by
  rcases map_surjective_or_missing_zero C σ u hcompute with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h,nonconstant_unary u (missing_zero_unary_nonconstant C σ u hcompute h)⟩

end PEqualNP.Outside.L_meta_1884.Semantic
