import constant_sweep
import one_not_semantics

namespace PEqualNP.Outside.L_meta_2592_aux.OneNotCompile

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open ConstantSweep

def seed (m : ℕ) (b : Bool) : List Ref :=
  List.ofFn (fun i : Fin m => Sum.inr i.val) ++ [Sum.inl b]

lemma seed_related (w : List Bool) (b : Bool) :
    related (seed w.length b) w (w ++ [b]) := by
  constructor
  · dsimp only [seed]
    rw [List.map_append, List.map_ofFn]
    simp only [List.map_cons, List.map_nil, value]
    congr 1
    symm
    change List.ofFn (fun i : Fin w.length => w.getD i.val false) = w
    have h : (fun i : Fin w.length => w.getD i.val false) =
        (fun i : Fin w.length => w[i.val]) := by
      funext i
      exact List.getD_eq_getElem _ _ i.isLt
    rw [h]
    exact List.ofFn_getElem
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
      exact i.isLt
    · obtain rfl := List.mem_singleton.mp hr
      trivial

lemma seed_last (m : ℕ) (b : Bool) : read (seed m b) m = .inl b := by
  simpa only [ConstantSweep.read, seed, List.length_ofFn] using
    (getD_last (List.ofFn fun i : Fin m => (Sum.inr i.val : Ref)) (.inl b) fixed)

lemma compile_constant_suffix {n : ℕ} (F : (Fin n → Bool) → Bool)
    (pre suffix : List Gate) (outIdx : ℕ) (b : Bool)
    (hs : ∀ g ∈ suffix, good g)
    (correct : ∀ x, (run suffix (run pre (List.ofFn x) ++ [b])).getD outIdx false = F x)
    (nonconstant : ∃ x y, F x ≠ F y) :
    ∃ (out : List Gate) (j : ℕ),
      (∀ g ∈ out, good g) ∧
      out.length + (suffix.filter (touched {n + pre.length})).length ≤ suffix.length ∧
      ∀ x, (Circuit.mk (pre ++ out) j).eval (List.ofFn x) = F x := by
  let m := n + pre.length
  obtain ⟨out, refs, hout, hsize, hsem⟩ :=
    sweep {m} suffix hs (seed m b) m
      (by
        intro i hi
        have : i = m := by simpa using hi
        subst i
        simp [seed])
      (by
        intro i hi
        have : i = m := by simpa using hi
        subst i
        exact ⟨b, seed_last _ _⟩)
  have result : ∀ x, value (run out (run pre (List.ofFn x))) (read refs outIdx) = F x := by
    intro x
    have hw : (run pre (List.ofFn x)).length = m := by simp [run_length, m]
    have hr : related (seed m b) (run pre (List.ofFn x)) (run pre (List.ofFn x) ++ [b]) := by
      simpa only [hw] using seed_related (run pre (List.ofFn x)) b
    exact (read_value (hsem _ _ hw hr) outIdx).trans (correct x)
  cases he : read refs outIdx with
  | inl c =>
    obtain ⟨x,y,hne⟩ := nonconstant
    have hx := result x
    have hy := result y
    simp only [he, value] at hx hy
    exact False.elim (hne (hx.symm.trans hy))
  | inr j =>
    refine ⟨out,j,hout,hsize,?_⟩
    intro x
    have h := result x
    simp only [he, value] at h
    change (run (pre ++ out) (List.ofFn x)).getD j false = F x
    rw [run_append]
    exact h

lemma eliminate_dominated_not {n : ℕ} (F g : (Fin n → Bool) → Bool)
    (pre suffix : List Gate) (outIdx : ℕ)
    (hs : Monotone2 (Circuit.mk suffix outIdx))
    (correct : ∀ x, F x = (Circuit.mk suffix outIdx).eval
      (run pre (List.ofFn x) ++ [!(g x)]))
    (below : ∀ x, g x ≤ F x)
    (nonconstant : ∃ x y, F x ≠ F y) :
    ∃ (out : List Gate) (j : ℕ),
      (∀ q ∈ out, good q) ∧
      out.length + (suffix.filter (touched {n + pre.length})).length ≤ suffix.length ∧
      ∀ x, (Circuit.mk (pre ++ out) j).eval (List.ofFn x) = F x := by
  apply compile_constant_suffix F pre suffix outIdx true ?_ ?_ nonconstant
  · intro q hq
    have h := hs q hq
    constructor
    · rcases h.1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact h.2
  · exact OneNot.replace_not_from_below F g (fun x => run pre (List.ofFn x))
      (Circuit.mk suffix outIdx) hs correct below

end PEqualNP.Outside.L_meta_2592_aux.OneNotCompile
