import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3787.Embedding

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) :
    (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

lemma relabel_size (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) :
    (relabel n m π C).size = C.size := by
  simp [relabel, Circuit.size]

lemma relabel_monotone (n m : ℕ) (π : Fin n → Fin m) (C : Circuit)
    (hC : Monotone2 C) : Monotone2 (relabel n m π C) := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
  exact ⟨(hC g0 hg0).1, by simpa [relGate] using (hC g0 hg0).2⟩

lemma relabel_eval (n m : ℕ) (π : Fin n → Fin m) (C : Circuit)
    (x : Fin m → Bool) :
    (relabel n m π C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ π)) := by
  exact (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

lemma relabel_valid (n m : ℕ) (π : Fin n → Fin m) (C : Circuit)
    (hC : C.output < n + C.size) :
    (relabel n m π C).output < m + (relabel n m π C).size := by
  rw [relabel_size]
  change wmap n m π C.output < m + C.size
  unfold wmap
  split
  · have := (π ⟨C.output, by assumption⟩).2
    omega
  · omega

def selection : List (Fin 26) :=
  [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

def pick : Fin 21 → Fin 26 :=
  ![2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

lemma pick_map (x : Fin 26 → Bool) :
    List.ofFn (x ∘ pick) = selection.map x := by
  rfl

def embed (C : Circuit) : Circuit := relabel 21 26 pick C

lemma embed_size (C : Circuit) : (embed C).size = C.size :=
  relabel_size 21 26 pick C

lemma embed_monotone (C : Circuit) (hC : Monotone2 C) : Monotone2 (embed C) :=
  relabel_monotone 21 26 pick C hC

lemma embed_valid (C : Circuit) (hC : C.output < 21 + C.size) :
    (embed C).output < 26 + (embed C).size :=
  relabel_valid 21 26 pick C hC

lemma embed_eval (C : Circuit) (x : Fin 26 → Bool) :
    (embed C).eval (List.ofFn x) = C.eval (selection.map x) := by
  rw [embed, relabel_eval, pick_map]

end PEqualNP.Outside.L_meta_3787.Embedding
