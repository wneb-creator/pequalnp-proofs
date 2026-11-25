import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602Guard

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((hC j hj).2 i hi)]

lemma aob_of_ao (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) : AOB n C := by
  intro j hj
  have hm : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  exact ⟨hC.1 _ hm, hC.2.1 j hj⟩

lemma wv_mono (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (b t : Fin n → Bool) (hbt : ∀ i, b i = true → t i = true) :
    ∀ w, wv n C b w = true → wv n C t w = true := by
  have model := aob_of_ao n C hC
  intro w
  induction w using Nat.strong_induction_on with
  | h w ih =>
    intro hw
    by_cases low : w < n
    · rw [wv_input n C b w low] at hw
      rw [wv_input n C t w low]
      exact hbt _ hw
    by_cases valid : w < n + C.gates.length
    · let j := w - n
      have hj : j < C.gates.length := by omega
      have eqw : w = n+j := by omega
      rw [eqw, wv_rec n C b model j hj] at hw
      rw [eqw, wv_rec n C t model j hj]
      rcases (model j hj).1 with hand | hor
      · rw [hand] at hw ⊢
        simp only [GateOp.eval, List.all_map, List.all_eq_true] at hw ⊢
        intro i hi
        exact ih i (by have := (model j hj).2 i hi; omega) (hw i hi)
      · rw [hor] at hw ⊢
        simp only [GateOp.eval, List.any_map, List.any_eq_true] at hw ⊢
        obtain ⟨i,hi,yes⟩ := hw
        exact ⟨i,hi,ih i (by have := (model j hj).2 i hi; omega) yes⟩
    · have len : (C.wires (List.ofFn b)).length = n+C.gates.length := by
        rw [wires_eq, foldl_len, List.length_ofFn]
      have off : wv n C b w = false := by
        unfold wv
        apply List.getD_eq_default
        omega
      rw [off] at hw
      contradiction

lemma guarded_propagation : ∀ (n : ℕ) (C : Circuit), PEqualNP.TopForm.IsAO2 n C →
    ∀ b t : Fin n → Bool, (∀ i, b i=true → t i=true) →
    let v := fun (z : Fin n → Bool) (k : ℕ) => (C.wires (List.ofFn z)).getD k false
    (∀ i : Fin n, v t i.val=t i) ∧ ∀ j g i, C.gates[j]?=some g → i∈g.inputs → v t (n+j)=false →
      (g.op=GateOp.or ∨ ∀ k∈g.inputs, k≠i → v b k=true) → v t i=false := by
  intro n C hC b t hbt
  change (∀ i : Fin n, wv n C t i.val=t i) ∧ _
  constructor
  · intro i
    exact wv_input n C t i.val i.isLt
  · intro j g i hg hi hout guard
    have hj : j < C.gates.length := List.getElem?_eq_some_iff.mp hg |>.1
    have hgate : gateAt C j = g := by
      unfold gateAt
      simp [List.getD_eq_getElem?_getD,hg]
    have rec := wv_rec n C t (aob_of_ao n C hC) j hj
    rw [hgate] at rec
    change wv n C t (n+j) = false at hout
    rw [rec] at hout
    change wv n C t i = false
    apply Bool.eq_false_iff.mpr
    intro yes
    have hmem : g ∈ C.gates := List.mem_of_getElem? hg
    rcases hC.1 g hmem with hand | hor
    · have others : ∀ k∈g.inputs, k≠i → wv n C b k=true := by
        rcases guard with h | h
        · rw [hand] at h; contradiction
        · exact h
      have all : g.op.eval (g.inputs.map (wv n C t)) = true := by
        rw [hand]
        simp only [GateOp.eval,List.all_map,List.all_eq_true]
        intro k hk
        by_cases e : k=i
        · simpa [e] using yes
        · exact wv_mono n C hC b t hbt k (others k hk e)
      rw [all] at hout
      contradiction
    · have any : g.op.eval (g.inputs.map (wv n C t)) = true := by
        rw [hor]
        simp only [GateOp.eval,List.any_map,List.any_eq_true]
        exact ⟨i,hi,yes⟩
      rw [any] at hout
      contradiction

end PEqualNP.Outside.L_meta_2602Guard
