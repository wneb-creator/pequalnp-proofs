import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4887
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem pref_get {α : Type} (B L : List α) (j p : ℕ) (h : p < (B ++ L.take j).length) (d : α) :
    (B ++ L).getD p d = (B ++ L.take j)[p] := by
  have hpre : (B ++ L.take j) <+: (B ++ L) :=
    (List.prefix_append_right_inj B).2 (List.take_prefix j L)
  have hlen : p < (B ++ L).length := lt_of_lt_of_le h hpre.length_le
  rw [List.getD_eq_getElem _ _ hlen]
  exact (hpre.getElem h).symm

theorem ev2 (op : GateOp) (a b : ℕ) (w : List Bool) :
    op.eval (([a, b] : List ℕ).map fun i => w.getD i false) = op.eval [w.getD a false, w.getD b false] := rfl

end PEqualNP.Outside.L_meta_4887

open PEqualNP.Outside.L_meta_4887 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4887 : ∀ (x1 : ℕ) (x2 : List ((Fin x1 → Bool) → Bool)) (x3 : List (Bool → Set (Fin x1 → Bool))) (x4 : Bool → Set (Fin x1 → Bool)),   have x5 : List (Bool → Set (Fin x1 → Bool)) := List.map (fun (x5 : (Fin x1 → Bool) → Bool) (x6 : Bool) => {x7 : Fin x1 → Bool | x5 x7 = x6}) x2;   x4 ∈ x5 ++ x3 →     (∀ (x7 : Fin x3.length),         have x8 : List (Bool → Set (Fin x1 → Bool)) := x5 ++ List.take (↑x7) x3;         ∃ x9 ∈ x8, ∃ x10 ∈ x8, ∃ (x11 : Bool), ∀ (x12 : Bool), x3.get x7 x12 ⊆ if x12 = x11 then x9 x12 ∪ x10 x12 else x9 x12 ∩ x10 x12) →       ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ x3.length ∧ ∀ (x9 : Fin x1 → Bool) (x10 : Bool), x9 ∈ x4 x10 → x8.eval (List.map (fun (x12 : (Fin x1 → Bool) → Bool) => x12 x9) x2) = x10 := by
  intro n fs L T B hT hder
  classical
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Bool → Set (Fin n → Bool),
      A = fun i => (B ++ L).getD i (fun _ => ∅) := ⟨_, rfl⟩
  have hBl : B.length = fs.length := List.length_map _
  have H : ∀ j : Fin L.length, ∃ (p q : ℕ) (c : Bool), p < fs.length + j.1 ∧ q < fs.length + j.1 ∧
      ∀ b : Bool, A (fs.length + j.1) b ⊆ if b = c then A p b ∪ A q b else A p b ∩ A q b := by
    intro j
    obtain ⟨P, hP, Q, hQ, c, hc⟩ := hder j
    obtain ⟨p, hp, eP⟩ := List.getElem_of_mem hP
    obtain ⟨q, hq, eQ⟩ := List.getElem_of_mem hQ
    have hlen : (B ++ L.take j.1).length = fs.length + j.1 := by
      rw [List.length_append, List.length_take, hBl, Nat.min_eq_left (le_of_lt j.2)]
    refine ⟨p, q, c, by rw [← hlen]; exact hp, by rw [← hlen]; exact hq, ?_⟩
    have e1 : A p = P := by rw [hA]; show (B ++ L).getD p _ = P; rw [pref_get B L j.1 p hp]; exact eP
    have e2 : A q = Q := by rw [hA]; show (B ++ L).getD q _ = Q; rw [pref_get B L j.1 q hq]; exact eQ
    have e3 : A (fs.length + j.1) = L.get j := by
      rw [hA]
      show (B ++ L).getD (fs.length + j.1) _ = L.get j
      rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hBl]; exact Nat.add_lt_add_left j.2 _),
        List.getElem_append_right (by rw [hBl]; exact Nat.le_add_right _ _)]
      show L[fs.length + j.1 - B.length] = L[j.1]
      congr 1
      rw [hBl]; omega
    rw [e1, e2, e3]
    exact hc
  choose p q c hp hq hsub using H
  obtain ⟨gates, hg⟩ : ∃ gates : List Gate, gates = List.ofFn (fun j : Fin L.length =>
      (⟨if c j = true then GateOp.or else GateOp.and, [p j, q j]⟩ : Gate)) := ⟨_, rfl⟩
  have hgl : gates.length = L.length := by rw [hg]; simp
  have inv : ∀ (x : Fin n → Bool) (k : ℕ), k ≤ L.length → ∀ i, i < fs.length + k → ∀ b : Bool,
      x ∈ A i b → (wf (gates.take k) (fs.map fun f => f x)).getD i false = b := by
    intro x k
    induction k with
    | zero =>
      intro _ i hi b hx
      have hi' : i < fs.length := hi
      show (fs.map fun f => f x).getD i false = b
      rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hi'), List.getElem_map]
      rw [hA] at hx
      have e : (B ++ L).getD i (fun _ => ∅) = fun b => {y : Fin n → Bool | fs[i] y = b} := by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hBl]; omega),
          List.getElem_append_left (by rw [hBl]; exact hi')]
        show (fs.map _)[i] = _
        rw [List.getElem_map]
      have hx' : x ∈ (B ++ L).getD i (fun _ => ∅) b := hx
      rw [e] at hx'
      exact hx'
    | succ k ih =>
      intro hk i hi b hx
      have hk' : k < L.length := hk
      have ih' := ih (le_of_lt hk')
      have hkg : k < gates.length := by rw [hgl]; exact hk'
      have hlenP : (wf (gates.take k) (fs.map fun f => f x)).length = fs.length + k := by
        rw [wf_len, List.length_map, List.length_take, Nat.min_eq_left (le_of_lt hkg)]
      rw [List.take_succ_eq_append_getElem hkg, wf_snoc]
      by_cases hik : i < fs.length + k
      · rw [getD_snoc_lt _ _ _ (by rw [hlenP]; exact hik)]
        exact ih' i hik b hx
      · have hieq : i = fs.length + k := by omega
        rw [hieq, ← hlenP, getD_snoc_eq]
        have hgk : gates[k] = (⟨if c ⟨k, hk'⟩ = true then GateOp.or else GateOp.and,
            [p ⟨k, hk'⟩, q ⟨k, hk'⟩]⟩ : Gate) := by
          simp [hg]
        rw [hgk]
        show (if c ⟨k, hk'⟩ = true then GateOp.or else GateOp.and).eval
          (([p ⟨k, hk'⟩, q ⟨k, hk'⟩] : List ℕ).map fun i =>
            (wf (gates.take k) (fs.map fun f => f x)).getD i false) = b
        rw [ev2]
        rw [hieq] at hx
        have hs := hsub ⟨k, hk'⟩ b hx
        have ihp := ih' (p ⟨k, hk'⟩) (hp ⟨k, hk'⟩)
        have ihq := ih' (q ⟨k, hk'⟩) (hq ⟨k, hk'⟩)
        cases hcb : c ⟨k, hk'⟩ <;> cases b <;> rw [hcb] at hs
        · rw [if_pos rfl] at hs
          rcases hs with h1 | h1
          · rw [ihp false h1]; simp [GateOp.eval]
          · rw [ihq false h1]; simp [GateOp.eval]
        · rw [if_neg (by decide)] at hs
          rw [ihp true hs.1, ihq true hs.2]; simp [GateOp.eval]
        · rw [if_neg (by decide)] at hs
          rw [ihp false hs.1, ihq false hs.2]; simp [GateOp.eval]
        · rw [if_pos rfl] at hs
          rcases hs with h1 | h1
          · rw [ihp true h1]; simp [GateOp.eval]
          · rw [ihq true h1]; simp [GateOp.eval]
  obtain ⟨t, ht, eT⟩ := List.getElem_of_mem hT
  refine ⟨⟨gates, t⟩, ?_, le_of_eq hgl, ?_⟩
  · intro g hgm
    rw [hg] at hgm
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hgm
    refine ⟨?_, by simp⟩
    show (if c j = true then GateOp.or else GateOp.and) ∈ ({GateOp.and, GateOp.or} : Set GateOp)
    split <;> simp
  · intro x b hx
    have hlt : t < fs.length + L.length := by
      rw [List.length_append, hBl] at ht; exact ht
    have hAt : A t = T := by
      rw [hA]
      show (B ++ L).getD t _ = T
      rw [List.getD_eq_getElem _ _ ht]; exact eT
    have h := inv x L.length (le_refl _) t hlt b (by rw [hAt]; exact hx)
    rw [List.take_of_length_le (le_of_eq hgl)] at h
    exact h
