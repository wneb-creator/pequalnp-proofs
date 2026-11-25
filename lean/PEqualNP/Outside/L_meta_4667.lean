import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4667

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_len : ∀ (gs : List Gate) (l : List Bool), (gs.foldl step l).length = l.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro l; simp
  | cons g gs ih =>
    intro l
    rw [List.foldl_cons, ih]
    simp [step]
    omega

theorem foldl_prefix : ∀ (gs : List Gate) (l : List Bool), l <+: gs.foldl step l := by
  intro gs
  induction gs with
  | nil => intro l; simp
  | cons g gs ih =>
    intro l
    exact (List.prefix_append l _).trans (ih _)

theorem getD_of_prefix {p q : List Bool} (h : p <+: q) {i : ℕ} (hi : i < p.length) :
    q.getD i false = p.getD i false := by
  obtain ⟨t, rfl⟩ := h
  exact List.getD_append _ _ _ _ hi

theorem foldl_val : ∀ (gs : List Gate) (l : List Bool) (j : ℕ) (hj : j < gs.length),
    (gs.foldl step l).getD (l.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < l.length + j then (gs.foldl step l).getD i false else false) := by
  intro gs
  induction gs with
  | nil => intro l j hj; simp at hj
  | cons g gs ih =>
    intro l j hj
    rw [List.foldl_cons]
    rcases j with _ | j
    · have hlt : l.length < (step l g).length := by simp [step]
      rw [Nat.add_zero, getD_of_prefix (foldl_prefix gs _) hlt]
      simp only [List.getElem_cons_zero]
      have hlast : (step l g).getD l.length false = g.op.eval (g.inputs.map fun i => l.getD i false) := by
        simp [step, List.getD_eq_getElem?_getD]
      rw [hlast]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < l.length
      · rw [if_pos hi, getD_of_prefix (foldl_prefix gs _) (by simp [step]; omega)]
        simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi, List.getD_eq_default _ _ (by omega)]
    · have hj' : j < gs.length := by simp at hj; omega
      have h := ih (step l g) j hj'
      have hlen : (step l g).length = l.length + 1 := by simp [step]
      rw [hlen] at h
      rw [show l.length + (j + 1) = l.length + 1 + j by omega, h]
      rfl

end PEqualNP.Outside.L_meta_4667

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_4667 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     ∀ (x3 : Fin (24 : ℕ) → List Bool),       (∀ (x4 : Fin (24 : ℕ)), (x3 x4).length = (11 : ℕ)) →         have x5 : List (Fin (24 : ℕ) → Bool) := (List.ofFn fun (x5 : Fin (11 : ℕ)) (x6 : Fin (24 : ℕ)) => (x3 x6).getD (↑x5) Bool.false) ++ [fun (x5 : Fin (24 : ℕ)) => Bool.false, fun (x5 : Fin (24 : ℕ)) => Bool.true];         ∃ (x6 : List (Fin (24 : ℕ) → Bool)),           x6.length ≤ x1.size ∧             (fun (x7 : Fin (24 : ℕ)) => x1.eval (x3 x7)) ∈ x5 ++ x6 ∧               ∀ (x7 : Fin x6.length),                 have x8 : List (Fin (24 : ℕ) → Bool) := x5 ++ List.take (↑x7) x6;                 (∃ x9 ∈ x8, x6.get x7 = fun (x10 : Fin (24 : ℕ)) => !x9 x10) ∨ ∃ x9 ∈ x8, ∃ x10 ∈ x8, (x6.get x7 = fun (x11 : Fin (24 : ℕ)) => x9 x11 && x10 x11) ∨ x6.get x7 = fun (x11 : Fin (24 : ℕ)) => x9 x11 || x10 x11 := by
  intro C hf X hX
  dsimp only
  have hWlen : ∀ p, (C.wires (X p)).length = 11 + C.gates.length := by
    intro p
    rw [PEqualNP.Outside.L_meta_4667.wires_eq, PEqualNP.Outside.L_meta_4667.foldl_len, hX p]
  have hWpre : ∀ p i, i < 11 → (C.wires (X p)).getD i false = (X p).getD i false := by
    intro p i hi
    rw [PEqualNP.Outside.L_meta_4667.wires_eq]
    exact PEqualNP.Outside.L_meta_4667.getD_of_prefix
      (PEqualNP.Outside.L_meta_4667.foldl_prefix _ _) (by rw [hX p]; exact hi)
  have hcoord : ∀ i, i < 11 → (fun p : Fin 24 => (X p).getD i false) ∈
      ((List.ofFn fun (x5 : Fin 11) (x6 : Fin 24) => (X x6).getD (↑x5) false) ++
        [fun (_ : Fin 24) => false, fun (_ : Fin 24) => true]) := by
    intro i hi
    apply List.mem_append_left
    rw [List.mem_ofFn]
    exact ⟨⟨i, hi⟩, rfl⟩
  have hfalse : (fun (_ : Fin 24) => false) ∈
      ((List.ofFn fun (x5 : Fin 11) (x6 : Fin 24) => (X x6).getD (↑x5) false) ++
        [fun (_ : Fin 24) => false, fun (_ : Fin 24) => true]) := by simp
  have htrue : (fun (_ : Fin 24) => true) ∈
      ((List.ofFn fun (x5 : Fin 11) (x6 : Fin 24) => (X x6).getD (↑x5) false) ++
        [fun (_ : Fin 24) => false, fun (_ : Fin 24) => true]) := by simp
  refine ⟨List.ofFn (fun j : Fin C.gates.length => fun p : Fin 24 => (C.wires (X p)).getD (11 + j.val) false),
    by simp [PEqualNP.CircuitLowerBounds.Circuit.size], ?_, ?_⟩
  · -- the output signature
    by_cases ho : C.output < 11
    · apply List.mem_append_left
      have h : (fun p => C.eval (X p)) = (fun p => (X p).getD C.output false) := by
        funext p
        exact hWpre p _ ho
      rw [h]
      exact hcoord _ ho
    · by_cases ho2 : C.output < 11 + C.gates.length
      · apply List.mem_append_right
        rw [List.mem_ofFn]
        refine ⟨⟨C.output - 11, by omega⟩, ?_⟩
        funext p
        show (C.wires (X p)).getD (11 + (C.output - 11)) false = C.eval (X p)
        rw [show 11 + (C.output - 11) = C.output by omega]
        rfl
      · apply List.mem_append_left
        have h : (fun p => C.eval (X p)) = (fun (_ : Fin 24) => false) := by
          funext p
          exact List.getD_eq_default _ _ (by rw [hWlen p]; omega)
        rw [h]
        exact hfalse
  · intro k
    have hk : k.val < C.gates.length := by simpa using k.isLt
    have hget : (List.ofFn (fun j : Fin C.gates.length => fun p : Fin 24 =>
        (C.wires (X p)).getD (11 + j.val) false)).get k =
        fun p => (C.wires (X p)).getD (11 + k.val) false := by simp
    rw [hget]
    have hval : ∀ p, (C.wires (X p)).getD (11 + k.val) false =
        C.gates[k.val].op.eval (C.gates[k.val].inputs.map fun i =>
          if i < 11 + k.val then (C.wires (X p)).getD i false else false) := by
      intro p
      have h := PEqualNP.Outside.L_meta_4667.foldl_val C.gates (X p) k.val hk
      rw [hX p] at h
      rw [PEqualNP.Outside.L_meta_4667.wires_eq]
      exact h
    have hop : ∀ i, (fun p : Fin 24 => if i < 11 + k.val then (C.wires (X p)).getD i false else false) ∈
        ((List.ofFn fun (x5 : Fin 11) (x6 : Fin 24) => (X x6).getD (↑x5) false) ++
          [fun (_ : Fin 24) => false, fun (_ : Fin 24) => true]) ++
        List.take k.val (List.ofFn (fun j : Fin C.gates.length => fun p : Fin 24 =>
          (C.wires (X p)).getD (11 + j.val) false)) := by
      intro i
      by_cases hi : i < 11
      · apply List.mem_append_left
        have h : (fun p : Fin 24 => if i < 11 + k.val then (C.wires (X p)).getD i false else false) =
            (fun p => (X p).getD i false) := by
          funext p
          rw [if_pos (by omega), hWpre p i hi]
        rw [h]
        exact hcoord i hi
      · by_cases hi2 : i < 11 + k.val
        · apply List.mem_append_right
          rw [List.mem_iff_getElem]
          refine ⟨i - 11, by simp; omega, ?_⟩
          funext p
          simp only [List.getElem_take, List.getElem_ofFn]
          rw [if_pos hi2, show 11 + (i - 11) = i by omega]
        · apply List.mem_append_left
          have h : (fun p : Fin 24 => if i < 11 + k.val then (C.wires (X p)).getD i false else false) =
              (fun (_ : Fin 24) => false) := by
            funext p
            rw [if_neg hi2]
          rw [h]
          exact hfalse
    have hmem : C.gates[k.val] ∈ C.gates := List.getElem_mem hk
    have hT : (fun (_ : Fin 24) => true) ∈ ((List.ofFn fun (x5 : Fin 11) (x6 : Fin 24) => (X x6).getD (↑x5) false) ++
          [fun (_ : Fin 24) => false, fun (_ : Fin 24) => true]) ++
        List.take k.val (List.ofFn (fun j : Fin C.gates.length => fun p : Fin 24 =>
          (C.wires (X p)).getD (11 + j.val) false)) := List.mem_append_left _ htrue
    have hF : (fun (_ : Fin 24) => false) ∈ ((List.ofFn fun (x5 : Fin 11) (x6 : Fin 24) => (X x6).getD (↑x5) false) ++
          [fun (_ : Fin 24) => false, fun (_ : Fin 24) => true]) ++
        List.take k.val (List.ofFn (fun j : Fin C.gates.length => fun p : Fin 24 =>
          (C.wires (X p)).getD (11 + j.val) false)) := List.mem_append_left _ hfalse
    have hfg := hf _ hmem
    generalize C.gates[k.val] = g at hval hfg
    obtain ⟨op, ins⟩ := g
    obtain ⟨hopset, hlen⟩ := hfg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hopset
    have hfun : (fun p => (C.wires (X p)).getD (11 + k.val) false) = fun p =>
        op.eval (ins.map fun i => if i < 11 + k.val then (C.wires (X p)).getD i false else false) := by
      funext p
      exact hval p
    rw [hfun]
    simp only at hlen
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · rcases hopset with rfl | rfl | rfl
      · exact Or.inr ⟨_, hT, _, hT, Or.inl (by funext p; simp [GateOp.eval])⟩
      · exact Or.inr ⟨_, hF, _, hF, Or.inr (by funext p; simp [GateOp.eval])⟩
      · exact Or.inl ⟨_, hF, by funext p; simp [GateOp.eval]⟩
    · rcases hopset with rfl | rfl | rfl
      · exact Or.inr ⟨_, hop a, _, hop a, Or.inl (by funext p; simp [GateOp.eval])⟩
      · exact Or.inr ⟨_, hop a, _, hop a, Or.inr (by funext p; simp [GateOp.eval])⟩
      · exact Or.inl ⟨_, hop a, by funext p; simp [GateOp.eval]⟩
    · rcases hopset with rfl | rfl | rfl
      · exact Or.inr ⟨_, hop a, _, hop b, Or.inl (by funext p; simp [GateOp.eval])⟩
      · exact Or.inr ⟨_, hop a, _, hop b, Or.inr (by funext p; simp [GateOp.eval])⟩
      · exact Or.inl ⟨_, hop a, by funext p; simp [GateOp.eval]⟩
    · simp at hlen
