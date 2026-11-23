import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_670_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

lemma mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

lemma mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

lemma agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

lemma agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

lemma cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

lemma cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

lemma cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

lemma dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

def graph (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

lemma all_inputs_essential (i : Fin 9) :
    ∃ x : Fin 9 → Bool, graph (Function.update x i (!x i)) ≠ graph x := by
  fin_cases i
  · exact ⟨fun j => decide (j = 1), by decide⟩
  · exact ⟨fun j => decide (j = 0), by decide⟩
  · exact ⟨fun j => decide (j = 1), by decide⟩
  · exact ⟨fun j => decide (j = 2), by decide⟩
  · exact ⟨fun j => decide (j = 0), by decide⟩
  · exact ⟨fun j => decide (j = 0), by decide⟩
  · exact ⟨fun j => decide (j = 1), by decide⟩
  · exact ⟨fun j => decide (j = 2), by decide⟩
  · exact ⟨fun j => decide (j = 3), by decide⟩

lemma dependency_lower (s : ℕ) (h : HasCircuitSize 9 graph s) : 8 ≤ s := by
  have := dep_lower 9 graph all_inputs_essential s h
  omega

end PEqualNP.Outside.L_meta_670_aux


namespace PEqualNP.Outside.L_meta_670_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev NGate := Fin 3 × Nat × Nat

def clamp (n i : Nat) : Nat := min i n

def normalizedGate (n : Nat) (g : Gate) : NGate :=
  match g.op, g.inputs with
  | .and, [] => (2, n, n)
  | .and, [a] => (0, clamp n a, clamp n a)
  | .and, a :: b :: _ => (0, clamp n a, clamp n b)
  | .or, [] => (1, n, n)
  | .or, [a] => (1, clamp n a, clamp n a)
  | .or, a :: b :: _ => (1, clamp n a, clamp n b)
  | .not, [] => (2, n, n)
  | .not, a :: _ => (2, clamp n a, n)
  | _, _ => (1, n, n)

def normalizedEval (w : List Bool) (g : NGate) : Bool :=
  if g.1 = 0 then w.getD g.2.1 false && w.getD g.2.2 false
  else if g.1 = 1 then w.getD g.2.1 false || w.getD g.2.2 false
  else !(w.getD g.2.1 false)

lemma clamp_read (w : List Bool) (i : Nat) :
    w.getD (clamp w.length i) false = w.getD i false := by
  by_cases hi : i ≤ w.length
  · simp [clamp, Nat.min_eq_left hi]
  · have hni : w.length ≤ i := by omega
    simp [clamp, Nat.min_eq_right hni, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none hni]

lemma clamp_read_opt (w : List Bool) (i : Nat) :
    (w[clamp w.length i]?).getD false = (w[i]?).getD false :=
  clamp_read w i

lemma normalizedGate_bound (n : Nat) (g : Gate) :
    (normalizedGate n g).2.1 ≤ n ∧ (normalizedGate n g).2.2 ≤ n := by
  cases g with
  | mk op ins =>
    cases op <;> cases ins with
    | nil => simp [normalizedGate]
    | cons a t =>
      cases t <;> simp [normalizedGate, clamp]

lemma normalizedGate_eval (w : List Bool) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    normalizedEval w (normalizedGate w.length g) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  cases g with
  | mk op ins =>
    change op = .and ∨ op = .or ∨ op = .not at hop
    rcases hop with rfl | rfl | rfl
    · cases ins with
      | nil => simp [normalizedEval, normalizedGate, GateOp.eval]
      | cons a t =>
        cases t with
        | nil => simp [normalizedEval, normalizedGate, GateOp.eval, clamp_read_opt]
        | cons b u =>
          have hu : u = [] := by simpa using hlen
          subst u
          simp [normalizedEval, normalizedGate, GateOp.eval, clamp_read_opt]
    · cases ins with
      | nil => simp [normalizedEval, normalizedGate, GateOp.eval]
      | cons a t =>
        cases t with
        | nil => simp [normalizedEval, normalizedGate, GateOp.eval, clamp_read_opt]
        | cons b u =>
          have hu : u = [] := by simpa using hlen
          subst u
          simp [normalizedEval, normalizedGate, GateOp.eval, clamp_read_opt]
    · cases ins <;> simp [normalizedEval, normalizedGate, GateOp.eval, clamp_read_opt]

end PEqualNP.Outside.L_meta_670_aux
