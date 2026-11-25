import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970.SemanticSupport

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

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

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

lemma wire_mono (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (w : ℕ) :
    Monotone (fun x : Fin n → Bool => wireValue C n x w) := by
  intro x y hxy
  change (wf C.gates (List.ofFn x)).getD w false ≤ (wf C.gates (List.ofFn y)).getD w false
  rw [Bool.le_iff_imp]
  refine mono2 C.gates (fun g hg => ⟨hC.1 g hg, le_of_eq (hC.2.2 g hg)⟩)
    _ _ (by simp) ?_ w
  intro i
  apply ofFn_mono n x y _ i
  intro v hv
  exact (Bool.le_iff_imp.mp (hxy v)) hv

lemma support_of_false_complement (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (S : Finset (Fin n)) (w : ℕ)
    (hz : wireValue C n (fun i => decide (i ∉ S)) w = false) :
    (Finset.univ.filter fun i : Fin n =>
      wireValue C n (fun k => decide (k = i)) w = true) ⊆ S := by
  intro i hi
  by_contra hn
  have hx : (fun k : Fin n => decide (k = i)) ≤ (fun k => decide (k ∉ S)) := by
    intro k
    rw [Bool.le_iff_imp]
    intro hk
    have hki : k = i := of_decide_eq_true hk
    subst k
    exact decide_eq_true hn
  have hm := wire_mono n C hC w hx
  have hit : wireValue C n (fun k => decide (k = i)) w = true :=
    (Finset.mem_filter.mp hi).2
  dsimp only at hm
  rw [hit, hz] at hm
  exact Bool.false_ne_true ((Bool.le_iff_imp.mp hm) rfl)

lemma below_disjunction_iff (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (S : Finset (Fin n)) (w : ℕ) :
    wireValue C n (fun i => decide (i ∉ S)) w = false ↔
    ∀ x : Fin n → Bool, wireValue C n x w = true → ∃ i ∈ S, x i = true := by
  constructor
  · intro hz x hx
    by_contra hn
    have hle : x ≤ (fun i => decide (i ∉ S)) := by
      intro i
      rw [Bool.le_iff_imp]
      intro hi
      exact decide_eq_true (fun his => hn ⟨i, his, hi⟩)
    have hm := wire_mono n C hC w hle
    dsimp only at hm
    rw [hx, hz] at hm
    exact Bool.false_ne_true ((Bool.le_iff_imp.mp hm) rfl)
  · intro h
    cases he : wireValue C n (fun i => decide (i ∉ S)) w
    · rfl
    · obtain ⟨i, his, hi⟩ := h _ he
      have hin : i ∉ S := of_decide_eq_true hi
      exact False.elim (hin his)

end PEqualNP.Outside.L_meta_4970.SemanticSupport
