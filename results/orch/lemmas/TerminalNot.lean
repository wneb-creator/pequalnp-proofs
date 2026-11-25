import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592.TerminalNot
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

lemma ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

lemma wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma monoW : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ U V : List Bool, U.length = V.length → (∀ i, U.getD i false = true → V.getD i false = true) →
    ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro _ U V _ h i; exact h i
  | cons g t ih =>
    intro hop U V hlen hUV i
    rw [wf_cons, wf_cons]
    refine ih (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hlen]) ?_ i
    intro j hj
    rcases Nat.lt_trichotomy j U.length with hj' | hj' | hj'
    · rw [getD_snoc_lt _ _ _ hj'] at hj
      rw [getD_snoc_lt _ _ _ (by omega)]
      exact hUV j hj
    · rw [hj', getD_snoc_eq] at hj
      rw [hj', hlen, getD_snoc_eq]
      exact eval_mono g.op (hop g (List.mem_cons_self ..)) g.inputs U V hUV hj
    · rw [getD_snoc_gt _ _ _ hj'] at hj
      exact absurd hj (by simp)


lemma wf_len (gs : List Gate) (w : List Bool) :
    (wf gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wf_cons, ih]
    simp
    omega

lemma output_not_eval (gs : List Gate) (j : Nat) (ins : List Nat)
    (n : Nat) (x : Fin n → Bool) :
    (Circuit.mk (gs ++ [⟨GateOp.not, j :: ins⟩]) (n + gs.length)).eval (List.ofFn x) =
      !(Circuit.mk gs j).eval (List.ofFn x) := by
  unfold Circuit.eval Circuit.wires
  rw [List.foldl_append]
  change ((wf gs (List.ofFn x)) ++ [!(wf gs (List.ofFn x)).getD j false]).getD
    (n + gs.length) false = _
  have hlen := wf_len gs (List.ofFn x)
  simp only [List.length_ofFn] at hlen
  rw [← hlen]
  exact getD_snoc_eq _ _

lemma prefix_no_not (gs : List Gate) (g : Gate) (hn : g.op = GateOp.not)
    (out : Nat)
    (count : PEqualNP.NotBracket.notCount (Circuit.mk (gs ++ [g]) out) = 1) :
    ∀ a ∈ gs, a.op ≠ GateOp.not := by
  let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
  have zero : (gs.filter (fun a => decide (a.op = GateOp.not))).length = 0 := by
    simpa [PEqualNP.NotBracket.notCount, List.filter_append, hn] using count
  intro a ha hop
  have member : a ∈ gs.filter (fun a => decide (a.op = GateOp.not)) := by
    simp [ha, hop]
  have positive := List.length_pos_of_mem member
  omega

lemma single_not_output_impossible (n : Nat) (f : (Fin n → Bool) → Bool)
    (bottom : f (fun _ => false) = false) (top : f (fun _ => true) = true)
    (gs : List Gate) (ins : List Nat)
    (legal : PEqualNP.MetaComplexity.FanInTwo
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)))
    (count : PEqualNP.NotBracket.notCount
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)) = 1) :
    ¬ ∀ x : Fin n → Bool,
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)).eval (List.ofFn x) = f x := by
  intro computes
  have h0 := computes (fun _ => false)
  have h1 := computes (fun _ => true)
  rw [bottom] at h0
  rw [top] at h1
  cases ins with
  | nil =>
    have hlen := wf_len gs (List.ofFn (fun _ : Fin n => false))
    simp only [List.length_ofFn] at hlen
    unfold Circuit.eval Circuit.wires at h0
    rw [List.foldl_append] at h0
    change ((wf gs (List.ofFn (fun _ : Fin n => false))) ++ [true]).getD
      (n + gs.length) false = false at h0
    rw [← hlen, getD_snoc_eq] at h0
    cases h0
  | cons j ins =>
    rw [output_not_eval] at h0 h1
    have noNot := prefix_no_not gs ⟨GateOp.not, j :: ins⟩ rfl (n + gs.length) count
    have mono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      have hops := (legal g (List.mem_append_left _ hg)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hops
      rcases hops with hand | hor | hnot
      · exact Or.inl hand
      · exact Or.inr hor
      · exact False.elim (noNot g hg hnot)
    have val0 : (Circuit.mk gs j).eval (List.ofFn (fun _ : Fin n => false)) = true := by
      simpa using h0
    have val1 : (Circuit.mk gs j).eval (List.ofFn (fun _ : Fin n => true)) = false := by
      simpa using h1
    have contradiction := monoW gs mono _ _ (by simp)
      (ofFn_mono n (fun _ => false) (fun _ => true) (by simp)) j val0
    change (Circuit.mk gs j).eval (List.ofFn (fun _ : Fin n => true)) = true at contradiction
    rw [val1] at contradiction
    cases contradiction

end PEqualNP.Outside.L_meta_2592.TerminalNot
