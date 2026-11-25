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

lemma snoc_mono (U V : List Bool) (b c : Bool) (hlen : U.length = V.length)
    (hwire : ∀ i, U.getD i false = true → V.getD i false = true)
    (hbit : b = true → c = true) :
    ∀ i, (U ++ [b]).getD i false = true → (V ++ [c]).getD i false = true := by
  intro i hi
  rcases Nat.lt_trichotomy i U.length with h | h | h
  · rw [getD_snoc_lt _ _ _ h] at hi
    rw [getD_snoc_lt _ _ _ (by omega)]
    exact hwire i hi
  · rw [h, getD_snoc_eq] at hi
    rw [h, hlen, getD_snoc_eq]
    exact hbit hi
  · rw [getD_snoc_gt _ _ _ h] at hi
    cases hi

lemma two_not_terminal_reduces (n : Nat) (f : (Fin n → Bool) → Bool)
    (bottom : f (fun _ => false) = false) (top : f (fun _ => true) = true)
    (P Q : Circuit)
    (pMono : ∀ g ∈ P.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (qMono : ∀ g ∈ Q.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (computes : ∀ x : Fin n → Bool,
      Bool.not (Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)])) = f x) :
    ∀ x : Fin n → Bool, P.eval (List.ofFn x) = f x := by
  have rise (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
      (b c : Bool) (hbc : b = true → c = true) :
      Q.eval (P.wires (List.ofFn x) ++ [b]) = true →
      Q.eval (P.wires (List.ofFn y) ++ [c]) = true := by
    apply monoW Q.gates qMono _ _ _ _ Q.output
    · have hx := wf_len P.gates (List.ofFn x)
      have hy := wf_len P.gates (List.ofFn y)
      change (wf P.gates (List.ofFn x) ++ [b]).length =
        (wf P.gates (List.ofFn y) ++ [c]).length
      simp [hx, hy]
    · apply snoc_mono _ _ _ _ _ _ hbc
      · have hx := wf_len P.gates (List.ofFn x)
        have hy := wf_len P.gates (List.ofFn y)
        change (wf P.gates (List.ofFn x)).length = (wf P.gates (List.ofFn y)).length
        simp [hx, hy]
      · exact monoW P.gates pMono _ _ (by simp) (ofFn_mono n x y hxy)
  have low : Q.eval (P.wires (List.ofFn (fun _ : Fin n => false)) ++
      [!P.eval (List.ofFn (fun _ : Fin n => false))]) = true := by
    simpa [bottom] using computes (fun _ => false)
  have high : Q.eval (P.wires (List.ofFn (fun _ : Fin n => true)) ++
      [!P.eval (List.ofFn (fun _ : Fin n => true))]) = false := by
    simpa [top] using computes (fun _ => true)
  intro x
  cases hx : P.eval (List.ofFn x) with
  | false =>
    have qx : Q.eval (P.wires (List.ofFn x) ++ [true]) = true :=
      rise (fun _ => false) x (by simp) _ true (by simp) low
    simpa [hx, qx] using computes x
  | true =>
    have qx : Q.eval (P.wires (List.ofFn x) ++ [false]) = false := by
      cases hq : Q.eval (P.wires (List.ofFn x) ++ [false]) with
      | false => rfl
      | true =>
        have impossible := rise x (fun _ => true) (by simp) false
          (!P.eval (List.ofFn (fun _ : Fin n => true))) (by simp) hq
        rw [high] at impossible
        cases impossible
    simpa [hx, qx] using computes x

lemma not_inputs_eval (gs : List Gate) (ins : List Nat) (n : Nat) (x : Fin n → Bool) :
    GateOp.not.eval (ins.map fun i => (wf gs (List.ofFn x)).getD i false) =
      !(Circuit.mk gs (ins.headD (n + gs.length))).eval (List.ofFn x) := by
  cases ins with
  | nil =>
    have hlen := wf_len gs (List.ofFn x)
    simp only [List.length_ofFn] at hlen
    change true = !(wf gs (List.ofFn x)).getD (n + gs.length) false
    rw [List.getD_eq_default _ _ (by omega)]
    rfl
  | cons j ins => rfl

lemma output_not_eval_all (gs : List Gate) (ins : List Nat) (n : Nat) (x : Fin n → Bool) :
    (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)).eval (List.ofFn x) =
      !(Circuit.mk gs (ins.headD (n + gs.length))).eval (List.ofFn x) := by
  unfold Circuit.eval Circuit.wires
  rw [List.foldl_append]
  change ((wf gs (List.ofFn x)) ++
    [GateOp.not.eval (ins.map fun i => (wf gs (List.ofFn x)).getD i false)]).getD
    (n + gs.length) false = _
  have hlen := wf_len gs (List.ofFn x)
  simp only [List.length_ofFn] at hlen
  have reading := getD_snoc_eq (wf gs (List.ofFn x))
    (GateOp.not.eval (ins.map fun i => (wf gs (List.ofFn x)).getD i false))
  rw [hlen] at reading
  exact reading.trans (not_inputs_eval gs ins n x)

lemma insert_not_wires (before : List Gate) (ins : List Nat) (after : List Gate)
    (n : Nat) (x : Fin n → Bool) :
    wf (before ++ ⟨GateOp.not, ins⟩ :: after) (List.ofFn x) =
      wf after (wf before (List.ofFn x) ++
        [!(Circuit.mk before (ins.headD (n + before.length))).eval (List.ofFn x)]) := by
  unfold wf
  rw [List.foldl_append]
  change wf after (wf before (List.ofFn x) ++
    [GateOp.not.eval (ins.map fun i => (wf before (List.ofFn x)).getD i false)]) = _
  rw [not_inputs_eval]
  rfl

lemma split_unique_not (gs : List Gate)
    (count : PEqualNP.NotBracket.notCount (Circuit.mk gs 0) = 1) :
    ∃ before g after, gs = before ++ g :: after ∧ g.op = GateOp.not ∧
      (∀ a ∈ before, a.op ≠ GateOp.not) ∧ (∀ a ∈ after, a.op ≠ GateOp.not) := by
  let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
  let isN := fun a : Gate => decide (a.op = GateOp.not)
  have hc : (gs.filter isN).length = 1 := count
  obtain ⟨g, hg⟩ : ∃ g, g ∈ gs.filter isN := by
    cases h : gs.filter isN with
    | nil => simp [h] at hc
    | cons a rest => exact ⟨a, by simp [h]⟩
  obtain ⟨member, yes⟩ := List.mem_filter.mp hg
  have gn : g.op = GateOp.not := by simpa [isN] using yes
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  have parts : (before.filter isN).length + 1 + (after.filter isN).length = 1 := by
    simpa [split, List.filter_append, isN, gn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hc
  have none (l : List Gate) (zero : (l.filter isN).length = 0) :
      ∀ a ∈ l, a.op ≠ GateOp.not := by
    intro a ha hn
    have ha' : a ∈ l.filter isN := by simp [ha, isN, hn]
    have positive := List.length_pos_of_mem ha'
    omega
  exact ⟨before, g, after, split, gn, none before (by omega), none after (by omega)⟩

lemma two_not_output_reduces (n : Nat) (f : (Fin n → Bool) → Bool)
    (bottom : f (fun _ => false) = false) (top : f (fun _ => true) = true)
    (gs : List Gate) (ins : List Nat)
    (legal : PEqualNP.MetaComplexity.FanInTwo
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)))
    (count : PEqualNP.NotBracket.notCount
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)) = 2)
    (computes : ∀ x : Fin n → Bool,
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)).eval (List.ofFn x) = f x) :
    ∃ P : Circuit, PEqualNP.MetaComplexity.Monotone2 P ∧
      P.size + 2 ≤ (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)).size ∧
      ∀ x : Fin n → Bool, P.eval (List.ofFn x) = f x := by
  let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
  have countGs : PEqualNP.NotBracket.notCount (Circuit.mk gs 0) = 1 := by
    simpa [PEqualNP.NotBracket.notCount, List.filter_append] using count
  obtain ⟨before, g, after, split, gn, beforeNot, afterNot⟩ := split_unique_not gs countGs
  have geq : g = ⟨GateOp.not, g.inputs⟩ := by cases g; simp_all
  let P : Circuit := ⟨before, g.inputs.headD (n + before.length)⟩
  let Q : Circuit := ⟨after, ins.headD (n + gs.length)⟩
  have beforeFan (a : Gate) (ha : a ∈ before) :
      a.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ a.inputs.length ≤ 2 := by
    apply legal a
    apply List.mem_append_left
    rw [split]
    exact List.mem_append_left _ ha
  have afterFan (a : Gate) (ha : a ∈ after) :
      a.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ a.inputs.length ≤ 2 := by
    apply legal a
    apply List.mem_append_left
    rw [split]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ ha)
  have pMono : ∀ a ∈ P.gates, a.op = GateOp.and ∨ a.op = GateOp.or := by
    intro a ha
    have hop := (beforeFan a ha).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (beforeNot a ha h)
  have qMono : ∀ a ∈ Q.gates, a.op = GateOp.and ∨ a.op = GateOp.or := by
    intro a ha
    have hop := (afterFan a ha).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (afterNot a ha h)
  refine ⟨P, ?_, ?_, ?_⟩
  · intro a ha
    exact ⟨pMono a ha, (beforeFan a ha).2⟩
  · simp only [Circuit.size, P, split, List.length_append, List.length_cons, List.length_nil]
    omega
  · apply two_not_terminal_reduces n f bottom top P Q pMono qMono
    intro x
    have original := computes x
    rw [output_not_eval_all] at original
    have middle : (Circuit.mk gs (ins.headD (n + gs.length))).eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
      change (wf gs (List.ofFn x)).getD (ins.headD (n + gs.length)) false =
        (wf after (wf before (List.ofFn x) ++
          [!(Circuit.mk before (g.inputs.headD (n + before.length))).eval (List.ofFn x)])).getD
            (ins.headD (n + gs.length)) false
      rw [split, geq, insert_not_wires]
    rw [middle] at original
    exact original

lemma wf_preserves (tail : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (wf tail w).getD i false = w.getD i false := by
  induction tail generalizing w with
  | nil => rfl
  | cons g tail ih =>
    rw [wf_cons, ih _ (by simp; omega), getD_snoc_lt _ _ _ hi]

lemma appended_eval (gs tail : List Gate) (out : Nat) (w : List Bool)
    (bound : out < w.length + gs.length) :
    (Circuit.mk (gs ++ tail) out).eval w = (Circuit.mk gs out).eval w := by
  unfold Circuit.eval Circuit.wires
  rw [List.foldl_append]
  exact wf_preserves tail (wf gs w) out (by rw [wf_len]; exact bound)

lemma not_output_reduces (n : Nat) (f : (Fin n → Bool) → Bool)
    (bottom : f (fun _ => false) = false) (top : f (fun _ => true) = true)
    (gs : List Gate) (ins : List Nat) (tail : List Gate)
    (legal : PEqualNP.MetaComplexity.FanInTwo
      (Circuit.mk ((gs ++ [⟨GateOp.not, ins⟩]) ++ tail) (n + gs.length)))
    (count : PEqualNP.NotBracket.notCount
      (Circuit.mk ((gs ++ [⟨GateOp.not, ins⟩]) ++ tail) (n + gs.length)) ≤ 2)
    (computes : ∀ x : Fin n → Bool,
      (Circuit.mk ((gs ++ [⟨GateOp.not, ins⟩]) ++ tail) (n + gs.length)).eval
        (List.ofFn x) = f x) :
    ∃ P : Circuit, PEqualNP.MetaComplexity.Monotone2 P ∧
      P.size + 2 ≤ (Circuit.mk ((gs ++ [⟨GateOp.not, ins⟩]) ++ tail) (n + gs.length)).size ∧
      ∀ x : Fin n → Bool, P.eval (List.ofFn x) = f x := by
  let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
  have prefixFan : PEqualNP.MetaComplexity.FanInTwo
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)) := by
    intro g hg
    exact legal g (List.mem_append_left _ hg)
  have prefixCount : PEqualNP.NotBracket.notCount
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)) ≤ 2 := by
    unfold PEqualNP.NotBracket.notCount at count ⊢
    simp only [List.filter_append, List.length_append] at count ⊢
    omega
  have prefixPos : 1 ≤ PEqualNP.NotBracket.notCount
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)) := by
    simp [PEqualNP.NotBracket.notCount, List.filter_append]
  have prefixComputes : ∀ x : Fin n → Bool,
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)).eval (List.ofFn x) = f x := by
    intro x
    have preserved := appended_eval (gs ++ [⟨GateOp.not, ins⟩]) tail (n + gs.length)
      (List.ofFn x) (by simp)
    exact preserved.symm.trans (computes x)
  have cases : PEqualNP.NotBracket.notCount
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)) = 1 ∨
      PEqualNP.NotBracket.notCount
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)) = 2 := by omega
  rcases cases with h | h
  · exact False.elim (single_not_output_impossible n f bottom top gs ins prefixFan h prefixComputes)
  · obtain ⟨P, mono, budget, correct⟩ :=
      two_not_output_reduces n f bottom top gs ins prefixFan h prefixComputes
    refine ⟨P, mono, budget.trans ?_, correct⟩
    simp [Circuit.size, List.length_append]

end PEqualNP.Outside.L_meta_2592.TerminalNot
