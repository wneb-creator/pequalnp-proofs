import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585_aux.Multilinear

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi


lemma scan_two {α : Type} (step : List α → Gate → α) (gs : List Gate) (g1 g2 : Gate)
    (w : List α) :
    scan step (gs ++ [g1, g2]) w =
      (scan step gs w ++ [step (scan step gs w) g1]) ++
        [step (scan step gs w ++ [step (scan step gs w) g1]) g2] := by
  rw [scan_append]
  rfl

lemma getD_init {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_last {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_last' {α : Type} (z : α) (l : List α) (b : α) (m : ℕ) (hm : l.length = m) :
    (l ++ [b]).getD m z = b := by
  subst hm
  exact getD_last z l b

def rstep (k : ℕ) (S : List ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

lemma readVectors_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = scan (rstep k S) C.gates ((List.range n).map (leafVectors S k)) := rfl

lemma readVectors_length (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    (readVectors C n S k).length = n + C.gates.length := by
  rw [readVectors_eq, scan_length]
  simp

lemma readVectors_leaf (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (a : ℕ) (ha : a < n) :
    (readVectors C n S k).getD a [] = leafVectors S k a := by
  rw [readVectors_eq, scan_prefix _ _ _ _ _ (by simpa using ha)]
  simp [List.getD_eq_getElem?_getD, ha]

lemma mem_insertNew (a v : List ℕ) (A : List (List ℕ)) :
    v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
  unfold insertNew
  by_cases ha : a ∈ A
  · simp [ha, or_iff_left_of_imp (fun (e : v = a) => e.symm ▸ ha)]
  · simp [ha]

lemma mem_fold_insertNew (v : List ℕ) (B A : List (List ℕ)) :
    v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons b B ih => simp [ih, mem_insertNew, or_assoc]

lemma mem_andStep (k : ℕ) (v : List ℕ) (A B : List (List ℕ)) :
    v ∈ andStep k A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd k u w := by
  simp [andStep, mem_fold_insertNew, List.mem_flatMap, List.mem_map, eq_comm]

lemma mem_orFold (v : List ℕ) (ins : List (List (List ℕ))) (acc : List (List ℕ)) :
    v ∈ ins.foldl (fun acc A => A.foldl insertNew acc) acc ↔ v ∈ acc ∨ ∃ A ∈ ins, v ∈ A := by
  induction ins generalizing acc with
  | nil => simp
  | cons A ins ih =>
    simp only [List.foldl_cons, ih, mem_fold_insertNew, List.mem_cons, exists_eq_or_imp]
    tauto

lemma mem_rstep_or (k : ℕ) (S : List ℕ) (R : List (List (List ℕ))) (i j : ℕ) (v : List ℕ)
    (h : v ∈ R.getD i [] ∨ v ∈ R.getD j []) :
    v ∈ rstep k S R ⟨GateOp.or, [i, j]⟩ := by
  show v ∈ ([i, j].map fun t => R.getD t []).foldl (fun acc A => A.foldl insertNew acc) []
  rw [mem_orFold]
  right
  rcases h with h | h
  · exact ⟨R.getD i [], by simp, h⟩
  · exact ⟨R.getD j [], by simp, h⟩

lemma mem_rstep_and (k : ℕ) (S : List ℕ) (R : List (List (List ℕ))) (i j : ℕ) (u w : List ℕ)
    (hu : u ∈ R.getD i []) (hw : w ∈ R.getD j []) :
    capAdd k (capAdd k (S.map fun _ => 0) u) w ∈ rstep k S R ⟨GateOp.and, [i, j]⟩ := by
  show _ ∈ andStep k (andStep k [S.map fun _ => 0] (R.getD i [])) (R.getD j [])
  rw [mem_andStep]
  exact ⟨_, (mem_andStep _ _ _ _).mpr ⟨_, by simp, u, hu, rfl⟩, w, hw, rfl⟩

lemma capAdd_map (k : ℕ) (S : List ℕ) (f g : ℕ → ℕ) :
    capAdd k (S.map f) (S.map g) = S.map fun j => min (f j + g j) (k + 1) := by
  induction S with
  | nil => rfl
  | cons s S ih =>
    simp only [capAdd, List.map_cons, List.zipWith_cons_cons] at ih ⊢
    rw [ih]

open PEqualNP.SyntacticMultilinear PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover

def vvec {n : ℕ} (S T : Finset (Fin n)) : List ℕ :=
  (setList S).map fun j => if j ∈ T.image Fin.val then 1 else 0

def sstep {n : ℕ} (U : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  g.inputs.foldr (fun w acc => U.getD w ∅ ∪ acc) ∅

def bstep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

lemma vvec_union {n : ℕ} (S A B : Finset (Fin n)) (hab : Disjoint A B) :
    capAdd 1 (vvec S A) (vvec S B) = vvec S (A ∪ B) := by
  have hd : Disjoint (A.image Fin.val) (B.image Fin.val) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hj
    have e : b = a := Fin.ext hba
    subst b
    exact Finset.disjoint_left.mp hab ha hb
  rw [vvec, vvec, capAdd_map]
  unfold vvec
  apply List.map_congr_left
  intro j hj
  by_cases ha : j ∈ A.image Fin.val <;> by_cases hb : j ∈ B.image Fin.val
  · exact (Finset.disjoint_left.mp hd ha hb).elim
  · simp [Finset.image_union, ha, hb]
  · simp [Finset.image_union, ha, hb]
  · simp [Finset.image_union, ha, hb]

lemma cap_zero_vvec {n : ℕ} (S A : Finset (Fin n)) :
    capAdd 1 ((setList S).map fun _ => 0) (vvec S A) = vvec S A := by
  unfold vvec
  rw [capAdd_map]
  apply List.map_congr_left
  intro j hj
  by_cases h : j ∈ A.image Fin.val <;> simp [h]

def Inv {n : ℕ} (S : Finset (Fin n)) (U : List (Finset (Fin n)))
    (w : List Bool) (R : List (List (List ℕ))) : Prop :=
  U.length = w.length ∧ R.length = w.length ∧
  ∀ i, w.getD i false = true →
    ∃ T : Finset (Fin n), T ⊆ U.getD i ∅ ∧ vvec S T ∈ R.getD i []

lemma snoc_other {α : Type} (l : List α) (a d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [a]).getD i d = l.getD i d := by
  by_cases h : i < l.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma inv_step {n : ℕ} (S : Finset (Fin n)) (U : List (Finset (Fin n)))
    (w : List Bool) (R : List (List (List ℕ))) (a b : ℕ) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (hdis : op = GateOp.and → Disjoint (U.getD a ∅) (U.getD b ∅))
    (hi : Inv S U w R) :
    Inv S (U ++ [sstep U ⟨op, [a,b]⟩])
      (w ++ [bstep w ⟨op, [a,b]⟩])
      (R ++ [rstep 1 (setList S) R ⟨op, [a,b]⟩]) := by
  obtain ⟨hu, hr, hi⟩ := hi
  refine ⟨by simp [hu], by simp [hr], ?_⟩
  intro i hval
  by_cases heq : i = w.length
  · subst i
    rw [getD_last] at hval
    rw [← hu, getD_last, hu, ← hr, getD_last]
    rcases hop with rfl | rfl
    · have hbits : w.getD a false = true ∧ w.getD b false = true := by
        simpa [bstep, GateOp.eval] using hval
      obtain ⟨A, hA, hvA⟩ := hi a hbits.1
      obtain ⟨B, hB, hvB⟩ := hi b hbits.2
      refine ⟨A ∪ B, ?_, ?_⟩
      · simpa [sstep] using Finset.union_subset_union hA hB
      · have hd : Disjoint A B := (hdis rfl).mono hA hB
        have hm := mem_rstep_and 1 (setList S) R a b (vvec S A) (vvec S B) hvA hvB
        rw [cap_zero_vvec, vvec_union S A B hd] at hm
        exact hm
    · have hbits : w.getD a false = true ∨ w.getD b false = true := by
        simpa [bstep, GateOp.eval] using hval
      rcases hbits with ha | hb
      · obtain ⟨A, hA, hvA⟩ := hi a ha
        refine ⟨A, ?_, mem_rstep_or 1 (setList S) R a b _ (Or.inl hvA)⟩
        simpa [sstep] using hA.trans (Finset.subset_union_left)
      · obtain ⟨B, hB, hvB⟩ := hi b hb
        refine ⟨B, ?_, mem_rstep_or 1 (setList S) R a b _ (Or.inr hvB)⟩
        simpa [sstep] using hB.trans (Finset.subset_union_right)
  · rw [snoc_other _ _ _ _ heq] at hval
    rw [snoc_other _ _ _ _ (by omega), snoc_other _ _ _ _ (by omega)]
    exact hi i hval

lemma mem_setList {n : ℕ} (S : Finset (Fin n)) (a : ℕ) :
    a ∈ setList S ↔ ∃ i ∈ S, i.val = a := by
  simp [setList]

lemma inv_inputs {n : ℕ} (S : Finset (Fin n)) :
    Inv S (List.ofFn fun i : Fin n => ({i} : Finset (Fin n)))
      (List.ofFn (setInput S)) ((List.range n).map (leafVectors (setList S) 1)) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i hi
  have hin : i < n := by
    by_contra h
    rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    cases hi
  have his : (⟨i,hin⟩ : Fin n) ∈ S := by
    simpa [List.getD_eq_getElem?_getD, hin, setInput] using hi
  have hm : i ∈ setList S := mem_setList S i |>.mpr ⟨⟨i,hin⟩,his,rfl⟩
  refine ⟨{⟨i,hin⟩}, ?_, ?_⟩
  · simp [List.getD_eq_getElem?_getD, hin]
  · simp [List.getD_eq_getElem?_getD, hin, leafVectors, hm, vvec]

lemma scan_snoc {α : Type} (step : List α → Gate → α) (gs : List Gate) (g : Gate)
    (w : List α) :
    scan step (gs ++ [g]) w = scan step gs w ++ [step (scan step gs w) g] := by
  rw [scan_append]
  rfl

lemma scan_take_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate)
    (w : List α) (d : α) (j i : ℕ) (hi : i < w.length + (gs.take j).length) :
    (scan step gs w).getD i d = (scan step (gs.take j) w).getD i d := by
  calc
    _ = (scan step (gs.drop j) (scan step (gs.take j) w)).getD i d := by
      rw [← scan_append, List.take_append_drop]
    _ = _ := scan_prefix step _ _ d i (by simpa [scan_length] using hi)

lemma support_prefix (n : ℕ) (C : Circuit) (j i : ℕ)
    (hi : i < n + (C.gates.take j).length) :
    support n C i =
      (scan sstep (C.gates.take j) (List.ofFn fun k : Fin n => ({k} : Finset (Fin n)))).getD i ∅ := by
  exact scan_take_prefix sstep C.gates _ ∅ j i (by simpa using hi)

lemma inv_full (n : ℕ) (C : Circuit) (S : Finset (Fin n))
    (hAO : IsAO2 n C) (hml : IsSyntMultilinear n C) :
    Inv S (supports n C) (C.wires (List.ofFn (setInput S))) (readVectors C n (setList S) 1) := by
  have h : ∀ j, j ≤ C.gates.length →
      Inv S
        (scan sstep (C.gates.take j) (List.ofFn fun k : Fin n => ({k} : Finset (Fin n))))
        (scan bstep (C.gates.take j) (List.ofFn (setInput S)))
        (scan (rstep 1 (setList S)) (C.gates.take j)
          ((List.range n).map (leafVectors (setList S) 1))) := by
    intro j
    induction j with
    | zero =>
      intro hj
      simpa [scan] using inv_inputs S
    | succ j ih =>
      intro hj
      have hj' : j < C.gates.length := by omega
      have hm : C.gates[j] ∈ C.gates := List.getElem_mem hj'
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 _ hm)
      have hgat : gateAt C j = C.gates[j] := by
        simp [gateAt, List.getD_eq_getElem?_getD, hj']
      have hshape : C.gates[j] = ⟨(C.gates[j]).op, [a,b]⟩ := by rw [← hab]
      have hop := hAO.1 _ hm
      have ha : a < n + j := hAO.2.1 j hj' a (by simp [hgat, hab])
      have hb : b < n + j := hAO.2.1 j hj' b (by simp [hgat, hab])
      have hdis : (C.gates[j]).op = GateOp.and →
          Disjoint
            ((scan sstep (C.gates.take j)
              (List.ofFn fun k : Fin n => ({k} : Finset (Fin n)))).getD a ∅)
            ((scan sstep (C.gates.take j)
              (List.ofFn fun k : Fin n => ({k} : Finset (Fin n)))).getD b ∅) := by
        intro hand
        have hd : Disjoint (operandSupport n C j a) (operandSupport n C j b) := by
          simpa [AndOperandsDisjoint, hgat, hab] using hml j hj' (by simpa [hgat] using hand)
        rw [operandSupport, operandSupport, ite_eq_left ha, ite_eq_left hb] at hd
        rw [support_prefix n C j a (by simp; omega),
          support_prefix n C j b (by simp; omega)] at hd
        exact hd
      rw [List.take_succ_eq_append_getElem hj', scan_snoc, scan_snoc, scan_snoc, hshape]
      exact inv_step S _ _ _ a b _ hop hdis (ih (by omega))
  have hs : supports n C = scan sstep C.gates
      (List.ofFn fun k : Fin n => ({k} : Finset (Fin n))) := rfl
  have hw : C.wires (List.ofFn (setInput S)) =
      scan bstep C.gates (List.ofFn (setInput S)) := rfl
  rw [hs, hw, readVectors_eq]
  simpa only [List.take_length] using h C.gates.length le_rfl

lemma syntactic_multilinear_read_one (n : ℕ) (C : Circuit)
    (hAO : IsAO2 n C) (hml : IsSyntMultilinear n C) : IsReadK n C 1 := by
  intro S hS
  have hi := inv_full n C S hAO hml
  have hv : (C.wires (List.ofFn (setInput S))).getD C.output false = true := hS.1
  obtain ⟨T, _, hT⟩ := hi.2.2 C.output hv
  apply List.any_eq_true.mpr
  refine ⟨vvec S T, hT, ?_⟩
  apply List.all_eq_true.mpr
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
  by_cases h : j ∈ T.image Fin.val <;> simp [h]


open PEqualNP.EdgeOwnership

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h

lemma scan_gate_value {α : Type} (step : List α → Gate → α) (gs : List Gate)
    (w : List α) (d : α) (k : ℕ) (hk : k < gs.length) :
    (scan step gs w).getD (w.length + k) d =
      step (scan step (gs.take k) w) gs[k] := by
  rw [scan_take_prefix step gs w d (k+1) (w.length+k) (by simp; omega),
    List.take_succ_eq_append_getElem hk, scan_snoc]
  apply getD_last'
  simp [scan_length]
  omega

lemma support_gate_two (n : ℕ) (C : Circuit) (j a b : ℕ) (hj : j < C.gates.length)
    (hab : (gateAt C j).inputs = [a,b]) (ha : a < n+j) (hb : b < n+j) :
    support n C (n+j) = support n C a ∪ support n C b := by
  have h := scan_gate_value sstep C.gates
    (List.ofFn fun i : Fin n => ({i} : Finset (Fin n))) ∅ j hj
  simp only [List.length_ofFn] at h
  have hgat := gateAt_eq C j hj
  rw [hgat] at hab
  simp only [sstep, hab, List.foldr_cons, List.foldr_nil, Finset.union_empty] at h
  rw [← support_prefix n C j a (by simp; omega),
    ← support_prefix n C j b (by simp; omega)] at h
  exact h

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wire_gate_two (n : ℕ) (C : Circuit) (j a b : ℕ) (hj : j < C.gates.length)
    (hab : (gateAt C j).inputs = [a,b]) (ha : a < n+j) (hb : b < n+j)
    (x : Fin n → Bool) :
    wv n C x (n+j) = (gateAt C j).op.eval [wv n C x a, wv n C x b] := by
  have h := scan_gate_value bstep C.gates (List.ofFn x) false j hj
  simp only [List.length_ofFn] at h
  have hgat := gateAt_eq C j hj
  rw [hgat] at hab
  simp only [bstep, hab, List.map_cons, List.map_nil] at h
  rw [← scan_take_prefix bstep C.gates (List.ofFn x) false j a (by simp; omega),
    ← scan_take_prefix bstep C.gates (List.ofFn x) false j b (by simp; omega)] at h
  simpa only [hgat, wv, Circuit.wires, scan, bstep] using h

lemma support_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    support n C w = {⟨w,hw⟩} := by
  rw [support_prefix n C 0 w (by simpa using hw)]
  simp [scan, List.getD_eq_getElem?_getD, hw]

lemma wire_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    wv n C x w = x ⟨w,hw⟩ := by
  change (scan bstep C.gates (List.ofFn x)).getD w false = _
  rw [scan_prefix bstep C.gates (List.ofFn x) false w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma no_and_support_true (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ∀ w, w < n + C.gates.length →
      (∀ k < C.gates.length, (w = n+k ∨ n ≤ w ∧ InCone n C k (w-n)) →
        (gateAt C k).op ≠ GateOp.and) →
      ∀ v : Fin n, v ∈ support n C w →
        wv n C (fun r => decide (r=v)) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hno v hv
    by_cases hwn : w < n
    · rw [support_input n C w hwn, Finset.mem_singleton] at hv
      rw [wire_input n C w hwn]
      simp [hv]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n+j := ⟨w-n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hgat := gateAt_eq C j hj
      have hm : gateAt C j ∈ C.gates := by rw [hgat]; exact List.getElem_mem hj
      obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hAO.2.2 _ hm)
      have ha : a < n+j := hAO.2.1 j hj a (by simp [hab])
      have hb : b < n+j := hAO.2.1 j hj b (by simp [hab])
      have hop : (gateAt C j).op = GateOp.or := by
        rcases hAO.1 _ hm with h | h
        · exact (hno j hj (Or.inl rfl) h).elim
        · exact h
      have hchild (r : ℕ) (hr : r ∈ (gateAt C j).inputs) (hlt : r < n+j) :
          ∀ k < C.gates.length, (r = n+k ∨ n ≤ r ∧ InCone n C k (r-n)) →
            (gateAt C k).op ≠ GateOp.and := by
        intro k hk hc
        apply hno k hk
        right
        refine ⟨by omega, ?_⟩
        have hc' : InCone n C k j := by
          apply (inCone_iff n C k j hj).mpr
          rcases hc with heq | ⟨hn, hcone⟩
          · exact ⟨r, hr, by omega, hlt, Or.inl (by omega)⟩
          · exact ⟨r, hr, hn, hlt, Or.inr hcone⟩
        simpa using hc'
      rw [support_gate_two n C j a b hj hab ha hb, Finset.mem_union] at hv
      rw [wire_gate_two n C j a b hj hab ha hb, hop]
      rcases hv with hva | hvb
      · have ht := ih a ha (by omega) (hchild a (by simp [hab]) ha) v hva
        simp [GateOp.eval, ht]
      · have ht := ih b hb (by omega) (hchild b (by simp [hab]) hb) v hvb
        simp [GateOp.eval, ht]

lemma no_nested_and_multilinear (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hnested : ∀ i < C.gates.length, ∀ j < C.gates.length,
      (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and → ¬ InCone n C i j)
    (hzero : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ v : Fin n, gateVal n C j (fun r => decide (r=v)) = false) :
    IsSyntMultilinear n C := by
  intro j hj hand
  have hgat := gateAt_eq C j hj
  have hm : gateAt C j ∈ C.gates := by rw [hgat]; exact List.getElem_mem hj
  obtain ⟨a,b,hab⟩ := List.length_eq_two.mp (hAO.2.2 _ hm)
  have ha : a < n+j := hAO.2.1 j hj a (by simp [hab])
  have hb : b < n+j := hAO.2.1 j hj b (by simp [hab])
  have hchild (r : ℕ) (hr : r ∈ (gateAt C j).inputs) (hlt : r < n+j) :
      ∀ k < C.gates.length, (r = n+k ∨ n ≤ r ∧ InCone n C k (r-n)) →
        (gateAt C k).op ≠ GateOp.and := by
    intro k hk hc hkand
    apply hnested k hk j hj hkand hand
    apply (inCone_iff n C k j hj).mpr
    rcases hc with heq | ⟨hn, hcone⟩
    · exact ⟨r,hr,by omega,hlt,Or.inl (by omega)⟩
    · exact ⟨r,hr,hn,hlt,Or.inr hcone⟩
  have hd : Disjoint (support n C a) (support n C b) := by
    apply Finset.disjoint_left.mpr
    intro v hva hvb
    have va := no_and_support_true n C hAO a (by omega)
      (hchild a (by simp [hab]) ha) v hva
    have vb := no_and_support_true n C hAO b (by omega)
      (hchild b (by simp [hab]) hb) v hvb
    have htrue : gateVal n C j (fun r => decide (r=v)) = true := by
      change wv n C (fun r => decide (r=v)) (n+j) = true
      rw [wire_gate_two n C j a b hj hab ha hb, hand]
      simp [GateOp.eval, va, vb]
    rw [hzero j hj hand v] at htrue
    cases htrue
  simpa [AndOperandsDisjoint,hab,operandSupport,ha,hb] using hd

lemma and_pairs_zero_read_one (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hpairs : andPairs n C = 0)
    (hzero : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ v : Fin n, gateVal n C j (fun r => decide (r=v)) = false) :
    IsReadK n C 1 := by
  apply syntactic_multilinear_read_one n C hAO
  apply no_nested_and_multilinear n C hAO ?_ hzero
  intro i hi j hj hiand hjand hcone
  have hpos : 0 < andPairs n C := by
    apply Finset.card_pos.mpr
    refine ⟨(i,j), ?_⟩
    simp [hi, hj, hiand, hjand, hcone]
  omega

end PEqualNP.Outside.L_meta_2585_aux.Multilinear

namespace PEqualNP.Outside.L_meta_2585.CleanTopForm

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover

lemma singleton_false (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : graphFun G ∅ (PEqualNP.SplitCount.unitInput v) = false := by
  simp [graphFun, PEqualNP.SplitCount.unitInput]

lemma no_nested_and (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (htop : TopForm G C)
    (hclean : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → BelowF G C i) :
    ∀ i < C.gates.length, ∀ j < C.gates.length,
      (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.and → ¬ InCone n C i j := by
  intro i hi j hj hopi hopj
  exact htop i hi j hj hopi (hclean i hi hopi) hopj

lemma and_singleton_false (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit)
    (hclean : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → BelowF G C i) :
    ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → ∀ v : Fin n,
      gateVal n C i (PEqualNP.SplitCount.unitInput v) = false := by
  intro i hi hop v
  cases hv : gateVal n C i (PEqualNP.SplitCount.unitInput v) with
  | false => rfl
  | true =>
    have h := hclean i hi hop (PEqualNP.SplitCount.unitInput v) hv
    rw [singleton_false n G v] at h
    cases h

end PEqualNP.Outside.L_meta_2585.CleanTopForm

namespace PEqualNP.Outside.L_meta_2585.CleanJunk

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover

lemma all_and_below_of_junk_empty (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hJ : junk G C = ∅) :
    ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → BelowF G C i := by
  intro i hi hop x hx
  cases hF : graphFun G ∅ x with
  | true => rfl
  | false =>
    have hmem : i ∈ junk G C := by
      simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range]
      exact ⟨hi, hop, hi, x, hx, hF⟩
    have hnot : i ∉ junk G C := by simp [hJ]
    exact False.elim (hnot hmem)

end PEqualNP.Outside.L_meta_2585.CleanJunk

namespace PEqualNP.Outside.L_meta_2585.CleanReadOne

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

lemma clean_topform_read_one (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (htop : TopForm G C) (hJ : junk G C = ∅) :
    PEqualNP.ReadK.IsReadK n C 1 := by
  have hbelow := PEqualNP.Outside.L_meta_2585.CleanJunk.all_and_below_of_junk_empty n G C hJ
  apply PEqualNP.Outside.L_meta_2585_aux.Multilinear.syntactic_multilinear_read_one n C hAO
  apply PEqualNP.Outside.L_meta_2585_aux.Multilinear.no_nested_and_multilinear n C hAO
  · exact PEqualNP.Outside.L_meta_2585.CleanTopForm.no_nested_and n G C htop hbelow
  · exact PEqualNP.Outside.L_meta_2585.CleanTopForm.and_singleton_false n G C hbelow

lemma incidence_replacement_of_clean_topform (P L : ℕ)
    (I : Fin P → Fin L → Prop) [DecidableRel I] (C : Circuit)
    (G : SimpleGraph (Fin (P + L))) [DecidableRel G.Adj]
    (hAO : IsAO2 (P + L) C) (htop : TopForm G C) (hJ : junk G C = ∅)
    (hfun : ∀ z : Fin (P + L) → Bool,
      PEqualNP.MetaComplexity.circuitFun (P + L) C z =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) :
    ∃ D : Circuit, IsAO2 (P + L) D ∧
      (∀ z : Fin (P + L) → Bool,
        PEqualNP.MetaComplexity.circuitFun (P + L) D z =
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
            z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 1 := by
  exact ⟨C, hAO, hfun, le_rfl, clean_topform_read_one (P + L) G C hAO htop hJ⟩

end PEqualNP.Outside.L_meta_2585.CleanReadOne
