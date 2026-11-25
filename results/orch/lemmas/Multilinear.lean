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

end PEqualNP.Outside.L_meta_2585_aux.Multilinear
