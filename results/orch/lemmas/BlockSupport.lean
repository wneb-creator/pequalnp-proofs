import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.BlockSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def evalFrom {α : Type} (d : α) (op : GateOp → List α → α) (gates : List Gate) (xs : List α) :
    List α :=
  gates.foldl (fun u g => u ++ [op g.op (g.inputs.map fun i => u.getD i d)]) xs

lemma evalFrom_cons {α : Type} (d : α) (op : GateOp → List α → α) (g : Gate) (gs : List Gate)
    (xs : List α) :
    evalFrom d op (g :: gs) xs = evalFrom d op gs
      (xs ++ [op g.op (g.inputs.map fun i => xs.getD i d)]) := rfl

lemma evalFrom_length {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) : (evalFrom d op gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalFrom]
  | cons g gs ih => rw [evalFrom_cons, ih]; simp; omega

lemma evalFrom_input {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (evalFrom d op gs xs).getD i d = xs.getD i d := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [evalFrom_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]


def run (gs : List Gate) (xs : List Bool) : List Bool :=
  evalFrom false GateOp.eval gs xs

lemma run_snoc (gs : List Gate) (g : Gate) (xs : List Bool) :
    run (gs ++ [g]) xs = run gs xs ++ [g.op.eval (g.inputs.map fun i => (run gs xs).getD i false)] := by
  simp [run, evalFrom, List.foldl_append]

lemma run_length (gs : List Gate) (xs : List Bool) :
    (run gs xs).length = xs.length + gs.length :=
  evalFrom_length false GateOp.eval gs xs

lemma supports (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (F : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ F.card + gs.length ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ F, (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing F with
  | nil => exact ⟨F, by simp, fun _ _ _ _ ha => ha⟩
  | append_singleton gs g ih =>
    let j := n + gs.length
    let B := if j ∈ F then F.erase j ∪ g.inputs.toFinset else F
    have hb : B.card ≤ F.card + 1 := by
      by_cases hj : j ∈ F
      · have hu := Finset.card_union_le (F.erase j) g.inputs.toFinset
        have he := Finset.card_erase_add_one hj
        have hd := (List.toFinset_card_le g.inputs).trans (hg g (by simp))
        simp only [B, ite_eq_left hj]
        omega
      · simp [B, hj]
    obtain ⟨S, hS, hs⟩ := ih (fun a ha => hg a (List.mem_append_left _ ha)) B
    refine ⟨S, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro x y hx hy ha i hi
    have ex : (run gs x).length = j := by simp [run_length, hx, j]
    have ey : (run gs y).length = j := by simp [run_length, hy, j]
    rw [run_snoc, run_snoc]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply hs x y hx hy ha i
      by_cases hj : j ∈ F
      · simpa [B, hj] using Finset.mem_union_left g.inputs.toFinset (Finset.mem_erase.mpr ⟨hij.ne, hi⟩)
      · simpa [B, hj] using hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [ex, ey, Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro k hk
      apply hs x y hx hy ha k
      simpa [B, hi] using Finset.mem_union_right (F.erase j) (List.mem_toFinset.mpr hk)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma essential_set_bound {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (T : Finset (Fin n))
    (he : ∀ i ∈ T, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
      circuitFun n C x ≠ circuitFun n C y) :
    T.card ≤ C.size + 1 := by
  obtain ⟨S, hS, hs⟩ := supports n C.gates hg {C.output}
  have hh : T.image Fin.val ⊆ S := by
    intro i hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    by_contra hni
    obtain ⟨x, y, hxy, hne⟩ := he a ha
    apply hne
    apply hs (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
    intro j hj
    by_cases hjn : j < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hjn),
        List.getD_eq_getElem _ _ (by simpa using hjn)]
      simp only [List.getElem_ofFn]
      apply hxy
      intro e
      have he : j = a.val := congrArg Fin.val e
      exact hni (he ▸ hj)
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn)]
  have hc := Finset.card_le_card hh
  rw [Finset.card_image_of_injective _ Fin.val_injective] at hc
  simp only [Finset.card_singleton] at hS
  unfold Circuit.size
  omega

lemma left_ne_right {n m : ℕ} (p : Fin n) (l : Fin m) :
    Fin.castAdd m p ≠ Fin.natAdd n l := by
  intro h
  have he := congrArg Fin.val h
  change p.val = n + l.val at he
  omega

def incidenceSupport {n m : ℕ} (E : Finset (Fin n × Fin m)) : Finset (Fin (n + m)) :=
  ((E.image Prod.fst).image (Fin.castAdd m)) ∪ ((E.image Prod.snd).image (Fin.natAdd n))

lemma incidenceSupport_card {n m : ℕ} (E : Finset (Fin n × Fin m)) :
    (incidenceSupport E).card = (E.image Prod.fst).card + (E.image Prod.snd).card := by
  have leftInj : Function.Injective (Fin.castAdd m : Fin n → Fin (n + m)) := by
    intro p p' he
    have hv := congrArg Fin.val he
    exact Fin.ext hv
  have rightInj : Function.Injective (Fin.natAdd n : Fin m → Fin (n + m)) := by
    intro l l' he
    apply Fin.ext
    have hv := congrArg Fin.val he
    change n + l.val = n + l'.val at hv
    omega
  have hd : Disjoint ((E.image Prod.fst).image (Fin.castAdd m))
      ((E.image Prod.snd).image (Fin.natAdd n)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hi
    obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hj
    exact left_ne_right p l (hp.trans hl.symm)
  rw [incidenceSupport, Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ leftInj, Finset.card_image_of_injective _ rightInj]

lemma incidence_support_bound {n m : ℕ} (E : Finset (Fin n × Fin m)) (C : Circuit)
    (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hC : ∀ z : Fin (n + m) → Bool, circuitFun (n + m) C z =
      decide (∃ p l, (p, l) ∈ E ∧ z (Fin.castAdd m p) = true ∧
        z (Fin.natAdd n l) = true)) :
    (E.image Prod.fst).card + (E.image Prod.snd).card ≤ C.size + 1 := by
  rw [← incidenceSupport_card E]
  apply essential_set_bound C hg (incidenceSupport E)
  have hpair (p : Fin n) (l : Fin m) (he : (p, l) ∈ E) :
      circuitFun (n + m) C (fun i => decide (i = Fin.castAdd m p ∨ i = Fin.natAdd n l)) = true := by
    rw [hC, decide_eq_true_eq]
    exact ⟨p, l, he, by simp, by simp⟩
  have hpoint (p : Fin n) :
      circuitFun (n + m) C (fun i => decide (i = Fin.castAdd m p)) = false := by
    rw [hC, decide_eq_false_iff_not]
    rintro ⟨_, l, _, _, hl⟩
    exact left_ne_right p l (of_decide_eq_true hl).symm
  have hline (l : Fin m) :
      circuitFun (n + m) C (fun i => decide (i = Fin.natAdd n l)) = false := by
    rw [hC, decide_eq_false_iff_not]
    rintro ⟨p, _, _, hp, _⟩
    exact left_ne_right p l (of_decide_eq_true hp)
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨(fun i => decide (i = Fin.castAdd m e.1 ∨ i = Fin.natAdd n e.2)),
      (fun i => decide (i = Fin.natAdd n e.2)), ?_, ?_⟩
    · intro j hj
      simp [hj]
    · rw [hpair _ _ he, hline]
      decide
  · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hl
    refine ⟨(fun i => decide (i = Fin.castAdd m e.1 ∨ i = Fin.natAdd n e.2)),
      (fun i => decide (i = Fin.castAdd m e.1)), ?_, ?_⟩
    · intro j hj
      simp [hj]
    · rw [hpair _ _ he, hpoint]
      decide

end PEqualNP.Outside.L_meta_2583.BlockSupport
