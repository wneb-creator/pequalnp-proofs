import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.Support

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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
    (∀ g ∈ gs, g.inputs.length ≤ 2) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self) h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this


lemma essential_card_le (n : ℕ) (C : Circuit) (S : Finset (Fin n))
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hdep : ∀ i ∈ S, ∃ x y : Fin n → Bool,
      (∀ j, j ≠ i → x j = y j) ∧ circuitFun n C x ≠ circuitFun n C y) :
    S.card ≤ C.size + 1 := by
  let U := (suppsFrom C.gates (inputSupps n)).getD C.output ∅
  have hsub : S ⊆ U := by
    intro i hi
    by_contra hni
    obtain ⟨x, y, hxy, hne⟩ := hdep i hi
    apply hne
    have hag := (agree_wiresFrom x y C.gates _ _ _ (agree_inputs x y)).2.2 C.output (by
      intro j hj
      exact hxy j (fun hji => hni (hji ▸ hj)))
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) hfan cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  exact (Finset.card_le_card hsub).trans hc

lemma incident_card_le (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hfun : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    (E.biUnion fun e => {Fin.castAdd l e.1, Fin.natAdd p e.2}).card ≤ C.size + 1 := by
  classical
  have sep : ∀ (a : Fin p) (b : Fin l),
      (Fin.castAdd l a : Fin (p + l)) ≠ Fin.natAdd p b := by
    intro a b h
    have hh : a.val = p + b.val := congrArg Fin.val h
    have := a.isLt
    omega
  have single (i : Fin (p + l)) :
      circuitFun (p + l) C (fun k => decide (k = i)) = false := by
    rw [hfun, decide_eq_false_iff_not]
    rintro ⟨a, b, _, ha, hb⟩
    simp only [decide_eq_true_eq] at ha hb
    exact sep a b (ha.trans hb.symm)
  apply essential_card_le (p + l) C _ hfan
  intro i hi
  obtain ⟨⟨a, b⟩, he, hi⟩ := Finset.mem_biUnion.mp hi
  have pair : circuitFun (p + l) C
      (fun k => decide (k = Fin.castAdd l a ∨ k = Fin.natAdd p b)) = true := by
    rw [hfun, decide_eq_true_eq]
    exact ⟨a, b, he, by simp, by simp⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · refine ⟨(fun k => decide (k = Fin.castAdd l a ∨ k = Fin.natAdd p b)),
      (fun k => decide (k = Fin.natAdd p b)), ?_, ?_⟩
    · intro j hj
      simp [hj]
    · rw [pair, single]
      decide
  · refine ⟨(fun k => decide (k = Fin.castAdd l a ∨ k = Fin.natAdd p b)),
      (fun k => decide (k = Fin.castAdd l a)), ?_, ?_⟩
    · intro j hj
      simp [hj]
    · rw [pair, single]
      decide

end PEqualNP.Outside.L_meta_4675.Support

namespace PEqualNP.Outside.L_meta_4675.StarForest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma endpoint_card_le (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hfun : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    (E.image fun e => Fin.castAdd l e.1).card +
      (E.image fun e => Fin.natAdd p e.2).card ≤ C.size + 1 := by
  classical
  have hdisj : Disjoint (E.image fun e => Fin.castAdd l e.1)
      (E.image fun e => Fin.natAdd p e.2) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    obtain ⟨e, _, he⟩ := Finset.mem_image.mp hi
    obtain ⟨f, _, hf⟩ := Finset.mem_image.mp hj
    have hh : e.1.val = p + f.2.val := congrArg Fin.val (he.trans hf.symm)
    have := e.1.isLt
    omega
  have heq : E.biUnion (fun e => {Fin.castAdd l e.1, Fin.natAdd p e.2}) =
      (E.image fun e => Fin.castAdd l e.1) ∪ (E.image fun e => Fin.natAdd p e.2) := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨e, he, hi | hi⟩
      · exact Or.inl ⟨e, he, hi.symm⟩
      · exact Or.inr ⟨e, he, hi.symm⟩
    · rintro (⟨e, he, hi⟩ | ⟨e, he, hi⟩)
      · exact ⟨e, he, Or.inl hi.symm⟩
      · exact ⟨e, he, Or.inr hi.symm⟩
  have hcard := Support.incident_card_le p l E C hfan hfun
  rw [heq, Finset.card_union_of_disjoint hdisj] at hcard
  exact hcard

lemma point_degree_one_bound (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hfst : Set.InjOn Prod.fst (↑E : Set (Fin p × Fin l)))
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hfun : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  classical
  refine ⟨E.image (fun e => Fin.natAdd p e.2), ?_, ?_⟩
  · intro a b hab
    exact Or.inr (Finset.mem_image.mpr ⟨(a, b), hab, rfl⟩)
  · have hcard := endpoint_card_le p l E C hfan hfun
    have hinj : Set.InjOn (fun e : Fin p × Fin l => Fin.castAdd l e.1) (↑E : Set _) := by
      intro e he f hf h
      exact hfst he hf (by simpa using h)
    rw [Finset.card_image_of_injOn hinj] at hcard
    exact hcard

lemma line_degree_one_bound (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hsnd : Set.InjOn Prod.snd (↑E : Set (Fin p × Fin l)))
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hfun : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  classical
  refine ⟨E.image (fun e => Fin.castAdd l e.1), ?_, ?_⟩
  · intro a b hab
    exact Or.inl (Finset.mem_image.mpr ⟨(a, b), hab, rfl⟩)
  · have hcard := endpoint_card_le p l E C hfan hfun
    have hinj : Set.InjOn (fun e : Fin p × Fin l => Fin.natAdd p e.2) (↑E : Set _) := by
      intro e he f hf h
      exact hsnd he hf (by simpa using h)
    rw [Finset.card_image_of_injOn hinj] at hcard
    simpa [Nat.add_comm] using hcard

end PEqualNP.Outside.L_meta_4675.StarForest
