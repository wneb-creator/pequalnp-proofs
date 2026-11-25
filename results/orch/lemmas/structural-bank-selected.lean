import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.Semantic

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

lemma essential_card_le (n : ℕ) (C : Circuit) (T : Finset (Fin n))
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool,
      circuitFun n C (Function.update x i (!x i)) ≠ circuitFun n C x) :
    T.card ≤ C.size + 1 := by
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hsub : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) hlen cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  exact le_trans (Finset.card_le_card hsub) hc

end PEqualNP.Outside.L_meta_4675.Semantic

namespace PEqualNP.Outside.L_meta_4675.MatchingBank

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma cast_ne_nat {n m : ℕ} (i : Fin n) (j : Fin m) :
    Fin.castAdd m i ≠ Fin.natAdd n j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma append_update {n m : ℕ} (x : Fin n → Bool) (b : Fin m → Bool) (i : Fin n) (v : Bool) :
    Function.update (Fin.addCases x b : Fin (n + m) → Bool) (Fin.castAdd m i) v =
      Fin.addCases (Function.update x i v) b := by
  funext k
  refine Fin.addCases (m := n) (n := m) (fun j => ?_) (fun j => ?_) k
  · have he : Fin.castAdd m j = Fin.castAdd m i ↔ j = i := by
      simp [Fin.ext_iff]
    simp [Function.update_apply, he]
  · have he := (cast_ne_nat i j).symm
    simp [he]

lemma bank_essential_bound {n m : ℕ} (C : Circuit)
    (f : (Fin n → Bool) → Bool) (bank : (Fin n → Bool) → Fin m → Bool)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hfun : ∀ x : Fin n → Bool, circuitFun (n + m) C (Fin.addCases x (bank x)) = f x)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool,
      f (Function.update x i (!x i)) ≠ f x ∧
      bank (Function.update x i (!x i)) = bank x) :
    n ≤ C.size + 1 := by
  let T : Finset (Fin (n + m)) := Finset.univ.image (Fin.castAdd m)
  have hc := Semantic.essential_card_le (n + m) C T hlen ?_
  · have hT : T.card = n := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro a b hab
        apply Fin.ext
        have hv := congrArg (fun z : Fin (n + m) => z.val) hab
        simpa using hv
    rwa [hT] at hc
  · intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨x, hx, hb⟩ := hdep j
    refine ⟨Fin.addCases x (bank x), ?_⟩
    simp only [Fin.addCases_left]
    rw [hfun x, append_update, ← hb, hfun]
    exact hx


lemma bank_essential_selected_bound {n m : ℕ} (C : Circuit) (T : Finset (Fin n))
    (f : (Fin n → Bool) → Bool) (bank : (Fin n → Bool) → Fin m → Bool)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hfun : ∀ x : Fin n → Bool, circuitFun (n + m) C (Fin.addCases x (bank x)) = f x)
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool,
      f (Function.update x i (!x i)) ≠ f x ∧
      bank (Function.update x i (!x i)) = bank x) :
    T.card ≤ C.size + 1 := by
  let U : Finset (Fin (n + m)) := T.image (Fin.castAdd m)
  have hc := Semantic.essential_card_le (n + m) C U hlen ?_
  · have hU : U.card = T.card := by
      apply Finset.card_image_iff.mpr
      intro a _ b _ hab
      apply Fin.ext
      have hv := congrArg (fun z : Fin (n + m) => z.val) hab
      simpa using hv
    rwa [hU] at hc
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨x, hx, hb⟩ := hdep j hj
    refine ⟨Fin.addCases x (bank x), ?_⟩
    simp only [Fin.addCases_left]
    rw [hfun x, append_update, ← hb, hfun]
    exact hx

end PEqualNP.Outside.L_meta_4675.MatchingBank
