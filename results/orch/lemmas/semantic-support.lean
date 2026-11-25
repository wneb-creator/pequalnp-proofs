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

def edgeFun {p l : ℕ} (E : Finset (Fin p × Fin l)) (x : Fin (p + l) → Bool) : Bool :=
  decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
    x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)

lemma point_ne_line {p l : ℕ} (a : Fin p) (b : Fin l) :
    Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  have := a.isLt
  omega

lemma edgeFun_singleton {p l : ℕ} (E : Finset (Fin p × Fin l))
    (i : Fin (p + l)) : edgeFun E (fun j => decide (j = i)) = false := by
  apply decide_eq_false
  intro h
  obtain ⟨a, b, _, ha, hb⟩ := h
  have ha' : Fin.castAdd l a = i := of_decide_eq_true ha
  have hb' : Fin.natAdd p b = i := of_decide_eq_true hb
  exact point_ne_line a b (ha'.trans hb'.symm)

lemma edge_endpoints_card_le {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hfun : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x = edgeFun E x) :
    ((E.image fun e => Fin.castAdd l e.1) ∪
      (E.image fun e => Fin.natAdd p e.2)).card ≤ C.size + 1 := by
  apply essential_card_le (p + l) C _ hlen
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hi
    let x : Fin (p + l) → Bool := fun j => decide (j = Fin.natAdd p b)
    have hx : x (Fin.castAdd l a) = false := by simp [x, point_ne_line a b]
    have hzero : edgeFun E x = false := edgeFun_singleton E _
    have hone : edgeFun E (Function.update x (Fin.castAdd l a) (!x (Fin.castAdd l a))) = true := by
      apply decide_eq_true
      exact ⟨a, b, hab, by simp [hx], by simp [x, Ne.symm (point_ne_line a b)]⟩
    refine ⟨x, ?_⟩
    rw [hfun, hfun, hone, hzero]
    decide
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hi
    let x : Fin (p + l) → Bool := fun j => decide (j = Fin.castAdd l a)
    have hx : x (Fin.natAdd p b) = false := by simp [x, Ne.symm (point_ne_line a b)]
    have hzero : edgeFun E x = false := edgeFun_singleton E _
    have hone : edgeFun E (Function.update x (Fin.natAdd p b) (!x (Fin.natAdd p b))) = true := by
      apply decide_eq_true
      exact ⟨a, b, hab, by simp [x, point_ne_line a b], by simp [hx]⟩
    refine ⟨x, ?_⟩
    rw [hfun, hfun, hone, hzero]
    decide

lemma endpoint_images_disjoint {p l : ℕ} (E : Finset (Fin p × Fin l)) :
    Disjoint (E.image fun e => Fin.castAdd l e.1)
      (E.image fun e => Fin.natAdd p e.2) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨⟨a, b⟩, _, ha⟩ := Finset.mem_image.mp hi
  obtain ⟨⟨a', b'⟩, _, hb⟩ := Finset.mem_image.mp hj
  exact point_ne_line a b' (ha.trans hb.symm)

lemma point_star_bound {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (a0 : Fin p) (hstar : ∀ a b, (a, b) ∈ E → a = a0)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hfun : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x = edgeFun E x) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  by_cases he : E = ∅
  · subst E
    exact ⟨∅, by simp, by simp⟩
  have hne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr he
  have hpoint : (E.image fun e => Fin.castAdd l e.1) = {Fin.castAdd l a0} := by
    ext i
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨a, b⟩, hab, rfl⟩
      rw [hstar a b hab]
    · intro hi
      obtain ⟨⟨a, b⟩, hab⟩ := hne
      exact ⟨(a, b), hab, by rw [hstar a b hab]; exact hi.symm⟩
  have hline : (E.image fun e => Fin.natAdd p e.2).card = E.card := by
    apply Finset.card_image_iff.mpr
    intro e he f hf h
    apply Prod.ext
    · exact (hstar e.1 e.2 he).trans (hstar f.1 f.2 hf).symm
    · apply Fin.ext
      have hv := congrArg Fin.val h
      simpa using hv
  have hc := edge_endpoints_card_le E C hlen hfun
  rw [Finset.card_union_of_disjoint (endpoint_images_disjoint E), hpoint,
    Finset.card_singleton, hline] at hc
  refine ⟨{Fin.castAdd l a0}, ?_, ?_⟩
  · intro a b hab
    left
    simp only [Finset.mem_singleton, hstar a b hab]
  · simpa only [Finset.card_singleton, Nat.add_comm] using hc

lemma matching_bound {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hleft : Set.InjOn Prod.fst (E : Set (Fin p × Fin l)))
    (hright : Set.InjOn Prod.snd (E : Set (Fin p × Fin l)))
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hfun : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x = edgeFun E x) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  have hpcard : (E.image fun e => Fin.castAdd l e.1).card = E.card := by
    apply Finset.card_image_iff.mpr
    intro e he f hf h
    apply hleft he hf
    apply Fin.ext
    exact congrArg (fun i : Fin (p + l) => i.val) h
  have hlcard : (E.image fun e => Fin.natAdd p e.2).card = E.card := by
    apply Finset.card_image_iff.mpr
    intro e he f hf h
    apply hright he hf
    apply Fin.ext
    have hv := congrArg Fin.val h
    simpa using hv
  have hc := edge_endpoints_card_le E C hlen hfun
  rw [Finset.card_union_of_disjoint (endpoint_images_disjoint E), hpcard, hlcard] at hc
  refine ⟨E.image (fun e => Fin.castAdd l e.1), ?_, ?_⟩
  · intro a b hab
    exact Or.inl (Finset.mem_image.mpr ⟨(a, b), hab, rfl⟩)
  · rwa [hpcard]

end PEqualNP.Outside.L_meta_4675.Semantic
