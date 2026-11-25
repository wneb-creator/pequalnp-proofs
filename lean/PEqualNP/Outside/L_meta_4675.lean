import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675

lemma rectangle_star {p l : ℕ} (E : Finset (Fin p × Fin l))
    (h4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (ha : A.Nonempty) (hb : B.Nonempty)
    (hab : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    (∃ a : Fin p, ∀ a' ∈ A, a' = a) ∨
      (∃ b : Fin l, ∀ b' ∈ B, b' = b) := by
  by_cases hA : A.card ≤ 1
  · obtain ⟨a, ha⟩ := ha
    exact Or.inl ⟨a, fun a' ha' => Finset.card_le_one.mp hA a' ha' a ha⟩
  · have hB : B.card ≤ 1 := by
      by_contra hB
      obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
      obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp (show 1 < B.card by omega)
      exact h4 a a' b b' haa' hbb'
        ⟨hab a ha b hb, hab a ha b' hb', hab a' ha' b hb, hab a' ha' b' hb'⟩
    obtain ⟨b, hb⟩ := hb
    exact Or.inr ⟨b, fun b' hb' => Finset.card_le_one.mp hB b' hb' b hb⟩

lemma rectangle_center {p l : ℕ} (E : Finset (Fin p × Fin l))
    (h4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (ha : A.Nonempty) (hb : B.Nonempty)
    (hab : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    ∃ c : Fin (p + l), ∀ a ∈ A, ∀ b ∈ B,
      Fin.castAdd l a = c ∨ Fin.natAdd p b = c := by
  rcases rectangle_star E h4 A B ha hb hab with ⟨a, ha⟩ | ⟨b, hb⟩
  · exact ⟨Fin.castAdd l a, fun a' ha' _ _ => Or.inl (congrArg (Fin.castAdd l) (ha a' ha'))⟩
  · exact ⟨Fin.natAdd p b, fun _ _ b' hb' => Or.inr (congrArg (Fin.natAdd p) (hb b' hb'))⟩

lemma rectangle_cover {p l k : ℕ} (E : Finset (Fin p × Fin l))
    (h4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Fin k → Finset (Fin p)) (B : Fin k → Finset (Fin l))
    (ha : ∀ i, (A i).Nonempty) (hb : ∀ i, (B i).Nonempty)
    (hab : ∀ i, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ E)
    (cover : ∀ a b, (a, b) ∈ E → ∃ i, a ∈ A i ∧ b ∈ B i) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      S.card ≤ k := by
  classical
  choose c hc using fun i => rectangle_center E h4 (A i) (B i) (ha i) (hb i) (hab i)
  refine ⟨Finset.univ.image c, ?_, ?_⟩
  · intro a b hab
    obtain ⟨i, hai, hbi⟩ := cover a b hab
    rcases hc i a hai b hbi with h | h
    · exact Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩)
  · exact (Finset.card_image_le).trans (by simp)

end PEqualNP.Outside.L_meta_4675

namespace PEqualNP.Outside.L_meta_4675

lemma linear_and_prune {α : Type*} [DecidableEq α]
    (A : Finset α) (f g : (α → Bool) → Bool)
    (hf : ∀ x y, (∀ a, x a = true → y a = true) → f x = true → f y = true)
    (hg : ∀ x y, (∀ a, x a = true → y a = true) → g x = true → g y = true)
    (hfg : ∀ x, (f x && g x) = decide (∃ a ∈ A, x a = true)) :
    (∀ x, f x = decide (∃ a ∈ A, x a = true)) ∨
      (∀ x, g x = decide (∃ a ∈ A, x a = true)) := by
  classical
  let z : α → Bool := fun a => decide (a ∉ A)
  have hz : ¬ ∃ a ∈ A, z a = true := by simp [z]
  have off : f z = false ∨ g z = false := by
    have h := hfg z
    simpa only [hz, decide_false, Bool.and_eq_false_iff] using h
  have prune (q : (α → Bool) → Bool)
      (hq : ∀ x y, (∀ a, x a = true → y a = true) → q x = true → q y = true)
      (hoff : q z = false)
      (hon : ∀ x, (∃ a ∈ A, x a = true) → q x = true) :
      ∀ x, q x = decide (∃ a ∈ A, x a = true) := by
    intro x
    by_cases hx : ∃ a ∈ A, x a = true
    · simpa [hx] using hon x hx
    · have xz : ∀ a, x a = true → z a = true := by
        intro a ha
        simp only [z, decide_eq_true_eq]
        exact fun hA => hx ⟨a, hA, ha⟩
      have hqx : q x = false := by
        cases h : q x with
        | false => rfl
        | true =>
          have h' := hq x z xz h
          simp [hoff] at h'
      simpa [hx] using hqx
  rcases off with hoff | hoff
  · apply Or.inl
    apply prune f hf hoff
    intro x hx
    have h := hfg x
    simp only [hx, decide_true, Bool.and_eq_true] at h
    exact h.1
  · apply Or.inr
    apply prune g hg hoff
    intro x hx
    have h := hfg x
    simp only [hx, decide_true, Bool.and_eq_true] at h
    exact h.2

end PEqualNP.Outside.L_meta_4675

namespace PEqualNP.Outside.L_meta_4675

lemma no_twoColour {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit}
    {s : ℕ → Bool} (h : PEqualNP.TwoColour.tCount n C s = 0) (g : ℕ) :
    ¬ PEqualNP.TwoColour.IsTwoColour n C s g := by
  intro hg
  have he : PEqualNP.TwoColour.twoColour n C s = ∅ := Finset.card_eq_zero.mp h
  have hm : g ∈ PEqualNP.TwoColour.twoColour n C s :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.1, hg⟩
  rw [he] at hm
  simp at hm

lemma orIn_colour_eq {n : ℕ} {C : PEqualNP.CircuitLowerBounds.Circuit}
    {s : ℕ → Bool} (h : PEqualNP.TwoColour.tCount n C s = 0)
    {g : ℕ} (hg : g < C.gates.length)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op =
      PEqualNP.CircuitLowerBounds.GateOp.or)
    {i j : Fin n} (hi : i ∈ PEqualNP.TopForm.orIn n C (n + g))
    (hj : j ∈ PEqualNP.TopForm.orIn n C (n + g)) : s i = s j := by
  have hn := no_twoColour h g
  cases hsi : s i <;> cases hsj : s j
  · rfl
  · exact False.elim (hn ⟨hg, hop, ⟨i, hi, hsi⟩, ⟨j, hj, hsj⟩⟩)
  · exact False.elim (hn ⟨hg, hop, ⟨j, hj, hsj⟩, ⟨i, hi, hsi⟩⟩)
  · rfl

end PEqualNP.Outside.L_meta_4675

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

namespace PEqualNP.Outside.L_meta_4675

open PEqualNP.CircuitLowerBounds

def maskedOr : Circuit :=
  ⟨[⟨GateOp.and, [0, 0]⟩, ⟨GateOp.or, [2, 1]⟩], 3⟩

lemma maskedOr_isAO2 : PEqualNP.TopForm.IsAO2 2 maskedOr := by decide

lemma maskedOr_tCount :
    PEqualNP.TwoColour.tCount 2 maskedOr (fun i => decide (1 ≤ i)) = 0 := by decide

lemma maskedOr_point :
    PEqualNP.MetaComplexity.circuitFun 2 maskedOr
      (fun i => decide (i = (0 : Fin 2))) = true := by decide

lemma maskedOr_line :
    PEqualNP.MetaComplexity.circuitFun 2 maskedOr
      (fun i => decide (i = (1 : Fin 2))) = true := by decide

end PEqualNP.Outside.L_meta_4675

namespace PEqualNP.Outside.L_meta_4675

def independentLines {p l : ℕ} (E : Finset (Fin p × Fin l))
    (z : Fin p → Bool) (b : Fin l) : Bool :=
  decide (∀ a, (a, b) ∈ E → z a = false)

lemma edge_certificate {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : (Fin (p + l) → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hpos : ∀ a b, (a, b) ∈ E →
      f (fun i => decide (i = Fin.castAdd l a ∨ i = Fin.natAdd p b)) = true)
    (hneg : ∀ z : Fin p → Bool, f (Fin.addCases z (independentLines E z)) = false) :
    ∀ x, f x = true ↔ ∃ a b, (a, b) ∈ E ∧
      x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true := by
  intro x
  constructor
  · intro hon
    by_contra hnone
    let z : Fin p → Bool := fun a => x (Fin.castAdd l a)
    have lift : ∀ i : Fin (p + l), x i = true →
        Fin.addCases z (independentLines E z) i = true := by
      intro i
      refine Fin.addCases (m := p) (n := l) (fun a ha => ?_) (fun b hb => ?_) i
      · simpa [z] using ha
      · simp only [Fin.addCases_right, independentLines, decide_eq_true_eq]
        intro a hab
        cases hz : z a with
        | false => rfl
        | true => exact False.elim (hnone ⟨a, b, hab, hz, hb⟩)
    have bad := hmono x (Fin.addCases z (independentLines E z)) lift hon
    rw [hneg z] at bad
    contradiction
  · rintro ⟨a, b, hab, ha, hb⟩
    apply hmono _ x _ (hpos a b hab)
    intro i hi
    simp only [decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb

lemma edge_one_line {p l : ℕ} (E : Finset (Fin p × Fin l))
    (b : Fin l) (z : Fin p → Bool) :
    (∃ a b', (a, b') ∈ E ∧
      Fin.addCases z (fun j => decide (j = b)) (Fin.castAdd l a) = true ∧
      Fin.addCases z (fun j => decide (j = b)) (Fin.natAdd p b') = true) ↔
    ∃ a, (a, b) ∈ E ∧ z a = true := by
  simp only [Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b', hab, ha, rfl⟩
    exact ⟨a, hab, ha⟩
  · rintro ⟨a, hab, ha⟩
    exact ⟨a, b, hab, ha, rfl⟩

end PEqualNP.Outside.L_meta_4675

namespace PEqualNP.Outside.L_meta_4675.Buffer

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour

def bufferGate (i : ℕ) : Gate := ⟨GateOp.and, [i, i]⟩

def bufferGates (n : ℕ) : List Gate := (List.range n).map bufferGate

def shiftGate (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (n + ·)⟩

def buffered (n : ℕ) (C : Circuit) : Circuit :=
  ⟨bufferGates n ++ C.gates.map (shiftGate n), n + C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma buffered_size (n : ℕ) (C : Circuit) : (buffered n C).size = n + C.size := by
  simp [buffered, bufferGates, Circuit.size]

lemma prefix_getD (x w : List Bool) (i : ℕ) :
    (x ++ w).getD (x.length + i) false = w.getD i false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

lemma shift_step (x w : List Bool) (g : Gate) :
    step (x ++ w) (shiftGate x.length g) = x ++ step w g := by
  simp only [step, shiftGate, List.map_map]
  have h : g.inputs.map (fun i => (x ++ w).getD (x.length + i) false) =
      g.inputs.map (fun i => w.getD i false) := by
    apply List.map_congr_left
    intro i _
    exact prefix_getD x w i
  simp only [Function.comp_def]
  rw [h]
  exact List.append_assoc _ _ _

lemma shift_fold (gs : List Gate) (x w : List Bool) :
    (gs.map (shiftGate x.length)).foldl step (x ++ w) = x ++ gs.foldl step w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [shift_step, ih]

lemma buffer_fold (x : List Bool) (k : ℕ) (hk : k ≤ x.length) :
    (bufferGates k).foldl step x = x ++ x.take k := by
  induction k with
  | zero => simp [bufferGates]
  | succ k ih =>
    have hlt : k < x.length := by omega
    have hle : k ≤ x.length := by omega
    have hb : bufferGates (k + 1) = bufferGates k ++ [bufferGate k] := by
      simp [bufferGates, List.range_succ]
    rw [hb, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih hle]
    simp only [step, bufferGate, List.map_cons, List.map_nil, GateOp.eval,
      List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_self]
    rw [List.getD_append _ _ _ _ hlt, List.getD_eq_getElem _ _ hlt]
    rw [List.append_assoc, List.take_concat_get' x k hlt]

lemma buffered_wires (C : Circuit) (x : List Bool) :
    (buffered x.length C).wires x = x ++ C.wires x := by
  change (bufferGates x.length ++ C.gates.map (shiftGate x.length)).foldl step x =
    x ++ C.gates.foldl step x
  rw [List.foldl_append, buffer_fold x x.length le_rfl, List.take_length, shift_fold]

lemma buffered_fun (n : ℕ) (C : Circuit) : circuitFun n (buffered n C) = circuitFun n C := by
  funext x
  have hx : (List.ofFn x).length = n := by simp
  change ((buffered n C).wires (List.ofFn x)).getD (n + C.output) false =
    (C.wires (List.ofFn x)).getD C.output false
  have hh := buffered_wires C (List.ofFn x)
  simp only [List.length_ofFn] at hh
  rw [hh]
  simpa using prefix_getD (List.ofFn x) (C.wires (List.ofFn x)) C.output

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    Option.getD_some]
  exact List.getElem_mem hj

lemma buffered_or_inputs (n : ℕ) (C : Circuit) {g : Gate}
    (hg : g ∈ (buffered n C).gates) (ho : g.op = GateOp.or) :
    ∀ i ∈ g.inputs, n ≤ i := by
  simp only [buffered, List.mem_append] at hg
  rcases hg with hg | hg
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
    cases ho
  · obtain ⟨g, _, rfl⟩ := List.mem_map.mp hg
    intro i hi
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    omega

lemma buffered_orIn (n : ℕ) (C : Circuit) (w : ℕ) (hw : n ≤ w) :
    orIn n (buffered n C) w = ∅ := by
  apply Finset.ext
  intro i
  constructor
  · intro hi
    exfalso
    simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases hi with hi | ⟨k, hk, _, hop, hi⟩
    · have := i.isLt
      omega
    · have hge := buffered_or_inputs n C (gateAt_mem hk) hop i hi
      exact (Nat.not_le_of_gt i.isLt) hge
  · simp

lemma buffered_tCount (n : ℕ) (C : Circuit) (s : ℕ → Bool) :
    tCount n (buffered n C) s = 0 := by
  unfold tCount twoColour
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g _ hg
  rcases hg.2.2.1 with ⟨i, hi, _⟩
  rw [buffered_orIn n C (n + g) (by omega)] at hi
  simp at hi

lemma buffered_gateAt_left (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < n) :
    gateAt (buffered n C) j = bufferGate j := by
  simp [gateAt, buffered, bufferGates, List.getD_eq_getElem?_getD,
    List.getElem?_append, hj]

lemma buffered_gateAt_right (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    gateAt (buffered n C) (n + j) = shiftGate n (gateAt C j) := by
  simp [gateAt, buffered, bufferGates, List.getD_eq_getElem?_getD,
    hj]

lemma buffered_isAO2 (n : ℕ) (C : Circuit) (h : IsAO2 n C) :
    IsAO2 n (buffered n C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [buffered, List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
      exact Or.inl rfl
    · obtain ⟨g, hmem, rfl⟩ := List.mem_map.mp hg
      exact h.1 g hmem
  · intro j hj i hi
    by_cases hjn : j < n
    · rw [buffered_gateAt_left n C hjn] at hi
      simp [bufferGate] at hi
      subst i
      omega
    · obtain ⟨k, rfl⟩ : ∃ k, j = n + k := ⟨j - n, by omega⟩
      have hk : k < C.gates.length := by
        change n + k < (buffered n C).size at hj
        rw [buffered_size] at hj
        exact Nat.lt_of_add_lt_add_left hj
      rw [buffered_gateAt_right n C hk] at hi
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
      have ha' := h.2.1 k hk a ha
      omega
  · intro g hg
    simp only [buffered, List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
      rfl
    · obtain ⟨g, hmem, rfl⟩ := List.mem_map.mp hg
      simpa [shiftGate] using h.2.2 g hmem

lemma buffered_exists (n : ℕ) (C : Circuit) (h : IsAO2 n C) (s : ℕ → Bool) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size + n ∧
      circuitFun n D = circuitFun n C ∧ tCount n D s = 0 := by
  refine ⟨buffered n C, buffered_isAO2 n C h, ?_, buffered_fun n C, buffered_tCount n C s⟩
  rw [buffered_size, Nat.add_comm]

end PEqualNP.Outside.L_meta_4675.Buffer

namespace PEqualNP.Outside.L_meta_4675.OneColour

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour PEqualNP.Outside.L_meta_4675.Buffer

def rename (n p i : ℕ) : ℕ := if i < n then if i < p then n + i else i else p + i

def renameGate (n p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rename n p)⟩

def circuit (n p : ℕ) (C : Circuit) : Circuit :=
  ⟨bufferGates p ++ C.gates.map (renameGate n p), rename n p C.output⟩

lemma rename_ge (n p : ℕ) (hp : p ≤ n) (i : ℕ) : p ≤ rename n p i := by
  unfold rename
  split_ifs <;> omega

lemma rename_lt (n p m i : ℕ) (_hp : p ≤ n) (hn : n ≤ m) (hi : i < m) :
    rename n p i < p + m := by
  unfold rename
  split_ifs <;> omega

lemma rename_ge_input (n p i : ℕ) (hi : n ≤ i) : rename n p i = p + i := by
  simp [rename, Nat.not_lt.mpr hi]

lemma renamed_step (n p : ℕ) (hp : p ≤ n) (w z : List Bool)
    (hn : n ≤ w.length) (hz : z.length = p + w.length)
    (h : ∀ i, z.getD (rename n p i) false = w.getD i false) (g : Gate) :
    ∀ i, (step z (renameGate n p g)).getD (rename n p i) false =
      (step w g).getD i false := by
  have hv : (renameGate n p g).op.eval ((renameGate n p g).inputs.map fun i => z.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
    congr 1
    simp only [renameGate, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro i _
    exact h i
  intro i
  unfold step
  rw [hv]
  by_cases hi : i < w.length
  · rw [List.getD_append _ _ _ _ (by rw [hz]; exact rename_lt n p w.length i hp hn hi),
      List.getD_append _ _ _ _ hi, h i]
  · rw [rename_ge_input n p i (by omega)]
    rw [List.getD_append_right _ _ _ _ (by rw [hz]; omega),
      List.getD_append_right _ _ _ _ (by omega), hz]
    have hidx : p + i - (p + w.length) = i - w.length := by omega
    rw [hidx]

lemma renamed_fold (n p : ℕ) (hp : p ≤ n) (gs : List Gate) (w z : List Bool)
    (hn : n ≤ w.length) (hz : z.length = p + w.length)
    (h : ∀ i, z.getD (rename n p i) false = w.getD i false) :
    ∀ i, ((gs.map (renameGate n p)).foldl step z).getD (rename n p i) false =
      (gs.foldl step w).getD i false := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simpa [step] using Nat.le_trans hn (Nat.le_succ w.length)
    · simp only [step, List.length_append, List.length_singleton]
      omega
    · exact renamed_step n p hp w z hn hz h g

lemma initial_rename (x : List Bool) (p : ℕ) (hp : p ≤ x.length) (i : ℕ) :
    (x ++ x.take p).getD (rename x.length p i) false = x.getD i false := by
  unfold rename
  split_ifs with hi hip
  · rw [prefix_getD]
    simp [List.getD_eq_getElem?_getD, hip]
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

lemma circuit_fun (n p : ℕ) (hp : p ≤ n) (C : Circuit) :
    circuitFun n (circuit n p C) = circuitFun n C := by
  funext x
  change ((bufferGates p ++ C.gates.map (renameGate n p)).foldl step (List.ofFn x)).getD
    (rename n p C.output) false = (C.gates.foldl step (List.ofFn x)).getD C.output false
  rw [List.foldl_append, buffer_fold (List.ofFn x) p (by simpa using hp)]
  apply renamed_fold n p hp C.gates (List.ofFn x) ((List.ofFn x) ++ (List.ofFn x).take p)
  · simp
  · simp [Nat.min_eq_left hp, Nat.add_comm]
  · intro i
    simpa using initial_rename (List.ofFn x) p (by simpa using hp) i

lemma circuit_size (n p : ℕ) (C : Circuit) : (circuit n p C).size = C.size + p := by
  simp [circuit, bufferGates, Circuit.size, Nat.add_comm]

lemma circuit_or_inputs (n p : ℕ) (hp : p ≤ n) (C : Circuit) {g : Gate}
    (hg : g ∈ (circuit n p C).gates) (ho : g.op = GateOp.or) :
    ∀ i ∈ g.inputs, p ≤ i := by
  simp only [circuit, List.mem_append] at hg
  rcases hg with hg | hg
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
    cases ho
  · obtain ⟨g, _, rfl⟩ := List.mem_map.mp hg
    intro i hi
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    exact rename_ge n p hp j

lemma circuit_orIn (n p : ℕ) (hp : p ≤ n) (C : Circuit) (w : ℕ) (hw : n ≤ w) :
    ∀ i ∈ orIn n (circuit n p C) w, p ≤ i.val := by
  intro i hi
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with hi | ⟨k, hk, _, hop, hi⟩
  · have := i.isLt
    omega
  · exact circuit_or_inputs n p hp C (gateAt_mem hk) hop i hi

lemma circuit_tCount (n p : ℕ) (hp : p ≤ n) (C : Circuit) :
    tCount n (circuit n p C) (fun i => decide (p ≤ i)) = 0 := by
  unfold tCount twoColour
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g _ hg
  rcases hg.2.2.1 with ⟨i, hi, hfalse⟩
  have hge := circuit_orIn n p hp C (n + g) (by omega) i hi
  simp [hge] at hfalse

lemma circuit_gateAt_left (n p : ℕ) (C : Circuit) {j : ℕ} (hj : j < p) :
    gateAt (circuit n p C) j = bufferGate j := by
  simp [gateAt, circuit, bufferGates, List.getD_eq_getElem?_getD,
    List.getElem?_append, hj]

lemma circuit_gateAt_right (n p : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    gateAt (circuit n p C) (p + j) = renameGate n p (gateAt C j) := by
  simp [gateAt, circuit, bufferGates, List.getD_eq_getElem?_getD, hj]

lemma circuit_isAO2 (n p : ℕ) (hp : p ≤ n) (C : Circuit) (h : IsAO2 n C) :
    IsAO2 n (circuit n p C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
      exact Or.inl rfl
    · obtain ⟨g, hmem, rfl⟩ := List.mem_map.mp hg
      exact h.1 g hmem
  · intro j hj i hi
    by_cases hjp : j < p
    · rw [circuit_gateAt_left n p C hjp] at hi
      simp [bufferGate] at hi
      subst i
      omega
    · obtain ⟨k, rfl⟩ : ∃ k, j = p + k := ⟨j - p, by omega⟩
      have hk : k < C.gates.length := by
        change p + k < (circuit n p C).size at hj
        rw [circuit_size] at hj
        dsimp [Circuit.size] at hj
        omega
      rw [circuit_gateAt_right n p C hk] at hi
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
      have ha' := h.2.1 k hk a ha
      have hlt := rename_lt n p (n+k) a hp (by omega) ha'
      omega
  · intro g hg
    simp only [circuit, List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hg
      rfl
    · obtain ⟨g, hmem, rfl⟩ := List.mem_map.mp hg
      simpa [renameGate] using h.2.2 g hmem

lemma exists_no_twoColour (p l : ℕ) (C : Circuit) (h : IsAO2 (p + l) C) :
    ∃ D : Circuit, IsAO2 (p + l) D ∧ D.size = C.size + p ∧
      circuitFun (p + l) D = circuitFun (p + l) C ∧
      tCount (p + l) D (fun i => decide (p ≤ i)) = 0 := by
  exact ⟨circuit (p+l) p C, circuit_isAO2 (p+l) p (by omega) C h,
    circuit_size (p+l) p C, circuit_fun (p+l) p (by omega) C,
    circuit_tCount (p+l) p (by omega) C⟩

end PEqualNP.Outside.L_meta_4675.OneColour

namespace PEqualNP.Outside.L_meta_4675.SemanticLinear

def TruthMono {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true

def BelowLinear {n : ℕ} (S : Finset (Fin n)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x, f x = true → ∃ i ∈ S, x i = true

lemma and_below_linear {n : ℕ} (S : Finset (Fin n))
    (f g : (Fin n → Bool) → Bool) (hf : TruthMono f) (hg : TruthMono g)
    (h : BelowLinear S (fun x => f x && g x)) :
    BelowLinear S f ∨ BelowLinear S g := by
  classical
  by_contra hn
  have hnf : ¬ BelowLinear S f := fun h' => hn (Or.inl h')
  have hng : ¬ BelowLinear S g := fun h' => hn (Or.inr h')
  unfold BelowLinear at hnf hng
  push Not at hnf hng
  obtain ⟨x, hfx, hx⟩ := hnf
  obtain ⟨y, hgy, hy⟩ := hng
  let z : Fin n → Bool := fun i => decide (i ∉ S)
  have hfz : f z = true := hf x z (by
    intro i hi
    apply decide_eq_true
    intro his
    exact hx i his hi) hfx
  have hgz : g z = true := hg y z (by
    intro i hi
    apply decide_eq_true
    intro his
    exact hy i his hi) hgy
  obtain ⟨i, his, hiz⟩ := h z (by simp only [hfz, hgz, Bool.and_self])
  have hin : i ∉ S := of_decide_eq_true hiz
  exact hin his

lemma or_below_linear {n : ℕ} (S : Finset (Fin n))
    (f g : (Fin n → Bool) → Bool)
    (h : BelowLinear S (fun x => f x || g x)) :
    BelowLinear S f ∧ BelowLinear S g := by
  constructor
  · intro x hx
    exact h x (by simp [hx])
  · intro x hx
    exact h x (by simp [hx])

end PEqualNP.Outside.L_meta_4675.SemanticLinear

namespace PEqualNP.Outside.L_meta_4675.SemanticStarForest

lemma point_ne_line {p l : ℕ} (a : Fin p) (b : Fin l) :
    Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  have := a.isLt
  omega

lemma star_forest_cover {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hstar : ∀ a b, (a, b) ∈ E →
      (∀ b', (a, b') ∈ E → b' = b) ∨ (∀ a', (a', b) ∈ E → a' = a)) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card = ((E.image fun e => Fin.castAdd l e.1) ∪
        (E.image fun e => Fin.natAdd p e.2)).card := by
  classical
  let U : Fin p → Prop := fun a => ∀ b b', (a, b) ∈ E → (a, b') ∈ E → b = b'
  let leaf : Fin p × Fin l → Fin (p + l) := fun e =>
    if U e.1 then Fin.castAdd l e.1 else Fin.natAdd p e.2
  let center : Fin p × Fin l → Fin (p + l) := fun e =>
    if U e.1 then Fin.natAdd p e.2 else Fin.castAdd l e.1
  have hu {a : Fin p} {b : Fin l} (hab : (a, b) ∈ E) (ha : ¬ U a) :
      ∀ a', (a', b) ∈ E → a' = a := by
    rcases hstar a b hab with hp | hl
    · exact False.elim (ha (fun b1 b2 hb1 hb2 => (hp b1 hb1).trans (hp b2 hb2).symm))
    · exact hl
  have hlinj : Set.InjOn leaf (E : Set (Fin p × Fin l)) := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd h
    by_cases ha : U a <;> by_cases hc : U c
    · simp only [leaf, if_pos ha, if_pos hc] at h
      have hac : a = c := Fin.ext (congrArg (fun i : Fin (p + l) => i.val) h)
      subst c
      exact Prod.ext rfl (ha b d hab hcd)
    · simp only [leaf, if_pos ha, if_neg hc] at h
      exact False.elim (point_ne_line a d h)
    · simp only [leaf, if_neg ha, if_pos hc] at h
      exact False.elim (point_ne_line c b h.symm)
    · simp only [leaf, if_neg ha, if_neg hc] at h
      have hbd : b = d := by
        apply Fin.ext
        have hv := congrArg (fun i : Fin (p + l) => i.val) h
        simpa using hv
      subst d
      exact Prod.ext (hu hab ha c hcd).symm rfl
  have hdisj : Disjoint (E.image leaf) (E.image center) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨⟨a, b⟩, hab, habv⟩ := Finset.mem_image.mp hv
    obtain ⟨⟨c, d⟩, hcd, hcdv⟩ := Finset.mem_image.mp hw
    have h : leaf (a, b) = center (c, d) := habv.trans hcdv.symm
    by_cases ha : U a <;> by_cases hc : U c
    · simp only [leaf, center, if_pos ha, if_pos hc] at h
      exact point_ne_line a d h
    · simp only [leaf, center, if_pos ha, if_neg hc] at h
      have hac : a = c := Fin.ext (congrArg (fun i : Fin (p + l) => i.val) h)
      exact hc (hac ▸ ha)
    · simp only [leaf, center, if_neg ha, if_pos hc] at h
      have hbd : b = d := by
        apply Fin.ext
        have hv := congrArg (fun i : Fin (p + l) => i.val) h
        simpa using hv
      subst d
      have hca := hu hab ha c hcd
      exact ha (hca ▸ hc)
    · simp only [leaf, center, if_neg ha, if_neg hc] at h
      exact point_ne_line c b h.symm
  have hunion : (E.image leaf) ∪ (E.image center) =
      (E.image fun e => Fin.castAdd l e.1) ∪ (E.image fun e => Fin.natAdd p e.2) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
      · by_cases hu' : U e.1
        · exact Or.inl ⟨e, he, by simp [leaf, hu']⟩
        · exact Or.inr ⟨e, he, by simp [leaf, hu']⟩
      · by_cases hu' : U e.1
        · exact Or.inr ⟨e, he, by simp [center, hu']⟩
        · exact Or.inl ⟨e, he, by simp [center, hu']⟩
    · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
      · by_cases hu' : U e.1
        · exact Or.inl ⟨e, he, by simp [leaf, hu']⟩
        · exact Or.inr ⟨e, he, by simp [center, hu']⟩
      · by_cases hu' : U e.1
        · exact Or.inr ⟨e, he, by simp [center, hu']⟩
        · exact Or.inl ⟨e, he, by simp [leaf, hu']⟩
  refine ⟨E.image center, ?_, ?_⟩
  · intro a b hab
    by_cases ha : U a
    · right
      exact Finset.mem_image.mpr ⟨(a, b), hab, by simp [center, ha]⟩
    · left
      exact Finset.mem_image.mpr ⟨(a, b), hab, by simp [center, ha]⟩
  · rw [← hunion, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_iff.mpr hlinj]

end PEqualNP.Outside.L_meta_4675.SemanticStarForest

namespace PEqualNP.Outside.L_meta_4675.SemanticStarForest

lemma star_forest_bound {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hstar : ∀ a b, (a, b) ∈ E →
      (∀ b', (a, b') ∈ E → b' = b) ∨ (∀ a', (a', b) ∈ E → a' = a))
    (hAO : PEqualNP.TopForm.IsAO2 (p + l) C)
    (hfun : ∀ x : Fin (p + l) → Bool,
      PEqualNP.MetaComplexity.circuitFun (p + l) C x =
        decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
          x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  obtain ⟨S, hS, hcard⟩ := star_forest_cover E hstar
  refine ⟨S, hS, ?_⟩
  rw [hcard]
  exact PEqualNP.Outside.L_meta_4675.Semantic.edge_endpoints_card_le E C
    (fun g hg => (hAO.2.2 g hg).le) hfun

end PEqualNP.Outside.L_meta_4675.SemanticStarForest
