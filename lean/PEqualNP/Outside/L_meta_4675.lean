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

namespace PEqualNP.Outside.L_meta_4675.SemanticMinterms

def edgeFun {p l : ℕ} (E : Finset (Fin p × Fin l)) (x : Fin (p + l) → Bool) : Bool :=
  decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
    x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)

lemma eq_edgeFun_of_pair_checks {p l : ℕ} (E : Finset (Fin p × Fin l))
    (g : (Fin (p + l) → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → g x = true → g y = true)
    (hle : ∀ x, g x = true → edgeFun E x = true)
    (hpairs : ∀ a b, (a, b) ∈ E →
      g (fun i => decide (i = Fin.castAdd l a ∨ i = Fin.natAdd p b)) = true) :
    ∀ x, g x = edgeFun E x := by
  intro x
  cases hx : edgeFun E x with
  | false =>
    cases hg : g x with
    | false => rfl
    | true =>
      have hbad := hle x hg
      simp only [hx, Bool.false_eq_true] at hbad
  | true =>
    obtain ⟨a, b, hab, hxa, hxb⟩ := of_decide_eq_true hx
    apply hmono _ x _ (hpairs a b hab)
    intro i hi
    rcases of_decide_eq_true hi with hi | hi
    · simpa only [hi] using hxa
    · simpa only [hi] using hxb

end PEqualNP.Outside.L_meta_4675.SemanticMinterms

namespace PEqualNP.Outside.L_meta_4675

def rowNegative {p l : ℕ} (E : Finset (Fin p × Fin l)) (b : Fin l) :
    Fin (p + l) → Bool :=
  Fin.addCases (fun a => decide ((a, b) ∉ E)) (fun j => decide (j = b))

lemma singleton_mem_row {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : (Fin (p + l) → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (a : Fin p) (b : Fin l)
    (ha : f (fun i => decide (i = Fin.castAdd l a)) = true)
    (hb : f (rowNegative E b) = false) : (a, b) ∈ E := by
  by_contra hab
  have hlift : ∀ i : Fin (p + l), decide (i = Fin.castAdd l a) = true →
      rowNegative E b i = true := by
    intro i hi
    have he : i = Fin.castAdd l a := of_decide_eq_true hi
    subst i
    simp [rowNegative, hab]
  have bad := hmono _ _ hlift ha
  rw [hb] at bad
  contradiction

lemma two_rows_support_card {p l : ℕ} (E : Finset (Fin p × Fin l))
    (h4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (f : (Fin (p + l) → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (b b' : Fin l) (hne : b ≠ b')
    (hb : f (rowNegative E b) = false)
    (hb' : f (rowNegative E b') = false) :
    (Finset.univ.filter fun a : Fin p =>
      f (fun i => decide (i = Fin.castAdd l a)) = true).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha a' ha'
  have hon := (Finset.mem_filter.mp ha).2
  have hon' := (Finset.mem_filter.mp ha').2
  by_contra hne'
  exact h4 a a' b b' hne' hne
    ⟨singleton_mem_row E f hmono a b hon hb,
      singleton_mem_row E f hmono a b' hon hb',
      singleton_mem_row E f hmono a' b hon' hb,
      singleton_mem_row E f hmono a' b' hon' hb'⟩

end PEqualNP.Outside.L_meta_4675

namespace PEqualNP.Outside.L_meta_4675

lemma common_neighbours_small {p l : ℕ} (E : Finset (Fin p × Fin l))
    (h4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} (haa' : a ≠ a') (B : Finset (Fin l)) :
    (B.filter fun b => (a, b) ∈ E ∧ (a', b) ∈ E).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro b hb b' hb'
  simp only [Finset.mem_filter] at hb hb'
  by_contra hbb'
  exact h4 a a' b b' haa' hbb' ⟨hb.2.1, hb'.2.1, hb.2.2, hb'.2.2⟩

lemma two_rectangle_partners_small {p l : ℕ} (E : Finset (Fin p × Fin l))
    (h4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l)) (ha : 2 ≤ A.card)
    {z z' : Fin p} (hzz' : z ≠ z')
    (hz : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E ∨ (z, b) ∈ E)
    (hz' : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E ∨ (z', b) ∈ E) :
    B.card ≤ 2 := by
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
  let U := B.filter fun b => (z, b) ∈ E ∧ (z', b) ∈ E
  let V := B.filter fun b => (a, b) ∈ E ∧ (a', b) ∈ E
  have hu : U.card ≤ 1 := common_neighbours_small E h4 hzz' B
  have hv : V.card ≤ 1 := common_neighbours_small E h4 haa' B
  have hsub : B ⊆ U ∪ V := by
    intro b hb
    by_cases hzb : (z, b) ∈ E
    · by_cases hz'b : (z', b) ∈ E
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hb, hzb, hz'b⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨hb, (hz' a ha b hb).resolve_right hz'b, (hz' a' ha' b hb).resolve_right hz'b⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨hb, (hz a ha b hb).resolve_right hzb, (hz a' ha' b hb).resolve_right hzb⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le U V)
  omega

lemma large_rectangle_partner_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (h4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l)) (ha : 2 ≤ A.card) (hb : 3 ≤ B.card)
    {z z' : Fin p}
    (hz : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E ∨ (z, b) ∈ E)
    (hz' : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E ∨ (z', b) ∈ E) :
    z = z' := by
  by_contra hzz'
  have := two_rectangle_partners_small E h4 A B ha hzz' hz hz'
  omega

end PEqualNP.Outside.L_meta_4675

namespace PEqualNP.Outside.L_meta_4675.PairClean

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj


def posRead {n : ℕ} (gs : List Gate) (w : ℕ) (x : Fin n → Bool) : Bool :=
  match w with
  | 0 => false
  | i + 1 => (wiresFrom gs (List.ofFn x)).getD i false

def clampWire (lim i : ℕ) : ℕ := if i < lim then i + 1 else 0

def gateAtPos (n : ℕ) (gs : List Gate) (w : ℕ) : Gate :=
  gs.getD (w - (n + 1)) ⟨GateOp.or, []⟩

def firstWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 0 (w-1))

def secondWire (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ :=
  clampWire (w-1) ((gateAtPos n gs w).inputs.getD 1 ((gateAtPos n gs w).inputs.getD 0 (w-1)))

def andPos (n : ℕ) (gs : List Gate) (w : ℕ) : Bool :=
  match (gateAtPos n gs w).op with
  | GateOp.and => true
  | _ => false

lemma clamp_lt (w i : ℕ) (hw : 0 < w) : clampWire (w-1) i < w := by
  unfold clampWire
  split <;> omega

lemma pos_clamp {n : ℕ} (gs : List Gate) (lim i : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire lim i) x =
    (if i < lim then (wiresFrom gs (List.ofFn x)).getD i false else false) := by
  simp only [clampWire]
  split <;> rfl

lemma pos_input {n : ℕ} (gs : List Gate) (i : ℕ) (hi : i < n) (x : Fin n → Bool) :
    posRead gs (i+1) x = x ⟨i,hi⟩ := by
  change (wiresFrom gs (List.ofFn x)).getD i false = x ⟨i,hi⟩
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem (List.ofFn x) false (by simpa using hi),List.getElem_ofFn]

lemma pos_mono {n : ℕ} (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) (x y : Fin n → Bool) (le : ∀ i, x i = true → y i = true) :
    posRead gs w x = true → posRead gs w y = true := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    apply wiresFrom_mono gs ops _ _ (by simp)
    intro j h
    by_cases hj : j < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn] at h ⊢
      exact le _ h
    · rw [List.getD_eq_default _ _ (by simp; omega)] at h
      contradiction

def edgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

def singletonBits {n : ℕ} (u : Fin n) : Fin n → Bool := fun z => decide (z = u)
def pairBits {n : ℕ} (u v : Fin n) : Fin n → Bool := fun z => decide (z = u ∨ z = v)

lemma edge_single {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    ¬ edgeTrue G (singletonBits u) := by
  rintro ⟨i,j,h,hi,hj⟩
  simp only [singletonBits, decide_eq_true_eq] at hi hj
  subst i
  subst j
  exact G.loopless.irrefl u h

lemma edge_pair {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    edgeTrue G (pairBits u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨i,j,h,hi,hj⟩
    simp only [pairBits, decide_eq_true_eq] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (G.loopless.irrefl _ h).elim
    · exact h
    · exact h.symm
    · exact (G.loopless.irrefl _ h).elim
  · intro h
    exact ⟨u,v,h,by simp [pairBits],by simp [pairBits]⟩

lemma binary_eval (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (hl : l.length ≤ 2) (nonempty : op = GateOp.and → l ≠ [])
    (v : ℕ → Bool) (lim : ℕ) (vd : v lim = false) :
    op.eval (l.map v) =
      (if (match op with | GateOp.and => true | _ => false) then
        v (l.getD 0 lim) && v (l.getD 1 (l.getD 0 lim))
       else v (l.getD 0 lim) || v (l.getD 1 (l.getD 0 lim))) := by
  cases l with
  | nil =>
    rcases hop with rfl | rfl
    · exact (nonempty rfl rfl).elim
    · simp [GateOp.eval,vd]
  | cons i t =>
    cases t with
    | nil => rcases hop with rfl | rfl <;> simp [GateOp.eval]
    | cons j t =>
      have ht : t = [] := List.length_eq_zero_iff.mp (by simpa using hl)
      subst t
      rcases hop with rfl | rfl <;> simp [GateOp.eval]

def supports {n : ℕ} (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => posRead gs w (singletonBits u) = true

lemma mem_support {n : ℕ} (gs : List Gate) (w : ℕ) (u : Fin n) :
    u ∈ supports gs w ↔ posRead gs w (singletonBits u) = true := by simp [supports]


def cleanOn {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) : Prop :=
  ∀ (j : Fin gs.length) (x : Fin n → Bool),
    (x = (fun _ => false) ∨ (∃ u, x = singletonBits u) ∨ (∃ u v, x = pairBits u v)) →
    (gs.get j).op = GateOp.and →
    (wiresFrom gs (List.ofFn x)).getD (n + j.val) false = true → edgeTrue G x

def binaryOps (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma gateAt_index {n : ℕ} (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtPos n gs (n+j+1) = gs[j] := by
  unfold gateAtPos
  rw [show n+j+1-(n+1) = j by omega,List.getD_eq_getElem _ _ hj]

lemma pos_gate {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs)
    (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length) (x : Fin n → Bool) :
    posRead gs w x =
      (if andPos n gs w then
        posRead gs (firstWire n gs w) x && posRead gs (secondWire n gs w) x
       else posRead gs (firstWire n gs w) x || posRead gs (secondWire n gs w) x) := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  have hg := ops _ (List.getElem_mem hj)
  have nonempty : gs[j].op = GateOp.and → gs[j].inputs ≠ [] := by
    intro ha hempty
    let z : Fin n → Bool := fun _ => false
    have eqg := getD_wiresFrom_gate gs (List.ofFn z) j hj
    simp only [List.length_ofFn, hempty, List.map_nil, ha, GateOp.eval, List.all_nil] at eqg
    obtain ⟨u,v,_,h,_⟩ := clean ⟨j,hj⟩ z (Or.inl rfl) ha eqg
    contradiction
  rw [hw]
  simp only [firstWire, secondWire, andPos, gateAt_index gs j hj, Nat.add_sub_cancel, pos_clamp]
  change (wiresFrom gs (List.ofFn x)).getD (n+j) false = _
  have h := getD_wiresFrom_gate gs (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  rw [h]
  exact binary_eval gs[j].op hg.1 gs[j].inputs hg.2 nonempty
    (fun i => if i < n+j then (wiresFrom gs (List.ofFn x)).getD i false else false)
    (n+j) (by simp)

lemma pos_clean {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) (x : Fin n → Bool)
    (hx : x = (fun _ => false) ∨ (∃ u, x = singletonBits u) ∨ (∃ u v, x = pairBits u v)) :
    posRead gs w x = true → edgeTrue G x := by
  let j := w-(n+1)
  have hj : j < gs.length := by dsimp [j]; omega
  have hw : w = n+j+1 := by dsimp [j]; omega
  rw [hw] at ha ⊢
  simp only [andPos, gateAt_index gs j hj] at ha
  have hop : gs[j].op = GateOp.and := by
    cases h : gs[j].op <;> simp_all
  exact clean ⟨j,hj⟩ x hx hop

lemma support_base {n : ℕ} (gs : List Gate) (w : ℕ) (hw : w < n+1) :
    (supports (n:=n) gs w).card ≤ 1 := by
  cases w with
  | zero => simp [supports,posRead]
  | succ i =>
    have hi : i < n := by omega
    have hs : supports gs (i+1) = {⟨i,hi⟩} := by
      ext u
      simp [mem_support,pos_input gs i hi,singletonBits,eq_comm]
    simp [hs]

lemma hit_base {n : ℕ} (gs : List Gate) (w : ℕ) (u v : Fin n) (hw : w < n+1) :
    posRead gs w (pairBits u v) = true → u ∈ supports gs w ∨ v ∈ supports gs w := by
  cases w with
  | zero => simp [posRead]
  | succ i =>
    have hi : i<n := by omega
    simp [mem_support,pos_input gs i hi,pairBits,singletonBits]

lemma support_and {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w) (hi : w < n+1+gs.length)
    (ha : andPos n gs w = true) : supports (n:=n) gs w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  exact edge_single G u (pos_clean G gs clean w lo hi ha _ (Or.inr (Or.inl ⟨u, rfl⟩)) ((mem_support gs w u).mp hu))

lemma support_or {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = false) :
    supports (n:=n) gs w = supports gs (firstWire n gs w) ∪ supports gs (secondWire n gs w) := by
  ext u
  simp only [Finset.mem_union,mem_support,pos_gate G gs ops clean w lo hi,ha]
  simp

lemma cross_support {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (ops : binaryOps gs) (clean : cleanOn G gs) (w : ℕ) (lo : n+1 ≤ w)
    (hi : w < n+1+gs.length) (ha : andPos n gs w = true)
    (u : Fin n) (hu : u ∈ supports gs (firstWire n gs w))
    (v : Fin n) (hv : v ∈ supports gs (secondWire n gs w)) : G.Adj u v := by
  apply (edge_pair G u v).mp
  apply pos_clean G gs clean w lo hi ha _ (Or.inr (Or.inr ⟨u, v, rfl⟩))
  rw [pos_gate G gs ops clean w lo hi,ha]
  simp only [ite_true, Bool.and_eq_true]
  have hm := pos_mono (n:=n) gs (fun g h => (ops g h).1)
  constructor
  · apply hm (firstWire n gs w) (singletonBits u) (pairBits u v) _ ((mem_support _ _ _).mp hu)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]
  · apply hm (secondWire n gs w) (singletonBits v) (pairBits u v) _ ((mem_support _ _ _).mp hv)
    intro i ht
    simp only [singletonBits,decide_eq_true_eq] at ht
    simp [pairBits,ht]


lemma root_read {n : ℕ} (gs : List Gate) (out : ℕ) (x : Fin n → Bool) :
    posRead gs (clampWire (n+gs.length) out) x = (Circuit.mk gs out).eval (List.ofFn x) := by
  rw [pos_clamp]
  change (if out < n+gs.length then _ else _) = (wiresFrom gs (List.ofFn x)).getD out false
  split_ifs with h
  · rfl
  · symm
    apply List.getD_eq_default
    simpa only [length_wiresFrom, List.length_ofFn] using Nat.le_of_not_lt h

lemma root_bound (n len out : ℕ) : clampWire (n+len) out < n+1+len := by
  unfold clampWire
  split <;> omega

lemma root_support_empty {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    supports (n:=n) gs (clampWire (n+gs.length) out) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u h
  apply edge_single G u
  apply (heval _).mp
  rw [← root_read]
  exact (mem_support _ _ _).mp h

lemma root_hits {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (out : ℕ)
    (heval : ∀ x, (Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x) :
    ∀ u v, G.Adj u v → posRead gs (clampWire (n+gs.length) out) (pairBits u v) = true := by
  intro u v h
  rw [root_read,heval]
  exact (edge_pair G u v).mpr h

lemma countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

lemma dag_union_bound {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (R B : Finset ℕ)
    (step : ∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
      (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  let m := R.sup id + 1
  have hr : R ⊆ Finset.range m := by
    intro w hw
    have h : w ≤ R.sup id := Finset.le_sup (f := id) hw
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have haux : (R.biUnion f).card ≤ R.card + (Finset.range m ∩ B).card := by
    apply countUnion f B m _ R hr
    intro i _ hi
    rcases step i hi with ⟨a, ha, hsub⟩ | ⟨hiB, a, ha, b, hb, hsub⟩
    · refine ⟨{a}, ?_, ?_, ?_⟩
      · simpa using ha
      · simpa using hsub
      · simp
    · refine ⟨{a,b}, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_range.mpr hb
      · simpa using hsub
      · simp only [hiB, ite_true]
        exact Finset.card_le_two
  have hl := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.range m) (s₂ := B))
  omega

lemma gate_partition_count (n len : ℕ) (A : ℕ → Bool) (S : ℕ → Finset (Fin n)) :
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = true)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      1 < (S w).card)).card +
    ((Finset.range (n + 1 + len)).filter (fun w => n + 1 ≤ w ∧ A w = false ∧
      (S w).card ≤ 1)).card ≤ len := by
  classical
  let gates := Finset.range (n + 1 + len)
  let ands := gates.filter (fun w => n + 1 ≤ w ∧ A w = true)
  let large := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ 1 < (S w).card)
  let small := gates.filter (fun w => n + 1 ≤ w ∧ A w = false ∧ (S w).card ≤ 1)
  change ands.card + large.card + small.card ≤ len
  have hdis : Disjoint ands large := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have a := (Finset.mem_filter.mp h₁).2.2
    have b := (Finset.mem_filter.mp h₂).2.2.1
    simp_all
  have hdis' : Disjoint (ands ∪ large) small := by
    apply Finset.disjoint_left.mpr
    intro w h₁ h₂
    have b := (Finset.mem_filter.mp h₂).2.2
    rcases Finset.mem_union.mp h₁ with ha | hl
    · have a := (Finset.mem_filter.mp ha).2.2
      simp_all
    · have a := (Finset.mem_filter.mp hl).2.2.2
      exact (Nat.not_lt_of_ge b.2) a
  have hsub : (ands ∪ large) ∪ small ⊆ Finset.Ico (n+1) (n+1+len) := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · rcases Finset.mem_union.mp h with h | h <;>
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
          Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
    · exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp h).2.1,
        Finset.mem_range.mp (Finset.mem_filter.mp h).1⟩
  rw [← Finset.card_union_of_disjoint hdis, ← Finset.card_union_of_disjoint hdis']
  simpa using Finset.card_le_card hsub

def coverCert {n : ℕ} (k N : ℕ) (S : ℕ → Finset (Fin n))
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w) (w : ℕ) : Finset (Fin n) :=
  if (S w).card ≤ 1 then
    if _hg : k ≤ w ∧ w < N then
      if A w = true then
        if (S (a w)).card ≤ 1 then coverCert k N S a b A ha hb (a w)
        else coverCert k N S a b A ha hb (b w)
      else
        coverCert k N S a b A ha hb (a w) ∪ coverCert k N S a b A ha hb (b w)
    else S w
  else ∅
termination_by w
decreasing_by all_goals first | exact ha _ _hg.1 _hg.2 | exact hb _ _hg.1 _hg.2

lemma cover_half (n k N r : ℕ) (G : SimpleGraph (Fin n))
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool) (hr : r < N) (hrS : S r = ∅)
    (hrH : ∀ u v, G.Adj u v → H r u v)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handS : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdag : ∀ (f : ℕ → Finset (Fin n)) (R B : Finset ℕ),
      (∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
        (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) →
      (R.biUnion f).card ≤ R.card + B.card) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ 1 + ((Finset.range N).filter fun w =>
        k ≤ w ∧ A w = false ∧ (S w).card ≤ 1).card := by
  let f := coverCert k N S a b A ha hb
  let B := (Finset.range N).filter fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1
  have feq (w : ℕ) : f w =
      if (S w).card ≤ 1 then
        if k ≤ w ∧ w < N then
          if A w = true then
            if (S (a w)).card ≤ 1 then f (a w) else f (b w)
          else f (a w) ∪ f (b w)
        else S w
      else ∅ := by
    exact coverCert.eq_1 ..
  have hit : ∀ w, w < N → (S w).card ≤ 1 →
      ∀ u v, H w u v → u ∈ f w ∨ v ∈ f w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw ht u v hwuv
      rw [feq, ite_eq_left ht]
      by_cases hkw : k ≤ w
      · rw [ite_eq_left ⟨hkw, hw⟩]
        cases hg : A w with
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          have heq := horS w hkw hw hg
          have hta : (S (a w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_left
          have htb : (S (b w)).card ≤ 1 := by
            apply (Finset.card_le_card _).trans ht
            rw [heq]
            exact Finset.subset_union_right
          have hia := ha w hkw hw
          have hib := hb w hkw hw
          rcases horH w u v hkw hw hg hwuv with h | h
          · have hitA := ih _ hia (hia.trans hw) hta u v h
            simp only [Finset.mem_union]
            tauto
          · have hitB := ih _ hib (hib.trans hw) htb u v h
            simp only [Finset.mem_union]
            tauto
        | true =>
          simp only [ite_true]
          have hz := handH w u v hkw hw hg hwuv
          by_cases htA : (S (a w)).card ≤ 1
          · rw [ite_eq_left htA]
            have hl := ha w hkw hw
            exact ih _ hl (hl.trans hw) htA u v hz.1
          · rw [ite_eq_right htA]
            have hl := hb w hkw hw
            exact ih _ hl (hl.trans hw) ((handS w hkw hw hg).resolve_left htA) u v hz.2
      · rw [ite_eq_right (fun h => hkw h.1)]
        exact hinput w u v (Nat.lt_of_not_ge hkw) hwuv
  refine ⟨f r, fun u v huv => hit r hr (by simp [hrS]) u v (hrH u v huv), ?_⟩
  have hstep (w : ℕ) (hw : 1 < (f w).card) :
      (∃ j < w, f w ⊆ f j) ∨
        (w ∈ B ∧ ∃ i < w, ∃ j < w, f w ⊆ f i ∪ f j) := by
    have ht : (S w).card ≤ 1 := by
      by_contra ht
      rw [feq, ite_eq_right ht] at hw
      simp at hw
    have hg : k ≤ w ∧ w < N := by
      by_contra h
      rw [feq, ite_eq_left ht, ite_eq_right h] at hw
      omega
    have hia := ha w hg.1 hg.2
    have hib := hb w hg.1 hg.2
    cases hop : A w with
    | false =>
      right
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.2, hg.1, hop, ht⟩,
        a w, hia, b w, hib, ?_⟩
      rw [feq, ite_eq_left ht, ite_eq_left hg, hop]
      simp
    | true =>
      left
      by_cases htA : (S (a w)).card ≤ 1
      · refine ⟨a w, hia, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_left htA]
      · refine ⟨b w, hib, ?_⟩
        rw [feq, ite_eq_left ht, ite_eq_left hg, ite_eq_left hop, ite_eq_right htA]
  simpa [B] using hdag f {r} B hstep

lemma edge_birth (n k N r : ℕ) (S : ℕ → Finset (Fin n))
    (H : ℕ → Fin n → Fin n → Prop) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (x y : Fin n) (hr : r < N) (hxy : H r x y) (hx : x ∉ S r) (hy : y ∉ S r)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hdisj : ∀ w, k ≤ w → w < N → A w = true → Disjoint (S (a w)) (S (b w))) :
    ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((x ∈ S (a w) ∧ y ∈ S (b w)) ∨ (y ∈ S (a w) ∧ x ∈ S (b w))) := by
  induction r using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hkw : k ≤ w
    · have hia := ha w hkw hr
      have hib := hb w hkw hr
      cases hop : A w with
      | false =>
        have hSw := horS w hkw hr hop
        rw [hSw, Finset.mem_union] at hx hy
        rcases horH w x y hkw hr hop hxy with h | h
        · exact ih _ hia (hia.trans hr) h (fun h => hx (.inl h)) (fun h => hy (.inl h))
        · exact ih _ hib (hib.trans hr) h (fun h => hx (.inr h)) (fun h => hy (.inr h))
      | true =>
        have htrue := handH w x y hkw hr hop hxy
        by_cases hsa : x ∈ S (a w) ∨ y ∈ S (a w)
        · by_cases hsb : x ∈ S (b w) ∨ y ∈ S (b w)
          · refine ⟨w, hkw, hr, hop, ?_⟩
            have hd := Finset.disjoint_left.mp (hdisj w hkw hr hop)
            rcases hsa with hax | hay <;> rcases hsb with hbx | hby
            · exact False.elim (hd hax hbx)
            · exact Or.inl ⟨hax, hby⟩
            · exact Or.inr ⟨hay, hbx⟩
            · exact False.elim (hd hay hby)
          · exact ih _ hib (hib.trans hr) htrue.2 (fun h => hsb (.inl h)) (fun h => hsb (.inr h))
        · exact ih _ hia (hia.trans hr) htrue.1 (fun h => hsa (.inl h)) (fun h => hsa (.inr h))
    · rcases hinput w x y (Nat.lt_of_not_ge hkw) hxy with h | h
      · exact False.elim (hx h)
      · exact False.elim (hy h)

lemma edge_finset_gate_bound (n k N : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hparents : ∀ w, k ≤ w → w < N → a w < w ∧ b w < w)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hunion : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hside : ∀ w, k ≤ w → w < N → A w = true →
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1)
    (hcover : ∀ u v, G.Adj u v → ∃ w, k ≤ w ∧ w < N ∧ A w = true ∧
      ((u ∈ S (a w) ∧ v ∈ S (b w)) ∨ (v ∈ S (a w) ∧ u ∈ S (b w)))) :
    G.edgeFinset.card ≤
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card := by
  classical
  cases isEmpty_or_nonempty (Fin n) with
  | inl h =>
    have := h
    have he : G.edgeFinset = ∅ := Finset.eq_empty_of_forall_notMem (fun e => isEmptyElim e)
    simp [he]
  | inr hn =>
    let z := Classical.choice hn
    let AS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = true)
    let OS := (Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)
    let adj (c : Fin n) (w : ℕ) := ∀ x ∈ S w, G.Adj c x
    let F (c : Fin n) (w : ℕ) := if w < N ∧ adj c w then S w else ∅
    have pick : ∀ w, ∃ (c : Fin n) (j : ℕ), w ∈ AS →
        ∀ u ∈ S (a w), ∀ v ∈ S (b w),
          (u = c ∧ v ∈ F c j) ∨ (v = c ∧ u ∈ F c j) := by
      intro w
      by_cases hw : w ∈ AS
      · obtain ⟨hN, hk, hA⟩ : w < N ∧ k ≤ w ∧ A w = true := by simpa [AS] using hw
        obtain ⟨ha,hb⟩ := hparents w hk hN
        have hJ := hjoin w hk hN hA
        rcases hside w hk hN hA with h | h
        · by_cases hne : (S (a w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (b w) = S (b w) := ite_eq_left ⟨by omega, hJ c hc⟩
            exact ⟨c, b w, fun _ u hu v hv => Or.inl ⟨Finset.card_le_one.mp h u hu c hc, hf ▸ hv⟩⟩
          · exact ⟨z, 0, fun _ u hu => (hne ⟨u,hu⟩).elim⟩
        · by_cases hne : (S (b w)).Nonempty
          · obtain ⟨c,hc⟩ := hne
            have hf : F c (a w) = S (a w) := ite_eq_left ⟨by omega, fun x hx => (hJ x hx c hc).symm⟩
            exact ⟨c, a w, fun _ u hu v hv => Or.inr ⟨Finset.card_le_one.mp h v hv c hc, hf ▸ hu⟩⟩
          · exact ⟨z, 0, fun _ _ _ v hv => (hne ⟨v,hv⟩).elim⟩
      · exact ⟨z, 0, fun h => (hw h).elim⟩
    choose cOf jOf spec using pick
    let oc (w : ℕ) := if h : ∃ c, adj c w then h.choose else z
    have owner_eq (w : ℕ) (c : Fin n) (hbig : 1 < (S w).card) (h : adj c w) : oc w = c := by
      have hex : ∃ c, adj c w := ⟨c,h⟩
      have h' : adj (oc w) w := by simpa [oc, hex] using hex.choose_spec
      by_contra hne
      obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hbig
      exact hc4 (oc w) u c v hne huv ⟨h' u hu, (h u hu).symm, h v hv, (h' v hv).symm⟩
    let R (c : Fin n) := (AS.filter (fun w => cOf w = c)).image jOf
    let B (c : Fin n) := OS.filter (fun w => oc w = c)
    have hlocal (c : Fin n) : ((R c).biUnion (F c)).card ≤ (R c).card + (B c).card := by
      apply dag_union_bound
      intro i hi
      by_cases hgood : i < N ∧ adj c i
      · have hf : F c i = S i := ite_eq_left hgood
        rw [hf] at hi
        have hk : k ≤ i := by by_contra! h; have := hsmall i h; omega
        have hA : A i = false := by
          cases he : A i with
          | false => rfl
          | true => simp [hzero i hk hgood.1 he] at hi
        have ⟨ha,hb⟩ := hparents i hk hgood.1
        have hu := hunion i hk hgood.1 hA
        have hfa : F c (a i) = S (a i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_left _ hx)⟩
        have hfb : F c (b i) = S (b i) := ite_eq_left ⟨by omega,
          fun x hx => hgood.2 x (hu ▸ Finset.mem_union_right _ hx)⟩
        right
        refine ⟨?_, a i, ha, b i, hb, ?_⟩
        · simp [B, OS, hgood.1, hk, hA, hi, owner_eq i c hi hgood.2]
        · rw [hf,hfa,hfb,hu]
      · simp [F,hgood] at hi
    let E (c : Fin n) := ((R c).biUnion (F c)).image (fun x => s(c,x))
    have subset : G.edgeFinset ⊆ Finset.univ.biUnion E := by
      intro e
      induction e using Sym2.inductionOn with
      | _ u v =>
        intro he
        have huv : G.Adj u v := G.mem_edgeFinset.mp he
        obtain ⟨w,hk,hN,hA,how⟩ := hcover u v huv
        have hw : w ∈ AS := by simp [AS,hN,hk,hA]
        have hj : jOf w ∈ R (cOf w) := Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw,rfl⟩)
        have member (t : Fin n) (ht : t ∈ F (cOf w) (jOf w)) :
            s(cOf w,t) ∈ Finset.univ.biUnion E :=
          Finset.mem_biUnion.mpr ⟨cOf w, Finset.mem_univ _,
            Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨jOf w,hj,ht⟩)⟩
        rcases how with ⟨hu,hv⟩ | ⟨hv,hu⟩
        · rcases spec w hw u hu v hv with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he] using member v ht
          · simpa only [he, Sym2.eq_swap] using member u ht
        · rcases spec w hw v hv u hu with ⟨he,ht⟩ | ⟨he,ht⟩
          · simpa only [he, Sym2.eq_swap] using member u ht
          · simpa only [he] using member v ht
    have hrs : (∑ c, (AS.filter (fun w => cOf w = c)).card) = AS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := cOf) (t := Finset.univ) (by simp)).symm
    have hbs : (∑ c, (B c).card) = OS.card :=
      (Finset.card_eq_sum_card_fiberwise (f := oc) (t := Finset.univ) (by simp)).symm
    calc
      G.edgeFinset.card ≤ (Finset.univ.biUnion E).card := Finset.card_le_card subset
      _ ≤ ∑ c, (E c).card := Finset.card_biUnion_le
      _ ≤ ∑ c, ((AS.filter (fun w => cOf w = c)).card + (B c).card) := by
        apply Finset.sum_le_sum
        intro c _
        exact Finset.card_image_le.trans ((hlocal c).trans (Nat.add_le_add_right Finset.card_image_le _))
      _ = _ := by rw [Finset.sum_add_distrib, hrs, hbs]

lemma total_from_model (n k N r L : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : ℕ → Finset (Fin n)) (H : ℕ → Fin n → Fin n → Prop)
    (a b : ℕ → ℕ) (A : ℕ → Bool)
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hr : r < N) (hrS : S r = ∅) (hrH : ∀ u v, G.Adj u v → H r u v)
    (hsmall : ∀ w < k, (S w).card ≤ 1)
    (hinput : ∀ w u v, w < k → H w u v → u ∈ S w ∨ v ∈ S w)
    (ha : ∀ w, k ≤ w → w < N → a w < w)
    (hb : ∀ w, k ≤ w → w < N → b w < w)
    (horS : ∀ w, k ≤ w → w < N → A w = false → S w = S (a w) ∪ S (b w))
    (horH : ∀ w u v, k ≤ w → w < N → A w = false → H w u v →
      H (a w) u v ∨ H (b w) u v)
    (handH : ∀ w u v, k ≤ w → w < N → A w = true → H w u v →
      H (a w) u v ∧ H (b w) u v)
    (hzero : ∀ w, k ≤ w → w < N → A w = true → S w = ∅)
    (hjoin : ∀ w, k ≤ w → w < N → A w = true →
      ∀ u ∈ S (a w), ∀ v ∈ S (b w), G.Adj u v)
    (hpartition :
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = true)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ 1 < (S w).card)).card +
      ((Finset.range N).filter (fun w => k ≤ w ∧ A w = false ∧ (S w).card ≤ 1)).card ≤ L) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ L + 1 := by
  classical
  have hd (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) : Disjoint (S (a w)) (S (b w)) := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    exact G.loopless.irrefl t (hjoin w hk hN hA t ht t ht')
  have hside (w : ℕ) (hk : k ≤ w) (hN : w < N) (hA : A w = true) :
      (S (a w)).card ≤ 1 ∨ (S (b w)).card ≤ 1 := by
    by_contra! hf
    obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hf.1
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hf.2
    have hJ := hjoin w hk hN hA
    exact hc4 u x v y huv hxy ⟨hJ u hu x hx, (hJ v hv x hx).symm, hJ v hv y hy, (hJ u hu y hy).symm⟩
  have births (u v) (huv : G.Adj u v) := edge_birth n k N r S H a b A u v hr
    (hrH u v huv) (by simp [hrS]) (by simp [hrS]) hinput ha hb horS horH handH hd
  have edgeCount := edge_finset_gate_bound n k N G S a b A hc4 hsmall
    (fun w hk hN => ⟨ha w hk hN, hb w hk hN⟩) hzero horS hjoin hside births
  obtain ⟨T,hT,hcard⟩ := cover_half n k N r G S H a b A hr hrS hrH hinput ha hb
    horS horH hside handH (fun f R B step => dag_union_bound f R B step)
  exact ⟨T,hT,by omega⟩

lemma pairCleanBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (x = (fun _ => false) ∨ (∃ u : Fin n, x = fun z => decide (z = u)) ∨ (∃ u v : Fin n, x = fun z => decide (z = u ∨ z = v))) → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1 := by
  intro n G inst hc4 gs out ops eval clean
  have he : ∀ x : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.mk gs out).eval (List.ofFn x) = true ↔ edgeTrue G x := by
    intro x
    rw [eval]
    exact decide_eq_true_iff
  apply total_from_model n (n+1) (n+1+gs.length) (clampWire (n+gs.length) out) gs.length G
    (supports gs) (fun w u v => posRead gs w (pairBits u v) = true)
    (firstWire n gs) (secondWire n gs) (andPos n gs) hc4 (root_bound n gs.length out)
    (root_support_empty G gs out he) (root_hits G gs out he) (support_base gs) (hit_base gs)
  · intro w lo _
    exact clamp_lt w _ (by omega)
  · intro w lo _
    exact clamp_lt w _ (by omega)
  · exact support_or G gs ops clean
  · intro w u v lo hi ha h
    simpa only [pos_gate G gs ops clean w lo hi,ha,Bool.false_eq_true,ite_false,Bool.or_eq_true]
      using h
  · intro w u v lo hi ha h
    simpa only [pos_gate G gs ops clean w lo hi,ha,ite_true,Bool.and_eq_true] using h
  · exact support_and G gs clean
  · exact cross_support G gs ops clean
  · exact gate_partition_count n gs.length (andPos n gs) (supports gs)

lemma core : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], (∀ p q r s : Fin m, p ≠ r → q ≠ s → ¬ (H.Adj p q ∧ H.Adj q r ∧ H.Adj r s ∧ H.Adj s p)) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ e w : Fin m, ¬ H.Adj e w → PEqualNP.EdgeOwnership.gateVal m D k (PEqualNP.EdgeOwnership.pairInput e w) = false) → ∃ S : Finset (Fin m), (∀ y z : Fin m, H.Adj y z → y ∈ S ∨ z ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 := by
  intro m H _ h4 D hM hfun hclean
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨∅, fun y => y.elim0, ?_⟩
    have he : H.edgeFinset = ∅ :=
      Finset.eq_empty_of_forall_notMem (fun e _ => Sym2.inductionOn e (fun a _ => a.elim0))
    simp [he]
  · have hmono : ∀ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      intro g hg
      have := (hM g hg).1
      simpa using this
    refine PEqualNP.Outside.L_meta_4675.PairClean.pairCleanBound m H h4 D.gates D.output
      (fun g hg => ⟨hmono g hg, (hM g hg).2⟩) (fun x => ?_) (fun i x hx hop hv => ?_)
    · have := congrFun hfun x
      simpa [PEqualNP.MetaComplexity.circuitFun, PEqualNP.MetaComplexity.NestedCover.graphFun]
        using this
    · have hop' : (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op =
          PEqualNP.CircuitLowerBounds.GateOp.and := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem _ _ i.2]
        exact hop
      have hval : ∀ e w : Fin m, ¬ H.Adj e w →
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨D.gates, 0⟩
            (List.ofFn (PEqualNP.EdgeOwnership.pairInput e w))).getD (m + (i : ℕ)) false = true →
          False := by
        intro e w hew h
        have h2 := hclean i i.2 hop' e w hew
        have h3 : PEqualNP.EdgeOwnership.gateVal m D i (PEqualNP.EdgeOwnership.pairInput e w)
            = true := h
        rw [h2] at h3
        exact Bool.false_ne_true h3
      rcases hx with rfl | ⟨u, rfl⟩ | ⟨u, v, rfl⟩
      · exfalso
        refine hval ⟨0, hm⟩ ⟨0, hm⟩ (H.irrefl) ?_
        refine PEqualNP.Outside.L_meta_4675.PairClean.wiresFrom_mono D.gates hmono _ _ (by simp) ?_ _ hv
        intro j h
        by_cases hj : j < m
        · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn] at h
          exact absurd h Bool.false_ne_true
        · rw [List.getD_eq_default _ _ (by simp; omega)] at h
          exact absurd h Bool.false_ne_true
      · exfalso
        refine hval u u (H.irrefl) ?_
        have hxe : (fun z : Fin m => decide (z = u)) = PEqualNP.EdgeOwnership.pairInput u u := by
          funext z
          simp [PEqualNP.EdgeOwnership.pairInput]
        rw [← hxe]
        exact hv
      · by_cases hadj : H.Adj u v
        · exact ⟨u, v, hadj, by simp, by simp⟩
        · exact (hval u v hadj hv).elim



lemma pair_clean_lower_bound : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsAO2 x1 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (∀ x8 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 x12 : Fin x1), ¬x2.Adj x11 x12 → PEqualNP.EdgeOwnership.gateVal x1 x4 x8 (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.false) → ∃ (x9 : Finset (Fin x1)), (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∈ x9 ∨ x11 ∈ x9) ∧ x2.edgeFinset.card + x9.card ≤ x4.size + (1 : ℕ) := by
  intro n G _ C hNo hAO hfun hclean
  have h4 : ∀ p q r s : Fin n, p ≠ r → q ≠ s → ¬ (G.Adj p q ∧ G.Adj q r ∧ G.Adj r s ∧ G.Adj s p) := by
    intro p q r s hpr hqs ⟨hpq, hqr, hrs, hsp⟩
    have hc := hNo p r hpr
    have hsub : ({q, s} : Finset (Fin n)) ⊆ Finset.univ.filter (fun w => G.Adj p w ∧ G.Adj r w) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact ⟨hpq, hqr.symm⟩
      · exact ⟨hsp.symm, hrs⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hqs] at this
    omega
  have hM : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    refine ⟨?_, ?_⟩
    · rcases hAO.1 g hg with h | h <;> simp [h]
    · rw [hAO.2.2 g hg]
  exact PEqualNP.Outside.L_meta_4675.PairClean.core n G h4 C hM hfun hclean

end PEqualNP.Outside.L_meta_4675.PairClean

namespace PEqualNP.Outside.L_meta_4675.Bipartite

def cross {m n : ℕ} (E : Finset (Fin m × Fin n)) : (Fin m ⊕ Fin n) → (Fin m ⊕ Fin n) → Prop
  | .inl p, .inr q => (p,q) ∈ E
  | .inr q, .inl p => (p,q) ∈ E
  | _, _ => False

def graph {m n : ℕ} (E : Finset (Fin m × Fin n)) : SimpleGraph (Fin (m+n)) where
  Adj u v := cross E (finSumFinEquiv.symm u) (finSumFinEquiv.symm v)
  symm := ⟨by
    intro u v
    cases finSumFinEquiv.symm u <;> cases finSumFinEquiv.symm v <;> simp [cross]⟩
  loopless := ⟨by
    intro u
    cases finSumFinEquiv.symm u <;> simp [cross]⟩

lemma noRectangle {m n : ℕ} (E : Finset (Fin m × Fin n))
    (hf : ∀ a b c d, a ≠ b → c ≠ d → ¬ ((a,c) ∈ E ∧ (a,d) ∈ E ∧ (b,c) ∈ E ∧ (b,d) ∈ E)) :
    @PEqualNP.TopForm.NoFourCycle _ (graph E) (Classical.decRel _) := by
  classical
  intro a b hab
  apply Finset.card_le_one.mpr
  intro u hu v hv
  obtain ⟨hau,hbu⟩ := (Finset.mem_filter.mp hu).2
  obtain ⟨hav,hbv⟩ := (Finset.mem_filter.mp hv).2
  by_contra huv
  cases a using Fin.addCases <;> cases b using Fin.addCases <;>
    cases u using Fin.addCases <;> cases v using Fin.addCases <;>
    simp [graph,cross] at hau hbu hav hbv hab huv
  all_goals apply hf _ _ _ _ (by assumption) (by assumption) <;> exact ⟨by assumption,by assumption,by assumption,by assumption⟩

lemma counts {m n : ℕ} (E : Finset (Fin m × Fin n)) :
    E.card ≤ (letI := Classical.decRel (graph E).Adj; (graph E).edgeFinset.card) := by
  classical
  apply Finset.card_le_card_of_injOn (fun p : Fin m × Fin n => Sym2.mk (Fin.castAdd n p.1) (Fin.natAdd m p.2))
  · intro p hp
    rw [Finset.mem_coe,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
    simpa [graph,cross] using hp
  · rintro ⟨a,b⟩ _ ⟨c,d⟩ _ eq
    rcases (Sym2.mk_eq_mk_iff (p := (Fin.castAdd n a, Fin.natAdd m b)) (q := (Fin.castAdd n c, Fin.natAdd m d))).mp eq with forward|reverse
    · have hf := congrArg Prod.fst forward
      have hs := congrArg Prod.snd forward
      exact Prod.ext (by simpa using hf) (by simpa using hs)
    · have h : Fin.castAdd n a = Fin.natAdd m d := congrArg Prod.fst reverse
      have h' := congrArg Fin.val h
      simp at h'
      omega


lemma edge_card {m n : ℕ} (E : Finset (Fin m × Fin n)) :
    (letI := Classical.decRel (graph E).Adj; (graph E).edgeFinset.card) = E.card := by
  classical
  symm
  apply Finset.card_bij (fun e _ =>
    Sym2.mk (Fin.castAdd n e.1) (Fin.natAdd m e.2))
  · intro e he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    simpa [graph, cross] using he
  · rintro ⟨a, b⟩ _ ⟨c, d⟩ _ heq
    rcases (Sym2.mk_eq_mk_iff
      (p := (Fin.castAdd n a, Fin.natAdd m b))
      (q := (Fin.castAdd n c, Fin.natAdd m d))).mp heq with hf | hr
    · exact Prod.ext (by simpa using congrArg Prod.fst hf)
        (by simpa using congrArg Prod.snd hf)
    · have he : Fin.castAdd n a = Fin.natAdd m d := congrArg Prod.fst hr
      have hv := congrArg Fin.val he
      simp at hv
      omega
  · intro e he
    revert he
    refine Sym2.inductionOn e (fun u v he => ?_)
    have hadj : (graph E).Adj u v := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
    cases u using Fin.addCases <;> cases v using Fin.addCases <;>
      simp [graph, cross] at hadj
    · exact ⟨(_, _), hadj, rfl⟩
    · refine ⟨(_, _), hadj, ?_⟩
      exact Sym2.eq_swap

lemma graphFun_eq {p l : ℕ} (E : Finset (Fin p × Fin l))
    [DecidableRel (graph E).Adj] (x : Fin (p + l) → Bool) :
    PEqualNP.MetaComplexity.NestedCover.graphFun (graph E) ∅ x =
      decide (∃ a b, (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) := by
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun,
    Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
  congr 1
  apply propext
  constructor
  · rintro ⟨u, v, ha, hu, hv⟩
    cases u using Fin.addCases <;> cases v using Fin.addCases <;>
      simp [graph, cross] at ha
    · exact ⟨_, _, ha, hu, hv⟩
    · exact ⟨_, _, ha, hv, hu⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    exact ⟨Fin.castAdd l a, Fin.natAdd p b,
      by simpa [graph, cross] using hab, ha, hb⟩

lemma pair_clean_bipartite (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (h4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hAO : PEqualNP.TopForm.IsAO2 (p + l) C)
    (hfun : ∀ x : Fin (p + l) → Bool,
      PEqualNP.MetaComplexity.circuitFun (p + l) C x =
        decide (∃ a b, (a, b) ∈ E ∧
          x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (hclean : ∀ k < C.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
        PEqualNP.CircuitLowerBounds.GateOp.and →
      ∀ u v : Fin (p + l), ¬ (graph E).Adj u v →
        PEqualNP.EdgeOwnership.gateVal (p + l) C k
          (PEqualNP.EdgeOwnership.pairInput u v) = false) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  classical
  letI : DecidableRel (graph E).Adj := Classical.decRel _
  have heq : PEqualNP.MetaComplexity.circuitFun (p + l) C =
      PEqualNP.MetaComplexity.NestedCover.graphFun (graph E) ∅ := by
    funext x
    rw [hfun, graphFun_eq]
  obtain ⟨S, hcover, hsize⟩ :=
    PEqualNP.Outside.L_meta_4675.PairClean.pair_clean_lower_bound
      (p + l) (graph E) C (noRectangle E h4) hAO heq hclean
  refine ⟨S, ?_, ?_⟩
  · intro a b hab
    exact hcover (Fin.castAdd l a) (Fin.natAdd p b)
      (by simpa [graph, cross] using hab)
  · have hc := counts E
    omega

end PEqualNP.Outside.L_meta_4675.Bipartite

namespace PEqualNP.Outside.L_meta_4675.SemanticFold

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma foldl_append_length {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β) :
    (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

lemma foldl_append_getD_lt {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (k : ℕ) (hk : k < acc.length) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD k d = acc.getD k d := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have hk' : k < (acc ++ [f acc a]).length := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [ih (acc ++ [f acc a]) hk']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]

lemma foldl_append_getD_gate {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j : ℕ) (hj : j < l.length) (defaultA : α) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD (acc.length + j) d =
      f ((l.take j).foldl (fun w g => w ++ [f w g]) acc) (l.getD j defaultA) := by
  have hsplit : l = l.take j ++ l[j] :: l.drop (j + 1) := by
    have h1 := (List.take_append_drop j l).symm
    have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2]
    exact h1
  have hget : l.getD j defaultA = l[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  rw [hget]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pre := (l.take j).foldl (fun w g => w ++ [f w g]) acc
  have hprelen : pre.length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : acc.length + j < (pre ++ [f pre l[j]]).length := by
    rw [List.length_append, List.length_singleton, hprelen]
    omega
  rw [foldl_append_getD_lt f (l.drop (j + 1)) (pre ++ [f pre l[j]]) d (acc.length + j) hlt]
  rw [List.getD_eq_getElem?_getD, ← hprelen]
  simp

lemma foldl_append_take_getD {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j i : ℕ) (hj : j ≤ l.length) (hi : i < acc.length + j) :
    ((l.take j).foldl (fun w g => w ++ [f w g]) acc).getD i d =
      (l.foldl (fun w g => w ++ [f w g]) acc).getD i d := by
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hprelen : ((l.take j).foldl (fun w g => w ++ [f w g]) acc).length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left hj]
  rw [foldl_append_getD_lt f (l.drop j) _ d i (hprelen ▸ hi)]

lemma inputs_eq_pair {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ hmem
  unfold opnd
  rcases h : (gateAt C j).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
  · simp [h] at hlen
  · simp [h] at hlen
  · simp
  · simp [h] at hlen

lemma opnd_mem_inputs {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [inputs_eq_pair hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem_inputs hAO hj b)

lemma orSets_length (n : ℕ) (C : Circuit) :
    (orSets n C).length = C.gates.length := by
  unfold orSets orStep
  rw [foldl_append_length]
  simp

lemma orSets_getD_ge (n : ℕ) (C : Circuit) {j : ℕ} (hj : C.gates.length ≤ j) :
    (orSets n C).getD j [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [orSets_length]; exact hj

lemma orSets_getD_lt_or (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    (orSets n C).getD j [] =
      j :: ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (orSets n C).getD (w - n) []) := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change pre.length :: (if (gateAt C j).op = GateOp.or then
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
        (fun w => pre.getD (w - n) [])
      else []) = _
  rw [hprelen, ite_eq_left_of_eq_true _ _ (eq_true hop)]
  congr 1
  apply List.flatMap_congr
  intro w hw
  rw [List.mem_filter, decide_eq_true_eq] at hw
  have hlt : w - n < ([] : List (List ℕ)).length + j := by simp; omega
  exact foldl_append_take_getD _ C.gates [] [] j (w - n) (Nat.le_of_lt hj) hlt

lemma orSets_getD_lt_not_or (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op ≠ GateOp.or) :
    (orSets n C).getD j [] = [j] := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change pre.length :: (if (gateAt C j).op = GateOp.or then
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
        (fun w => pre.getD (w - n) [])
      else []) = [j]
  rw [hprelen, ite_eq_right_of_eq_false _ _ (eq_false hop)]

lemma orReaches_iff {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (w g : ℕ) :
    OrReaches n C w g ↔
      ∃ j < C.gates.length, w = n + j ∧
        (g = j ∨ ((gateAt C j).op = GateOp.or ∧ ∃ b : Fin 2, OrReaches n C (opnd C j b) g)) := by
  constructor
  · rintro ⟨hnw, hmem⟩
    have hlt : w - n < C.gates.length := by
      by_contra hge
      push Not at hge
      rw [orSets_getD_ge n C hge] at hmem
      simp at hmem
    refine ⟨w - n, hlt, by omega, ?_⟩
    by_cases hop : (gateAt C (w - n)).op = GateOp.or
    · rw [orSets_getD_lt_or n C hlt hop, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact Or.inl rfl
      · right
        rw [List.mem_flatMap] at hmem
        rcases hmem with ⟨u, hu, hgu⟩
        rw [List.mem_filter, decide_eq_true_eq] at hu
        rw [inputs_eq_pair hAO hlt] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu.1 with rfl | rfl
        · exact ⟨hop, 0, hu.2.1, hgu⟩
        · exact ⟨hop, 1, hu.2.1, hgu⟩
    · rw [orSets_getD_lt_not_or n C hlt hop, List.mem_singleton] at hmem
      exact Or.inl hmem
  · rintro ⟨j, hj, rfl, hcase⟩
    refine ⟨Nat.le_add_right n j, ?_⟩
    rw [Nat.add_sub_cancel_left]
    rcases hcase with rfl | ⟨hop, b, hnu, hgu⟩
    · by_cases hop : (gateAt C g).op = GateOp.or
      · rw [orSets_getD_lt_or n C hj hop]; exact List.mem_cons_self
      · rw [orSets_getD_lt_not_or n C hj hop]; exact List.mem_singleton_self g
    · rw [orSets_getD_lt_or n C hj hop, List.mem_cons]
      right
      rw [List.mem_flatMap]
      refine ⟨opnd C j b, ?_, hgu⟩
      rw [List.mem_filter, decide_eq_true_eq]
      exact ⟨opnd_mem_inputs hAO hj b, hnu, opnd_lt hAO hj b⟩

lemma orReaches_self {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (orReaches_iff hAO (n + j) j).mpr ⟨j, hj, rfl, Or.inl rfl⟩

lemma orReaches_le {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g : ℕ, OrReaches n C w g → n + g ≤ w ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨_, b, hb⟩⟩
    · exact ⟨le_rfl, hj⟩
    · have hlt : opnd C j b < n + j := opnd_lt hAO hj b
      have hrec := ih _ hlt g hb
      exact ⟨by omega, hrec.2⟩

lemma orIn_input {n : ℕ} {C : Circuit} (i : Fin n) :
    orIn n C i.val = {i} := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro (hu | ⟨k, _, ⟨hni, _⟩, _, _⟩)
    · exact Fin.ext hu
    · omega
  · rintro rfl
    exact Or.inl rfl

lemma orIn_ge {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {w : ℕ}
    (hw : n + C.gates.length ≤ w) :
    orIn n C w = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hwk, _, _⟩)
  · omega
  · rw [orReaches_iff hAO] at hwk
    rcases hwk with ⟨j, hj, rfl, _⟩
    omega

lemma orIn_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hjk, hkop, _⟩)
  · omega
  · rw [orReaches_iff hAO] at hjk
    rcases hjk with ⟨j', _, heq, hcase⟩
    have hjj' : j' = j := by omega
    subst hjj'
    rcases hcase with rfl | ⟨hor, _⟩
    · rw [hop] at hkop; cases hkop
    · rw [hop] at hor; cases hor

lemma orIn_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) := by
  ext u
  unfold orIn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hu | ⟨k, hk, hjk, hkop, huk⟩)
    · omega
    · rw [orReaches_iff hAO] at hjk
      rcases hjk with ⟨j', _, heq, hcase⟩
      have hjj' : j' = j := by omega
      subst hjj'
      rcases hcase with rfl | ⟨_, b, hb⟩
      · rw [inputs_eq_pair hAO hj] at huk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at huk
        rcases huk with h0 | h1
        · exact Or.inl (Or.inl h0)
        · exact Or.inr (Or.inl h1)
      · fin_cases b
        · exact Or.inl (Or.inr ⟨k, hk, hb, hkop, huk⟩)
        · exact Or.inr (Or.inr ⟨k, hk, hb, hkop, huk⟩)
  · rintro ((h0 | ⟨k, hk, h0k, hkop, huk⟩) | (h1 | ⟨k, hk, h1k, hkop, huk⟩))
    · right
      refine ⟨j, hj, orReaches_self hAO hj, hop, ?_⟩
      rw [h0]
      exact opnd_mem_inputs hAO hj 0
    · right
      refine ⟨k, hk, ?_, hkop, huk⟩
      exact (orReaches_iff hAO (n + j) k).mpr ⟨j, hj, rfl, Or.inr ⟨hop, 0, h0k⟩⟩
    · right
      refine ⟨j, hj, orReaches_self hAO hj, hop, ?_⟩
      rw [h1]
      exact opnd_mem_inputs hAO hj 1
    · right
      refine ⟨k, hk, ?_, hkop, huk⟩
      exact (orReaches_iff hAO (n + j) k).mpr ⟨j, hj, rfl, Or.inr ⟨hop, 1, h1k⟩⟩


lemma orIn_snoc_old {n : ℕ} (gs : List Gate) (g : Gate)
    (hAO : IsAO2 n ⟨gs, 0⟩) (w : ℕ) (hw : w < n + gs.length) :
    orIn n ⟨gs ++ [g], 0⟩ w = orIn n ⟨gs, 0⟩ w := by
  have hreach : ∀ k, OrReaches n ⟨gs ++ [g], 0⟩ w k ↔
      OrReaches n ⟨gs, 0⟩ w k := by
    intro k
    unfold OrReaches
    by_cases hn : n ≤ w
    · have hw' : w - n < (orSets n ⟨gs, 0⟩).length := by
        rw [orSets_length]
        exact Nat.sub_lt_left_of_lt_add hn hw
      unfold orSets
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      unfold orStep
      unfold orSets orStep at hw'
      rw [List.getD_append _ _ _ _ hw']
    · simp only [hn, false_and]
  ext i
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hi | ⟨k, hk, hr, hop, hm⟩)
    · exact Or.inl hi
    · have hr' := (hreach k).mp hr
      have hk' := (orReaches_le hAO w k hr').2
      have he : gateAt ⟨gs ++ [g], 0⟩ k = gateAt ⟨gs, 0⟩ k :=
        List.getD_append _ _ _ _ hk'
      exact Or.inr ⟨k, hk', hr', he ▸ hop, he ▸ hm⟩
  · rintro (hi | ⟨k, hk, hr, hop, hm⟩)
    · exact Or.inl hi
    · have he : gateAt ⟨gs ++ [g], 0⟩ k = gateAt ⟨gs, 0⟩ k :=
        List.getD_append _ _ _ _ hk
      exact Or.inr ⟨k, by simp only [List.length_append, List.length_singleton]; omega,
        (hreach k).mpr hr, he.symm ▸ hop, he.symm ▸ hm⟩


abbrev Src (n : ℕ) (ι : Type) := Option (Fin n ⊕ ι)


def srcAt {n : ℕ} {ι : Type} (x : Fin n → Bool) (t : ι → Bool) (s : Src n ι) : Bool :=
  s.elim false (Sum.elim x t)


def opv (a : Bool) (p q : Bool) : Bool := if a then p && q else p || q

lemma opv_mono (a p q p' q' : Bool) (h : p = true → p' = true) (h' : q = true → q' = true) :
    opv a p q = true → opv a p' q' = true := by
  cases a <;> cases p <;> cases q <;> cases p' <;> cases q' <;> simp_all [opv]

abbrev Prog (n : ℕ) (ι : Type) := (ι → Bool) × (ι → Fin 2 → Src n ι)

variable {n : ℕ} {ι : Type}


def Closed (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) : Prop :=
  ∀ i ∈ K, ∀ b : Fin 2, ∀ j : ι, P.2 i b = some (Sum.inr j) → j ∈ K ∧ rank j < rank i


def SolAt (P : Prog n ι) (K : Finset ι) (x : Fin n → Bool) (t : ι → Bool) : Prop :=
  ∀ i ∈ K, t i = opv (P.1 i) (srcAt x t (P.2 i 0)) (srcAt x t (P.2 i 1))


def Sol (P : Prog n ι) (K : Finset ι) (v : ι → (Fin n → Bool) → Bool) : Prop :=
  ∀ x, SolAt P K x (fun i => v i x)

lemma rank_induction (rank : ι → ℕ) (p : ι → Prop)
    (h : ∀ i, (∀ j, rank j < rank i → p j) → p i) : ∀ i, p i := by
  have key : ∀ m, ∀ i, rank i = m → p i := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih => exact fun i hi => h i fun j hj => ih (rank j) (hi ▸ hj) j rfl
  exact fun i => key _ i rfl


lemma sol_le (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) (hcl : Closed P rank K) (x : Fin n → Bool)
    (t u : ι → Bool) (ht : SolAt P K x t)
    (hs : ∀ i ∈ K, opv (P.1 i) (srcAt x u (P.2 i 0)) (srcAt x u (P.2 i 1)) = true → u i = true) :
    ∀ i ∈ K, t i = true → u i = true := by
  refine fun i => rank_induction rank (fun i => i ∈ K → t i = true → u i = true) ?_ i
  intro i ih hi hti
  rw [ht i hi] at hti
  refine hs i hi (opv_mono _ _ _ _ _ ?_ ?_ hti)
  all_goals
    intro h
    revert h
    generalize hb : P.2 i _ = s
    rcases s with _ | (a | j)
    · exact fun h => h
    · exact fun h => h
    · intro h
      obtain ⟨hj, hr⟩ := hcl i hi _ j hb
      exact ih j hr hj h


lemma le_sol (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) (hcl : Closed P rank K) (x : Fin n → Bool)
    (t u : ι → Bool) (ht : SolAt P K x t)
    (hs : ∀ i ∈ K, u i = true → opv (P.1 i) (srcAt x u (P.2 i 0)) (srcAt x u (P.2 i 1)) = true) :
    ∀ i ∈ K, u i = true → t i = true := by
  refine fun i => rank_induction rank (fun i => i ∈ K → u i = true → t i = true) ?_ i
  intro i ih hi hui
  rw [ht i hi]
  refine opv_mono _ _ _ _ _ ?_ ?_ (hs i hi hui)
  all_goals
    intro h
    revert h
    generalize hb : P.2 i _ = s
    rcases s with _ | (a | j)
    · exact fun h => h
    · exact fun h => h
    · intro h
      obtain ⟨hj, hr⟩ := hcl i hi _ j hb
      exact ih j hr hj h


lemma sol_mono (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) (hcl : Closed P rank K)
    (v : ι → (Fin n → Bool) → Bool) (hv : Sol P K v) (x y : Fin n → Bool)
    (hxy : ∀ a, x a = true → y a = true) : ∀ i ∈ K, v i x = true → v i y = true := by
  refine sol_le P rank K hcl x (fun i => v i x) (fun i => v i y) (hv x) ?_
  intro i hi h
  have e := hv y i hi
  simp only at e
  rw [e]
  refine opv_mono _ _ _ _ _ ?_ ?_ h
  all_goals
    generalize P.2 i _ = s
    rcases s with _ | (a | j)
    · exact fun h => h
    · exact hxy a
    · exact fun h => h


lemma sol_exists (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) (hcl : Closed P rank K) :
    ∃ v : ι → (Fin n → Bool) → Bool, Sol P K v := by
  classical
  suffices h : ∀ L : Finset ι, L ⊆ K → Closed P rank L → ∃ v : ι → (Fin n → Bool) → Bool, Sol P L v from
    h K (Finset.Subset.refl K) hcl
  intro L
  induction L using Finset.induction_on_max_value rank with
  | empty => exact fun _ _ => ⟨fun _ _ => false, fun _ i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha hmax ih =>
    intro hsub hL
    have hs : Closed P rank s := by
      intro i hi b j hj
      obtain ⟨h1, h2⟩ := hL i (Finset.mem_insert_of_mem hi) b j hj
      refine ⟨(Finset.mem_insert.1 h1).resolve_left ?_, h2⟩
      rintro rfl
      exact absurd (hmax i hi) (by omega)
    obtain ⟨v, hv⟩ := ih ((Finset.subset_insert a s).trans hsub) hs
    let v' : ι → (Fin n → Bool) → Bool := fun i x => if i = a then
      opv (P.1 a) (srcAt x (fun j => v j x) (P.2 a 0)) (srcAt x (fun j => v j x) (P.2 a 1)) else v i x
    have hsrc : ∀ i ∈ insert a s, ∀ b x, srcAt x (fun j => v' j x) (P.2 i b)
        = srcAt x (fun j => v j x) (P.2 i b) := by
      intro i hi b x
      rcases hb : P.2 i b with _ | (c | j)
      · rfl
      · rfl
      · obtain ⟨_, hr⟩ := hL i hi b j hb
        have hja : j ≠ a := by
          rintro rfl
          rcases Finset.mem_insert.1 hi with rfl | hi'
          · exact absurd hr (lt_irrefl _)
          · exact absurd (hmax i hi') (by omega)
        simp [srcAt, v', hja]
    refine ⟨v', fun x i hi => ?_⟩
    simp only
    rw [hsrc i hi 0 x, hsrc i hi 1 x]
    rcases Finset.mem_insert.1 hi with rfl | hi'
    · simp [v']
    · have hia : i ≠ a := by
        rintro rfl
        exact ha hi'
      have := hv x i hi'
      simpa [v', hia] using this

lemma wires_length (gs : List Gate) (w0 : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).length
      = w0.length + gs.length := by
  induction gs generalizing w0 with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega

lemma wires_snoc (gs : List Gate) (g : Gate) (o : ℕ) (x : List Bool) :
    (⟨gs ++ [g], o⟩ : Circuit).wires x = (⟨gs, o⟩ : Circuit).wires x
      ++ [g.op.eval (g.inputs.map fun i => ((⟨gs, o⟩ : Circuit).wires x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

lemma wireVal_old (gs : List Gate) (g : Gate) (w : ℕ) (hw : w < n + gs.length) (x : Fin n → Bool) :
    wireVal n ⟨gs ++ [g], 0⟩ w x = wireVal n ⟨gs, 0⟩ w x := by
  unfold wireVal
  rw [wires_snoc, List.getD_append]
  have : ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).length = n + gs.length := by
    have h := wires_length gs (List.ofFn x)
    rw [List.length_ofFn] at h
    exact h
  omega

lemma wireVal_new (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    wireVal n ⟨gs ++ [g], 0⟩ (n + gs.length) x
      = g.op.eval (g.inputs.map fun i => wireVal n ⟨gs, 0⟩ i x) := by
  unfold wireVal
  have : ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).length = n + gs.length := by
    have h := wires_length gs (List.ofFn x)
    rw [List.length_ofFn] at h
    exact h
  rw [wires_snoc, List.getD_append_right _ _ _ _ (by omega), this]
  simp

lemma wires_prefix (gs : List Gate) (w0 : List Bool) (i : ℕ) (hi : i < w0.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w0).getD i false
      = w0.getD i false := by
  induction gs generalizing w0 with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

lemma wireVal_input (gs : List Gate) (i : Fin n) (x : Fin n → Bool) :
    wireVal n ⟨gs, 0⟩ (i : ℕ) x = x i := by
  unfold wireVal Circuit.wires
  rw [wires_prefix _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]


lemma isAO2_snoc (gs : List Gate) (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or) (a b : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length) (h : IsAO2 n ⟨gs, 0⟩) :
    IsAO2 n ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact h1 g hg
    · rw [List.mem_singleton.1 hg]
      exact ho
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjl : j < gs.length
    · have e : gateAt ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
        exact List.getD_append _ _ _ _ hjl
      rw [e] at hi
      exact h2 j hjl i hi
    · have hj' : j = gs.length := by omega
      subst hj'
      have e : gateAt ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ gs.length = ⟨o, [a, b]⟩ := by
        simp [gateAt]
      rw [e] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact h3 g hg
    · rw [List.mem_singleton.1 hg]
      rfl

def kept (P : Prog n ι) (v : ι → (Fin n → Bool) → Bool) (K : Finset ι) : Finset ι :=
  K.filter fun i => srcAt (fun _ => true) (fun j => v j fun _ => true) (P.2 i 0) = true ∧
    srcAt (fun _ => true) (fun j => v j fun _ => true) (P.2 i 1) = true


def srcReach {n : ℕ} {ι : Type} (R : ι → Finset (Fin n)) (s : Src n ι) : Finset (Fin n) :=
  s.elim ∅ (Sum.elim (fun i => {i}) R)

def Res (gs : List Gate) (f : (Fin n → Bool) → Bool) (R : Finset (Fin n)) : Prop :=
  (∀ x, f x = false) ∨ (f (fun _ => true) = true ∧ ∃ w < n + gs.length,
    (∀ x, wireVal n ⟨gs, 0⟩ w x = f x) ∧ orIn n ⟨gs, 0⟩ w ⊆ R)

def Good (color : Fin n → Bool) (gs : List Gate) : Prop :=
  ∀ j < gs.length, (gateAt ⟨gs, 0⟩ j).op = GateOp.or →
    ∀ u ∈ orIn n ⟨gs, 0⟩ (n + j), ∀ v ∈ orIn n ⟨gs, 0⟩ (n + j), color u = color v

lemma res_mono (gs : List Gate) (g : Gate) (hAO : IsAO2 n ⟨gs, 0⟩)
    (f : (Fin n → Bool) → Bool) (R : Finset (Fin n)) (h : Res gs f R) :
    Res (gs ++ [g]) f R := by
  rcases h with h | ⟨h1, w, hw, h2, hR⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, w, by simp; omega, ?_, ?_⟩
    · intro x
      rw [wireVal_old gs g w hw x, h2 x]
    · rwa [orIn_snoc_old gs g hAO w hw]

lemma good_snoc (color : Fin n → Bool) (gs : List Gate) (o : GateOp)
    (ho : o = GateOp.and ∨ o = GateOp.or) (a b : ℕ)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hAO : IsAO2 n ⟨gs, 0⟩) (hgood : Good color gs)
    (hcolor : o = GateOp.or →
      ∀ u ∈ orIn n ⟨gs, 0⟩ a ∪ orIn n ⟨gs, 0⟩ b,
      ∀ v ∈ orIn n ⟨gs, 0⟩ a ∪ orIn n ⟨gs, 0⟩ b, color u = color v) :
    Good color (gs ++ [⟨o, [a, b]⟩]) := by
  intro j hj hjop u hu v hv
  by_cases hjold : j < gs.length
  · have he : gateAt ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ j = gateAt ⟨gs, 0⟩ j :=
      List.getD_append _ _ _ _ hjold
    rw [orIn_snoc_old gs _ hAO (n + j) (by omega)] at hu hv
    exact hgood j hjold (he ▸ hjop) u hu v hv
  · have hj' : j = gs.length := by simp only [List.length_append, List.length_singleton] at hj; omega
    subst j
    have he : gateAt ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ gs.length = ⟨o, [a, b]⟩ := by simp [gateAt]
    have hop : o = GateOp.or := by simpa only [he] using hjop
    have hAO' := isAO2_snoc gs o ho a b ha hb hAO
    have hr := orIn_or hAO' (by simp) hjop
    have h0 : opnd ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ gs.length 0 = a := by simp [opnd, he]
    have h1 : opnd ⟨gs ++ [⟨o, [a, b]⟩], 0⟩ gs.length 1 = b := by simp [opnd, he]
    rw [hr, h0, h1, orIn_snoc_old gs _ hAO a ha, orIn_snoc_old gs _ hAO b hb] at hu hv
    exact hcolor hop u hu v hv

lemma build (P : Prog n ι) (rank : ι → ℕ) (v : ι → (Fin n → Bool) → Bool)
    (K : Finset ι) (R : ι → Finset (Fin n)) (color : Fin n → Bool)
    (hcl : Closed P rank K) (hv : Sol P K v)
    (hR : ∀ i ∈ K, P.1 i = false → srcReach R (P.2 i 0) ∪ srcReach R (P.2 i 1) ⊆ R i)
    (hcolor : ∀ i ∈ K, P.1 i = false → ∀ u ∈ R i, ∀ w ∈ R i, color u = color w) :
    ∃ gs : List Gate, IsAO2 n ⟨gs, 0⟩ ∧ Good color gs ∧
      gs.length ≤ (kept P v K).card ∧ ∀ i ∈ K, Res gs (v i) (R i) := by
  classical
  induction K using Finset.induction_on_max_value rank with
  | empty =>
    refine ⟨[], ⟨?_, ?_, ?_⟩, ?_, by simp, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    · intro g hg; simp at hg
    · intro j hj; simp at hj
    · intro g hg; simp at hg
    · intro j hj; simp at hj
  | insert a s ha hmax ih =>
    have hs : Closed P rank s := by
      intro i hi b j hj
      obtain ⟨h1, h2⟩ := hcl i (Finset.mem_insert_of_mem hi) b j hj
      refine ⟨(Finset.mem_insert.1 h1).resolve_left ?_, h2⟩
      rintro rfl
      exact absurd (hmax i hi) (by omega)
    obtain ⟨gs, hAO, hgood, hlen, hres⟩ := ih hs
      (fun x i hi => hv x i (Finset.mem_insert_of_mem hi))
      (fun i hi => hR i (Finset.mem_insert_of_mem hi))
      (fun i hi => hcolor i (Finset.mem_insert_of_mem hi))
    have hsrc : ∀ b : Fin 2,
        Res gs (fun x => srcAt x (fun j => v j x) (P.2 a b)) (srcReach R (P.2 a b)) := by
      intro b
      rcases hb : P.2 a b with _ | (c | j)
      · exact Or.inl fun x => rfl
      · refine Or.inr ⟨rfl, c, by have := c.2; omega, fun x => wireVal_input gs c x, ?_⟩
        rw [orIn_input]
        exact Finset.Subset.refl _
      · obtain ⟨h1, h2⟩ := hcl a (Finset.mem_insert_self a s) b j hb
        refine hres j ((Finset.mem_insert.1 h1).resolve_left ?_)
        rintro rfl
        exact absurd h2 (lt_irrefl _)
    have hva : ∀ x, v a x = opv (P.1 a) (srcAt x (fun j => v j x) (P.2 a 0))
        (srcAt x (fun j => v j x) (P.2 a 1)) := fun x => hv x a (Finset.mem_insert_self a s)
    have hsub : kept P v s ⊆ kept P v (insert a s) :=
      Finset.filter_subset_filter _ (Finset.subset_insert a s)
    have hlen' : gs.length ≤ (kept P v (insert a s)).card := hlen.trans (Finset.card_le_card hsub)
    have same : Res gs (v a) (R a) → ∃ gs : List Gate,
        IsAO2 n ⟨gs, 0⟩ ∧ Good color gs ∧ gs.length ≤ (kept P v (insert a s)).card ∧
        ∀ i ∈ insert a s, Res gs (v i) (R i) := by
      intro h
      refine ⟨gs, hAO, hgood, hlen', fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · exact h
      · exact hres i hi'
    simp only [Res] at hsrc
    rcases hsrc 0 with h0 | ⟨h0, w0, hw0, hv0, hr0⟩
    · refine same ?_
      cases hop : P.1 a
      · rcases hsrc 1 with h1 | ⟨h1, w1, hw1, hv1, hr1⟩
        · exact Or.inl fun x => by rw [hva x, h0 x, h1 x, hop]; rfl
        · refine Or.inr ⟨by rw [hva, h0, h1, hop]; rfl, w1, hw1, ?_, ?_⟩
          · intro x
            rw [hv1 x, hva x, h0 x, hop]; simp [opv]
          · intro u hu
            exact hR a (Finset.mem_insert_self a s) hop (Finset.mem_union_right _ (hr1 hu))
      · exact Or.inl fun x => by rw [hva x, h0 x, hop]; rfl
    · rcases hsrc 1 with h1 | ⟨h1, w1, hw1, hv1, hr1⟩
      · refine same ?_
        cases hop : P.1 a
        · refine Or.inr ⟨by rw [hva, h0, h1, hop]; rfl, w0, hw0, ?_, ?_⟩
          · intro x
            rw [hv0 x, hva x, h1 x, hop]; simp [opv]
          · intro u hu
            exact hR a (Finset.mem_insert_self a s) hop (Finset.mem_union_left _ (hr0 hu))
        · exact Or.inl fun x => by rw [hva x, h1 x, hop]; simp [opv]
      · have hak : a ∈ kept P v (insert a s) :=
          Finset.mem_filter.2 ⟨Finset.mem_insert_self a s, h0, h1⟩
        have hcard : (kept P v s).card + 1 ≤ (kept P v (insert a s)).card := by
          have hnot : a ∉ kept P v s := fun h => ha (Finset.mem_filter.1 h).1
          rw [← Finset.card_insert_of_notMem hnot]
          exact Finset.card_le_card (Finset.insert_subset hak hsub)
        let o : GateOp := if P.1 a then GateOp.and else GateOp.or
        have ho : o = GateOp.and ∨ o = GateOp.or := by
          by_cases h : P.1 a = true <;> simp [o, h]
        have hor : o = GateOp.or → P.1 a = false := by
          intro h
          cases he : P.1 a <;> simp [o, he] at h ⊢
        have hreach : P.1 a = false →
            orIn n ⟨gs, 0⟩ w0 ∪ orIn n ⟨gs, 0⟩ w1 ⊆ R a := by
          intro ha' u hu
          apply hR a (Finset.mem_insert_self a s) ha'
          rcases Finset.mem_union.mp hu with hu | hu
          · exact Finset.mem_union_left _ (hr0 hu)
          · exact Finset.mem_union_right _ (hr1 hu)
        have hAO' := isAO2_snoc gs o ho w0 w1 hw0 hw1 hAO
        have hgood' : Good color (gs ++ [⟨o, [w0, w1]⟩]) := by
          apply good_snoc color gs o ho w0 w1 hw0 hw1 hAO hgood
          intro hop u hu w hw
          exact hcolor a (Finset.mem_insert_self a s) (hor hop)
            u (hreach (hor hop) hu) w (hreach (hor hop) hw)
        refine ⟨gs ++ [⟨o, [w0, w1]⟩], hAO', hgood', ?_, fun i hi => ?_⟩
        · simp only [List.length_append, List.length_singleton]; omega
        · rcases Finset.mem_insert.1 hi with rfl | hi'
          · refine Or.inr ⟨?_, n + gs.length, by simp, ?_, ?_⟩
            · rw [hva]
              rw [h0, h1]
              cases P.1 i <;> rfl
            · intro x
              rw [wireVal_new, hva x]
              simp only [List.map_cons, List.map_nil, hv0 x, hv1 x]
              by_cases h : P.1 i = true
              · simp [o, h, opv, GateOp.eval]
              · simp [o, h, opv, GateOp.eval]
            · have hi' : gs.length < (gs ++ [({ op := o, inputs := [w0, w1] } : Gate)]).length := by simp
              have he : gateAt ⟨gs ++ [⟨o, [w0, w1]⟩], 0⟩ gs.length = ⟨o, [w0, w1]⟩ := by simp [gateAt]
              cases hp : P.1 i
              · have hop : (gateAt ⟨gs ++ [⟨o, [w0, w1]⟩], 0⟩ gs.length).op = GateOp.or := by rw [he]; simp [o, hp]
                rw [orIn_or hAO' hi' hop]
                have he0 : opnd ⟨gs ++ [⟨o, [w0, w1]⟩], 0⟩ gs.length 0 = w0 := by simp [opnd, he]
                have he1 : opnd ⟨gs ++ [⟨o, [w0, w1]⟩], 0⟩ gs.length 1 = w1 := by simp [opnd, he]
                rw [he0, he1, orIn_snoc_old gs _ hAO w0 hw0, orIn_snoc_old gs _ hAO w1 hw1]
                exact hreach hp
              · have hop : (gateAt ⟨gs ++ [⟨o, [w0, w1]⟩], 0⟩ gs.length).op = GateOp.and := by rw [he]; simp [o, hp]
                rw [orIn_and hAO' hi' hop]
                exact Finset.empty_subset _
          · exact res_mono gs _ hAO _ _ (hres i hi')

lemma good_tCount_zero (gs : List Gate) (color : ℕ → Bool)
    (hgood : Good (fun i : Fin n => color i) gs) :
    PEqualNP.TwoColour.tCount n ⟨gs, 0⟩ color = 0 := by
  apply Finset.card_eq_zero.mpr
  ext j
  simp only [Finset.notMem_empty, iff_false]
  intro hj
  obtain ⟨_, hj, hop, ⟨u, hu, hcu⟩, ⟨v, hv, hcv⟩⟩ := Finset.mem_filter.mp hj
  have he := hgood j hj hop u hu v hv
  change color u = color v at he
  rw [hcu, hcv] at he
  cases he

lemma fold_prog (P : Prog n ι) (rank : ι → ℕ) (v : ι → (Fin n → Bool) → Bool)
    (K : Finset ι) (R : ι → Finset (Fin n)) (color : ℕ → Bool)
    (hcl : Closed P rank K) (hv : Sol P K v)
    (hR : ∀ i ∈ K, P.1 i = false → srcReach R (P.2 i 0) ∪ srcReach R (P.2 i 1) ⊆ R i)
    (hcolor : ∀ i ∈ K, P.1 i = false → ∀ u ∈ R i, ∀ w ∈ R i, color u = color w)
    (o : Src n ι) (ho : ∀ j, o = some (Sum.inr j) → j ∈ K)
    (h1 : srcAt (fun _ => true) (fun j => v j fun _ => true) o = true) :
    ∃ D : Circuit, IsAO2 n D ∧ PEqualNP.TwoColour.tCount n D color = 0 ∧
      D.size ≤ (kept P v K).card ∧
      (∀ x : Fin n → Bool, circuitFun n D x = srcAt x (fun j => v j x) o) ∧
      orIn n D D.output ⊆ srcReach R o := by
  obtain ⟨gs, hAO, hgood, hlen, hres⟩ := build P rank v K R (fun i => color i) hcl hv hR hcolor
  have hR' : Res gs (fun x => srcAt x (fun j => v j x) o) (srcReach R o) := by
    rcases o with _ | (c | j)
    · exact Or.inl fun x => rfl
    · refine Or.inr ⟨rfl, c, by have := c.2; omega, fun x => wireVal_input gs c x, ?_⟩
      rw [orIn_input]
      exact Finset.Subset.refl _
    · exact hres j (ho j rfl)
  rcases hR' with h | ⟨_, w, _, hw, hr⟩
  · exact absurd (h1.symm.trans (h fun _ => true)) (by decide)
  · exact ⟨⟨gs, w⟩, hAO, good_tCount_zero gs color hgood, hlen, hw, hr⟩

open PEqualNP.EdgeOwnership (gateVal pairInput)

def srcOf (n w : ℕ) : Src n ℕ := if h : w < n then some (Sum.inl ⟨w, h⟩) else some (Sum.inr (w - n))

lemma srcOf_inr (w j : ℕ) (h : srcOf n w = some (Sum.inr j)) : w = n + j := by
  unfold srcOf at h
  split_ifs at h with hw
  · simp at h
  · simp only [Option.some.injEq, Sum.inr.injEq] at h
    omega


def isA : GateOp → Bool
  | GateOp.and => true
  | _ => false


def progOf (C : Circuit) (ρ : ℕ → Fin 2 → Src n ℕ) : Prog n ℕ :=
  ⟨fun i => isA (gateAt C i).op, ρ⟩

lemma wireVal_lt (C : Circuit) (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    wireVal n C w x = x ⟨w, hw⟩ := by
  unfold wireVal Circuit.wires
  rw [wires_prefix _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma srcAt_srcOf (C : Circuit) (w : ℕ) (x : Fin n → Bool) :
    srcAt x (fun j => gateVal n C j x) (srcOf n w) = wireVal n C w x := by
  unfold srcOf
  split_ifs with hw
  · exact (wireVal_lt C w hw x).symm
  · show gateVal n C (w - n) x = _
    have : n + (w - n) = w := by omega
    unfold gateVal wireVal
    rw [this]


lemma gate_eq (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) (x : Fin n → Bool) :
    gateVal n C k x = opv (isA (gateAt C k).op) (wireVal n C (opnd C k 0) x)
      (wireVal n C (opnd C k 1) x) := by
  have hg : C.gates[k]? = some (gateAt C k) := by
    simp [gateAt, List.getD_eq_getElem?_getD, hk]
  have hmem : gateAt C k ∈ C.gates := List.mem_of_getElem? hg
  have hlen := hC.2.2 _ hmem
  have hop := hC.1 _ hmem
  have hback := hC.2.1 k hk
  have hsplit : C.gates = C.gates.take k ++ gateAt C k :: C.gates.drop (k + 1) := by
    have h := List.take_append_drop k C.gates
    rw [List.drop_eq_getElem_cons hk] at h
    have e : C.gates[k] = gateAt C k := by simp [gateAt, List.getD_eq_getElem?_getD, hk]
    rw [e] at h
    exact h.symm
  have htake : (C.gates.take k).length = k := by simp; omega
  have hold : ∀ w < n + k, wireVal n C w x = wireVal n ⟨C.gates.take k, 0⟩ w x := by
    intro w hw
    unfold wireVal Circuit.wires
    conv_lhs => rw [hsplit, List.foldl_append]
    rw [wires_prefix]
    rw [wires_length, htake]
    simpa using hw
  have hnew : gateVal n C k x = (gateAt C k).op.eval
      ((gateAt C k).inputs.map fun i => wireVal n ⟨C.gates.take k, 0⟩ i x) := by
    rw [← wireVal_new, htake]
    unfold gateVal wireVal Circuit.wires
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    rw [wires_prefix]
    · simp [List.foldl_append]
    · rw [List.length_append, wires_length, htake, List.length_ofFn]; simp
  obtain ⟨p, q, hpq⟩ : ∃ p q, (gateAt C k).inputs = [p, q] := List.length_eq_two.1 hlen
  have hp : p < n + k := hback p (by rw [hpq]; simp)
  have hq : q < n + k := hback q (by rw [hpq]; simp)
  rw [hnew]
  simp only [opnd, hpq, List.map_cons, List.map_nil, ← hold p hp, ← hold q hq]
  rcases hop with h | h <;> simp [h, GateOp.eval, opv, isA]

lemma super_of_le (C : Circuit) (hC : IsAO2 n C) (K : Finset ℕ) (hK : ∀ k ∈ K, k < C.gates.length)
    (ρ : ℕ → Fin 2 → Src n ℕ) (x : Fin n → Bool)
    (h : ∀ k ∈ K, ∀ b, srcAt x (fun j => gateVal n C j x) (ρ k b) = true → wireVal n C (opnd C k b) x = true) :
    ∀ k ∈ K, opv ((progOf C ρ).1 k) (srcAt x (fun j => gateVal n C j x) (ρ k 0))
      (srcAt x (fun j => gateVal n C j x) (ρ k 1)) = true → gateVal n C k x = true := by
  intro k hk hv
  rw [gate_eq C hC k (hK k hk) x]
  exact opv_mono _ _ _ _ _ (h k hk 0) (h k hk 1) hv


def killSrc (n j w : ℕ) : Src n ℕ := if w = n + j then none else srcOf n w

lemma killSrc_inr (j w k : ℕ) (h : killSrc n j w = some (Sum.inr k)) :
    w = n + k ∧ k ≠ j := by
  by_cases hw : w = n + j
  · simp [killSrc, hw] at h
  · have hsrc : srcOf n w = some (Sum.inr k) := by simpa [killSrc, hw] using h
    have hk := srcOf_inr w k hsrc
    exact ⟨hk, by intro he; subst k; exact hw hk⟩

lemma killSrc_le (C : Circuit) (j w : ℕ) (x : Fin n → Bool) :
    srcAt x (fun k => gateVal n C k x) (killSrc n j w) = true → wireVal n C w x = true := by
  unfold killSrc
  split_ifs with hw
  · intro h
    exact False.elim (Bool.false_ne_true h)
  · rw [srcAt_srcOf]
    exact id

lemma killSrc_eq (C : Circuit) (j w : ℕ) (x : Fin n → Bool)
    (hz : gateVal n C j x = false) :
    srcAt x (fun k => gateVal n C k x) (killSrc n j w) = wireVal n C w x := by
  unfold killSrc
  split_ifs with hw
  · subst w
    exact hz.symm
  · exact srcAt_srcOf C w x

lemma srcReach_srcOf (C : Circuit) (w : ℕ) :
    srcReach (fun k => orIn n C (n + k)) (srcOf n w) = orIn n C w := by
  unfold srcOf
  split_ifs with hw
  · exact (orIn_input (C := C) ⟨w, hw⟩).symm
  · change orIn n C (n + (w - n)) = orIn n C w
    rw [Nat.add_sub_of_le (by omega)]

lemma srcReach_kill (C : Circuit) (j w : ℕ) :
    srcReach (fun k => orIn n C (n + k)) (killSrc n j w) ⊆ orIn n C w := by
  unfold killSrc
  split_ifs
  · exact Finset.empty_subset _
  · rw [srcReach_srcOf]

lemma tCount_zero_good (C : Circuit) (color : ℕ → Bool)
    (hzero : PEqualNP.TwoColour.tCount n C color = 0) :
    Good (fun i : Fin n => color i) C.gates := by
  intro j hj hop u hu v hv
  have he : PEqualNP.TwoColour.twoColour n C color = ∅ := Finset.card_eq_zero.mp hzero
  have hn : ¬ PEqualNP.TwoColour.IsTwoColour n C color j := by
    intro h
    have hm : j ∈ PEqualNP.TwoColour.twoColour n C color :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, h⟩
    rw [he] at hm
    exact Finset.notMem_empty _ hm
  change color u = color v
  cases hcu : color u <;> cases hcv : color v
  · rfl
  · exact False.elim (hn ⟨hj, hop, ⟨u, hu, hcu⟩, ⟨v, hv, hcv⟩⟩)
  · exact False.elim (hn ⟨hj, hop, ⟨v, hv, hcv⟩, ⟨u, hu, hcu⟩⟩)
  · rfl

lemma srcAt_eq_of_eq {ι : Type} (K : Finset ι) (x : Fin n → Bool) (t u : ι → Bool)
    (o : Src n ι) (ho : ∀ j, o = some (Sum.inr j) → j ∈ K)
    (h : ∀ j ∈ K, t j = u j) : srcAt x t o = srcAt x u o := by
  rcases o with _ | (c | j)
  · rfl
  · rfl
  · exact h j (ho j rfl)

lemma srcAt_le_of_le {ι : Type} (K : Finset ι) (x : Fin n → Bool) (t u : ι → Bool)
    (o : Src n ι) (ho : ∀ j, o = some (Sum.inr j) → j ∈ K)
    (h : ∀ j ∈ K, t j = true → u j = true) : srcAt x t o = true → srcAt x u o = true := by
  rcases o with _ | (c | j)
  · exact id
  · exact id
  · exact h j (ho j rfl)

lemma isA_false_or (C : Circuit) (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (h : isA (gateAt C j).op = false) :
    (gateAt C j).op = GateOp.or := by
  have hjg : C.gates[j]? = some (gateAt C j) := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  have hjm : gateAt C j ∈ C.gates := List.mem_of_getElem? hjg
  rcases hAO.1 _ hjm with ha | ho
  · simp [ha, isA] at h
  · exact ho

lemma delete_gate (C : Circuit) (color : ℕ → Bool) (j : ℕ)
    (hAO : IsAO2 n C) (hzero : PEqualNP.TwoColour.tCount n C color = 0)
    (hj : j < C.gates.length)
    (hpos : ∃ x : Fin n → Bool, gateVal n C j x = false ∧ circuitFun n C x = true) :
    ∃ D : Circuit, IsAO2 n D ∧ PEqualNP.TwoColour.tCount n D color = 0 ∧ D.size < C.size ∧
      (∀ x : Fin n → Bool, circuitFun n D x = true → circuitFun n C x = true) ∧
      (∀ x : Fin n → Bool, gateVal n C j x = false → circuitFun n D x = circuitFun n C x) := by
  classical
  let K : Finset ℕ := (Finset.range C.gates.length).erase j
  let ρ : ℕ → Fin 2 → Src n ℕ := fun k b => killSrc n j (opnd C k b)
  let P : Prog n ℕ := progOf C ρ
  let o : Src n ℕ := killSrc n j C.output
  let R : ℕ → Finset (Fin n) := fun k => orIn n C (n + k)
  have hK : ∀ k ∈ K, k < C.gates.length := by
    intro k hk
    exact Finset.mem_range.mp (Finset.mem_erase.mp hk).2
  have hcl : Closed P id K := by
    intro k hk b i hi
    have hii : opnd C k b = n + i ∧ i ≠ j := killSrc_inr j (opnd C k b) i hi
    have hback := opnd_lt hAO (hK k hk) b
    have hik : i < k := by omega
    exact ⟨Finset.mem_erase.mpr ⟨hii.2, Finset.mem_range.mpr (lt_trans hik (hK k hk))⟩, hik⟩
  have hout : C.output < n + C.gates.length := by
    obtain ⟨x, _, hx⟩ := hpos
    by_contra h
    have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
      exact (wires_length C.gates (List.ofFn x)).trans (by simp)
    change (C.wires (List.ofFn x)).getD C.output false = true at hx
    rw [List.getD_eq_default _ _ (by omega)] at hx
    cases hx
  have ho : ∀ k, o = some (Sum.inr k) → k ∈ K := by
    intro k hk
    obtain ⟨he, hne⟩ := killSrc_inr j C.output k hk
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨v, hv⟩ := sol_exists P id K hcl
  have hsubsol (x : Fin n → Bool) : ∀ k ∈ K,
      opv (P.1 k) (srcAt x (fun i => gateVal n C i x) (P.2 k 0))
        (srcAt x (fun i => gateVal n C i x) (P.2 k 1)) = true → gateVal n C k x = true := by
    exact super_of_le C hAO K hK ρ x (fun k _ b => killSrc_le C j (opnd C k b) x)
  have hle (x : Fin n → Bool) :
      srcAt x (fun k => v k x) o = true → circuitFun n C x = true := by
    intro hx
    have hvals := sol_le P id K hcl x (fun k => v k x) (fun k => gateVal n C k x) (hv x) (hsubsol x)
    exact killSrc_le C j C.output x (srcAt_le_of_le K x _ _ o ho hvals hx)
  have heq (x : Fin n → Bool) (hz : gateVal n C j x = false) :
      srcAt x (fun k => v k x) o = circuitFun n C x := by
    have hold : SolAt P K x (fun k => gateVal n C k x) := by
      intro k hk
      change gateVal n C k x = opv (isA (gateAt C k).op)
        (srcAt x (fun i => gateVal n C i x) (killSrc n j (opnd C k 0)))
        (srcAt x (fun i => gateVal n C i x) (killSrc n j (opnd C k 1)))
      rw [killSrc_eq C j _ x hz, killSrc_eq C j _ x hz]
      exact gate_eq C hAO k (hK k hk) x
    have hvals : ∀ k ∈ K, v k x = gateVal n C k x := by
      intro k hk
      have h1 := sol_le P id K hcl x (fun k => v k x) (fun k => gateVal n C k x) (hv x)
        (fun i hi h => (hold i hi).trans h) k hk
      have h2 := le_sol P id K hcl x (fun k => v k x) (fun k => gateVal n C k x) (hv x)
        (fun i hi h => (hold i hi).symm.trans h) k hk
      apply Bool.eq_iff_iff.mpr
      exact ⟨h1, h2⟩
    rw [srcAt_eq_of_eq K x _ _ o ho hvals]
    exact killSrc_eq C j C.output x hz
  have h1 : srcAt (fun _ => true) (fun k => v k fun _ => true) o = true := by
    obtain ⟨x, hz, hx⟩ := hpos
    have hvx : srcAt x (fun k => v k x) o = true := (heq x hz).trans hx
    rcases ho' : o with _ | (c | k)
    · rw [ho'] at hvx
      exact False.elim (Bool.false_ne_true hvx)
    · rfl
    · rw [ho'] at hvx
      exact sol_mono P id K hcl v hv x (fun _ => true) (fun _ _ => rfl) k (ho k ho') hvx
  have hR : ∀ i ∈ K, P.1 i = false → srcReach R (P.2 i 0) ∪ srcReach R (P.2 i 1) ⊆ R i := by
    intro i hi hio
    have hop := isA_false_or C hAO (hK i hi) hio
    change srcReach R (killSrc n j (opnd C i 0)) ∪ srcReach R (killSrc n j (opnd C i 1)) ⊆ orIn n C (n + i)
    rw [orIn_or hAO (hK i hi) hop]
    exact Finset.union_subset_union (srcReach_kill C j _) (srcReach_kill C j _)
  have hcolor : ∀ i ∈ K, P.1 i = false → ∀ u ∈ R i, ∀ w ∈ R i, color u = color w := by
    intro i hi hio u hu w hw
    exact tCount_zero_good C color hzero i (hK i hi) (isA_false_or C hAO (hK i hi) hio) u hu w hw
  obtain ⟨D, hD, hDz, hDs, hDf, _⟩ := fold_prog P id v K R color hcl hv hR hcolor o ho h1
  refine ⟨D, hD, hDz, ?_, ?_, ?_⟩
  · have hcard : (kept P v K).card ≤ K.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hKcard : K.card < C.size := by
      dsimp [K, Circuit.size]
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hj), Finset.card_range]
      omega
    exact lt_of_le_of_lt hDs (lt_of_le_of_lt hcard hKcard)
  · intro x hx
    rw [hDf x] at hx
    exact hle x hx
  · intro x hz
    rw [hDf x]
    exact heq x hz

lemma wireVal_mono (C : Circuit) (hAO : IsAO2 n C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ w, wireVal n C w x = true → wireVal n C w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hx
    by_cases hw : w < n
    · rw [wireVal_lt C w hw x] at hx
      rw [wireVal_lt C w hw y]
      exact hxy _ hx
    · by_cases hvalid : w < n + C.gates.length
      · have hj : w - n < C.gates.length := by omega
        have hidx : n + (w - n) = w := by omega
        have ex : wireVal n C w x = gateVal n C (w - n) x := by
          unfold wireVal gateVal
          rw [hidx]
        have ey : wireVal n C w y = gateVal n C (w - n) y := by
          unfold wireVal gateVal
          rw [hidx]
        rw [ex, gate_eq C hAO (w - n) hj x] at hx
        rw [ey, gate_eq C hAO (w - n) hj y]
        apply opv_mono _ _ _ _ _ ?_ ?_ hx
        · exact ih _ (by have := opnd_lt hAO hj 0; omega)
        · exact ih _ (by have := opnd_lt hAO hj 1; omega)
      · have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length :=
          (wires_length C.gates (List.ofFn x)).trans (by simp)
        unfold wireVal at hx
        rw [List.getD_eq_default _ _ (by omega)] at hx
        cases hx

lemma graphFun_empty (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u w, G.Adj u w ∧ x u = true ∧ x w = true := by
  simp [graphFun]

lemma graphFun_pair (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (huv : G.Adj u v) : graphFun G ∅ (pairInput u v) = true := by
  apply (graphFun_empty G _).mpr
  exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

lemma delete_pair_inactive (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (color : ℕ → Bool) (j : ℕ)
    (hAO : IsAO2 n C) (hzero : PEqualNP.TwoColour.tCount n C color = 0)
    (hfun : circuitFun n C = graphFun G ∅) (hne : ∃ u v, G.Adj u v)
    (hj : j < C.gates.length)
    (hinactive : ∀ u v, G.Adj u v → gateVal n C j (pairInput u v) = false) :
    ∃ D : Circuit, IsAO2 n D ∧ PEqualNP.TwoColour.tCount n D color = 0 ∧
      D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  have hpos : ∃ x, gateVal n C j x = false ∧ circuitFun n C x = true := by
    obtain ⟨u, v, huv⟩ := hne
    refine ⟨pairInput u v, hinactive u v huv, ?_⟩
    rw [hfun]
    exact graphFun_pair G u v huv
  obtain ⟨D, hD, hDz, hDs, hle, heq⟩ := delete_gate C color j hAO hzero hj hpos
  refine ⟨D, hD, hDz, hDs, funext fun x => ?_⟩
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    rw [← hfun]
    exact hle x hx
  · intro hx
    obtain ⟨u, v, huv, hxu, hxv⟩ := (graphFun_empty G x).mp hx
    have hp : circuitFun n D (pairInput u v) = true := by
      rw [heq _ (hinactive u v huv), hfun]
      exact graphFun_pair G u v huv
    apply wireVal_mono D hD (pairInput u v) x ?_ D.output hp
    intro i hi
    simp only [pairInput, decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact hxu
    · exact hxv

lemma normalise_pair_active (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (color : ℕ → Bool)
    (hAO : IsAO2 n C) (hzero : PEqualNP.TwoColour.tCount n C color = 0)
    (hfun : circuitFun n C = graphFun G ∅) (hne : ∃ u v, G.Adj u v) :
    ∃ D : Circuit, IsAO2 n D ∧ PEqualNP.TwoColour.tCount n D color = 0 ∧
      D.size ≤ C.size ∧ circuitFun n D = graphFun G ∅ ∧
      ∀ j < D.gates.length, ∃ u v, G.Adj u v ∧ gateVal n D j (pairInput u v) = true := by
  classical
  let Q : ℕ → Prop := fun m => ∃ D : Circuit, IsAO2 n D ∧
    PEqualNP.TwoColour.tCount n D color = 0 ∧ circuitFun n D = graphFun G ∅ ∧ D.size = m
  have hex : ∃ m, Q m := ⟨C.size, C, hAO, hzero, hfun, rfl⟩
  obtain ⟨D, hD, hDz, hDf, hDs⟩ := Nat.find_spec hex
  have hmin : ∀ D' : Circuit, IsAO2 n D' → PEqualNP.TwoColour.tCount n D' color = 0 →
      circuitFun n D' = graphFun G ∅ → D.size ≤ D'.size := by
    intro D' hD' hz' hf'
    rw [hDs]
    exact Nat.find_min' hex ⟨D', hD', hz', hf', rfl⟩
  refine ⟨D, hD, hDz, hmin C hAO hzero hfun, hDf, ?_⟩
  intro j hj
  by_contra hn
  have hinactive : ∀ u v, G.Adj u v → gateVal n D j (pairInput u v) = false := by
    intro u v huv
    cases hval : gateVal n D j (pairInput u v)
    · rfl
    · exact False.elim (hn ⟨u, v, huv, hval⟩)
  obtain ⟨D', hD', hz', hs', hf'⟩ := delete_pair_inactive G D color j hD hDz hDf hne hj hinactive
  exact Nat.not_lt_of_ge (hmin D' hD' hz' hf') hs'

lemma least_pair_active (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (color : ℕ → Bool)
    (hAO : IsAO2 n C) (hzero : PEqualNP.TwoColour.tCount n C color = 0)
    (hfun : circuitFun n C = graphFun G ∅) (hne : ∃ u v, G.Adj u v)
    (hmin : ∀ D : Circuit, IsAO2 n D → PEqualNP.TwoColour.tCount n D color = 0 →
      circuitFun n D = graphFun G ∅ → C.size ≤ D.size) :
    ∀ j < C.gates.length, ∃ u v, G.Adj u v ∧ gateVal n C j (pairInput u v) = true := by
  classical
  intro j hj
  by_contra hn
  have hinactive : ∀ u v, G.Adj u v → gateVal n C j (pairInput u v) = false := by
    intro u v huv
    cases hval : gateVal n C j (pairInput u v)
    · rfl
    · exact False.elim (hn ⟨u, v, huv, hval⟩)
  obtain ⟨D, hD, hz, hs, hf⟩ := delete_pair_inactive G C color j hAO hzero hfun hne hj hinactive
  exact Nat.not_lt_of_ge (hmin D hD hz hf) hs

def cutKeep (C : Circuit) (j : ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).erase j

def cutProg (C : Circuit) (j : ℕ) : Prog n ℕ :=
  progOf C (fun k b => killSrc n j (opnd C k b))

def cutFun (C : Circuit) (j : ℕ) (v : ℕ → (Fin n → Bool) → Bool)
    (x : Fin n → Bool) : Bool :=
  srcAt x (fun k => v k x) (killSrc n j C.output)

lemma cutKeep_lt (C : Circuit) (j k : ℕ) (hk : k ∈ cutKeep C j) :
    k < C.gates.length :=
  Finset.mem_range.mp (Finset.mem_erase.mp hk).2

lemma cut_closed (C : Circuit) (j : ℕ) (hAO : IsAO2 n C) :
    Closed (cutProg (n := n) C j) id (cutKeep C j) := by
  intro k hk b i hi
  have hii : opnd C k b = n + i ∧ i ≠ j := killSrc_inr j (opnd C k b) i hi
  have hback := opnd_lt hAO (cutKeep_lt C j k hk) b
  have hik : i < k := by omega
  exact ⟨Finset.mem_erase.mpr ⟨hii.2,
    Finset.mem_range.mpr (lt_trans hik (cutKeep_lt C j k hk))⟩, hik⟩

lemma cut_solution_exists (C : Circuit) (j : ℕ) (hAO : IsAO2 n C) :
    ∃ v : ℕ → (Fin n → Bool) → Bool, Sol (cutProg C j) (cutKeep C j) v :=
  sol_exists (cutProg C j) id (cutKeep C j) (cut_closed C j hAO)

lemma cut_output_closed (C : Circuit) (j : ℕ) (hout : C.output < n + C.gates.length) :
    ∀ k, killSrc n j C.output = some (Sum.inr k) → k ∈ cutKeep C j := by
  intro k hk
  obtain ⟨he, hne⟩ := killSrc_inr j C.output k hk
  exact Finset.mem_erase.mpr ⟨hne, Finset.mem_range.mpr (by omega)⟩

lemma cut_le (C : Circuit) (j : ℕ) (hAO : IsAO2 n C)
    (hout : C.output < n + C.gates.length)
    (v : ℕ → (Fin n → Bool) → Bool) (hv : Sol (cutProg C j) (cutKeep C j) v)
    (x : Fin n → Bool) : cutFun C j v x = true → circuitFun n C x = true := by
  intro hx
  have hsuper := super_of_le C hAO (cutKeep C j) (fun k hk => cutKeep_lt C j k hk)
    (fun k b => killSrc n j (opnd C k b)) x
    (fun k _ b => killSrc_le C j (opnd C k b) x)
  have hvals := sol_le (cutProg C j) id (cutKeep C j) (cut_closed C j hAO) x
    (fun k => v k x) (fun k => gateVal n C k x) (hv x) hsuper
  exact killSrc_le C j C.output x
    (srcAt_le_of_le (cutKeep C j) x _ _ _ (cut_output_closed C j hout) hvals hx)

lemma cut_same (C : Circuit) (j : ℕ) (hAO : IsAO2 n C)
    (hout : C.output < n + C.gates.length)
    (v : ℕ → (Fin n → Bool) → Bool) (hv : Sol (cutProg C j) (cutKeep C j) v)
    (x : Fin n → Bool) (hz : gateVal n C j x = false) :
    cutFun C j v x = circuitFun n C x := by
  have hold : SolAt (cutProg C j) (cutKeep C j) x (fun k => gateVal n C k x) := by
    intro k hk
    change gateVal n C k x = opv (isA (gateAt C k).op)
      (srcAt x (fun i => gateVal n C i x) (killSrc n j (opnd C k 0)))
      (srcAt x (fun i => gateVal n C i x) (killSrc n j (opnd C k 1)))
    rw [killSrc_eq C j _ x hz, killSrc_eq C j _ x hz]
    exact gate_eq C hAO k (cutKeep_lt C j k hk) x
  have hvals : ∀ k ∈ cutKeep C j, v k x = gateVal n C k x := by
    intro k hk
    have h1 := sol_le (cutProg C j) id (cutKeep C j) (cut_closed C j hAO) x
      (fun k => v k x) (fun k => gateVal n C k x) (hv x)
      (fun i hi h => (hold i hi).trans h) k hk
    have h2 := le_sol (cutProg C j) id (cutKeep C j) (cut_closed C j hAO) x
      (fun k => v k x) (fun k => gateVal n C k x) (hv x)
      (fun i hi h => (hold i hi).symm.trans h) k hk
    exact Bool.eq_iff_iff.mpr ⟨h1, h2⟩
  unfold cutFun
  rw [srcAt_eq_of_eq (cutKeep C j) x _ _ _ (cut_output_closed C j hout) hvals]
  exact killSrc_eq C j C.output x hz

lemma cut_unique (C : Circuit) (j : ℕ) (hAO : IsAO2 n C)
    (hout : C.output < n + C.gates.length)
    (v w : ℕ → (Fin n → Bool) → Bool)
    (hv : Sol (cutProg C j) (cutKeep C j) v)
    (hw : Sol (cutProg C j) (cutKeep C j) w) : cutFun C j v = cutFun C j w := by
  funext x
  apply srcAt_eq_of_eq (cutKeep C j) x _ _ _ (cut_output_closed C j hout)
  intro k hk
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact sol_le (cutProg C j) id (cutKeep C j) (cut_closed C j hAO) x
      (fun k => v k x) (fun k => w k x) (hv x)
      (fun i hi h => (hw x i hi).trans h) k hk
  · exact sol_le (cutProg C j) id (cutKeep C j) (cut_closed C j hAO) x
      (fun k => w k x) (fun k => v k x) (hw x)
      (fun i hi h => (hv x i hi).trans h) k hk

lemma fold_cut (C : Circuit) (color : ℕ → Bool) (j : ℕ)
    (hAO : IsAO2 n C) (hzero : PEqualNP.TwoColour.tCount n C color = 0)
    (hj : j < C.gates.length) (hout : C.output < n + C.gates.length)
    (v : ℕ → (Fin n → Bool) → Bool) (hv : Sol (cutProg C j) (cutKeep C j) v)
    (hpos : ∃ x, cutFun C j v x = true) :
    ∃ D : Circuit, IsAO2 n D ∧ PEqualNP.TwoColour.tCount n D color = 0 ∧
      D.size < C.size ∧ circuitFun n D = cutFun C j v := by
  let P := cutProg (n := n) C j
  let K := cutKeep C j
  let R : ℕ → Finset (Fin n) := fun k => orIn n C (n + k)
  let o := killSrc n j C.output
  have hcl : Closed P id K := cut_closed C j hAO
  have ho : ∀ k, o = some (Sum.inr k) → k ∈ K := cut_output_closed C j hout
  have h1 : srcAt (fun _ => true) (fun k => v k fun _ => true) o = true := by
    obtain ⟨x, hx⟩ := hpos
    rcases ho' : o with _ | (c | k)
    · change srcAt x (fun k => v k x) o = true at hx
      rw [ho'] at hx
      exact False.elim (Bool.false_ne_true hx)
    · rfl
    · change srcAt x (fun k => v k x) o = true at hx
      rw [ho'] at hx
      exact sol_mono P id K hcl v hv x (fun _ => true) (fun _ _ => rfl) k (ho k ho') hx
  have hR : ∀ i ∈ K, P.1 i = false → srcReach R (P.2 i 0) ∪ srcReach R (P.2 i 1) ⊆ R i := by
    intro i hi hio
    have hop := isA_false_or C hAO (cutKeep_lt C j i hi) hio
    change srcReach R (killSrc n j (opnd C i 0)) ∪ srcReach R (killSrc n j (opnd C i 1)) ⊆ orIn n C (n + i)
    rw [orIn_or hAO (cutKeep_lt C j i hi) hop]
    exact Finset.union_subset_union (srcReach_kill C j _) (srcReach_kill C j _)
  have hcolor : ∀ i ∈ K, P.1 i = false → ∀ u ∈ R i, ∀ w ∈ R i, color u = color w := by
    intro i hi hio u hu w hw
    exact tCount_zero_good C color hzero i (cutKeep_lt C j i hi)
      (isA_false_or C hAO (cutKeep_lt C j i hi) hio) u hu w hw
  obtain ⟨D, hD, hDz, hDs, hDf, _⟩ := fold_prog P id v K R color hcl hv hR hcolor o ho h1
  refine ⟨D, hD, hDz, ?_, funext hDf⟩
  have hcard : (kept P v K).card ≤ K.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hKcard : K.card < C.size := by
    dsimp [K, cutKeep, Circuit.size]
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hj), Finset.card_range]
    omega
  exact lt_of_le_of_lt hDs (lt_of_le_of_lt hcard hKcard)

lemma output_lt_of_true (C : Circuit) (x : Fin n → Bool) (hx : circuitFun n C x = true) :
    C.output < n + C.gates.length := by
  by_contra h
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length :=
    (wires_length C.gates (List.ofFn x)).trans (by simp)
  change (C.wires (List.ofFn x)).getD C.output false = true at hx
  rw [List.getD_eq_default _ _ (by omega)] at hx
  cases hx

lemma least_gate_pivotal (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (color : ℕ → Bool)
    (hAO : IsAO2 n C) (hzero : PEqualNP.TwoColour.tCount n C color = 0)
    (hfun : circuitFun n C = graphFun G ∅) (hne : ∃ u w, G.Adj u w)
    (hmin : ∀ D : Circuit, IsAO2 n D → PEqualNP.TwoColour.tCount n D color = 0 →
      circuitFun n D = graphFun G ∅ → C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length)
    (v : ℕ → (Fin n → Bool) → Bool) (hv : Sol (cutProg C j) (cutKeep C j) v) :
    ∃ u w, G.Adj u w ∧ cutFun C j v (pairInput u w) = false ∧
      gateVal n C j (pairInput u w) = true := by
  classical
  have hout : C.output < n + C.gates.length := by
    obtain ⟨u, w, huw⟩ := hne
    apply output_lt_of_true C (pairInput u w)
    rw [hfun]
    exact graphFun_pair G u w huw
  suffices h : ∃ u w, G.Adj u w ∧ cutFun C j v (pairInput u w) = false by
    obtain ⟨u, w, huw, hc⟩ := h
    refine ⟨u, w, huw, hc, ?_⟩
    cases hg : gateVal n C j (pairInput u w)
    · have he := cut_same C j hAO hout v hv (pairInput u w) hg
      rw [hc, hfun, graphFun_pair G u w huw] at he
      cases he
    · rfl
  by_contra hn
  have hkeep : ∀ u w, G.Adj u w → cutFun C j v (pairInput u w) = true := by
    intro u w huw
    cases hc : cutFun C j v (pairInput u w)
    · exact False.elim (hn ⟨u, w, huw, hc⟩)
    · rfl
  have hpos : ∃ x, cutFun C j v x = true := by
    obtain ⟨u, w, huw⟩ := hne
    exact ⟨pairInput u w, hkeep u w huw⟩
  obtain ⟨D, hD, hDz, hDs, hDf⟩ := fold_cut C color j hAO hzero hj hout v hv hpos
  have heq : circuitFun n D = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      rw [hDf] at hx
      rw [← hfun]
      exact cut_le C j hAO hout v hv x hx
    · intro hx
      obtain ⟨u, w, huw, hxu, hxw⟩ := (graphFun_empty G x).mp hx
      have hp : circuitFun n D (pairInput u w) = true := by
        rw [hDf]
        exact hkeep u w huw
      apply wireVal_mono D hD (pairInput u w) x ?_ D.output hp
      intro i hi
      simp only [pairInput, decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact hxu
      · exact hxw
  exact Nat.not_lt_of_ge (hmin D hD hDz heq) hDs

lemma cut_same_of_no_reader (C : Circuit) (j : ℕ) (hAO : IsAO2 n C)
    (hout : C.output < n + C.gates.length) (hjo : n + j ≠ C.output)
    (hread : ∀ k < C.gates.length, n + j ∉ (gateAt C k).inputs)
    (v : ℕ → (Fin n → Bool) → Bool) (hv : Sol (cutProg C j) (cutKeep C j) v) :
    cutFun C j v = circuitFun n C := by
  funext x
  have hold : SolAt (cutProg C j) (cutKeep C j) x (fun k => gateVal n C k x) := by
    intro k hk
    have hopnd (b : Fin 2) : opnd C k b ≠ n + j := by
      intro he
      exact hread k (cutKeep_lt C j k hk) (he ▸ opnd_mem_inputs hAO (cutKeep_lt C j k hk) b)
    change gateVal n C k x = opv (isA (gateAt C k).op)
      (srcAt x (fun i => gateVal n C i x) (killSrc n j (opnd C k 0)))
      (srcAt x (fun i => gateVal n C i x) (killSrc n j (opnd C k 1)))
    simp only [killSrc, ite_eq_right (hopnd 0), ite_eq_right (hopnd 1), srcAt_srcOf]
    exact gate_eq C hAO k (cutKeep_lt C j k hk) x
  have hvals : ∀ k ∈ cutKeep C j, v k x = gateVal n C k x := by
    intro k hk
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact sol_le (cutProg C j) id (cutKeep C j) (cut_closed C j hAO) x
        (fun k => v k x) (fun k => gateVal n C k x) (hv x)
        (fun i hi h => (hold i hi).trans h) k hk
    · exact le_sol (cutProg C j) id (cutKeep C j) (cut_closed C j hAO) x
        (fun k => v k x) (fun k => gateVal n C k x) (hv x)
        (fun i hi h => (hold i hi).symm.trans h) k hk
  unfold cutFun
  rw [srcAt_eq_of_eq (cutKeep C j) x _ _ _ (cut_output_closed C j hout) hvals]
  simp only [killSrc, ite_eq_right (Ne.symm hjo), srcAt_srcOf]
  rfl

lemma least_no_unused (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (color : ℕ → Bool)
    (hAO : IsAO2 n C) (hzero : PEqualNP.TwoColour.tCount n C color = 0)
    (hfun : circuitFun n C = graphFun G ∅) (hne : ∃ u w, G.Adj u w)
    (hmin : ∀ D : Circuit, IsAO2 n D → PEqualNP.TwoColour.tCount n D color = 0 →
      circuitFun n D = graphFun G ∅ → C.size ≤ D.size) :
    ∀ j < C.gates.length, n + j ≠ C.output →
      ∃ r, j < r ∧ r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs := by
  classical
  intro j hj hjo
  by_contra hn
  have hread : ∀ k < C.gates.length, n + j ∉ (gateAt C k).inputs := by
    intro k hk hm
    have hback := hAO.2.1 k hk (n + j) hm
    exact hn ⟨k, by omega, hk, hm⟩
  have hout : C.output < n + C.gates.length := by
    obtain ⟨u, w, huw⟩ := hne
    apply output_lt_of_true C (pairInput u w)
    rw [hfun]
    exact graphFun_pair G u w huw
  obtain ⟨v, hv⟩ := cut_solution_exists C j hAO
  obtain ⟨u, w, huw, hc, _⟩ := least_gate_pivotal G C color hAO hzero hfun hne hmin j hj v hv
  rw [cut_same_of_no_reader C j hAO hout hjo hread v hv, hfun,
    graphFun_pair G u w huw] at hc
  cases hc

lemma graphFun_singleton_false (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Fin n) :
    graphFun G ∅ (fun i => decide (i = a)) = false := by
  cases he : graphFun G ∅ (fun i => decide (i = a))
  · rfl
  · obtain ⟨u, w, huw, hu, hw⟩ := (graphFun_empty G _).mp he
    simp only [decide_eq_true_eq] at hu hw
    subst u
    subst w
    exact False.elim (G.ne_of_adj huw rfl)

lemma graph_output_ge (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hfun : circuitFun n C = graphFun G ∅) : n ≤ C.output := by
  by_contra hn
  have ho : C.output < n := by omega
  let a : Fin n := ⟨C.output, ho⟩
  have hx : circuitFun n C (fun i => decide (i = a)) = true := by
    change wireVal n C C.output _ = true
    rw [wireVal_lt C C.output ho]
    simp [a]
  rw [hfun, graphFun_singleton_false G a] at hx
  cases hx

lemma least_output_last (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (color : ℕ → Bool)
    (hAO : IsAO2 n C) (hzero : PEqualNP.TwoColour.tCount n C color = 0)
    (hfun : circuitFun n C = graphFun G ∅) (hne : ∃ u w, G.Adj u w)
    (hmin : ∀ D : Circuit, IsAO2 n D → PEqualNP.TwoColour.tCount n D color = 0 →
      circuitFun n D = graphFun G ∅ → C.size ≤ D.size) :
    n ≤ C.output ∧ C.output + 1 = n + C.gates.length := by
  have hlo := graph_output_ge G C hfun
  have hhi : C.output < n + C.gates.length := by
    obtain ⟨u, w, huw⟩ := hne
    apply output_lt_of_true C (pairInput u w)
    rw [hfun]
    exact graphFun_pair G u w huw
  have hnz : 0 < C.gates.length := by omega
  by_cases he : n + (C.gates.length - 1) = C.output
  · exact ⟨hlo, by omega⟩
  · obtain ⟨r, hr, hr', _⟩ := least_no_unused G C color hAO hzero hfun hne hmin
      (C.gates.length - 1) (by omega) he
    omega

def maskSrc (n : ℕ) (C : Circuit) (R : Finset ℕ) (a : Fin n) (k : ℕ) (b : Fin 2) : Src n ℕ :=
  if k ∈ R ∧ opnd C k b = a.val then none else srcOf n (opnd C k b)

def maskProg (C : Circuit) (R : Finset ℕ) (a : Fin n) : Prog n ℕ :=
  progOf C (maskSrc n C R a)

lemma srcAt_input (a : Fin n) (x : Fin n → Bool) (v : ℕ → Bool) :
    srcAt x v (srcOf n a.val) = x a := by
  simp [srcOf, a.isLt, srcAt]

lemma mask_closed (C : Circuit) (R : Finset ℕ) (a : Fin n) (hAO : IsAO2 n C) :
    Closed (maskProg C R a) id (Finset.range C.gates.length) := by
  intro k hk b i hi
  have hk' := Finset.mem_range.mp hk
  change maskSrc n C R a k b = some (Sum.inr i) at hi
  by_cases hm : k ∈ R ∧ opnd C k b = a.val
  · simp [maskSrc, hm] at hi
  · have hs : srcOf n (opnd C k b) = some (Sum.inr i) := by simpa [maskSrc, hm] using hi
    have he := srcOf_inr (opnd C k b) i hs
    have hb := opnd_lt hAO hk' b
    exact ⟨Finset.mem_range.mpr (by omega), by change i < k; omega⟩

lemma mask_src_false (C : Circuit) (R : Finset ℕ) (a : Fin n) (k : ℕ) (b : Fin 2)
    (x : Fin n → Bool) (ha : x a = false) :
    srcAt x (fun i => gateVal n C i x) (maskSrc n C R a k b) = wireVal n C (opnd C k b) x := by
  unfold maskSrc
  split_ifs with hm
  · rw [hm.2, wireVal_lt C a.val a.isLt]
    exact ha.symm
  · exact srcAt_srcOf C _ x

lemma or_operand_true (f : Fin 2 → Bool) (b : Fin 2) (hb : f b = true) :
    opv false (f 0) (f 1) = true := by
  fin_cases b <;> simp_all [opv]

lemma mask_values_outside (C : Circuit) (R : Finset ℕ) (a : Fin n)
    (hAO : IsAO2 n C)
    (hmask : ∀ k < C.gates.length, k ∉ R →
      (∃ b : Fin 2, ∃ i ∈ R, opnd C k b = n + i) →
      (gateAt C k).op = GateOp.or ∧ ∃ b : Fin 2, opnd C k b = a.val)
    (v : ℕ → (Fin n → Bool) → Bool)
    (hv : Sol (maskProg C R a) (Finset.range C.gates.length) v)
    (x : Fin n → Bool) :
    ∀ k < C.gates.length, k ∉ R → v k x = gateVal n C k x := by
  have hcl := mask_closed C R a hAO
  by_cases hxa : x a = false
  · have hold : SolAt (maskProg C R a) (Finset.range C.gates.length) x (fun k => gateVal n C k x) := by
      intro k hk
      change gateVal n C k x = opv (isA (gateAt C k).op)
        (srcAt x (fun i => gateVal n C i x) (maskSrc n C R a k 0))
        (srcAt x (fun i => gateVal n C i x) (maskSrc n C R a k 1))
      rw [mask_src_false C R a k 0 x hxa, mask_src_false C R a k 1 x hxa]
      exact gate_eq C hAO k (Finset.mem_range.mp hk) x
    intro k hk _
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact sol_le _ id _ hcl x (fun k => v k x) (fun k => gateVal n C k x) (hv x)
        (fun i hi h => (hold i hi).trans h) k (Finset.mem_range.mpr hk)
    · exact le_sol _ id _ hcl x (fun k => v k x) (fun k => gateVal n C k x) (hv x)
        (fun i hi h => (hold i hi).symm.trans h) k (Finset.mem_range.mpr hk)
  · have hxa' : x a = true := by cases h : x a <;> simp_all
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk hkR
      have hnew := hv x k (Finset.mem_range.mpr hk)
      change v k x = opv (isA (gateAt C k).op)
        (srcAt x (fun i => v i x) (maskSrc n C R a k 0))
        (srcAt x (fun i => v i x) (maskSrc n C R a k 1)) at hnew
      simp only [maskSrc, hkR, false_and, ↓reduceIte] at hnew
      by_cases hcross : ∃ b : Fin 2, ∃ i ∈ R, opnd C k b = n + i
      · obtain ⟨hop, b, hb⟩ := hmask k hk hkR hcross
        have hnewone : v k x = true := by
          rw [hnew, hop]
          apply or_operand_true (fun b => srcAt x (fun i => v i x) (srcOf n (opnd C k b))) b
          rw [hb, srcAt_input, hxa']
        have holdone : gateVal n C k x = true := by
          rw [gate_eq C hAO k hk x, hop]
          apply or_operand_true (fun b => wireVal n C (opnd C k b) x) b
          rw [hb, wireVal_lt C a.val a.isLt, hxa']
        exact hnewone.trans holdone.symm
      · have hsrc (b : Fin 2) :
            srcAt x (fun i => v i x) (srcOf n (opnd C k b)) = wireVal n C (opnd C k b) x := by
          let w := opnd C k b
          have hw : w < n + k := opnd_lt hAO hk b
          by_cases hwi : w < n
          · change srcAt x (fun i => v i x) (srcOf n w) = wireVal n C w x
            simp only [srcOf, dite_eq_left hwi]
            exact (wireVal_lt C w hwi x).symm
          · have hi : w - n < k := by omega
            have hiR : w - n ∉ R := by
              intro hm
              exact hcross ⟨b, w - n, hm, by dsimp [w] at *; omega⟩
            have he := ih (w - n) hi (lt_trans hi hk) hiR
            change srcAt x (fun i => v i x) (srcOf n w) = wireVal n C w x
            unfold srcOf
            rw [dite_eq_right hwi]
            change v (w - n) x = wireVal n C w x
            rw [he]
            have hn : n + (w - n) = w := by omega
            unfold gateVal wireVal
            rw [hn]
        rw [hnew, hsrc 0, hsrc 1]
        exact (gate_eq C hAO k hk x).symm

lemma mask_region_smaller (C : Circuit) (color : ℕ → Bool) (R : Finset ℕ) (a : Fin n)
    (hAO : IsAO2 n C) (hzero : PEqualNP.TwoColour.tCount n C color = 0)
    (hpos : ∃ x : Fin n → Bool, circuitFun n C x = true)
    (houtR : ∀ i ∈ R, C.output ≠ n + i)
    (hmask : ∀ k < C.gates.length, k ∉ R →
      (∃ b : Fin 2, ∃ i ∈ R, opnd C k b = n + i) →
      (gateAt C k).op = GateOp.or ∧ ∃ b : Fin 2, opnd C k b = a.val)
    (hread : ∃ k < C.gates.length, k ∈ R ∧ ∃ b : Fin 2, opnd C k b = a.val) :
    ∃ D : Circuit, IsAO2 n D ∧ PEqualNP.TwoColour.tCount n D color = 0 ∧
      D.size < C.size ∧ circuitFun n D = circuitFun n C := by
  classical
  let P := maskProg C R a
  let K := Finset.range C.gates.length
  let Q : ℕ → Finset (Fin n) := fun k => orIn n C (n + k)
  let o := srcOf n C.output
  have hcl : Closed P id K := mask_closed C R a hAO
  have hout : C.output < n + C.gates.length := by
    obtain ⟨x, hx⟩ := hpos
    exact output_lt_of_true C x hx
  have ho : ∀ k, o = some (Sum.inr k) → k ∈ K := by
    intro k hk
    have he := srcOf_inr C.output k hk
    exact Finset.mem_range.mpr (by omega)
  obtain ⟨v, hv⟩ := sol_exists P id K hcl
  have heq (x : Fin n → Bool) : srcAt x (fun k => v k x) o = circuitFun n C x := by
    by_cases hw : C.output < n
    · unfold o srcOf
      rw [dite_eq_left hw]
      exact (wireVal_lt C C.output hw x).symm
    · have hi : C.output - n < C.gates.length := by omega
      have hiR : C.output - n ∉ R := by
        intro hm
        exact houtR _ hm (by omega)
      have hval := mask_values_outside C R a hAO hmask v hv x (C.output - n) hi hiR
      unfold o srcOf
      rw [dite_eq_right hw]
      change v (C.output - n) x = circuitFun n C x
      rw [hval]
      unfold gateVal circuitFun Circuit.eval
      congr 1
      omega
  have h1 : srcAt (fun _ => true) (fun k => v k fun _ => true) o = true := by
    obtain ⟨x, hx⟩ := hpos
    rw [heq]
    exact wireVal_mono C hAO x (fun _ => true) (fun _ _ => rfl) C.output hx
  have hR : ∀ i ∈ K, P.1 i = false → srcReach Q (P.2 i 0) ∪ srcReach Q (P.2 i 1) ⊆ Q i := by
    intro i hi hio
    have hop := isA_false_or C hAO (Finset.mem_range.mp hi) hio
    change srcReach Q (maskSrc n C R a i 0) ∪ srcReach Q (maskSrc n C R a i 1) ⊆ orIn n C (n + i)
    rw [orIn_or hAO (Finset.mem_range.mp hi) hop]
    apply Finset.union_subset_union
    all_goals
      unfold maskSrc
      split_ifs
      · exact Finset.empty_subset _
      · rw [srcReach_srcOf]
  have hcolor : ∀ i ∈ K, P.1 i = false → ∀ u ∈ Q i, ∀ w ∈ Q i, color u = color w := by
    intro i hi hio u hu w hw
    exact tCount_zero_good C color hzero i (Finset.mem_range.mp hi)
      (isA_false_or C hAO (Finset.mem_range.mp hi) hio) u hu w hw
  obtain ⟨D, hD, hDz, hDs, hDf, _⟩ := fold_prog P id v K Q color hcl hv hR hcolor o ho h1
  refine ⟨D, hD, hDz, ?_, funext fun x => (hDf x).trans (heq x)⟩
  obtain ⟨k, hk, hkR, b, hb⟩ := hread
  have hkK : k ∈ K := Finset.mem_range.mpr hk
  have hknot : k ∉ kept P v K := by
    intro hm
    have hboth := (Finset.mem_filter.mp hm).2
    have hbfalse : srcAt (fun _ => true) (fun j => v j fun _ => true) (P.2 k b) = false := by
      simp [P, maskProg, progOf, maskSrc, hkR, hb, srcAt]
    fin_cases b
    · change srcAt (fun _ => true) (fun j => v j fun _ => true) (P.2 k 0) = false at hbfalse
      exact Bool.false_ne_true (hbfalse.symm.trans hboth.1)
    · change srcAt (fun _ => true) (fun j => v j fun _ => true) (P.2 k 1) = false at hbfalse
      exact Bool.false_ne_true (hbfalse.symm.trans hboth.2)
  have hsub : kept P v K ⊂ K := Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.filter_subset _ _, by intro he; exact hknot (he.symm ▸ hkK)⟩
  have hc := Finset.card_lt_card hsub
  have hK : K.card = C.size := by simp [K, Circuit.size]
  omega

lemma least_mask_region_no_read (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (color : ℕ → Bool) (R : Finset ℕ) (a : Fin n)
    (hAO : IsAO2 n C) (hzero : PEqualNP.TwoColour.tCount n C color = 0)
    (hfun : circuitFun n C = graphFun G ∅) (hne : ∃ u w, G.Adj u w)
    (hmin : ∀ D : Circuit, IsAO2 n D → PEqualNP.TwoColour.tCount n D color = 0 →
      circuitFun n D = graphFun G ∅ → C.size ≤ D.size)
    (houtR : ∀ i ∈ R, C.output ≠ n + i)
    (hmask : ∀ k < C.gates.length, k ∉ R →
      (∃ b : Fin 2, ∃ i ∈ R, opnd C k b = n + i) →
      (gateAt C k).op = GateOp.or ∧ ∃ b : Fin 2, opnd C k b = a.val) :
    ∀ k < C.gates.length, k ∈ R → ∀ b : Fin 2, opnd C k b ≠ a.val := by
  intro k hk hkR b hb
  have hpos : ∃ x : Fin n → Bool, circuitFun n C x = true := by
    obtain ⟨u, w, huw⟩ := hne
    refine ⟨pairInput u w, ?_⟩
    rw [hfun]
    exact graphFun_pair G u w huw
  obtain ⟨D, hD, hDz, hDs, hDf⟩ := mask_region_smaller C color R a hAO hzero hpos
    houtR hmask ⟨k, hk, hkR, b, hb⟩
  have hm := hmin D hD hDz (hDf.trans hfun)
  omega

def RegionClosed (n : ℕ) (C : Circuit) (R : Finset ℕ) : Prop :=
  ∀ k < C.gates.length, k ∈ R → ∀ b : Fin 2, ∀ i : ℕ,
    opnd C k b = n + i → i ∈ R

lemma closed_region_ignores_input (C : Circuit) (R : Finset ℕ) (a : Fin n)
    (hAO : IsAO2 n C) (hclosed : RegionClosed n C R)
    (hno : ∀ k < C.gates.length, k ∈ R → ∀ b : Fin 2, opnd C k b ≠ a.val)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, i ≠ a → x i = y i) :
    ∀ k < C.gates.length, k ∈ R → gateVal n C k x = gateVal n C k y := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk hkR
    have hsrc (b : Fin 2) : wireVal n C (opnd C k b) x = wireVal n C (opnd C k b) y := by
      let w := opnd C k b
      have hw : w < n + k := opnd_lt hAO hk b
      by_cases hwi : w < n
      · change wireVal n C w x = wireVal n C w y
        rw [wireVal_lt C w hwi, wireVal_lt C w hwi]
        apply hxy ⟨w, hwi⟩
        intro he
        exact hno k hk hkR b (congrArg Fin.val he)
      · have hi : w - n < k := by omega
        have he : w = n + (w - n) := by omega
        have hiR := hclosed k hk hkR b (w - n) he
        have hval := ih (w - n) hi (lt_trans hi hk) hiR
        change wireVal n C w x = wireVal n C w y
        unfold wireVal gateVal at *
        rw [← he] at hval
        exact hval
    rw [gate_eq C hAO k hk x, gate_eq C hAO k hk y, hsrc 0, hsrc 1]

lemma least_mask_dirty_witness (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (color : ℕ → Bool) (R : Finset ℕ) (a : Fin n)
    (hAO : IsAO2 n C) (hzero : PEqualNP.TwoColour.tCount n C color = 0)
    (hfun : circuitFun n C = graphFun G ∅) (hne : ∃ u w, G.Adj u w)
    (hmin : ∀ D : Circuit, IsAO2 n D → PEqualNP.TwoColour.tCount n D color = 0 →
      circuitFun n D = graphFun G ∅ → C.size ≤ D.size)
    (houtR : ∀ i ∈ R, C.output ≠ n + i)
    (hmask : ∀ k < C.gates.length, k ∉ R →
      (∃ b : Fin 2, ∃ i ∈ R, opnd C k b = n + i) →
      (gateAt C k).op = GateOp.or ∧ ∃ b : Fin 2, opnd C k b = a.val)
    (hclosed : RegionClosed n C R) (j : ℕ) (hjR : j ∈ R)
    (hdirty : IsDirty n G C j) :
    ∃ x : Fin n → Bool, x a = false ∧ gateVal n C j x = true ∧ graphFun G ∅ x = false := by
  obtain ⟨hj, x, hxj, hxG⟩ := hdirty
  let y := Function.update x a false
  have hno := least_mask_region_no_read G C color R a hAO hzero hfun hne hmin houtR hmask
  have heq : gateVal n C j x = gateVal n C j y := by
    apply closed_region_ignores_input C R a hAO hclosed hno x y ?_ j hj hjR
    intro i hi
    simp [y, Function.update_of_ne hi]
  refine ⟨y, by simp [y], heq.symm.trans hxj, ?_⟩
  have hle : ∀ i, y i = true → x i = true := by
    intro i hi
    by_cases hia : i = a
    · subst i
      simp [y] at hi
    · simpa [y, Function.update_of_ne hia] using hi
  cases hyG : graphFun G ∅ y
  · rfl
  · have hyC : circuitFun n C y = true := by rw [hfun]; exact hyG
    have hxC := wireVal_mono C hAO y x hle C.output hyC
    change circuitFun n C x = true at hxC
    rw [hfun, hxG] at hxC
    cases hxC

end PEqualNP.Outside.L_meta_4675.SemanticFold

namespace PEqualNP.Outside.L_meta_4675.Redirect

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma foldl_append_length {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β) :
    (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

lemma foldl_append_getD_lt {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (k : ℕ) (hk : k < acc.length) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD k d = acc.getD k d := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have hk' : k < (acc ++ [f acc a]).length := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [ih (acc ++ [f acc a]) hk']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]

lemma foldl_append_getD_gate {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j : ℕ) (hj : j < l.length) (defaultA : α) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD (acc.length + j) d =
      f ((l.take j).foldl (fun w g => w ++ [f w g]) acc) (l.getD j defaultA) := by
  have hsplit : l = l.take j ++ l[j] :: l.drop (j + 1) := by
    have h1 := (List.take_append_drop j l).symm
    have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2]
    exact h1
  have hget : l.getD j defaultA = l[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  rw [hget]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pre := (l.take j).foldl (fun w g => w ++ [f w g]) acc
  have hprelen : pre.length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : acc.length + j < (pre ++ [f pre l[j]]).length := by
    rw [List.length_append, List.length_singleton, hprelen]
    omega
  rw [foldl_append_getD_lt f (l.drop (j + 1)) (pre ++ [f pre l[j]]) d (acc.length + j) hlt]
  rw [List.getD_eq_getElem?_getD, ← hprelen]
  simp

lemma foldl_append_take_getD {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j i : ℕ) (hj : j ≤ l.length) (hi : i < acc.length + j) :
    ((l.take j).foldl (fun w g => w ++ [f w g]) acc).getD i d =
      (l.foldl (fun w g => w ++ [f w g]) acc).getD i d := by
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hprelen : ((l.take j).foldl (fun w g => w ++ [f w g]) acc).length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left hj]
  rw [foldl_append_getD_lt f (l.drop j) _ d i (hprelen ▸ hi)]

lemma inputs_eq_pair {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ hmem
  unfold opnd
  rcases h : (gateAt C j).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
  · simp [h] at hlen
  · simp [h] at hlen
  · simp
  · simp [h] at hlen

lemma opnd_mem_inputs {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [inputs_eq_pair hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem_inputs hAO hj b)

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  unfold Circuit.wires
  rw [foldl_append_length, List.length_ofFn]

lemma wireVal_input {n : ℕ} (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
    wireVal n C i.val x = x i := by
  unfold wireVal Circuit.wires
  have hi : i.val < (List.ofFn x).length := by rw [List.length_ofFn]; exact i.isLt
  rw [foldl_append_getD_lt _ C.gates (List.ofFn x) false i.val hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp

lemma wireVal_ge {n : ℕ} (C : Circuit) {w : ℕ} (hw : n + C.gates.length ≤ w)
    (x : Fin n → Bool) :
    wireVal n C w x = false := by
  unfold wireVal
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [wires_length]; exact hw

lemma wireVal_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun w => wireVal n C w x) := by
  unfold wireVal Circuit.wires
  have hgate := foldl_append_getD_gate
    (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates (List.ofFn x) false j hj ⟨GateOp.or, []⟩
  rw [List.length_ofFn] at hgate
  rw [hgate]
  change (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i =>
        ((C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x)).getD i false) =
    (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i =>
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x)).getD i false)
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < (List.ofFn x).length + j := by
    rw [List.length_ofFn]
    exact hAO.2.1 j hj i hi
  exact foldl_append_take_getD _ C.gates (List.ofFn x) false j i (Nat.le_of_lt hj) hilt

lemma wireVal_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO hj, hop, inputs_eq_pair hAO hj]
  simp [GateOp.eval]

lemma wireVal_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO hj, hop, inputs_eq_pair hAO hj]
  simp [GateOp.eval]

lemma circuitFun_eq_wireVal {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = wireVal n C C.output x := rfl

lemma orSets_length (n : ℕ) (C : Circuit) :
    (orSets n C).length = C.gates.length := by
  unfold orSets orStep
  rw [foldl_append_length]
  simp

lemma orSets_getD_ge (n : ℕ) (C : Circuit) {j : ℕ} (hj : C.gates.length ≤ j) :
    (orSets n C).getD j [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [orSets_length]; exact hj

lemma orSets_getD_lt_or (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    (orSets n C).getD j [] =
      j :: ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (orSets n C).getD (w - n) []) := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change pre.length :: (if (gateAt C j).op = GateOp.or then
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
        (fun w => pre.getD (w - n) [])
      else []) = _
  rw [hprelen, ite_eq_left_of_eq_true _ _ (eq_true hop)]
  congr 1
  apply List.flatMap_congr
  intro w hw
  rw [List.mem_filter, decide_eq_true_eq] at hw
  have hlt : w - n < ([] : List (List ℕ)).length + j := by simp; omega
  exact foldl_append_take_getD _ C.gates [] [] j (w - n) (Nat.le_of_lt hj) hlt

lemma orSets_getD_lt_not_or (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op ≠ GateOp.or) :
    (orSets n C).getD j [] = [j] := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change pre.length :: (if (gateAt C j).op = GateOp.or then
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
        (fun w => pre.getD (w - n) [])
      else []) = [j]
  rw [hprelen, ite_eq_right_of_eq_false _ _ (eq_false hop)]

lemma orReaches_iff {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (w g : ℕ) :
    OrReaches n C w g ↔
      ∃ j < C.gates.length, w = n + j ∧
        (g = j ∨ ((gateAt C j).op = GateOp.or ∧ ∃ b : Fin 2, OrReaches n C (opnd C j b) g)) := by
  constructor
  · rintro ⟨hnw, hmem⟩
    have hlt : w - n < C.gates.length := by
      by_contra hge
      push Not at hge
      rw [orSets_getD_ge n C hge] at hmem
      simp at hmem
    refine ⟨w - n, hlt, by omega, ?_⟩
    by_cases hop : (gateAt C (w - n)).op = GateOp.or
    · rw [orSets_getD_lt_or n C hlt hop, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact Or.inl rfl
      · right
        rw [List.mem_flatMap] at hmem
        rcases hmem with ⟨u, hu, hgu⟩
        rw [List.mem_filter, decide_eq_true_eq] at hu
        rw [inputs_eq_pair hAO hlt] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu.1 with rfl | rfl
        · exact ⟨hop, 0, hu.2.1, hgu⟩
        · exact ⟨hop, 1, hu.2.1, hgu⟩
    · rw [orSets_getD_lt_not_or n C hlt hop, List.mem_singleton] at hmem
      exact Or.inl hmem
  · rintro ⟨j, hj, rfl, hcase⟩
    refine ⟨Nat.le_add_right n j, ?_⟩
    rw [Nat.add_sub_cancel_left]
    rcases hcase with rfl | ⟨hop, b, hnu, hgu⟩
    · by_cases hop : (gateAt C g).op = GateOp.or
      · rw [orSets_getD_lt_or n C hj hop]; exact List.mem_cons_self
      · rw [orSets_getD_lt_not_or n C hj hop]; exact List.mem_singleton_self g
    · rw [orSets_getD_lt_or n C hj hop, List.mem_cons]
      right
      rw [List.mem_flatMap]
      refine ⟨opnd C j b, ?_, hgu⟩
      rw [List.mem_filter, decide_eq_true_eq]
      exact ⟨opnd_mem_inputs hAO hj b, hnu, opnd_lt hAO hj b⟩

lemma orReaches_self {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (orReaches_iff hAO (n + j) j).mpr ⟨j, hj, rfl, Or.inl rfl⟩

lemma orReaches_le {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g : ℕ, OrReaches n C w g → n + g ≤ w ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨_, b, hb⟩⟩
    · exact ⟨le_rfl, hj⟩
    · have hlt : opnd C j b < n + j := opnd_lt hAO hj b
      have hrec := ih _ hlt g hb
      exact ⟨by omega, hrec.2⟩

lemma orReaches_trans {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g h : ℕ, OrReaches n C w g → OrReaches n C (n + g) h → OrReaches n C w h := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g h hwg hgh
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, b, hb⟩⟩
    · exact hgh
    · have hrec := ih _ (opnd_lt hAO hj b) g h hb hgh
      exact (orReaches_iff hAO (n + j) h).mpr ⟨j, hj, rfl, Or.inr ⟨hop, b, hrec⟩⟩

lemma orReaches_parent {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g : ℕ, OrReaches n C w g →
      w = n + g ∨
        ∃ h < C.gates.length, (gateAt C h).op = GateOp.or ∧ OrReaches n C w h ∧
          ∃ b : Fin 2, opnd C h b = n + g := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, b, hb⟩⟩
    · exact Or.inl rfl
    · right
      rcases ih _ (opnd_lt hAO hj b) g hb with hEq | ⟨h, hh, hhop, hreach, b', hb'⟩
      · exact ⟨j, hj, hop, orReaches_self hAO hj, b, hEq⟩
      · exact ⟨h, hh, hhop, (orReaches_iff hAO (n + j) h).mpr ⟨j, hj, rfl, Or.inr ⟨hop, b, hreach⟩⟩, b', hb'⟩

lemma wireVal_of_orReaches {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g : ℕ, OrReaches n C w g →
      ∀ x : Fin n → Bool, wireVal n C (n + g) x = true → wireVal n C w x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg x hxg
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, b, hb⟩⟩
    · exact hxg
    · have hsub := ih _ (opnd_lt hAO hj b) g hb x hxg
      rw [wireVal_or hAO hj hop, Bool.or_eq_true]
      fin_cases b
      · exact Or.inl hsub
      · exact Or.inr hsub

lemma orIn_input {n : ℕ} {C : Circuit} (i : Fin n) :
    orIn n C i.val = {i} := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro (hu | ⟨k, _, ⟨hni, _⟩, _, _⟩)
    · exact Fin.ext hu
    · omega
  · rintro rfl
    exact Or.inl rfl

lemma orIn_ge {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {w : ℕ}
    (hw : n + C.gates.length ≤ w) :
    orIn n C w = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hwk, _, _⟩)
  · omega
  · rw [orReaches_iff hAO] at hwk
    rcases hwk with ⟨j, hj, rfl, _⟩
    omega

lemma orIn_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hjk, hkop, _⟩)
  · omega
  · rw [orReaches_iff hAO] at hjk
    rcases hjk with ⟨j', _, heq, hcase⟩
    have hjj' : j' = j := by omega
    subst hjj'
    rcases hcase with rfl | ⟨hor, _⟩
    · rw [hop] at hkop; cases hkop
    · rw [hop] at hor; cases hor

lemma orIn_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) := by
  ext u
  unfold orIn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hu | ⟨k, hk, hjk, hkop, huk⟩)
    · omega
    · rw [orReaches_iff hAO] at hjk
      rcases hjk with ⟨j', _, heq, hcase⟩
      have hjj' : j' = j := by omega
      subst hjj'
      rcases hcase with rfl | ⟨_, b, hb⟩
      · rw [inputs_eq_pair hAO hj] at huk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at huk
        rcases huk with h0 | h1
        · exact Or.inl (Or.inl h0)
        · exact Or.inr (Or.inl h1)
      · fin_cases b
        · exact Or.inl (Or.inr ⟨k, hk, hb, hkop, huk⟩)
        · exact Or.inr (Or.inr ⟨k, hk, hb, hkop, huk⟩)
  · rintro ((h0 | ⟨k, hk, h0k, hkop, huk⟩) | (h1 | ⟨k, hk, h1k, hkop, huk⟩))
    · right
      refine ⟨j, hj, orReaches_self hAO hj, hop, ?_⟩
      rw [h0]
      exact opnd_mem_inputs hAO hj 0
    · right
      refine ⟨k, hk, ?_, hkop, huk⟩
      exact (orReaches_iff hAO (n + j) k).mpr ⟨j, hj, rfl, Or.inr ⟨hop, 0, h0k⟩⟩
    · right
      refine ⟨j, hj, orReaches_self hAO hj, hop, ?_⟩
      rw [h1]
      exact opnd_mem_inputs hAO hj 1
    · right
      refine ⟨k, hk, ?_, hkop, huk⟩
      exact (orReaches_iff hAO (n + j) k).mpr ⟨j, hj, rfl, Or.inr ⟨hop, 1, h1k⟩⟩

lemma orIn_subset_of_orReaches {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {w g : ℕ} (hwg : OrReaches n C w g) :
    orIn n C (n + g) ⊆ orIn n C w := by
  intro u hu
  unfold orIn at hu ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  rcases hu with hEq | ⟨k, hk, hgk, hkop, huk⟩
  · omega
  · exact Or.inr ⟨k, hk, orReaches_trans hAO w g k hwg hgk, hkop, huk⟩

lemma wireVal_true_of_mem_orIn {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {i : Fin n} {x : Fin n → Bool} (hxi : x i = true) :
    ∀ w : ℕ, i ∈ orIn n C w → wireVal n C w x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hi
    by_cases hlt : w < n
    · have heq : orIn n C w = {⟨w, hlt⟩} := orIn_input ⟨w, hlt⟩
      rw [heq, Finset.mem_singleton] at hi
      subst hi
      exact (wireVal_input C ⟨w, hlt⟩ x).trans hxi
    · by_cases hge : n + C.gates.length ≤ w
      · rw [orIn_ge hAO hge] at hi
        simp at hi
      · set j := w - n
        have hw : w = n + j := by omega
        have hj : j < C.gates.length := by omega
        have hmem : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        rw [hw] at hi ⊢
        rcases hAO.1 _ hmem with hop | hop
        · rw [orIn_and hAO hj hop] at hi
          simp at hi
        · rw [orIn_or hAO hj hop, Finset.mem_union] at hi
          rw [wireVal_or hAO hj hop, Bool.or_eq_true]
          rcases hi with h0 | h1
          · exact Or.inl (ih _ (hw ▸ opnd_lt hAO hj 0) h0)
          · exact Or.inr (ih _ (hw ▸ opnd_lt hAO hj 1) h1)

def tau (n r b w : ℕ) : ℕ := if w < n + r then w else if w = n + r then b else w - 1

def rho (r k : ℕ) : ℕ := if k < r then k else k + 1

def IsRedirect (n : ℕ) (C D : Circuit) (r b : ℕ) : Prop :=
  ∀ k, k < C.gates.length - 1 →
    gateAt D k = ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩

lemma tau_low (n r b w : ℕ) (hw : w < n + r) : tau n r b w = w := by
  simp [tau, hw]

lemma tau_rho (n r b k : ℕ) : tau n r b (n + rho r k) = n + k := by
  unfold tau rho
  split_ifs <;> omega

lemma rho_lt (r k m : ℕ) (hr : r < m) (hk : k < m - 1) : rho r k < m := by
  unfold rho
  split_ifs <;> omega

lemma rho_surj (r j m : ℕ) (hr : r < m) (hj : j < m) (hne : j ≠ r) :
    ∃ k, k < m - 1 ∧ rho r k = j := by
  by_cases hlt : j < r
  · exact ⟨j, by omega, by simp [rho, hlt]⟩
  · refine ⟨j - 1, by omega, ?_⟩
    unfold rho
    split_ifs <;> omega

lemma redirect_opnd (n : ℕ) (C D : Circuit) (r b k : ℕ)
    (hb : b < n + r) (hk : k < C.gates.length - 1)
    (hrd : IsRedirect n C D r b) (e : Fin 2) :
    opnd D k e = tau n r b (opnd C (rho r k) e) := by
  unfold opnd
  rw [hrd k hk]
  have hz : tau n r b 0 = 0 := tau_low n r b 0 (by omega)
  simpa only [hz] using List.getD_map (gateAt C (rho r k)).inputs 0 (n := e.val) (tau n r b)

lemma orIn_redirect_subset (n : ℕ) (C D : Circuit) (r b : ℕ)
    (hC : IsAO2 n C) (hD : IsAO2 n D)
    (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ D.gates.length)
    (hrd : IsRedirect n C D r b)
    (hsub : orIn n C b ⊆ orIn n C (n + r)) :
    ∀ w, w < n + C.gates.length → orIn n D (tau n r b w) ⊆ orIn n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hinput : w < n
    · rw [tau_low n r b w (by omega)]
      have h1 := orIn_input (C := C) (⟨w, hinput⟩ : Fin n)
      have h2 := orIn_input (C := D) (⟨w, hinput⟩ : Fin n)
      dsimp only at h1 h2
      rw [h1, h2]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      by_cases heq : j = r
      · subst j
        have hb' := ih b hb (by omega)
        rw [tau_low n r b b hb] at hb'
        have ht : tau n r b (n + r) = b := by simp [tau]
        rw [ht]
        exact hb'.trans hsub
      · obtain ⟨k, hk, hkj⟩ := rho_surj r j C.gates.length hr hj heq
        have hkD : k < D.gates.length := lt_of_lt_of_le hk hlen
        have ht : tau n r b (n + j) = n + k := by
          rw [← hkj]
          exact tau_rho n r b k
        have hg := hrd k hk
        rw [hkj] at hg
        have hmem : gateAt C j ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
            Option.getD_some]
          exact List.getElem_mem hj
        have hopnd : ∀ e : Fin 2, opnd D k e = tau n r b (opnd C j e) := by
          intro e
          rw [← hkj]
          exact redirect_opnd n C D r b k hb hk hrd e
        rcases hC.1 _ hmem with hop | hop
        · have hopD : (gateAt D k).op = GateOp.and := by rw [hg]; exact hop
          rw [ht, orIn_and hD hkD hopD, orIn_and hC hj hop]
        · have hopD : (gateAt D k).op = GateOp.or := by rw [hg]; exact hop
          rw [ht, orIn_or hD hkD hopD, orIn_or hC hj hop, hopnd 0, hopnd 1]
          apply Finset.union_subset_union
          · exact ih _ (opnd_lt hC hj 0) (by have := opnd_lt hC hj 0; omega)
          · exact ih _ (opnd_lt hC hj 1) (by have := opnd_lt hC hj 1; omega)

lemma below_singleton_free_orIn_empty (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (F : (Fin n → Bool) → Bool)
    (hF : ∀ i : Fin n, F (fun j => decide (j = i)) = false)
    (w : ℕ) (hw : ∀ x, wireVal n C w x = true → F x = true) :
    orIn n C w = ∅ := by
  apply Finset.ext
  intro i
  constructor
  · intro hi
    have hwi := wireVal_true_of_mem_orIn hC (i := i)
      (x := fun j => decide (j = i)) (by simp) w hi
    have hfi := hw _ hwi
    rw [hF i] at hfi
    cases hfi
  · simp

lemma tCount_redirect_zero (n : ℕ) (C D : Circuit) (r b : ℕ) (s : ℕ → Bool)
    (hC : IsAO2 n C) (hD : IsAO2 n D)
    (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ D.gates.length)
    (hrd : IsRedirect n C D r b)
    (hsub : orIn n C b ⊆ orIn n C (n + r))
    (hnew : ∀ g < D.gates.length, C.gates.length - 1 ≤ g → orIn n D (n + g) = ∅)
    (hz : PEqualNP.TwoColour.tCount n C s = 0) : PEqualNP.TwoColour.tCount n D s = 0 := by
  unfold PEqualNP.TwoColour.tCount PEqualNP.TwoColour.twoColour at *
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hz ⊢
  intro g _ hg
  rcases hg with ⟨hgD, hopD, ⟨a, ha, hsa⟩, ⟨b', hb', hsb⟩⟩
  by_cases hsmall : g < C.gates.length - 1
  · have hj := rho_lt r g C.gates.length hr hsmall
    have hgate := hrd g hsmall
    have hop : (gateAt C (rho r g)).op = GateOp.or := by
      rw [hgate] at hopD
      exact hopD
    have hs := orIn_redirect_subset n C D r b hC hD hr hb hlen hrd hsub
      (n + rho r g) (by omega)
    rw [tau_rho] at hs
    exact hz (Finset.mem_range.mpr hj)
      ⟨hj, hop, ⟨a, hs ha, hsa⟩, ⟨b', hs hb', hsb⟩⟩
  · rw [hnew g hgD (by omega)] at ha
    simp at ha

end PEqualNP.Outside.L_meta_4675.Redirect

namespace PEqualNP.Outside.L_meta_4675.Lift

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [ite_eq_left ((hC j hj).2 i hi)]

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_reader (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → ∃ r, r < C.gates.length ∧ i < r ∧ n + i ∈ (gateAt C r).inputs ∧
      (r = j ∨ InCone n C r j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    have h' := h
    rw [inCone_iff] at h'
    obtain ⟨h0, k, hk, hin, h3 | h3⟩ := h'
    · subst h3
      exact ⟨j, h0, hk, hin, Or.inl rfl⟩
    · obtain ⟨r, hr, hir, hrin, h4⟩ := ih k hk h3
      refine ⟨r, hr, hir, hrin, Or.inr ?_⟩
      rw [inCone_iff]
      refine ⟨h0, k, hk, hin, ?_⟩
      rcases h4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr h4

def tau (n r b w : ℕ) : ℕ := if w < n + r then w else if w = n + r then b else w - 1

def rho (r k : ℕ) : ℕ := if k < r then k else k + 1

def IsRedirect (n : ℕ) (C C' : Circuit) (r b : ℕ) : Prop :=
  ∀ k, k < C.gates.length - 1 →
    gateAt C' k = ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩

lemma transfer (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool) (R : Bool → Bool → Prop)
    (hRrefl : ∀ a, R a a) (hRtrans : ∀ a b c, R a b → R b c → R a c)
    (hRand : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.and.eval (l.map f)) (GateOp.and.eval (l.map f')))
    (hRor : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.or.eval (l.map f)) (GateOp.or.eval (l.map f')))
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → R (wv n C x (n + r)) (wv n C x b)) →
      R (wv n C x w) (wv n C' x (tau n r b w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hR0
    by_cases h1 : w < n
    · have ht : tau n r b w = w := by unfold tau; rw [ite_eq_left (by omega)]
      rw [ht, wv_input n C x w h1, wv_input n C' x w h1]
      exact hRrefl _
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k = r
      · subst hk
        have ht : tau n k b (n + k) = b := by unfold tau; simp
        have htb : tau n k b b = b := by unfold tau; rw [ite_eq_left hb]
        have h2 := ih b (by omega) (by omega) (fun h => absurd h (by omega))
        rw [htb] at h2
        rw [ht]
        exact hRtrans _ _ _ (hR0 le_rfl) h2
      · have hkm : k < C.gates.length := by omega
        obtain ⟨k', hk'1, hk'2, hk'3⟩ : ∃ k', tau n r b (n + k) = n + k' ∧ rho r k' = k ∧
            k' < C.gates.length - 1 := by
          by_cases hkr : k < r
          · refine ⟨k, ?_, ?_, by omega⟩
            · unfold tau; rw [ite_eq_left (by omega)]
            · unfold rho; rw [ite_eq_left hkr]
          · refine ⟨k - 1, ?_, ?_, by omega⟩
            · unfold tau; rw [ite_eq_right (by omega), ite_eq_right (by omega)]; omega
            · unfold rho; rw [ite_eq_right (by omega)]; omega
        have hg := hred k' hk'3
        rw [hk'2] at hg
        rw [hk'1, wv_rec n C x hC k hkm, wv_rec n C' x hC' k' (by omega), hg]
        simp only [List.map_map]
        have hin : ∀ w ∈ (gateAt C k).inputs,
            R (wv n C x w) ((wv n C' x ∘ tau n r b) w) := by
          intro w hw'
          have hlt := (hC k hkm).2 w hw'
          exact ih w hlt (by omega) (fun h => hR0 (by omega))
        rcases (hC k hkm).1 with hop | hop
        · rw [hop]; exact hRand _ _ _ hin
        · rw [hop]; exact hRor _ _ _ hin

lemma transfer_eq (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → wv n C x (n + r) = wv n C x b) →
      wv n C x w = wv n C' x (tau n r b w) := by
  refine transfer n C C' r b x (fun a b => a = b) (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2)
    ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h
    rw [List.map_congr_left h]
  · intro l f f' h
    rw [List.map_congr_left h]

lemma transfer_le (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length →
      (n + r ≤ w → (wv n C x (n + r) = true → wv n C x b = true)) →
      (wv n C x w = true → wv n C' x (tau n r b w) = true) := by
  refine transfer n C C' r b x (fun a b => a = true → b = true) (fun _ h => h)
    (fun _ _ _ h1 h2 h => h2 (h1 h)) ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h hall
    simp only [GateOp.eval] at hall ⊢
    rw [List.all_eq_true] at hall ⊢
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h w hw (hall (f w) (List.mem_map.mpr ⟨w, hw, rfl⟩))
  · intro l f f' h hany
    simp only [GateOp.eval] at hany ⊢
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨v, hv, hv2⟩ := hany
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨f' w, List.mem_map.mpr ⟨w, hw, rfl⟩, h w hw hv2⟩


def gfun (n : ℕ) (C : Circuit) (r b : ℕ) (top : Gate) (k : ℕ) : Gate :=
  if k < C.gates.length - 1 then
    ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ else top

def V1 (n : ℕ) (C : Circuit) (r b : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (gfun n C r b ⟨GateOp.or, []⟩), tau n r b C.output⟩

def V2 (n : ℕ) (C : Circuit) (r b i : ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (gfun n C r b ⟨GateOp.or, [tau n r b C.output, n + i]⟩),
    n + C.gates.length - 1⟩

lemma gateAt_range (m : ℕ) (g : ℕ → Gate) (out k : ℕ) (hk : k < m) :
    gateAt ⟨(List.range m).map g, out⟩ k = g k := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma V1_len (n : ℕ) (C : Circuit) (r b : ℕ) :
    (V1 n C r b).gates.length = C.gates.length - 1 := by simp [V1]

lemma V2_len (n : ℕ) (C : Circuit) (r b i : ℕ) :
    (V2 n C r b i).gates.length = C.gates.length := by simp [V2]

lemma V1_gate (n : ℕ) (C : Circuit) (r b k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V1 n C r b) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V1
  rw [gateAt_range _ _ _ _ hk]
  unfold gfun
  rw [ite_eq_left hk]

lemma V2_gate (n : ℕ) (C : Circuit) (r b i k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V2 n C r b i) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [ite_eq_left hk]

lemma V2_top (n : ℕ) (C : Circuit) (r b i : ℕ) (hm : 0 < C.gates.length) :
    gateAt (V2 n C r b i) (C.gates.length - 1) =
      ⟨GateOp.or, [tau n r b C.output, n + i]⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [ite_eq_right (by omega)]

def AO2 (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (∃ a b, (gateAt C j).inputs = [a, b]) ∧ ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma mem_gateAt (C : Circuit) (g : Gate) (hg : g ∈ C.gates) :
    ∃ j, j < C.gates.length ∧ gateAt C j = g := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  exact ⟨j, hj, by unfold gateAt; rw [List.getD_eq_getElem _ _ hj]⟩


lemma ao2_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO2 n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro j hj
  have hm := gateAt_mem C j hj
  exact ⟨h1 _ hm, List.length_eq_two.mp (h3 _ hm), h2 j hj⟩

lemma ao2_to (n : ℕ) (C : Circuit) (h : AO2 n C) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_gateAt C g hg
    exact (h j hj).1
  · intro j hj
    exact (h j hj).2.2
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_gateAt C g hg
    obtain ⟨a, b, hab⟩ := (h j hj).2.1
    rw [hab]
    rfl


lemma aob {n : ℕ} {C : Circuit} (h : AO2 n C) : AOB n C :=
  fun j hj => ⟨(h j hj).1, (h j hj).2.2⟩

lemma rho_lt (r k m : ℕ) (hr : r < m) (hk : k < m - 1) : rho r k < m := by
  unfold rho; split_ifs <;> omega

lemma tau_lt (n r b w k : ℕ) (hb : b < n + r) (hw : w < n + rho r k) :
    tau n r b w < n + k := by
  unfold tau; unfold rho at hw; split_ifs at hw ⊢ <;> omega

lemma tau_low (n r b w : ℕ) (hw : w < n + r) : tau n r b w = w := by
  unfold tau; rw [ite_eq_left hw]

lemma tau_rho (n r b k : ℕ) : tau n r b (n + rho r k) = n + k := by
  unfold tau rho; split_ifs <;> omega

lemma eval_or_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map f) = (f a || f b) := by simp [GateOp.eval]

lemma eval_and_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map f) = (f a && f b) := by simp [GateOp.eval]

lemma V1_AO2 (n : ℕ) (C : Circuit) (r b : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) : AO2 n (V1 n C r b) := by
  intro k hk
  rw [V1_len] at hk
  rw [V1_gate n C r b k hk]
  obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk)
  refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  exact tau_lt n r b w0 k hb (h3 w0 hw0)

lemma V2_AO2 (n : ℕ) (C : Circuit) (r b i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) (hi : i < r) (hout : C.output < n + C.gates.length) :
    AO2 n (V2 n C r b i) := by
  intro k hk
  rw [V2_len] at hk
  by_cases hk1 : k < C.gates.length - 1
  · rw [V2_gate n C r b i k hk1]
    obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk1)
    refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact tau_lt n r b w0 k hb (h3 w0 hw0)
  · have hk2 : k = C.gates.length - 1 := by omega
    subst hk2
    rw [V2_top n C r b i (by omega)]
    refine ⟨Or.inr rfl, ⟨_, _, rfl⟩, ?_⟩
    intro w hw
    have hw' : w = tau n r b C.output ∨ w = n + i := by simpa using hw
    rcases hw' with rfl | rfl
    · unfold tau; split_ifs <;> omega
    · omega

lemma V1_red (n : ℕ) (C : Circuit) (r b : ℕ) : IsRedirect n C (V1 n C r b) r b :=
  fun k hk => V1_gate n C r b k hk

lemma V2_red (n : ℕ) (C : Circuit) (r b i : ℕ) : IsRedirect n C (V2 n C r b i) r b :=
  fun k hk => V2_gate n C r b i k hk

lemma V1_fun (n : ℕ) (C : Circuit) (r b : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hout : C.output < n + C.gates.length)
    (h1 : wv n C x b = true → wv n C x C.output = true)
    (h2 : wv n C x b = false → wv n C x (n + r) = false) :
    wv n (V1 n C r b) x (V1 n C r b).output = wv n C x C.output := by
  have hC' := V1_AO2 n C r b hC hr hb
  have hlen : C.gates.length - 1 ≤ (V1 n C r b).gates.length := by rw [V1_len]
  show wv n (V1 n C r b) x (tau n r b C.output) = wv n C x C.output
  cases hbv : wv n C x b with
  | true =>
    rw [h1 hbv]
    exact transfer_le n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ _ => hbv) (h1 hbv)
  | false =>
    exact (transfer_eq n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ => by rw [h2 hbv, hbv])).symm

lemma V2_low (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) :
    ∀ w, w < n + r → wv n (V2 n C r b i) x w = wv n C x w := by
  intro w hw
  have h := transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w (by omega) (fun h => absurd h (by omega))
  rw [tau_low n r b w hw] at h
  exact h.symm

lemma V2_same (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x b) :
    ∀ w, w < n + C.gates.length → wv n (V2 n C r b i) x (tau n r b w) = wv n C x w := by
  intro w hw
  exact (transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w hw (fun _ => h0)).symm

lemma V2_out (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbel : wv n C x (n + i) = true → wv n C x C.output = true)
    (h0 : wv n C x (n + i) = false → wv n C x (n + r) = wv n C x b) :
    wv n (V2 n C r b i) x (V2 n C r b i).output = wv n C x C.output := by
  have hC' := V2_AO2 n C r b i hC hr hb hi hout
  have hm : 0 < C.gates.length := by omega
  have e : (V2 n C r b i).output = n + (C.gates.length - 1) := by
    show n + C.gates.length - 1 = _
    omega
  rw [e, wv_rec n _ x (aob hC') (C.gates.length - 1) (by rw [V2_len]; omega),
    V2_top n C r b i hm]
  have hi' := V2_low n C r b i x hC hr hb hi hout (n + i) (by omega)
  dsimp only
  rw [eval_or_pair, hi']
  cases hv : wv n C x (n + i) with
  | true => rw [hbel hv]; simp
  | false =>
    rw [V2_same n C r b i x hC hr hb hi hout (h0 hv) C.output hout]; simp

lemma V1_fun_top (n : ℕ) (D : Circuit) (r c i y : ℕ) (x : Fin n → Bool) (hD : AO2 n D)
    (hr : r < D.gates.length - 1) (hc : c < n + r) (hi : i < r)
    (hout : D.output = n + (D.gates.length - 1))
    (htop : gateAt D (D.gates.length - 1) = ⟨GateOp.or, [y, n + i]⟩)
    (h0 : wv n D x (n + i) = false → wv n D x (n + r) = wv n D x c) :
    wv n (V1 n D r c) x (V1 n D r c).output = wv n D x D.output := by
  have hr' : r < D.gates.length := by omega
  have hE := V1_AO2 n D r c hD hr' hc
  have hlen : D.gates.length - 1 ≤ (V1 n D r c).gates.length := by rw [V1_len]
  have hred := V1_red n D r c
  show wv n (V1 n D r c) x (tau n r c D.output) = wv n D x D.output
  cases hv : wv n D x (n + i) with
  | false =>
    exact (transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred D.output (by omega)
      (fun _ => h0 hv)).symm
  | true =>
    have e1 : wv n D x D.output = true := by
      rw [hout, wv_rec n D x (aob hD) _ (by omega), htop]
      dsimp only
      rw [eval_or_pair, hv]; simp
    have e2 : tau n r c D.output = n + (D.gates.length - 2) := by
      rw [hout]; unfold tau; rw [ite_eq_right (by omega), ite_eq_right (by omega)]; omega
    have e3 : gateAt (V1 n D r c) (D.gates.length - 2) =
        ⟨GateOp.or, [tau n r c y, n + i]⟩ := by
      rw [V1_gate n D r c _ (by omega)]
      have hrho : rho r (D.gates.length - 2) = D.gates.length - 1 := by
        unfold rho; rw [ite_eq_right (by omega)]; omega
      rw [hrho, htop]
      simp [tau_low n r c (n + i) (by omega)]
    have e4 : wv n (V1 n D r c) x (n + i) = true := by
      have h := transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred (n + i) (by omega)
        (fun h => absurd h (by omega))
      rw [tau_low n r c (n + i) (by omega)] at h
      rw [← h, hv]
    rw [e1, e2, wv_rec n _ x (aob hE) _ (by rw [V1_len]; omega), e3]
    dsimp only
    rw [eval_or_pair, e4]; simp

lemma orIn_below_empty (n : ℕ) (C : Circuit) (hC : AO2 n C)
    (hsingle : ∀ a : Fin n, wv n C (fun j => decide (j = a)) C.output = false)
    (w : ℕ) (hw : ∀ x, wv n C x w = true → wv n C x C.output = true) :
    PEqualNP.TopForm.orIn n C w = ∅ := by
  exact PEqualNP.Outside.L_meta_4675.Redirect.below_singleton_free_orIn_empty n C
    (ao2_to n C hC) (fun x => wv n C x C.output) hsingle w hw

lemma orIn_or_input_subset (n : ℕ) (C : Circuit) (hC : AO2 n C)
    (r : ℕ) (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or)
    (b : ℕ) (hb : b ∈ (gateAt C r).inputs) :
    PEqualNP.TopForm.orIn n C b ⊆ PEqualNP.TopForm.orIn n C (n + r) := by
  obtain ⟨a, c, heq⟩ := (hC r hr).2.1
  rw [heq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rw [PEqualNP.Outside.L_meta_4675.Redirect.orIn_or (ao2_to n C hC) hr hop]
  simp only [PEqualNP.TopForm.opnd, heq]
  change PEqualNP.TopForm.orIn n C b ⊆ PEqualNP.TopForm.orIn n C a ∪ PEqualNP.TopForm.orIn n C c
  rcases hb with rfl | rfl
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

lemma V1_tzero (n : ℕ) (C : Circuit) (r b : ℕ) (s : ℕ → Bool)
    (hC : AO2 n C) (hr : r < C.gates.length) (hb : b < n + r)
    (hz : PEqualNP.TwoColour.tCount n C s = 0)
    (hsub : PEqualNP.TopForm.orIn n C b ⊆ PEqualNP.TopForm.orIn n C (n + r)) :
    PEqualNP.TwoColour.tCount n (V1 n C r b) s = 0 := by
  apply PEqualNP.Outside.L_meta_4675.Redirect.tCount_redirect_zero n C (V1 n C r b) r b s
    (ao2_to n C hC) (ao2_to n _ (V1_AO2 n C r b hC hr hb)) hr hb
    (by rw [V1_len]) (V1_red n C r b) hsub
  · intro g hg hge
    rw [V1_len] at hg
    omega
  · exact hz

lemma V2_tzero (n : ℕ) (C : Circuit) (r b i : ℕ) (s : ℕ → Bool)
    (hC : AO2 n C) (hr : r < C.gates.length) (hb : b < n + r)
    (hD : AO2 n (V2 n C r b i))
    (hfun : ∀ x, wv n (V2 n C r b i) x (V2 n C r b i).output = wv n C x C.output)
    (hop : (gateAt C r).op = GateOp.or) (hbin : b ∈ (gateAt C r).inputs)
    (hz : PEqualNP.TwoColour.tCount n C s = 0)
    (hsingle : ∀ a : Fin n, wv n C (fun j => decide (j = a)) C.output = false) :
    PEqualNP.TwoColour.tCount n (V2 n C r b i) s = 0 := by
  apply PEqualNP.Outside.L_meta_4675.Redirect.tCount_redirect_zero n C (V2 n C r b i) r b s
    (ao2_to n C hC) (ao2_to n _ hD) hr hb (by rw [V2_len]; omega)
    (V2_red n C r b i) (orIn_or_input_subset n C hC r hr hop b hbin)
  · intro g hg hge
    rw [V2_len] at hg
    have hg' : g = C.gates.length - 1 := by omega
    subst g
    have hidx : n + (C.gates.length - 1) = (V2 n C r b i).output := by
      dsimp [V2]
      omega
    rw [hidx]
    exact orIn_below_empty n _ hD (fun a => (hfun _).trans (hsingle a)) _ (fun _ h => h)
  · exact hz

variable {s : ℕ → Bool}

def Least (n : ℕ) (C : Circuit) : Prop :=
  AO2 n C ∧ ∀ D : Circuit, AO2 n D → (∀ x, wv n D x D.output = wv n C x C.output) →
    PEqualNP.TwoColour.tCount n D s = 0 → C.gates.length ≤ D.gates.length

lemma reader_or (n : ℕ) (C : Circuit) (hL : Least (s := s) n C) (hzero : PEqualNP.TwoColour.tCount n C s = 0)
    (hsingle : ∀ a : Fin n, wv n C (fun j => decide (j = a)) C.output = false) (hout : C.output < n + C.gates.length)
    (i r : ℕ) (hr : r < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin : n + i ∈ (gateAt C r).inputs) :
    (gateAt C r).op = GateOp.or ∧ ∃ c, c ≠ n + i ∧ c < n + r ∧
      ((gateAt C r).inputs = [n + i, c] ∨ (gateAt C r).inputs = [c, n + i]) := by
  obtain ⟨hop, ⟨a, c0, hab⟩, hlt⟩ := hL.1 r hr
  have hir : n + i < n + r := hlt _ hin
  have hin' : n + i = a ∨ n + i = c0 := by rw [hab] at hin; simpa using hin
  by_contra hcon
  have key : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = false := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hab]
    rcases hop with hop | hop
    · rw [hop, eval_and_pair]
      rcases hin' with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
    · rw [hop, eval_or_pair]
      have ha : a = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, a, hne, hlt a (by rw [hab]; simp), ?_⟩
        rcases hin' with h | h
        · exact absurd h.symm hne
        · right; rw [hab, h]
      have hc : c0 = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, c0, hne, hlt c0 (by rw [hab]; simp), ?_⟩
        left; rw [hab, ha]
      rw [ha, hc, hx]; rfl
  have hfun : ∀ x, wv n (V1 n C r (n + i)) x (V1 n C r (n + i)).output = wv n C x C.output :=
    fun x => V1_fun n C r (n + i) x hL.1 hr hir hout (hbel x) (key x)
  have hz' := V1_tzero n C r (n + i) s hL.1 hr hir hzero (by
    rw [orIn_below_empty n C hL.1 hsingle (n + i) hbel]
    exact Finset.empty_subset _)
  have hle := hL.2 _ (V1_AO2 n C r (n + i) hL.1 hr hir) hfun hz' 
  rw [V1_len] at hle
  omega

lemma reader_unique (n : ℕ) (C : Circuit) (hL : Least (s := s) n C) (hzero : PEqualNP.TwoColour.tCount n C s = 0)
    (hsingle : ∀ a : Fin n, wv n C (fun j => decide (j = a)) C.output = false)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := reader_or n C hL hzero hsingle hout i r1 hr1 hbel hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := reader_or n C hL hzero hsingle hout i r2 hr2 hbel hin2
  have hir1 : i < r1 := by have := (hL.1 r1 hr1).2.2 _ hin1; omega
  have hir2 : i < r2 := by omega
  have k2 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r2) = wv n C x c2 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r2 hr2, hop2]
    rcases hi2 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have k1 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r1) = wv n C x c1 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r1 hr1, hop1]
    rcases hi1 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have hD : AO2 n (V2 n C r2 c2 i) := V2_AO2 n C r2 c2 i hL.1 hr2 hc2lt hir2 hout
  have hDlen := V2_len n C r2 c2 i
  have hDfun : ∀ x, wv n (V2 n C r2 c2 i) x (V2 n C r2 c2 i).output = wv n C x C.output :=
    fun x => V2_out n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (hbel x) (k2 x)
  have hDout : (V2 n C r2 c2 i).output = n + ((V2 n C r2 c2 i).gates.length - 1) := by
    rw [hDlen]
    show n + C.gates.length - 1 = n + (C.gates.length - 1)
    omega
  have hDtop : gateAt (V2 n C r2 c2 i) ((V2 n C r2 c2 i).gates.length - 1) =
      ⟨GateOp.or, [tau n r2 c2 C.output, n + i]⟩ := by
    rw [hDlen]
    exact V2_top n C r2 c2 i (by omega)
  have h0 : ∀ x, wv n (V2 n C r2 c2 i) x (n + i) = false →
      wv n (V2 n C r2 c2 i) x (n + r1) = wv n (V2 n C r2 c2 i) x c1 := by
    intro x hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + i) (by omega)] at hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + r1) (by omega),
      V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout c1 (by omega)]
    exact k1 x hx
  have hEfun : ∀ x, wv n (V1 n (V2 n C r2 c2 i) r1 c1) x (V1 n (V2 n C r2 c2 i) r1 c1).output =
      wv n C x C.output := fun x =>
    (V1_fun_top n (V2 n C r2 c2 i) r1 c1 i (tau n r2 c2 C.output) x hD (by rw [hDlen]; omega)
      hc1lt hir1 hDout hDtop (h0 x)).trans (hDfun x)
  have hc2mem : c2 ∈ (gateAt C r2).inputs := by
    rcases hi2 with e | e <;> rw [e] <;> simp
  have hDz := V2_tzero n C r2 c2 i s hL.1 hr2 hc2lt hD hDfun hop2 hc2mem hzero hsingle
  have hgate1 : gateAt (V2 n C r2 c2 i) r1 = gateAt C r1 := by
    rw [V2_gate n C r2 c2 i r1 (by omega)]
    have hrho : rho r2 r1 = r1 := by simp [rho, h12]
    rw [hrho]
    have hm : (gateAt C r1).inputs.map (tau n r2 c2) = (gateAt C r1).inputs.map id := by
      apply List.map_congr_left
      intro w hw
      exact tau_low n r2 c2 w (by have := (hL.1 r1 hr1).2.2 w hw; omega)
    rw [hm, List.map_id]
  have hc1mem : c1 ∈ (gateAt C r1).inputs := by
    rcases hi1 with e | e <;> rw [e] <;> simp
  have hEz := V1_tzero n (V2 n C r2 c2 i) r1 c1 s hD (by rw [hDlen]; omega)
    hc1lt hDz (orIn_or_input_subset n (V2 n C r2 c2 i) hD r1 (by rw [hDlen]; omega)
      (by rw [hgate1]; exact hop1) c1 (by rw [hgate1]; exact hc1mem))
  have hle := hL.2 _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun hEz
  rw [V1_len, hDlen] at hle
  omega

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

lemma V2_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hc : c < n + r) (hcin : c ∈ (gateAt C r).inputs) (a' : ℕ) :
    ∀ b', b' < C.gates.length - 1 → InCone n (V2 n C r c i) a' b' →
      InCone n C (rho r a') (rho r b') := by
  intro b'
  induction b' using Nat.strong_induction_on with
  | _ b' ih =>
    intro hb' h
    rw [inCone_iff] at h
    obtain ⟨_, k', hk', hin, h3⟩ := h
    rw [V2_gate n C r c i b' hb'] at hin
    simp only [List.mem_map] at hin
    obtain ⟨w, hw, hwk⟩ := hin
    have hbm : rho r b' < C.gates.length := rho_lt r b' _ hr hb'
    have hwlt := (hC (rho r b') hbm).2.2 w hw
    have hrb : rho r b' ≤ b' + 1 := by unfold rho; split_ifs <;> omega
    have hrb2 : b' < r → rho r b' = b' := by intro h; unfold rho; rw [ite_eq_left h]
    have hstep : InCone n C (rho r k') (rho r b') := by
      unfold tau at hwk
      by_cases h1 : w < n + r
      · rw [ite_eq_left h1] at hwk
        have e : rho r k' = k' := by unfold rho; rw [ite_eq_left (by omega)]
        rw [e, inCone_iff]
        refine ⟨hbm, k', by omega, ?_, Or.inl rfl⟩
        rw [← hwk]; exact hw
      · rw [ite_eq_right h1] at hwk
        by_cases h2 : w = n + r
        · rw [ite_eq_left h2] at hwk
          have e : rho r k' = k' := by unfold rho; rw [ite_eq_left (by omega)]
          rw [e]
          have s1 : InCone n C k' r := by
            rw [inCone_iff]
            refine ⟨hr, k', by omega, ?_, Or.inl rfl⟩
            rw [← hwk]; exact hcin
          have s2 : InCone n C r (rho r b') := by
            rw [inCone_iff]
            refine ⟨hbm, r, by omega, ?_, Or.inl rfl⟩
            rw [← h2]; exact hw
          exact inCone_trans n C k' r s1 _ s2
        · rw [ite_eq_right h2] at hwk
          have e : rho r k' = k' + 1 := by unfold rho; rw [ite_eq_right (by omega)]
          rw [e, inCone_iff]
          refine ⟨hbm, k' + 1, by omega, ?_, Or.inl rfl⟩
          have e2 : n + (k' + 1) = w := by omega
          rw [e2]; exact hw
    rcases h3 with h3 | h3
    · rw [h3]; exact hstep
    · exact inCone_trans n C _ _ (ih k' hk' (by omega) h3) _ hstep

lemma V2_no_reader (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ k', k' < C.gates.length - 1 → n + i ∉ (gateAt (V2 n C r c i) k').inputs := by
  intro k' hk' hin
  rw [V2_gate n C r c i k' hk'] at hin
  simp only [List.mem_map] at hin
  obtain ⟨w, hw, hwk⟩ := hin
  have hbm : rho r k' < C.gates.length := rho_lt r k' _ hr hk'
  have hne : rho r k' ≠ r := by unfold rho; split_ifs <;> omega
  unfold tau at hwk
  by_cases h1 : w < n + r
  · rw [ite_eq_left h1] at hwk
    rw [hwk] at hw
    exact hne (huniq _ hbm hw)
  · rw [ite_eq_right h1] at hwk
    by_cases h2 : w = n + r
    · rw [ite_eq_left h2] at hwk
      exact hci hwk
    · rw [ite_eq_right h2] at hwk
      omega

lemma V2_no_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ j', j' < C.gates.length - 1 → ¬ InCone n (V2 n C r c i) i j' := by
  intro j' hj' h
  obtain ⟨r', _, _, hrin, h4⟩ := inCone_reader n _ i j' h
  have hr'j : r' ≤ j' := by
    rcases h4 with h4 | h4
    · omega
    · have := (inCone_lt n _ r' j' h4).1
      omega
  exact V2_no_reader n C r c i hr hi hci huniq r' (by omega) hrin


lemma rho_inj (r : ℕ) : Function.Injective (rho r) := by
  intro a b h
  unfold rho at h
  split_ifs at h <;> omega

lemma rho_ne (r k : ℕ) : rho r k ≠ r := by
  unfold rho; split_ifs <;> omega

lemma rho_surj (r k m : ℕ) (hr : r < m) (hk : k < m) (hne : k ≠ r) : ∃ k', k' < m - 1 ∧ rho r k' = k := by
  by_cases h : k < r
  · exact ⟨k, by omega, by unfold rho; rw [ite_eq_left h]⟩
  · exact ⟨k - 1, by omega, by unfold rho; rw [ite_eq_right (by omega)]; omega⟩

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq, foldl_len, List.length_ofFn]

lemma out_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : wv n C x C.output = true) :
    C.output < n + C.gates.length := by
  by_contra hge
  unfold wv at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; omega)] at h
  simp at h

lemma step3_core (n : ℕ) (C : Circuit) (hL : Least (s := s) n C) (hzero : PEqualNP.TwoColour.tCount n C s = 0)
    (hsingle : ∀ a : Fin n, wv n C (fun j => decide (j = a)) C.output = false) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := reader_or n C hL hzero hsingle hout i r hr hbel hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (reader_unique n C hL hzero hsingle hout i k r h hr hbel hkin hrin).elim
    · exact h
    · exact (reader_unique n C hL hzero hsingle hout i r k h hk hbel hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma least_of_same (n : ℕ) (C D : Circuit) (hL : Least (s := s) n C) (hD : AO2 n D)
    (hfun : ∀ x, wv n D x D.output = wv n C x C.output)
    (hlen : D.gates.length = C.gates.length) : Least (s := s) n D :=
  ⟨hD, fun E hE hEf hEz => by rw [hlen]; exact hL.2 E hE (fun x => (hEf x).trans (hfun x)) hEz⟩

lemma V2_gateval (n : ℕ) (C : Circuit) (r c i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    wv n (V2 n C r c i) x (n + k') = wv n C x (n + rho r k') := by
  have h := V2_same n C r c i x hC hr hb hi hout h0 (n + rho r k')
    (by have := rho_lt r k' _ hr hk'; omega)
  rw [tau_rho] at h
  exact h

lemma V2_below (n : ℕ) (C : Circuit) (r c i : ℕ) (F : (Fin n → Bool) → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbelF : ∀ x, wv n C x (n + i) = true → F x = true)
    (h0 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    (∀ x, wv n (V2 n C r c i) x (n + k') = true → F x = true) ↔
      (∀ x, wv n C x (n + rho r k') = true → F x = true) := by
  constructor
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [← V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv


lemma card_filter_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) [DecidablePred P]
    [DecidablePred Q]
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    ((Finset.range m).filter Q).card = ((Finset.range m).filter P).card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [Finset.mem_filter, Finset.mem_range] at hk' ⊢
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

lemma card_pairs_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → ℕ → Prop)
    [DecidablePred (fun p : ℕ × ℕ => P p.1 p.2)] [DecidablePred (fun p : ℕ × ℕ => Q p.1 p.2)]
    (hQP : ∀ a' b', a' < m → b' < m → Q a' b' →
      a' < m - 1 ∧ b' < m - 1 ∧ P (rho r a') (rho r b'))
    (i j : ℕ) (hi : i < m) (hj : j < m) (hP : P i j)
    (hne : ∀ a' b', Q a' b' → ¬ (rho r a' = i ∧ rho r b' = j)) :
    ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => Q p.1 p.2)).card <
      ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => P p.1 p.2)).card := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (rho r p.1, rho r p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (rho_inj r h.1) (rho_inj r h.2)
  rw [← Finset.card_image_of_injective _ hinj]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨⟨hi, hj⟩, hP⟩
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨⟨a', b'⟩, hab, heq⟩ := hmem
      rw [Finset.mem_filter] at hab
      simp only [Prod.mk.injEq] at heq
      exact hne a' b' hab.2 heq
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨⟨a', b'⟩, hab, rfl⟩ := hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    obtain ⟨h1, h2, h3⟩ := hQP a' b' hab.1.1 hab.1.2 hab.2
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨rho_lt r a' m hr h1, rho_lt r b' m hr h2⟩, h3⟩


lemma step3_struct (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool) (hL : Least (s := s) n C) (hzero : PEqualNP.TwoColour.tCount n C s = 0)
    (hsingle : ∀ a : Fin n, wv n C (fun j => decide (j = a)) C.output = false)
    (hF : ∀ x, wv n C x C.output = F x) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → F x = true)
    (hcone : InCone n C i j) :
    ∃ (C' : Circuit) (r : ℕ), r < C.gates.length ∧ i < r ∧ Least (s := s) n C' ∧
      (∀ x, wv n C' x C'.output = F x) ∧ C'.gates.length = C.gates.length ∧
      (∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op) ∧
      (gateAt C' (C.gates.length - 1)).op = GateOp.or ∧ (gateAt C r).op = GateOp.or ∧
      (∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true))) ∧
      (∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b')) ∧
      (∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j') ∧
      PEqualNP.TwoColour.tCount n C' s = 0 := by
  have hbel' : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true :=
    fun x h => by rw [hF]; exact hbel x h
  obtain ⟨r, c, hr, hir, hclt, hci, hcin, hop, huniq, h0⟩ :=
    step3_core n C hL hzero hsingle hout i j hbel' hcone
  have hD := V2_AO2 n C r c i hL.1 hr hclt hir hout
  have hfun : ∀ x, wv n (V2 n C r c i) x (V2 n C r c i).output = wv n C x C.output :=
    fun x => V2_out n C r c i x hL.1 hr hclt hir hout (hbel' x) (h0 x)
  refine ⟨V2 n C r c i, r, hr, hir, least_of_same n C _ hL hD hfun (V2_len n C r c i),
    fun x => (hfun x).trans (hF x), V2_len n C r c i, ?_, ?_, hop, ?_, ?_, ?_,
    V2_tzero n C r c i s hL.1 hr hclt hD hfun hop hcin hzero hsingle⟩
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro k' hk'
    exact V2_below n C r c i F hL.1 hr hclt hir hout hbel h0 k' hk'
  · intro a' b' hb' h
    exact V2_cone n C r c i hL.1 hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq

lemma pairs_lt (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
      (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)]
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
      (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)] :
    ((Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)).card <
    ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card := by
  rw [hlen]
  have hjm := (inCone_lt n C i j hij)
  refine card_pairs_rho C.gates.length r hr
    (fun a b => (gateAt C a).op = GateOp.and ∧ (gateAt C b).op = GateOp.and ∧ InCone n C a b)
    (fun a b => (gateAt C' a).op = GateOp.and ∧ (gateAt C' b).op = GateOp.and ∧
      InCone n C' a b) ?_ i j (by omega) hjm.2 ⟨hi, hj, hij⟩ ?_
  · rintro a' b' _ hb' ⟨ha, hb, hab⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have ha' := (inCone_lt n C' a' b' hab).1
    have ha'' : a' < C.gates.length - 1 := by omega
    refine ⟨ha'', hb'', ?_, ?_, hcone a' b' hb'' hab⟩
    · rw [← hops a' ha'']; exact ha
    · rw [← hops b' hb'']; exact hb
  · rintro a' b' ⟨_, hb, hab⟩ ⟨h1, _⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have hb3 := (inCone_lt n C' a' b' hab).2
        have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have e : rho r i = i := by unfold rho; rw [ite_eq_left hir]
    have e2 : a' = i := rho_inj r (h1.trans e.symm)
    rw [e2] at hab
    exact hno b' hb'' hab

lemma card_mem_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < m ∧ P k) (hS' : ∀ k, k ∈ S' ↔ k < m ∧ Q k)
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    S'.card = S.card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [hS'] at hk'
    rw [hS]
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [hS] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [hS']
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

lemma junk_eq (n : ℕ) (C C' : Circuit) (F : (Fin n → Bool) → Bool) (r : ℕ)
    (hr : r < C.gates.length)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hopr : (gateAt C r).op = GateOp.or)
    (hbelow : ∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true)))
    (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → F x = true)
    (hS' : ∀ k, k ∈ S' ↔ k < C'.gates.length ∧ (gateAt C' k).op = GateOp.and ∧
      ¬ ∀ x, wv n C' x (n + k) = true → F x = true) :
    S'.card = S.card := by
  rw [hlen] at hS'
  apply card_mem_rho C.gates.length r hr _ _ S S' hS hS'
  · intro k' hk'
    rw [hops k' hk', hbelow k' hk']
  · rintro ⟨h, _⟩
    rw [hopr] at h
    exact absurd h (by simp)
  · rintro ⟨h, _⟩
    rw [htop] at h
    exact absurd h (by simp)



end PEqualNP.Outside.L_meta_4675.Lift

namespace PEqualNP.Outside.L_meta_4675.Minimum

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.TwoColour

lemma constrained_least {n : ℕ} (f : (Fin n → Bool) → Bool) (s : ℕ → Bool)
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = f)
    (ht : tCount n C s = 0) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = f ∧ tCount n D s = 0 ∧
      D.size ≤ C.size ∧
      ∀ D' : Circuit, IsAO2 n D' → circuitFun n D' = f → tCount n D' s = 0 →
        D.size ≤ D'.size := by
  classical
  let P : ℕ → Prop := fun k => ∃ D : Circuit,
    IsAO2 n D ∧ circuitFun n D = f ∧ tCount n D s = 0 ∧ D.size = k
  have hex : ∃ k, P k := ⟨C.size, C, hAO, hfun, ht, rfl⟩
  obtain ⟨D, hD, hDf, hDt, hsize⟩ := Nat.find_spec hex
  refine ⟨D, hD, hDf, hDt, ?_, ?_⟩
  · rw [hsize]
    exact Nat.find_min' hex ⟨C, hAO, hfun, ht, rfl⟩
  · intro D' hD' hDf' hDt'
    rw [hsize]
    exact Nat.find_min' hex ⟨D', hD', hDf', hDt', rfl⟩

lemma constrained_least_pairs {n : ℕ} (f : (Fin n → Bool) → Bool) (s : ℕ → Bool)
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = f)
    (ht : tCount n C s = 0) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = f ∧ tCount n D s = 0 ∧
      D.size ≤ C.size ∧
      (∀ D' : Circuit, IsAO2 n D' → circuitFun n D' = f → tCount n D' s = 0 →
        D.size ≤ D'.size) ∧
      (∀ D' : Circuit, IsAO2 n D' → circuitFun n D' = f → tCount n D' s = 0 →
        D'.size = D.size → andPairs n D ≤ andPairs n D') := by
  classical
  obtain ⟨B, hB, hBf, hBt, hBC, hmin⟩ := constrained_least f s C hAO hfun ht
  let P : ℕ → Prop := fun k => ∃ D : Circuit,
    IsAO2 n D ∧ circuitFun n D = f ∧ tCount n D s = 0 ∧
      D.size = B.size ∧ andPairs n D = k
  have hex : ∃ k, P k := ⟨andPairs n B, B, hB, hBf, hBt, rfl, rfl⟩
  obtain ⟨D, hD, hDf, hDt, hsize, hpairs⟩ := Nat.find_spec hex
  refine ⟨D, hD, hDf, hDt, ?_, ?_, ?_⟩
  · exact hsize.trans_le hBC
  · intro D' hD' hDf' hDt'
    exact hsize.trans_le (hmin D' hD' hDf' hDt')
  · intro D' hD' hDf' hDt' hsize'
    rw [hpairs]
    exact Nat.find_min' hex ⟨D', hD', hDf', hDt', hsize'.trans hsize, rfl⟩

end PEqualNP.Outside.L_meta_4675.Minimum

namespace PEqualNP.Outside.L_meta_4675.Lift

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.TwoColour

lemma exists_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) : ∃ x : Fin n → Bool, graphFun G ∅ x = true := by
  refine ⟨fun _ => true, ?_⟩
  obtain ⟨e, he⟩ := hG
  rw [SimpleGraph.mem_edgeFinset] at he
  revert he
  refine Sym2.inductionOn e ?_
  intro u v he
  have hadj : G.Adj u v := he
  unfold graphFun
  have hd : decide (∃ u v, G.Adj u v ∧ (fun _ : Fin n => true) u = true ∧
      (fun _ : Fin n => true) v = true) = true := decide_eq_true ⟨u, v, hadj, rfl, rfl⟩
  rw [hd]
  simp

lemma top_form_of_constrained_minima (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : ℕ → Bool) (hG : G.edgeFinset.Nonempty)
    (hC : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅) (hz : tCount n C s = 0)
    (hmin : ∀ D : Circuit, IsAO2 n D → circuitFun n D = graphFun G ∅ → tCount n D s = 0 →
      C.size ≤ D.size)
    (hpairs : ∀ D : Circuit, IsAO2 n D → circuitFun n D = graphFun G ∅ → tCount n D s = 0 →
      D.size = C.size → andPairs n C ≤ andPairs n D) :
    PEqualNP.TopForm.TopForm G C := by
  classical
  have hL : Least (s := s) n C := by
    refine ⟨ao2_of n C hC, ?_⟩
    intro D hD hDf hDz
    exact hmin D (ao2_to n D hD) (funext fun x => (hDf x).trans (congrFun hfun x)) hDz
  have hF : ∀ x, wv n C x C.output = graphFun G ∅ x := congrFun hfun
  have hsingle : ∀ a : Fin n, wv n C (fun j => decide (j = a)) C.output = false := by
    intro a
    rw [hF]
    simp [graphFun]
  intro i hi j hj hopi hbi hopj hcone
  obtain ⟨x, hx⟩ := exists_true n G hG
  have hout : C.output < n + C.gates.length := out_lt n C x (by rw [hF]; exact hx)
  obtain ⟨D, r, hr, hir, hLD, hFD, hlen, hops, htop, _, _, hcn, hno, hDz⟩ :=
    step3_struct n C (graphFun G ∅) hL hz hsingle hF hout i j hbi hcone
  have hlt := pairs_lt n C D r i j hr hir hlen hops htop hcn hno hopi hopj hcone
  have hcount (X : Circuit) :
      ((Finset.range X.gates.length ×ˢ Finset.range X.gates.length).filter
        (fun p : ℕ × ℕ => (gateAt X p.1).op = GateOp.and ∧
          (gateAt X p.2).op = GateOp.and ∧ InCone n X p.1 p.2)).card = andPairs n X := by
    unfold andPairs
    congr 1
    ext p
    simp only [Finset.mem_filter]
  rw [hcount D, hcount C] at hlt
  have hge := hpairs D (ao2_to n D hLD.1) (funext hFD) hDz hlen
  omega

lemma exists_top_form_zero (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : ℕ → Bool) (hG : G.edgeFinset.Nonempty)
    (hC : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅) (hz : tCount n C s = 0) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ tCount n D s = 0 ∧
      D.size ≤ C.size ∧ PEqualNP.TopForm.TopForm G D ∧
      (∀ D' : Circuit, IsAO2 n D' → circuitFun n D' = graphFun G ∅ → tCount n D' s = 0 →
        D.size ≤ D'.size) := by
  obtain ⟨D, hD, hDf, hDz, hsize, hmin, hpairs⟩ :=
    PEqualNP.Outside.L_meta_4675.Minimum.constrained_least_pairs (graphFun G ∅) s C hC hfun hz
  exact ⟨D, hD, hDf, hDz, hsize,
    top_form_of_constrained_minima n G D s hG hD hDf hDz hmin hpairs, hmin⟩

end PEqualNP.Outside.L_meta_4675.Lift

namespace PEqualNP.Outside.L_meta_4675.Lift

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.TwoColour

lemma transfer_ge (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length →
      (n + r ≤ w → (wv n C x b = true → wv n C x (n + r) = true)) →
      (wv n C' x (tau n r b w) = true → wv n C x w = true) := by
  refine transfer n C C' r b x (fun a b => b = true → a = true) (fun _ h => h)
    (fun _ _ _ h1 h2 h => h1 (h2 h)) ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h hall
    simp only [GateOp.eval] at hall ⊢
    rw [List.all_eq_true] at hall ⊢
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h w hw (hall (f' w) (List.mem_map.mpr ⟨w, hw, rfl⟩))
  · intro l f f' h hany
    simp only [GateOp.eval] at hany ⊢
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨v, hv, hv2⟩ := hany
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨f w, List.mem_map.mpr ⟨w, hw, rfl⟩, h w hw hv2⟩

lemma wv_mono (n : ℕ) (C : Circuit) (hC : AO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ a, x a = true → y a = true) :
    ∀ w, wv n C x w = true → wv n C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hin : w < n
    · simpa only [wv_input n C x w hin, wv_input n C y w hin] using hxy ⟨w, hin⟩
    by_cases hout : n + C.gates.length ≤ w
    · have hf : wv n C x w = false := Redirect.wireVal_ge C hout x
      simp [hf]
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    obtain ⟨a, b, hab⟩ := (hC j hj).2.1
    have ha := (hC j hj).2.2 a (by simp [hab])
    have hb := (hC j hj).2.2 b (by simp [hab])
    have iha := ih a ha
    have ihb := ih b hb
    rw [wv_rec n C x (aob hC) j hj, wv_rec n C y (aob hC) j hj, hab]
    rcases (hC j hj).1 with hand | hor
    · rw [hand, eval_and_pair, eval_and_pair]
      simp only [Bool.and_eq_true]
      exact fun h => ⟨iha h.1, ihb h.2⟩
    · rw [hor, eval_or_pair, eval_or_pair]
      simp only [Bool.or_eq_true]
      exact fun h => h.imp iha ihb

lemma V1_or_le (n : ℕ) (C : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AO2 n C) (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or)
    (hbin : b ∈ (gateAt C r).inputs) (hout : C.output < n + C.gates.length) :
    wv n (V1 n C r b) x (V1 n C r b).output = true → wv n C x C.output = true := by
  have hb := (hC r hr).2.2 b hbin
  apply transfer_ge n C _ r b x (aob hC) (aob (V1_AO2 n C r b hC hr hb)) hr hb
    (by rw [V1_len]) (V1_red n C r b) C.output hout
  intro _ hbv
  rw [wv_rec n C x (aob hC) r hr, hop]
  simp only [GateOp.eval, List.any_eq_true]
  exact ⟨wv n C x b, List.mem_map.mpr ⟨b, hbin, rfl⟩, hbv⟩

lemma graph_eq_of_edges (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (g : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → g x = true → g y = true)
    (hle : ∀ x, g x = true → graphFun G ∅ x = true)
    (hedges : ∀ u v, G.Adj u v → g (pairInput u v) = true) :
    ∀ x, g x = graphFun G ∅ x := by
  intro x
  cases hx : graphFun G ∅ x with
  | false =>
    cases hg : g x with
    | false => rfl
    | true => exact False.elim (Bool.false_ne_true (hx ▸ hle x hg))
  | true =>
    have hf : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
      simpa [graphFun] using hx
    obtain ⟨u, v, huv, hxu, hxv⟩ := hf
    apply hmono (pairInput u v) x _ (hedges u v huv)
    intro i hi
    rcases of_decide_eq_true hi with hi | hi
    · simpa only [hi] using hxu
    · simpa only [hi] using hxv

lemma V1_or_same_of_edges (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (r b : ℕ) (hC : AO2 n C)
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or)
    (hbin : b ∈ (gateAt C r).inputs) (hout : C.output < n + C.gates.length)
    (hfun : circuitFun n C = graphFun G ∅)
    (hedges : ∀ u v, G.Adj u v → circuitFun n (V1 n C r b) (pairInput u v) = true) :
    circuitFun n (V1 n C r b) = graphFun G ∅ := by
  have hb := (hC r hr).2.2 b hbin
  have hD := V1_AO2 n C r b hC hr hb
  apply funext
  apply graph_eq_of_edges n G
  · intro x y hxy
    exact wv_mono n _ hD x y hxy _
  · intro x hx
    exact (congrFun hfun x) ▸ (V1_or_le n C r b x hC hr hop hbin hout hx)
  · exact hedges

lemma least_or_branch_essential (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : ℕ → Bool) (hG : G.edgeFinset.Nonempty)
    (hC : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅) (hz : tCount n C s = 0)
    (hmin : ∀ D : Circuit, IsAO2 n D → circuitFun n D = graphFun G ∅ → tCount n D s = 0 →
      C.size ≤ D.size)
    (r b : ℕ) (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or)
    (hbin : b ∈ (gateAt C r).inputs) :
    ∃ u v : Fin n, G.Adj u v ∧ circuitFun n (V1 n C r b) (pairInput u v) = false := by
  classical
  have hAO := ao2_of n C hC
  have hb := (hAO r hr).2.2 b hbin
  obtain ⟨x, hx⟩ := exists_true n G hG
  have hout : C.output < n + C.gates.length := out_lt n C x (by
    change circuitFun n C x = true
    rw [hfun]
    exact hx)
  by_contra! hnone
  have hfunD := V1_or_same_of_edges n G C r b hAO hr hop hbin hout hfun
    (fun u v huv => by simpa using hnone u v huv)
  have hAO' := ao2_to n _ (V1_AO2 n C r b hAO hr hb)
  have hz' := V1_tzero n C r b s hAO hr hb hz (orIn_or_input_subset n C hAO r hr hop b hbin)
  have hle := hmin _ hAO' hfunD hz'
  change C.gates.length ≤ (V1 n C r b).gates.length at hle
  rw [V1_len] at hle
  omega

lemma least_or_branch_pair_values (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : ℕ → Bool) (hG : G.edgeFinset.Nonempty)
    (hC : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅) (hz : tCount n C s = 0)
    (hmin : ∀ D : Circuit, IsAO2 n D → circuitFun n D = graphFun G ∅ → tCount n D s = 0 →
      C.size ≤ D.size)
    (r a b : ℕ) (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or)
    (hinputs : (gateAt C r).inputs = [a, b]) :
    ∃ u v : Fin n, G.Adj u v ∧
      circuitFun n (V1 n C r b) (pairInput u v) = false ∧
      wv n C (pairInput u v) a = true ∧ wv n C (pairInput u v) b = false := by
  classical
  have hAO := ao2_of n C hC
  have hbin : b ∈ (gateAt C r).inputs := by simp [hinputs]
  have hb := (hAO r hr).2.2 b hbin
  obtain ⟨u, v, huv, hDuv⟩ := least_or_branch_essential n G C s hG hC hfun hz hmin r b hr hop hbin
  have hCuv : circuitFun n C (pairInput u v) = true := by
    rw [hfun]
    unfold graphFun
    simp only [Bool.or_eq_true]
    exact Or.inr (decide_eq_true ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩)
  have hout : C.output < n + C.gates.length := out_lt n C _ hCuv
  have hne : wv n C (pairInput u v) (n + r) ≠ wv n C (pairInput u v) b := by
    intro heq
    have he := transfer_eq n C _ r b (pairInput u v) (aob hAO)
      (aob (V1_AO2 n C r b hAO hr hb)) hr hb (by rw [V1_len]) (V1_red n C r b)
      C.output hout (fun _ => heq)
    change circuitFun n C (pairInput u v) = circuitFun n (V1 n C r b) (pairInput u v) at he
    rw [hCuv, hDuv] at he
    contradiction
  rw [wv_rec n C (pairInput u v) (aob hAO) r hr, hop, hinputs, eval_or_pair] at hne
  refine ⟨u, v, huv, hDuv, ?_⟩
  cases ha : wv n C (pairInput u v) a <;> cases hb' : wv n C (pairInput u v) b <;>
    simp_all

end PEqualNP.Outside.L_meta_4675.Lift

namespace PEqualNP.Outside.L_meta_4675.StructuralPrefix

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount

private lemma foldl_append_length {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β) :
    (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private lemma foldl_append_getD_lt {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (k : ℕ) (hk : k < acc.length) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD k d = acc.getD k d := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have hk' : k < (acc ++ [f acc a]).length := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [ih (acc ++ [f acc a]) hk']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]

private lemma foldl_append_getD_gate {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j : ℕ) (hj : j < l.length) (defaultA : α) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD (acc.length + j) d =
      f ((l.take j).foldl (fun w g => w ++ [f w g]) acc) (l.getD j defaultA) := by
  have hsplit : l = l.take j ++ l[j] :: l.drop (j + 1) := by
    have h1 := (List.take_append_drop j l).symm
    have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2]
    exact h1
  have hget : l.getD j defaultA = l[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  rw [hget]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pre := (l.take j).foldl (fun w g => w ++ [f w g]) acc
  have hprelen : pre.length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : acc.length + j < (pre ++ [f pre l[j]]).length := by
    rw [List.length_append, List.length_singleton, hprelen]
    omega
  rw [foldl_append_getD_lt f (l.drop (j + 1)) (pre ++ [f pre l[j]]) d (acc.length + j) hlt]
  rw [List.getD_eq_getElem?_getD, ← hprelen]
  simp

private lemma foldl_append_take_getD {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j i : ℕ) (hj : j ≤ l.length) (hi : i < acc.length + j) :
    ((l.take j).foldl (fun w g => w ++ [f w g]) acc).getD i d =
      (l.foldl (fun w g => w ++ [f w g]) acc).getD i d := by
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hprelen : ((l.take j).foldl (fun w g => w ++ [f w g]) acc).length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left hj]
  rw [foldl_append_getD_lt f (l.drop j) _ d i (hprelen ▸ hi)]

private lemma inputs_eq_pair {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ hmem
  unfold opnd
  rcases h : (gateAt C j).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
  · simp [h] at hlen
  · simp [h] at hlen
  · simp
  · simp [h] at hlen

private lemma opnd_mem_inputs {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [inputs_eq_pair hAO hj]
  fin_cases b <;> simp

private lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem_inputs hAO hj b)

private lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  unfold Circuit.wires
  rw [foldl_append_length, List.length_ofFn]

private lemma wireVal_input {n : ℕ} (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
    wireVal n C i.val x = x i := by
  unfold wireVal Circuit.wires
  have hi : i.val < (List.ofFn x).length := by rw [List.length_ofFn]; exact i.isLt
  rw [foldl_append_getD_lt _ C.gates (List.ofFn x) false i.val hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp

private lemma wireVal_ge {n : ℕ} (C : Circuit) {w : ℕ} (hw : n + C.gates.length ≤ w)
    (x : Fin n → Bool) :
    wireVal n C w x = false := by
  unfold wireVal
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [wires_length]; exact hw

private lemma wireVal_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun w => wireVal n C w x) := by
  unfold wireVal Circuit.wires
  have hgate := foldl_append_getD_gate
    (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates (List.ofFn x) false j hj ⟨GateOp.or, []⟩
  rw [List.length_ofFn] at hgate
  rw [hgate]
  change (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i =>
        ((C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x)).getD i false) =
    (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i =>
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x)).getD i false)
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < (List.ofFn x).length + j := by
    rw [List.length_ofFn]
    exact hAO.2.1 j hj i hi
  exact foldl_append_take_getD _ C.gates (List.ofFn x) false j i (Nat.le_of_lt hj) hilt

private lemma wireVal_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO hj, hop, inputs_eq_pair hAO hj]
  simp [GateOp.eval]

private lemma wireVal_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO hj, hop, inputs_eq_pair hAO hj]
  simp [GateOp.eval]

private lemma circuitFun_eq_wireVal {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = wireVal n C C.output x := rfl


private lemma gate_op {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
  apply hAO.1
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma wire_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ a, x a = true → y a = true) :
    ∀ w, wireVal n C w x = true → wireVal n C w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hin : w < n
    · simpa only [wireVal_input C ⟨w, hin⟩] using hxy ⟨w, hin⟩
    by_cases hout : n + C.gates.length ≤ w
    · simp [wireVal_ge C hout]
    let j := w - n
    have hj : j < C.gates.length := by dsimp [j]; omega
    have hw : w = n + j := by dsimp [j]; omega
    have h0 := opnd_lt hAO hj (0 : Fin 2)
    have h1 := opnd_lt hAO hj (1 : Fin 2)
    have i0 := ih (opnd C j 0) (by omega)
    have i1 := ih (opnd C j 1) (by omega)
    rcases gate_op hAO hj with hand | hor
    · rw [hw, wireVal_and hAO hj hand, wireVal_and hAO hj hand]
      simp only [Bool.and_eq_true]
      exact fun h => ⟨i0 h.1, i1 h.2⟩
    · rw [hw, wireVal_or hAO hj hor, wireVal_or hAO hj hor]
      simp only [Bool.or_eq_true]
      exact fun h => h.imp i0 i1

lemma prefix_support {n k : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C)
    (hclean : ∀ j < k, j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ a b : Fin n, ¬ G.Adj a b → gateVal n C j (pairInput a b) = false) :
    ∀ w < n + k, ∀ x : Fin n → Bool, wireVal n C w x = true →
      graphFun G ∅ x = true ∨ ∃ a : Fin n, x a = true ∧
        wireVal n C w (unitInput a) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwk x hx
    by_cases hin : w < n
    · right
      refine ⟨⟨w, hin⟩, ?_, ?_⟩
      · simpa only [wireVal_input C ⟨w, hin⟩] using hx
      · rw [wireVal_input C ⟨w, hin⟩]
        simp [unitInput]
    by_cases hout : n + C.gates.length ≤ w
    · rw [wireVal_ge C hout] at hx
      contradiction
    let j := w - n
    have hj : j < C.gates.length := by dsimp [j]; omega
    have hjk : j < k := by dsimp [j]; omega
    have hw : w = n + j := by dsimp [j]; omega
    have h0 := opnd_lt hAO hj (0 : Fin 2)
    have h1 := opnd_lt hAO hj (1 : Fin 2)
    have i0 := ih (opnd C j 0) (by omega) (by omega) x
    have i1 := ih (opnd C j 1) (by omega) (by omega) x
    rcases gate_op hAO hj with hand | hor
    · rw [hw, wireVal_and hAO hj hand, Bool.and_eq_true] at hx
      rcases i0 hx.1 with hf | ⟨a, hxa, ha⟩
      · exact Or.inl hf
      rcases i1 hx.2 with hf | ⟨b, hxb, hb⟩
      · exact Or.inl hf
      have ha' : wireVal n C (opnd C j 0) (pairInput a b) = true := by
        apply wire_mono hAO (unitInput a) (pairInput a b) _ _ ha
        intro v hv
        simp only [unitInput, decide_eq_true_eq] at hv
        subst v
        simp [pairInput]
      have hb' : wireVal n C (opnd C j 1) (pairInput a b) = true := by
        apply wire_mono hAO (unitInput b) (pairInput a b) _ _ hb
        intro v hv
        simp only [unitInput, decide_eq_true_eq] at hv
        subst v
        simp [pairInput]
      have hg : gateVal n C j (pairInput a b) = true := by
        change wireVal n C (n + j) (pairInput a b) = true
        rw [wireVal_and hAO hj hand, ha', hb']
        rfl
      have hab : G.Adj a b := by
        by_contra hab
        have hf := hclean j hjk hj hand a b hab
        rw [hf] at hg
        contradiction
      left
      simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨a, b, hab, hxa, hxb⟩
    · rw [hw, wireVal_or hAO hj hor, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · rcases i0 hx with hf | ⟨a, hxa, ha⟩
        · exact Or.inl hf
        · right
          refine ⟨a, hxa, ?_⟩
          rw [hw, wireVal_or hAO hj hor, ha]
          rfl
      · rcases i1 hx with hf | ⟨a, hxa, ha⟩
        · exact Or.inl hf
        · right
          refine ⟨a, hxa, ?_⟩
          rw [hw, wireVal_or hAO hj hor, ha, Bool.or_true]

lemma pair_clean_prefix_below {n k : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C)
    (hclean : ∀ j < k, j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ a b : Fin n, ¬ G.Adj a b → gateVal n C j (pairInput a b) = false) :
    ∀ j < k, j < C.gates.length → (gateAt C j).op = GateOp.and → BelowF G C j := by
  intro j hjk hj hand x hx
  have h := prefix_support G hAO hclean (n + j) (by omega) x hx
  rcases h with hf | ⟨a, _, ha⟩
  · exact hf
  · have hf := hclean j hjk hj hand a a (G.loopless.irrefl a)
    have he : pairInput a a = unitInput a := by
      funext v
      simp [pairInput, unitInput]
    rw [he] at hf
    change wireVal n C (n + j) (unitInput a) = false at hf
    rw [hf] at ha
    contradiction

end PEqualNP.Outside.L_meta_4675.StructuralPrefix


namespace PEqualNP.Outside.L_meta_4675.StructuralCone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩


end PEqualNP.Outside.L_meta_4675.StructuralCone

namespace PEqualNP.Outside.L_meta_4675.TopRectangle

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Outside.L_meta_4675.Redirect PEqualNP.Outside.L_meta_4675.StructuralCone

lemma child_in_cone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) (i : ℕ)
    (hi : opnd C j b = n + i ∨
      (n ≤ opnd C j b ∧ InCone n C i (opnd C j b - n))) :
    InCone n C i j := by
  have hb := opnd_lt hAO hj b
  rcases hi with hi | ⟨hni, hi⟩
  · apply (inCone_iff n C i j).mpr
    refine ⟨hj, i, by omega, ?_, Or.inl rfl⟩
    rw [← hi]
    exact opnd_mem_inputs hAO hj b
  · apply (inCone_iff n C i j).mpr
    refine ⟨hj, opnd C j b - n, by omega, ?_, Or.inr hi⟩
    have he : n + (opnd C j b - n) = opnd C j b := by omega
    rw [he]
    exact opnd_mem_inputs hAO hj b

lemma pure_or_wire {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w : ℕ,
      (∀ i, w = n + i ∨ (n ≤ w ∧ InCone n C i (w - n)) →
        (gateAt C i).op ≠ GateOp.and) →
      ∀ x : Fin n → Bool,
        (wireVal n C w x = true ↔ ∃ a ∈ orIn n C w, x a = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hno x
    by_cases hin : w < n
    · rw [wireVal_input C ⟨w, hin⟩ x, orIn_input (C := C) ⟨w, hin⟩]
      simp
    by_cases hout : n + C.gates.length ≤ w
    · rw [wireVal_ge C hout, orIn_ge hAO hout]
      simp
    let j := w - n
    have hj : j < C.gates.length := by dsimp [j]; omega
    have hw : w = n + j := by dsimp [j]; omega
    have hmem : gateAt C j ∈ C.gates := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have hor : (gateAt C j).op = GateOp.or :=
      (hAO.1 _ hmem).resolve_left (hno j (Or.inl hw))
    have sub (b : Fin 2) : ∀ i,
        opnd C j b = n + i ∨ (n ≤ opnd C j b ∧ InCone n C i (opnd C j b - n)) →
          (gateAt C i).op ≠ GateOp.and := by
      intro i hi
      apply hno i
      right
      refine ⟨by omega, ?_⟩
      change InCone n C i j
      exact child_in_cone hAO hj b i hi
    have h0 := opnd_lt hAO hj (0 : Fin 2)
    have h1 := opnd_lt hAO hj (1 : Fin 2)
    have i0 := ih (opnd C j 0) (by omega) (sub 0) x
    have i1 := ih (opnd C j 1) (by omega) (sub 1) x
    rw [hw, wireVal_or hAO hj hor, Bool.or_eq_true, i0, i1, orIn_or hAO hj hor]
    simp only [Finset.mem_union, or_and_right, exists_or]

lemma earliest_no_and_cone {n k : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C) (htop : TopForm G C)
    (hclean : ∀ j < k, j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ a b : Fin n, ¬ G.Adj a b → gateVal n C j (pairInput a b) = false)
    (hk : k < C.gates.length) (hand : (gateAt C k).op = GateOp.and) :
    ∀ i, InCone n C i k → (gateAt C i).op ≠ GateOp.and := by
  intro i hic hiand
  have hik := (inCone_lt n C i k hic).1
  have hi : i < C.gates.length := by omega
  have hbelow := StructuralPrefix.pair_clean_prefix_below G hAO hclean i hik hi hiand
  exact htop i hi k hk hiand hbelow hand hic

lemma earliest_operands_or {n k : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C) (htop : TopForm G C)
    (hclean : ∀ j < k, j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ a b : Fin n, ¬ G.Adj a b → gateVal n C j (pairInput a b) = false)
    (hk : k < C.gates.length) (hand : (gateAt C k).op = GateOp.and)
    (b : Fin 2) (x : Fin n → Bool) :
    wireVal n C (opnd C k b) x = true ↔
      ∃ a ∈ orIn n C (opnd C k b), x a = true := by
  apply pure_or_wire hAO
  intro i hi
  apply earliest_no_and_cone G hAO htop hclean hk hand i
  exact child_in_cone hAO hk b i hi

lemma earliest_and_rectangle {n k : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C) (htop : TopForm G C)
    (hclean : ∀ j < k, j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ a b : Fin n, ¬ G.Adj a b → gateVal n C j (pairInput a b) = false)
    (hk : k < C.gates.length) (hand : (gateAt C k).op = GateOp.and)
    (x : Fin n → Bool) :
    gateVal n C k x = true ↔
      (∃ a ∈ orIn n C (opnd C k 0), x a = true) ∧
      (∃ b ∈ orIn n C (opnd C k 1), x b = true) := by
  change wireVal n C (n + k) x = true ↔ _
  rw [wireVal_and hAO hk hand, Bool.and_eq_true,
    earliest_operands_or G hAO htop hclean hk hand 0 x,
    earliest_operands_or G hAO htop hclean hk hand 1 x]

end PEqualNP.Outside.L_meta_4675.TopRectangle

namespace PEqualNP.Outside.L_meta_4675.TopRectangle

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount
  PEqualNP.Outside.L_meta_4675.Redirect

lemma wire_orIn_one_colour {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (s : ℕ → Bool)
    (hzero : PEqualNP.TwoColour.tCount n C s = 0) (w : ℕ)
    {a b : Fin n} (ha : a ∈ orIn n C w) (hb : b ∈ orIn n C w) :
    s a = s b := by
  by_cases hin : w < n
  · rw [orIn_input (C := C) ⟨w, hin⟩] at ha hb
    simp only [Finset.mem_singleton] at ha hb
    rw [ha, hb]
  by_cases hout : n + C.gates.length ≤ w
  · rw [orIn_ge hAO hout] at ha
    exact False.elim (Finset.notMem_empty a ha)
  let j := w - n
  have hj : j < C.gates.length := by dsimp [j]; omega
  have hw : w = n + j := by dsimp [j]; omega
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  rcases hAO.1 _ hmem with hand | hor
  · rw [hw, orIn_and hAO hj hand] at ha
    exact False.elim (Finset.notMem_empty a ha)
  · have hnot : ¬ PEqualNP.TwoColour.IsTwoColour n C s j := by
      intro h
      have he : PEqualNP.TwoColour.twoColour n C s = ∅ := Finset.card_eq_zero.mp hzero
      have hm : j ∈ PEqualNP.TwoColour.twoColour n C s :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, h⟩
      rw [he] at hm
      exact Finset.notMem_empty j hm
    rw [hw] at ha hb
    cases hsa : s a <;> cases hsb : s b
    · rfl
    · exact False.elim (hnot ⟨hj, hor, ⟨a, ha, hsa⟩, ⟨b, hb, hsb⟩⟩)
    · exact False.elim (hnot ⟨hj, hor, ⟨b, hb, hsb⟩, ⟨a, ha, hsa⟩⟩)
    · rfl

lemma earliest_active_classification {n k : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C) (htop : TopForm G C)
    (hclean : ∀ j < k, j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ a b : Fin n, ¬ G.Adj a b → gateVal n C j (pairInput a b) = false)
    (hk : k < C.gates.length) (hand : (gateAt C k).op = GateOp.and)
    (s : ℕ → Bool) (hzero : PEqualNP.TwoColour.tCount n C s = 0)
    (hbip : ∀ u v : Fin n, G.Adj u v → s u ≠ s v)
    (hactive : ∃ u v : Fin n, G.Adj u v ∧ gateVal n C k (pairInput u v) = true) :
    (∃ a : Fin n, gateVal n C k (unitInput a) = true) ∨
      (∀ a ∈ orIn n C (opnd C k 0), ∀ b ∈ orIn n C (opnd C k 1), s a ≠ s b) := by
  have shared (a : Fin n) (ha : a ∈ orIn n C (opnd C k 0))
      (hb : a ∈ orIn n C (opnd C k 1)) :
      ∃ a : Fin n, gateVal n C k (unitInput a) = true := by
    refine ⟨a, (earliest_and_rectangle G hAO htop hclean hk hand (unitInput a)).mpr ?_⟩
    exact ⟨⟨a, ha, by simp [unitInput]⟩, ⟨a, hb, by simp [unitInput]⟩⟩
  have separated (a b : Fin n) (ha : a ∈ orIn n C (opnd C k 0))
      (hb : b ∈ orIn n C (opnd C k 1)) (hc : s a ≠ s b) :
      ∀ a' ∈ orIn n C (opnd C k 0), ∀ b' ∈ orIn n C (opnd C k 1), s a' ≠ s b' := by
    intro a' ha' b' hb' he
    have he1 := wire_orIn_one_colour hAO s hzero _ ha' ha
    have he2 := wire_orIn_one_colour hAO s hzero _ hb' hb
    exact hc (he1.symm.trans (he.trans he2))
  obtain ⟨u, v, huv, hact⟩ := hactive
  obtain ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩ :=
    (earliest_and_rectangle G hAO htop hclean hk hand (pairInput u v)).mp hact
  simp only [pairInput, decide_eq_true_eq] at hax hbx
  rcases hax with haeq | haeq <;> rcases hbx with hbeq | hbeq
  all_goals
    rw [haeq] at ha
    rw [hbeq] at hb
  · exact Or.inl (shared u ha hb)
  · exact Or.inr (separated u v ha hb (hbip u v huv))
  · exact Or.inr (separated v u ha hb (Ne.symm (hbip u v huv)))
  · exact Or.inl (shared v ha hb)

end PEqualNP.Outside.L_meta_4675.TopRectangle

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

namespace PEqualNP.Outside.L_meta_4675.Normalized

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.TwoColour

lemma exists_top_form_pair_active {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : ℕ → Bool) (hne : ∃ u v, G.Adj u v)
    (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅) (ht : tCount n C s = 0) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ tCount n D s = 0 ∧
      D.size ≤ C.size ∧ PEqualNP.TopForm.TopForm G D ∧
      (∀ D' : Circuit, IsAO2 n D' → circuitFun n D' = graphFun G ∅ → tCount n D' s = 0 →
        D.size ≤ D'.size) ∧
      (∀ j < D.gates.length, ∃ u v, G.Adj u v ∧ gateVal n D j (pairInput u v) = true) := by
  classical
  have hG : G.edgeFinset.Nonempty := by
    obtain ⟨u, v, huv⟩ := hne
    exact ⟨s(u, v), by simpa using huv⟩
  obtain ⟨D, hD, hDf, hDt, hsize, htop, hmin⟩ :=
    PEqualNP.Outside.L_meta_4675.Lift.exists_top_form_zero n G C s hG hAO hfun ht
  refine ⟨D, hD, hDf, hDt, hsize, htop, hmin, ?_⟩
  exact PEqualNP.Outside.L_meta_4675.SemanticFold.least_pair_active G D s hD hDt hDf hne
    (fun D' hD' hDt' hDf' => hmin D' hD' hDf' hDt')

end PEqualNP.Outside.L_meta_4675.Normalized

namespace PEqualNP.Outside.L_meta_4675.TreeCount
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4675.Lift PEqualNP.CircuitMoves PEqualNP.EdgeOwnership

def Bel (n : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  ∀ x : Fin n → Bool, wv n C x (n+j) = true → wv n C x C.output = true

def AO (n : ℕ) (C : Circuit) : Prop := ∀ j < C.gates.length,
  ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
  ∃ a b, (gateAt C j).inputs = [a,b] ∧ a < n+j ∧ b < n+j

lemma ao (n : ℕ) (C : Circuit) (hC : Lift.AO2 n C) : AO n C := by
  intro j hj
  obtain ⟨hop, ⟨a,b,hin⟩, hb⟩ := hC j hj
  exact ⟨hop,a,b,hin,hb a (by rw [hin]; simp),hb b (by rw [hin]; simp)⟩

lemma w_or (n : ℕ) (C : Circuit) (hC : Lift.AO2 n C) (x : Fin n → Bool)
    (r : ℕ) (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or)
    (a b : ℕ) (hin : (gateAt C r).inputs = [a,b]) :
    wv n C x (n+r) = (wv n C x a || wv n C x b) := by
  rw [wv_rec n C x (aob hC) r hr, hop, hin, eval_or_pair]

lemma or_children (n : ℕ) (C : Circuit) (s : ℕ → Bool) (hL : Lift.Least (s := s) n C)
    (hz : PEqualNP.TwoColour.tCount n C s = 0)
    (hS : ∀ u : Fin n, wv n C (fun j => decide (j=u)) C.output = false)
    (hout : C.output < n+C.gates.length)
    (r : ℕ) (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) (hB : Bel n C r) :
    ∃ a b, (gateAt C r).inputs = [n+a,n+b] ∧ a < r ∧ b < r ∧ a ≠ b ∧
      Bel n C a ∧ Bel n C b := by
  obtain ⟨_,a,b,hin,ha,hb⟩ := ao n C hL.1 r hr
  have hWr := fun x => w_or n C hL.1 x r hr hop a b hin
  have hvar : ∀ c, c<n → (∀ x, wv n C x c = true → wv n C x (n+r) = true) → False := by
    intro c hc hcr
    let u : Fin n := ⟨c,hc⟩
    have hv : wv n C (fun j => decide (j=u)) c = true := by rw [wv_input n C _ c hc]; simp [u]
    have ho := hB _ (hcr _ hv)
    rw [hS u] at ho
    cases ho
  have hna : n≤a := by
    by_contra h
    exact hvar a (by omega) (fun x hx => by rw [hWr x,hx]; rfl)
  have hnb : n≤b := by
    by_contra h
    exact hvar b (by omega) (fun x hx => by rw [hWr x,hx]; simp)
  obtain ⟨a',rfl⟩ := Nat.exists_eq_add_of_le hna
  obtain ⟨b',rfl⟩ := Nat.exists_eq_add_of_le hnb
  have hBa : Bel n C a' := by intro x hx; exact hB x (by rw [hWr x,hx]; rfl)
  have hBb : Bel n C b' := by intro x hx; exact hB x (by rw [hWr x,hx]; simp)
  refine ⟨a',b',hin,by omega,by omega,?_,hBa,hBb⟩
  intro hab
  subst b'
  obtain ⟨_,c,hc,_,hh⟩ := Lift.reader_or n C hL hz hS hout a' r hr hBa (by rw [hin]; simp)
  rcases hh with hh | hh
  · rw [hin] at hh
    simp only [List.cons.injEq, and_true, true_and] at hh
    exact hc hh.symm
  · rw [hin] at hh
    simp only [List.cons.injEq, and_true, true_and] at hh
    exact hc hh.symm

lemma has_top (n : ℕ) (C : Circuit) (s : ℕ → Bool) (hL : Lift.Least (s := s) n C)
    (hz : PEqualNP.TwoColour.tCount n C s = 0)
    (hS : ∀ u : Fin n, wv n C (fun j => decide (j=u)) C.output = false)
    (hOut : n ≤ C.output ∧ C.output + 1 = n + C.gates.length)
    (hRead : ∀ j, j < C.gates.length → n+j ≠ C.output →
      ∃ r, j<r ∧ r<C.gates.length ∧ n+j ∈ (gateAt C r).inputs)
    (Cone : ℕ → ℕ → Prop)
    (c1 : ∀ i k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → Cone i k)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k) :
    ∀ j, j < C.gates.length → Bel n C j →
      ∃ t, t < C.gates.length ∧ (gateAt C t).op = GateOp.and ∧ Bel n C t ∧ (t = j ∨ Cone t j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hB
    rcases (ao n C hL.1 j hj).1 with hop | hop
    · exact ⟨j, hj, hop, hB, Or.inl rfl⟩
    · obtain ⟨a, b, hin, ha, hb, hab, hBa, hBb⟩ := or_children n C s hL hz hS (by omega) j hj hop hB
      obtain ⟨t, ht, hopt, hBt, htj⟩ := ih a ha (by omega) hBa
      refine ⟨t, ht, hopt, hBt, Or.inr ?_⟩
      have hmem : n + a ∈ (gateAt C j).inputs := by rw [hin]; simp
      rcases htj with rfl | h
      · exact c1 _ j hj hmem
      · exact c2 t a j hj h hmem

lemma up (n : ℕ) (C : Circuit) (s : ℕ → Bool) (hL : Lift.Least (s := s) n C)
    (hz : PEqualNP.TwoColour.tCount n C s = 0)
    (hS : ∀ u : Fin n, wv n C (fun j => decide (j=u)) C.output = false)
    (hOut : n ≤ C.output ∧ C.output + 1 = n + C.gates.length)
    (hRead : ∀ j, j < C.gates.length → n+j ≠ C.output →
      ∃ r, j<r ∧ r<C.gates.length ∧ n+j ∈ (gateAt C r).inputs) (hout : C.output + 1 = n + C.gates.length)
    (Cone : ℕ → ℕ → Prop)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k)
    (t : ℕ) (hTop : ∀ s, s < C.gates.length → (gateAt C s).op = GateOp.and → ¬ Cone t s) :
    ∀ d s, s < C.gates.length → C.gates.length - s = d → Cone t s → Bel n C s := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro s hs hd hc
    by_cases hso : n + s = C.output
    · intro x hx
      have h1 : wv n C x C.output = true := by rw [← hso]; exact hx
      exact h1
    · obtain ⟨k, hsk, hk, hmk⟩ := hRead s hs hso
      have hck := c2 t s k hk hc hmk
      have hBk := ih (C.gates.length - k) (by omega) k hk rfl hck
      obtain ⟨hop, a, b, hin, ha, hb⟩ := ao n C hL.1 k hk
      have hopk : (gateAt C k).op = GateOp.or := by
        rcases hop with h | h
        · exact absurd hck (hTop k hk h)
        · exact h
      intro x hx
      apply hBk x
      rw [w_or n C hL.1 x k hk hopk a b hin]
      rw [hin] at hmk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmk
      rcases hmk with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp

lemma main_abs (n : ℕ) (C : Circuit) (s : ℕ → Bool) (hL : Lift.Least (s := s) n C)
    (hz : PEqualNP.TwoColour.tCount n C s = 0)
    (hS : ∀ u : Fin n, wv n C (fun j => decide (j=u)) C.output = false)
    (hOut : n ≤ C.output ∧ C.output + 1 = n + C.gates.length)
    (hRead : ∀ j, j < C.gates.length → n+j ≠ C.output →
      ∃ r, j<r ∧ r<C.gates.length ∧ n+j ∈ (gateAt C r).inputs)
    (Cone : ℕ → ℕ → Prop)
    (c1 : ∀ i k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → Cone i k)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k)
    (hTop : ∀ t s, t < C.gates.length → s < C.gates.length → (gateAt C t).op = GateOp.and →
      Bel n C t → (gateAt C s).op = GateOp.and → ¬ Cone t s) :
    (∀ j, j < C.gates.length → Bel n C j → n + j ≠ C.output →
      ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
        (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
        (gateAt C r).op = GateOp.or ∧ Bel n C r) ∧
    (n ≤ C.output ∧ C.output + 1 = n + C.gates.length) ∧
    (∀ O A : Finset ℕ,
      (∀ k, k ∈ O ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ Bel n C k) →
      (∀ k, k ∈ A ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ Bel n C k) →
      O.card + 1 = A.card) := by
  have hout := hOut
  have part1 : ∀ j, j < C.gates.length → Bel n C j → n + j ≠ C.output →
      ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
        (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
        (gateAt C r).op = GateOp.or ∧ Bel n C r := by
    intro j hj hB hne
    obtain ⟨r,hjr,hr,hmr⟩ := hRead j hj hne
    have hopr := (Lift.reader_or n C hL hz hS (by omega) j r hr hB hmr).1
    have huniq : ∀ k, k < C.gates.length → n+j ∈ (gateAt C k).inputs → k=r := by
      intro k hk hmk
      rcases lt_trichotomy k r with hkr | hkr | hkr
      · exact (Lift.reader_unique n C hL hz hS (by omega) j k r hkr hr hB hmk hmr).elim
      · exact hkr
      · exact (Lift.reader_unique n C hL hz hS (by omega) j r k hkr hk hB hmr hmk).elim
    refine ⟨r, hr, hmr, huniq, hopr, ?_⟩
    obtain ⟨t, ht, hopt, hBt, htj⟩ := has_top n C s hL hz hS hOut hRead Cone c1 c2 j hj hB
    have hc : Cone t r := by
      rcases htj with rfl | h
      · exact c1 _ r hr hmr
      · exact c2 t j r hr h hmr
    exact up n C s hL hz hS hOut hRead hout.2 Cone c2 t (fun s hs hops => hTop t s ht hs hopt hBt hops) _ r hr rfl hc
  refine ⟨part1, hout, ?_⟩
  intro O A hO hA
  classical
  have hBo : Bel n C (C.gates.length - 1) := by
    intro x hx
    have h1 : n + (C.gates.length - 1) = C.output := by omega
    rw [h1] at hx
    exact hx
  have hoB : C.gates.length - 1 ∈ O ∪ A := by
    rcases (ao n C hL.1 (C.gates.length - 1) (by omega)).1 with h | h
    · exact Finset.mem_union_right _ ((hA _).2 ⟨by omega, h, hBo⟩)
    · exact Finset.mem_union_left _ ((hO _).2 ⟨by omega, h, hBo⟩)
  have hdisj : Disjoint O A := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    have e1 := ((hO k).1 h1).2.1
    have e2 := ((hA k).1 h2).2.1
    rw [e1] at e2
    cases e2
  obtain ⟨B, hBdef⟩ : ∃ B, B = (O ∪ A).erase (C.gates.length - 1) := ⟨_, rfl⟩
  have hBmem : ∀ j, j ∈ B ↔ j < C.gates.length ∧ Bel n C j ∧ n + j ≠ C.output := by
    intro j
    rw [hBdef, Finset.mem_erase, Finset.mem_union, hO, hA]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h2.1, h2.2.2, by omega⟩
      · exact ⟨h2.1, h2.2.2, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, ?_⟩
      rcases (ao n C hL.1 j h1).1 with h | h
      · exact Or.inr ⟨h1, h, h2⟩
      · exact Or.inl ⟨h1, h, h2⟩
  have hcount := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := B) (t := O)
    (fun j k => n + j ∈ (gateAt C k).inputs)
  have hleft : ∀ j ∈ B,
      (Finset.bipartiteAbove (fun j k => n + j ∈ (gateAt C k).inputs) O j).card = 1 := by
    intro j hj
    obtain ⟨hj1, hj2, hj3⟩ := (hBmem j).1 hj
    obtain ⟨r, hr, hmr, huniq, hopr, hBr⟩ := part1 j hj1 hj2 hj3
    rw [Finset.card_eq_one]
    refine ⟨r, ?_⟩
    ext k
    simp only [Finset.bipartiteAbove, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hmk⟩
      exact huniq k ((hO k).1 hk).1 hmk
    · rintro rfl
      exact ⟨(hO _).2 ⟨hr, hopr, hBr⟩, hmr⟩
  have hright : ∀ k ∈ O,
      (Finset.bipartiteBelow (fun j k => n + j ∈ (gateAt C k).inputs) B k).card = 2 := by
    intro k hk
    obtain ⟨hk1, hk2, hk3⟩ := (hO k).1 hk
    obtain ⟨a, b, hin, ha, hb, hab, hBa, hBb⟩ := or_children n C s hL hz hS (by omega) k hk1 hk2 hk3
    rw [Finset.card_eq_two]
    refine ⟨a, b, hab, ?_⟩
    ext j
    simp only [Finset.bipartiteBelow, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      hin, List.mem_cons, List.not_mem_nil, or_false, hBmem]
    constructor
    · rintro ⟨_, h | h⟩
      · left; omega
      · right; omega
    · rintro (rfl | rfl)
      · exact ⟨⟨by omega, hBa, by omega⟩, Or.inl rfl⟩
      · exact ⟨⟨by omega, hBb, by omega⟩, Or.inr rfl⟩
  rw [Finset.sum_congr rfl hleft, Finset.sum_congr rfl hright] at hcount
  simp only [Finset.sum_const, smul_eq_mul] at hcount
  have hBc : B.card = (O ∪ A).card - 1 := by rw [hBdef]; exact Finset.card_erase_of_mem hoB
  have hU : (O ∪ A).card = O.card + A.card := Finset.card_union_of_disjoint hdisj
  have hpos : 0 < (O ∪ A).card := Finset.card_pos.mpr ⟨_, hoB⟩
  omega



lemma balance (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : ℕ → Bool) (hL : Lift.Least (s := s) n C)
    (hz : PEqualNP.TwoColour.tCount n C s = 0)
    (hS : ∀ u : Fin n, wv n C (fun j => decide (j=u)) C.output = false)
    (hOut : n ≤ C.output ∧ C.output + 1 = n + C.gates.length)
    (hRead : ∀ j, j < C.gates.length → n+j ≠ C.output →
      ∃ r, j<r ∧ r<C.gates.length ∧ n+j ∈ (gateAt C r).inputs)
    (hfun : circuitFun n C = graphFun G ∅) (hTF : PEqualNP.TopForm.TopForm G C) :
    (orT G C).card + 1 = (tops G C).card := by
  have hBel : ∀ j, BelowF G C j ↔ Bel n C j := by
    intro j
    constructor
    · intro h x hx
      exact (congrFun hfun x).trans (h x hx)
    · intro h x hx
      exact (congrFun hfun x).symm.trans (h x hx)
  have c1 : ∀ i k, k < C.gates.length → n+i ∈ (gateAt C k).inputs → InCone n C i k := by
    intro i k hk hm
    have hi := (hL.1 k hk).2.2 _ hm
    exact (Lift.inCone_iff n C i k).2 ⟨hk,i,by omega,hm,Or.inl rfl⟩
  have c2 : ∀ t i k, k < C.gates.length → InCone n C t i → n+i ∈ (gateAt C k).inputs → InCone n C t k := by
    intro t i k hk hc hm
    have hi := (hL.1 k hk).2.2 _ hm
    exact (Lift.inCone_iff n C t k).2 ⟨hk,i,by omega,hm,Or.inr hc⟩
  obtain ⟨_,_,hcount⟩ := main_abs n C s hL hz hS hOut hRead (InCone n C) c1 c2 (by
    intro t k ht hk hopt hBt hopk
    exact hTF t ht k hk hopt ((hBel t).2 hBt) hopk)
  exact hcount _ _ (fun k => by simp only [orT,gatesWhere,Finset.mem_filter,Finset.mem_range,hBel])
    (fun k => by simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range,hBel])

end PEqualNP.Outside.L_meta_4675.TreeCount

namespace PEqualNP.Outside.L_meta_4675.Residual

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

namespace S90


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact h4 a b c d hac hbd
    ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

open PEqualNP.EdgeOwnership in
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

open PEqualNP.EdgeOwnership in
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

open PEqualNP.EdgeOwnership in
lemma side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
    (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
    (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
    (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
  apply hF
  apply hbel
  rw [val_and (n := n) (by simp) ha hop, hin]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
  · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩

open PEqualNP.EdgeOwnership in
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv

open PEqualNP.EdgeOwnership

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩

open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

open PEqualNP.TopForm in
lemma top_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hC : IsAO2 n C) (a : ℕ) (ha : a ∈ tops G C) :
    Disjoint (side (n := n) C a 0) (side (n := n) C a 1) ∧
    (∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v) ∧
    ((side (n := n) C a 0).card ≤ 1 ∨ (side (n := n) C a 1).card ≤ 1) := by
  obtain ⟨hAO, hRB, h2⟩ := hC
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨halen, hop, hbel⟩ := ha
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have hp : p < n + a := hRB a halen p (by rw [hin]; simp)
  have hq : q < n + a := hRB a halen q (by rw [hin]; simp)
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  have hadj : ∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v := by
    intro u hu v hv
    simp only [side, e0] at hu
    simp only [side, e1] at hv
    exact side_adj G (graphFun G ∅) (fun u v h => (graphFun_pair G u v).mp h) a halen hop hbel
      p q hin hp hq u v (mem_orIn_reach u hu) (mem_orIn_reach v hv)
  refine ⟨?_, hadj, ?_⟩
  · rw [Finset.disjoint_left]
    intro u hu hv
    exact G.irrefl (hadj u hu u hv)
  · by_contra hcon
    simp only [not_or, not_le] at hcon
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcon.1
    have hsub : side (n := n) C a 1 ⊆ Finset.univ.filter (fun w => G.Adj x w ∧ G.Adj y w) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hadj x hx w hw, hadj y hy w hw⟩
    have h5 := Finset.card_le_card hsub
    have h6 := h4 x y hxy
    omega

end S90

lemma cover_g {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset α)
    (hf : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (Z : Finset ℕ) (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) :
    f (n + r) ⊆ stops.biUnion f ∧ ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
  have hdown : ∀ k, k ∈ R → f (n + k) ⊆ stops.biUnion f := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk u hu
      by_cases hs : k ∈ Z ∨ (g k).op ≠ GateOp.or
      · refine Finset.mem_biUnion.2 ⟨n + k, (hstops _).2 (Or.inr ⟨by omega, ?_, ?_⟩), hu⟩
        · rwa [Nat.add_sub_cancel_left]
        · rwa [Nat.add_sub_cancel_left]
      · have hkZ : k ∉ Z := fun h => hs (Or.inl h)
        have hor : (g k).op = GateOp.or := by
          by_contra h
          exact hs (Or.inr h)
        obtain ⟨w, hw, huw⟩ := (hf k hor u).1 hu
        by_cases hwn : w < n
        · exact Finset.mem_biUnion.2 ⟨w, (hstops _).2 (Or.inl ⟨hwn, k, hk, hkZ, hor, hw⟩), huw⟩
        · have hwk := hback k w hw
          have hweq : n + (w - n) = w := by omega
          have hwR : w - n ∈ R :=
            (hR _).2 (((hR k).1 hk).tail ⟨hkZ, hor, by rwa [hweq]⟩)
          exact ih (w - n) (by omega) hwR (by rwa [hweq])
  have hup : ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
    intro k hk
    have h := (hR k).1 hk
    clear hk
    induction h with
    | refl => exact Finset.Subset.refl _
    | tail _ hbc ih =>
      intro u hu
      exact ih ((hf _ hbc.2.1 u).2 ⟨_, hbc.2.2, hu⟩)
  exact ⟨hdown r ((hR r).2 Relation.ReflTransGen.refl), hup⟩

lemma cover_bound (n : ℕ) (H : SimpleGraph (Fin n)) (T : Finset ℕ) (c : ℕ → Fin n)
    (hcov : ∀ u v : Fin n, H.Adj u v → ∃ a, a ∈ T ∧ (c a = u ∨ c a = v))
    (K : Finset (Fin n)) (hK : IsMinCover H K) : K.card ≤ T.card := by
  classical
  refine (hK.2 (T.image c) ?_).trans Finset.card_image_le
  intro u v huv
  obtain ⟨a, ha, h | h⟩ := hcov u v huv
  · left
    rw [Finset.mem_coe, ← h]
    exact Finset.mem_image_of_mem _ ha
  · right
    rw [Finset.mem_coe, ← h]
    exact Finset.mem_image_of_mem _ ha

lemma four_split (N : ℕ) (isAnd isOr bel : ℕ → Prop)
    (hAO : ∀ k, k < N → (isAnd k ∧ ¬ isOr k) ∨ (isOr k ∧ ¬ isAnd k))
    (T J O Q : Finset ℕ)
    (hT : ∀ k, k ∈ T ↔ k < N ∧ isAnd k ∧ bel k)
    (hJ : ∀ k, k ∈ J ↔ k < N ∧ isAnd k ∧ ¬ bel k)
    (hO : ∀ k, k ∈ O ↔ k < N ∧ isOr k ∧ bel k)
    (hQ : ∀ k, k ∈ Q ↔ k < N ∧ isOr k ∧ ¬ bel k) :
    T.card + J.card + O.card + Q.card = N := by
  classical
  have h1 : Disjoint T J := by
    rw [Finset.disjoint_left]
    intro k h h'
    exact ((hJ k).1 h').2.2 ((hT k).1 h).2.2
  have h2 : Disjoint (T ∪ J) O := by
    rw [Finset.disjoint_left]
    intro k h h'
    have ho := (hO k).1 h'
    rcases hAO k ho.1 with ha | ha
    · exact ha.2 ho.2.1
    · rcases Finset.mem_union.1 h with h | h
      · exact ha.2 ((hT k).1 h).2.1
      · exact ha.2 ((hJ k).1 h).2.1
  have h3 : Disjoint (T ∪ J ∪ O) Q := by
    rw [Finset.disjoint_left]
    intro k h h'
    have hq := (hQ k).1 h'
    rcases Finset.mem_union.1 h with h | h
    · rcases hAO k hq.1 with ha | ha
      · exact ha.2 hq.2.1
      · rcases Finset.mem_union.1 h with h | h
        · exact ha.2 ((hT k).1 h).2.1
        · exact ha.2 ((hJ k).1 h).2.1
    · exact hq.2.2 ((hO k).1 h).2.2
  have h4 : T ∪ J ∪ O ∪ Q = Finset.range N := by
    ext k
    simp only [Finset.mem_union, Finset.mem_range, hT, hJ, hO, hQ]
    constructor
    · rintro (((h | h) | h) | h) <;> exact h.1
    · intro hk
      by_cases hb : bel k
      · rcases hAO k hk with ha | ha
        · exact Or.inl (Or.inl (Or.inl ⟨hk, ha.1, hb⟩))
        · exact Or.inl (Or.inr ⟨hk, ha.1, hb⟩)
      · rcases hAO k hk with ha | ha
        · exact Or.inl (Or.inl (Or.inr ⟨hk, ha.1, hb⟩))
        · exact Or.inr ⟨hk, ha.1, hb⟩
  have h5 := congrArg Finset.card h4
  rw [Finset.card_union_of_disjoint h3, Finset.card_union_of_disjoint h2,
    Finset.card_union_of_disjoint h1, Finset.card_range] at h5
  exact h5

def TwoNe {α : Type} (g : ℕ → Gate) (f : ℕ → Finset α) (k : ℕ) : Prop :=
  ∃ w1 ∈ (g k).inputs, ∃ w2 ∈ (g k).inputs, w1 ≠ w2 ∧ (f w1).Nonempty ∧ (f w2).Nonempty

lemma cone_count2 {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate) (f : ℕ → Finset α)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (Z : Finset ℕ)
    (hlen : ∀ k, k ∉ Z → (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)))
    (I : Finset ℕ)
    (hI : ∀ k, k ∈ R → k ∉ Z → (g k).op = GateOp.or → TwoNe g f k → k ∈ I) :
    (stops.filter (fun w => (f w).Nonempty)).card ≤ I.card + 1 := by
  classical
  set E : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or) with hE
  set N : ℕ → Finset ℕ := fun k => (g k).inputs.toFinset.filter (fun w => (f w).Nonempty)
    with hN
  set U : Finset ℕ := insert (n + r) (E.biUnion N) with hU
  set E2 := E.filter (fun k => 2 ≤ (N k).card) with hE2
  set Ene := E.filter (fun k => (f (n + k)).Nonempty) with hEne
  have hE2I : E2 ⊆ I := by
    intro k hk
    simp only [hE2, hE, Finset.mem_filter] at hk
    obtain ⟨⟨hkR, hkZ, hor⟩, h2⟩ := hk
    apply hI k hkR hkZ hor
    obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < (N k).card)
    simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw1 hw2
    exact ⟨w1, hw1.1, w2, hw2.1, hne, hw1.2, hw2.2⟩
  have hNk : ∀ k ∈ E, (N k).card ≤ (if 2 ≤ (N k).card then 1 else 0) +
      (if (f (n + k)).Nonempty then 1 else 0) := by
    intro k hk
    simp only [hE, Finset.mem_filter] at hk
    have hc : (N k).card ≤ 2 := (Finset.card_filter_le _ _).trans
      ((List.toFinset_card_le _).trans (hlen k hk.2.1 hk.2.2))
    have hne : 1 ≤ (N k).card → (f (n + k)).Nonempty := by
      intro h1
      obtain ⟨w, hw⟩ := Finset.card_pos.1 (by omega : 0 < (N k).card)
      simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw
      obtain ⟨u, hu⟩ := hw.2
      exact ⟨u, (hf2 k hk.2.2 u).2 ⟨w, hw.1, hu⟩⟩
    rcases Nat.lt_or_ge (N k).card 1 with h0 | h0
    · omega
    · rw [if_pos (hne h0)]
      split_ifs <;> omega
  have hsum : (E.biUnion N).card ≤ E2.card + Ene.card := by
    calc (E.biUnion N).card ≤ ∑ k ∈ E, (N k).card := Finset.card_biUnion_le
      _ ≤ ∑ k ∈ E, ((if 2 ≤ (N k).card then 1 else 0) +
          (if (f (n + k)).Nonempty then 1 else 0)) := Finset.sum_le_sum hNk
      _ = E2.card + Ene.card := by
        rw [Finset.sum_add_distrib, hE2, hEne, Finset.card_filter, Finset.card_filter]
  have hUcard : U.card ≤ E2.card + Ene.card + 1 := by
    have hins : U.card ≤ (E.biUnion N).card + 1 := Finset.card_insert_le (n + r) (E.biUnion N)
    omega
  have hmem : ∀ w, (f w).Nonempty → (w = n + r ∨ ∃ k' ∈ E, w ∈ (g k').inputs) → w ∈ U := by
    rintro w hw (h | ⟨k', hk', hin⟩)
    · rw [h]
      exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨k', hk', ?_⟩)
      simp only [hN, Finset.mem_filter, List.mem_toFinset]
      exact ⟨hin, hw⟩
  have hRU : ∀ k, k ∈ R → n + k = n + r ∨ ∃ k' ∈ E, n + k ∈ (g k').inputs := by
    intro k hk
    rcases Relation.ReflTransGen.cases_tail ((hR k).1 hk) with h | ⟨b, hb, hb1, hb2, hb3⟩
    · left
      rw [h]
    · right
      refine ⟨b, ?_, hb3⟩
      rw [hE, Finset.mem_filter]
      exact ⟨(hR b).2 hb, hb1, hb2⟩
  set S2 : Finset ℕ := Ene.image (fun k => n + k) with hS2
  have hS2card : S2.card = Ene.card :=
    Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)
  have hdisj : Disjoint (stops.filter (fun w => (f w).Nonempty)) S2 := by
    rw [Finset.disjoint_left]
    intro w hw hw2
    rw [Finset.mem_filter] at hw
    rw [hS2, Finset.mem_image] at hw2
    obtain ⟨k, hk, rfl⟩ := hw2
    rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
    rcases (hstops _).1 hw.1 with ⟨h1, _⟩ | ⟨_, _, h3⟩
    · omega
    · rw [Nat.add_sub_cancel_left] at h3
      rcases h3 with h3 | h3
      · exact hk.1.2.1 h3
      · exact h3 hk.1.2.2
  have hsub : (stops.filter (fun w => (f w).Nonempty)) ∪ S2 ⊆ U := by
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · rw [Finset.mem_filter] at hw
      rcases (hstops _).1 hw.1 with ⟨_, k, hk, hk1, hk2, hk3⟩ | ⟨h1, h2, _⟩
      · refine hmem w hw.2 (Or.inr ⟨k, ?_, hk3⟩)
        rw [hE, Finset.mem_filter]
        exact ⟨hk, hk1, hk2⟩
      · have := hRU _ h2
        rw [Nat.add_sub_cancel' h1] at this
        exact hmem w hw.2 this
    · rw [hS2, Finset.mem_image] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
      exact hmem _ hk.2 (hRU k hk.1.1)
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hS2card] at h3
  have h4 := Finset.card_le_card hE2I
  omega

lemma top_step2 (n : ℕ) (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (Z : Finset ℕ) (ρ : ℕ) (c : Fin n) (E0 : Finset (Sym2 (Fin n)))
    (hZ : ∀ k, k ∈ Z → f (n + k) ⊆ f ρ →
      (∀ v, v ∈ f (n + k) → s(c, v) ∈ E0) ∨ (f (n + k)).card ≤ 1) :
    ∃ Znew : Finset ℕ, Disjoint Z Znew ∧
      (∀ k, k ∈ Znew → (g k).op = GateOp.or ∧ TwoNe g f k ∧ n ≤ ρ ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (ρ - n) k ∧ f (n + k) ⊆ f ρ) ∧
      (((f ρ).image (fun v => s(c, v))) \ E0).card ≤ Znew.card + 1 := by
  classical
  by_cases hρ : ρ < n
  · refine ⟨∅, Finset.disjoint_empty_right _, by simp, ?_⟩
    calc (((f ρ).image (fun v => s(c, v))) \ E0).card
        ≤ ((f ρ).image (fun v => s(c, v))).card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ (f ρ).card := Finset.card_image_le
      _ ≤ 1 := hf1 ρ hρ
      _ ≤ (∅ : Finset ℕ).card + 1 := by simp
  · have hρn : n ≤ ρ := Nat.le_of_not_lt hρ
    obtain ⟨r, rfl⟩ : ∃ r, ρ = n + r := ⟨ρ - n, by omega⟩
    have hle : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k → k ≤ r := by
      intro k h
      induction h with
      | refl => exact le_refl _
      | tail _ hbc ih =>
        have := hback _ _ hbc.2.2
        omega
    set R : Finset ℕ := (Finset.range (r + 1)).filter (fun k =>
      Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k) with hRdef
    have hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
      intro k
      rw [hRdef, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨Nat.lt_succ_of_le (hle k h), h⟩
    set stops : Finset ℕ := (Finset.range (n + r + 1)).filter (fun w =>
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) with hsdef
    have hstops : ∀ w, w ∈ stops ↔
        (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
        (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)) := by
      intro w
      rw [hsdef, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rcases h with ⟨h1, _⟩ | ⟨h1, h2, _⟩
        · omega
        · have := hle _ ((hR _).1 h2)
          omega
    set Znew : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or ∧ TwoNe g f k)
      with hZn
    obtain ⟨hcov, hup⟩ := cover_g n g hback f hf2 Z r R hR stops hstops
    have hcnt : (stops.filter (fun w => (f w).Nonempty)).card ≤ Znew.card + 1 :=
      cone_count2 n g f hf2 Z (fun k _ h => hlen k h) r R hR stops hstops Znew (by
        intro k hk hkZ hor htwo
        rw [hZn, Finset.mem_filter]
        exact ⟨hk, hkZ, hor, htwo⟩)
    refine ⟨Znew, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro k hk hk2
      rw [hZn, Finset.mem_filter] at hk2
      exact hk2.2.1 hk
    · intro k hk
      rw [hZn, Finset.mem_filter] at hk
      refine ⟨hk.2.2.1, hk.2.2.2, hρn, ?_, hup k hk.1⟩
      rw [Nat.add_sub_cancel_left]
      have hreach : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k →
          Relation.ReflTransGen (fun k k' : ℕ =>
            (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
        intro k h
        induction h with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hbc ih => exact ih.tail hbc.2
      exact hreach k ((hR k).1 hk.1)
    · have hsub : ((f (n + r)).image (fun v => s(c, v))) \ E0 ⊆
          (stops.filter (fun w => (f w).Nonempty)).biUnion
            (fun w => ((f w).image (fun v => s(c, v))) \ E0) := by
        intro e he
        rw [Finset.mem_sdiff, Finset.mem_image] at he
        obtain ⟨⟨v, hv, rfl⟩, he0⟩ := he
        obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.1 (hcov hv)
        refine Finset.mem_biUnion.2 ⟨w, Finset.mem_filter.2 ⟨hw, ⟨v, hvw⟩⟩, ?_⟩
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_image_of_mem _ hvw, he0⟩
      have hone : ∀ w, w ∈ stops.filter (fun w => (f w).Nonempty) →
          (((f w).image (fun v => s(c, v))) \ E0).card ≤ 1 := by
        intro w hw'
        have hw := (Finset.mem_filter.1 hw').1
        have himg : ∀ t : Finset (Fin n), t.card ≤ 1 →
            ((t.image (fun v => s(c, v))) \ E0).card ≤ 1 := fun t ht =>
          (Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_image_le.trans ht)
        rcases (hstops w).1 hw with ⟨hwn, _⟩ | ⟨hwn, hwR, hw2⟩
        · exact himg _ (hf1 w hwn)
        · have hweq : n + (w - n) = w := by omega
          rcases hw2 with hz | hnor
          · have hsubw : f (n + (w - n)) ⊆ f (n + r) := hup _ hwR
            rcases hZ _ hz hsubw with hall | hc1
            · rw [hweq] at hall
              have hempty : ((f w).image (fun v => s(c, v))) \ E0 = ∅ := by
                rw [Finset.sdiff_eq_empty_iff_subset]
                intro e he
                obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
                exact hall v hv
              rw [hempty]
              simp
            · rw [hweq] at hc1
              exact himg _ hc1
          · have := hf3 _ hnor
            rw [hweq] at this
            exact himg _ this
      calc (((f (n + r)).image (fun v => s(c, v))) \ E0).card
          ≤ ((stops.filter (fun w => (f w).Nonempty)).biUnion
              (fun w => ((f w).image (fun v => s(c, v))) \ E0)).card :=
            Finset.card_le_card hsub
        _ ≤ (stops.filter (fun w => (f w).Nonempty)).card * 1 :=
            Finset.card_biUnion_le_card_mul _ _ _ hone
        _ ≤ Znew.card + 1 := by omega

lemma star_count2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
    (l : List (Fin n × ℕ))
    (hadj : ∀ p, p ∈ l → ∀ v, v ∈ f p.2 → G.Adj p.1 v) :
    ∃ Z : Finset ℕ,
      (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ p, p ∈ l ∧ n ≤ p.2 ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (p.2 - n) k ∧ f (n + k) ⊆ f p.2) ∧
      (l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v)))).card
        ≤ l.length + Z.card := by
  classical
  induction l with
  | nil => exact ⟨∅, by simp, by simp⟩
  | cons p l ih =>
    obtain ⟨Z, hZ1, hZ2⟩ := ih (fun q hq => hadj q (List.mem_cons_of_mem _ hq))
    set E0 := l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v))) with hE0
    obtain ⟨Znew, hd, hn1, hn2⟩ := top_step2 n g hlen hback f hf1 hf2 hf3 (Z ∪ B) p.2 p.1 E0 (by
      intro k hk hsub
      rcases Finset.mem_union.1 hk with hk | hk
      · obtain ⟨_, _, _, q, hq, _, _, hfq⟩ := hZ1 k hk
        by_cases hc : q.1 = p.1
        · left
          intro v hv
          rw [hE0]
          refine Finset.mem_biUnion.2 ⟨q, List.mem_toFinset.2 hq, ?_⟩
          rw [← hc]
          exact Finset.mem_image_of_mem _ (hfq hv)
        · right
          by_contra hcard
          have h2 : 1 < (f (n + k)).card := by omega
          obtain ⟨v, hv, v', hv', hne⟩ := Finset.one_lt_card.1 h2
          have a1 : G.Adj p.1 v := hadj p List.mem_cons_self v (hsub hv)
          have a2 : G.Adj p.1 v' := hadj p List.mem_cons_self v' (hsub hv')
          have b1 : G.Adj q.1 v := hadj q (List.mem_cons_of_mem _ hq) v (hfq hv)
          have b2 : G.Adj q.1 v' := hadj q (List.mem_cons_of_mem _ hq) v' (hfq hv')
          exact h4 p.1 v q.1 v' (fun h => hc h.symm) hne ⟨a1, b1.symm, b2, a2.symm⟩
      · exact Or.inr (hB k hk))
    have hd1 : Disjoint Z Znew := Finset.disjoint_of_subset_left Finset.subset_union_left hd
    refine ⟨Z ∪ Znew, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_union.1 hk with hk | hk
      · obtain ⟨h0, h1, ht, q, hq, h2⟩ := hZ1 k hk
        exact ⟨h0, h1, ht, q, List.mem_cons_of_mem _ hq, h2⟩
      · obtain ⟨h1, ht, h2, h3, h5⟩ := hn1 k hk
        refine ⟨?_, h1, ht, p, List.mem_cons_self, h2, h3, h5⟩
        intro hkB
        exact (Finset.disjoint_left.1 hd (Finset.mem_union_right _ hkB)) hk
    · rw [List.toFinset_cons, Finset.biUnion_insert, Finset.card_union_of_disjoint hd1,
        List.length_cons, ← hE0]
      have hsplit : (f p.2).image (fun v => s(p.1, v)) ∪ E0 =
          (((f p.2).image (fun v => s(p.1, v))) \ E0) ∪ E0 := by
        rw [Finset.sdiff_union_self_eq_union]
      have hle := Finset.card_union_le (((f p.2).image (fun v => s(p.1, v))) \ E0) E0
      rw [← hsplit] at hle
      omega

lemma assemble2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
    (T : Finset ℕ) (o : ℕ → Fin 2 → ℕ)
    (hstar : ∀ a, a ∈ T → (∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) → G.Adj u v) ∧
      ((f (o a 0)).card ≤ 1 ∨ (f (o a 1)).card ≤ 1))
    (Es : Finset (Sym2 (Fin n)))
    (hEs : ∀ e, e ∈ Es → ∃ a, a ∈ T ∧ ∃ u, u ∈ f (o a 0) ∧ ∃ v, v ∈ f (o a 1) ∧ e = s(u, v)) :
    (∃ Z : Finset ℕ,
      (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ a, a ∈ T ∧ ∃ b : Fin 2,
        n ≤ o a b ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (o a b - n) k ∧
        f (n + k) ⊆ f (o a b) ∧ (f (o a (1 - b))).card = 1) ∧
      Es.card ≤ T.card + Z.card) ∧
    ∀ (H : SimpleGraph (Fin n)) (K : Finset (Fin n)),
      (∀ u v : Fin n, H.Adj u v → s(u, v) ∈ Es) → IsMinCover H K → K.card ≤ T.card := by
  classical
  by_cases hEe : Es = ∅
  · subst hEe
    refine ⟨⟨∅, by simp, by simp⟩, ?_⟩
    intro H K hH hK
    have h0 := hK.2 ∅ (by
      intro u v huv
      exact absurd (hH u v huv) (Finset.notMem_empty _))
    simp only [Finset.card_empty] at h0
    omega
  · obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.2 hEe
    obtain ⟨_, _, v0, _, _⟩ := hEs e0 he0
    set c : ℕ → Fin n := fun a =>
      if (f (o a 0)).card ≤ 1 then (if h : (f (o a 0)).Nonempty then h.choose else v0)
      else (if h : (f (o a 1)).Nonempty then h.choose else v0) with hc
    set ρ : ℕ → ℕ := fun a => if (f (o a 0)).card ≤ 1 then o a 1 else o a 0 with hρ
    have hkey : ∀ a, a ∈ T → ∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) →
        (c a = u ∧ v ∈ f (ρ a)) ∨ (c a = v ∧ u ∈ f (ρ a)) := by
      intro a ha u hu v hv
      by_cases h0 : (f (o a 0)).card ≤ 1
      · left
        have hne : (f (o a 0)).Nonempty := ⟨u, hu⟩
        refine ⟨?_, ?_⟩
        · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
          exact Finset.card_le_one.1 h0 _ hne.choose_spec _ hu
        · simp only [hρ, h0, ↓reduceIte]
          exact hv
      · right
        have h1 : (f (o a 1)).card ≤ 1 := by
          rcases (hstar a ha).2 with h | h
          · exact absurd h h0
          · exact h
        have hne : (f (o a 1)).Nonempty := ⟨v, hv⟩
        refine ⟨?_, ?_⟩
        · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
          exact Finset.card_le_one.1 h1 _ hne.choose_spec _ hv
        · simp only [hρ, h0, ↓reduceIte]
          exact hu
    set T' : Finset ℕ := T.filter (fun a => (f (o a 0)).Nonempty ∧ (f (o a 1)).Nonempty)
      with hT'
    have hT'T : ∀ a, a ∈ T' → a ∈ T := fun a ha => (Finset.mem_filter.1 ha).1
    have hT'card : T'.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hadjc : ∀ a, a ∈ T' → ∀ v, v ∈ f (ρ a) → G.Adj (c a) v := by
      intro a ha' v hv
      have ha := hT'T a ha'
      have hnn := (Finset.mem_filter.1 ha').2
      by_cases h0 : (f (o a 0)).card ≤ 1
      · simp only [hρ, h0, ↓reduceIte] at hv
        have hne := hnn.1
        simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
        exact (hstar a ha).1 _ hne.choose_spec v hv
      · simp only [hρ, h0, ↓reduceIte] at hv
        have hne := hnn.2
        simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
        exact ((hstar a ha).1 v hv _ hne.choose_spec).symm
    have hEs' : ∀ e, e ∈ Es → ∃ a, a ∈ T' ∧ ∃ v, v ∈ f (ρ a) ∧ e = s(c a, v) := by
      intro e he
      obtain ⟨a, ha, u, hu, v, hv, rfl⟩ := hEs e he
      have ha' : a ∈ T' := Finset.mem_filter.2 ⟨ha, ⟨u, hu⟩, ⟨v, hv⟩⟩
      rcases hkey a ha u hu v hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨a, ha', v, h2, by rw [h1]⟩
      · exact ⟨a, ha', u, h2, by rw [h1]; exact Sym2.eq_swap⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨Z, hZ1, hZ2⟩ := star_count2 n G h4 g hlen hback f hf1 hf2 hf3 B hB
        (T'.toList.map (fun a => (c a, ρ a))) (by
          intro p hp v hv
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
          exact hadjc a (Finset.mem_toList.1 ha) v hv)
      refine ⟨Z, ?_, ?_⟩
      · intro k hk
        obtain ⟨h1, h2, ht, p, hp, h3, h5, h6⟩ := hZ1 k hk
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
        have ha' := Finset.mem_toList.1 ha
        have hnn := (Finset.mem_filter.1 ha').2
        refine ⟨h1, h2, ht, a, hT'T a ha', ?_⟩
        by_cases h0 : (f (o a 0)).card ≤ 1
        · refine ⟨1, ?_⟩
          simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
          have e : (1 - 1 : Fin 2) = 0 := by decide
          rw [e]
          exact ⟨h3, h5, h6, le_antisymm h0 (Finset.card_pos.2 hnn.1)⟩
        · refine ⟨0, ?_⟩
          simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
          have e : (1 - 0 : Fin 2) = 1 := by decide
          rw [e]
          have h1' : (f (o a 1)).card ≤ 1 := by
            rcases (hstar a (hT'T a ha')).2 with h | h
            · exact absurd h h0
            · exact h
          exact ⟨h3, h5, h6, le_antisymm h1' (Finset.card_pos.2 hnn.2)⟩
      · have hsub : Es ⊆ (T'.toList.map (fun a => (c a, ρ a))).toFinset.biUnion
            (fun p => (f p.2).image (fun v => s(p.1, v))) := by
          intro e he
          obtain ⟨a, ha, v, hv, rfl⟩ := hEs' e he
          refine Finset.mem_biUnion.2 ⟨(c a, ρ a), ?_, Finset.mem_image_of_mem _ hv⟩
          exact List.mem_toFinset.2 (List.mem_map.2 ⟨a, Finset.mem_toList.2 ha, rfl⟩)
        have h1 := Finset.card_le_card hsub
        rw [List.length_map, Finset.length_toList] at hZ2
        omega
    · intro H K hH hK
      refine (cover_bound n H T' c ?_ K hK).trans hT'card
      intro u v huv
      obtain ⟨a, ha, w, hw, he⟩ := hEs' _ (hH u v huv)
      refine ⟨a, ha, ?_⟩
      have := Sym2.eq_iff.1 he
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inl h1.symm
      · exact Or.inr h2.symm

lemma gateAt_ge {C : Circuit} {k : ℕ} (hk : C.gates.length ≤ k) :
    gateAt C k = ⟨GateOp.or, []⟩ := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]

lemma orIn_iff_reach {n : ℕ} {C : Circuit} (p : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C p ↔ Relation.ReflTransGen (S90.OrStep n C) p u.val :=
  ⟨S90.mem_orIn_reach u, S90.reach_mem_orIn u⟩

lemma orIn_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [orIn_iff_reach] at ha hb
  have h1 : ∀ c : Fin n, Relation.ReflTransGen (S90.OrStep n C) w c.val → c.val = w := by
    intro c hc
    rcases Relation.ReflTransGen.cases_head hc with h | ⟨d, hd, _⟩
    · exact h.symm
    · obtain ⟨k, _, h3, _⟩ := hd
      omega
  exact Fin.ext ((h1 a ha).trans (h1 b hb).symm)

lemma orIn_gate {n : ℕ} (C : Circuit) (k : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔ k < C.gates.length ∧
      (gateAt C k).op = GateOp.or ∧ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧
        u ∈ PEqualNP.TopForm.orIn n C w := by
  rw [orIn_iff_reach]
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨d, hd, hr⟩
    · have := u.isLt
      omega
    · obtain ⟨k', hk', he, hop, hin, hlt⟩ := hd
      have hkk : k' = k := by omega
      subst hkk
      exact ⟨hk', hop, d, hin, hlt, (orIn_iff_reach d u).2 hr⟩
  · rintro ⟨hk, hop, w, hw, hlt, hu⟩
    exact Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hw, hlt⟩ ((orIn_iff_reach w u).1 hu)

lemma junk_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ PEqualNP.TopForm.junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ PEqualNP.TopForm.BelowF G C k := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  simp only [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
  constructor
  · rintro ⟨h1, h2, _, x, hx1, hx2⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have h3 := h x hx1
    rw [hx2] at h3
    exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h1, ?_⟩
    by_contra hc
    apply h3
    intro x hx
    by_contra hf
    exact hc ⟨x, hx, by simpa using hf⟩

lemma opnd_lt {n : ℕ} {C : Circuit} (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hRB : ReadsBack n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    PEqualNP.TopForm.opnd C a b < n + a := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (S90.gateAt_mem ha))
  have hp : p < n + a := hRB a ha p (by rw [hin]; simp)
  have hq : q < n + a := hRB a ha q (by rw [hin]; simp)
  fin_cases b
  · simpa [PEqualNP.TopForm.opnd, hin] using hp
  · simpa [PEqualNP.TopForm.opnd, hin] using hq

lemma rtg_conv {n : ℕ} (C : Circuit) (hRB : ReadsBack n C) (r k : ℕ)
    (h : Relation.ReflTransGen (fun k k' : ℕ =>
      (gateAt C k).op = GateOp.or ∧ n + k' ∈ (gateAt C k).inputs) r k)
    (hr : r < C.gates.length) :
    Relation.ReflTransGen (S90.OrStep n C) (n + r) (n + k) ∧ k < C.gates.length := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, hr⟩
  | tail _ hbc ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hlt := hRB _ ih2 _ hbc.2
    exact ⟨ih1.tail ⟨_, ih2, rfl, hbc.1, hbc.2, hlt⟩, by omega⟩

lemma two_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hRB : ReadsBack n C) {k : ℕ}
    (hk : k < C.gates.length) (hor : (gateAt C k).op = GateOp.or)
    (htwo : TwoNe (gateAt C) (PEqualNP.TopForm.orIn n C) k) :
    ¬ PEqualNP.TopForm.BelowF G C k ∧
      (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C k 0)).Nonempty ∧
      (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C k 1)).Nonempty := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (S90.gateAt_mem hk))
  have e0 : PEqualNP.TopForm.opnd C k 0 = p := by simp [PEqualNP.TopForm.opnd, hin]
  have e1 : PEqualNP.TopForm.opnd C k 1 = q := by simp [PEqualNP.TopForm.opnd, hin]
  obtain ⟨w1, hw1, w2, hw2, hne, hn1, hn2⟩ := htwo
  have hw1lt : w1 < n + k := hRB k hk w1 hw1
  have hw1m := hw1
  rw [hin] at hw1 hw2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw1 hw2
  refine ⟨?_, ?_⟩
  · intro hbel
    obtain ⟨u, hu⟩ := hn1
    have hu2 : u ∈ PEqualNP.TopForm.orIn n C (n + k) :=
      (orIn_gate C k u).2 ⟨hk, hor, w1, hw1m, hw1lt, hu⟩
    have hr := (orIn_iff_reach _ u).1 hu2
    have hv := S90.reach_var_val (PEqualNP.EdgeOwnership.pairInput u u) (n + k) u hr
      (S90.pairInput_left u u)
    have hF := hbel _ (by rw [S90.gateVal_eq_val]; exact hv)
    exact G.irrefl ((S90.graphFun_pair G u u).1 hF)
  · rw [e0, e1]
    rcases hw1 with h1 | h1 <;> rcases hw2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1] at hn1
      rw [h2] at hn2
      exact ⟨hn1, hn2⟩
    · rw [h1] at hn1
      rw [h2] at hn2
      exact ⟨hn2, hn1⟩
    · exact absurd (h1.trans h2.symm) hne

lemma main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : PEqualNP.TopForm.NoFourCycle G)
    (hC : PEqualNP.TopForm.IsAO2 n C)
    (hcount : (PEqualNP.TopForm.orT G C).card + 1 = (PEqualNP.TopForm.tops G C).card) :
    G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
      K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card := by
  classical
  obtain ⟨hAO, hRB, h2⟩ := id hC
  have hlen : ∀ k, (gateAt C k).op = GateOp.or → (gateAt C k).inputs.length ≤ 2 := by
    intro k _
    by_cases hk : k < C.gates.length
    · rw [h2 _ (S90.gateAt_mem hk)]
    · rw [gateAt_ge (by omega)]
      simp
  have hback : ∀ k, ∀ i ∈ (gateAt C k).inputs, i < n + k := by
    intro k i hi
    by_cases hk : k < C.gates.length
    · exact hRB k hk i hi
    · rw [gateAt_ge (by omega)] at hi
      simp at hi
  have hf2 : ∀ k, (gateAt C k).op = GateOp.or → ∀ u,
      u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔
        ∃ w ∈ (gateAt C k).inputs, u ∈ PEqualNP.TopForm.orIn n C w := by
    intro k hop u
    rw [orIn_gate]
    constructor
    · rintro ⟨_, _, w, hw, _, hu⟩
      exact ⟨w, hw, hu⟩
    · rintro ⟨w, hw, hu⟩
      have hk : k < C.gates.length := by
        by_contra hk
        rw [gateAt_ge (by omega)] at hw
        simp at hw
      exact ⟨hk, hop, w, hw, hRB k hk w hw, hu⟩
  have hf3 : ∀ k, (gateAt C k).op ≠ GateOp.or →
      (PEqualNP.TopForm.orIn n C (n + k)).card ≤ 1 := by
    intro k hop
    rw [Finset.card_le_one]
    intro a ha
    exact absurd ((orIn_gate C k a).1 ha).2.1 hop
  have h4' : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    rintro a b c d hac hbd ⟨h1, h2', h3, h5⟩
    have hsub : ({b, d} : Finset (Fin n)) ⊆
        Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj c w) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact ⟨h1, h2'.symm⟩
      · exact ⟨h5.symm, h3⟩
    have := (Finset.card_le_card hsub).trans (h4 a c hac)
    rw [Finset.card_pair hbd] at this
    omega
  have hstar : ∀ a, a ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C →
      (∀ u, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) →
        ∀ v, v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1) → G.Adj u v) ∧
      ((PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0)).card ≤ 1 ∨
        (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1)).card ≤ 1) := by
    intro a ha
    have hf := S90.top_facts G C h4 hC a (Finset.mem_sdiff.1 ha).1
    exact ⟨hf.2.1, hf.2.2⟩
  have hEs : ∀ e, e ∈ G.edgeFinset \ PEqualNP.TopForm.Ustar G C →
      ∃ a, a ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C ∧
        ∃ u, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) ∧
        ∃ v, v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1) ∧ e = s(u, v) := by
    intro e he
    have he' : e ∈ PEqualNP.TopForm.starEdges G C := by
      simp only [PEqualNP.TopForm.Ustar, Finset.mem_sdiff, not_and, not_not] at he
      exact he.2 he.1
    simp only [PEqualNP.TopForm.starEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_product] at he'
    obtain ⟨a, ha, p, hp, hpe⟩ := he'
    refine ⟨a, ?_, p.1, hp.1, p.2, hp.2, hpe.symm⟩
    rw [Finset.mem_sdiff]
    refine ⟨ha, fun hc => ?_⟩
    simp only [PEqualNP.TopForm.centreless, Finset.mem_filter] at hc
    rcases hc.2 with h | h
    · have := hp.1
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
    · have := hp.2
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
  obtain ⟨⟨Z, hZ1, hZ2⟩, hcov⟩ := assemble2 n G h4' (gateAt C) hlen hback
    (fun w => PEqualNP.TopForm.orIn n C w) (fun w hw => orIn_input C w hw) hf2 hf3 ∅ (by simp)
    (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C) (PEqualNP.TopForm.opnd C)
    hstar (G.edgeFinset \ PEqualNP.TopForm.Ustar G C) hEs
  refine ⟨?_, ?_⟩
  · have hZlam : Z ⊆ PEqualNP.TopForm.lam G C := by
      intro k hk
      obtain ⟨-, hor, htwo, a, ha, b, hnb, hrt, -, hcard⟩ := hZ1 k hk
      have hatop := (Finset.mem_sdiff.1 ha).1
      have halen : a < C.gates.length := by
        simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
          Finset.mem_range] at hatop
        exact hatop.1
      have hlt := opnd_lt h2 hRB halen b
      obtain ⟨hreach, hklen⟩ := rtg_conv C hRB _ k hrt (by omega)
      rw [show n + (PEqualNP.TopForm.opnd C a b - n) = PEqualNP.TopForm.opnd C a b by omega]
        at hreach
      have hOR := S90.reach_orReaches hreach k rfl hklen
      obtain ⟨hnbel, hn0, hn1⟩ := two_facts G C h2 hRB hklen hor htwo
      simp only [PEqualNP.TopForm.lam, PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range]
      exact ⟨⟨hklen, hor, hnbel⟩, hn0, hn1, a, hatop, b, hcard, hOR⟩
    have hAO' : ∀ k, k < C.gates.length →
        ((gateAt C k).op = GateOp.and ∧ ¬ (gateAt C k).op = GateOp.or) ∨
        ((gateAt C k).op = GateOp.or ∧ ¬ (gateAt C k).op = GateOp.and) := by
      intro k hk
      rcases hAO _ (S90.gateAt_mem hk) with h | h
      · exact Or.inl ⟨h, fun h' => by rw [h] at h'; cases h'⟩
      · exact Or.inr ⟨h, fun h' => by rw [h] at h'; cases h'⟩
    have hsplit := four_split C.gates.length (fun k => (gateAt C k).op = GateOp.and)
      (fun k => (gateAt C k).op = GateOp.or) (fun k => PEqualNP.TopForm.BelowF G C k) hAO'
      (PEqualNP.TopForm.tops G C) (PEqualNP.TopForm.junk G C) (PEqualNP.TopForm.orT G C)
      (PEqualNP.TopForm.orN G C)
      (fun k => by simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
      (fun k => junk_iff G C k)
      (fun k => by simp only [PEqualNP.TopForm.orT, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
      (fun k => by simp only [PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
    have hm := hcount
    have hsize : C.size = C.gates.length := rfl
    have hU := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.Ustar G C ⊆ G.edgeFinset from Finset.sdiff_subset)
    have hTc := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.centreless G C ⊆ PEqualNP.TopForm.tops G C from
        Finset.filter_subset _ _)
    have hlam := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.lam G C ⊆ PEqualNP.TopForm.orN G C from
        Finset.filter_subset _ _)
    have hZl := Finset.card_le_card hZlam
    omega
  · intro K hK
    refine hcov _ K ?_ hK
    intro u v huv
    rw [SimpleGraph.deleteEdges_adj] at huv
    rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
    exact ⟨huv.1, fun h => huv.2 (Finset.mem_coe.2 h)⟩

end PEqualNP.Outside.L_meta_4675.Residual

namespace PEqualNP.Outside.L_meta_4675.Residual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

lemma exists_min_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ K : Finset (Fin n), IsMinCover G K := by
  classical
  let W : Finset (Finset (Fin n)) := Finset.univ.filter (fun K => G.IsVertexCover (K : Set (Fin n)))
  have hW : W.Nonempty := ⟨Finset.univ, by simp [W,SimpleGraph.IsVertexCover]⟩
  obtain ⟨K,hK,hmin⟩ := W.exists_min_image Finset.card hW
  exact ⟨K,(Finset.mem_filter.mp hK).2,fun K' hK' => hmin K' (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hK'⟩)⟩

lemma complete (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hC : IsAO2 n C)
    (hcount : (orT G C).card + 1 = (tops G C).card)
    (hres : ∃ S : Finset (Fin n),
      (∀ u v : Fin n, G.Adj u v → s(u,v) ∈ Ustar G C → u∈S ∨ v∈S) ∧
      (Ustar G C).card + S.card ≤ 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) :
    ∃ S : Finset (Fin n), (∀ u v, G.Adj u v → u∈S ∨ v∈S) ∧
      G.edgeFinset.card + S.card ≤ C.size+1 := by
  classical
  obtain ⟨hbudget,hcover⟩ := main n G C h4 hC hcount
  obtain ⟨S,hS,hSc⟩ := hres
  obtain ⟨K,hK⟩ := exists_min_cover (G.deleteEdges ↑(Ustar G C))
  have hKc := hcover K hK
  refine ⟨K∪S,?_,?_⟩
  · intro u v huv
    by_cases he : s(u,v) ∈ Ustar G C
    · exact (hS u v huv he).imp (Finset.mem_union_right K) (Finset.mem_union_right K)
    · have hdel : (G.deleteEdges ↑(Ustar G C)).Adj u v := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨huv,he⟩
      exact (hK.1 hdel).imp (Finset.mem_union_left S) (Finset.mem_union_left S)
  · have hcard := Finset.card_union_le K S
    omega

end PEqualNP.Outside.L_meta_4675.Residual

namespace PEqualNP.Outside.L_meta_4675.Residual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

lemma constrained_balance (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : ℕ → Bool) (hC : IsAO2 n C)
    (hz : PEqualNP.TwoColour.tCount n C s = 0)
    (hfun : circuitFun n C = graphFun G ∅) (hne : ∃ u v, G.Adj u v)
    (hmin : ∀ D : Circuit, IsAO2 n D → PEqualNP.TwoColour.tCount n D s = 0 →
      circuitFun n D = graphFun G ∅ → C.size ≤ D.size)
    (hTF : PEqualNP.TopForm.TopForm G C) :
    (orT G C).card + 1 = (tops G C).card := by
  have hL : Lift.Least (s := s) n C := by
    refine ⟨Lift.ao2_of n C hC,?_⟩
    intro D hD hf hDz
    apply hmin D (Lift.ao2_to n D hD) hDz
    funext x
    exact (hf x).trans (congrFun hfun x)
  have hS : ∀ a : Fin n, Lift.wv n C (fun j => decide (j=a)) C.output = false := by
    intro a
    change circuitFun n C _ = false
    rw [hfun]
    exact SemanticFold.graphFun_singleton_false G a
  exact TreeCount.balance n G C s hL hz hS
    (SemanticFold.least_output_last G C s hC hz hfun hne hmin)
    (SemanticFold.least_no_unused G C s hC hz hfun hne hmin) hfun hTF

lemma constrained_main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : ℕ → Bool) (h4 : NoFourCycle G) (hC : IsAO2 n C)
    (hz : PEqualNP.TwoColour.tCount n C s = 0)
    (hfun : circuitFun n C = graphFun G ∅) (hne : ∃ u v, G.Adj u v)
    (hmin : ∀ D : Circuit, IsAO2 n D → PEqualNP.TwoColour.tCount n D s = 0 →
      circuitFun n D = graphFun G ∅ → C.size ≤ D.size)
    (hTF : PEqualNP.TopForm.TopForm G C) :
    G.edgeFinset.card + (tops G C \ centreless G C).card + 2*(centreless G C).card +
      (junk G C).card + (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n), IsMinCover (G.deleteEdges ↑(Ustar G C)) K →
      K.card ≤ (tops G C \ centreless G C).card :=
  main n G C h4 hC (constrained_balance n G C s hC hz hfun hne hmin hTF)

lemma constrained_complete (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : ℕ → Bool) (h4 : NoFourCycle G) (hC : IsAO2 n C)
    (hz : PEqualNP.TwoColour.tCount n C s = 0)
    (hfun : circuitFun n C = graphFun G ∅) (hne : ∃ u v, G.Adj u v)
    (hmin : ∀ D : Circuit, IsAO2 n D → PEqualNP.TwoColour.tCount n D s = 0 →
      circuitFun n D = graphFun G ∅ → C.size ≤ D.size)
    (hTF : PEqualNP.TopForm.TopForm G C)
    (hres : ∃ S : Finset (Fin n),
      (∀ u v : Fin n, G.Adj u v → s(u,v) ∈ Ustar G C → u∈S ∨ v∈S) ∧
      (Ustar G C).card + S.card ≤ 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) :
    ∃ S : Finset (Fin n), (∀ u v, G.Adj u v → u∈S ∨ v∈S) ∧
      G.edgeFinset.card + S.card ≤ C.size+1 :=
  complete n G C h4 hC (constrained_balance n G C s hC hz hfun hne hmin hTF) hres

end PEqualNP.Outside.L_meta_4675.Residual

namespace PEqualNP.Outside.L_meta_4675.Residual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

def Certificate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Prop :=
  ∃ S : Finset (Fin n),
    (∀ u v : Fin n, G.Adj u v → s(u,v) ∈ Ustar G C → u∈S ∨ v∈S) ∧
    (Ustar G C).card + S.card ≤ 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card

lemma bipartite_reduction (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (h4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a,b)∈E ∧ (a,b')∈E ∧ (a',b)∈E ∧ (a',b')∈E))
    (hAO : IsAO2 (p + l) C)
    (hfun : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ a b, (a,b)∈E ∧ x (Fin.castAdd l a)= true ∧ x (Fin.natAdd p b)= true))
    (hz : PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0)
    (hresidual : letI := Classical.decRel (Bipartite.graph E).Adj
      ∀ D : Circuit, IsAO2 (p + l) D → circuitFun (p + l) D = graphFun (Bipartite.graph E) ∅ →
        PEqualNP.TwoColour.tCount (p + l) D (fun i => decide (p ≤ i)) = 0 →
        PEqualNP.TopForm.TopForm (Bipartite.graph E) D →
        (∀ D' : Circuit, IsAO2 (p + l) D' → circuitFun (p + l) D' = graphFun (Bipartite.graph E) ∅ →
          PEqualNP.TwoColour.tCount (p + l) D' (fun i => decide (p ≤ i)) = 0 → D.size ≤ D'.size) →
        (∀ j < D.gates.length, ∃ u v, (Bipartite.graph E).Adj u v ∧ gateVal (p + l) D j (pairInput u v)= true) →
        Certificate (Bipartite.graph E) D) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a,b)∈E → Fin.castAdd l a∈S ∨ Fin.natAdd p b∈S) ∧
      E.card+S.card ≤ C.size+1 := by
  classical
  letI := Classical.decRel (Bipartite.graph E).Adj
  by_cases he : E=∅
  · subst E
    exact ⟨∅,by simp,by simp⟩
  have hne : ∃ u v, (Bipartite.graph E).Adj u v := by
    obtain ⟨⟨a,b⟩,hab⟩ := Finset.nonempty_iff_ne_empty.mpr he
    exact ⟨Fin.castAdd l a,Fin.natAdd p b,by simpa [Bipartite.graph,Bipartite.cross] using hab⟩
  have hf : circuitFun (p + l) C = graphFun (Bipartite.graph E) ∅ := by
    funext x
    rw [hfun,Bipartite.graphFun_eq]
  obtain ⟨D,hD,hDf,hDz,hsize,hTF,hmin,hactive⟩ :=
    Normalized.exists_top_form_pair_active (Bipartite.graph E) C (fun i => decide (p ≤ i)) hne hAO hf hz
  have hcert := hresidual D hD hDf hDz hTF hmin hactive
  obtain ⟨S,hS,hSc⟩ := constrained_complete (p + l) (Bipartite.graph E) D
    (fun i => decide (p ≤ i)) (Bipartite.noRectangle E h4) hD hDz hDf hne
    (fun D' hD' hDz' hDf' => hmin D' hD' hDf' hDz') hTF hcert
  refine ⟨S,?_,?_⟩
  · intro a b hab
    exact hS (Fin.castAdd l a) (Fin.natAdd p b) (by simpa [Bipartite.graph,Bipartite.cross] using hab)
  · rw [Bipartite.edge_card] at hSc
    omega

end PEqualNP.Outside.L_meta_4675.Residual

namespace PEqualNP.Outside.L_meta_4675.Residual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

noncomputable def largeLam {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Finset ℕ :=
  (PEqualNP.TopForm.lam G C).filter (fun k => 2 ≤ (PEqualNP.TopForm.orIn n C (n+k)).card)

lemma main_large (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : PEqualNP.TopForm.NoFourCycle G)
    (hC : PEqualNP.TopForm.IsAO2 n C)
    (hcount : (PEqualNP.TopForm.orT G C).card + 1 = (PEqualNP.TopForm.tops G C).card) :
    G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ largeLam G C).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
      K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card := by
  classical
  obtain ⟨hAO, hRB, h2⟩ := id hC
  have hlen : ∀ k, (gateAt C k).op = GateOp.or → (gateAt C k).inputs.length ≤ 2 := by
    intro k _
    by_cases hk : k < C.gates.length
    · rw [h2 _ (S90.gateAt_mem hk)]
    · rw [gateAt_ge (by omega)]
      simp
  have hback : ∀ k, ∀ i ∈ (gateAt C k).inputs, i < n + k := by
    intro k i hi
    by_cases hk : k < C.gates.length
    · exact hRB k hk i hi
    · rw [gateAt_ge (by omega)] at hi
      simp at hi
  have hf2 : ∀ k, (gateAt C k).op = GateOp.or → ∀ u,
      u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔
        ∃ w ∈ (gateAt C k).inputs, u ∈ PEqualNP.TopForm.orIn n C w := by
    intro k hop u
    rw [orIn_gate]
    constructor
    · rintro ⟨_, _, w, hw, _, hu⟩
      exact ⟨w, hw, hu⟩
    · rintro ⟨w, hw, hu⟩
      have hk : k < C.gates.length := by
        by_contra hk
        rw [gateAt_ge (by omega)] at hw
        simp at hw
      exact ⟨hk, hop, w, hw, hRB k hk w hw, hu⟩
  have hf3 : ∀ k, (gateAt C k).op ≠ GateOp.or →
      (PEqualNP.TopForm.orIn n C (n + k)).card ≤ 1 := by
    intro k hop
    rw [Finset.card_le_one]
    intro a ha
    exact absurd ((orIn_gate C k a).1 ha).2.1 hop
  have h4' : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    rintro a b c d hac hbd ⟨h1, h2', h3, h5⟩
    have hsub : ({b, d} : Finset (Fin n)) ⊆
        Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj c w) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact ⟨h1, h2'.symm⟩
      · exact ⟨h5.symm, h3⟩
    have := (Finset.card_le_card hsub).trans (h4 a c hac)
    rw [Finset.card_pair hbd] at this
    omega
  have hstar : ∀ a, a ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C →
      (∀ u, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) →
        ∀ v, v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1) → G.Adj u v) ∧
      ((PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0)).card ≤ 1 ∨
        (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1)).card ≤ 1) := by
    intro a ha
    have hf := S90.top_facts G C h4 hC a (Finset.mem_sdiff.1 ha).1
    exact ⟨hf.2.1, hf.2.2⟩
  have hEs : ∀ e, e ∈ G.edgeFinset \ PEqualNP.TopForm.Ustar G C →
      ∃ a, a ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C ∧
        ∃ u, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) ∧
        ∃ v, v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1) ∧ e = s(u, v) := by
    intro e he
    have he' : e ∈ PEqualNP.TopForm.starEdges G C := by
      simp only [PEqualNP.TopForm.Ustar, Finset.mem_sdiff, not_and, not_not] at he
      exact he.2 he.1
    simp only [PEqualNP.TopForm.starEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_product] at he'
    obtain ⟨a, ha, p, hp, hpe⟩ := he'
    refine ⟨a, ?_, p.1, hp.1, p.2, hp.2, hpe.symm⟩
    rw [Finset.mem_sdiff]
    refine ⟨ha, fun hc => ?_⟩
    simp only [PEqualNP.TopForm.centreless, Finset.mem_filter] at hc
    rcases hc.2 with h | h
    · have := hp.1
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
    · have := hp.2
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
  obtain ⟨⟨Z, hZ1, hZ2⟩, hcov⟩ := assemble2 n G h4' (gateAt C) hlen hback
    (fun w => PEqualNP.TopForm.orIn n C w) (fun w hw => orIn_input C w hw) hf2 hf3
    ((Finset.range C.gates.length).filter (fun k => (PEqualNP.TopForm.orIn n C (n+k)).card ≤ 1))
    (fun k hk => (Finset.mem_filter.mp hk).2)
    (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C) (PEqualNP.TopForm.opnd C)
    hstar (G.edgeFinset \ PEqualNP.TopForm.Ustar G C) hEs
  refine ⟨?_, ?_⟩
  · have hZlam : Z ⊆ largeLam G C := by
      intro k hk
      obtain ⟨hnotSmall, hor, htwo, a, ha, b, hnb, hrt, -, hcard⟩ := hZ1 k hk
      have hatop := (Finset.mem_sdiff.1 ha).1
      have halen : a < C.gates.length := by
        simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
          Finset.mem_range] at hatop
        exact hatop.1
      have hlt := opnd_lt h2 hRB halen b
      obtain ⟨hreach, hklen⟩ := rtg_conv C hRB _ k hrt (by omega)
      rw [show n + (PEqualNP.TopForm.opnd C a b - n) = PEqualNP.TopForm.opnd C a b by omega]
        at hreach
      have hOR := S90.reach_orReaches hreach k rfl hklen
      obtain ⟨hnbel, hn0, hn1⟩ := two_facts G C h2 hRB hklen hor htwo
      have hbig : 2 ≤ (PEqualNP.TopForm.orIn n C (n+k)).card := by
        by_contra hn
        apply hnotSmall
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hklen,by omega⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_,hbig⟩
      simp only [PEqualNP.TopForm.lam, PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range]
      exact ⟨⟨hklen, hor, hnbel⟩, hn0, hn1, a, hatop, b, hcard, hOR⟩
    have hAO' : ∀ k, k < C.gates.length →
        ((gateAt C k).op = GateOp.and ∧ ¬ (gateAt C k).op = GateOp.or) ∨
        ((gateAt C k).op = GateOp.or ∧ ¬ (gateAt C k).op = GateOp.and) := by
      intro k hk
      rcases hAO _ (S90.gateAt_mem hk) with h | h
      · exact Or.inl ⟨h, fun h' => by rw [h] at h'; cases h'⟩
      · exact Or.inr ⟨h, fun h' => by rw [h] at h'; cases h'⟩
    have hsplit := four_split C.gates.length (fun k => (gateAt C k).op = GateOp.and)
      (fun k => (gateAt C k).op = GateOp.or) (fun k => PEqualNP.TopForm.BelowF G C k) hAO'
      (PEqualNP.TopForm.tops G C) (PEqualNP.TopForm.junk G C) (PEqualNP.TopForm.orT G C)
      (PEqualNP.TopForm.orN G C)
      (fun k => by simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
      (fun k => junk_iff G C k)
      (fun k => by simp only [PEqualNP.TopForm.orT, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
      (fun k => by simp only [PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
    have hm := hcount
    have hsize : C.size = C.gates.length := rfl
    have hU := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.Ustar G C ⊆ G.edgeFinset from Finset.sdiff_subset)
    have hTc := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.centreless G C ⊆ PEqualNP.TopForm.tops G C from
        Finset.filter_subset _ _)
    have hlam := Finset.card_sdiff_add_card_eq_card
      (show largeLam G C ⊆ PEqualNP.TopForm.orN G C from
        (Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
    have hZl := Finset.card_le_card hZlam
    omega
  · intro K hK
    refine hcov _ K ?_ hK
    intro u v huv
    rw [SimpleGraph.deleteEdges_adj] at huv
    rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
    exact ⟨huv.1, fun h => huv.2 (Finset.mem_coe.2 h)⟩

end PEqualNP.Outside.L_meta_4675.Residual

namespace PEqualNP.Outside.L_meta_4675.Residual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma complete_large (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hC : IsAO2 n C)
    (hcount : (orT G C).card + 1 = (tops G C).card)
    (hres : ∃ S : Finset (Fin n),
      (∀ u v : Fin n, G.Adj u v → s(u,v) ∈ Ustar G C → u∈S ∨ v∈S) ∧
      (Ustar G C).card + S.card ≤ 2*(centreless G C).card + (junk G C).card + (orN G C \ largeLam G C).card) :
    ∃ S : Finset (Fin n), (∀ u v, G.Adj u v → u∈S ∨ v∈S) ∧
      G.edgeFinset.card + S.card ≤ C.size+1 := by
  classical
  obtain ⟨hbudget,hcover⟩ := main_large n G C h4 hC hcount
  obtain ⟨S,hS,hSc⟩ := hres
  obtain ⟨K,hK⟩ := exists_min_cover (G.deleteEdges ↑(Ustar G C))
  have hKc := hcover K hK
  refine ⟨K∪S,?_,?_⟩
  · intro u v huv
    by_cases he : s(u,v) ∈ Ustar G C
    · exact (hS u v huv he).imp (Finset.mem_union_right K) (Finset.mem_union_right K)
    · have hdel : (G.deleteEdges ↑(Ustar G C)).Adj u v := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨huv,he⟩
      exact (hK.1 hdel).imp (Finset.mem_union_left S) (Finset.mem_union_left S)
  · have hcard := Finset.card_union_le K S
    omega


def LargeCertificate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Prop :=
  ∃ S : Finset (Fin n),
    (∀ u v : Fin n, G.Adj u v → s(u,v) ∈ Ustar G C → u∈S ∨ v∈S) ∧
    (Ustar G C).card + S.card ≤ 2*(centreless G C).card + (junk G C).card + (orN G C \ largeLam G C).card

lemma bipartite_reduction_large (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (h4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a,b)∈E ∧ (a,b')∈E ∧ (a',b)∈E ∧ (a',b')∈E))
    (hAO : IsAO2 (p + l) C)
    (hfun : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ a b, (a,b)∈E ∧ x (Fin.castAdd l a)= true ∧ x (Fin.natAdd p b)= true))
    (hz : PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0)
    (hresidual : letI := Classical.decRel (Bipartite.graph E).Adj
      ∀ D : Circuit, IsAO2 (p + l) D → circuitFun (p + l) D = graphFun (Bipartite.graph E) ∅ →
        PEqualNP.TwoColour.tCount (p + l) D (fun i => decide (p ≤ i)) = 0 →
        PEqualNP.TopForm.TopForm (Bipartite.graph E) D →
        (∀ D' : Circuit, IsAO2 (p + l) D' → circuitFun (p + l) D' = graphFun (Bipartite.graph E) ∅ →
          PEqualNP.TwoColour.tCount (p + l) D' (fun i => decide (p ≤ i)) = 0 → D.size ≤ D'.size) →
        (∀ j < D.gates.length, ∃ u v, (Bipartite.graph E).Adj u v ∧ gateVal (p + l) D j (pairInput u v)= true) →
        LargeCertificate (Bipartite.graph E) D) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a,b)∈E → Fin.castAdd l a∈S ∨ Fin.natAdd p b∈S) ∧
      E.card+S.card ≤ C.size+1 := by
  classical
  letI := Classical.decRel (Bipartite.graph E).Adj
  by_cases he : E=∅
  · subst E
    exact ⟨∅,by simp,by simp⟩
  have hne : ∃ u v, (Bipartite.graph E).Adj u v := by
    obtain ⟨⟨a,b⟩,hab⟩ := Finset.nonempty_iff_ne_empty.mpr he
    exact ⟨Fin.castAdd l a,Fin.natAdd p b,by simpa [Bipartite.graph,Bipartite.cross] using hab⟩
  have hf : circuitFun (p + l) C = graphFun (Bipartite.graph E) ∅ := by
    funext x
    rw [hfun,Bipartite.graphFun_eq]
  obtain ⟨D,hD,hDf,hDz,hsize,hTF,hmin,hactive⟩ :=
    Normalized.exists_top_form_pair_active (Bipartite.graph E) C (fun i => decide (p ≤ i)) hne hAO hf hz
  have hcert := hresidual D hD hDf hDz hTF hmin hactive
  have hbalance := constrained_balance (p + l) (Bipartite.graph E) D
    (fun i => decide (p ≤ i)) hD hDz hDf hne
    (fun D' hD' hDz' hDf' => hmin D' hD' hDf' hDz') hTF
  obtain ⟨S,hS,hSc⟩ := complete_large (p + l) (Bipartite.graph E) D
    (Bipartite.noRectangle E h4) hD hbalance hcert
  refine ⟨S,?_,?_⟩
  · intro a b hab
    exact hS (Fin.castAdd l a) (Fin.natAdd p b) (by simpa [Bipartite.graph,Bipartite.cross] using hab)
  · rw [Bipartite.edge_card] at hSc
    omega

end PEqualNP.Outside.L_meta_4675.Residual

namespace PEqualNP.Outside.L_meta_4675.MaskMerge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.TwoColour
open PEqualNP.Outside.L_meta_4675.Lift

def merged (n : ℕ) (C : Circuit) (j k a b : ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (fun r =>
    if r = j then ⟨GateOp.or, [a,b]⟩
    else if r = k then ⟨GateOp.and, [n+j,n+j]⟩ else gateAt C r), C.output⟩

lemma merged_len (n : ℕ) (C : Circuit) (j k a b : ℕ) :
    (merged n C j k a b).gates.length = C.gates.length := by simp [merged]

lemma merged_gate (n : ℕ) (C : Circuit) (j k a b r : ℕ) (hr : r < C.gates.length) :
    gateAt (merged n C j k a b) r =
      if r = j then ⟨GateOp.or, [a,b]⟩
      else if r = k then ⟨GateOp.and, [n+j,n+j]⟩ else gateAt C r := by
  exact gateAt_range _ _ _ _ hr

lemma merged_AO (n : ℕ) (C : Circuit) (j k a b : ℕ) (hC : AO2 n C)
    (hjk : j < k) (ha : a < n+j) (hb : b < n+j) :
    AO2 n (merged n C j k a b) := by
  intro r hr
  rw [merged_len] at hr
  rw [merged_gate n C j k a b r hr]
  split_ifs with hj hk
  · subst r
    refine ⟨Or.inr rfl, ⟨a,b,rfl⟩, ?_⟩
    intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl <;> assumption
  · subst r
    refine ⟨Or.inl rfl, ⟨n+j,n+j,rfl⟩, ?_⟩
    intro w hw
    have hw' : w = n+j := by simpa using hw
    omega
  · exact hC r hr

lemma merged_values (n : ℕ) (C : Circuit) (i j k a b : ℕ)
    (hC : AO2 n C) (hij : i < j) (hjk : j < k) (hk : k < C.gates.length)
    (hiGate : gateAt C i = ⟨GateOp.and,[a,a]⟩)
    (hjGate : gateAt C j = ⟨GateOp.and,[b,b]⟩)
    (hkGate : gateAt C k = ⟨GateOp.or,[n+i,n+j]⟩)
    (huses : ∀ r < C.gates.length, r ≠ k → n+j ∉ (gateAt C r).inputs)
    (x : Fin n → Bool) :
    ∀ w < n+C.gates.length,
      wv n (merged n C j k a b) x w =
        if w = n+j then (wv n C x a || wv n C x b) else wv n C x w := by
  have hi : i < C.gates.length := by omega
  have hj : j < C.gates.length := by omega
  have ha := (hC i hi).2.2 a (by simp [hiGate])
  have hb := (hC j hj).2.2 b (by simp [hjGate])
  have hD := merged_AO n C j k a b hC hjk (by omega) hb
  have va : wv n C x (n+i) = wv n C x a := by
    rw [wv_rec n C x (aob hC) i hi, hiGate]
    simp [GateOp.eval]
  have vb : wv n C x (n+j) = wv n C x b := by
    rw [wv_rec n C x (aob hC) j hj, hjGate]
    simp [GateOp.eval]
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hin : w < n
    · rw [wv_input n _ x w hin, wv_input n C x w hin, ite_eq_right (by omega)]
    obtain ⟨r,rfl⟩ : ∃r,w=n+r := ⟨w-n,by omega⟩
    have hr : r < C.gates.length := by omega
    rw [wv_rec n _ x (aob hD) r (by rw [merged_len]; exact hr), merged_gate n C j k a b r hr]
    by_cases hrj : r = j
    · subst r
      rw [ite_eq_left rfl, ite_eq_left rfl]
      rw [eval_or_pair, ih a (by omega) (by omega), ih b (by omega) (by omega)]
      simp [show a ≠ n+j by omega,show b ≠ n+j by omega]
    · by_cases hrk : r = k
      · subst r
        rw [ite_eq_right hrj, ite_eq_left rfl, ite_eq_right (by omega)]
        rw [eval_and_pair, ih (n+j) (by omega) (by omega), ite_eq_left rfl]
        rw [wv_rec n C x (aob hC) k hk, hkGate, eval_or_pair, va, vb]
        simp
      · rw [ite_eq_right hrj, ite_eq_right hrk, ite_eq_right (by omega), wv_rec n C x (aob hC) r hr]
        congr 1
        apply List.map_congr_left
        intro v hv
        have hvlt := (hC r hr).2.2 v hv
        have hvne : v ≠ n+j := fun he => huses r hr hrk (he ▸ hv)
        rw [ih v hvlt (by omega), ite_eq_right hvne]

lemma merged_reach (n : ℕ) (C : Circuit) (i j k a b : ℕ)
    (hC : AO2 n C) (hij : i < j) (hjk : j < k) (hk : k < C.gates.length)
    (hiGate : gateAt C i = ⟨GateOp.and,[a,a]⟩)
    (hjGate : gateAt C j = ⟨GateOp.and,[b,b]⟩)
    (hkGate : gateAt C k = ⟨GateOp.or,[n+i,n+j]⟩)
    (huses : ∀ r < C.gates.length, r ≠ k → n+j ∉ (gateAt C r).inputs) :
    ∀ w < n+C.gates.length,
      orIn n (merged n C j k a b) w =
        if w = n+j then orIn n C a ∪ orIn n C b else orIn n C w := by
  have hi : i < C.gates.length := by omega
  have hj : j < C.gates.length := by omega
  have ha := (hC i hi).2.2 a (by simp [hiGate])
  have hb := (hC j hj).2.2 b (by simp [hjGate])
  have hD := merged_AO n C j k a b hC hjk (by omega) hb
  have hAO := ao2_to n C hC
  have hDO := ao2_to n _ hD
  have reachK : orIn n C (n+k) = ∅ := by
    rw [Redirect.orIn_or hAO hk (by rw [hkGate])]
    simp only [opnd,hkGate]
    change orIn n C (n+i) ∪ orIn n C (n+j) = ∅
    rw [Redirect.orIn_and hAO hi (by rw [hiGate]), Redirect.orIn_and hAO hj (by rw [hjGate])]
    simp
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hin : w < n
    · rw [Redirect.orIn_input (C := merged n C j k a b) ⟨w,hin⟩,
        Redirect.orIn_input (C := C) ⟨w,hin⟩, ite_eq_right (by omega)]
    obtain ⟨r,rfl⟩ : ∃r,w=n+r := ⟨w-n,by omega⟩
    have hr : r < C.gates.length := by omega
    have hrD : r < (merged n C j k a b).gates.length := by rw [merged_len]; exact hr
    have hg := merged_gate n C j k a b r hr
    by_cases hrj : r = j
    · subst r
      have hg' : gateAt (merged n C j k a b) j = ⟨GateOp.or,[a,b]⟩ := by simpa using hg
      rw [Redirect.orIn_or hDO hrD (by rw [hg']), ite_eq_left rfl]
      simp only [opnd,hg']
      change orIn n (merged n C j k a b) a ∪ orIn n (merged n C j k a b) b = _
      rw [ih a (by omega) (by omega), ih b (by omega) (by omega)]
      simp [show a ≠ n+j by omega,show b ≠ n+j by omega]
    · by_cases hrk : r = k
      · subst r
        have hg' : gateAt (merged n C j k a b) k = ⟨GateOp.and,[n+j,n+j]⟩ := by simpa [hrj] using hg
        rw [Redirect.orIn_and hDO hrD (by rw [hg']), ite_eq_right (by omega), reachK]
      · have hgs : gateAt (merged n C j k a b) r = gateAt C r := by simpa [hrj,hrk] using hg
        rw [ite_eq_right (by omega)]
        rcases (hC r hr).1 with hand | hor
        · rw [Redirect.orIn_and hDO hrD (by rw [hgs]; exact hand), Redirect.orIn_and hAO hr hand]
        · obtain ⟨u,v,huv⟩ := (hC r hr).2.1
          have huin : u ∈ (gateAt C r).inputs := by simp [huv]
          have hvin : v ∈ (gateAt C r).inputs := by simp [huv]
          have hult := (hC r hr).2.2 u huin
          have hvlt := (hC r hr).2.2 v hvin
          have hune : u ≠ n+j := fun he => huses r hr hrk (he ▸ huin)
          have hvne : v ≠ n+j := fun he => huses r hr hrk (he ▸ hvin)
          rw [Redirect.orIn_or hDO hrD (by rw [hgs]; exact hor), Redirect.orIn_or hAO hr hor]
          simp only [opnd,hgs,huv]
          change orIn n (merged n C j k a b) u ∪ orIn n (merged n C j k a b) v = orIn n C u ∪ orIn n C v
          rw [ih u hult (by omega), ih v hvlt (by omega), ite_eq_right hune, ite_eq_right hvne]


lemma merged_tzero (n : ℕ) (C : Circuit) (i j k a b : ℕ) (s : ℕ → Bool)
    (hC : AO2 n C) (hij : i < j) (hjk : j < k) (hk : k < C.gates.length)
    (hiGate : gateAt C i = ⟨GateOp.and,[a,a]⟩)
    (hjGate : gateAt C j = ⟨GateOp.and,[b,b]⟩)
    (hkGate : gateAt C k = ⟨GateOp.or,[n+i,n+j]⟩)
    (huses : ∀ r < C.gates.length, r ≠ k → n+j ∉ (gateAt C r).inputs)
    (hz : tCount n C s = 0)
    (hmono : ∀ u ∈ orIn n C a ∪ orIn n C b, ∀ v ∈ orIn n C a ∪ orIn n C b,
      s u = s v) :
    tCount n (merged n C j k a b) s = 0 := by
  classical
  have hzC := Finset.card_eq_zero.mp hz
  change (Finset.range C.gates.length).filter (IsTwoColour n C s) = ∅ at hzC
  have hnone := Finset.filter_eq_empty_iff.mp hzC
  unfold tCount twoColour
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro r hr hbad
  rw [Finset.mem_range, merged_len] at hr
  obtain ⟨_, hop, ⟨u,hu,hsu⟩, ⟨v,hv,hsv⟩⟩ := hbad
  have hreach := merged_reach n C i j k a b hC hij hjk hk hiGate hjGate hkGate huses
    (n+r) (by omega)
  have hg := merged_gate n C j k a b r hr
  by_cases hrj : r = j
  · subst r
    rw [ite_eq_left rfl] at hreach
    rw [hreach] at hu hv
    have he := hmono u hu v hv
    rw [hsu,hsv] at he
    contradiction
  · by_cases hrk : r = k
    · subst r
      rw [hg,ite_eq_right hrj,ite_eq_left rfl] at hop
      cases hop
    · have hgs : gateAt (merged n C j k a b) r = gateAt C r := by simpa [hrj,hrk] using hg
      rw [hgs] at hop
      rw [ite_eq_right (by omega)] at hreach
      rw [hreach] at hu hv
      exact hnone (Finset.mem_range.mpr hr) ⟨hr,hop,⟨u,hu,hsu⟩,⟨v,hv,hsv⟩⟩

lemma merged_fun (n : ℕ) (C : Circuit) (i j k a b : ℕ)
    (hC : AO2 n C) (hij : i < j) (hjk : j < k) (hk : k < C.gates.length)
    (hiGate : gateAt C i = ⟨GateOp.and,[a,a]⟩)
    (hjGate : gateAt C j = ⟨GateOp.and,[b,b]⟩)
    (hkGate : gateAt C k = ⟨GateOp.or,[n+i,n+j]⟩)
    (huses : ∀ r < C.gates.length, r ≠ k → n+j ∉ (gateAt C r).inputs)
    (hout : C.output < n+C.gates.length) (houtj : C.output ≠ n+j) :
    circuitFun n (merged n C j k a b) = circuitFun n C := by
  funext x
  change wv n (merged n C j k a b) x C.output = wv n C x C.output
  rw [merged_values n C i j k a b hC hij hjk hk hiGate hjGate hkGate huses x C.output hout,
    ite_eq_right houtj]

lemma merged_unused (n : ℕ) (C : Circuit) (i j k a b : ℕ)
    (hC : AO2 n C) (hij : i < j) (hjk : j < k) (hk : k < C.gates.length)
    (hiGate : gateAt C i = ⟨GateOp.and,[a,a]⟩)
    (hjGate : gateAt C j = ⟨GateOp.and,[b,b]⟩)
    (huses : ∀ r < C.gates.length, r ≠ k → n+i ∉ (gateAt C r).inputs) :
    ∀ r < (merged n C j k a b).gates.length,
      n+i ∉ (gateAt (merged n C j k a b) r).inputs := by
  have hi : i < C.gates.length := by omega
  have hj : j < C.gates.length := by omega
  have ha := (hC i hi).2.2 a (by simp [hiGate])
  have hb : b ≠ n+i := by
    intro he
    exact huses j hj (by omega) (by simp [hjGate,he])
  intro r hr
  rw [merged_len] at hr
  rw [merged_gate n C j k a b r hr]
  split_ifs with hrj hrk
  · simp [show n+i ≠ a by omega, Ne.symm hb]
  · simp [show i ≠ j by omega]
  · exact huses r hr hrk

lemma minimum_no_private_buffer_merge (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : ℕ → Bool) (hC : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅) (hz : tCount n C s = 0)
    (hne : ∃ u v, G.Adj u v)
    (hmin : ∀ D : Circuit, IsAO2 n D → circuitFun n D = graphFun G ∅ → tCount n D s = 0 →
      C.size ≤ D.size)
    (i j k a b : ℕ) (hij : i < j) (hjk : j < k) (hk : k < C.gates.length)
    (hiGate : gateAt C i = ⟨GateOp.and,[a,a]⟩)
    (hjGate : gateAt C j = ⟨GateOp.and,[b,b]⟩)
    (hkGate : gateAt C k = ⟨GateOp.or,[n+i,n+j]⟩)
    (huses : ∀ r < C.gates.length, r ≠ k →
      n+i ∉ (gateAt C r).inputs ∧ n+j ∉ (gateAt C r).inputs)
    (houti : C.output ≠ n+i) (houtj : C.output ≠ n+j)
    (hmono : ∀ u ∈ orIn n C a ∪ orIn n C b, ∀ v ∈ orIn n C a ∪ orIn n C b,
      s u = s v) : False := by
  have hAO := ao2_of n C hC
  have hi : i < C.gates.length := by omega
  have hj : j < C.gates.length := by omega
  have ha := (hAO i hi).2.2 a (by simp [hiGate])
  have hb := (hAO j hj).2.2 b (by simp [hjGate])
  have hD := ao2_to n _ (merged_AO n C j k a b hAO hjk (by omega) hb)
  have hout : C.output < n+C.gates.length := by
    obtain ⟨u,v,huv⟩ := hne
    apply out_lt n C (pairInput u v)
    change circuitFun n C (pairInput u v) = true
    rw [hfun]
    exact SemanticFold.graphFun_pair G u v huv
  have hDf := (merged_fun n C i j k a b hAO hij hjk hk hiGate hjGate hkGate
    (fun r hr hrk => (huses r hr hrk).2) hout houtj).trans hfun
  have hDz := merged_tzero n C i j k a b s hAO hij hjk hk hiGate hjGate hkGate
    (fun r hr hrk => (huses r hr hrk).2) hz hmono
  have hDmin : ∀ D : Circuit, IsAO2 n D → tCount n D s = 0 → circuitFun n D = graphFun G ∅ →
      (merged n C j k a b).size ≤ D.size := by
    intro D hD' hDz' hDf'
    have h := hmin D hD' hDf' hDz'
    simpa only [Circuit.size,merged_len] using h
  obtain ⟨r,_,hr,hm⟩ := SemanticFold.least_no_unused G (merged n C j k a b) s
    hD hDz hDf hne hDmin i (by rw [merged_len]; exact hi) (Ne.symm houti)
  exact merged_unused n C i j k a b hAO hij hjk hk hiGate hjGate
    (fun r hr hrk => (huses r hr hrk).1) r hr hm

end PEqualNP.Outside.L_meta_4675.MaskMerge

namespace PEqualNP.Outside.L_meta_4675.MaskMerge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.TwoColour

lemma private_buffer_merge_smaller (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : ℕ → Bool) (hC : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅) (hz : tCount n C s = 0)
    (hne : ∃ u v, G.Adj u v)
    (i j k a b : ℕ) (hij : i < j) (hjk : j < k) (hk : k < C.gates.length)
    (hiGate : gateAt C i = ⟨GateOp.and,[a,a]⟩)
    (hjGate : gateAt C j = ⟨GateOp.and,[b,b]⟩)
    (hkGate : gateAt C k = ⟨GateOp.or,[n+i,n+j]⟩)
    (huses : ∀ r < C.gates.length, r ≠ k →
      n+i ∉ (gateAt C r).inputs ∧ n+j ∉ (gateAt C r).inputs)
    (houti : C.output ≠ n+i) (houtj : C.output ≠ n+j)
    (hmono : ∀ u ∈ orIn n C a ∪ orIn n C b, ∀ v ∈ orIn n C a ∪ orIn n C b,
      s u = s v) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ tCount n D s = 0 ∧
      D.size < C.size := by
  classical
  by_contra hn
  have hmin : ∀ D : Circuit, IsAO2 n D → circuitFun n D = graphFun G ∅ → tCount n D s = 0 →
      C.size ≤ D.size := by
    intro D hD hDf hDz
    by_contra hs
    exact hn ⟨D,hD,hDf,hDz,by omega⟩
  exact minimum_no_private_buffer_merge n G C s hC hfun hz hne hmin
    i j k a b hij hjk hk hiGate hjGate hkGate huses houti houtj hmono

end PEqualNP.Outside.L_meta_4675.MaskMerge

namespace PEqualNP.Outside.L_meta_4675.Centres
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

lemma hit_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (a : Fin n) (Z S : Finset (Fin n))
    (ha : a ∉ S) (hcentres : ∀ z∈Z, G.Adj a z)
    (hhit : ∀ z∈Z, ∃ u∈S, G.Adj z u) : Z.card ≤ S.card := by
  classical
  let f : Fin n → Fin n := fun z => if hz : z∈Z then (hhit z hz).choose else a
  have hf (z : Fin n) (hz : z∈Z) : f z∈S ∧ G.Adj z (f z) := by
    simp only [f,hz,dif_pos]
    exact (hhit z hz).choose_spec
  apply Finset.card_le_card_of_injOn f
  · intro z hz
    exact (hf z hz).1
  · intro z hz z' hz' heq
    by_contra hzz
    have hau : a ≠ f z := by intro he; exact ha (he ▸ (hf z hz).1)
    have hsub : ({z,z'} : Finset (Fin n)) ⊆
        Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj (f z) w) := by
      intro w hw
      simp only [Finset.mem_insert,Finset.mem_singleton] at hw
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      rcases hw with hw | hw
      · subst w
        exact ⟨hcentres z hz,(hf z hz).2.symm⟩
      · subst w
        exact ⟨hcentres z' hz',by rw [heq]; exact (hf z' hz').2.symm⟩
    have hc := (Finset.card_le_card hsub).trans (h4 a (f z) hau)
    rw [Finset.card_pair hzz] at hc
    omega

lemma extension_neighbour {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) (hno : graphFun G ∅ x = false) (z : Fin n)
    (hext : graphFun G ∅ (Function.update x z true) = true) :
    ∃ u, x u = true ∧ G.Adj z u := by
  have hf : ∃ u v, G.Adj u v ∧ Function.update x z true u = true ∧
      Function.update x z true v = true := by simpa [graphFun] using hext
  obtain ⟨u,v,huv,hu,hv⟩ := hf
  by_cases huz : u=z
  · subst u
    have hvz : v≠z := G.ne_of_adj huv.symm
    rw [Function.update_of_ne hvz] at hv
    exact ⟨v,hv,huv⟩
  · rw [Function.update_of_ne huz] at hu
    by_cases hvz : v=z
    · subst v
      exact ⟨u,hu,huv.symm⟩
    · rw [Function.update_of_ne hvz] at hv
      have hyes : graphFun G ∅ x = true := by
        simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
        exact Or.inr ⟨u,v,huv,hu,hv⟩
      rw [hno] at hyes
      cases hyes

lemma independent_payload_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (a : Fin n) (Z : Finset (Fin n))
    (hcentres : ∀ z∈Z, G.Adj a z)
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ u, x u = true → y u = true) → f x = true → f y = true)
    (hclean : ∀ z∈Z, ∀ y, f y = true → y z = true → graphFun G ∅ y = true)
    (x : Fin n → Bool) (hf : f x = true) (ha : x a = false)
    (hno : graphFun G ∅ x = false) :
    Z.card ≤ (Finset.univ.filter (fun u => x u = true)).card := by
  classical
  apply hit_bound G h4 a Z (Finset.univ.filter (fun u => x u = true))
  · simp [ha]
  · exact hcentres
  · intro z hz
    have hxy : ∀ u, x u = true → Function.update x z true u = true := by
      intro u hu
      by_cases huz : u=z
      · subst u; simp
      · rw [Function.update_of_ne huz]; exact hu
    have hext := hclean z hz (Function.update x z true) (hmono x _ hxy hf) (by simp)
    obtain ⟨u,hu,hzu⟩ := extension_neighbour G x hno z hext
    exact ⟨u,by simp [hu],hzu⟩

end PEqualNP.Outside.L_meta_4675.Centres

namespace PEqualNP.Outside.L_meta_4675.Centres
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

lemma proof_trace_charge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (a : Fin n) (Z : Finset (Fin n))
    (hcentres : ∀ z∈Z, G.Adj a z)
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ u, x u = true → y u = true) → f x = true → f y = true)
    (hclean : ∀ z∈Z, ∀ y, f y = true → y z = true → graphFun G ∅ y = true)
    (x : Fin n → Bool) (ha : x a = false) (hno : graphFun G ∅ x = false)
    (T : ℕ → Finset (Fin n)) (r : ℕ) (B : Finset ℕ)
    (hstep : ∀ i, 1 < (T i).card → (∃ j < i, T i ⊆ T j) ∨
      (i∈B ∧ ∃ j < i, ∃ k < i, T i ⊆ T j ∪ T k))
    (hsub : ∀ u∈T r, x u = true)
    (htrace : f (fun u => decide (u∈T r)) = true) :
    Z.card ≤ B.card+1 := by
  classical
  let y : Fin n → Bool := fun u => decide (u∈T r)
  have hya : y a = false := by
    simp only [y,decide_eq_false_iff_not]
    intro har
    have hat := hsub a har
    rw [ha] at hat
    cases hat
  have hyno : graphFun G ∅ y = false := by
    cases he : graphFun G ∅ y
    · rfl
    · obtain ⟨u,v,huv,hu,hv⟩ : ∃u v, G.Adj u v ∧ y u=true ∧ y v=true := by
        simpa [graphFun] using he
      have hyes : graphFun G ∅ x = true := by
        simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
        exact Or.inr ⟨u,v,huv,hsub u (of_decide_eq_true hu),hsub v (of_decide_eq_true hv)⟩
      rw [hno] at hyes
      cases hyes
  have hcent := independent_payload_bound G h4 a Z hcentres f hmono hclean y htrace hya hyno
  have hcount := PairClean.dag_union_bound T {r} B hstep
  have hyset : Finset.univ.filter (fun u => y u=true) = T r := by ext u; simp [y]
  rw [hyset] at hcent
  simpa using hcent.trans (by simpa [Nat.add_comm] using hcount)

end PEqualNP.Outside.L_meta_4675.Centres

namespace PEqualNP.Outside.L_meta_4675.AndTrace
open scoped Classical
open PEqualNP.CleanedNonEdge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.TopForm

noncomputable def support {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (x : Fin n → Bool) (w : ℕ) : Finset (Fin n) :=
  if hw : w<n then
    if x ⟨w,hw⟩ = true then {⟨w,hw⟩} else ∅
  else if hk : w-n<C.gates.length then
    if (gateAt C (w-n)).op = GateOp.and then
      support C hC x (opnd C (w-n) 0) ∪ support C hC x (opnd C (w-n) 1)
    else if wireVal n C (opnd C (w-n) 0) x = true then
      support C hC x (opnd C (w-n) 0)
    else support C hC x (opnd C (w-n) 1)
  else ∅
termination_by w
decreasing_by
  all_goals
    have h0 := Redirect.opnd_lt hC hk (0 : Fin 2)
    have h1 := Redirect.opnd_lt hC hk (1 : Fin 2)
    omega

lemma support_input {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool)
    (w : ℕ) (hw : w<n) : support C hC x w = if x ⟨w,hw⟩ = true then {⟨w,hw⟩} else ∅ := by
  rw [support,dif_pos hw]

lemma support_ge {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool)
    (w : ℕ) (hw : n+C.gates.length≤w) : support C hC x w = ∅ := by
  rw [support,dif_neg (by omega),dif_neg (by omega)]

lemma support_gate {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool)
    (k : ℕ) (hk : k<C.gates.length) :
    support C hC x (n+k) = if (gateAt C k).op = GateOp.and then
      support C hC x (opnd C k 0) ∪ support C hC x (opnd C k 1)
    else if wireVal n C (opnd C k 0) x = true then support C hC x (opnd C k 0)
    else support C hC x (opnd C k 1) := by
  rw [support,dif_neg (by omega)]
  simp only [Nat.add_sub_cancel_left,dif_pos hk]

lemma support_subset {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) :
    ∀ w, ∀ u∈support C hC x w, x u = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro u hu
    by_cases hw : w<n
    · rw [support_input C hC x w hw] at hu
      split_ifs at hu with hx
      · rw [Finset.mem_singleton] at hu
        subst u
        exact hx
      · exact False.elim (Finset.notMem_empty _ hu)
    by_cases hge : n+C.gates.length≤w
    · rw [support_ge C hC x w hge] at hu
      exact False.elim (Finset.notMem_empty _ hu)
    obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
    have hk : k<C.gates.length := by omega
    have h0 := Redirect.opnd_lt hC hk (0 : Fin 2)
    have h1 := Redirect.opnd_lt hC hk (1 : Fin 2)
    rw [support_gate C hC x k hk] at hu
    split_ifs at hu with hop hx
    · rcases Finset.mem_union.mp hu with hu | hu
      · exact ih _ h0 u hu
      · exact ih _ h1 u hu
    · exact ih _ h0 u hu
    · exact ih _ h1 u hu

lemma support_proves {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) :
    ∀ w, wireVal n C w x = true → ∀ y : Fin n → Bool,
      (∀ u∈support C hC x w, y u=true) → wireVal n C w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hx y hy
    by_cases hw : w<n
    · have hxi : x ⟨w,hw⟩ = true := by
        simpa only [Redirect.wireVal_input C ⟨w,hw⟩ x] using hx
      have hmem : (⟨w,hw⟩ : Fin n) ∈ support C hC x w := by
        rw [support_input C hC x w hw,if_pos hxi]
        exact Finset.mem_singleton_self _
      simpa only [Redirect.wireVal_input C ⟨w,hw⟩ y] using hy ⟨w,hw⟩ hmem
    by_cases hge : n+C.gates.length≤w
    · rw [Redirect.wireVal_ge C hge x] at hx
      cases hx
    obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
    have hk : k<C.gates.length := by omega
    have h0 := Redirect.opnd_lt hC hk (0 : Fin 2)
    have h1 := Redirect.opnd_lt hC hk (1 : Fin 2)
    rw [support_gate C hC x k hk] at hy
    by_cases hop : (gateAt C k).op = GateOp.and
    · rw [if_pos hop] at hy
      rw [Redirect.wireVal_and hC hk hop x] at hx
      rw [Redirect.wireVal_and hC hk hop y]
      simp only [Bool.and_eq_true] at hx ⊢
      exact ⟨ih _ h0 hx.1 y (fun u hu => hy u (Finset.mem_union_left _ hu)),
        ih _ h1 hx.2 y (fun u hu => hy u (Finset.mem_union_right _ hu))⟩
    · have hor : (gateAt C k).op = GateOp.or := by
        rcases (Lift.ao2_of n C hC k hk).1 with h | h
        · exact False.elim (hop h)
        · exact h
      rw [if_neg hop] at hy
      rw [Redirect.wireVal_or hC hk hor x] at hx
      rw [Redirect.wireVal_or hC hk hor y]
      simp only [Bool.or_eq_true] at hx ⊢
      by_cases hv0 : wireVal n C (opnd C k 0) x = true
      · rw [if_pos hv0] at hy
        exact Or.inl (ih _ h0 hv0 y hy)
      · rw [if_neg hv0] at hy
        have hv1 : wireVal n C (opnd C k 1) x = true := hx.resolve_left hv0
        exact Or.inr (ih _ h1 hv1 y hy)

noncomputable def andWires (n : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range (n+C.gates.length)).filter (fun w => n≤w ∧ (gateAt C (w-n)).op = GateOp.and)

lemma support_step {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool)
    (w : ℕ) (hbig : 1 < (support C hC x w).card) :
    (∃ v < w, support C hC x w ⊆ support C hC x v) ∨
    (w∈andWires n C ∧ ∃ u < w, ∃ v < w,
      support C hC x w ⊆ support C hC x u ∪ support C hC x v) := by
  by_cases hw : w<n
  · rw [support_input C hC x w hw] at hbig
    split_ifs at hbig <;> simp at hbig
  by_cases hge : n+C.gates.length≤w
  · rw [support_ge C hC x w hge] at hbig
    simp at hbig
  obtain ⟨k,rfl⟩ : ∃ k, w=n+k := ⟨w-n,by omega⟩
  have hk : k<C.gates.length := by omega
  have h0 := Redirect.opnd_lt hC hk (0 : Fin 2)
  have h1 := Redirect.opnd_lt hC hk (1 : Fin 2)
  by_cases hop : (gateAt C k).op = GateOp.and
  · right
    refine ⟨?_,opnd C k 0,h0,opnd C k 1,h1,?_⟩
    · simp [andWires,hop,hk]
    · rw [support_gate C hC x k hk,if_pos hop]
  · left
    by_cases hv0 : wireVal n C (opnd C k 0) x = true
    · refine ⟨opnd C k 0,h0,?_⟩
      rw [support_gate C hC x k hk,if_neg hop,if_pos hv0]
    · refine ⟨opnd C k 1,h1,?_⟩
      rw [support_gate C hC x k hk,if_neg hop,if_neg hv0]

lemma support_card {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (w : ℕ) :
    (support C hC x w).card ≤ (andWires n C).card+1 := by
  have h := PairClean.dag_union_bound (support C hC x) {w} (andWires n C)
    (support_step C hC x)
  simpa [Nat.add_comm] using h

lemma small_witness {n : ℕ} (C : Circuit) (hC : IsAO2 n C)
    (x : Fin n → Bool) (w : ℕ) (hx : wireVal n C w x = true) :
    ∃ S : Finset (Fin n), (∀ u∈S, x u=true) ∧ S.card≤(andWires n C).card+1 ∧
      wireVal n C w (fun u => decide (u∈S)) = true := by
  refine ⟨support C hC x w,support_subset C hC x w,support_card C hC x w,?_⟩
  exact support_proves C hC x w hx _ (fun u hu => decide_eq_true hu)

end PEqualNP.Outside.L_meta_4675.AndTrace

namespace PEqualNP.Outside.L_meta_4675.StructuralPrefix

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount

lemma clean_and_unit_adj {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and)
    (hclean : ∀ a b : Fin n, ¬ G.Adj a b → gateVal n C j (pairInput a b) = false)
    {a b : Fin n}
    (ha : wireVal n C (opnd C j 0) (unitInput a) = true)
    (hb : wireVal n C (opnd C j 1) (unitInput b) = true) : G.Adj a b := by
  have ha' : wireVal n C (opnd C j 0) (pairInput a b) = true := by
    apply wire_mono hAO (unitInput a) (pairInput a b) _ _ ha
    intro v hv
    simp only [unitInput, decide_eq_true_eq] at hv
    subst v
    simp [pairInput]
  have hb' : wireVal n C (opnd C j 1) (pairInput a b) = true := by
    apply wire_mono hAO (unitInput b) (pairInput a b) _ _ hb
    intro v hv
    simp only [unitInput, decide_eq_true_eq] at hv
    subst v
    simp [pairInput]
  have hg : gateVal n C j (pairInput a b) = true := by
    change wireVal n C (n + j) (pairInput a b) = true
    rw [wireVal_and hAO hj hand, ha', hb']
    rfl
  by_contra hab
  have hf := hclean a b hab
  rw [hf] at hg
  contradiction

lemma clean_left_units_one_colour {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and)
    (hclean : ∀ a b : Fin n, ¬ G.Adj a b → gateVal n C j (pairInput a b) = false)
    (col : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → col a ≠ col b)
    {a a' b : Fin n}
    (ha : wireVal n C (opnd C j 0) (unitInput a) = true)
    (ha' : wireVal n C (opnd C j 0) (unitInput a') = true)
    (hb : wireVal n C (opnd C j 1) (unitInput b) = true) : col a = col a' := by
  have h1 := hcol a b (clean_and_unit_adj G hAO hj hand hclean ha hb)
  have h2 := hcol a' b (clean_and_unit_adj G hAO hj hand hclean ha' hb)
  cases hca : col a <;> cases hca' : col a' <;> cases hcb : col b <;> simp_all

lemma mixed_left_forces_empty_right_units {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and)
    (hclean : ∀ a b : Fin n, ¬ G.Adj a b → gateVal n C j (pairInput a b) = false)
    (col : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → col a ≠ col b)
    {a a' : Fin n} (haa' : col a ≠ col a')
    (ha : wireVal n C (opnd C j 0) (unitInput a) = true)
    (ha' : wireVal n C (opnd C j 0) (unitInput a') = true) :
    ∀ b : Fin n, wireVal n C (opnd C j 1) (unitInput b) = false := by
  intro b
  cases hb : wireVal n C (opnd C j 1) (unitInput b) with
  | false => rfl
  | true => exact (haa' (clean_left_units_one_colour G hAO hj hand hclean col hcol ha ha' hb)).elim


lemma mixed_left_forces_empty_right_orIn {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and)
    (hclean : ∀ a b : Fin n, ¬ G.Adj a b → gateVal n C j (pairInput a b) = false)
    (col : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → col a ≠ col b)
    {a a' : Fin n} (haa' : col a ≠ col a')
    (ha : wireVal n C (opnd C j 0) (unitInput a) = true)
    (ha' : wireVal n C (opnd C j 0) (unitInput a') = true) :
    orIn n C (opnd C j 1) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  have hv := Redirect.wireVal_true_of_mem_orIn hAO
    (x := unitInput b) (i := b) (by simp [unitInput]) (opnd C j 1) hb
  have hf := mixed_left_forces_empty_right_units G hAO hj hand hclean col hcol haa' ha ha' b
  rw [hf] at hv
  contradiction

lemma singleton_masking_boundary {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C) {j g : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and)
    (hclean : ∀ a b : Fin n, ¬ G.Adj a b → gateVal n C j (pairInput a b) = false)
    (col : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → col a ≠ col b)
    {a p : Fin n} (hap : col a ≠ col p)
    (hga : gateVal n C g (unitInput a) = true)
    (hreach : OrReaches n C (opnd C j 0) g)
    (hp : p ∈ orIn n C (opnd C j 0)) :
    orIn n C (opnd C j 1) = ∅ := by
  apply mixed_left_forces_empty_right_orIn G hAO hj hand hclean col hcol hap
  · exact Redirect.wireVal_of_orReaches hAO (opnd C j 0) g hreach (unitInput a) hga
  · exact Redirect.wireVal_true_of_mem_orIn hAO
      (x := unitInput p) (i := p) (by simp [unitInput]) (opnd C j 0) hp


lemma gate_units_one_colour_of_left_reach {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C) {j g : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and)
    (hclean : ∀ a b : Fin n, ¬ G.Adj a b → gateVal n C j (pairInput a b) = false)
    (col : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → col a ≠ col b)
    (hreach : OrReaches n C (opnd C j 0) g)
    (hother : (orIn n C (opnd C j 1)).Nonempty)
    {a a' : Fin n}
    (ha : gateVal n C g (unitInput a) = true)
    (ha' : gateVal n C g (unitInput a') = true) : col a = col a' := by
  obtain ⟨b, hb⟩ := hother
  apply clean_left_units_one_colour G hAO hj hand hclean col hcol
  · exact Redirect.wireVal_of_orReaches hAO (opnd C j 0) g hreach (unitInput a) ha
  · exact Redirect.wireVal_of_orReaches hAO (opnd C j 0) g hreach (unitInput a') ha'
  · exact Redirect.wireVal_true_of_mem_orIn hAO
      (x := unitInput b) (i := b) (by simp [unitInput]) (opnd C j 1) hb

lemma gate_units_one_colour_of_right_reach {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C) {j g : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and)
    (hclean : ∀ a b : Fin n, ¬ G.Adj a b → gateVal n C j (pairInput a b) = false)
    (col : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → col a ≠ col b)
    (hreach : OrReaches n C (opnd C j 1) g)
    (hother : (orIn n C (opnd C j 0)).Nonempty)
    {a a' : Fin n}
    (ha : gateVal n C g (unitInput a) = true)
    (ha' : gateVal n C g (unitInput a') = true) : col a = col a' := by
  obtain ⟨b, hb⟩ := hother
  have h0 := Redirect.wireVal_true_of_mem_orIn hAO
    (x := unitInput b) (i := b) (by simp [unitInput]) (opnd C j 0) hb
  have h1 := Redirect.wireVal_of_orReaches hAO (opnd C j 1) g hreach (unitInput a) ha
  have h2 := Redirect.wireVal_of_orReaches hAO (opnd C j 1) g hreach (unitInput a') ha'
  have hc1 := hcol b a (clean_and_unit_adj G hAO hj hand hclean h0 h1)
  have hc2 := hcol b a' (clean_and_unit_adj G hAO hj hand hclean h0 h2)
  cases hca : col a <;> cases hca' : col a' <;> cases hcb : col b <;> simp_all


lemma belowF_pair_clean {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {j : ℕ} (hbelow : BelowF G C j) :
    ∀ a b : Fin n, ¬ G.Adj a b → gateVal n C j (pairInput a b) = false := by
  intro a b hab
  cases hg : gateVal n C j (pairInput a b) with
  | false => rfl
  | true =>
    have hf := hbelow (pairInput a b) hg
    simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq] at hf
    rcases hf with ⟨v, hv, _⟩ | ⟨u, v, huv, hu, hv⟩
    · exact (Finset.notMem_empty v hv).elim
    · simp only [pairInput, decide_eq_true_eq] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact (G.ne_of_adj huv rfl).elim
      · exact (hab huv).elim
      · exact (hab huv.symm).elim
      · exact (G.ne_of_adj huv rfl).elim

lemma lam_units_one_colour {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C)
    (col : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → col a ≠ col b)
    {g : ℕ} (hg : g ∈ lam G C) {a a' : Fin n}
    (ha : gateVal n C g (unitInput a) = true)
    (ha' : gateVal n C g (unitInput a') = true) : col a = col a' := by
  obtain ⟨_, _, _, j, hj, b, hcard, hreach⟩ := Finset.mem_filter.mp hg
  have hj' : j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧ BelowF G C j := by
    simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using hj
  have hclean := belowF_pair_clean G hj'.2.2
  have hn : (side (n := n) C j (1 - b)).Nonempty :=
    Finset.card_pos.mp (by omega)
  fin_cases b
  · apply gate_units_one_colour_of_left_reach G hAO hj'.1 hj'.2.1 hclean col hcol hreach
      (by simpa [side] using hn) ha ha'
  · apply gate_units_one_colour_of_right_reach G hAO hj'.1 hj'.2.1 hclean col hcol hreach
      (by simpa [side] using hn) ha ha'

lemma semantic_mixed_or_mem_paid {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C)
    (col : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → col a ≠ col b)
    {g : ℕ} (hg : g < C.gates.length) (hor : (gateAt C g).op = GateOp.or)
    {a a' : Fin n} (haa' : col a ≠ col a')
    (ha : gateVal n C g (unitInput a) = true)
    (ha' : gateVal n C g (unitInput a') = true) :
    g ∈ orN G C \ lam G C := by
  apply Finset.mem_sdiff.mpr
  constructor
  · have hnbelow : ¬ BelowF G C g := by
      intro hbelow
      have hf := hbelow (unitInput a) ha
      simp [graphFun, unitInput] at hf
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hg (And.intro hor hnbelow)
  · intro hlam
    exact haa' (lam_units_one_colour G hAO col hcol hlam ha ha')

lemma semantic_mixed_or_count {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C)
    (col : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → col a ≠ col b)
    (M : Finset ℕ)
    (hM : ∀ g ∈ M, g < C.gates.length ∧ (gateAt C g).op = GateOp.or ∧
      ∃ a a' : Fin n, col a ≠ col a' ∧ gateVal n C g (unitInput a) = true ∧
        gateVal n C g (unitInput a') = true) :
    M.card ≤ (orN G C \ lam G C).card := by
  apply Finset.card_le_card
  intro g hg
  obtain ⟨hlen, hor, a, a', haa', ha, ha'⟩ := hM g hg
  exact semantic_mixed_or_mem_paid G hAO col hcol hlen hor haa' ha ha'


end PEqualNP.Outside.L_meta_4675.StructuralPrefix
