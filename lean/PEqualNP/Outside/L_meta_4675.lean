import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675

lemma cover_of_row_bound (p l : ℕ) (E : Finset (Fin p × Fin l)) (s : ℕ)
    (h : E.card + (E.image Prod.fst).card ≤ s + 1) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ s + 1 := by
  classical
  let f : Fin p ↪ Fin (p + l) :=
    ⟨Fin.castAdd l, fun _ _ h => Fin.ext (congrArg (fun z : Fin (p + l) => z.val) h)⟩
  refine ⟨(E.image Prod.fst).map f, ?_, ?_⟩
  · intro a b hab
    left
    exact Finset.mem_map.mpr ⟨a, Finset.mem_image.mpr ⟨(a, b), hab, rfl⟩, rfl⟩
  · simpa using h

lemma cover_of_column_bound (p l : ℕ) (E : Finset (Fin p × Fin l)) (s : ℕ)
    (h : E.card + (E.image Prod.snd).card ≤ s + 1) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ s + 1 := by
  classical
  let f : Fin l ↪ Fin (p + l) :=
    ⟨Fin.natAdd p, fun _ _ h =>
      Fin.ext (Nat.add_left_cancel (congrArg (fun z : Fin (p + l) => z.val) h))⟩
  refine ⟨(E.image Prod.snd).map f, ?_, ?_⟩
  · intro a b hab
    right
    exact Finset.mem_map.mpr ⟨b, Finset.mem_image.mpr ⟨(a, b), hab, rfl⟩, rfl⟩
  · simpa using h

lemma cover_of_small_side_bound (p l : ℕ) (E : Finset (Fin p × Fin l)) (s : ℕ)
    (h : E.card + min p l ≤ s + 1) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ s + 1 := by
  classical
  by_cases hp : p ≤ l
  · apply cover_of_row_bound
    have hc : (E.image Prod.fst).card ≤ p := by
      simpa using Finset.card_le_univ (E.image Prod.fst)
    have hm : min p l = p := Nat.min_eq_left hp
    omega
  · apply cover_of_column_bound
    have hc : (E.image Prod.snd).card ≤ l := by
      simpa using Finset.card_le_univ (E.image Prod.snd)
    have hl : min p l = l := Nat.min_eq_right (by omega)
    omega

lemma empty_edge_cover (p l s : ℕ) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ (∅ : Finset (Fin p × Fin l)) →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      (∅ : Finset (Fin p × Fin l)).card + S.card ≤ s + 1 := by
  exact ⟨∅, by simp, by simp⟩

end PEqualNP.Outside.L_meta_4675
namespace PEqualNP.Outside.L_meta_4675_aux

lemma rectangle_card_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hrect : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_cases hA : A.card ≤ 1
  · exact Or.inl hA
  · right
    obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    apply Finset.card_le_one.mpr
    intro b hb b' hb'
    by_contra hbb'
    exact hC4 a a' b b' haa' hbb'
      ⟨hrect a ha b hb, hrect a ha b' hb', hrect a' ha' b hb, hrect a' ha' b' hb'⟩

lemma rectangle_center {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hrect : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    ∃ c : Fin (p + l), ∀ a ∈ A, ∀ b ∈ B,
      Fin.castAdd l a = c ∨ Fin.natAdd p b = c := by
  rcases rectangle_card_one E hC4 A B hrect with h | h
  · obtain ⟨a, ha⟩ := hA
    refine ⟨Fin.castAdd l a, ?_⟩
    intro a' ha' b hb
    exact Or.inl (congrArg (Fin.castAdd l) (Finset.card_le_one.mp h a' ha' a ha))
  · obtain ⟨b, hb⟩ := hB
    refine ⟨Fin.natAdd p b, ?_⟩
    intro a ha b' hb'
    exact Or.inr (congrArg (Fin.natAdd p) (Finset.card_le_one.mp h b' hb' b hb))

lemma rectangle_card_eq_sum {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hrect : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    (A ×ˢ B).card + 1 = A.card + B.card := by
  have ha := Finset.card_pos.mpr hA
  have hb := Finset.card_pos.mpr hB
  rw [Finset.card_product]
  rcases rectangle_card_one E hC4 A B hrect with h | h
  · have he : A.card = 1 := by omega
    simp [he, Nat.add_comm]
  · have he : B.card = 1 := by omega
    simp [he]

lemma rectangle_family_cover {p l m : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Fin m → Finset (Fin p)) (B : Fin m → Finset (Fin l))
    (hA : ∀ i, (A i).Nonempty) (hB : ∀ i, (B i).Nonempty)
    (hrect : ∀ i a, a ∈ A i → ∀ b, b ∈ B i → (a, b) ∈ E)
    (hcover : ∀ a b, (a, b) ∈ E → ∃ i, a ∈ A i ∧ b ∈ B i) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      S.card ≤ m ∧
      E.card + S.card ≤ ∑ i, ((A i).card + (B i).card) := by
  classical
  have hc : ∀ i, ∃ c : Fin (p + l), ∀ a ∈ A i, ∀ b ∈ B i,
      Fin.castAdd l a = c ∨ Fin.natAdd p b = c :=
    fun i => rectangle_center E hC4 (A i) (B i) (hA i) (hB i) (hrect i)
  choose c hc using hc
  let S := Finset.univ.image c
  have hS : S.card ≤ m := by
    exact (Finset.card_image_le).trans (by simp)
  have hE : E.card ≤ ∑ i, (A i ×ˢ B i).card := by
    calc
      E.card ≤ (Finset.univ.biUnion fun i => A i ×ˢ B i).card := by
        apply Finset.card_le_card
        intro e he
        obtain ⟨i, hiA, hiB⟩ := hcover e.1 e.2 he
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_product.mpr ⟨hiA, hiB⟩⟩
      _ ≤ ∑ i, (A i ×ˢ B i).card := Finset.card_biUnion_le
  have heq : (∑ i, (A i ×ˢ B i).card) + m =
      ∑ i, ((A i).card + (B i).card) := by
    calc
      _ = ∑ i : Fin m, ((A i ×ˢ B i).card + 1) := by simp [Finset.sum_add_distrib]
      _ = _ := Finset.sum_congr rfl (fun i _ =>
        rectangle_card_eq_sum E hC4 (A i) (B i) (hA i) (hB i) (hrect i))
  refine ⟨S, ?_, hS, ?_⟩
  · intro a b he
    obtain ⟨i, hiA, hiB⟩ := hcover a b he
    have hci : c i ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rcases hc i a hiA b hiB with h | h
    · exact Or.inl (h.symm ▸ hci)
    · exact Or.inr (h.symm ▸ hci)
  · omega

end PEqualNP.Outside.L_meta_4675_aux
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

namespace PEqualNP.Outside.L_meta_4675.Star

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma row_incident_card (p l : ℕ) (E : Finset (Fin p × Fin l)) (a0 : Fin p)
    (hrow : ∀ e ∈ E, e.1 = a0) (hne : E.Nonempty) :
    (E.biUnion fun e => {Fin.castAdd l e.1, Fin.natAdd p e.2}).card = E.card + 1 := by
  classical
  have hsep : ∀ b : Fin l, (Fin.castAdd l a0 : Fin (p + l)) ≠ Fin.natAdd p b := by
    intro b h
    have hh : a0.val = p + b.val := congrArg Fin.val h
    have := a0.isLt
    omega
  have hinj : Set.InjOn (fun e : Fin p × Fin l => Fin.natAdd p e.2) (↑E : Set _) := by
    intro e he f hf h
    apply Prod.ext
    · exact (hrow e he).trans (hrow f hf).symm
    · simpa using h
  have hcard : (E.image fun e => Fin.natAdd p e.2).card = E.card :=
    Finset.card_image_of_injOn hinj
  have hnot : Fin.castAdd l a0 ∉ E.image (fun e => Fin.natAdd p e.2) := by
    rintro h
    obtain ⟨e, _, he⟩ := Finset.mem_image.mp h
    exact hsep e.2 he.symm
  have heq : E.biUnion (fun e => {Fin.castAdd l e.1, Fin.natAdd p e.2}) =
      insert (Fin.castAdd l a0) (E.image fun e => Fin.natAdd p e.2) := by
    ext i
    constructor
    · intro hi
      obtain ⟨e, he, hi⟩ := Finset.mem_biUnion.mp hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with hi | hi
      · exact Finset.mem_insert.mpr (Or.inl (hi.trans (congrArg (Fin.castAdd l) (hrow e he))))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨e, he, hi.symm⟩))
    · intro hi
      rcases Finset.mem_insert.mp hi with hi | hi
      · obtain ⟨e, he⟩ := hne
        apply Finset.mem_biUnion.mpr
        refine ⟨e, he, ?_⟩
        simp [hi, hrow e he]
      · obtain ⟨e, he, hi⟩ := Finset.mem_image.mp hi
        apply Finset.mem_biUnion.mpr
        refine ⟨e, he, ?_⟩
        simp [← hi]
  rw [heq, Finset.card_insert_of_notMem hnot, hcard]

lemma row_bound (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit) (a0 : Fin p)
    (hrow : ∀ e ∈ E, e.1 = a0)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hfun : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  classical
  by_cases hempty : E = ∅
  · subst E
    exact ⟨∅, by simp, by simp⟩
  · refine ⟨{Fin.castAdd l a0}, ?_, ?_⟩
    · intro a b hab
      left
      exact Finset.mem_singleton.mpr (congrArg (Fin.castAdd l) (hrow (a, b) hab))
    · have hcard := Support.incident_card_le p l E C hfan hfun
      rw [row_incident_card p l E a0 hrow (Finset.nonempty_iff_ne_empty.mpr hempty)] at hcard
      simpa using hcard

lemma column_incident_card (p l : ℕ) (E : Finset (Fin p × Fin l)) (b0 : Fin l)
    (hcol : ∀ e ∈ E, e.2 = b0) (hne : E.Nonempty) :
    (E.biUnion fun e => {Fin.castAdd l e.1, Fin.natAdd p e.2}).card = E.card + 1 := by
  classical
  have hsep : ∀ a : Fin p, (Fin.natAdd p b0 : Fin (p + l)) ≠ Fin.castAdd l a := by
    intro a h
    have hh : p + b0.val = a.val := congrArg Fin.val h
    have := a.isLt
    omega
  have hinj : Set.InjOn (fun e : Fin p × Fin l => Fin.castAdd l e.1) (↑E : Set _) := by
    intro e he f hf h
    apply Prod.ext
    · simpa using h
    · exact (hcol e he).trans (hcol f hf).symm
  have hcard : (E.image fun e => Fin.castAdd l e.1).card = E.card :=
    Finset.card_image_of_injOn hinj
  have hnot : Fin.natAdd p b0 ∉ E.image (fun e => Fin.castAdd l e.1) := by
    rintro h
    obtain ⟨e, _, he⟩ := Finset.mem_image.mp h
    exact hsep e.1 he.symm
  have heq : E.biUnion (fun e => {Fin.castAdd l e.1, Fin.natAdd p e.2}) =
      insert (Fin.natAdd p b0) (E.image fun e => Fin.castAdd l e.1) := by
    ext i
    constructor
    · intro hi
      obtain ⟨e, he, hi⟩ := Finset.mem_biUnion.mp hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with hi | hi
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨e, he, hi.symm⟩))
      · exact Finset.mem_insert.mpr (Or.inl (hi.trans (congrArg (Fin.natAdd p) (hcol e he))))
    · intro hi
      rcases Finset.mem_insert.mp hi with hi | hi
      · obtain ⟨e, he⟩ := hne
        apply Finset.mem_biUnion.mpr
        refine ⟨e, he, ?_⟩
        simp [hi, hcol e he]
      · obtain ⟨e, he, hi⟩ := Finset.mem_image.mp hi
        apply Finset.mem_biUnion.mpr
        refine ⟨e, he, ?_⟩
        simp [← hi]
  rw [heq, Finset.card_insert_of_notMem hnot, hcard]

lemma column_bound (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit) (b0 : Fin l)
    (hcol : ∀ e ∈ E, e.2 = b0)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hfun : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  classical
  by_cases hempty : E = ∅
  · subst E
    exact ⟨∅, by simp, by simp⟩
  · refine ⟨{Fin.natAdd p b0}, ?_, ?_⟩
    · intro a b hab
      right
      exact Finset.mem_singleton.mpr (congrArg (Fin.natAdd p) (hcol (a, b) hab))
    · have hcard := Support.incident_card_le p l E C hfan hfun
      rw [column_incident_card p l E b0 hcol (Finset.nonempty_iff_ne_empty.mpr hempty)] at hcard
      simpa using hcard

end PEqualNP.Outside.L_meta_4675.Star
namespace PEqualNP.Outside.L_meta_4675.NormalizationFinal

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.TwoColour

lemma no_twoColour_of_count_zero (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hz : tCount n C s = 0) (g : ℕ) : ¬ IsTwoColour n C s g := by
  intro hg
  have he : twoColour n C s = ∅ := Finset.card_eq_zero.mp hz
  have hm : g ∈ twoColour n C s :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.1, hg⟩
  rw [he] at hm
  simp at hm

lemma orIn_same_colour (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hz : tCount n C s = 0) (g : ℕ) (hg : g < C.gates.length)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = GateOp.or)
    (i j : Fin n) (hi : i ∈ orIn n C (n + g)) (hj : j ∈ orIn n C (n + g)) :
    s i = s j := by
  cases hci : s i <;> cases hcj : s j
  · rfl
  · exact False.elim (no_twoColour_of_count_zero n C s hz g
      ⟨hg, hop, ⟨i, hi, hci⟩, ⟨j, hj, hcj⟩⟩)
  · exact False.elim (no_twoColour_of_count_zero n C s hz g
      ⟨hg, hop, ⟨j, hj, hcj⟩, ⟨i, hi, hci⟩⟩)
  · rfl

lemma orIn_one_colour (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hz : tCount n C s = 0) (g : ℕ) (hg : g < C.gates.length)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = GateOp.or) :
    (∀ i ∈ orIn n C (n + g), s i = false) ∨
      (∀ i ∈ orIn n C (n + g), s i = true) := by
  by_cases h : ∃ i ∈ orIn n C (n + g), s i = true
  · obtain ⟨i, hi, hci⟩ := h
    right
    intro j hj
    exact (orIn_same_colour n C s hz g hg hop j i hj hi).trans hci
  · left
    intro i hi
    cases hci : s i
    · rfl
    · exact False.elim (h ⟨i, hi, hci⟩)


open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wireStep_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl wireStep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wireStep_prefix (gs : List Gate) (acc : List Bool) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl wireStep acc).getD w false = acc.getD w false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hw' : w < (wireStep acc g).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (wireStep acc g) hw']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_left hw]

lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

lemma wireValue_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    PEqualNP.BlindGate.wireValue C n x w = x ⟨w, hw⟩ := by
  unfold PEqualNP.BlindGate.wireValue Circuit.wires
  have hw' : w < (List.ofFn x).length := by simp [hw]
  have h1 := foldl_wireStep_prefix C.gates (List.ofFn x) w hw'
  change (C.gates.foldl wireStep (List.ofFn x)).getD w false = x ⟨w, hw⟩
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw']
  simp

lemma wireValue_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) (hRB : ReadsBack n C) :
    PEqualNP.BlindGate.wireValue C n x (n + k) =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun u => PEqualNP.BlindGate.wireValue C n x u) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take k).foldl wireStep (List.ofFn x) with hacc
  have hacc_len : acc.length = n + k := by
    rw [hacc, foldl_wireStep_length, List.length_ofFn, List.length_take]
    omega
  have hpref : ∀ u < n + k, PEqualNP.BlindGate.wireValue C n x u = acc.getD u false := by
    intro u hu
    unfold PEqualNP.BlindGate.wireValue Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD u false = acc.getD u false
    conv_lhs => rw [← List.take_append_drop k C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_wireStep_prefix (C.gates.drop k) acc u (by omega)
  have hval : PEqualNP.BlindGate.wireValue C n x (n + k) =
      C.gates[k].op.eval (C.gates[k].inputs.map fun u => acc.getD u false) := by
    unfold PEqualNP.BlindGate.wireValue Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD (n + k) false = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : n + k < (wireStep acc C.gates[k]).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_wireStep_prefix (C.gates.drop (k + 1)) (wireStep acc C.gates[k]) (n + k) hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_right (by omega : acc.length ≤ n + k),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval, gateAt_eq_getElem C k hk]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [← gateAt_eq_getElem C k hk] at hu
  exact (hpref u (hRB k hk u hu)).symm

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

lemma orSets_length (n : ℕ) (C : Circuit) :
    (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := by
  unfold PEqualNP.CleanedNonEdge.orSets
  rw [orSets_len]; simp

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.CleanedNonEdge.orStep n (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
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
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
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
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
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
    · have e0 : (PEqualNP.CleanedNonEdge.orStep n
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD (w - n) []) := by
  have h := orSets_char n C.gates x k
  unfold PEqualNP.CleanedNonEdge.orSets gateAt
  rw [h]
  constructor
  · rintro ⟨_, h3⟩; exact h3
  · intro h3; exact ⟨hk, h3⟩

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ k < C.gates.length ∧
      (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ PEqualNP.CleanedNonEdge.OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold PEqualNP.CleanedNonEdge.OrReaches PEqualNP.CleanedNonEdge.orSets gateAt
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

lemma orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) j :=
  (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩

lemma orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C i g) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g :=
  (orReaches_iff n C j g).mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, h⟩⟩

lemma orIn_mem_filter {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  exact ⟨fun h => ((orIn_mem_filter _ _ _ _).1 h).2,
    fun h => (orIn_mem_filter _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma orIn_self (n : ℕ) (C : Circuit) (i : Fin n) : i ∈ PEqualNP.TopForm.orIn n C i :=
  (mem_orIn n C i i).mpr (Or.inl rfl)

lemma orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ PEqualNP.TopForm.orIn n C i) : a ∈ PEqualNP.TopForm.orIn n C (n + j) := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩

lemma orReaches_bound (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → n + g ≤ w ∧ w < n + C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp hr
    rcases h3 with h3 | ⟨_, i, _, hlt, hri⟩
    · omega
    · have := ih i hlt hri
      omega

lemma true_wire_source (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (x : Fin n → Bool) :
    ∀ w < n + C.gates.length, PEqualNP.BlindGate.wireValue C n x w = true →
      (∃ i ∈ orIn n C w, x i = true) ∨
      (∃ g < C.gates.length, OrReaches n C w g ∧
        (gateAt C g).op = GateOp.and ∧
        PEqualNP.BlindGate.wireValue C n x (n + g) = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hv
    by_cases hwinput : w < n
    · left
      refine ⟨⟨w, hwinput⟩, orIn_self n C ⟨w, hwinput⟩, ?_⟩
      rwa [wireValue_input n C x w hwinput] at hv
    · obtain ⟨g, rfl⟩ : ∃ g, w = n + g := ⟨w - n, by omega⟩
      have hg : g < C.gates.length := by omega
      have hmem : gateAt C g ∈ C.gates := by
        rw [gateAt_eq_getElem C g hg]
        exact List.getElem_mem hg
      rcases hAO.1 (gateAt C g) hmem with hop | hop
      · exact Or.inr ⟨g, hg, orReaches_self n C g hg, hop, hv⟩
      · rw [wireValue_gate n C x g hg hAO.2.1, hop] at hv
        have hor : ∃ u ∈ (gateAt C g).inputs,
            PEqualNP.BlindGate.wireValue C n x u = true := by
          simpa [GateOp.eval] using hv
        obtain ⟨u, hu, hvu⟩ := hor
        have hul : u < n + g := hAO.2.1 g hg u hu
        rcases ih u hul (by omega) hvu with ⟨i, hi, hxi⟩ | ⟨k, hk, hr, hopk, hvk⟩
        · exact Or.inl ⟨i, orIn_up n C g u i hg hop hu hul hi, hxi⟩
        · exact Or.inr ⟨k, hk, orReaches_step n C g u k hg hop hu hul hr, hopk, hvk⟩

lemma singleton_true_source (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (w : ℕ) (hw : w < n + C.gates.length) (i : Fin n)
    (hv : PEqualNP.BlindGate.wireValue C n (fun j => decide (j = i)) w = true) :
    i ∈ orIn n C w ∨
      ∃ g < C.gates.length, OrReaches n C w g ∧
        (gateAt C g).op = GateOp.and ∧
        PEqualNP.BlindGate.wireValue C n (fun j => decide (j = i)) (n + g) = true := by
  rcases true_wire_source n C hAO (fun j => decide (j = i)) w hw hv with
    ⟨j, hj, hji⟩ | h
  · have he : j = i := of_decide_eq_true hji
    exact Or.inl (he ▸ hj)
  · exact Or.inr h

lemma mixed_singletons_have_and (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hAO : IsAO2 n C) (hz : tCount n C s = 0)
    (g : ℕ) (hg : g < C.gates.length) (hop : (gateAt C g).op = GateOp.or)
    (i j : Fin n) (hij : s i ≠ s j)
    (hi : PEqualNP.BlindGate.wireValue C n (fun k => decide (k = i)) (n + g) = true)
    (hj : PEqualNP.BlindGate.wireValue C n (fun k => decide (k = j)) (n + g) = true) :
    ∃ k < C.gates.length, OrReaches n C (n + g) k ∧
      (gateAt C k).op = GateOp.and ∧
      (PEqualNP.BlindGate.wireValue C n (fun a => decide (a = i)) (n + k) = true ∨
       PEqualNP.BlindGate.wireValue C n (fun a => decide (a = j)) (n + k) = true) := by
  rcases singleton_true_source n C hAO (n + g) (by omega) i hi with
    hi | ⟨k, hk, hr, hand, hv⟩
  · rcases singleton_true_source n C hAO (n + g) (by omega) j hj with
      hj | ⟨k, hk, hr, hand, hv⟩
    · exact False.elim (hij (orIn_same_colour n C s hz g hg hop i j hi hj))
    · exact ⟨k, hk, hr, hand, Or.inr hv⟩
  · exact ⟨k, hk, hr, hand, Or.inl hv⟩

lemma mixed_singletons_have_dirty_and (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hAO : IsAO2 n C) (hz : tCount n C s = 0)
    (hunit : ∀ i : Fin n, circuitFun n C (fun k => decide (k = i)) = false)
    (g : ℕ) (hg : g < C.gates.length) (hop : (gateAt C g).op = GateOp.or)
    (i j : Fin n) (hij : s i ≠ s j)
    (hi : PEqualNP.BlindGate.wireValue C n (fun k => decide (k = i)) (n + g) = true)
    (hj : PEqualNP.BlindGate.wireValue C n (fun k => decide (k = j)) (n + g) = true) :
    ∃ k < C.gates.length, OrReaches n C (n + g) k ∧
      (gateAt C k).op = GateOp.and ∧
      ¬ PEqualNP.CircuitMoves.WireBelowOutput n C (n + k) := by
  obtain ⟨k, hk, hr, hand, hv⟩ :=
    mixed_singletons_have_and n C s hAO hz g hg hop i j hij hi hj
  refine ⟨k, hk, hr, hand, ?_⟩
  intro hbelow
  rcases hv with hv | hv
  · have ht := hbelow (fun a => decide (a = i)) hv
    have hf := hunit i
    change C.eval (List.ofFn (fun a => decide (a = i))) = false at hf
    rw [hf] at ht
    cases ht
  · have ht := hbelow (fun a => decide (a = j)) hv
    have hf := hunit j
    change C.eval (List.ofFn (fun a => decide (a = j))) = false at hf
    rw [hf] at ht
    cases ht

lemma prior_or_singletons_same_colour (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hAO : IsAO2 n C) (hz : tCount n C s = 0)
    (hunit : ∀ i : Fin n, circuitFun n C (fun k => decide (k = i)) = false)
    (g : ℕ)
    (hclean : ∀ k < g, (gateAt C k).op = GateOp.and →
      PEqualNP.CircuitMoves.WireBelowOutput n C (n + k))
    (a : ℕ) (ha : a < C.gates.length) (hag : a < g)
    (hop : (gateAt C a).op = GateOp.or)
    (i j : Fin n)
    (hi : PEqualNP.BlindGate.wireValue C n (fun k => decide (k = i)) (n + a) = true)
    (hj : PEqualNP.BlindGate.wireValue C n (fun k => decide (k = j)) (n + a) = true) :
    s i = s j := by
  by_contra hij
  obtain ⟨k, hk, hr, hand, hdirty⟩ :=
    mixed_singletons_have_dirty_and n C s hAO hz hunit a ha hop i j hij hi hj
  have hka := (orReaches_bound n C k (n + a) hr).1
  exact hdirty (hclean k (by omega) hand)

lemma prior_wire_singletons_same_colour (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hAO : IsAO2 n C) (hz : tCount n C s = 0)
    (hunit : ∀ i : Fin n, circuitFun n C (fun k => decide (k = i)) = false)
    (g : ℕ) (hg : g ≤ C.gates.length)
    (hclean : ∀ k < g, (gateAt C k).op = GateOp.and →
      PEqualNP.CircuitMoves.WireBelowOutput n C (n + k))
    (w : ℕ) (hw : w < n + g) (i j : Fin n)
    (hi : PEqualNP.BlindGate.wireValue C n (fun k => decide (k = i)) w = true)
    (hj : PEqualNP.BlindGate.wireValue C n (fun k => decide (k = j)) w = true) :
    s i = s j := by
  by_cases hin : w < n
  · rw [wireValue_input n C _ w hin] at hi hj
    have hwi : (⟨w, hin⟩ : Fin n) = i := of_decide_eq_true hi
    have hwj : (⟨w, hin⟩ : Fin n) = j := of_decide_eq_true hj
    rw [← hwi, ← hwj]
  · obtain ⟨a, rfl⟩ : ∃ a, w = n + a := ⟨w - n, by omega⟩
    have ha : a < C.gates.length := by omega
    have hag : a < g := by omega
    have hm : gateAt C a ∈ C.gates := by
      rw [gateAt_eq_getElem C a ha]
      exact List.getElem_mem ha
    rcases hAO.1 (gateAt C a) hm with hop | hop
    · have hbelow := hclean a hag hop
      have ht := hbelow (fun k => decide (k = i)) hi
      have hf := hunit i
      change C.eval (List.ofFn (fun k => decide (k = i))) = false at hf
      rw [hf] at ht
      cases ht
    · exact prior_or_singletons_same_colour n C s hAO hz hunit g hclean a ha hag hop i j hi hj

lemma orReaches_true (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (x : Fin n → Bool)
    (k : ℕ) (hv : PEqualNP.BlindGate.wireValue C n x (n + k) = true) :
    ∀ w, OrReaches n C w k → PEqualNP.BlindGate.wireValue C n x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hr
    have hn : n ≤ w := hr.1
    obtain ⟨a, rfl⟩ : ∃ a, w = n + a := ⟨w - n, by omega⟩
    obtain ⟨ha, he | ⟨hop, u, hu, hul, hur⟩⟩ := (orReaches_iff n C a k).mp hr
    · rw [← he]
      exact hv
    · rw [wireValue_gate n C x a ha hAO.2.1, hop]
      have hval := ih u hul hur
      simpa [GateOp.eval] using (show ∃ v ∈ (gateAt C a).inputs,
        PEqualNP.BlindGate.wireValue C n x v = true from ⟨u, hu, hval⟩)

lemma orIn_true (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (x : Fin n → Bool)
    (w : ℕ) (i : Fin n) (hi : i ∈ orIn n C w) (hx : x i = true) :
    PEqualNP.BlindGate.wireValue C n x w = true := by
  rw [mem_orIn] at hi
  have hxi : PEqualNP.BlindGate.wireValue C n x i = true :=
    (wireValue_input n C x i i.isLt).trans hx
  rcases hi with he | ⟨a, ha, hr, hop, hin⟩
  · rw [← he]
    exact hxi
  · apply orReaches_true n C hAO x a _ w hr
    rw [wireValue_gate n C x a ha hAO.2.1, hop]
    simpa [GateOp.eval] using (show ∃ v ∈ (gateAt C a).inputs,
      PEqualNP.BlindGate.wireValue C n x v = true from ⟨i, hin, hxi⟩)

lemma prior_wire_on_rejected_input (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (g : ℕ) (hg : g ≤ C.gates.length)
    (hclean : ∀ k < g, (gateAt C k).op = GateOp.and →
      PEqualNP.CircuitMoves.WireBelowOutput n C (n + k))
    (w : ℕ) (hw : w < n + g) (x : Fin n → Bool)
    (hx : circuitFun n C x = false) :
    PEqualNP.BlindGate.wireValue C n x w = true ↔ ∃ i ∈ orIn n C w, x i = true := by
  constructor
  · intro hv
    rcases true_wire_source n C hAO x w (by omega) hv with h | ⟨k, hk, hr, hand, hval⟩
    · exact h
    · have hkw := (orReaches_bound n C k w hr).1
      have hbelow := hclean k (by omega) hand
      have ht := hbelow x hval
      change C.eval (List.ofFn x) = false at hx
      rw [hx] at ht
      cases ht
  · rintro ⟨i, hi, hxi⟩
    exact orIn_true n C hAO x w i hi hxi

lemma below_output_orIn_empty (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hunit : ∀ i : Fin n, circuitFun n C (fun k => decide (k = i)) = false)
    (w : ℕ) (hw : PEqualNP.CircuitMoves.WireBelowOutput n C w) :
    orIn n C w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hv := orIn_true n C hAO (fun k => decide (k = i)) w i hi (by simp)
  have ht := hw (fun k => decide (k = i)) hv
  have hf := hunit i
  change C.eval (List.ofFn (fun k => decide (k = i))) = false at hf
  rw [hf] at ht
  cases ht

lemma orIn_gate_nonempty_is_or (n : ℕ) (C : Circuit) (g : ℕ)
    (h : (orIn n C (n + g)).Nonempty) :
    g < C.gates.length ∧ (gateAt C g).op = GateOp.or := by
  obtain ⟨i, hi⟩ := h
  rw [mem_orIn] at hi
  rcases hi with hi | ⟨k, hk, hr, hop, hin⟩
  · have hlt := i.isLt
    omega
  · obtain ⟨hg, he | ⟨hgo, hrest⟩⟩ := (orReaches_iff n C g k).mp hr
    · exact ⟨hg, he ▸ hop⟩
    · exact ⟨hg, hgo⟩

lemma all_orIn_same_colour (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hz : tCount n C s = 0) (w : ℕ) (i j : Fin n)
    (hi : i ∈ orIn n C w) (hj : j ∈ orIn n C w) : s i = s j := by
  by_cases hwi : w < n
  · have hiw : (i : ℕ) = w := by
      rw [mem_orIn] at hi
      rcases hi with he | ⟨k, hk, hr, hop, hin⟩
      · exact he
      · have hn := hr.1
        omega
    have hjw : (j : ℕ) = w := by
      rw [mem_orIn] at hj
      rcases hj with he | ⟨k, hk, hr, hop, hin⟩
      · exact he
      · have hn := hr.1
        omega
    rw [hiw, hjw]
  · obtain ⟨g, rfl⟩ : ∃ g, w = n + g := ⟨w - n, by omega⟩
    obtain ⟨hg, hop⟩ := orIn_gate_nonempty_is_or n C g ⟨i, hi⟩
    exact orIn_same_colour n C s hz g hg hop i j hi hj

lemma all_orIn_one_colour (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hz : tCount n C s = 0) (w : ℕ) :
    (∀ i ∈ orIn n C w, s i = false) ∨
      (∀ i ∈ orIn n C w, s i = true) := by
  by_cases h : ∃ i ∈ orIn n C w, s i = true
  · obtain ⟨i, hi, hci⟩ := h
    right
    intro j hj
    exact (all_orIn_same_colour n C s hz w j i hj hi).trans hci
  · left
    intro i hi
    cases hci : s i
    · rfl
    · exact False.elim (h ⟨i, hi, hci⟩)

end PEqualNP.Outside.L_meta_4675.NormalizationFinal
namespace PEqualNP.Outside.L_meta_4675.Normalization

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.TwoColour

lemma no_twoColour_of_count_zero (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hz : tCount n C s = 0) (g : ℕ) : ¬ IsTwoColour n C s g := by
  intro hg
  have he : twoColour n C s = ∅ := Finset.card_eq_zero.mp hz
  have hm : g ∈ twoColour n C s :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.1, hg⟩
  rw [he] at hm
  simpa using hm

lemma orIn_same_colour (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hz : tCount n C s = 0) (g : ℕ) (hg : g < C.gates.length)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = GateOp.or)
    (i j : Fin n) (hi : i ∈ orIn n C (n + g)) (hj : j ∈ orIn n C (n + g)) :
    s i = s j := by
  cases hci : s i <;> cases hcj : s j
  · rfl
  · exact False.elim (no_twoColour_of_count_zero n C s hz g
      ⟨hg, hop, ⟨i, hi, hci⟩, ⟨j, hj, hcj⟩⟩)
  · exact False.elim (no_twoColour_of_count_zero n C s hz g
      ⟨hg, hop, ⟨j, hj, hcj⟩, ⟨i, hi, hci⟩⟩)
  · rfl

lemma orIn_one_colour (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hz : tCount n C s = 0) (g : ℕ) (hg : g < C.gates.length)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = GateOp.or) :
    (∀ i ∈ orIn n C (n + g), s i = false) ∨
      (∀ i ∈ orIn n C (n + g), s i = true) := by
  by_cases h : ∃ i ∈ orIn n C (n + g), s i = true
  · obtain ⟨i, hi, hci⟩ := h
    right
    intro j hj
    exact (orIn_same_colour n C s hz g hg hop j i hj hi).trans hci
  · left
    intro i hi
    cases hci : s i
    · rfl
    · exact False.elim (h ⟨i, hi, hci⟩)

def maskedMix : Circuit :=
  ⟨[⟨GateOp.and, [0, 0]⟩, ⟨GateOp.and, [1, 1]⟩,
    ⟨GateOp.or, [2, 3]⟩], 4⟩

lemma maskedMix_ao : IsAO2 2 maskedMix := by decide

lemma maskedMix_count : tCount 2 maskedMix (fun i => decide (1 ≤ i)) = 0 := by decide

lemma maskedMix_reach : orIn 2 maskedMix 4 = ∅ := by decide

lemma maskedMix_semantics : ∀ x : Fin 2 → Bool,
    PEqualNP.MetaComplexity.circuitFun 2 maskedMix x = (x 0 || x 1) := by decide

def repeatedEdge : Circuit :=
  ⟨[⟨GateOp.and, [0, 0]⟩, ⟨GateOp.and, [2, 1]⟩], 3⟩

lemma repeatedEdge_ao : IsAO2 2 repeatedEdge := by decide

lemma repeatedEdge_count : tCount 2 repeatedEdge (fun i => decide (1 ≤ i)) = 0 := by decide

lemma repeatedEdge_semantics : ∀ x : Fin 2 → Bool,
    PEqualNP.MetaComplexity.circuitFun 2 repeatedEdge x = (x 0 && x 1) := by decide

lemma repeatedEdge_not_readOne : PEqualNP.ReadK.readsAtMost repeatedEdge 2 [0, 1] 1 = false := by decide

end PEqualNP.Outside.L_meta_4675.Normalization
namespace PEqualNP.Outside.L_meta_4675.NormalizationFinal

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.TwoColour
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

lemma graph_rejects_pair (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hcomp : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (x : Fin (p + l) → Bool) (a b : Fin (p + l))
    (hx : circuitFun (p + l) C x = false) (ha : x a = true) (hb : x b = true) :
    circuitFun (p + l) C (PEqualNP.EdgeOwnership.pairInput a b) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro ht
  rw [hcomp] at ht
  obtain ⟨i, j, he, hi, hj⟩ := of_decide_eq_true ht
  have hsub : ∀ z, PEqualNP.EdgeOwnership.pairInput a b z = true → x z = true := by
    intro z hz
    simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hz
    rcases hz with rfl | rfl
    · exact ha
    · exact hb
  have hout : circuitFun (p + l) C x = true := by
    rw [hcomp]
    exact decide_eq_true ⟨i, j, he, hsub _ hi, hsub _ hj⟩
  rw [hx] at hout
  cases hout

lemma first_dirty_pair_witness (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (hAO : IsAO2 (p + l) C)
    (hcomp : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (g : ℕ) (hg : g < C.gates.length)
    (hand : (gateAt C g).op = GateOp.and)
    (hclean : ∀ k < g, (gateAt C k).op = GateOp.and →
      PEqualNP.CircuitMoves.WireBelowOutput (p + l) C (p + l + k))
    (hdirty : ¬ PEqualNP.CircuitMoves.WireBelowOutput (p + l) C (p + l + g)) :
    ∃ a b : Fin (p + l),
      a ∈ orIn (p + l) C (opnd C g 0) ∧
      b ∈ orIn (p + l) C (opnd C g 1) ∧
      circuitFun (p + l) C (PEqualNP.EdgeOwnership.pairInput a b) = false ∧
      PEqualNP.BlindGate.wireValue C (p + l)
        (PEqualNP.EdgeOwnership.pairInput a b) (p + l + g) = true := by
  classical
  unfold PEqualNP.CircuitMoves.WireBelowOutput at hdirty
  push_neg at hdirty
  obtain ⟨x, hxgate, hxout⟩ := hdirty
  have hx : circuitFun (p + l) C x = false := Bool.eq_false_of_not_eq_true hxout
  have hmem : gateAt C g ∈ C.gates := by
    rw [gateAt_eq_getElem C g hg]
    exact List.getElem_mem hg
  have hlen := hAO.2.2 _ hmem
  obtain ⟨u, v, huv⟩ : ∃ u v, (gateAt C g).inputs = [u, v] := by
    exact List.length_eq_two.mp hlen
  have hu : u < p + l + g := hAO.2.1 g hg u (by simp [huv])
  have hv : v < p + l + g := hAO.2.1 g hg v (by simp [huv])
  have hop0 : opnd C g 0 = u := by simp [opnd, huv]
  have hop1 : opnd C g 1 = v := by simp [opnd, huv]
  change PEqualNP.BlindGate.wireValue C (p + l) x (p + l + g) = true at hxgate
  rw [wireValue_gate (p + l) C x g hg hAO.2.1, hand, huv] at hxgate
  have hxuv : PEqualNP.BlindGate.wireValue C (p + l) x u = true ∧
      PEqualNP.BlindGate.wireValue C (p + l) x v = true := by
    simpa [GateOp.eval] using hxgate
  obtain ⟨a, ha, hxa⟩ :=
    (prior_wire_on_rejected_input (p + l) C hAO g (by omega) hclean u hu x hx).mp hxuv.1
  obtain ⟨b, hb, hxb⟩ :=
    (prior_wire_on_rejected_input (p + l) C hAO g (by omega) hclean v hv x hx).mp hxuv.2
  refine ⟨a, b, by simpa [hop0] using ha, by simpa [hop1] using hb,
    graph_rejects_pair p l E C hcomp x a b hx hxa hxb, ?_⟩
  rw [wireValue_gate (p + l) C _ g hg hAO.2.1, hand, huv]
  have ha' := orIn_true (p + l) C hAO (PEqualNP.EdgeOwnership.pairInput a b) u a ha (by
    simp [PEqualNP.EdgeOwnership.pairInput])
  have hb' := orIn_true (p + l) C hAO (PEqualNP.EdgeOwnership.pairInput a b) v b hb (by
    simp [PEqualNP.EdgeOwnership.pairInput])
  simp [GateOp.eval, ha', hb']

lemma and_below_iff_cross_pairs (p l : ℕ) (E : Finset (Fin p × Fin l))
    (C : Circuit) (hAO : IsAO2 (p + l) C)
    (hcomp : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (g : ℕ) (hg : g < C.gates.length)
    (hand : (gateAt C g).op = GateOp.and)
    (hclean : ∀ k < g, (gateAt C k).op = GateOp.and →
      PEqualNP.CircuitMoves.WireBelowOutput (p + l) C (p + l + k)) :
    PEqualNP.CircuitMoves.WireBelowOutput (p + l) C (p + l + g) ↔
      ∀ a ∈ orIn (p + l) C (opnd C g 0),
        ∀ b ∈ orIn (p + l) C (opnd C g 1),
          circuitFun (p + l) C (PEqualNP.EdgeOwnership.pairInput a b) = true := by
  constructor
  · intro hbelow a ha b hb
    apply hbelow
    have hmem : gateAt C g ∈ C.gates := by
      rw [gateAt_eq_getElem C g hg]
      exact List.getElem_mem hg
    obtain ⟨u, v, huv⟩ := List.length_eq_two.mp (hAO.2.2 _ hmem)
    have ha' : a ∈ orIn (p + l) C u := by simpa [opnd, huv] using ha
    have hb' : b ∈ orIn (p + l) C v := by simpa [opnd, huv] using hb
    change PEqualNP.BlindGate.wireValue C (p + l) _ (p + l + g) = true
    rw [wireValue_gate (p + l) C _ g hg hAO.2.1, hand, huv]
    have hva := orIn_true (p + l) C hAO (PEqualNP.EdgeOwnership.pairInput a b) u a ha'
      (by simp [PEqualNP.EdgeOwnership.pairInput])
    have hvb := orIn_true (p + l) C hAO (PEqualNP.EdgeOwnership.pairInput a b) v b hb'
      (by simp [PEqualNP.EdgeOwnership.pairInput])
    simp [GateOp.eval, hva, hvb]
  · intro hpairs
    by_contra hdirty
    obtain ⟨a, b, ha, hb, hout, _⟩ :=
      first_dirty_pair_witness p l E C hAO hcomp g hg hand hclean hdirty
    have ht := hpairs a ha b hb
    rw [hout] at ht
    cases ht

end PEqualNP.Outside.L_meta_4675.NormalizationFinal
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
namespace PEqualNP.Outside.L_meta_4675.RowSharing

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.TwoColour

def circuit : Circuit :=
  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩,
    ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [7, 4]⟩,
    ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [8, 9]⟩], 10⟩

def edges : Finset (Fin 2 × Fin 3) := {(0, 0), (0, 2), (1, 1), (1, 2)}

lemma circuit_ao : IsAO2 5 circuit := by decide

lemma circuit_zero : tCount 5 circuit (fun i => decide (2 ≤ i)) = 0 := by decide

lemma no_rectangle : ∀ (a a' : Fin 2) (b b' : Fin 3), a ≠ a' → b ≠ b' →
    ¬ ((a, b) ∈ edges ∧ (a, b') ∈ edges ∧ (a', b) ∈ edges ∧ (a', b') ∈ edges) := by
  decide

lemma circuit_value : ∀ x : Fin 5 → Bool,
    PEqualNP.MetaComplexity.circuitFun 5 circuit x =
      decide (∃ (a : Fin 2) (b : Fin 3), (a, b) ∈ edges ∧
        x (Fin.castAdd 3 a) = true ∧ x (Fin.natAdd 2 b) = true) := by
  decide

def rowInput (a : Fin 2) (y : Fin 3 → Bool) : Fin 5 → Bool :=
  fun i => if h : i.val < 2 then decide (a.val = i.val) else y ⟨i.val - 2, by omega⟩

lemma shared_or_left : ∀ y : Fin 3 → Bool,
    PEqualNP.EdgeOwnership.gateVal 5 circuit 3 (rowInput 0 y) =
      (y 0 || y 2) := by decide

lemma shared_or_right : ∀ y : Fin 3 → Bool,
    PEqualNP.EdgeOwnership.gateVal 5 circuit 3 (rowInput 1 y) =
      (y 1 || y 2) := by decide

lemma shared_or_reach : orIn 5 circuit 8 = {4} := by decide

def clause (q : Fin 3 → Bool) : Finset (Fin 5) :=
  if q 2 then {0, 1}
  else ({4} ∪ (if q 0 then {2} else {0})) ∪ (if q 1 then {3} else {1})

lemma clause_semantics : ∀ x : Fin 5 → Bool,
    PEqualNP.MetaComplexity.circuitFun 5 circuit x = false ↔
      ∃ q : Fin 3 → Bool, ∀ v ∈ clause q, x v = false := by
  decide

lemma avoidance_not_cube_convex :
    ¬ (∀ (q r s : Fin 3 → Bool), 2 ∉ clause q → 2 ∉ clause r →
      (∀ i, s i = q i ∨ s i = r i) → 2 ∉ clause s) := by
  intro h
  have hq : 2 ∉ clause ![true, false, true] := by decide
  have hr : 2 ∉ clause ![false, false, false] := by decide
  have hs : ∀ i : Fin 3, (![true, false, false] : Fin 3 → Bool) i =
      (![true, false, true] : Fin 3 → Bool) i ∨
      (![true, false, false] : Fin 3 → Bool) i =
      (![false, false, false] : Fin 3 → Bool) i := by decide
  have hf := h ![true, false, true] ![false, false, false] ![true, false, false] hq hr hs
  exact hf (by decide)

end PEqualNP.Outside.L_meta_4675.RowSharing
namespace PEqualNP.Outside.L_meta_4675.ReaderPath

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.TwoColour
  PEqualNP.CleanedNonEdge

def edges : Finset (Fin 3 × Fin 2) := {(0, 0), (0, 1), (1, 0), (2, 1)}

abbrev graph : SimpleGraph (Fin 5) := SimpleGraph.fromRel fun u v =>
  (u.val, v.val) ∈ ([(0, 3), (0, 4), (1, 3), (2, 4)] : List (ℕ × ℕ))

def circuit : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [5, 6]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.and, [8, 9]⟩,
    ⟨GateOp.and, [2, 4]⟩,
    ⟨GateOp.or, [10, 11]⟩], 12⟩

lemma circuit_size : circuit.size = 8 := rfl

lemma legal : IsAO2 5 circuit := by decide +kernel

lemma computes : ∀ x : Fin 5 → Bool,
    circuitFun 5 circuit x =
      decide (∃ a : Fin 3, ∃ b : Fin 2, (a, b) ∈ edges ∧
        x (Fin.castAdd 2 a) = true ∧ x (Fin.natAdd 3 b) = true) := by decide +kernel

lemma computes_graph : circuitFun 5 circuit = graphFun graph ∅ := by decide +kernel

lemma zero_two_colour : tCount 5 circuit (fun i => decide (3 ≤ i)) = 0 := by decide +kernel

lemma no_four_cycle : NoFourCycle graph := by decide +kernel

lemma top_form : TopForm graph circuit := by decide +kernel

lemma one_dirty_and : junk graph circuit = {2} := by decide +kernel

lemma reader_is_below : BelowF graph circuit 5 := by decide +kernel

lemma reader_pair_values : ∀ (a : Fin 3) (b : Fin 2),
    PEqualNP.EdgeOwnership.gateVal 5 circuit 5
      (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd 2 a) (Fin.natAdd 3 b)) =
    decide ((a, b) ∈ ({(0, 0), (0, 1), (1, 0)} : Finset (Fin 3 × Fin 2))) := by
  decide +kernel

lemma reader_has_no_star_center : ¬ ∃ z : Fin 5, ∀ (a : Fin 3) (b : Fin 2),
    (a, b) ∈ ({(0, 0), (0, 1), (1, 0)} : Finset (Fin 3 × Fin 2)) →
    Fin.castAdd 2 a = z ∨ Fin.natAdd 3 b = z := by decide +kernel

end PEqualNP.Outside.L_meta_4675.ReaderPath
namespace PEqualNP.Outside.L_meta_4675.Buffering

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def copyGate (i : ℕ) : Gate := ⟨GateOp.and, [i, i]⟩

def shiftedGate (n : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (n + ·)⟩

def buffered (n : ℕ) (C : Circuit) : Circuit :=
  ⟨(List.range n).map copyGate ++ C.gates.map (shiftedGate n), n + C.output⟩

lemma getD_append_left (xs ys : List Bool) (i : ℕ) (hi : i < xs.length) :
    (xs ++ ys).getD i false = xs.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right (xs ys : List Bool) (i : ℕ) :
    (xs ++ ys).getD (xs.length + i) false = ys.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

lemma copy_step (xs acc : List Bool) (i : ℕ) (hi : i < xs.length) :
    step (xs ++ acc) (copyGate i) = xs ++ (acc ++ [xs.getD i false]) := by
  have hd := getD_append_left xs acc i hi
  simp only [step, copyGate, List.map_cons, List.map_nil, hd]
  have hb (b : Bool) : GateOp.and.eval [b, b] = b := by cases b <;> rfl
  rw [hb]
  simp [List.append_assoc]

lemma copy_fold (xs : List Bool) (ids : List ℕ)
    (hids : ∀ i ∈ ids, i < xs.length) (acc : List Bool) :
    ((ids.map copyGate).foldl step (xs ++ acc)) =
      xs ++ (acc ++ ids.map (fun i => xs.getD i false)) := by
  induction ids generalizing acc with
  | nil => simp
  | cons i ids ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [copy_step xs acc i (hids i (by simp))]
    rw [ih (fun j hj => hids j (by simp [hj]))]
    simp [List.append_assoc]

lemma range_lookup (xs : List Bool) :
    (List.range xs.length).map (fun i => xs.getD i false) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hil : i < xs.length := by simpa using hi
    simp [List.getD_eq_getElem?_getD, hil]

lemma copies_wires (n : ℕ) (xs : List Bool) (hx : xs.length = n) :
    (((List.range n).map copyGate).foldl step xs) = xs ++ xs := by
  rw [← hx]
  have h := copy_fold xs (List.range xs.length) (by intro i hi; exact List.mem_range.mp hi) []
  simpa only [List.append_nil, List.nil_append, range_lookup] using h

lemma shifted_step (n : ℕ) (pref xs : List Bool) (hp : pref.length = n) (g : Gate) :
    step (pref ++ xs) (shiftedGate n g) = pref ++ step xs g := by
  have he (i : ℕ) : (pref ++ xs).getD (n + i) false = xs.getD i false := by
    rw [← hp]
    exact getD_append_right pref xs i
  simp only [step, shiftedGate, List.map_map]
  simp only [Function.comp_def, he, List.append_assoc]

lemma shifted_fold (n : ℕ) (pref : List Bool) (hp : pref.length = n) (gs : List Gate)
    (xs : List Bool) :
    ((gs.map (shiftedGate n)).foldl step (pref ++ xs)) = pref ++ gs.foldl step xs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons, shifted_step n pref xs hp g]
    exact ih (step xs g)

lemma buffered_wires (n : ℕ) (C : Circuit) (xs : List Bool) (hx : xs.length = n) :
    (buffered n C).wires xs = xs ++ C.wires xs := by
  change ((List.range n).map copyGate ++ C.gates.map (shiftedGate n)).foldl step xs =
    xs ++ C.gates.foldl step xs
  rw [List.foldl_append, copies_wires n xs hx, shifted_fold n xs hx C.gates xs]

lemma buffered_eval (n : ℕ) (C : Circuit) (xs : List Bool) (hx : xs.length = n) :
    (buffered n C).eval xs = C.eval xs := by
  unfold Circuit.eval
  rw [buffered_wires n C xs hx]
  change (xs ++ C.wires xs).getD (n + C.output) false = (C.wires xs).getD C.output false
  rw [← hx]
  exact getD_append_right xs (C.wires xs) C.output

lemma buffered_size (n : ℕ) (C : Circuit) : (buffered n C).size = C.size + n := by
  simp [buffered, Circuit.size, Nat.add_comm]

lemma buffered_gate_early (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < n) :
    gateAt (buffered n C) j = copyGate j := by
  simp [gateAt, buffered, List.getD_eq_getElem?_getD, List.getElem?_append_left, hj]

lemma buffered_gate_late (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (buffered n C) (n + j) = shiftedGate n (gateAt C j) := by
  simp [gateAt, buffered, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.getElem_mem hj

lemma buffered_ao (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) : IsAO2 n (buffered n C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [buffered, List.mem_append, List.mem_map] at hg
    rcases hg with ⟨i, hi, rfl⟩ | ⟨g, hg, rfl⟩
    · exact Or.inl rfl
    · exact hAO.1 g hg
  · intro j hj w hw
    have hj' : j < n + C.gates.length := by simpa [buffered] using hj
    by_cases hjn : j < n
    · rw [buffered_gate_early n C j hjn] at hw
      simp only [copyGate, List.mem_cons, List.not_mem_nil, or_false, or_self] at hw
      omega
    · obtain ⟨k, rfl⟩ : ∃ k, j = n + k := ⟨j - n, by omega⟩
      have hk : k < C.gates.length := by omega
      rw [buffered_gate_late n C k hk] at hw
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      have hul := hAO.2.1 k hk u hu
      omega
  · intro g hg
    simp only [buffered, List.mem_append, List.mem_map] at hg
    rcases hg with ⟨i, hi, rfl⟩ | ⟨g, hg, rfl⟩
    · rfl
    · simpa [shiftedGate] using hAO.2.2 g hg

lemma buffered_or_inputs (n : ℕ) (C : Circuit) (g : Gate)
    (hg : g ∈ (buffered n C).gates) (hop : g.op = GateOp.or) (w : ℕ)
    (hw : w ∈ g.inputs) : n ≤ w := by
  simp only [buffered, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨i, hi, rfl⟩ | ⟨g, hg, rfl⟩
  · cases hop
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    omega

lemma buffered_orIn_empty (n : ℕ) (C : Circuit) (g : ℕ) :
    orIn n (buffered n C) (n + g) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with hi | ⟨k, hk, hr, hop, hin⟩
  · have hil := i.isLt
    omega
  · have hlo := buffered_or_inputs n C (gateAt (buffered n C) k)
      (gateAt_mem (buffered n C) k hk) hop i hin
    have hil := i.isLt
    omega

lemma buffered_count_zero (n : ℕ) (C : Circuit) (s : ℕ → Bool) :
    tCount n (buffered n C) s = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro g hg
  have h : IsTwoColour n (buffered n C) s g := (Finset.mem_filter.mp hg).2
  obtain ⟨i, hi, hs⟩ := h.2.2.1
  rw [buffered_orIn_empty n C g] at hi
  simp at hi

lemma additive_buffering (n : ℕ) (C : Circuit) (s : ℕ → Bool) (hAO : IsAO2 n C) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size + n ∧
      circuitFun n D = circuitFun n C ∧ tCount n D s = 0 := by
  refine ⟨buffered n C, buffered_ao n C hAO, buffered_size n C, ?_, buffered_count_zero n C s⟩
  funext x
  exact buffered_eval n C (List.ofFn x) (by simp)

def oneMap (n p w : ℕ) : ℕ :=
  if w < p then n + w else if w < n then w else p + w

def oneGate (n p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (oneMap n p)⟩

def oneBuffer (n p : ℕ) (C : Circuit) : Circuit :=
  ⟨(List.range p).map copyGate ++ C.gates.map (oneGate n p), oneMap n p C.output⟩

lemma take_lookup (xs : List Bool) (p : ℕ) (hp : p ≤ xs.length) :
    (List.range p).map (fun i => xs.getD i false) = xs.take p := by
  apply List.ext_getElem
  · simp [List.length_take, hp]
  · intro i hi hj
    have hip : i < p := by simpa using hi
    have hil : i < xs.length := by omega
    simp [List.getD_eq_getElem?_getD, hil]

lemma one_copies_wires (n p : ℕ) (hp : p ≤ n) (xs : List Bool) (hx : xs.length = n) :
    (((List.range p).map copyGate).foldl step xs) = xs ++ xs.take p := by
  have h := copy_fold xs (List.range p) (by
    intro i hi
    have := List.mem_range.mp hi
    omega) []
  simpa only [List.append_nil, List.nil_append, take_lookup xs p (by omega)] using h

lemma one_lookup (n p : ℕ) (hp : p ≤ n) (xs acc : List Bool) (hx : xs.length = n) (w : ℕ) :
    (xs ++ xs.take p ++ acc).getD (oneMap n p w) false = (xs ++ acc).getD w false := by
  have ht : (xs.take p).length = p := by simp [List.length_take, hx, hp]
  by_cases hwp : w < p
  · have hwn : w < n := by omega
    simp only [oneMap, ite_eq_left hwp]
    rw [List.append_assoc]
    have he : n + w = xs.length + w := by omega
    rw [he, getD_append_right, getD_append_left (xs.take p) acc w (by omega),
      getD_append_left xs acc w (by omega)]
    simp [List.getD_eq_getElem?_getD, hwp]
  · simp only [oneMap, ite_eq_right hwp]
    by_cases hwn : w < n
    · rw [ite_eq_left hwn, getD_append_left (xs ++ xs.take p) acc w (by simp [hx]; omega)]
      rw [getD_append_left xs (xs.take p) w (by omega), getD_append_left xs acc w (by omega)]
    · rw [ite_eq_right hwn]
      have he1 : p + w = (xs ++ xs.take p).length + (w - n) := by
        simp only [List.length_append, hx, ht]
        omega
      have he2 : w = xs.length + (w - n) := by omega
      rw [he1, getD_append_right, he2, getD_append_right]
      simp [hx]

lemma one_step (n p : ℕ) (hp : p ≤ n) (xs acc : List Bool) (hx : xs.length = n) (g : Gate) :
    step (xs ++ xs.take p ++ acc) (oneGate n p g) =
      xs ++ xs.take p ++ (acc ++ [g.op.eval (g.inputs.map fun w => (xs ++ acc).getD w false)]) := by
  simp only [step, oneGate, List.map_map, Function.comp_def]
  simp_rw [one_lookup n p hp xs acc hx]
  simp only [List.append_assoc]

lemma one_fold (n p : ℕ) (hp : p ≤ n) (xs : List Bool) (hx : xs.length = n)
    (gs : List Gate) (acc : List Bool) :
    ∃ tail : List Bool, gs.foldl step (xs ++ acc) = xs ++ tail ∧
      ((gs.map (oneGate n p)).foldl step (xs ++ xs.take p ++ acc)) = xs ++ xs.take p ++ tail := by
  induction gs generalizing acc with
  | nil => exact ⟨acc, rfl, rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun w => (xs ++ acc).getD w false)
    obtain ⟨tail, h1, h2⟩ := ih (acc ++ [v])
    refine ⟨tail, ?_, ?_⟩
    · simpa only [List.foldl_cons, step, ← List.append_assoc] using h1
    · simpa only [List.map_cons, List.foldl_cons, one_step n p hp xs acc hx g] using h2

lemma oneBuffer_eval (n p : ℕ) (hp : p ≤ n) (C : Circuit) (xs : List Bool) (hx : xs.length = n) :
    (oneBuffer n p C).eval xs = C.eval xs := by
  obtain ⟨tail, h1, h2⟩ := one_fold n p hp xs hx C.gates []
  simp only [List.append_nil] at h1 h2
  have hw : (oneBuffer n p C).wires xs = xs ++ xs.take p ++ tail := by
    change ((List.range p).map copyGate ++ C.gates.map (oneGate n p)).foldl step xs = _
    rw [List.foldl_append, one_copies_wires n p hp xs hx]
    exact h2
  change ((oneBuffer n p C).wires xs).getD (oneMap n p C.output) false =
    (C.wires xs).getD C.output false
  rw [hw, one_lookup n p hp xs tail hx]
  exact congrArg (fun ws : List Bool => ws.getD C.output false) h1.symm

lemma oneBuffer_size (n p : ℕ) (C : Circuit) : (oneBuffer n p C).size = C.size + p := by
  simp [oneBuffer, Circuit.size, Nat.add_comm]

lemma oneBuffer_gate_early (n p : ℕ) (C : Circuit) (j : ℕ) (hj : j < p) :
    gateAt (oneBuffer n p C) j = copyGate j := by
  simp [gateAt, oneBuffer, List.getD_eq_getElem?_getD, List.getElem?_append_left, hj]

lemma oneBuffer_gate_late (n p : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (oneBuffer n p C) (p + j) = oneGate n p (gateAt C j) := by
  simp [gateAt, oneBuffer, List.getD_eq_getElem?_getD, hj]

lemma oneMap_lt (n p B w : ℕ) (_hp : p ≤ n) (hw : w < n + B) : oneMap n p w < n + p + B := by
  unfold oneMap
  split_ifs <;> omega

lemma oneBuffer_ao (n p : ℕ) (hp : p ≤ n) (C : Circuit) (hAO : IsAO2 n C) :
    IsAO2 n (oneBuffer n p C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [oneBuffer, List.mem_append, List.mem_map] at hg
    rcases hg with ⟨i, hi, rfl⟩ | ⟨g, hg, rfl⟩
    · exact Or.inl rfl
    · exact hAO.1 g hg
  · intro j hj w hw
    have hj' : j < p + C.gates.length := by simpa [oneBuffer] using hj
    by_cases hjp : j < p
    · rw [oneBuffer_gate_early n p C j hjp] at hw
      simp only [copyGate, List.mem_cons, List.not_mem_nil, or_false, or_self] at hw
      omega
    · obtain ⟨k, rfl⟩ : ∃ k, j = p + k := ⟨j - p, by omega⟩
      have hk : k < C.gates.length := by omega
      rw [oneBuffer_gate_late n p C k hk] at hw
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
      have hul := oneMap_lt n p k u hp (hAO.2.1 k hk u hu)
      omega
  · intro g hg
    simp only [oneBuffer, List.mem_append, List.mem_map] at hg
    rcases hg with ⟨i, hi, rfl⟩ | ⟨g, hg, rfl⟩
    · rfl
    · simpa [oneGate] using hAO.2.2 g hg

lemma oneMap_ge (n p w : ℕ) (hp : p ≤ n) : p ≤ oneMap n p w := by
  unfold oneMap
  split_ifs <;> omega

lemma oneBuffer_or_inputs (n p : ℕ) (hp : p ≤ n) (C : Circuit) (g : Gate)
    (hg : g ∈ (oneBuffer n p C).gates) (hop : g.op = GateOp.or) (w : ℕ)
    (hw : w ∈ g.inputs) : p ≤ w := by
  simp only [oneBuffer, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨i, hi, rfl⟩ | ⟨g, hg, rfl⟩
  · cases hop
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
    exact oneMap_ge n p u hp

lemma oneBuffer_orIn_line (n p : ℕ) (hp : p ≤ n) (C : Circuit) (g : ℕ) (i : Fin n)
    (hi : i ∈ orIn n (oneBuffer n p C) (n + g)) : p ≤ (i : ℕ) := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with hi | ⟨k, hk, hr, hop, hin⟩
  · have hil := i.isLt
    omega
  · exact oneBuffer_or_inputs n p hp C (gateAt (oneBuffer n p C) k)
      (gateAt_mem (oneBuffer n p C) k hk) hop i hin

lemma oneBuffer_count_zero (n p : ℕ) (hp : p ≤ n) (C : Circuit) :
    tCount n (oneBuffer n p C) (fun i => decide (p ≤ i)) = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro g hg
  have h : IsTwoColour n (oneBuffer n p C) (fun i => decide (p ≤ i)) g :=
    (Finset.mem_filter.mp hg).2
  obtain ⟨i, hi, hs⟩ := h.2.2.1
  have hlo := oneBuffer_orIn_line n p hp C g i hi
  simp [hlo] at hs

lemma one_sided_buffering (p l : ℕ) (C : Circuit) (hAO : IsAO2 (p + l) C) :
    ∃ D : Circuit, IsAO2 (p + l) D ∧ D.size = C.size + p ∧
      circuitFun (p + l) D = circuitFun (p + l) C ∧
      tCount (p + l) D (fun i => decide (p ≤ i)) = 0 := by
  refine ⟨oneBuffer (p + l) p C, oneBuffer_ao (p + l) p (by omega) C hAO,
    oneBuffer_size (p + l) p C, ?_, oneBuffer_count_zero (p + l) p (by omega) C⟩
  funext x
  exact oneBuffer_eval (p + l) p (by omega) C (List.ofFn x) (by simp)

end PEqualNP.Outside.L_meta_4675.Buffering
namespace PEqualNP.Outside.L_meta_4675.Lattice

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def cut (k a : ℕ) : Bool := decide (k < a)

def gateN : GateOp → ℕ → ℕ → ℕ
  | .and, a, b => min a b
  | .or, a, b => max a b
  | _, _, _ => 0

def stepN (w : List ℕ) (g : Gate) : List ℕ :=
  w ++ [gateN g.op (w.getD (g.inputs.getD 0 0) 0) (w.getD (g.inputs.getD 1 0) 0)]

def stepB (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def natFun (n : ℕ) (C : Circuit) (x : Fin n → ℕ) : ℕ :=
  (C.gates.foldl stepN (List.ofFn x)).getD C.output 0

lemma cut_getD (w : List ℕ) (k i : ℕ) :
    (w.map (cut k)).getD i false = cut k (w.getD i 0) := by
  simpa [cut] using (List.getD_map w 0 (n := i) (cut k))

lemma step_threshold (w : List ℕ) (g : Gate) (k : ℕ)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2) :
    (stepN w g).map (cut k) = stepB (w.map (cut k)) g := by
  obtain ⟨i, j, hij⟩ := List.length_eq_two.mp hlen
  rcases hop with hop | hop <;>
    simp [stepN, stepB, hij, hop, gateN, cut, lt_min_iff, lt_max_iff]
  all_goals
    cases hi : w[i]? <;> cases hj : w[j]? <;> simp [GateOp.eval, cut]

lemma fold_threshold (gs : List Gate)
    (h : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (w : List ℕ) (k : ℕ) :
    (gs.foldl stepN w).map (cut k) = gs.foldl stepB (w.map (cut k)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hg := h g (by simp)
    have ht : ∀ a ∈ gs, (a.op = GateOp.and ∨ a.op = GateOp.or) ∧ a.inputs.length = 2 :=
      fun a ha => h a (by simp [ha])
    simp only [List.foldl_cons]
    rw [ih ht, step_threshold w g k hg.1 hg.2]

lemma circuit_threshold (n : ℕ) (C : Circuit) (hC : IsAO2 n C)
    (x : Fin n → ℕ) (k : ℕ) :
    PEqualNP.MetaComplexity.circuitFun n C (fun i => cut k (x i)) = cut k (natFun n C x) := by
  have h := fold_threshold C.gates (fun g hg => ⟨hC.1 g hg, hC.2.2 g hg⟩) (List.ofFn x) k
  have hh := congrArg (fun w : List Bool => w.getD C.output false) h
  rw [cut_getD] at hh
  unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval Circuit.wires natFun
  unfold stepB at hh
  simpa only [List.map_ofFn, Function.comp_def] using hh.symm

lemma edge_threshold (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hC : IsAO2 (p + l) C)
    (hfun : ∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (x : Fin (p + l) → ℕ) (k : ℕ) :
    k < natFun (p + l) C x ↔ ∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
      k < x (Fin.castAdd l a) ∧ k < x (Fin.natAdd p b) := by
  have h := hfun (fun i => cut k (x i))
  rw [circuit_threshold (p + l) C hC x k] at h
  have hh := congrArg (fun b : Bool => b = true) h
  simpa [cut] using (Iff.of_eq hh)

lemma edge_value (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hC : IsAO2 (p + l) C)
    (hfun : ∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true))
    (x : Fin (p + l) → ℕ) :
    natFun (p + l) C x =
      E.sup (fun e => min (x (Fin.castAdd l e.1)) (x (Fin.natAdd p e.2))) := by
  apply Nat.le_antisymm
  · by_contra h
    have hlt := Nat.lt_of_not_ge h
    obtain ⟨a, b, he, ha, hb⟩ := (edge_threshold p l E C hC hfun x _).mp hlt
    have hle : min (x (Fin.castAdd l a)) (x (Fin.natAdd p b)) ≤
        E.sup (fun e => min (x (Fin.castAdd l e.1)) (x (Fin.natAdd p e.2))) :=
      Finset.le_sup (f := fun e : Fin p × Fin l =>
        min (x (Fin.castAdd l e.1)) (x (Fin.natAdd p e.2))) he
    exact (not_lt_of_ge hle) (lt_min ha hb)
  · apply Finset.sup_le
    intro e he
    by_contra h
    have hlt := Nat.lt_of_not_ge h
    have heq : natFun (p + l) C x < natFun (p + l) C x :=
      (edge_threshold p l E C hC hfun x _).mpr
        ⟨e.1, e.2, he, (lt_min_iff.mp hlt).1, (lt_min_iff.mp hlt).2⟩
    exact (Nat.lt_irrefl _) heq

end PEqualNP.Outside.L_meta_4675.Lattice
namespace PEqualNP.Outside.L_meta_4675.MatchingConsequence

lemma cover_card_of_matching {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : Fin p → Fin l) (hf : Function.Injective f) (hE : ∀ a, (a, f a) ∈ E)
    (S : Finset (Fin (p + l)))
    (hS : ∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) :
    p ≤ S.card := by
  classical
  let pick : Fin p → Fin (p + l) :=
    fun a => if Fin.castAdd l a ∈ S then Fin.castAdd l a else Fin.natAdd p (f a)
  have hpick : Function.Injective pick := by
    intro a b he
    dsimp [pick] at he
    split_ifs at he with ha hb
    · apply Fin.ext
      have hval := congrArg Fin.val he
      simpa using hval
    · have hval := congrArg Fin.val he
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
      have := a.isLt
      omega
    · have hval := congrArg Fin.val he
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
      have := b.isLt
      omega
    · apply hf
      apply Fin.ext
      have hval := congrArg Fin.val he
      simpa using hval
  have hpS : ∀ a, pick a ∈ S := by
    intro a
    dsimp [pick]
    split_ifs with ha
    · exact ha
    · exact (hS a (f a) (hE a)).resolve_left ha
  calc
    p = (Finset.univ.image pick).card := by
      rw [Finset.card_image_of_injective _ hpick]
      simp
    _ ≤ S.card := Finset.card_le_card (by
      intro v hv
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hv
      exact hpS a)

lemma size_overhead_cancels {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : Fin p → Fin l) (hf : Function.Injective f) (hE : ∀ a, (a, f a) ∈ E)
    (s d : ℕ) (hd : d = s + p)
    (hbound : ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ d + 1) :
    E.card ≤ s + 1 := by
  obtain ⟨S, hS, hcard⟩ := hbound
  have hmatch := cover_card_of_matching E f hf hE S hS
  omega

end PEqualNP.Outside.L_meta_4675.MatchingConsequence
namespace PEqualNP.Outside.L_meta_4675.ReaderCharge

lemma nonstar_reader_shape {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A Q : Finset (Fin p)) (B P : Finset (Fin l))
    (hQ : 1 < Q.card) (hB : 1 < B.card)
    (hAQ : (A ∩ Q).Nonempty) (hP : P.Nonempty)
    (hbase : ∀ q ∈ Q, ∀ b ∈ P, (q, b) ∈ E)
    (hprod : ∀ a ∈ A, ∀ b ∈ B, ∀ q ∈ Q, (a, b) ∈ E ∨ (q, b) ∈ E)
    (hdirty : ∃ a ∈ A, ∃ b ∈ B, (a, b) ∉ E) :
    ∃ (b0 b1 : Fin l) (q0 : Fin p),
      b0 ≠ b1 ∧ P = {b0} ∧ B = {b0, b1} ∧ A ∩ Q = {q0} ∧
      (∀ a ∈ A, (a, b1) ∈ E) ∧ (∀ q ∈ Q, (q, b0) ∈ E) ∧
      (∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E ↔ b = b1 ∨ a = q0 ∧ b = b0) := by
  obtain ⟨a0, ha0, b0, hb0, hbad⟩ := hdirty
  obtain ⟨q0, hq0⟩ := hAQ
  obtain ⟨hq0A, hq0Q⟩ := Finset.mem_inter.mp hq0
  obtain ⟨q, hq, r, hr, hqr⟩ := Finset.one_lt_card.mp hQ
  have hQ0 : ∀ z ∈ Q, (z, b0) ∈ E := by
    intro z hz
    exact (hprod a0 ha0 b0 hb0 z hz).resolve_left hbad
  have hP0 : P = {b0} := by
    apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
    refine ⟨hP, ?_⟩
    intro b hb
    by_contra hbb
    exact hC4 q r b b0 hqr hbb
      ⟨hbase q hq b hb, hQ0 q hq, hbase r hr b hb, hQ0 r hr⟩
  have hother : ∀ b ∈ B, b ≠ b0 → ∀ a ∈ A, (a, b) ∈ E := by
    intro b hb hbb a ha
    by_contra hab
    have hqb := (hprod a ha b hb q hq).resolve_left hab
    have hrb := (hprod a ha b hb r hr).resolve_left hab
    exact hC4 q r b b0 hqr hbb ⟨hqb, hQ0 q hq, hrb, hQ0 r hr⟩
  have ha0q : a0 ≠ q0 := by
    intro he
    subst a0
    exact hbad (hQ0 q0 hq0Q)
  obtain ⟨b1, hb1, hb10⟩ : ∃ b1 ∈ B, b1 ≠ b0 := by
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hB
    by_cases hu0 : u = b0
    · exact ⟨v, hv, fun hv0 => huv (hu0.trans hv0.symm)⟩
    · exact ⟨u, hu, hu0⟩
  have hB01 : B = {b0, b1} := by
    apply Finset.Subset.antisymm
    · intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hb00 : b = b0
      · exact Or.inl hb00
      · right
        by_contra hb11
        exact hC4 a0 q0 b b1 ha0q hb11
          ⟨hother b hb hb00 a0 ha0, hother b1 hb1 hb10 a0 ha0,
            hother b hb hb00 q0 hq0A, hother b1 hb1 hb10 q0 hq0A⟩
    · exact Finset.insert_subset hb0 (Finset.singleton_subset_iff.mpr hb1)
  have hAQ0 : A ∩ Q = {q0} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_inter.mpr ⟨hq0A, hq0Q⟩, ?_⟩
    intro a ha
    obtain ⟨haA, haQ⟩ := Finset.mem_inter.mp ha
    by_contra haq
    exact hC4 a q0 b0 b1 haq hb10.symm
      ⟨hQ0 a haQ, hother b1 hb1 hb10 a haA,
        hQ0 q0 hq0Q, hother b1 hb1 hb10 q0 hq0A⟩
  refine ⟨b0, b1, q0, hb10.symm, hP0, hB01, hAQ0,
    hother b1 hb1 hb10, hQ0, ?_⟩
  intro a ha b hb
  constructor
  · intro hab
    have hbb : b = b0 ∨ b = b1 := by simpa [hB01] using hb
    rcases hbb with hb0eq | hb1eq
    · right
      refine ⟨?_, hb0eq⟩
      rw [hb0eq] at hab
      by_contra haq
      exact hC4 a q0 b0 b1 haq hb10.symm
        ⟨hab, hother b1 hb1 hb10 a ha,
          hQ0 q0 hq0Q, hother b1 hb1 hb10 q0 hq0A⟩
    · exact Or.inl hb1eq
  · rintro (hb1eq | ⟨haq, hb0eq⟩)
    · rw [hb1eq]
      exact hother b1 hb1 hb10 a ha
    · rw [haq, hb0eq]
      exact hQ0 q0 hq0Q

end PEqualNP.Outside.L_meta_4675.ReaderCharge
namespace PEqualNP.Outside.L_meta_4675.RestoreStar

def pairVal {α β : Type*} [DecidableEq α] [DecidableEq β]
    (a : α) (b : β) (v : α ⊕ β) : Bool :=
  decide (v = Sum.inl a ∨ v = Sum.inr b)

def graphValue {α β : Type*} (E : Finset (α × β)) (x : α ⊕ β → Bool) : Prop :=
  ∃ a b, (a, b) ∈ E ∧ x (Sum.inl a) = true ∧ x (Sum.inr b) = true

lemma pairVal_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (x : α ⊕ β → Bool) (a : α) (b : β)
    (ha : x (Sum.inl a) = true) (hb : x (Sum.inr b) = true) :
    ∀ v, pairVal a b v = true → x v = true := by
  intro v hv
  simp only [pairVal, decide_eq_true_eq] at hv
  rcases hv with hv | hv
  · simpa [hv] using ha
  · simpa [hv] using hb

lemma false_prune_restore_star {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (A : Finset α) (B : Finset β)
    (b0 b1 : β) (q0 : α) (F0 : (α ⊕ β → Bool) → Bool)
    (hmono : ∀ x y, (∀ v, x v = true → y v = true) →
      F0 x = true → F0 y = true)
    (hbelow : ∀ x, F0 x = true → graphValue E x)
    (houtside : ∀ a b, (a, b) ∈ E → (a ∉ A ∨ b ∉ B) →
      F0 (pairVal a b) = true)
    (hexception : F0 (pairVal q0 b0) = true)
    (hshape : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E →
      b = b1 ∨ a = q0 ∧ b = b0)
    (hcolumn : ∀ a ∈ A, (a, b1) ∈ E) :
    ∀ x, graphValue E x ↔
      F0 x = true ∨ (∃ a ∈ A, x (Sum.inl a) = true) ∧ x (Sum.inr b1) = true := by
  intro x
  constructor
  · rintro ⟨a, b, hab, hxa, hxb⟩
    by_cases ha : a ∈ A
    · by_cases hb : b ∈ B
      · rcases hshape a ha b hb hab with hb1 | ⟨ha0, hb0⟩
        · exact Or.inr ⟨⟨a, ha, hxa⟩, hb1 ▸ hxb⟩
        · apply Or.inl
          apply hmono (pairVal q0 b0) x
          · apply pairVal_le
            · simpa [ha0] using hxa
            · simpa [hb0] using hxb
          · exact hexception
      · exact Or.inl (hmono (pairVal a b) x (pairVal_le x a b hxa hxb)
          (houtside a b hab (Or.inr hb)))
    · exact Or.inl (hmono (pairVal a b) x (pairVal_le x a b hxa hxb)
        (houtside a b hab (Or.inl ha)))
  · rintro (hx | ⟨⟨a, ha, hxa⟩, hxb⟩)
    · exact hbelow x hx
    · exact ⟨a, b1, hcolumn a ha, hxa, hxb⟩

end PEqualNP.Outside.L_meta_4675.RestoreStar
namespace PEqualNP.Outside.L_meta_4675.SameColourCharge

lemma same_colour_reader_family {p l : ℕ} {ι : Type*}
    (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A B : Finset (Fin p)) (Q : ι → Finset (Fin l))
    (hI : 1 < (A ∩ B).card) (hne : ∃ r, (Q r).Nonempty)
    (hprod : ∀ r, ∀ a ∈ A, ∀ c ∈ B, ∀ q ∈ Q r,
      (a, q) ∈ E ∨ (c, q) ∈ E) :
    ∃ b : Fin l, (∀ r, Q r ⊆ {b}) ∧
      ((∀ a ∈ A, (a, b) ∈ E) ∨ (∀ c ∈ B, (c, b) ∈ E)) := by
  classical
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hI
  obtain ⟨huA, huB⟩ := Finset.mem_inter.mp hu
  obtain ⟨hvA, hvB⟩ := Finset.mem_inter.mp hv
  obtain ⟨r0, b, hb⟩ := hne
  have hrowu : ∀ r, ∀ q ∈ Q r, (u, q) ∈ E := by
    intro r q hq
    exact (hprod r u huA u huB q hq).elim id id
  have hrowv : ∀ r, ∀ q ∈ Q r, (v, q) ∈ E := by
    intro r q hq
    exact (hprod r v hvA v hvB q hq).elim id id
  refine ⟨b, ?_, ?_⟩
  · intro r q hq
    apply Finset.mem_singleton.mpr
    by_contra hqb
    exact hC4 u v q b huv hqb
      ⟨hrowu r q hq, hrowu r0 b hb, hrowv r q hq, hrowv r0 b hb⟩
  · by_cases hA : ∀ a ∈ A, (a, b) ∈ E
    · exact Or.inl hA
    · push_neg at hA
      obtain ⟨a, ha, hbad⟩ := hA
      exact Or.inr (fun c hc => (hprod r0 a ha c hc b hb).resolve_left hbad)

end PEqualNP.Outside.L_meta_4675.SameColourCharge
namespace PEqualNP.Outside.L_meta_4675.OneJunkGraph

lemma two_column_edges {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (q : Fin p) (b₀ b₁ : Fin l)
    (hq : q ∈ A) (hb : b₀ ≠ b₁)
    (hstar : ∀ a ∈ A, (a, b₁) ∈ E) (hex : (q, b₀) ∈ E) :
    E ∩ (A ×ˢ {b₀, b₁}) = (A ×ˢ {b₁}) ∪ {(q, b₀)} := by
  ext ⟨a, b⟩
  simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_union]
  constructor
  · rintro ⟨he, ha, hb' | hb'⟩
    · subst b
      have haq : a = q := by
        by_contra hne
        exact hC4 a q b₀ b₁ hne hb ⟨he, hstar a ha, hex, hstar q hq⟩
      exact Or.inr (by simp [haq])
    · exact Or.inl ⟨ha, hb'⟩
  · rintro (⟨ha, hb'⟩ | hab)
    · subst b
      exact ⟨hstar a ha, ha, Or.inr rfl⟩
    · cases hab
      exact ⟨hex, hq, Or.inl rfl⟩

lemma cross_triples_iff {p l : ℕ} (E : Finset (Fin p × Fin l))
    (A Q : Finset (Fin p)) (B : Finset (Fin l)) :
    (∀ a ∈ A, ∀ b ∈ B, ∀ q ∈ Q, (a, b) ∈ E ∨ (q, b) ∈ E) ↔
      ∀ b ∈ B, (∀ a ∈ A, (a, b) ∈ E) ∨ (∀ q ∈ Q, (q, b) ∈ E) := by
  classical
  constructor
  · intro h b hb
    by_cases hA : ∀ a ∈ A, (a, b) ∈ E
    · exact Or.inl hA
    · right
      push Not at hA
      obtain ⟨a, ha, hab⟩ := hA
      intro q hq
      exact (h a ha b hb q hq).resolve_left hab
  · intro h a ha b hb q hq
    rcases h b hb with hA | hQ
    · exact Or.inl (hA a ha)
    · exact Or.inr (hQ q hq)

end PEqualNP.Outside.L_meta_4675.OneJunkGraph
namespace PEqualNP.Outside.L_meta_4675.Pruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour

def step (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

def vals (gs : List Gate) (xs : List Bool) : List Bool := gs.foldl step xs

def optionalValue (ws : List Bool) (o : Option ℕ) : Bool :=
  o.elim false (fun i => ws.getD i false)

def pairOp (a : Bool) (x y : Bool) : Bool := if a then x && y else x || y

def pairGate (a : Bool) (i j : ℕ) : Gate :=
  ⟨if a then GateOp.and else GateOp.or, [i, j]⟩

def emitPair (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ) : List Gate × Option ℕ :=
  match x, y with
  | some i, some j => (gs ++ [pairGate a i j], some (n + gs.length))
  | some i, none => (gs, if a then none else some i)
  | none, some j => (gs, if a then none else some j)
  | none, none => (gs, none)

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def compileStep (n q : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) :
    List Gate × List (Option ℕ) :=
  if s.2.length = n + q then (s.1, s.2 ++ [none])
  else
    let r := emitPair n s.1 (isAnd g.op)
      (s.2.getD (g.inputs.getD 0 0) none) (s.2.getD (g.inputs.getD 1 0) none)
    (r.1, s.2 ++ [r.2])

def initial (n : ℕ) : List Gate × List (Option ℕ) := ([], (List.range n).map some)

def compiled (n q : ℕ) (gs : List Gate) : List Gate × List (Option ℕ) :=
  gs.foldl (compileStep n q) (initial n)

def forceStep (n q : ℕ) (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [if ws.length = n + q then false else g.op.eval (g.inputs.map fun i => ws.getD i false)]

def forcedValues (n q : ℕ) (C : Circuit) (xs : List Bool) : List Bool :=
  C.gates.foldl (forceStep n q) xs

def pruned (n q : ℕ) (C : Circuit) : Circuit :=
  let s := compiled n q C.gates
  ⟨s.1, (s.2.getD C.output none).getD (n + s.1.length)⟩

def Bounded (n : ℕ) (gs : List Gate) (o : Option ℕ) : Prop :=
  ∀ i, o = some i → i < n + gs.length

def Valid (n : ℕ) (s : List Gate × List (Option ℕ)) : Prop :=
  IsAO2 n ⟨s.1, 0⟩ ∧ ∀ o ∈ s.2, Bounded n s.1 o

def Related (xs old : List Bool) (s : List Gate × List (Option ℕ)) : Prop :=
  s.2.length = old.length ∧
    ∀ i, optionalValue (vals s.1 xs) (s.2.getD i none) = old.getD i false

lemma vals_length (gs : List Gate) (xs : List Bool) : (vals gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [vals]
  | cons g gs ih =>
    simp only [vals, List.foldl_cons] at *
    rw [ih]
    simp [step]
    omega

lemma vals_append (gs hs : List Gate) (xs : List Bool) : vals (gs ++ hs) xs = vals hs (vals gs xs) := by
  simp [vals, List.foldl_append]

lemma vals_snoc (gs : List Gate) (g : Gate) (xs : List Bool) : vals (gs ++ [g]) xs = step (vals gs xs) g := by
  rw [vals_append]
  rfl

lemma getD_append_lt {α : Type*} (ws ys : List α) (i : ℕ) (d : α) (hi : i < ws.length) :
    (ws ++ ys).getD i d = ws.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_last {α : Type*} (ws : List α) (x d : α) :
    (ws ++ [x]).getD ws.length d = x := by simp [List.getD_eq_getElem?_getD]

lemma getD_ge {α : Type*} (ws : List α) (i : ℕ) (d : α) (hi : ws.length ≤ i) : ws.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma pairGate_eval (a x y : Bool) : (pairGate a 0 1).op.eval [x, y] = pairOp a x y := by
  cases a <;> cases x <;> cases y <;> rfl

lemma emitPair_length_le (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ) :
    (emitPair n gs a x y).1.length ≤ gs.length + 1 := by
  cases x <;> cases y <;> simp [emitPair]

lemma emitPair_prefix (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ)
    (xs : List Bool) (hx : xs.length = n) (i : ℕ) (hi : i < n + gs.length) :
    (vals (emitPair n gs a x y).1 xs).getD i false = (vals gs xs).getD i false := by
  cases x <;> cases y <;> simp only [emitPair]
  rw [vals_snoc]
  exact getD_append_lt _ _ _ _ (by rw [vals_length, hx]; exact hi)

lemma emitPair_optional_prefix (n : ℕ) (gs : List Gate) (a : Bool) (x y o : Option ℕ)
    (xs : List Bool) (hx : xs.length = n) (ho : Bounded n gs o) :
    optionalValue (vals (emitPair n gs a x y).1 xs) o = optionalValue (vals gs xs) o := by
  cases o with
  | none => rfl
  | some i => exact emitPair_prefix n gs a x y xs hx i (ho i rfl)

lemma emitPair_semantics (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ)
    (xs : List Bool) (hx : xs.length = n) :
    optionalValue (vals (emitPair n gs a x y).1 xs) (emitPair n gs a x y).2 =
      pairOp a (optionalValue (vals gs xs) x) (optionalValue (vals gs xs) y) := by
  cases x with
  | none => cases y <;> cases a <;> simp [emitPair, optionalValue, pairOp]
  | some i =>
    cases y with
    | none => cases a <;> simp [emitPair, optionalValue, pairOp]
    | some j =>
      simp only [emitPair, optionalValue, Option.elim_some, vals_snoc, step]
      have hl : (vals gs xs).length = n + gs.length := by rw [vals_length, hx]
      rw [← hl, getD_append_last]
      cases a <;> simp [pairGate, pairOp, GateOp.eval]

lemma emitPair_bounded (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ)
    (hx : Bounded n gs x) (hy : Bounded n gs y) :
    Bounded n (emitPair n gs a x y).1 (emitPair n gs a x y).2 := by
  cases x <;> cases y <;> cases a <;> simp_all [emitPair, Bounded]

lemma bounded_getD (n : ℕ) (s : List Gate × List (Option ℕ))
    (h : ∀ o ∈ s.2, Bounded n s.1 o) (i : ℕ) : Bounded n s.1 (s.2.getD i none) := by
  by_cases hi : i < s.2.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact h s.2[i] (List.getElem_mem hi)
  · rw [getD_ge _ _ _ (by omega)]
    simp [Bounded]

lemma gateAt_snoc_old (gs : List Gate) (g : Gate) (j : ℕ) (hj : j < gs.length) :
    gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := getD_append_lt gs [g] j _ hj

lemma gateAt_snoc_last (gs : List Gate) (g : Gate) :
    gateAt ⟨gs ++ [g], 0⟩ gs.length = g := getD_append_last gs g _

lemma append_pair_ao (n : ℕ) (gs : List Gate) (h : IsAO2 n ⟨gs, 0⟩)
    (a : Bool) (i j : ℕ) (hi : i < n + gs.length) (hj : j < n + gs.length) :
    IsAO2 n ⟨gs ++ [pairGate a i j], 0⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rw [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h.1 g hg
    · cases a <;> simp [pairGate]
  · intro k hk w hw
    have hkl : k < gs.length + 1 := by simpa using hk
    by_cases hkold : k < gs.length
    · rw [gateAt_snoc_old gs _ k hkold] at hw
      exact h.2.1 k hkold w hw
    · have hke : k = gs.length := by omega
      subst k
      rw [gateAt_snoc_last] at hw
      simp only [pairGate, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> assumption
  · intro g hg
    rw [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h.2.2 g hg
    · rfl

lemma emitPair_ao (n : ℕ) (gs : List Gate) (h : IsAO2 n ⟨gs, 0⟩)
    (a : Bool) (x y : Option ℕ) (hx : Bounded n gs x) (hy : Bounded n gs y) :
    IsAO2 n ⟨(emitPair n gs a x y).1, 0⟩ := by
  cases x with
  | none => cases y <;> exact h
  | some i =>
    cases y with
    | none => exact h
    | some j => exact append_pair_ao n gs h a i j (hx i rfl) (hy j rfl)

lemma emitPair_length_ge (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ) :
    gs.length ≤ (emitPair n gs a x y).1.length := by
  cases x <;> cases y <;> simp [emitPair]

lemma compileStep_map_length (n q : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) :
    (compileStep n q s g).2.length = s.2.length + 1 := by
  unfold compileStep
  split_ifs <;> simp

lemma compileStep_size (n q : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) :
    (compileStep n q s g).1.length ≤ s.1.length + 1 := by
  unfold compileStep
  split_ifs
  · simp
  · exact emitPair_length_le _ _ _ _ _

lemma compileStep_valid (n q : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) (hs : Valid n s) :
    Valid n (compileStep n q s g) := by
  have h0 := bounded_getD n s hs.2 (g.inputs.getD 0 0)
  have h1 := bounded_getD n s hs.2 (g.inputs.getD 1 0)
  unfold compileStep
  split_ifs <;> dsimp only [Valid]
  · refine ⟨hs.1, ?_⟩
    intro o ho
    rw [List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · exact hs.2 o ho
    · simp [Bounded]
  · refine ⟨emitPair_ao _ _ hs.1 _ _ _ h0 h1, ?_⟩
    intro o ho
    rw [List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · intro i hi
      have hb := hs.2 o ho i hi
      have hl := emitPair_length_ge n s.1 (isAnd g.op)
        (s.2.getD (g.inputs.getD 0 0) none) (s.2.getD (g.inputs.getD 1 0) none)
      omega
    · exact emitPair_bounded _ _ _ _ _ h0 h1

lemma form_eval (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length = 2) (ws : List Bool) :
    g.op.eval (g.inputs.map fun i => ws.getD i false) =
      pairOp (isAnd g.op) (ws.getD (g.inputs.getD 0 0) false)
        (ws.getD (g.inputs.getD 1 0) false) := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rcases hop with hop | hop <;> simp [hop, hab, GateOp.eval, pairOp, isAnd]

lemma related_extend (xs old : List Bool) (gs : List Gate) (m : List (Option ℕ))
    (o : Option ℕ) (v : Bool) (hl : m.length = old.length)
    (hprior : ∀ i, optionalValue (vals gs xs) (m.getD i none) = old.getD i false)
    (hlast : optionalValue (vals gs xs) o = v) :
    Related xs (old ++ [v]) (gs, m ++ [o]) := by
  refine ⟨by simp [hl], ?_⟩
  intro i
  change optionalValue (vals gs xs) ((m ++ [o]).getD i none) = (old ++ [v]).getD i false
  rcases Nat.lt_trichotomy i m.length with hi | hi | hi
  · rw [getD_append_lt m [o] i none hi, getD_append_lt old [v] i false (by omega)]
    exact hprior i
  · subst i
    rw [getD_append_last, hl, getD_append_last]
    exact hlast
  · rw [getD_ge _ _ _ (by simp; omega), getD_ge _ _ _ (by simp; omega)]
    rfl

lemma compileStep_related (n q : ℕ) (xs old : List Bool) (hx : xs.length = n)
    (s : List Gate × List (Option ℕ)) (hs : Valid n s) (hr : Related xs old s)
    (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2) :
    Related xs (forceStep n q old g) (compileStep n q s g) := by
  by_cases hkill : s.2.length = n + q
  · have hold : old.length = n + q := by rw [← hr.1]; exact hkill
    simp only [compileStep, hkill, ↓reduceIte, forceStep, hold]
    exact related_extend xs old s.1 s.2 none false hr.1 hr.2 rfl
  · have hold : old.length ≠ n + q := by rw [← hr.1]; exact hkill
    simp only [compileStep, hkill, ↓reduceIte, forceStep, hold]
    apply related_extend xs old _ s.2 _ _ hr.1
    · intro i
      rw [emitPair_optional_prefix n s.1 (isAnd g.op) _ _ _ xs hx (bounded_getD n s hs.2 i)]
      exact hr.2 i
    · rw [emitPair_semantics n s.1 (isAnd g.op) _ _ xs hx, hr.2, hr.2]
      exact (form_eval g hop hlen old).symm

lemma initial_valid (n : ℕ) : Valid n (initial n) := by
  refine ⟨?_, ?_⟩
  · simp [initial, IsAO2, PEqualNP.EdgeOwnership.AndOrOnly, ReadsBack]
  · intro o ho
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ho
    have hin := List.mem_range.mp hi
    simpa [Bounded, initial] using hin

lemma initial_related (n : ℕ) (xs : List Bool) (hx : xs.length = n) : Related xs xs (initial n) := by
  refine ⟨by simp [initial, hx], ?_⟩
  intro i
  by_cases hi : i < n
  · simp [initial, vals, List.getD_eq_getElem?_getD, hi, optionalValue]
  · have hn : n ≤ i := by omega
    simp [initial, vals, List.getD_eq_getElem?_getD, hi, hx, optionalValue]

lemma fold_valid_related (n q : ℕ) (xs old : List Bool) (hx : xs.length = n)
    (gs : List Gate) (hform : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (s : List Gate × List (Option ℕ)) (hs : Valid n s) (hr : Related xs old s) :
    Valid n (gs.foldl (compileStep n q) s) ∧
      Related xs (gs.foldl (forceStep n q) old) (gs.foldl (compileStep n q) s) := by
  induction gs generalizing s old with
  | nil => exact ⟨hs, hr⟩
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hform g (by simp)
    exact ih (forceStep n q old g) (fun h hh => hform h (by simp [hh])) (compileStep n q s g)
      (compileStep_valid n q s g hs) (compileStep_related n q xs old hx s hs hr g hop hlen)

lemma compiled_valid_related (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (xs : List Bool) (hx : xs.length = n) :
    Valid n (compiled n q C.gates) ∧ Related xs (forcedValues n q C xs) (compiled n q C.gates) := by
  exact fold_valid_related n q xs xs hx C.gates
    (fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩) (initial n) (initial_valid n) (initial_related n xs hx)

lemma optionalValue_lookup (n : ℕ) (gs : List Gate) (xs : List Bool) (hx : xs.length = n)
    (o : Option ℕ) :
    (vals gs xs).getD (o.getD (n + gs.length)) false = optionalValue (vals gs xs) o := by
  cases o with
  | none =>
    change (vals gs xs).getD (n + gs.length) false = false
    exact getD_ge _ _ _ (by rw [vals_length, hx])
  | some i => rfl

lemma pruned_eval (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) (xs : List Bool) (hx : xs.length = n) :
    (pruned n q C).eval xs = (forcedValues n q C xs).getD C.output false := by
  have h := (compiled_valid_related n q C hAO xs hx).2.2 C.output
  change (vals (compiled n q C.gates).1 xs).getD
    (((compiled n q C.gates).2.getD C.output none).getD (n + (compiled n q C.gates).1.length)) false = _
  rw [optionalValue_lookup n _ xs hx]
  exact h

lemma pruned_ao (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) : IsAO2 n (pruned n q C) := by
  have h := (compiled_valid_related n q C hAO (List.replicate n false) (by simp)).1.1
  exact h

lemma compileStep_map_prior (n q : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate)
    (i : ℕ) (hi : i < s.2.length) :
    (compileStep n q s g).2.getD i none = s.2.getD i none := by
  unfold compileStep
  split_ifs <;> exact getD_append_lt _ _ _ _ hi

lemma fold_map_length (n q : ℕ) (gs : List Gate) (s : List Gate × List (Option ℕ)) :
    (gs.foldl (compileStep n q) s).2.length = s.2.length + gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, compileStep_map_length]
    simp [List.length_cons]
    omega

lemma fold_size_le (n q : ℕ) (gs : List Gate) (s : List Gate × List (Option ℕ)) :
    (gs.foldl (compileStep n q) s).1.length ≤ s.1.length + gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hh := ih (compileStep n q s g)
    have hs := compileStep_size n q s g
    simp only [List.length_cons]
    omega

lemma fold_map_prior (n q : ℕ) (gs : List Gate) (s : List Gate × List (Option ℕ))
    (i : ℕ) (hi : i < s.2.length) :
    (gs.foldl (compileStep n q) s).2.getD i none = s.2.getD i none := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (compileStep n q s g) (by rw [compileStep_map_length]; omega)]
    exact compileStep_map_prior n q s g i hi

lemma compiled_map_length (n q : ℕ) (gs : List Gate) :
    (compiled n q gs).2.length = n + gs.length := by
  rw [compiled, fold_map_length]
  simp [initial]

lemma compiled_size_le (n q : ℕ) (gs : List Gate) : (compiled n q gs).1.length ≤ gs.length := by
  simpa [compiled, initial] using fold_size_le n q gs (initial n)

lemma compiled_split (n q : ℕ) (gs : List Gate) (k : ℕ) :
    compiled n q gs = (gs.drop k).foldl (compileStep n q) (compiled n q (gs.take k)) := by
  unfold compiled
  rw [← List.foldl_append, List.take_append_drop]

lemma compiled_take_succ (n q : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    compiled n q (gs.take (j + 1)) = compileStep n q (compiled n q (gs.take j)) gs[j] := by
  unfold compiled
  rw [List.take_succ_eq_append_getElem hj, List.foldl_append]
  rfl

lemma forced_step (n q : ℕ) (gs : List Gate) (hq : q < gs.length) :
    compiled n q (gs.take (q + 1)) =
      ((compiled n q (gs.take q)).1, (compiled n q (gs.take q)).2 ++ [none]) := by
  rw [compiled_take_succ n q gs q hq]
  have hl : (compiled n q (gs.take q)).2.length = n + q := by
    rw [compiled_map_length, List.length_take, Nat.min_eq_left (by omega)]
  simp [compileStep, hl]

lemma killed_alias (n q : ℕ) (gs : List Gate) (hq : q < gs.length) :
    (compiled n q gs).2.getD (n + q) none = none := by
  rw [compiled_split n q gs (q + 1)]
  have hl : n + q < (compiled n q (gs.take (q + 1))).2.length := by
    rw [compiled_map_length, List.length_take, Nat.min_eq_left (by omega)]
    omega
  rw [fold_map_prior n q (gs.drop (q + 1)) _ (n + q) hl, forced_step n q gs hq]
  have hlq : (compiled n q (gs.take q)).2.length = n + q := by
    rw [compiled_map_length, List.length_take, Nat.min_eq_left (by omega)]
  change ((compiled n q (gs.take q)).2 ++ [none]).getD (n + q) none = none
  rw [← hlq, getD_append_last]

lemma emitPair_drop (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ)
    (h : x = none ∨ y = none) : (emitPair n gs a x y).1 = gs := by
  rcases h with rfl | rfl
  · cases y <;> rfl
  · cases x <;> rfl

lemma compileStep_drop_missing (n q : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate)
    (w : ℕ) (hw : w ∈ g.inputs) (hlen : g.inputs.length = 2) (hnone : s.2.getD w none = none) :
    (compileStep n q s g).1 = s.1 := by
  unfold compileStep
  split_ifs
  · rfl
  · apply emitPair_drop
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    simp only [hab, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl (by simpa [hab] using hnone)
    · exact Or.inr (by simpa [hab] using hnone)

lemma reader_step_drop (n q r : ℕ) (gs : List Gate) (hqr : q < r) (hr : r < gs.length)
    (hread : n + q ∈ gs[r].inputs) (hlen : gs[r].inputs.length = 2) :
    (compiled n q (gs.take (r + 1))).1 = (compiled n q (gs.take r)).1 := by
  rw [compiled_take_succ n q gs r hr]
  apply compileStep_drop_missing n q _ gs[r] (n + q) hread hlen
  exact killed_alias n q (gs.take r) (by simp [List.length_take]; omega)

lemma count_two_skips (f : ℕ → ℕ) (N q r : ℕ) (hqr : q < r) (hr : r < N)
    (hzero : f 0 = 0) (hstep : ∀ j < N, f (j + 1) ≤ f j + 1)
    (hqdrop : f (q + 1) = f q) (hrdrop : f (r + 1) = f r) : f N + 2 ≤ N := by
  have hinterval : ∀ a d, a + d ≤ N → f (a + d) ≤ f a + d := by
    intro a d
    induction d with
    | zero => simp
    | succ d ih =>
      intro hd
      have hi := ih (by omega)
      have hs := hstep (a + d) (by omega)
      have he : a + (d + 1) = (a + d) + 1 := by omega
      rw [he]
      omega
  have h0q := hinterval 0 q (by omega)
  have hqr' := hinterval (q + 1) (r - (q + 1)) (by omega)
  have hrN := hinterval (r + 1) (N - (r + 1)) (by omega)
  have heq : q + 1 + (r - (q + 1)) = r := by omega
  have her : r + 1 + (N - (r + 1)) = N := by omega
  rw [heq, hqdrop] at hqr'
  rw [her, hrdrop] at hrN
  simp only [zero_add, hzero] at h0q
  omega

lemma pruned_size_two (n q r : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hqr : q < r) (hr : r < C.gates.length) (hread : n + q ∈ C.gates[r].inputs) :
    (pruned n q C).size + 2 ≤ C.size := by
  have hlen := hAO.2.2 C.gates[r] (List.getElem_mem hr)
  have h := count_two_skips (fun j => (compiled n q (C.gates.take j)).1.length)
    C.gates.length q r hqr hr (by simp [compiled, initial]) ?_ ?_ ?_
  · simpa [pruned, Circuit.size] using h
  · intro j hj
    rw [compiled_take_succ n q C.gates j hj]
    exact compileStep_size n q _ C.gates[j]
  · rw [forced_step n q C.gates (by omega)]
  · rw [reader_step_drop n q r C.gates hqr hr hread hlen]

end PEqualNP.Outside.L_meta_4675.Pruning
