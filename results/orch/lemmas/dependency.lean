import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_3451_aux.Dependency

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

def support (n : ℕ) (C : Circuit) : Finset (Fin n) :=
  (suppsFrom C.gates (inputSupps n)).getD C.output ∅

lemma support_card (n : ℕ) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) : (support n C).card ≤ C.size + 1 := by
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) hfan cnt_inputs {C.output}
  simpa [support, Circuit.size] using hc

lemma agree_support (n : ℕ) (C : Circuit) (x y : Fin n → Bool)
    (h : ∀ i ∈ support n C, x i = y i) : circuitFun n C x = circuitFun n C y := by
  exact (agree_wiresFrom x y C.gates _ _ _ (agree_inputs _ _)).2.2 C.output h

lemma essential_card_le (n : ℕ) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (S : Finset (Fin n))
    (hdep : ∀ i ∈ S, ∃ x : Fin n → Bool,
      circuitFun n C (Function.update x i (!x i)) ≠ circuitFun n C x) :
    S.card ≤ C.size + 1 := by
  have hsub : S ⊆ support n C := by
    intro i hi
    by_contra hnot
    obtain ⟨x, hx⟩ := hdep i hi
    apply hx
    apply agree_support
    intro k hk
    have hki : k ≠ i := by
      intro he
      exact hnot (he ▸ hk)
    simp [Function.update_of_ne hki]
  exact (Finset.card_le_card hsub).trans (support_card n C hfan)

lemma all_inputs_lower (n : ℕ) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool,
      circuitFun n C (Function.update x i (!x i)) ≠ circuitFun n C x) :
    n ≤ C.size + 1 := by
  have h := essential_card_le n C hfan Finset.univ (fun i _ => hdep i)
  simpa using h

def activePoints (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] : Finset (Fin N) :=
  Finset.univ.filter (fun p => ∃ l, I p l)

def activeLines (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] : Finset (Fin N) :=
  Finset.univ.filter (fun l => ∃ p, I p l)

def activeInputs (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] : Finset (Fin (N + N)) :=
  (activePoints N I).image (Fin.castAdd N) ∪ (activeLines N I).image (Fin.natAdd N)

lemma point_ne_line {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma activeInputs_card (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] :
    (activeInputs N I).card = (activePoints N I).card + (activeLines N I).card := by
  have hp : Function.Injective (Fin.castAdd N : Fin N → Fin (N + N)) := by
    intro a b h
    have hv := congrArg (fun k : Fin (N + N) => k.val) h
    exact Fin.ext hv
  have hl : Function.Injective (Fin.natAdd N : Fin N → Fin (N + N)) := by
    intro a b h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd] at hv
    omega
  have hd : Disjoint ((activePoints N I).image (Fin.castAdd N))
      ((activeLines N I).image (Fin.natAdd N)) := by
    apply Finset.disjoint_left.mpr
    intro k hkP hkL
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hkP
    obtain ⟨l, _, he⟩ := Finset.mem_image.mp hkL
    exact point_ne_line p l he.symm
  rw [activeInputs, Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ hp, Finset.card_image_of_injective _ hl]

lemma incident_point_essential (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (p l : Fin N) (hI : I p l) :
    ∃ x : Fin (N + N) → Bool,
      circuitFun (N + N) C (Function.update x (Fin.castAdd N p) (!x (Fin.castAdd N p))) ≠
        circuitFun (N + N) C x := by
  let x : Fin (N + N) → Bool := fun k => decide (k = Fin.natAdd N l)
  have hx : x (Fin.castAdd N p) = false := by
    simp only [x, decide_eq_false_iff_not]
    exact point_ne_line p l
  have hf : circuitFun (N + N) C x = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨q, m, _, hq, _⟩ := (hfun x).mp h
    have he : Fin.castAdd N q = Fin.natAdd N l := of_decide_eq_true hq
    exact point_ne_line q l he
  have ht : circuitFun (N + N) C (Function.update x (Fin.castAdd N p) (!x (Fin.castAdd N p))) = true := by
    apply (hfun _).mpr
    refine ⟨p, l, hI, ?_, ?_⟩
    · rw [Function.update_self, hx]
      rfl
    · rw [Function.update_of_ne (point_ne_line p l).symm]
      simp [x]
  exact ⟨x, by rw [ht, hf]; decide⟩

lemma incident_line_essential (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (p l : Fin N) (hI : I p l) :
    ∃ x : Fin (N + N) → Bool,
      circuitFun (N + N) C (Function.update x (Fin.natAdd N l) (!x (Fin.natAdd N l))) ≠
        circuitFun (N + N) C x := by
  let x : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p)
  have hx : x (Fin.natAdd N l) = false := by
    simp only [x, decide_eq_false_iff_not]
    exact (point_ne_line p l).symm
  have hf : circuitFun (N + N) C x = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨q, m, _, _, hm⟩ := (hfun x).mp h
    have he : Fin.natAdd N m = Fin.castAdd N p := of_decide_eq_true hm
    exact point_ne_line p m he.symm
  have ht : circuitFun (N + N) C (Function.update x (Fin.natAdd N l) (!x (Fin.natAdd N l))) = true := by
    apply (hfun _).mpr
    refine ⟨p, l, hI, ?_, ?_⟩
    · rw [Function.update_of_ne (point_ne_line p l)]
      simp [x]
    · rw [Function.update_self, hx]
      rfl
  exact ⟨x, by rw [ht, hf]; decide⟩

lemma incidence_active_bound (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    (activePoints N I).card + (activeLines N I).card ≤ C.size + 1 := by
  rw [← activeInputs_card]
  apply essential_card_le (N + N) C hfan
  intro k hk
  rcases Finset.mem_union.mp hk with hk | hk
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨l, hI⟩ := (Finset.mem_filter.mp hp).2
    exact incident_point_essential N I C hfun p l hI
  · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨p, hI⟩ := (Finset.mem_filter.mp hl).2
    exact incident_line_essential N I C hfun p l hI

lemma active_sides_bound (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    (activePoints N I).card ≤ C.size ∧ (activeLines N I).card ≤ C.size := by
  by_cases hI : ∃ p l, I p l
  · obtain ⟨p, l, hpl⟩ := hI
    have hp : 0 < (activePoints N I).card := by
      apply Finset.card_pos.mpr
      refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      exact ⟨l, hpl⟩
    have hl : 0 < (activeLines N I).card := by
      apply Finset.card_pos.mpr
      refine ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      exact ⟨p, hpl⟩
    have h := incidence_active_bound N I C hfan hfun
    omega
  · have hn : ∀ p l, ¬ I p l := by
      intro p l hpl
      exact hI ⟨p, l, hpl⟩
    simp [activePoints, activeLines, hn]

end PEqualNP.Outside.L_meta_3451_aux.Dependency
