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

end PEqualNP.Outside.L_meta_4675.MatchingBank

namespace PEqualNP.Outside.L_meta_4675.MatchingBank

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma append_update_right {n m : ℕ} (x : Fin n → Bool) (b : Fin m → Bool) (i : Fin m) (v : Bool) :
    Function.update (Fin.addCases x b : Fin (n + m) → Bool) (Fin.natAdd n i) v =
      Fin.addCases x (Function.update b i v) := by
  funext k
  refine Fin.addCases (m := n) (n := m) (fun j => ?_) (fun j => ?_) k
  · have he := cast_ne_nat j i
    simp [he]
  · have he : Fin.natAdd n j = Fin.natAdd n i ↔ j = i := by
      simp [Fin.ext_iff]
    simp [Function.update_apply, he]

lemma fin_other {r : ℕ} (hr : 2 ≤ r) (i : Fin r) : ∃ j : Fin r, j ≠ i := by
  by_cases hi : i.val = 0
  · refine ⟨⟨1, by omega⟩, ?_⟩
    intro he
    have hv := congrArg Fin.val he
    dsimp at hv
    omega
  · refine ⟨⟨0, by omega⟩, ?_⟩
    intro he
    have hv := congrArg Fin.val he
    dsimp at hv
    omega

def matchingFun {r : ℕ} (x : Fin (r + r) → Bool) : Bool :=
  decide (∃ i : Fin r, x (Fin.castAdd r i) = true ∧ x (Fin.natAdd r i) = true)

def sideBank {r : ℕ} (x : Fin (r + r) → Bool) (q : Fin 2) : Bool :=
  if q = 0 then decide (∃ i : Fin r, x (Fin.castAdd r i) = true)
  else decide (∃ i : Fin r, x (Fin.natAdd r i) = true)

lemma bank_all_true {r : ℕ} {x : Fin (r + r) → Bool}
    (ha : ∃ i : Fin r, x (Fin.castAdd r i) = true)
    (hb : ∃ i : Fin r, x (Fin.natAdd r i) = true) :
    sideBank x = fun _ => true := by
  funext q
  unfold sideBank
  split
  · exact decide_eq_true_eq.mpr ha
  · exact decide_eq_true_eq.mpr hb

lemma matching_singletons_off {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    matchingFun (Fin.addCases (fun a : Fin r => decide (a = i))
      (fun b : Fin r => decide (b = j))) = false := by
  unfold matchingFun
  apply decide_eq_false_iff_not.mpr
  rintro ⟨a, ha, hb⟩
  simp only [Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq] at ha hb
  exact hij (ha.symm.trans hb)

lemma matching_point_witness {r : ℕ} (hr : 2 ≤ r) (i : Fin r) :
    ∃ x : Fin (r + r) → Bool,
      matchingFun (Function.update x (Fin.castAdd r i) (!x (Fin.castAdd r i))) ≠ matchingFun x ∧
      sideBank (Function.update x (Fin.castAdd r i) (!x (Fin.castAdd r i))) = sideBank x := by
  obtain ⟨j, hji⟩ := fin_other hr i
  let x : Fin (r + r) → Bool := Fin.addCases (fun a : Fin r => decide (a = j))
    (fun b : Fin r => decide (b = i))
  let y : Fin (r + r) → Bool := Fin.addCases
    (Function.update (fun a : Fin r => decide (a = j)) i true)
    (fun b : Fin r => decide (b = i))
  have hxi : x (Fin.castAdd r i) = false := by simp [x, Ne.symm hji]
  have he : Function.update x (Fin.castAdd r i) (!x (Fin.castAdd r i)) = y := by
    rw [hxi]
    exact append_update _ _ _ _
  have hya : y (Fin.castAdd r i) = true := by simp [y]
  have hyb : y (Fin.natAdd r i) = true := by
    simp only [y, Fin.addCases_right, decide_true]
  have hxoff : matchingFun x = false := matching_singletons_off j i hji
  have hyon : matchingFun y = true := decide_eq_true_eq.mpr ⟨i, hya, hyb⟩
  have hbx : sideBank x = fun _ => true :=
    bank_all_true ⟨j, by simp only [x, Fin.addCases_left, decide_true]⟩
      ⟨i, by simp only [x, Fin.addCases_right, decide_true]⟩
  have hby : sideBank y = fun _ => true := bank_all_true ⟨i, hya⟩ ⟨i, hyb⟩
  refine ⟨x, ?_, ?_⟩
  · rw [he, hxoff, hyon]
    decide
  · rw [he, hbx, hby]

lemma matching_line_witness {r : ℕ} (hr : 2 ≤ r) (i : Fin r) :
    ∃ x : Fin (r + r) → Bool,
      matchingFun (Function.update x (Fin.natAdd r i) (!x (Fin.natAdd r i))) ≠ matchingFun x ∧
      sideBank (Function.update x (Fin.natAdd r i) (!x (Fin.natAdd r i))) = sideBank x := by
  obtain ⟨j, hji⟩ := fin_other hr i
  let x : Fin (r + r) → Bool := Fin.addCases (fun a : Fin r => decide (a = i))
    (fun b : Fin r => decide (b = j))
  let y : Fin (r + r) → Bool := Fin.addCases (fun a : Fin r => decide (a = i))
    (Function.update (fun b : Fin r => decide (b = j)) i true)
  have hxi : x (Fin.natAdd r i) = false := by
    simp only [x, Fin.addCases_right]
    simp [Ne.symm hji]
  have he : Function.update x (Fin.natAdd r i) (!x (Fin.natAdd r i)) = y := by
    rw [hxi]
    exact append_update_right _ _ _ _
  have hya : y (Fin.castAdd r i) = true := by simp [y]
  have hyb : y (Fin.natAdd r i) = true := by
    simp only [y, Fin.addCases_right]
    simp
  have hxoff : matchingFun x = false := matching_singletons_off i j (Ne.symm hji)
  have hyon : matchingFun y = true := decide_eq_true_eq.mpr ⟨i, hya, hyb⟩
  have hbx : sideBank x = fun _ => true :=
    bank_all_true ⟨i, by simp only [x, Fin.addCases_left, decide_true]⟩
      ⟨j, by simp only [x, Fin.addCases_right, decide_true]⟩
  have hby : sideBank y = fun _ => true := bank_all_true ⟨i, hya⟩ ⟨i, hyb⟩
  refine ⟨x, ?_, ?_⟩
  · rw [he, hxoff, hyon]
    decide
  · rw [he, hbx, hby]

lemma matching_with_free_sides {r : ℕ} (hr : 2 ≤ r) (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hfun : ∀ x : Fin (r + r) → Bool,
      circuitFun (r + r + 2) C (Fin.addCases x (sideBank x)) = matchingFun x) :
    r + r ≤ C.size + 1 := by
  apply bank_essential_bound C matchingFun sideBank hlen hfun
  intro i
  refine Fin.addCases (m := r) (n := r)
    (fun a => matching_point_witness hr a) (fun b => matching_line_witness hr b) i

end PEqualNP.Outside.L_meta_4675.MatchingBank
