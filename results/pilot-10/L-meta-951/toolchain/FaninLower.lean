import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_951.Weighted

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

/-- The support of a gate: the union of the supports of the wires it reads. -/
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

/-- The supports of all wires, starting from the supports `L` of the wires present. -/
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

/-- The supports of the input wires: input `i` has support `{i}`. -/
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

/-- Wire lists `w`, `w'` (for the inputs `x`, `y`) agree on every wire whose support `x` and
`y` agree on. -/
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

/-- Any set `W` of wires has a joint support of size at most `t + |W|`. -/
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

def charge (gs : List Gate) : ℕ := (gs.map fun g => g.inputs.length - 1).sum

lemma cnt_step_weighted (t : ℕ) (L : List (Finset (Fin n))) (g : Gate)
    (h : Cnt t L) : Cnt (t + (g.inputs.length - 1)) (L ++ [gateSupp L g]) := by
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
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤
        (W.card - 1) + g.inputs.length := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (List.toFinset_card_le _) _
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

lemma cnt_suppsFrom_weighted (gs : List Gate) :
    ∀ (t : ℕ) (L : List (Finset (Fin n))),
      Cnt t L → Cnt (t + charge gs) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L h; simpa [charge, suppsFrom] using h
  | cons g gs ih =>
    intro t L h
    have hh := ih (t + (g.inputs.length - 1)) (L ++ [gateSupp L g])
      (cnt_step_weighted t L g h)
    simpa [charge, suppsFrom, Nat.add_assoc] using hh

lemma or_card_le_charge (S : Finset (Fin n)) (gs : List Gate) (out : ℕ)
    (hev : ∀ x : Fin n → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) =
      decide (∃ v ∈ S, x v = true)) : S.card ≤ charge gs + 1 := by
  classical
  set T := (suppsFrom gs (inputSupps n)).getD out ∅ with hT
  have hsub : S ⊆ T := by
    intro i hi
    by_contra hnot
    let x : Fin n → Bool := fun _ => false
    let y : Fin n → Bool := Function.update x i true
    have hag := (agree_wiresFrom y x gs _ _ _ (agree_inputs _ _)).2.2 out (by
      intro k hk
      have hki : k ≠ i := fun he => hnot (he ▸ hk)
      exact Function.update_of_ne hki true x)
    have hx : Circuit.eval ⟨gs, out⟩ (List.ofFn x) = false := by
      rw [hev]
      simp [x]
    have hy : Circuit.eval ⟨gs, out⟩ (List.ofFn y) = true := by
      rw [hev]
      apply decide_eq_true
      exact ⟨i, hi, by simp [y]⟩
    change Circuit.eval ⟨gs, out⟩ (List.ofFn y) =
      Circuit.eval ⟨gs, out⟩ (List.ofFn x) at hag
    rw [hx, hy] at hag
    contradiction
  have hc := cnt_suppsFrom_weighted gs 0 (inputSupps n) cnt_inputs {out}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  exact (Finset.card_le_card hsub).trans hc

lemma wiresFrom_get_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun j =>
        (wiresFrom (gs.take k) w).getD j false) := by
  induction gs generalizing w k with
  | nil => simp at hk
  | cons g gs ih =>
    cases k with
    | zero =>
      change (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)] )).getD (w.length + 0) false = _
      rw [getD_wiresFrom _ _ _ (by simp)]
      simp [wiresFrom]
    | succ k =>
      have hk' : k < gs.length := by simpa using hk
      have hh := ih (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) k hk'
      simpa [wiresFrom, Nat.add_assoc, Nat.add_comm 1 k] using hh

lemma wiresFrom_replace (gs hs : List Gate) (w : List Bool)
    (hlen : gs.length = hs.length)
    (heval : ∀ k (hk : k < gs.length),
      (gs[k]).op.eval ((gs[k]).inputs.map fun j => (wiresFrom (gs.take k) w).getD j false) =
      (hs[k]'(by omega)).op.eval
        ((hs[k]'(by omega)).inputs.map fun j => (wiresFrom (gs.take k) w).getD j false)) :
    wiresFrom gs w = wiresFrom hs w := by
  induction gs generalizing hs w with
  | nil =>
    have : hs = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
    subst hs
    rfl
  | cons g gs ih =>
    cases hs with
    | nil => simp at hlen
    | cons h hs =>
      have hzero := heval 0 (by simp)
      simp only [List.getElem_cons_zero, List.take_zero] at hzero
      change g.op.eval (g.inputs.map fun j => w.getD j false) =
        h.op.eval (h.inputs.map fun j => w.getD j false) at hzero
      change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) =
        wiresFrom hs (w ++ [h.op.eval (h.inputs.map fun j => w.getD j false)])
      rw [← hzero]
      apply ih _ _ (by simpa using hlen)
      intro k hk
      have hh := heval (k + 1) (by simpa using hk)
      simpa [wiresFrom] using hh

lemma target_eq_of_output_eq {m : ℕ} (S : Fin m → Finset (Fin n))
    (gs : List Gate) (out : Fin m → ℕ)
    (hev : ∀ (i : Fin m) (x : Fin n → Bool), Circuit.eval ⟨gs, out i⟩ (List.ofFn x) =
      decide (∃ v ∈ S i, x v = true)) {i j : Fin m} (h : out i = out j) : S i = S j := by
  classical
  ext v
  have hh : decide (∃ a ∈ S i, decide (a = v) = true) =
      decide (∃ a ∈ S j, decide (a = v) = true) := by
    rw [← hev i, ← hev j, h]
  simpa using hh

lemma outputs_injective {m : ℕ} (S : Fin m → Finset (Fin n))
    (hsz : ∀ i, 2 ≤ (S i).card)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (out : Fin m → ℕ)
    (hev : ∀ (i : Fin m) (x : Fin n → Bool), Circuit.eval ⟨gs, out i⟩ (List.ofFn x) =
      decide (∃ v ∈ S i, x v = true)) : Function.Injective out := by
  intro i j hij
  by_contra hne
  have he := target_eq_of_output_eq S gs out hev hij
  have hl := hlin i j hne
  rw [he, Finset.inter_self] at hl
  have hh := hsz j
  omega

lemma output_lt {S : Finset (Fin n)} (hS : S.Nonempty) (gs : List Gate) (out : ℕ)
    (hev : ∀ x : Fin n → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) =
      decide (∃ v ∈ S, x v = true)) : out < n + gs.length := by
  by_contra h
  have hh : Circuit.eval ⟨gs, out⟩ (List.ofFn (fun _ : Fin n => true)) = false := by
    unfold Circuit.eval
    change (wiresFrom gs _).getD out false = false
    apply List.getD_eq_default
    rw [length_wiresFrom, List.length_ofFn]
    omega
  rw [hev] at hh
  obtain ⟨v,hv⟩ := hS
  have ht : decide (∃ v ∈ S, (fun _ : Fin n => true) v = true) = true :=
    decide_eq_true ⟨v, hv, rfl⟩
  rw [ht] at hh
  contradiction

lemma output_ge {S : Finset (Fin n)} (hS : 2 ≤ S.card) (gs : List Gate) (out : ℕ)
    (hev : ∀ x : Fin n → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) =
      decide (∃ v ∈ S, x v = true)) : n ≤ out := by
  classical
  by_contra h
  have hout : out < n := by omega
  let o : Fin n := ⟨out, hout⟩
  have hex : ∃ v ∈ S, v ≠ o := by
    by_contra hh
    push Not at hh
    have hs : S ⊆ {o} := fun a ha => Finset.mem_singleton.mpr (hh a ha)
    have hc := Finset.card_le_card hs
    simp only [Finset.card_singleton] at hc
    omega
  obtain ⟨v,hv,hvo⟩ := hex
  let x : Fin n → Bool := fun a => decide (a = v)
  have hh : Circuit.eval ⟨gs, out⟩ (List.ofFn x) = false := by
    unfold Circuit.eval
    change (wiresFrom gs _).getD out false = false
    rw [getD_wiresFrom _ _ _ (by simpa using hout)]
    simp [List.getD_eq_getElem?_getD, hout, x, Ne.symm hvo, o]
  rw [hev] at hh
  have ht : decide (∃ a ∈ S, x a = true) = true :=
    decide_eq_true ⟨v, hv, by simp [x]⟩
  rw [ht] at hh
  contradiction

def replaceGates (gs : List Gate) (K : Finset (Fin gs.length))
    (r : Fin gs.length → Gate) : List Gate :=
  List.ofFn fun k => if k ∈ K then r k else gs.get k

lemma charge_replaceGates (gs : List Gate) (K : Finset (Fin gs.length))
    (r : Fin gs.length → Gate)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hr : ∀ k ∈ K, (r k).inputs.length ≤ 1) :
    charge (replaceGates gs K r) + K.card ≤ gs.length := by
  have hb : ∀ k : Fin gs.length,
      ((if k ∈ K then r k else gs.get k).inputs.length - 1) +
        (if k ∈ K then 1 else 0) ≤ 1 := by
    intro k
    by_cases hk : k ∈ K
    · have hh := hr k hk
      simp only [hk, ite_true]
      omega
    · have hh := hg (gs.get k) (List.get_mem gs k)
      simp only [hk, ite_false]
      omega
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hb k)
  simpa [charge, replaceGates, List.map_ofFn, List.sum_ofFn,
    Finset.sum_add_distrib] using hh

lemma wiresFrom_replaceGates (gs : List Gate) (K : Finset (Fin gs.length))
    (r : Fin gs.length → Gate) (w : List Bool)
    (hrep : ∀ k ∈ K,
      (r k).op.eval ((r k).inputs.map fun j => (wiresFrom (gs.take k.val) w).getD j false) =
      (gs.get k).op.eval ((gs.get k).inputs.map fun j =>
        (wiresFrom (gs.take k.val) w).getD j false)) :
    wiresFrom gs w = wiresFrom (replaceGates gs K r) w := by
  apply wiresFrom_replace gs _ w (by simp [replaceGates])
  intro k hk
  let ki : Fin gs.length := ⟨k, hk⟩
  by_cases hki : ki ∈ K
  · simpa [replaceGates, ki, hki] using (hrep ki hki).symm
  · simp [replaceGates, ki, hki]

lemma card_le_charge_of_singletons (S : Finset (Fin n)) (gs : List Gate) (out : ℕ)
    (hzero : Circuit.eval ⟨gs, out⟩ (List.ofFn (fun _ : Fin n => false)) = false)
    (hsingle : ∀ i ∈ S, Circuit.eval ⟨gs, out⟩
      (List.ofFn (Function.update (fun _ : Fin n => false) i true)) = true) :
    S.card ≤ charge gs + 1 := by
  classical
  set T := (suppsFrom gs (inputSupps n)).getD out ∅ with hT
  have hsub : S ⊆ T := by
    intro i hi
    by_contra hnot
    let x : Fin n → Bool := fun _ => false
    let y : Fin n → Bool := Function.update x i true
    have hag := (agree_wiresFrom y x gs _ _ _ (agree_inputs _ _)).2.2 out (by
      intro k hk
      have hki : k ≠ i := fun he => hnot (he ▸ hk)
      exact Function.update_of_ne hki true x)
    change Circuit.eval ⟨gs, out⟩ (List.ofFn y) =
      Circuit.eval ⟨gs, out⟩ (List.ofFn x) at hag
    change Circuit.eval ⟨gs, out⟩ (List.ofFn (Function.update (fun _ => false) i true)) =
      Circuit.eval ⟨gs, out⟩ (List.ofFn (fun _ => false)) at hag
    rw [hzero, hsingle i hi] at hag
    contradiction
  have hc := cnt_suppsFrom_weighted gs 0 (inputSupps n) cnt_inputs {out}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  exact (Finset.card_le_card hsub).trans hc

def restrictInputs (A : Finset (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  fun v => if v ∈ A then x v else false

noncomputable def restrictedOrGate (A T : Finset (Fin n)) : Gate :=
  ⟨GateOp.or, (T ∩ A).toList.map Fin.val⟩

lemma restrictedOrGate_eval (A T : Finset (Fin n)) (pre : List Gate)
    (x : Fin n → Bool) :
    (restrictedOrGate A T).op.eval
      ((restrictedOrGate A T).inputs.map fun j =>
        (wiresFrom pre (List.ofFn (restrictInputs A x))).getD j false) =
      decide (∃ v ∈ T, restrictInputs A x v = true) := by
  have hw : ∀ v : Fin n,
      (wiresFrom pre (List.ofFn (restrictInputs A x))).getD v.val false =
        restrictInputs A x v := by
    intro v
    rw [getD_wiresFrom _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, v.isLt]
  apply Bool.eq_iff_iff.mpr
  simp only [restrictedOrGate, GateOp.eval, List.map_map, Function.comp_def, hw,
    List.any_eq_true, List.mem_map, Finset.mem_toList, Finset.mem_inter, id,
    Bool.decide_iff]
  constructor
  · rintro ⟨b, ⟨v, ⟨hvT,hvA⟩, rfl⟩, hv⟩
    exact ⟨v, hvT, hv⟩
  · rintro ⟨v, hvT, hv⟩
    have hvA : v ∈ A := by
      by_contra h
      simp [restrictInputs, h] at hv
    exact ⟨_, ⟨v, ⟨hvT, hvA⟩, rfl⟩, hv⟩

lemma restrictedOrGate_length (A T : Finset (Fin n)) :
    (restrictedOrGate A T).inputs.length = (T ∩ A).card := by
  simp [restrictedOrGate]

lemma restrict_zero (A : Finset (Fin n)) :
    restrictInputs A (fun _ => false) = fun _ => false := by
  funext v
  simp [restrictInputs]

lemma restrict_singleton (A : Finset (Fin n)) (i : Fin n) (hi : i ∈ A) :
    restrictInputs A (Function.update (fun _ => false) i true) =
      Function.update (fun _ => false) i true := by
  funext v
  by_cases hv : v = i
  · subst v
    simp [restrictInputs, hi]
  · simp [restrictInputs, Function.update_of_ne hv]

lemma per_target_lower {m : ℕ} (S : Fin m → Finset (Fin n))
    (hsz : ∀ i, 2 ≤ (S i).card)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hev : ∀ (i : Fin m) (x : Fin n → Bool), Circuit.eval ⟨gs, out i⟩ (List.ofFn x) =
      decide (∃ v ∈ S i, x v = true)) (i : Fin m) :
    ((S i).card - 1) + (m - 1) ≤ gs.length := by
  classical
  have hge (j : Fin m) : n ≤ out j := output_ge (hsz j) gs (out j) (hev j)
  have hlt (j : Fin m) : out j < n + gs.length :=
    output_lt (Finset.card_pos.mp (by have := hsz j; omega)) gs (out j) (hev j)
  let idx : Fin m → Fin gs.length := fun j => ⟨out j - n, by have := hlt j; have := hge j; omega⟩
  have hidx (j : Fin m) : n + (idx j).val = out j := by
    dsimp [idx]
    have := hge j
    omega
  have hinj : Function.Injective idx := by
    intro j k hjk
    apply outputs_injective S hsz hlin gs out hev
    have hh := congrArg Fin.val hjk
    have := hidx j
    have := hidx k
    omega
  let K : Finset (Fin gs.length) := (Finset.univ.erase i).image idx
  have hKcard : K.card = m - 1 := by
    dsimp [K]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hkmem (k : Fin gs.length) (hk : k ∈ K) :
      ∃ j ∈ Finset.univ.erase i, idx j = k := Finset.mem_image.mp hk
  let f : (k : Fin gs.length) → k ∈ K → Fin m := fun k hk =>
    Classical.choose (hkmem k hk)
  have hf (k : Fin gs.length) (hk : k ∈ K) : f k hk ≠ i ∧ idx (f k hk) = k := by
    have hh := Classical.choose_spec (hkmem k hk)
    exact ⟨(Finset.mem_erase.mp hh.1).1, hh.2⟩
  let r : Fin gs.length → Gate := fun k =>
    if hk : k ∈ K then restrictedOrGate (S i) (S (f k hk)) else ⟨GateOp.or, []⟩
  let gs' := replaceGates gs K r
  have hcharge : charge gs' + (m - 1) ≤ gs.length := by
    rw [← hKcard]
    apply charge_replaceGates gs K r hg
    intro k hk
    dsimp [r]
    rw [dite_eq_left hk, restrictedOrGate_length]
    exact hlin (f k hk) i (hf k hk).1
  have hwires (x : Fin n → Bool) :
      wiresFrom gs (List.ofFn (restrictInputs (S i) x)) =
        wiresFrom gs' (List.ofFn (restrictInputs (S i) x)) := by
    apply wiresFrom_replaceGates gs K r
    intro k hk
    dsimp [r]
    rw [dite_eq_left hk, restrictedOrGate_eval, ← hev (f k hk) (restrictInputs (S i) x)]
    unfold Circuit.eval
    change (wiresFrom gs (List.ofFn (restrictInputs (S i) x))).getD (out (f k hk)) false = _
    have ho : out (f k hk) = n + k.val := by
      rw [← hidx, (hf k hk).2]
    rw [ho]
    simpa using wiresFrom_get_gate gs (List.ofFn (restrictInputs (S i) x)) k.val k.isLt
  have hc : (S i).card ≤ charge gs' + 1 := by
    apply card_le_charge_of_singletons (S i) gs' (out i)
    · have hw := congrArg (fun w : List Bool => w.getD (out i) false)
        (hwires (fun _ => false))
      rw [restrict_zero] at hw
      change Circuit.eval ⟨gs, out i⟩ (List.ofFn (fun _ => false)) =
        Circuit.eval ⟨gs', out i⟩ (List.ofFn (fun _ => false)) at hw
      rw [← hw, hev]
      simp
    · intro v hv
      have hw := congrArg (fun w : List Bool => w.getD (out i) false)
        (hwires (Function.update (fun _ => false) v true))
      rw [restrict_singleton (S i) v hv] at hw
      change Circuit.eval ⟨gs, out i⟩ (List.ofFn (Function.update (fun _ => false) v true)) =
        Circuit.eval ⟨gs', out i⟩ (List.ofFn (Function.update (fun _ => false) v true)) at hw
      rw [← hw, hev]
      exact decide_eq_true ⟨v, hv, by simp⟩
  omega

lemma sum_lower_one_large {m : ℕ} (S : Fin m → Finset (Fin n))
    (hsz : ∀ i, 2 ≤ (S i).card)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hev : ∀ (i : Fin m) (x : Fin n → Bool), Circuit.eval ⟨gs, out i⟩ (List.ofFn x) =
      decide (∃ v ∈ S i, x v = true)) (i : Fin m)
    (hsmall : ∀ j, j ≠ i → (S j).card = 2) :
    (∑ j : Fin m, ((S j).card - 1)) ≤ gs.length := by
  have heq : (∑ j ∈ Finset.univ.erase i, ((S j).card - 1)) = m - 1 := by
    calc
      (∑ j ∈ Finset.univ.erase i, ((S j).card - 1)) =
          ∑ _j ∈ Finset.univ.erase i, 1 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hsmall j (Finset.mem_erase.mp hj).1]
      _ = m - 1 := by simp
  have ht : (∑ j ∈ Finset.univ.erase i, ((S j).card - 1)) + ((S i).card - 1) =
      ∑ j : Fin m, ((S j).card - 1) := Finset.sum_erase_add _ _ (Finset.mem_univ i)
  rw [heq] at ht
  have hb := per_target_lower S hsz hlin gs out hg hev i
  omega

end PEqualNP.Outside.L_meta_951.Weighted
