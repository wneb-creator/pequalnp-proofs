import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585_aux.OrBound

open PEqualNP.CircuitLowerBounds PEqualNP.SharedBlockCost

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

lemma val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

lemma val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

lemma val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def T {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => val C (fun a : Fin n => decide (a = i)) w = true

lemma mem_T {n : ℕ} (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ (T C w : Finset (Fin n)) ↔ val C (fun a : Fin n => decide (a = i)) w = true := by
  simp [T]

lemma T_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (T C w : Finset (Fin n)) = {⟨w, hw⟩} := by
  ext i
  rw [mem_T]
  have h := val_input C (fun a : Fin n => decide (a = i)) ⟨w, hw⟩
  change val C (fun a : Fin n => decide (a = i)) w = _ at h
  rw [h]
  simp only [decide_eq_true_eq, Finset.mem_singleton]
  exact eq_comm

lemma T_gate {n : ℕ} (C : Circuit) (hC : IsOrCircuit n C) (p : ℕ) (hp : p < C.gates.length) :
    ∃ a b, a < n + p ∧ b < n + p ∧ (T C (n + p) : Finset (Fin n)) = T C a ∪ T C b := by
  obtain ⟨hop, hlen, hin⟩ := hC p hp
  have hg : C.gates[p]? = some C.gates[p] := List.getElem?_eq_getElem hp
  have hor : (C.gates[p]).op = GateOp.or := by
    generalize (C.gates[p]).op = o at hop
    cases o <;> first | rfl | (simp [isOrOp] at hop)
  obtain ⟨a, b, hab⟩ : ∃ a b, (C.gates[p]).inputs = [a, b] := by
    match h : (C.gates[p]).inputs, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  have ha : a < n + p := hin a (by simp [hab])
  have hb : b < n + p := hin b (by simp [hab])
  refine ⟨a, b, ha, hb, ?_⟩
  ext i
  rw [Finset.mem_union, mem_T, mem_T, mem_T, val_gate C _ hg, hor, hab]
  simp [GateOp.eval, operand, ha, hb]

lemma T_computes {n : ℕ} (C : Circuit) (w : ℕ) (s : Finset (Fin n))
    (h : ComputesOr n C w s) : T C w = s := by
  ext i
  rw [mem_T]
  have h2 := h.2 (fun a : Fin n => decide (a = i))
  change (val C (fun a : Fin n => decide (a = i)) w = true ↔ _) at h2
  rw [h2]
  simp


def Good {m n : ℕ} (R : Fin m → Fin n → Prop) (C : Circuit) (c : Fin m) (u : Fin n) (j : ℕ) : Prop :=
  j < C.gates.length ∧ (∀ t ∈ (T C (n + j) : Finset (Fin n)), R c t) ∧
    u ∈ (T C (n + j) : Finset (Fin n)) ∧ ∃ u0 ∈ (T C (n + j) : Finset (Fin n)), u0 < u

lemma no_below {m n : ℕ} (R : Fin m → Fin n → Prop) (C : Circuit) (c : Fin m) (u : Fin n) (j a : ℕ)
    (hj : j < C.gates.length) (ha : a < n + j)
    (hadj : ∀ t ∈ (T C a : Finset (Fin n)), R c t) (hu : u ∈ (T C a : Finset (Fin n)))
    (hmin : ∀ j', j' < j → ¬ Good R C c u j') : ∀ t ∈ (T C a : Finset (Fin n)), ¬ t < u := by
  intro t ht hlt
  by_cases han : a < n
  · rw [T_input C a han, Finset.mem_singleton] at hu ht
    rw [hu, ht] at hlt
    exact lt_irrefl _ hlt
  · obtain ⟨j', rfl⟩ : ∃ j', a = n + j' := ⟨a - n, by omega⟩
    exact hmin j' (by omega) ⟨by omega, hadj, hu, t, ht, hlt⟩

lemma no_lt_aux {m n : ℕ} (R : Fin m → Fin n → Prop) (C : Circuit) (c : Fin m) (u u' : Fin n) (j a b : ℕ)
    (hj : j < C.gates.length) (ha : a < n + j) (hb : b < n + j)
    (hT : (T C (n + j) : Finset (Fin n)) = T C a ∪ T C b)
    (hg : Good R C c u j)
    (hmin : ∀ j', j' < j → ¬ Good R C c u j') (hmin' : ∀ j', j' < j → ¬ Good R C c u' j')
    (hlt : u < u') (hu'a : u' ∈ (T C a : Finset (Fin n))) : False := by
  obtain ⟨_, hadj, hu, u0, hu0, hu0lt⟩ := hg
  have hadja : ∀ t ∈ (T C a : Finset (Fin n)), R c t :=
    fun t ht => hadj t (by rw [hT]; exact Finset.mem_union_left _ ht)
  have hadjb : ∀ t ∈ (T C b : Finset (Fin n)), R c t :=
    fun t ht => hadj t (by rw [hT]; exact Finset.mem_union_right _ ht)
  have h1 := no_below R C c u' j a hj ha hadja hu'a hmin'
  rw [hT, Finset.mem_union] at hu hu0
  rcases hu with hua | hub
  · exact h1 u hua hlt
  · have h2 := no_below R C c u j b hj hb hadjb hub hmin
    rcases hu0 with h | h
    · exact h1 u0 h (lt_trans hu0lt hlt)
    · exact h2 u0 h hu0lt

lemma no_lt {m n : ℕ} (R : Fin m → Fin n → Prop) (C : Circuit) (hC : IsOrCircuit n C)
    (c : Fin m) (u u' : Fin n) (j : ℕ) (hg : Good R C c u j) (hg' : Good R C c u' j)
    (hmin : ∀ j', j' < j → ¬ Good R C c u j') (hmin' : ∀ j', j' < j → ¬ Good R C c u' j')
    (hlt : u < u') : False := by
  have hj := hg.1
  obtain ⟨a, b, ha, hb, hT⟩ := T_gate C hC j hj
  have hu' := hg'.2.2.1
  rw [hT, Finset.mem_union] at hu'
  rcases hu' with h | h
  · exact no_lt_aux R C c u u' j a b hj ha hb hT hg hmin hmin' hlt h
  · exact no_lt_aux R C c u u' j b a hj hb ha (by rw [hT, Finset.union_comm]) hg hmin hmin' hlt h

lemma inj_core {m n : ℕ} (R : Fin m → Fin n → Prop)
    (hN : ∀ u0 u : Fin n, u0 ≠ u → ∀ c c', R c u0 → R c u → R c' u0 → R c' u → c = c')
    (C : Circuit) (hC : IsOrCircuit n C)
    (c : Fin m) (u : Fin n) (c' : Fin m) (u' : Fin n) (j : ℕ) (hg : Good R C c u j) (hg' : Good R C c' u' j)
    (hmin : ∀ j', j' < j → ¬ Good R C c u j') (hmin' : ∀ j', j' < j → ¬ Good R C c' u' j') :
    c = c' ∧ u = u' := by
  have hcc : c = c' := by
    obtain ⟨_, hadj, hu, u0, hu0, hu0lt⟩ := hg
    exact hN u0 u (ne_of_lt hu0lt) c c' (hadj u0 hu0) (hadj u hu) (hg'.2.1 u0 hu0) (hg'.2.1 u hu)
  subst hcc
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy u u' with h | h | h
  · exact (no_lt R C hC c u u' j hg hg' hmin hmin' h).elim
  · exact h
  · exact (no_lt R C hC c u' u j hg' hg hmin' hmin h).elim

lemma leaf_min {m n : ℕ} (R : Fin m → Fin n → Prop) (C : Circuit) (L : Finset (Fin n))
    (hS : ∃ w < n + C.gates.length, ComputesOr n C w L) (c : Fin m) (u : Fin n)
    (hadj : ∀ t ∈ L, R c t) (hu : u ∈ L)
    (hng : ¬ ∃ j, Good R C c u j) : ∀ t ∈ L, ¬ t < u := by
  intro t ht hlt
  obtain ⟨w, hw, hcomp⟩ := hS
  have hT := T_computes C w L hcomp
  by_cases hwn : w < n
  · rw [← hT, T_input C w hwn, Finset.mem_singleton] at hu ht
    rw [hu, ht] at hlt
    exact lt_irrefl _ hlt
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    exact hng ⟨j, by omega, by rw [hT]; exact hadj, by rw [hT]; exact hu, t,
      by rw [hT]; exact ht, hlt⟩

lemma card_le_of_unique_fibers {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : Finset α} {t : Finset β} (r : α → β → Prop)
    (hs : ∀ a ∈ s, ∃ b, b ∈ t ∧ r a b)
    (ht : ∀ b ∈ t, Set.Subsingleton {a | a ∈ s ∧ r a b}) : s.card ≤ t.card := by
  classical
  let f : s → β := fun a => Classical.choose (hs a.1 a.2)
  have hf (a : s) : f a ∈ t ∧ r a.1 (f a) := Classical.choose_spec (hs a.1 a.2)
  let g : s → t := fun a => ⟨f a, (hf a).1⟩
  apply Finset.card_le_card_of_injective (f := g)
  intro a a' heq
  have heq' : f a = f a' := congrArg Subtype.val heq
  apply Subtype.ext
  exact ht (f a) (hf a).1 ⟨a.2, (hf a).2⟩ ⟨a'.2, heq'.symm ▸ (hf a').2⟩

lemma count_gen {m n : ℕ} (R : Fin m → Fin n → Prop)
    (hN : ∀ u0 u : Fin n, u0 ≠ u → ∀ c c', R c u0 → R c u → R c' u0 → R c' u → c = c')
    (C : Circuit) (hC : IsOrCircuit n C)
    (K : Finset (Fin m × Finset (Fin n)))
    (hK : ∀ k ∈ K, (∃ w < n + C.gates.length, ComputesOr n C w k.2) ∧ ∀ t ∈ k.2, R k.1 t)
    (P : Finset (Σ _ : Fin m, Fin n))
    (hP : ∀ q ∈ P, ∃ k ∈ K, k.1 = q.1 ∧ q.2 ∈ k.2) :
    P.card ≤ C.gates.length + K.card := by
  classical
  have hQ : (P.filter fun q => ∃ j, Good R C q.1 q.2 j).card ≤ C.gates.length := by
    rw [← Finset.card_range C.gates.length]
    refine card_le_of_unique_fibers
      (fun q j => Good R C q.1 q.2 j ∧ ∀ j', j' < j → ¬ Good R C q.1 q.2 j') ?_ ?_
    · intro q hq
      obtain ⟨_, hex⟩ := Finset.mem_filter.1 hq
      refine ⟨Nat.find hex, ?_, Nat.find_spec hex, fun j' hj' => Nat.find_min hex hj'⟩
      exact Finset.mem_range.2 (Nat.find_spec hex).1
    · intro j _ q hq q' hq'
      obtain ⟨c, u⟩ := q
      obtain ⟨c', u'⟩ := q'
      obtain ⟨_, hg, hmin⟩ := hq
      obtain ⟨_, hg', hmin'⟩ := hq'
      obtain ⟨h1, h2⟩ := inj_core R hN C hC c u c' u' j hg hg' hmin hmin'
      subst h1; subst h2; rfl
  have hR : (P.filter fun q => ¬ ∃ j, Good R C q.1 q.2 j).card ≤ K.card := by
    refine card_le_of_unique_fibers
      (fun q k => k.1 = q.1 ∧ q.2 ∈ k.2) ?_ ?_
    · intro q hq
      exact hP q (Finset.mem_filter.1 hq).1
    · intro k hk q hq q' hq'
      obtain ⟨c, u⟩ := q
      obtain ⟨c', u'⟩ := q'
      obtain ⟨hq1, hqc, hqu⟩ := hq
      obtain ⟨hq1', hqc', hqu'⟩ := hq'
      have hcc : c = c' := hqc.symm.trans hqc'
      subst hcc
      obtain ⟨hcomp, hadj⟩ := hK k hk
      rw [hqc] at hadj
      have h1 := leaf_min R C k.2 hcomp c u hadj hqu (Finset.mem_filter.1 hq1).2
      have h2 := leaf_min R C k.2 hcomp c u' hadj hqu' (Finset.mem_filter.1 hq1').2
      have huu : u = u' := le_antisymm (not_lt.1 (h1 u' hqu')) (not_lt.1 (h2 u hqu))
      subst huu; rfl
  have hsplit := Finset.card_filter_add_card_filter_not (s := P)
    (fun q => ∃ j, Good R C q.1 q.2 j)
  omega

lemma linear_family_or_bound_active {m n c : ℕ} (S : Fin m → Finset (Fin n))
    (hlin : ∀ p q : Fin m, p ≠ q → (S p ∩ S q).card ≤ 1)
    (hcost : HasOrCost n ((Finset.univ.filter fun p => (S p).Nonempty).image S) c) :
    (∑ p : Fin m, (S p).card) ≤ c + (Finset.univ.filter fun p => (S p).Nonempty).card := by
  classical
  obtain ⟨C, hC, hsize⟩ := hcost
  let R : Fin m → Fin n → Prop := fun p u => u ∈ S p
  have hN : ∀ u0 u : Fin n, u0 ≠ u → ∀ p q : Fin m,
      R p u0 → R p u → R q u0 → R q u → p = q := by
    intro u0 u hne p q hp0 hpu hq0 hqu
    by_contra hpq
    have hs : ({u0, u} : Finset (Fin n)) ⊆ S p ∩ S q := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hp0, hq0⟩
      · exact Finset.mem_inter.mpr ⟨hpu, hqu⟩
    have hc : ({u0, u} : Finset (Fin n)).card = 2 := by simp [hne]
    have hle := Finset.card_le_card hs
    have hsmall := hlin p q hpq
    omega
  let A : Finset (Fin m) := Finset.univ.filter fun p => (S p).Nonempty
  let K : Finset (Fin m × Finset (Fin n)) := A.image fun p => (p, S p)
  let I : Finset (Σ _ : Fin m, Fin n) := Finset.univ.sigma S
  have hK : ∀ k ∈ K,
      (∃ w < n + C.gates.length, ComputesOr n C w k.2) ∧ ∀ t ∈ k.2, R k.1 t := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    exact ⟨hC.2 (S p) (Finset.mem_image.mpr ⟨p, hp, rfl⟩),
      fun _ ht => ht⟩
  have hP : ∀ q ∈ I, ∃ k ∈ K, k.1 = q.1 ∧ q.2 ∈ k.2 := by
    intro q hq
    refine ⟨(q.1, S q.1), ?_, rfl, (Finset.mem_sigma.mp hq).2⟩
    exact Finset.mem_image.mpr ⟨q.1, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨q.2, (Finset.mem_sigma.mp hq).2⟩⟩, rfl⟩
  have hbound := count_gen R hN C hC.1 K hK I hP
  have hKcard : K.card ≤ A.card := Finset.card_image_le
  dsimp [A] at hKcard
  have hIcard : I.card = ∑ p : Fin m, (S p).card := Finset.card_sigma _ _
  omega

lemma linear_family_or_cost {m n c : ℕ} (S : Fin m → Finset (Fin n))
    (hlin : ∀ p q : Fin m, p ≠ q → (S p ∩ S q).card ≤ 1)
    (hcost : HasOrCost n ((Finset.univ.filter fun p => (S p).Nonempty).image S) c) :
    (∑ p : Fin m, ((S p).card - 1)) ≤ c := by
  classical
  have hcard (p : Fin m) :
      (S p).card = ((S p).card - 1) + if (S p).Nonempty then 1 else 0 := by
    by_cases hp : (S p).Nonempty
    · have hpos := Finset.card_pos.mpr hp
      simp only [ite_eq_left hp]
      omega
    · have hempty : S p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hp
      simp [hempty]
  have hsum : (∑ p : Fin m, (S p).card) =
      (∑ p : Fin m, ((S p).card - 1)) +
        (Finset.univ.filter fun p => (S p).Nonempty).card := by
    calc
      (∑ p : Fin m, (S p).card) =
          ∑ p : Fin m, (((S p).card - 1) + if (S p).Nonempty then 1 else 0) :=
        Finset.sum_congr rfl (fun p _ => hcard p)
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id]
  have hb := linear_family_or_bound_active S hlin hcost
  omega

lemma linear_family_or_bound {m n c : ℕ} (S : Fin m → Finset (Fin n))
    (hlin : ∀ p q : Fin m, p ≠ q → (S p ∩ S q).card ≤ 1)
    (hcost : HasOrCost n (Finset.univ.image S) c) :
    (∑ p : Fin m, (S p).card) ≤ c + m := by
  classical
  have hcost' : HasOrCost n ((Finset.univ.filter fun p => (S p).Nonempty).image S) c := by
    obtain ⟨C, ⟨hC, hCs⟩, hsize⟩ := hcost
    refine ⟨C, ⟨hC, ?_⟩, hsize⟩
    intro s hs
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hs
    exact hCs (S p) (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩)
  have hb := linear_family_or_bound_active S hlin hcost'
  have ha : (Finset.univ.filter fun p => (S p).Nonempty).card ≤ m := by
    exact le_trans (Finset.card_filter_le _ _) (by simp)
  omega

end PEqualNP.Outside.L_meta_2585_aux.OrBound
