import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2373_aux

def matching (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)

def neighborClauses (x : Fin 6 → Bool) : Fin 4 → Bool :=
  ![x 0 || x 1 || x 4, x 2 || x 3 || x 4,
    x 0 || x 2 || x 5, x 1 || x 3 || x 5]

def stars (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1 && x 4) || (x 2 && x 3 && x 4) ||
    (x 0 && x 2 && x 5) || (x 1 && x 3 && x 5)

set_option maxRecDepth 4096 in
lemma clauses_cover_identity : ∀ x : Fin 6 → Bool,
    (neighborClauses x 0 && neighborClauses x 1 &&
      neighborClauses x 2 && neighborClauses x 3) =
      (matching x || stars x) := by
  decide

def lowWitness (v : Fin 6) : Fin 6 → Bool :=
  if v.val < 2 then ![false, false, true, true, true, false]
  else if v = 4 then ![true, false, true, false, false, true]
  else ![true, true, false, false, true, false]

def highWitness (v : Fin 6) (i : Fin 6) : Bool :=
  if i = v then true else lowWitness v i

set_option maxRecDepth 4096 in
lemma masked_witness : ∀ v : Fin 6,
    neighborClauses (lowWitness v) = neighborClauses (highWitness v) ∧
    matching (lowWitness v) = false ∧ matching (highWitness v) = true ∧
    ∀ i : Fin 6, i ≠ v → lowWitness v i = highWitness v i := by
  decide

lemma all_raw_coordinates_required
    (s : Finset (Fin 6))
    (h : (Fin 4 → Bool) → (Fin 6 → Bool) → Bool)
    (heq : ∀ x : Fin 6 → Bool,
      h (neighborClauses x) (fun i => if i ∈ s then x i else false) = matching x) :
    s = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro v
  by_contra hv
  obtain ⟨hc, hl, hh, hi⟩ := masked_witness v
  have hs : (fun i => if i ∈ s then lowWitness v i else false) =
      (fun i => if i ∈ s then highWitness v i else false) := by
    funext i
    by_cases his : i ∈ s
    · have hiv : i ≠ v := by
        intro hiv
        exact hv (hiv ▸ his)
      simp only [his, ite_true, hi i hiv]
    · simp only [his, ite_false]
  have hn := heq (lowWitness v)
  rw [hc, hs, heq (highWitness v), hl, hh] at hn
  contradiction

lemma clauses_alone_insufficient
    (h : (Fin 4 → Bool) → Bool) :
    ¬ ∀ x : Fin 6 → Bool, h (neighborClauses x) = matching x := by
  intro heq
  have hs := all_raw_coordinates_required ∅ (fun c _ => h c) heq
  have hzero : (0 : Fin 6) ∈ (∅ : Finset (Fin 6)) := hs ▸ Finset.mem_univ 0
  exact Finset.notMem_empty 0 hzero

def petersen (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def matchingRestriction (x : Fin 6 → Bool) : Fin 10 → Bool :=
  ![x 0, false, x 1, x 2, false, x 3, x 4, false, false, x 5]

set_option maxRecDepth 4096 in
lemma petersen_matching_restriction : ∀ x : Fin 6 → Bool,
    petersen (matchingRestriction x) = matching x := by
  decide


open PEqualNP.CircuitLowerBounds

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

lemma exists_small_support (n : ℕ) (C : Circuit)
    (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ S : Finset (Fin n), S.card ≤ C.size + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) →
        C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
  let S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅
  refine ⟨S, ?_, ?_⟩
  · have hc := cnt_suppsFrom C.gates 0 (inputSupps n) hfanin cnt_inputs {C.output}
    simpa only [Finset.singleton_biUnion, Finset.card_singleton, zero_add,
      Circuit.size] using hc
  · intro x y hxy
    exact (agree_wiresFrom x y C.gates _ _ _ (agree_inputs x y)).2.2 C.output hxy

lemma circuit_lower_of_observation_collisions {α : Type} (n k : ℕ)
    (signals : α → Fin n → Bool) (target : α → Bool)
    (hcollision : ∀ S : Finset (Fin n), S.card ≤ k →
      ∃ x y : α, (∀ i ∈ S, signals x i = signals y i) ∧ target x ≠ target y)
    (C : Circuit) (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hcompute : ∀ x : α, C.eval (List.ofFn (signals x)) = target x) : k ≤ C.size := by
  by_contra hsmall
  have hsize : C.size + 1 ≤ k := by omega
  obtain ⟨S, hS, hagree⟩ := exists_small_support n C hfanin
  obtain ⟨x, y, hxy, hne⟩ := hcollision S (hS.trans hsize)
  exact hne ((hcompute x).symm.trans ((hagree (signals x) (signals y) hxy).trans (hcompute y)))


def independent3 (b : Fin 3 → Bool) : Fin 6 → Bool :=
  ![b 0, b 1, !b 1, !b 0, b 2, !b 2]

def missing3 (b : Fin 3 → Bool) (i : Fin 3) : Fin 6 :=
  if b i then ![3, 2, 5] i else ![0, 1, 4] i

def augmented3 (b : Fin 3 → Bool) (i : Fin 3) : Fin 6 → Bool :=
  fun v => independent3 b v || decide (v = missing3 b i)

def orSignal3 (S : Finset (Fin 6)) (x : Fin 6 → Bool) : Bool :=
  decide (∃ v ∈ S, x v = true)

def separated3 (q : (Fin 6 → Bool) → Bool) : Finset ((Fin 3 → Bool) × Fin 3) :=
  Finset.univ.filter fun w => q (independent3 w.1) ≠ q (augmented3 w.1 w.2)

def distinguished3 (S : Finset (Fin 6)) : Finset ((Fin 3 → Bool) × Fin 3) :=
  separated3 (orSignal3 S)

lemma independent3_false : ∀ b, matching (independent3 b) = false := by
  decide

lemma augmented3_true : ∀ b i, matching (augmented3 b i) = true := by
  decide

set_option maxRecDepth 20000 in
lemma distinguished3_card_le : ∀ S : Finset (Fin 6), (distinguished3 S).card ≤ 4 := by
  decide

lemma obligations3_card : (Finset.univ : Finset ((Fin 3 → Bool) × Fin 3)).card = 24 := by
  decide

lemma four_capacity_collision {α : Type*} (T : Finset α)
    (q : α → (Fin 6 → Bool) → Bool) (hcard : T.card ≤ 5)
    (hq : ∀ a ∈ T, (separated3 (q a)).card ≤ 4) :
    ∃ b i, ∀ a ∈ T, q a (independent3 b) = q a (augmented3 b i) := by
  classical
  let U := T.biUnion fun a => separated3 (q a)
  have hU : U.card ≤ T.card * 4 := by
    calc
      U.card ≤ ∑ a ∈ T, (separated3 (q a)).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ T, 4 := Finset.sum_le_sum hq
      _ = T.card * 4 := by simp
  have hnot : ¬ ∀ w, w ∈ U := by
    intro h
    have hsub : (Finset.univ : Finset ((Fin 3 → Bool) × Fin 3)) ⊆ U := by
      intro w _
      exact h w
    have hle := Finset.card_le_card hsub
    rw [obligations3_card] at hle
    omega
  obtain ⟨w, hw⟩ := not_forall.mp hnot
  refine ⟨w.1, w.2, ?_⟩
  intro a ha
  by_contra hne
  apply hw
  exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hne⟩⟩

lemma five_or_sources_collision {α : Type*} (T : Finset α)
    (q : α → (Fin 6 → Bool) → Bool) (hcard : T.card ≤ 5)
    (hq : ∀ a ∈ T, (∃ S, q a = orSignal3 S) ∨ q a = fun _ => true) :
    ∃ b i, ∀ a ∈ T, q a (independent3 b) = q a (augmented3 b i) := by
  apply four_capacity_collision T q hcard
  intro a ha
  rcases hq a ha with ⟨S, hs⟩ | ht
  · rw [hs]
    exact distinguished3_card_le S
  · simp [separated3, ht]

lemma five_or_sources_not_matching {α : Type*} (T : Finset α)
    (q : α → (Fin 6 → Bool) → Bool) (hcard : T.card ≤ 5)
    (hq : ∀ a ∈ T, (∃ S, q a = orSignal3 S) ∨ q a = fun _ => true)
    (H : (Fin 6 → Bool) → Bool)
    (hdep : ∀ x y, (∀ a ∈ T, q a x = q a y) → H x = H y) :
    H ≠ matching := by
  intro hH
  obtain ⟨b, i, h⟩ := five_or_sources_collision T q hcard hq
  have he := hdep (independent3 b) (augmented3 b i) h
  rw [hH, independent3_false b, augmented3_true b i] at he
  cases he


lemma matching_free_or_lower (n : ℕ)
    (signals : Fin n → (Fin 6 → Bool) → Bool)
    (hsignals : ∀ j, (∃ S, signals j = orSignal3 S) ∨ signals j = fun _ => true)
    (C : Circuit) (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hcompute : ∀ x, C.eval (List.ofFn (fun j => signals j x)) = matching x) :
    5 ≤ C.size := by
  apply circuit_lower_of_observation_collisions n 5
    (fun x j => signals j x) matching ?_ C hfanin hcompute
  intro T hT
  obtain ⟨b, i, hbi⟩ := five_or_sources_collision T signals hT (fun j _ => hsignals j)
  refine ⟨independent3 b, augmented3 b i, hbi, ?_⟩
  rw [independent3_false, augmented3_true]
  decide

lemma petersen_restriction_free_or_lower (n : ℕ)
    (signals : Fin n → (Fin 6 → Bool) → Bool)
    (hsignals : ∀ j, (∃ S, signals j = orSignal3 S) ∨ signals j = fun _ => true)
    (C : Circuit) (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hcompute : ∀ x, C.eval (List.ofFn (fun j => signals j x)) =
      petersen (matchingRestriction x)) :
    5 ≤ C.size := by
  apply matching_free_or_lower n signals hsignals C hfanin
  intro x
  rw [hcompute, petersen_matching_restriction]

lemma capacity_required {α : Type*} (T : Finset α)
    (q : α → (Fin 6 → Bool) → Bool)
    (hdep : ∀ x y, (∀ a ∈ T, q a x = q a y) → matching x = matching y) :
    24 ≤ ∑ a ∈ T, (separated3 (q a)).card := by
  classical
  let U := T.biUnion fun a => separated3 (q a)
  have hsub : (Finset.univ : Finset ((Fin 3 → Bool) × Fin 3)) ⊆ U := by
    intro w _
    by_contra hw
    have he : ∀ a ∈ T, q a (independent3 w.1) = q a (augmented3 w.1 w.2) := by
      intro a ha
      by_contra hne
      exact hw (Finset.mem_biUnion.mpr
        ⟨a, ha, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hne⟩⟩)
    have hm := hdep (independent3 w.1) (augmented3 w.1 w.2) he
    rw [independent3_false w.1, augmented3_true w.1 w.2] at hm
    cases hm
  calc
    24 = (Finset.univ : Finset ((Fin 3 → Bool) × Fin 3)).card := obligations3_card.symm
    _ ≤ U.card := Finset.card_le_card hsub
    _ ≤ ∑ a ∈ T, (separated3 (q a)).card := Finset.card_biUnion_le

lemma six_capacity_card_eq {α : Type*} (T : Finset α)
    (q : α → (Fin 6 → Bool) → Bool) (hcard : T.card ≤ 6)
    (hq : ∀ a ∈ T, (separated3 (q a)).card ≤ 4)
    (hdep : ∀ x y, (∀ a ∈ T, q a x = q a y) → matching x = matching y) :
    T.card = 6 := by
  have hreq := capacity_required T q hdep
  have hsum : (∑ a ∈ T, (separated3 (q a)).card) ≤ T.card * 4 := by
    calc
      (∑ a ∈ T, (separated3 (q a)).card) ≤ ∑ _a ∈ T, 4 := Finset.sum_le_sum hq
      _ = T.card * 4 := by simp
  omega

lemma six_capacity_saturated {α : Type*} (T : Finset α)
    (q : α → (Fin 6 → Bool) → Bool) (hcard : T.card ≤ 6)
    (hq : ∀ a ∈ T, (separated3 (q a)).card ≤ 4)
    (hdep : ∀ x y, (∀ a ∈ T, q a x = q a y) → matching x = matching y) :
    ∀ a ∈ T, (separated3 (q a)).card = 4 := by
  intro a ha
  have hreq := capacity_required T q hdep
  have hle := hq a ha
  by_contra hne
  have hlt : (separated3 (q a)).card < 4 := by omega
  have hslt : (∑ b ∈ T, (separated3 (q b)).card) < ∑ _b ∈ T, 4 :=
    Finset.sum_lt_sum hq ⟨a, ha, hlt⟩
  have heq : (∑ _b ∈ T, 4) = T.card * 4 := by simp
  rw [heq] at hslt
  omega

lemma separated3_not (q : (Fin 6 → Bool) → Bool) :
    separated3 (fun x => !q x) = separated3 q := by
  ext w
  simp only [separated3, Finset.mem_filter, Finset.mem_univ, true_and]
  cases q (independent3 w.1) <;> cases q (augmented3 w.1 w.2) <;> decide

lemma signed_or_capacity_le (S : Finset (Fin 6)) (b : Bool) :
    (separated3 (fun x => Bool.xor b (orSignal3 S x))).card ≤ 4 := by
  cases b
  · simpa only [distinguished3, Bool.false_xor] using distinguished3_card_le S
  · simpa only [distinguished3, Bool.true_xor, separated3_not] using distinguished3_card_le S


set_option maxRecDepth 20000 in
lemma or_capacity_four_iff : ∀ S : Finset (Fin 6),
    (distinguished3 S).card = 4 ↔
      S.card = 1 ∨ (S.card = 2 ∧ matching (fun i => decide (i ∈ S)) = false) := by
  decide

lemma matching_five_gate_sources (n : ℕ)
    (signals : Fin n → (Fin 6 → Bool) → Bool)
    (hsignals : ∀ j, (∃ S, signals j = orSignal3 S) ∨ signals j = fun _ => true)
    (C : Circuit) (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hsize : C.size ≤ 5)
    (hcompute : ∀ x, C.eval (List.ofFn (fun j => signals j x)) = matching x) :
    ∃ T : Finset (Fin n), T.card = 6 ∧
      (∀ j ∈ T, (separated3 (signals j)).card = 4) ∧
      ∀ x y, (∀ j ∈ T, signals j x = signals j y) → matching x = matching y := by
  obtain ⟨T, hT, hagree⟩ := exists_small_support n C hfanin
  have hT6 : T.card ≤ 6 := by omega
  have hdep : ∀ x y, (∀ j ∈ T, signals j x = signals j y) → matching x = matching y := by
    intro x y hxy
    rw [← hcompute x, ← hcompute y]
    exact hagree _ _ hxy
  have hcap : ∀ j ∈ T, (separated3 (signals j)).card ≤ 4 := by
    intro j _
    rcases hsignals j with ⟨S, hs⟩ | ht
    · rw [hs]
      exact distinguished3_card_le S
    · simp [separated3, ht]
  exact ⟨T, six_capacity_card_eq T signals hT6 hcap hdep,
    six_capacity_saturated T signals hT6 hcap hdep, hdep⟩

lemma matching_five_gate_source_shapes (n : ℕ)
    (signals : Fin n → (Fin 6 → Bool) → Bool)
    (hsignals : ∀ j, (∃ S, signals j = orSignal3 S) ∨ signals j = fun _ => true)
    (C : Circuit) (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hsize : C.size ≤ 5)
    (hcompute : ∀ x, C.eval (List.ofFn (fun j => signals j x)) = matching x) :
    ∃ T : Finset (Fin n), T.card = 6 ∧
      (∀ j ∈ T, ∃ S : Finset (Fin 6), signals j = orSignal3 S ∧
        (S.card = 1 ∨ (S.card = 2 ∧ matching (fun i => decide (i ∈ S)) = false))) ∧
      ∀ x y, (∀ j ∈ T, signals j x = signals j y) → matching x = matching y := by
  obtain ⟨T, hT, hcap, hdep⟩ :=
    matching_five_gate_sources n signals hsignals C hfanin hsize hcompute
  refine ⟨T, hT, ?_, hdep⟩
  intro j hj
  have hc := hcap j hj
  rcases hsignals j with ⟨S, hs⟩ | ht
  · refine ⟨S, hs, (or_capacity_four_iff S).mp ?_⟩
    rw [hs] at hc
    exact hc
  · simp [separated3, ht] at hc

lemma matching_free_signed_or_lower (n : ℕ)
    (signals : Fin n → (Fin 6 → Bool) → Bool)
    (hsignals : ∀ j, ∃ (S : Finset (Fin 6)) (b : Bool),
      signals j = fun x => Bool.xor b (orSignal3 S x))
    (C : Circuit) (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hcompute : ∀ x, C.eval (List.ofFn (fun j => signals j x)) = matching x) :
    5 ≤ C.size := by
  apply circuit_lower_of_observation_collisions n 5
    (fun x j => signals j x) matching ?_ C hfanin hcompute
  intro T hT
  have hcap : ∀ j ∈ T, (separated3 (signals j)).card ≤ 4 := by
    intro j _
    obtain ⟨S, b, hs⟩ := hsignals j
    rw [hs]
    exact signed_or_capacity_le S b
  obtain ⟨b, i, hbi⟩ := four_capacity_collision T signals hT hcap
  refine ⟨independent3 b, augmented3 b i, hbi, ?_⟩
  rw [independent3_false, augmented3_true]
  decide

end PEqualNP.Outside.L_meta_2373_aux
