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

def matchingRestrictionAt (k : Fin 5) (x : Fin 6 → Bool) : Fin 10 → Bool :=
  ![![false, x 1, false, x 0, x 3, x 4, x 2, x 5, false, false],
    ![false, x 0, x 3, false, x 1, x 4, false, false, x 5, x 2],
    ![x 0, false, x 1, false, x 3, false, x 4, x 2, x 5, false],
    matchingRestriction x,
    ![x 0, x 3, false, x 1, false, false, false, x 4, x 2, x 5]] k

set_option maxRecDepth 20000 in
lemma five_matching_restrictions : ∀ (k : Fin 5) (x : Fin 6 → Bool),
    petersen (matchingRestrictionAt k x) = matching x := by
  decide

set_option maxRecDepth 20000 in
lemma restriction_source_capacity : ∀ (k : Fin 5) (i : Fin 10),
    (separated3 (fun x => matchingRestrictionAt k x i)).card ≤ 4 := by
  decide

namespace WeightedCapacity

open PEqualNP.CircuitLowerBounds

def gateFunction (L : List ((Fin 6 → Bool) → Bool)) (g : Gate) :
    (Fin 6 → Bool) → Bool :=
  fun x => g.op.eval (g.inputs.map fun i => L.getD i (fun _ => false) x)

def functionWires (gs : List Gate) (L : List ((Fin 6 → Bool) → Bool)) :
    List ((Fin 6 → Bool) → Bool) :=
  gs.foldl (fun L g => L ++ [gateFunction L g]) L

def highCount : List Gate → List ((Fin 6 → Bool) → Bool) → ℕ
  | [], _ => 0
  | g :: gs, L =>
      (if 4 < (separated3 (gateFunction L g)).card then 1 else 0) +
        highCount gs (L ++ [gateFunction L g])

def Budget (k : ℕ) (L : List ((Fin 6 → Bool) → Bool)) : Prop :=
  ∀ W : Finset ℕ,
    (W.biUnion fun j => separated3 (L.getD j (fun _ => false))).card ≤ 4 * (k + W.card)

lemma separated_gate_subset (L : List ((Fin 6 → Bool) → Bool)) (g : Gate) :
    separated3 (gateFunction L g) ⊆
      g.inputs.toFinset.biUnion (fun j => separated3 (L.getD j (fun _ => false))) := by
  classical
  intro w hw
  by_contra hnot
  have hsame : ∀ j ∈ g.inputs,
      L.getD j (fun _ => false) (independent3 w.1) =
        L.getD j (fun _ => false) (augmented3 w.1 w.2) := by
    intro j hj
    by_contra hne
    exact hnot (Finset.mem_biUnion.mpr
      ⟨j, List.mem_toFinset.mpr hj, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hne⟩⟩)
  have hm : g.inputs.map (fun j => L.getD j (fun _ => false) (independent3 w.1)) =
      g.inputs.map (fun j => L.getD j (fun _ => false) (augmented3 w.1 w.2)) :=
    List.map_congr_left hsame
  exact (Finset.mem_filter.mp hw).2 (congrArg g.op.eval hm)

lemma budget_initial (L : List ((Fin 6 → Bool) → Bool))
    (hL : ∀ q ∈ L, (separated3 q).card ≤ 4) : Budget 0 L := by
  intro W
  calc
    (W.biUnion fun j => separated3 (L.getD j (fun _ => false))).card
        ≤ ∑ j ∈ W, (separated3 (L.getD j (fun _ => false))).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ W, 4 := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hjl : j < L.length
      · apply hL
        simpa only [List.getD_eq_getElem L (fun _ => false) hjl] using (List.getElem_mem hjl)
      · rw [List.getD_eq_default _ _ (by omega)]
        simp [separated3]
    _ = 4 * (0 + W.card) := by simp [Nat.mul_comm]

lemma budget_low (k : ℕ) (L : List ((Fin 6 → Bool) → Bool))
    (q : (Fin 6 → Bool) → Bool) (hq : (separated3 q).card ≤ 4)
    (h : Budget k L) : Budget k (L ++ [q]) := by
  classical
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => separated3 ((L ++ [q]).getD j (fun _ => false)))
        ⊆ ((W.erase L.length).biUnion fun j => separated3 (L.getD j (fun _ => false)))
          ∪ separated3 q := by
      intro w hw
      obtain ⟨j, hj, hwj⟩ := Finset.mem_biUnion.mp hw
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hwj
        exact Finset.mem_union_right _ hwj
      · rw [getD_snoc_ne _ _ _ _ hjl] at hwj
        exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_erase.mpr ⟨hjl, hj⟩, hwj⟩)
    have hcard := Finset.card_le_card hsub
    have huni := Finset.card_union_le
      ((W.erase L.length).biUnion fun j => separated3 (L.getD j (fun _ => false)))
      (separated3 q)
    have hold := h (W.erase L.length)
    have he := Finset.card_erase_of_mem hW
    have hpos : 1 ≤ W.card := Finset.card_pos.mpr ⟨_, hW⟩
    omega
  · have heq : (W.biUnion fun j => separated3 ((L ++ [q]).getD j (fun _ => false))) =
        W.biUnion fun j => separated3 (L.getD j (fun _ => false)) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      rw [getD_snoc_ne _ _ _ _ (fun he => hW (he ▸ hj))]
    rw [heq]
    exact h W

lemma budget_high (k : ℕ) (L : List ((Fin 6 → Bool) → Bool))
    (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Budget k L) : Budget (k + 1) (L ++ [gateFunction L g]) := by
  classical
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => separated3
        ((L ++ [gateFunction L g]).getD j (fun _ => false)))
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion
          fun j => separated3 (L.getD j (fun _ => false))) := by
      intro w hw
      obtain ⟨j, hj, hwj⟩ := Finset.mem_biUnion.mp hw
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hwj
        obtain ⟨a, ha, hwa⟩ := Finset.mem_biUnion.mp (separated_gate_subset L g hwj)
        exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_union_right _ ha, hwa⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hwj
        exact Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hjl, hj⟩), hwj⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hpos : 1 ≤ W.card := Finset.card_pos.mpr ⟨_, hW⟩
    have hold := h (W.erase L.length ∪ g.inputs.toFinset)
    have hcard := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => separated3
        ((L ++ [gateFunction L g]).getD j (fun _ => false))) =
        W.biUnion fun j => separated3 (L.getD j (fun _ => false)) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      rw [getD_snoc_ne _ _ _ _ (fun he => hW (he ▸ hj))]
    rw [heq]
    have hold := h W
    omega

lemma budget_wires (gs : List Gate) :
    ∀ (k : ℕ) (L : List ((Fin 6 → Bool) → Bool)),
      (∀ g ∈ gs, g.inputs.length ≤ 2) → Budget k L →
      Budget (k + highCount gs L) (functionWires gs L) := by
  induction gs with
  | nil => intro k L _ h; exact h
  | cons g gs ih =>
    intro k L hf h
    have ht : ∀ a ∈ gs, a.inputs.length ≤ 2 := fun a ha => hf a (List.mem_cons_of_mem _ ha)
    by_cases hq : 4 < (separated3 (gateFunction L g)).card
    · have hs := budget_high k L g (hf g List.mem_cons_self) h
      have hh := ih (k + 1) (L ++ [gateFunction L g]) ht hs
      simpa only [highCount, ite_eq_left hq, functionWires, List.foldl_cons, Nat.add_assoc] using hh
    · have hs := budget_low k L (gateFunction L g) (by omega) h
      have hh := ih k (L ++ [gateFunction L g]) ht hs
      simpa only [highCount, ite_eq_right hq, Nat.zero_add, functionWires, List.foldl_cons] using hh

lemma map_apply_getD (L : List ((Fin 6 → Bool) → Bool)) (j : ℕ) (x : Fin 6 → Bool) :
    (L.map (fun q => q x)).getD j false = L.getD j (fun _ => false) x := by
  induction L generalizing j with
  | nil => simp
  | cons q L ih => cases j <;> simp_all

lemma map_apply_wires (gs : List Gate) (L : List ((Fin 6 → Bool) → Bool))
    (x : Fin 6 → Bool) :
    (functionWires gs L).map (fun q => q x) = wiresFrom gs (L.map fun q => q x) := by
  induction gs generalizing L with
  | nil => rfl
  | cons g gs ih =>
    change (functionWires gs (L ++ [gateFunction L g])).map (fun q => q x) =
      wiresFrom gs (L.map (fun q => q x) ++
        [g.op.eval (g.inputs.map fun j => (L.map (fun q => q x)).getD j false)])
    rw [ih]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil]
    congr 2
    unfold gateFunction
    congr 1
    apply List.map_congr_left
    intro j _
    exact (map_apply_getD L j x).symm

lemma output_capacity_bound (gs : List Gate) (L : List ((Fin 6 → Bool) → Bool))
    (hfanin : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hL : ∀ q ∈ L, (separated3 q).card ≤ 4) (o : ℕ) :
    (separated3 ((functionWires gs L).getD o (fun _ => false))).card ≤
      4 * (highCount gs L + 1) := by
  have h := budget_wires gs 0 L hfanin (budget_initial L hL) {o}
  simpa only [Finset.singleton_biUnion, Finset.card_singleton, Nat.zero_add] using h

lemma highCount_lower (C : Circuit) (L : List ((Fin 6 → Bool) → Bool))
    (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hL : ∀ q ∈ L, (separated3 q).card ≤ 4)
    (hcompute : ∀ x : Fin 6 → Bool,
      C.eval (L.map fun q => q x) = matching x) :
    5 ≤ highCount C.gates L := by
  have hc := output_capacity_bound C.gates L hfanin hL C.output
  have heq : (functionWires C.gates L).getD C.output (fun _ => false) = matching := by
    funext x
    rw [← map_apply_getD, map_apply_wires]
    exact hcompute x
  rw [heq] at hc
  have hm : (separated3 matching).card = 24 := by
    have he : separated3 matching = Finset.univ := by
      ext w
      simp [separated3, independent3_false, augmented3_true]
    rw [he]
    exact obligations3_card
  rw [hm] at hc
  omega

lemma raw_highCount_lower (C : Circuit)
    (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hcompute : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = matching x) :
    5 ≤ highCount C.gates (List.ofFn fun v : Fin 6 => fun x : Fin 6 → Bool => x v) := by
  apply highCount_lower C _ hfanin
  · intro q hq
    obtain ⟨v, hv⟩ := List.mem_ofFn.mp hq
    subst q
    have he : (fun x : Fin 6 → Bool => x v) = orSignal3 {v} := by
      funext x
      simp [orSignal3]
    rw [he]
    exact distinguished3_card_le {v}
  · intro x
    simpa only [List.map_ofFn, Function.comp_def] using hcompute x

def generatedFunctions : List Gate → List ((Fin 6 → Bool) → Bool) →
    List ((Fin 6 → Bool) → Bool)
  | [], _ => []
  | g :: gs, L => gateFunction L g :: generatedFunctions gs (L ++ [gateFunction L g])

lemma generatedFunctions_length (gs : List Gate) (L : List ((Fin 6 → Bool) → Bool)) :
    (generatedFunctions gs L).length = gs.length := by
  induction gs generalizing L with
  | nil => rfl
  | cons g gs ih => simp only [generatedFunctions, List.length_cons, ih]

lemma functionWires_eq_append_generated (gs : List Gate)
    (L : List ((Fin 6 → Bool) → Bool)) :
    functionWires gs L = L ++ generatedFunctions gs L := by
  induction gs generalizing L with
  | nil => simp [functionWires, generatedFunctions]
  | cons g gs ih =>
    change functionWires gs (L ++ [gateFunction L g]) = _
    rw [ih]
    simp only [generatedFunctions, List.append_assoc, List.singleton_append]

lemma highCount_eq_countP (gs : List Gate) (L : List ((Fin 6 → Bool) → Bool)) :
    highCount gs L = (generatedFunctions gs L).countP
      (fun q => decide (4 < (separated3 q).card)) := by
  induction gs generalizing L with
  | nil => rfl
  | cons g gs ih =>
    simp only [highCount, generatedFunctions, List.countP_cons, ih, decide_eq_true_eq]
    omega

lemma highCount_le_length (gs : List Gate) (L : List ((Fin 6 → Bool) → Bool)) :
    highCount gs L ≤ gs.length := by
  rw [highCount_eq_countP]
  exact (List.countP_le_length).trans (by rw [generatedFunctions_length])

lemma highCount_cover_lower (C : Circuit) (L : List ((Fin 6 → Bool) → Bool))
    (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hL : ∀ q ∈ L, (separated3 q).card ≤ 4) (p q : ℕ)
    (hcover : ∀ x : Fin 6 → Bool,
      ((C.wires (L.map fun f => f x)).getD p false ||
        (C.wires (L.map fun f => f x)).getD q false) = matching x) :
    4 ≤ highCount C.gates L := by
  let F := functionWires C.gates L
  let W : Finset ℕ := {p, q}
  have hW : W.card ≤ 2 := by
    have h := Finset.card_insert_le p ({q} : Finset ℕ)
    simpa only [Finset.card_singleton] using h
  have hcov : ∀ x : Fin 6 → Bool,
      (F.getD p (fun _ => false) x || F.getD q (fun _ => false) x) = matching x := by
    intro x
    rw [← map_apply_getD F p x, ← map_apply_getD F q x]
    change (((functionWires C.gates L).map (fun f => f x)).getD p false ||
      ((functionWires C.gates L).map (fun f => f x)).getD q false) = matching x
    rw [map_apply_wires]
    exact hcover x
  have hsub : (Finset.univ : Finset ((Fin 3 → Bool) × Fin 3)) ⊆
      W.biUnion (fun j => separated3 (F.getD j (fun _ => false))) := by
    intro w _
    by_contra hw
    have he : ∀ j ∈ W, F.getD j (fun _ => false) (independent3 w.1) =
        F.getD j (fun _ => false) (augmented3 w.1 w.2) := by
      intro j hj
      by_contra hne
      exact hw (Finset.mem_biUnion.mpr
        ⟨j, hj, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hne⟩⟩)
    have hp := he p (by simp [W])
    have hq := he q (by simp [W])
    have hi := hcov (independent3 w.1)
    have ha := hcov (augmented3 w.1 w.2)
    rw [independent3_false] at hi
    rw [augmented3_true] at ha
    rw [hp, hq, ha] at hi
    cases hi
  have hcard := Finset.card_le_card hsub
  rw [obligations3_card] at hcard
  have hb := budget_wires C.gates 0 L hfanin (budget_initial L hL) W
  change (W.biUnion fun j => separated3 (F.getD j (fun _ => false))).card ≤
    4 * (0 + highCount C.gates L + W.card) at hb
  omega

end WeightedCapacity

def restrictionSources (k : Fin 5) : List ((Fin 6 → Bool) → Bool) :=
  List.ofFn fun i : Fin 10 => fun x : Fin 6 → Bool => matchingRestrictionAt k x i

lemma restriction_sources_capacity (k : Fin 5) :
    ∀ q ∈ restrictionSources k, (separated3 q).card ≤ 4 := by
  intro q hq
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hq
  subst q
  exact restriction_source_capacity k i

lemma petersen_high_count_lower (C : Circuit)
    (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hcompute : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (k : Fin 5) :
    5 ≤ WeightedCapacity.highCount C.gates (restrictionSources k) := by
  apply WeightedCapacity.highCount_lower C (restrictionSources k) hfanin
    (restriction_sources_capacity k)
  intro x
  simpa only [restrictionSources, List.map_ofFn, Function.comp_def,
    five_matching_restrictions] using hcompute (matchingRestrictionAt k x)

lemma petersen_cover_high_count_lower (C : Circuit)
    (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (p q : ℕ)
    (hcover : ∀ x : Fin 10 → Bool,
      ((C.wires (List.ofFn x)).getD p false ||
        (C.wires (List.ofFn x)).getD q false) = petersen x)
    (k : Fin 5) :
    4 ≤ WeightedCapacity.highCount C.gates (restrictionSources k) := by
  apply WeightedCapacity.highCount_cover_lower C (restrictionSources k) hfanin
    (restriction_sources_capacity k) p q
  intro x
  simpa only [restrictionSources, List.map_ofFn, Function.comp_def,
    five_matching_restrictions] using hcover (matchingRestrictionAt k x)

lemma petersen_cover_high_count_sum (C : Circuit)
    (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (p q : ℕ)
    (hcover : ∀ x : Fin 10 → Bool,
      ((C.wires (List.ofFn x)).getD p false ||
        (C.wires (List.ofFn x)).getD q false) = petersen x) :
    20 ≤ ∑ k : Fin 5, WeightedCapacity.highCount C.gates (restrictionSources k) := by
  calc
    20 = ∑ _k : Fin 5, 4 := by decide
    _ ≤ ∑ k : Fin 5, WeightedCapacity.highCount C.gates (restrictionSources k) :=
      Finset.sum_le_sum (fun k _ => petersen_cover_high_count_lower C hfanin p q hcover k)

end PEqualNP.Outside.L_meta_2373_aux
