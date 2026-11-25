import PEqualNP.Defs

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

end PEqualNP.Outside.L_meta_4675.SemanticFold

namespace PEqualNP.Outside.L_meta_4675.MaskCutFlex

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.TwoColour
open PEqualNP.Outside.L_meta_4675.SemanticFold

abbrev Key := ℕ × Bool

def wv (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def rank (q : Key) : ℕ := 2*q.1 + if q.2 then 1 else 0

def keys (m : ℕ) (B K : Finset ℕ) : Finset Key :=
  ((Finset.range m \ B).image fun i => (i,false)) ∪ (K.image fun i => (i,true))

lemma keys_false (m : ℕ) (B K : Finset ℕ) (i : ℕ) :
    (i,false) ∈ keys m B K ↔ i < m ∧ i ∉ B := by simp [keys]

lemma keys_true (m : ℕ) (B K : Finset ℕ) (i : ℕ) :
    (i,true) ∈ keys m B K ↔ i ∈ K := by simp [keys]

def source {n : ℕ} (B K : Finset ℕ) (a : ℕ → Fin n) (w : ℕ) : Src n Key :=
  if h : w < n then some (Sum.inl ⟨w,h⟩)
  else if w-n ∈ K then some (Sum.inr (w-n,true))
  else if w-n ∈ B then some (Sum.inl (a (w-n))) else some (Sum.inr (w-n,false))

lemma source_key {n : ℕ} (B K : Finset ℕ) (a : ℕ → Fin n) (w : ℕ) (q : Key)
    (h : source B K a w = some (Sum.inr q)) :
    w = n+q.1 ∧ (q.2=false → q.1∉B) ∧ (q.2 = true ↔ q.1 ∈ K) := by
  unfold source at h
  split_ifs at h with hw hK hB
  · simp at h
  · have he : (w-n,true) = q := by simpa using h
    subst q
    simp only [Bool.true_eq_false, false_implies, true_iff]
    exact ⟨by omega,trivial,hK⟩
  · simp at h
  · have he : (w-n,false) = q := by simpa using h
    subst q
    simp only [Bool.false_eq_true, false_iff, forall_true_left]
    exact ⟨by omega,hB,hK⟩

def program {n : ℕ} (C : Circuit) (B K : Finset ℕ) (a : ℕ → Fin n) : Prog n Key :=
  ⟨fun q => if q.2 then true else isA (gateAt C q.1).op,
   fun q b => if q.2 then (if q.1∈B then some (Sum.inl (a q.1)) else some (Sum.inr (q.1,false)))
     else source B K a (opnd C q.1 b)⟩

lemma source_closed {n : ℕ} (C : Circuit) (B K : Finset ℕ) (a : ℕ → Fin n)
    (_hK : K ⊆ Finset.range C.gates.length) (w : ℕ) (hw : w < n+C.gates.length) :
    ∀ q, source B K a w = some (Sum.inr q) → q ∈ keys C.gates.length B K := by
  intro q hq
  obtain ⟨hwire,hB,hKq⟩ := source_key B K a w q hq
  rcases q with ⟨i,t⟩
  cases t
  · exact (keys_false _ _ _ _).mpr ⟨by simp at hwire; omega,hB rfl⟩
  · exact (keys_true _ _ _ _).mpr (hKq.mp rfl)

lemma program_closed {n : ℕ} (C : Circuit) (B K : Finset ℕ) (a : ℕ → Fin n)
    (hAO : IsAO2 n C) (hK : K ⊆ Finset.range C.gates.length) :
    Closed (program C B K a) rank (keys C.gates.length B K) := by
  intro q hq b q' hs
  rcases q with ⟨i,t⟩
  cases t
  · have hi := (keys_false _ _ _ _).mp hq
    change source B K a (opnd C i b) = some (Sum.inr q') at hs
    have hw := opnd_lt hAO hi.1 b
    have hq' := source_closed C B K a hK (opnd C i b) (by omega) q' hs
    have he := (source_key B K a (opnd C i b) q' hs).1
    refine ⟨hq',?_⟩
    rcases q' with ⟨j,t'⟩
    cases t' <;> simp [rank] at * <;> omega
  · have hiK := (keys_true _ _ _ _).mp hq
    change (if i∈B then some (Sum.inl (a i)) else some (Sum.inr (i,false))) = some (Sum.inr q') at hs
    by_cases hiB : i∈B
    · simp [hiB] at hs
    · rw [ite_eq_right hiB] at hs
      have he : (i,false) = q' := by simpa using hs
      subst q'
      refine ⟨(keys_false _ _ _ _).mpr ⟨Finset.mem_range.mp (hK hiK),hiB⟩,?_⟩
      simp [rank]

lemma source_value {n : ℕ} (C : Circuit) (B K : Finset ℕ) (a : ℕ → Fin n)
    (hAO : IsAO2 n C) (hB : B ⊆ Finset.range C.gates.length)
    (hbuf : ∀ i ∈ B, gateAt C i = ⟨GateOp.and,[a i,a i]⟩)
    (w : ℕ) (x : Fin n → Bool) :
    srcAt x (fun q : Key => gateVal n C q.1 x) (source B K a w) = wv n C w x := by
  unfold source
  split_ifs with hw hmemK hmem
  · exact (wireVal_lt C w hw x).symm
  · change gateVal n C (w-n) x = wv n C w x
    change wv n C (n+(w-n)) x = wv n C w x
    rw [Nat.add_sub_of_le (by omega)]
  · change x (a (w-n)) = wv n C w x
    have hj := Finset.mem_range.mp (hB hmem)
    have hg : gateVal n C (w-n) x = x (a (w-n)) := by
      rw [gate_eq C hAO (w-n) hj x]
      simp only [hbuf _ hmem,isA,opv,opnd]
      change (wv n C (a (w-n)) x && wv n C (a (w-n)) x) = _
      have hx : wv n C (a (w-n)) x = x (a (w-n)) :=
        wireVal_lt C (a (w-n)) (a (w-n)).isLt x
      rw [hx]
      simp
    change wv n C (n+(w-n)) x = x (a (w-n)) at hg
    rw [Nat.add_sub_of_le (by omega)] at hg
    exact hg.symm
  · change gateVal n C (w-n) x = wv n C w x
    change wv n C (n+(w-n)) x = wv n C w x
    rw [Nat.add_sub_of_le (by omega)]

lemma program_solution {n : ℕ} (C : Circuit) (B K : Finset ℕ) (a : ℕ → Fin n)
    (hAO : IsAO2 n C) (hB : B ⊆ Finset.range C.gates.length)
    (hbuf : ∀ i ∈ B, gateAt C i = ⟨GateOp.and,[a i,a i]⟩) :
    Sol (program C B K a) (keys C.gates.length B K)
      (fun q x => gateVal n C q.1 x) := by
  intro x q hq
  rcases q with ⟨i,t⟩
  cases t
  · have hi := (keys_false _ _ _ _).mp hq
    change gateVal n C i x = opv (isA (gateAt C i).op)
      (srcAt x (fun q : Key => gateVal n C q.1 x) (source B K a (opnd C i 0)))
      (srcAt x (fun q : Key => gateVal n C q.1 x) (source B K a (opnd C i 1)))
    rw [source_value C B K a hAO hB hbuf,source_value C B K a hAO hB hbuf]
    exact gate_eq C hAO i hi.1 x
  · by_cases hiB : i∈B
    · change gateVal n C i x = opv true
        (srcAt x (fun q : Key => gateVal n C q.1 x) (if i∈B then some (Sum.inl (a i)) else some (Sum.inr (i,false))))
        (srcAt x (fun q : Key => gateVal n C q.1 x) (if i∈B then some (Sum.inl (a i)) else some (Sum.inr (i,false))))
      rw [ite_eq_left hiB,gate_eq C hAO i (Finset.mem_range.mp (hB hiB)) x]
      simp only [hbuf i hiB,isA,opv,opnd]
      change (wv n C (a i) x && wv n C (a i) x) = (x (a i) && x (a i))
      have hx : wv n C (a i) x = x (a i) := wireVal_lt C (a i) (a i).isLt x
      rw [hx]
    · change gateVal n C i x = opv true
        (srcAt x (fun q : Key => gateVal n C q.1 x) (if i∈B then some (Sum.inl (a i)) else some (Sum.inr (i,false))))
        (srcAt x (fun q : Key => gateVal n C q.1 x) (if i∈B then some (Sum.inl (a i)) else some (Sum.inr (i,false))))
      rw [ite_eq_right hiB]
      simp [opv,srcAt]

def labels {n : ℕ} (C : Circuit) (R : Finset ℕ) (S : Finset (Fin n)) (q : Key) : Finset (Fin n) :=
  if q.2 then ∅ else if q.1 ∈ R then S else orIn n C (n+q.1)

lemma source_inside {n : ℕ} (C : Circuit) (B K R : Finset ℕ) (S : Finset (Fin n))
    (a : ℕ → Fin n) (hS : ∀ i ∈ B, a i ∈ S)
    (w : ℕ) (hraw : orIn n C w ⊆ S) :
    srcReach (labels C R S) (source B K a w) ⊆ S := by
  unfold source
  split_ifs with hw hK hB
  · change {⟨w,hw⟩} ⊆ S
    rwa [orIn_input (C := C) ⟨w,hw⟩] at hraw
  · simp [srcReach,labels]
  · change {a (w-n)} ⊆ S
    simpa using hS (w-n) hB
  · change (if w-n∈R then S else orIn n C (n+(w-n))) ⊆ S
    split_ifs
    · exact Finset.Subset.refl _
    · rwa [Nat.add_sub_of_le (by omega)]

lemma source_outside {n : ℕ} (C : Circuit) (B K R : Finset ℕ) (S : Finset (Fin n))
    (a : ℕ → Fin n) (w : ℕ)
    (hboundary : ∀ i, w=n+i → (i∈B ∨ i∈R) → i∈K) :
    srcReach (labels C R S) (source B K a w) ⊆ orIn n C w := by
  unfold source
  split_ifs with hw hK hB
  · change {⟨w,hw⟩} ⊆ orIn n C w
    rw [orIn_input (C := C) ⟨w,hw⟩]
  · simp [srcReach,labels]
  · have he : w=n+(w-n) := by omega
    exact False.elim (hK (hboundary (w-n) he (Or.inl hB)))
  · have he : w=n+(w-n) := by omega
    have hR : w-n∉R := fun h => hK (hboundary (w-n) he (Or.inr h))
    change (if w-n∈R then S else orIn n C (n+(w-n))) ⊆ orIn n C w
    rw [ite_eq_right hR,←he]

lemma program_reach {n : ℕ} (C : Circuit) (B K R : Finset ℕ) (S : Finset (Fin n))
    (a : ℕ → Fin n) (hAO : IsAO2 n C)
    (hS : ∀ i ∈ B, a i ∈ S)
    (hregion : ∀ r ∈ R, ∀ b : Fin 2, orIn n C (opnd C r b) ⊆ S)
    (hboundary : ∀ r < C.gates.length, r∉R → (gateAt C r).op=GateOp.or →
      ∀ b : Fin 2, ∀ i, opnd C r b=n+i → (i∈B ∨ i∈R) → i∈K) :
    ∀ q ∈ keys C.gates.length B K, (program C B K a).1 q=false →
      srcReach (labels C R S) ((program C B K a).2 q 0) ∪
      srcReach (labels C R S) ((program C B K a).2 q 1) ⊆ labels C R S q := by
  intro q hq hop
  rcases q with ⟨r,t⟩
  cases t
  · have hr := ((keys_false _ _ _ _).mp hq).1
    have hor : (gateAt C r).op=GateOp.or := by
      have hmem : gateAt C r ∈ C.gates := by
        unfold gateAt
        rw [List.getD_eq_getElem _ _ hr]
        exact List.getElem_mem hr
      rcases hAO.1 _ hmem with h | h
      · change isA (gateAt C r).op=false at hop
        simp [h,isA] at hop
      · exact h
    change srcReach (labels C R S) (source B K a (opnd C r 0)) ∪
      srcReach (labels C R S) (source B K a (opnd C r 1)) ⊆
      (if r∈R then S else orIn n C (n+r))
    by_cases hrR : r∈R
    · rw [ite_eq_left hrR]
      exact Finset.union_subset
        (source_inside C B K R S a hS _ (hregion r hrR 0))
        (source_inside C B K R S a hS _ (hregion r hrR 1))
    · rw [ite_eq_right hrR,orIn_or hAO hr hor]
      exact Finset.union_subset_union
        (source_outside C B K R S a _ (hboundary r hr hrR hor 0))
        (source_outside C B K R S a _ (hboundary r hr hrR hor 1))
  · change true=false at hop
    cases hop

lemma program_color {n : ℕ} (C : Circuit) (B K R : Finset ℕ) (S : Finset (Fin n))
    (a : ℕ → Fin n) (hAO : IsAO2 n C) (s : ℕ → Bool) (hz : tCount n C s=0)
    (hmono : ∀ u∈S, ∀ v∈S, s u=s v) :
    ∀ q ∈ keys C.gates.length B K, (program C B K a).1 q=false →
      ∀ u∈labels C R S q, ∀ v∈labels C R S q, s u=s v := by
  intro q hq hop u hu v hv
  rcases q with ⟨r,t⟩
  cases t
  · have hr := ((keys_false _ _ _ _).mp hq).1
    have hor : (gateAt C r).op=GateOp.or := by
      have hmem : gateAt C r ∈ C.gates := by
        unfold gateAt
        rw [List.getD_eq_getElem _ _ hr]
        exact List.getElem_mem hr
      rcases hAO.1 _ hmem with h | h
      · change isA (gateAt C r).op=false at hop
        simp [h,isA] at hop
      · exact h
    by_cases hrR : r∈R
    · simp only [labels,Bool.false_eq_true,ite_false,ite_eq_left hrR] at hu hv
      exact hmono u hu v hv
    · simp only [labels,Bool.false_eq_true,ite_false,ite_eq_right hrR] at hu hv
      exact tCount_zero_good C s hz r hr hor u hu v hv
  · change true=false at hop
    cases hop

lemma keys_budget (m : ℕ) (B K : Finset ℕ) (hB : B ⊆ Finset.range m) :
    (keys m B K).card+B.card ≤ m+K.card := by
  have hU := Finset.card_union_le
    ((Finset.range m \ B).image fun i => (i,false)) (K.image fun i => (i,true))
  have h0 := Finset.card_image_le (s := Finset.range m \ B) (f := fun i => (i,false))
  have h1 := Finset.card_image_le (s := K) (f := fun i => (i,true))
  have h2 := Finset.card_sdiff_add_card_eq_card hB
  rw [Finset.card_range] at h2
  change (keys m B K).card ≤ _ at hU
  omega

lemma relocate_input_buffers {n : ℕ} (C : Circuit) (B K R : Finset ℕ) (S : Finset (Fin n))
    (a : ℕ → Fin n) (hAO : IsAO2 n C) (s : ℕ → Bool) (hz : tCount n C s=0)
    (hB : B ⊆ Finset.range C.gates.length) (hK : K ⊆ Finset.range C.gates.length)
    (hbuf : ∀ i∈B, gateAt C i=⟨GateOp.and,[a i,a i]⟩)
    (hS : ∀ i∈B, a i∈S) (hmono : ∀ u∈S, ∀ v∈S, s u=s v)
    (hregion : ∀ r∈R, ∀ b : Fin 2, orIn n C (opnd C r b) ⊆ S)
    (hboundary : ∀ r<C.gates.length, r∉R → (gateAt C r).op=GateOp.or →
      ∀ b : Fin 2, ∀ i, opnd C r b=n+i → (i∈B ∨ i∈R) → i∈K)
    (hpos : circuitFun n C (fun _=>true)=true) :
    ∃ D : Circuit, IsAO2 n D ∧ tCount n D s=0 ∧ circuitFun n D=circuitFun n C ∧
      D.size+B.card ≤ C.size+K.card := by
  classical
  have hout := output_lt_of_true C (fun _=>true) hpos
  obtain ⟨D,hD,hDz,hsize,hfun,_⟩ := fold_prog (program C B K a) rank
    (fun q x=>gateVal n C q.1 x) (keys C.gates.length B K) (labels C R S) s
    (program_closed C B K a hAO hK) (program_solution C B K a hAO hB hbuf)
    (program_reach C B K R S a hAO hS hregion hboundary)
    (program_color C B K R S a hAO s hz hmono)
    (source B K a C.output) (source_closed C B K a hK C.output hout) (by
      rw [source_value C B K a hAO hB hbuf]
      exact hpos)
  refine ⟨D,hD,hDz,?_,?_⟩
  · funext x
    rw [hfun x,source_value C B K a hAO hB hbuf]
    rfl
  · have hsub : kept (program C B K a) (fun q x=>gateVal n C q.1 x)
        (keys C.gates.length B K) ⊆ keys C.gates.length B K := Finset.filter_subset _ _
    have hc := Finset.card_le_card hsub
    have hb := keys_budget C.gates.length B K hB
    change D.gates.length+B.card ≤ C.gates.length+K.card
    change D.gates.length ≤ _ at hsize
    omega

end PEqualNP.Outside.L_meta_4675.MaskCutFlex


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

end PEqualNP.Outside.L_meta_4675.StructuralPrefix


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

end PEqualNP.Outside.L_meta_4675.Redirect

namespace PEqualNP.Outside.L_meta_4675.StructuralPrefix

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount

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


namespace PEqualNP.Outside.L_meta_4675.BufferBoundary

open PEqualNP.SplitCount
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

noncomputable def region (n : ℕ) (C : Circuit) (B : Finset ℕ) (S : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun r =>
    (gateAt C r).op = GateOp.or ∧ orIn n C (n+r) ⊆ S ∧
      ∃ i ∈ B, OrReaches n C (n+r) i

lemma mem_region {n : ℕ} {C : Circuit} {B : Finset ℕ} {S : Finset (Fin n)} {r : ℕ} :
    r ∈ region n C B S ↔ r < C.gates.length ∧ (gateAt C r).op = GateOp.or ∧
      orIn n C (n+r) ⊆ S ∧ ∃ i ∈ B, OrReaches n C (n+r) i := by
  classical
  simp [region]

noncomputable def boundary (n : ℕ) (C : Circuit) (B : Finset ℕ) (S : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (B ∪ region n C B S).filter fun i => ∃ r < C.gates.length,
    (gateAt C r).op = GateOp.or ∧ r ∉ region n C B S ∧ n+i ∈ (gateAt C r).inputs

lemma affected_path {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (B : Finset ℕ) (S : Finset (Fin n)) (hB : B ⊆ Finset.range C.gates.length)
    {i : ℕ} (hi : i ∈ B ∪ region n C B S) : ∃ b ∈ B, OrReaches n C (n+i) b := by
  rcases Finset.mem_union.mp hi with hi | hi
  · exact ⟨i, hi, Redirect.orReaches_self hAO (Finset.mem_range.mp (hB hi))⟩
  · exact (mem_region.mp hi).2.2.2

lemma affected_compatible {n : ℕ} {C : Circuit} (B : Finset ℕ) (S : Finset (Fin n))
    (hB : ∀ i ∈ B, orIn n C (n+i) ⊆ S)
    {i : ℕ} (hi : i ∈ B ∪ region n C B S) : orIn n C (n+i) ⊆ S := by
  rcases Finset.mem_union.mp hi with hi | hi
  · exact hB i hi
  · exact (mem_region.mp hi).2.2.1

lemma reader_path {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {r i b : ℕ} (hr : r < C.gates.length) (hor : (gateAt C r).op = GateOp.or)
    (hi : n+i ∈ (gateAt C r).inputs) (hpath : OrReaches n C (n+i) b) :
    OrReaches n C (n+r) b := by
  rw [Redirect.inputs_eq_pair hAO hr] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  apply (Redirect.orReaches_iff hAO (n+r) b).mpr
  refine ⟨r, hr, rfl, Or.inr ⟨hor, ?_⟩⟩
  rcases hi with hi | hi
  · exact ⟨0, by rw [← hi]; exact hpath⟩
  · exact ⟨1, by rw [← hi]; exact hpath⟩

lemma compatible_reader_in_region {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (B : Finset ℕ) (S : Finset (Fin n)) (hB : B ⊆ Finset.range C.gates.length)
    {r i : ℕ} (hr : r < C.gates.length) (hor : (gateAt C r).op = GateOp.or)
    (hi : i ∈ B ∪ region n C B S) (hin : n+i ∈ (gateAt C r).inputs)
    (hcomp : orIn n C (n+r) ⊆ S) : r ∈ region n C B S := by
  obtain ⟨b, hb, hpath⟩ := affected_path hAO B S hB hi
  exact mem_region.mpr ⟨hr, hor, hcomp, b, hb, reader_path hAO hr hor hin hpath⟩

lemma outside_reader_unique {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (B : Finset ℕ) (S : Finset (Fin n)) (hB : B ⊆ Finset.range C.gates.length)
    (hcompB : ∀ i ∈ B, orIn n C (n+i) ⊆ S)
    {r i j : ℕ} (hr : r < C.gates.length) (hor : (gateAt C r).op = GateOp.or)
    (hout : r ∉ region n C B S)
    (hi : i ∈ B ∪ region n C B S) (hj : j ∈ B ∪ region n C B S)
    (hir : n+i ∈ (gateAt C r).inputs) (hjr : n+j ∈ (gateAt C r).inputs) : i = j := by
  by_contra hij
  have hci := affected_compatible B S hcompB hi
  have hcj := affected_compatible B S hcompB hj
  apply hout
  apply compatible_reader_in_region hAO B S hB hr hor hi hir
  rw [Redirect.inputs_eq_pair hAO hr] at hir hjr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hir hjr
  rw [Redirect.orIn_or hAO hr hor]
  rcases hir with hi0 | hi1 <;> rcases hjr with hj0 | hj1
  · omega
  · exact Finset.union_subset (by rw [← hi0]; exact hci) (by rw [← hj1]; exact hcj)
  · exact Finset.union_subset (by rw [← hj0]; exact hcj) (by rw [← hi1]; exact hci)
  · omega

lemma boundary_card_le_readers {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (B : Finset ℕ) (S : Finset (Fin n)) (hB : B ⊆ Finset.range C.gates.length)
    (hcompB : ∀ i ∈ B, orIn n C (n+i) ⊆ S) (P : Finset ℕ)
    (hP : ∀ r < C.gates.length, (gateAt C r).op = GateOp.or → r ∉ region n C B S →
      ∀ i ∈ B ∪ region n C B S, n+i ∈ (gateAt C r).inputs → r ∈ P) :
    (boundary n C B S).card ≤ P.card := by
  classical
  have hex (i : ℕ) (hi : i ∈ boundary n C B S) : ∃ r < C.gates.length,
      (gateAt C r).op = GateOp.or ∧ r ∉ region n C B S ∧ n+i ∈ (gateAt C r).inputs :=
    (Finset.mem_filter.mp hi).2
  let f : ℕ → ℕ := fun i => if hi : i ∈ boundary n C B S then (hex i hi).choose else 0
  have hf (i : ℕ) (hi : i ∈ boundary n C B S) : f i < C.gates.length ∧
      (gateAt C (f i)).op = GateOp.or ∧ f i ∉ region n C B S ∧ n+i ∈ (gateAt C (f i)).inputs := by
    simp only [f, hi, dite_eq_left]
    exact (hex i hi).choose_spec
  apply Finset.card_le_card_of_injOn f
  · intro i hi
    obtain ⟨hr, hor, hout, hin⟩ := hf i hi
    exact hP (f i) hr hor hout i (Finset.mem_filter.mp hi).1 hin
  · intro i hi j hj he
    obtain ⟨hr, hor, hout, hin⟩ := hf i hi
    have hjn := (hf j hj).2.2.2
    rw [← he] at hjn
    exact outside_reader_unique hAO B S hB hcompB hr hor hout
      (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hin hjn

lemma region_operands_compatible {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (B : Finset ℕ) (S : Finset (Fin n)) :
    ∀ r ∈ region n C B S, ∀ b : Fin 2, orIn n C (opnd C r b) ⊆ S := by
  intro r hr b
  obtain ⟨hlen, hor, hsub, _⟩ := mem_region.mp hr
  rw [Redirect.orIn_or hAO hlen hor] at hsub
  fin_cases b
  · exact (Finset.union_subset_iff.mp hsub).1
  · exact (Finset.union_subset_iff.mp hsub).2

lemma boundary_valid {n : ℕ} {C : Circuit} (B : Finset ℕ) (S : Finset (Fin n))
    (hB : B ⊆ Finset.range C.gates.length) :
    boundary n C B S ⊆ Finset.range C.gates.length := by
  classical
  intro i hi
  rcases Finset.mem_union.mp (Finset.mem_filter.mp hi).1 with hi | hi
  · exact hB hi
  · exact Finset.mem_range.mpr (mem_region.mp hi).1

lemma boundary_condition {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (B : Finset ℕ) (S : Finset (Fin n)) :
    ∀ r < C.gates.length, r ∉ region n C B S → (gateAt C r).op = GateOp.or →
      ∀ b : Fin 2, ∀ i, opnd C r b = n+i → (i∈B ∨ i∈region n C B S) →
        i∈boundary n C B S := by
  classical
  intro r hr hout hor b i he hi
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_union.mpr hi, r, hr, hor, hout,
    he ▸ Redirect.opnd_mem_inputs hAO hr b⟩


lemma outside_reader_mixed {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (B : Finset ℕ) (S : Finset (Fin n)) (hB : B ⊆ Finset.range C.gates.length)
    (col : Fin n → Bool) (c : Bool) (hS : ∀ a, a ∈ S ↔ col a = c)
    (hunit : ∀ i ∈ B, ∃ a ∈ S, gateVal n C i (unitInput a) = true)
    {r i : ℕ} (hr : r < C.gates.length) (hor : (gateAt C r).op = GateOp.or)
    (hout : r ∉ region n C B S) (hi : i ∈ B ∪ region n C B S)
    (hin : n+i ∈ (gateAt C r).inputs) :
    ∃ a p : Fin n, col a = c ∧ col p ≠ c ∧ gateVal n C r (unitInput a) = true ∧
      gateVal n C r (unitInput p) = true ∧ p ∈ orIn n C (n+r) := by
  classical
  have hncomp : ¬ orIn n C (n+r) ⊆ S := fun hc =>
    hout (compatible_reader_in_region hAO B S hB hr hor hi hin hc)
  obtain ⟨p, hp, hpS⟩ := Finset.not_subset.mp hncomp
  obtain ⟨b, hb, hbpath⟩ := affected_path hAO B S hB hi
  obtain ⟨a, haS, ha⟩ := hunit b hb
  have hpath := reader_path hAO hr hor hin hbpath
  refine ⟨a, p, (hS a).mp haS, (fun he => hpS ((hS p).mpr he)), ?_, ?_, hp⟩
  · exact Redirect.wireVal_of_orReaches hAO (n+r) b hpath (unitInput a) ha
  · exact Redirect.wireVal_true_of_mem_orIn hAO
      (x := unitInput p) (i := p) (by simp [unitInput]) (n+r) hp

noncomputable def paidOpp {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (col : Fin n → Bool) (c : Bool) : Finset ℕ := by
  classical
  exact (orN G C \ lam G C).filter fun r => ∃ p ∈ orIn n C (n+r), col p ≠ c

lemma outside_reader_paidOpp {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C)
    (B : Finset ℕ) (S : Finset (Fin n)) (hB : B ⊆ Finset.range C.gates.length)
    (col : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → col a ≠ col b)
    (c : Bool) (hS : ∀ a, a ∈ S ↔ col a = c)
    (hunit : ∀ i ∈ B, ∃ a ∈ S, gateVal n C i (unitInput a) = true)
    {r i : ℕ} (hr : r < C.gates.length) (hor : (gateAt C r).op = GateOp.or)
    (hout : r ∉ region n C B S) (hi : i ∈ B ∪ region n C B S)
    (hin : n+i ∈ (gateAt C r).inputs) : r ∈ paidOpp G C col c := by
  classical
  obtain ⟨a, p, ha, hp, hga, hgp, hpin⟩ :=
    outside_reader_mixed hAO B S hB col c hS hunit hr hor hout hi hin
  apply Finset.mem_filter.mpr
  refine ⟨StructuralPrefix.semantic_mixed_or_mem_paid G hAO col hcol hr hor ?_ hga hgp,
    p, hpin, hp⟩
  intro he
  exact hp (he.symm.trans ha)

lemma boundary_card_le_paidOpp {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hAO : IsAO2 n C)
    (B : Finset ℕ) (S : Finset (Fin n)) (hB : B ⊆ Finset.range C.gates.length)
    (hcompB : ∀ i ∈ B, orIn n C (n+i) ⊆ S)
    (col : Fin n → Bool) (hcol : ∀ a b, G.Adj a b → col a ≠ col b)
    (c : Bool) (hS : ∀ a, a ∈ S ↔ col a = c)
    (hunit : ∀ i ∈ B, ∃ a ∈ S, gateVal n C i (unitInput a) = true) :
    (boundary n C B S).card ≤ (paidOpp G C col c).card := by
  apply boundary_card_le_readers hAO B S hB hcompB
  intro r hr hor hout i hi hin
  exact outside_reader_paidOpp G hAO B S hB col hcol c hS hunit hr hor hout hi hin

lemma paidOpp_disjoint {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (s : ℕ → Bool) (hz : PEqualNP.TwoColour.tCount n C s = 0) :
    Disjoint (paidOpp G C (fun a => s a) false) (paidOpp G C (fun a => s a) true) := by
  classical
  apply Finset.disjoint_left.mpr
  intro r hf ht
  obtain ⟨hpaid, p, hp, hpc⟩ := Finset.mem_filter.mp hf
  obtain ⟨_, q, hq, hqc⟩ := Finset.mem_filter.mp ht
  have hpt : s p = true := by cases hs : s p <;> simp_all
  have hqf : s q = false := by cases hs : s q <;> simp_all
  have hN := (Finset.mem_sdiff.mp hpaid).1
  have hr : r < C.gates.length ∧ (gateAt C r).op = GateOp.or ∧ ¬ BelowF G C r := by
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using hN
  have htwo : PEqualNP.TwoColour.IsTwoColour n C s r :=
    ⟨hr.1, hr.2.1, ⟨q, hq, hqf⟩, ⟨p, hp, hpt⟩⟩
  have hempty : PEqualNP.TwoColour.twoColour n C s = ∅ := Finset.card_eq_zero.mp hz
  have hmem : r ∈ PEqualNP.TwoColour.twoColour n C s :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr.1, htwo⟩
  rw [hempty] at hmem
  exact Finset.notMem_empty _ hmem

lemma paidOpp_card_sum_le {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (s : ℕ → Bool) (hz : PEqualNP.TwoColour.tCount n C s = 0) :
    (paidOpp G C (fun a => s a) false).card + (paidOpp G C (fun a => s a) true).card ≤
      (orN G C \ lam G C).card := by
  classical
  rw [← Finset.card_union_of_disjoint (paidOpp_disjoint G s hz)]
  apply Finset.card_le_card
  intro r hr
  rcases Finset.mem_union.mp hr with hr | hr <;> exact (Finset.mem_filter.mp hr).1

end PEqualNP.Outside.L_meta_4675.BufferBoundary
namespace PEqualNP.Outside.L_meta_4675.InputBufferCharge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.TwoColour
  PEqualNP.SplitCount
open PEqualNP.Outside.L_meta_4675.BufferBoundary

lemma one_colour {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (B : Finset ℕ) (a : ℕ → Fin n) (s : ℕ → Bool) (c : Bool)
    (hAO : IsAO2 n C) (hz : tCount n C s=0)
    (hcol : ∀ u v,G.Adj u v → s u ≠ s v)
    (hB : B ⊆ Finset.range C.gates.length)
    (hbuf : ∀ i∈B,gateAt C i=⟨GateOp.and,[a i,a i]⟩)
    (hc : ∀ i∈B,s (a i)=c)
    (hpos : circuitFun n C (fun _=>true)=true)
    (hmin : ∀ D,IsAO2 n D → circuitFun n D=circuitFun n C → tCount n D s=0 → C.size≤D.size) :
    B.card≤(paidOpp G C (fun u=>s u) c).card := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun u=>s u=c
  have hS (u : Fin n) : u∈S ↔ s u=c := by simp [S]
  have hBufS : ∀ i∈B,a i∈S := fun i hi=>(hS _).mpr (hc i hi)
  have hmono : ∀ u∈S,∀v∈S,s u=s v := by
    intro u hu v hv
    exact ((hS u).mp hu).trans ((hS v).mp hv).symm
  obtain ⟨D,hD,hDz,hDf,hsize⟩ := MaskCutFlex.relocate_input_buffers C B (boundary n C B S)
    (region n C B S) S a hAO s hz hB (boundary_valid B S hB) hbuf hBufS hmono
    (region_operands_compatible hAO B S) (boundary_condition hAO B S) hpos
  have hsmall := hmin D hD hDf hDz
  have hBK : B.card≤(boundary n C B S).card := by omega
  apply hBK.trans
  apply boundary_card_le_paidOpp G hAO B S hB
  · intro i hi
    rw [Redirect.orIn_and hAO (Finset.mem_range.mp (hB hi)) (by rw [hbuf i hi])]
    exact Finset.empty_subset _
  · exact hcol
  · exact hS
  · intro i hi
    refine ⟨a i,hBufS i hi,?_⟩
    change wireVal n C (n+i) (unitInput (a i))=true
    rw [Redirect.wireVal_and hAO (Finset.mem_range.mp (hB hi)) (by rw [hbuf i hi])]
    simp only [opnd,hbuf i hi]
    change (wireVal n C (a i) (unitInput (a i)) && wireVal n C (a i) (unitInput (a i)))=true
    rw [Redirect.wireVal_input C (a i) (unitInput (a i))]
    simp [unitInput]

lemma all_input_buffers_le_paid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (B : Finset ℕ) (a : ℕ → Fin n) (s : ℕ → Bool)
    (hAO : IsAO2 n C) (hz : tCount n C s=0)
    (hcol : ∀ u v,G.Adj u v → s u ≠ s v)
    (hB : B ⊆ Finset.range C.gates.length)
    (hbuf : ∀ i∈B,gateAt C i=⟨GateOp.and,[a i,a i]⟩)
    (hpos : circuitFun n C (fun _=>true)=true)
    (hmin : ∀ D,IsAO2 n D → circuitFun n D=circuitFun n C → tCount n D s=0 → C.size≤D.size) :
    B.card≤(orN G C \ lam G C).card := by
  classical
  have hpart (c : Bool) := one_colour G C (B.filter fun i=>s (a i)=c) a s c hAO hz hcol
    (fun i hi=>hB (Finset.mem_filter.mp hi).1)
    (fun i hi=>hbuf i (Finset.mem_filter.mp hi).1)
    (fun i hi=>(Finset.mem_filter.mp hi).2) hpos hmin
  have hsum := paidOpp_card_sum_le G s hz
  have hcard : (B.filter fun i=>s (a i)=false).card+(B.filter fun i=>s (a i)=true).card=B.card := by
    simpa using Finset.card_filter_add_card_filter_not (s := B) (fun i=>s (a i)=false)
  have h0 := hpart false
  have h1 := hpart true
  omega

end PEqualNP.Outside.L_meta_4675.InputBufferCharge
