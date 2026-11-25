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

end PEqualNP.Outside.L_meta_4675.SemanticFold
