import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3566

abbrev heawood : SimpleGraph (Fin 14) :=
  SimpleGraph.fromRel fun u v =>
    u.val < 7 ∧ 7 ≤ v.val ∧ (v.val - 7 + 7 - u.val) % 7 ∈ ([0, 1, 3] : List ℕ)

lemma heawood_bipartite :
    ∃ c : Fin 14 → Bool, ∀ u v : Fin 14, heawood.Adj u v → c u ≠ c v := by
  refine ⟨fun u => decide (u.val < 7), ?_⟩
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
lemma heawood_no_four : PEqualNP.TopForm.NoFourCycle heawood := by
  decide

lemma heawood_degree : ∀ z : Fin 14, heawood.degree z = 3 := by
  decide

lemma heawood_edges : heawood.edgeFinset.card = 21 := by
  decide

lemma heawood_no_leaf : ¬ ∃ z : Fin 14, heawood.degree z ≤ 2 := by
  intro ⟨z, hz⟩
  have hd := heawood_degree z
  omega


abbrev heawoodLeft (i : Fin 7) : Fin 14 := ⟨i.val, by omega⟩
abbrev heawoodRight (i : Fin 7) : Fin 14 := ⟨i.val + 7, by omega⟩

lemma heawood_matching : ∀ i : Fin 7, heawood.Adj (heawoodLeft i) (heawoodRight i) := by
  decide

lemma heawood_cover_lower (S : Finset (Fin 14))
    (hS : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover heawood S) :
    7 ≤ S.card := by
  let f (i : Fin 7) : Fin 14 := if heawoodLeft i ∈ S then heawoodLeft i else heawoodRight i
  have hmem (i : Fin 7) : f i ∈ S := by
    dsimp [f]
    split_ifs with h
    · exact h
    · exact (hS _ _ (heawood_matching i)).resolve_left h
  have hfmod (i : Fin 7) : (f i).val % 7 = i.val := by
    dsimp [f]
    split_ifs <;> dsimp [heawoodLeft, heawoodRight] <;> omega
  have hinj : Function.Injective (fun i : Fin 7 => (⟨f i, hmem i⟩ : S)) := by
    intro i j hij
    have heq : f i = f j := congrArg Subtype.val hij
    have hi := hfmod i
    have hj := hfmod j
    apply Fin.ext
    rw [heq] at hi
    omega
  have hc := Fintype.card_le_of_injective _ hinj
  simpa using hc

abbrev heawoodCover : Finset (Fin 14) := Finset.univ.filter (fun z => z.val < 7)

lemma heawood_cover_valid :
    PEqualNP.MetaComplexity.CoverPromise.IsVertexCover heawood heawoodCover := by
  unfold PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
  decide

lemma heawood_cover_card : heawoodCover.card = 7 := by
  decide


abbrev heawoodCutCover (z : Fin 14) : Finset (Fin 14) :=
  Finset.univ.filter (fun v => (v.val < 7 ↔ z.val < 7) ∧ v ≠ z)

set_option synthInstance.maxSize 1000 in
lemma heawood_cut_cover_valid : ∀ z : Fin 14,
    PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
      (heawood.deleteEdges (heawood.incidenceSet z)) (heawoodCutCover z) := by
  unfold PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
  simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.mk'_mem_incidenceSet_iff]
  decide

lemma heawood_cut_cover_card : ∀ z : Fin 14, (heawoodCutCover z).card = 6 := by
  decide

lemma heawood_cut_cover_drop (z : Fin 14) :
    ∃ S : Finset (Fin 14), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
        (heawood.deleteEdges (heawood.incidenceSet z)) S ∧
      ∀ T : Finset (Fin 14), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover heawood T →
        S.card < T.card := by
  refine ⟨heawoodCutCover z, heawood_cut_cover_valid z, ?_⟩
  intro T hT
  have h := heawood_cover_lower T hT
  rw [heawood_cut_cover_card]
  omega


lemma heawood_cut_cover_lower (z : Fin 14) (S : Finset (Fin 14))
    (hS : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
      (heawood.deleteEdges (heawood.incidenceSet z)) S) :
    6 ≤ S.card := by
  have hfull : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover heawood (insert z S) := by
    intro a b hab
    by_cases hza : z = a
    · exact Or.inl (by simp [← hza])
    by_cases hzb : z = b
    · exact Or.inr (by simp [← hzb])
    have hcut : (heawood.deleteEdges (heawood.incidenceSet z)).Adj a b := by
      simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.mk'_mem_incidenceSet_iff]
      exact ⟨hab, fun h => h.2.elim hza hzb⟩
    rcases hS a b hcut with ha | hb
    · exact Or.inl (Finset.mem_insert_of_mem ha)
    · exact Or.inr (Finset.mem_insert_of_mem hb)
  have h := heawood_cover_lower (insert z S) hfull
  have hcard := Finset.card_insert_le z S
  omega


namespace Pruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge

abbrev Src (n : ℕ) (ι : Type) := Option (Fin n ⊕ ι)


def srcAt {n : ℕ} {ι : Type} (x : Fin n → Bool) (t : ι → Bool) (s : Src n ι) : Bool :=
  s.elim false (Sum.elim x t)


def opv (a : Bool) (p q : Bool) : Bool := if a then p && q else p || q

lemma opv_mono (a p q p' q' : Bool) (h : p = true → p' = true) (h' : q = true → q' = true) :
    opv a p q = true → opv a p' q' = true := by
  cases a <;> cases p <;> cases q <;> cases p' <;> cases q' <;> simp_all [opv]

abbrev Prog (n : ℕ) (ι : Type) := (ι → Bool) × (ι → Fin 2 → Src n ι)

def Prog.isAnd {n : ℕ} {ι : Type} (P : Prog n ι) : ι → Bool := P.1

def Prog.src {n : ℕ} {ι : Type} (P : Prog n ι) : ι → Fin 2 → Src n ι := P.2

variable {n : ℕ} {ι : Type}


def Closed (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) : Prop :=
  ∀ i ∈ K, ∀ b : Fin 2, ∀ j : ι, P.src i b = some (Sum.inr j) → j ∈ K ∧ rank j < rank i


def SolAt (P : Prog n ι) (K : Finset ι) (x : Fin n → Bool) (t : ι → Bool) : Prop :=
  ∀ i ∈ K, t i = opv (P.isAnd i) (srcAt x t (P.src i 0)) (srcAt x t (P.src i 1))


def Sol (P : Prog n ι) (K : Finset ι) (v : ι → (Fin n → Bool) → Bool) : Prop :=
  ∀ x, SolAt P K x (fun i => v i x)

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


def Res (gs : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∀ x, f x = false) ∨ (f (fun _ => true) = true ∧ ∃ w < n + gs.length, ∀ x, wireVal n ⟨gs, 0⟩ w x = f x)

lemma res_mono (gs : List Gate) (g : Gate) (f : (Fin n → Bool) → Bool) (h : Res gs f) :
    Res (gs ++ [g]) f := by
  rcases h with h | ⟨h1, w, hw, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, w, by simp; omega, fun x => ?_⟩
    rw [wireVal_old gs g w hw x, h2 x]

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
  K.filter fun i => srcAt (fun _ => true) (fun j => v j fun _ => true) (P.src i 0) = true ∧
    srcAt (fun _ => true) (fun j => v j fun _ => true) (P.src i 1) = true

lemma build (P : Prog n ι) (rank : ι → ℕ) (v : ι → (Fin n → Bool) → Bool) (K : Finset ι)
    (hcl : Closed P rank K) (hv : Sol P K v) :
    ∃ gs : List Gate, IsAO2 n ⟨gs, 0⟩ ∧ gs.length ≤ (kept P v K).card ∧ ∀ i ∈ K, Res gs (v i) := by
  classical
  induction K using Finset.induction_on_max_value rank with
  | empty =>
    refine ⟨[], ⟨?_, ?_, ?_⟩, by simp, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    · intro g hg; simp at hg
    · intro j hj; simp at hj
    · intro g hg; simp at hg
  | insert a s ha hmax ih =>
    have hs : Closed P rank s := by
      intro i hi b j hj
      obtain ⟨h1, h2⟩ := hcl i (Finset.mem_insert_of_mem hi) b j hj
      refine ⟨(Finset.mem_insert.1 h1).resolve_left ?_, h2⟩
      rintro rfl
      exact absurd (hmax i hi) (by omega)
    obtain ⟨gs, hAO, hlen, hres⟩ := ih hs fun x i hi => hv x i (Finset.mem_insert_of_mem hi)
    have hsrc' : ∀ b : Fin 2, Res gs (fun x => srcAt x (fun j => v j x) (P.src a b)) := by
      intro b
      rcases hb : P.src a b with _ | (c | j)
      · exact Or.inl fun x => rfl
      · exact Or.inr ⟨rfl, c, by have := c.2; omega, fun x => wireVal_input gs c x⟩
      · obtain ⟨h1, h2⟩ := hcl a (Finset.mem_insert_self a s) b j hb
        refine hres j ((Finset.mem_insert.1 h1).resolve_left ?_)
        rintro rfl
        exact absurd h2 (lt_irrefl _)
    have hsrc : ∀ b : Fin 2, (∀ x, srcAt x (fun j => v j x) (P.src a b) = false) ∨
        (srcAt (fun _ => true) (fun j => v j fun _ => true) (P.src a b) = true ∧ ∃ w < n + gs.length,
          ∀ x, wireVal n ⟨gs, 0⟩ w x = srcAt x (fun j => v j x) (P.src a b)) := hsrc'
    have hva : ∀ x, v a x = opv (P.isAnd a) (srcAt x (fun j => v j x) (P.src a 0))
        (srcAt x (fun j => v j x) (P.src a 1)) := fun x => hv x a (Finset.mem_insert_self a s)
    have hsub : kept P v s ⊆ kept P v (insert a s) :=
      Finset.filter_subset_filter _ (Finset.subset_insert a s)
    have hlen' : gs.length ≤ (kept P v (insert a s)).card := hlen.trans (Finset.card_le_card hsub)
    have same : Res gs (v a) → ∃ gs : List Gate, IsAO2 n ⟨gs, 0⟩ ∧
        gs.length ≤ (kept P v (insert a s)).card ∧ ∀ i ∈ insert a s, Res gs (v i) := by
      intro h
      refine ⟨gs, hAO, hlen', fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · exact h
      · exact hres i hi'
    rcases hsrc 0 with h0 | ⟨h0, w0, hw0, hv0⟩
    · -- first operand constant false
      refine same ?_
      cases hop : P.isAnd a
      · rcases hsrc 1 with h1 | ⟨h1, w1, hw1, hv1⟩
        · exact Or.inl fun x => by rw [hva x, h0 x, h1 x, hop]; rfl
        · refine Or.inr ⟨by rw [hva, h0, h1, hop]; rfl, w1, hw1, fun x => ?_⟩
          rw [hv1 x, hva x, h0 x, hop]; simp [opv]
      · exact Or.inl fun x => by rw [hva x, h0 x, hop]; rfl
    · rcases hsrc 1 with h1 | ⟨h1, w1, hw1, hv1⟩
      · refine same ?_
        cases hop : P.isAnd a
        · refine Or.inr ⟨by rw [hva, h0, h1, hop]; rfl, w0, hw0, fun x => ?_⟩
          rw [hv0 x, hva x, h1 x, hop]; simp [opv]
        · exact Or.inl fun x => by rw [hva x, h1 x, hop]; simp [opv]
      · -- both operands kept: append a gate
        have hak : a ∈ kept P v (insert a s) :=
          Finset.mem_filter.2 ⟨Finset.mem_insert_self a s, h0, h1⟩
        have hcard : (kept P v s).card + 1 ≤ (kept P v (insert a s)).card := by
          have hnot : a ∉ kept P v s := fun h => ha (Finset.mem_filter.1 h).1
          rw [← Finset.card_insert_of_notMem hnot]
          exact Finset.card_le_card (Finset.insert_subset hak hsub)
        let o : GateOp := if P.isAnd a then GateOp.and else GateOp.or
        have ho : o = GateOp.and ∨ o = GateOp.or := by
          by_cases h : P.isAnd a = true <;> simp [o, h]
        refine ⟨gs ++ [⟨o, [w0, w1]⟩], isAO2_snoc gs o ho w0 w1 hw0 hw1 hAO, ?_, fun i hi => ?_⟩
        · simp only [List.length_append, List.length_singleton]; omega
        · rcases Finset.mem_insert.1 hi with rfl | hi'
          · refine Or.inr ⟨?_, n + gs.length, by simp, fun x => ?_⟩
            · rw [hva]
              simp only at h0 h1
              rw [h0, h1]
              cases P.isAnd i <;> rfl
            · rw [wireVal_new, hva x]
              simp only [List.map_cons, List.map_nil, hv0 x, hv1 x]
              by_cases h : P.isAnd i = true
              · simp [o, h, opv, GateOp.eval]
              · simp [o, h, opv, GateOp.eval]
          · exact res_mono gs _ _ (hres i hi')

lemma zero_ao (n : ℕ) : IsAO2 n ⟨[], n⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg; simp at hg
  · intro j hj; simp at hj
  · intro g hg; simp at hg

lemma zero_fun (n : ℕ) : circuitFun n ⟨[], n⟩ = fun _ => false := by
  funext x
  simp [circuitFun, Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]

lemma fold_total (P : Prog n ι) (rank : ι → ℕ)
    (v : ι → (Fin n → Bool) → Bool) (K : Finset ι)
    (hcl : Closed P rank K) (hv : Sol P K v) (o : Src n ι)
    (ho : ∀ j, o = some (Sum.inr j) → j ∈ K) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ (kept P v K).card ∧
      ∀ x : Fin n → Bool, circuitFun n D x = srcAt x (fun j => v j x) o := by
  obtain ⟨gs, hAO, hlen, hres⟩ := build P rank v K hcl hv
  have hR : Res gs (fun x => srcAt x (fun j => v j x) o) := by
    rcases o with _ | (c | j)
    · exact Or.inl fun x => rfl
    · exact Or.inr ⟨rfl, c, by have := c.2; omega, fun x => wireVal_input gs c x⟩
    · exact hres j (ho j rfl)
  rcases hR with h | ⟨_, w, _, hw⟩
  · refine ⟨⟨[], n⟩, zero_ao n, Nat.zero_le _, fun x => ?_⟩
    rw [zero_fun]
    exact (h x).symm
  · refine ⟨⟨gs, w⟩, ⟨hAO.1, hAO.2.1, hAO.2.2⟩, hlen, fun x => hw x⟩

open PEqualNP.EdgeOwnership (gateVal)

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


lemma prune_closed (C : Circuit) (hC : IsAO2 n C) (K : Finset ℕ)
    (hK : ∀ k ∈ K, k < C.gates.length)
    (hcl : ∀ k ∈ K, ∀ w ∈ (gateAt C k).inputs, n ≤ w → w - n ∈ K)
    (ho : ∀ j, srcOf n C.output = some (Sum.inr j) → j ∈ K) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ K.card ∧ circuitFun n D = circuitFun n C := by
  let P : Prog n ℕ := progOf C fun k b => srcOf n (opnd C k b)
  let v : ℕ → (Fin n → Bool) → Bool := fun k x => gateVal n C k x
  have hback : ∀ k ∈ K, ∀ b : Fin 2, opnd C k b ∈ (gateAt C k).inputs := by
    intro k hk b
    have hm : gateAt C k ∈ C.gates := by
      exact List.mem_of_getElem? (show C.gates[k]? = some (gateAt C k) by
        simp [gateAt, List.getD_eq_getElem?_getD, hK k hk])
    have hlen := hC.2.2 _ hm
    have hb : b.val < (gateAt C k).inputs.length := by rw [hlen]; exact b.isLt
    exact List.mem_of_getElem? (show (gateAt C k).inputs[b.val]? = some (opnd C k b) by
      simp [opnd, List.getD_eq_getElem?_getD, hb])
  have hclosed : Closed P id K := by
    intro k hk b j hsrc
    change srcOf n (opnd C k b) = some (Sum.inr j) at hsrc
    have hw := srcOf_inr (opnd C k b) j hsrc
    have hlt := hC.2.1 k (hK k hk) (opnd C k b) (hback k hk b)
    refine ⟨?_, ?_⟩
    · have hmem := hcl k hk (opnd C k b) (hback k hk b) (by omega)
      simpa [hw] using hmem
    · simpa using (show j < k by omega)
  have hsol : Sol P K v := by
    intro x k hk
    change gateVal n C k x = opv (isA (gateAt C k).op)
      (srcAt x (fun j => gateVal n C j x) (srcOf n (opnd C k 0)))
      (srcAt x (fun j => gateVal n C j x) (srcOf n (opnd C k 1)))
    rw [srcAt_srcOf, srcAt_srcOf]
    exact gate_eq C hC k (hK k hk) x
  obtain ⟨D, hD, hsize, hfun⟩ := fold_total P id v K hclosed hsol (srcOf n C.output) ho
  refine ⟨D, hD, hsize.trans (Finset.card_filter_le K _), funext fun x => ?_⟩
  rw [hfun x]
  exact srcAt_srcOf C C.output x

lemma prune_complement (C : Circuit) (hC : IsAO2 n C) (J : Finset ℕ)
    (hJ : J ⊆ Finset.range C.size)
    (hcl : ∀ k < C.size, k ∉ J → ∀ w ∈ (gateAt C k).inputs,
      n ≤ w → w - n ∉ J)
    (ho : C.output < n + C.size)
    (hjout : n ≤ C.output → C.output - n ∉ J) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + J.card ≤ C.size ∧
      circuitFun n D = circuitFun n C := by
  classical
  let K := Finset.range C.size \ J
  have hK : ∀ k ∈ K, k < C.gates.length := by
    intro k hk
    exact Finset.mem_range.mp (Finset.mem_sdiff.mp hk).1
  have hclosed : ∀ k ∈ K, ∀ w ∈ (gateAt C k).inputs, n ≤ w → w - n ∈ K := by
    intro k hk w hw hwn
    obtain ⟨hkr, hkj⟩ := Finset.mem_sdiff.mp hk
    have hkl := Finset.mem_range.mp hkr
    have hwl := hC.2.1 k hkl w hw
    apply Finset.mem_sdiff.mpr
    exact ⟨Finset.mem_range.mpr (by omega),
      hcl k hkl hkj w hw hwn⟩
  have hout : ∀ j, srcOf n C.output = some (Sum.inr j) → j ∈ K := by
    intro j hj
    have heq := srcOf_inr C.output j hj
    apply Finset.mem_sdiff.mpr
    exact ⟨Finset.mem_range.mpr (by omega), by simpa [heq] using hjout (by omega)⟩
  obtain ⟨D, hD, hs, hf⟩ := prune_closed C hC K hK hclosed hout
  refine ⟨D, hD, ?_, hf⟩
  have hcard : K.card + J.card = C.size := by
    simpa [K] using Finset.card_sdiff_add_card_eq_card hJ
  omega

lemma erase_unread (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (hj : j < C.size)
    (hread : ∀ k < C.size, k ≠ j → n + j ∉ (gateAt C k).inputs)
    (ho : C.output < n + C.size) (hjo : C.output ≠ n + j) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + 1 ≤ C.size ∧
      circuitFun n D = circuitFun n C := by
  classical
  apply prune_complement C hC {j}
  · simpa using hj
  · intro k hk hkj w hw hwn
    have hkj' : k ≠ j := by simpa using hkj
    intro hmem
    have heq : w - n = j := by simpa using hmem
    have hwj : w = n + j := by omega
    exact hread k hk hkj' (hwj ▸ hw)
  · exact ho
  · intro hn hmem
    have heq : C.output - n = j := by simpa using hmem
    exact hjo (by omega)

def WireStep (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  ∃ k < C.size, a = n + k ∧ b ∈ (gateAt C k).inputs

noncomputable def liveGates (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter fun k =>
    Relation.ReflTransGen (WireStep n C) C.output (n + k)

lemma prune_reachable (C : Circuit) (hC : IsAO2 n C)
    (ho : C.output < n + C.size) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ (liveGates n C).card ∧
      circuitFun n D = circuitFun n C := by
  classical
  apply prune_closed C hC (liveGates n C)
  · intro k hk
    exact Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  · intro k hk w hw hwn
    obtain ⟨hkr, hreach⟩ := Finset.mem_filter.mp hk
    have hkl := Finset.mem_range.mp hkr
    have hwl := hC.2.1 k hkl w hw
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    have hnext : WireStep n C (n + k) w := ⟨k, hkl, rfl, hw⟩
    have hfull := hreach.tail hnext
    simpa [Nat.add_sub_of_le hwn] using hfull
  · intro j hj
    have heq := srcOf_inr C.output j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    rw [heq]

lemma least_all_live (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (ho : C.output < n + C.size) :
    liveGates n C = Finset.range C.size := by
  classical
  obtain ⟨D, hD, hs, hf⟩ := prune_reachable C hC.1 ho
  have hmin := hC.2.2 D hD (hf.trans hC.2.1)
  have hsub : liveGates n C ⊆ Finset.range C.size := Finset.filter_subset _ _
  apply Finset.eq_of_subset_of_card_le hsub
  simpa using hmin.trans hs

lemma live_has_reader (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (hj : j ∈ liveGates n C) (hjo : C.output ≠ n + j) :
    ∃ k < C.size, j < k ∧ n + j ∈ (gateAt C k).inputs := by
  classical
  have hreach := (Finset.mem_filter.mp hj).2
  change Relation.ReflTransGen (WireStep n C) C.output (n + j) at hreach
  rcases hreach.cases_tail with heq | ⟨b, hpath, hstep⟩
  · exact False.elim (hjo heq.symm)
  · obtain ⟨k, hk, hbk, hread⟩ := hstep
    have hlt := hC.2.1 k hk (n + j) hread
    exact ⟨k, hk, by omega, hread⟩

lemma least_has_reader (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (ho : C.output < n + C.size)
    (j : ℕ) (hj : j < C.size) (hjo : C.output ≠ n + j) :
    ∃ k < C.size, j < k ∧ n + j ∈ (gateAt C k).inputs := by
  apply live_has_reader C hC.1 j _ hjo
  rw [least_all_live G C hC ho]
  exact Finset.mem_range.mpr hj


lemma rank_induction (rank : ι → ℕ) (p : ι → Prop)
    (h : ∀ i, (∀ j, rank j < rank i → p j) → p i) : ∀ i, p i := by
  have key : ∀ m, ∀ i, rank i = m → p i := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih => exact fun i hi => h i fun j hj => ih (rank j) (hi ▸ hj) j rfl
  exact fun i => key _ i rfl

lemma sol_le (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) (hcl : Closed P rank K) (x : Fin n → Bool)
    (t u : ι → Bool) (ht : SolAt P K x t)
    (hs : ∀ i ∈ K, opv (P.isAnd i) (srcAt x u (P.src i 0)) (srcAt x u (P.src i 1)) = true → u i = true) :
    ∀ i ∈ K, t i = true → u i = true := by
  refine fun i => rank_induction rank (fun i => i ∈ K → t i = true → u i = true) ?_ i
  intro i ih hi hti
  rw [ht i hi] at hti
  refine hs i hi (opv_mono _ _ _ _ _ ?_ ?_ hti)
  all_goals
    intro h
    revert h
    generalize hb : P.src i _ = s
    rcases s with _ | (a | j)
    · exact fun h => h
    · exact fun h => h
    · intro h
      obtain ⟨hj, hr⟩ := hcl i hi _ j hb
      exact ih j hr hj h

lemma le_sol (P : Prog n ι) (rank : ι → ℕ) (K : Finset ι) (hcl : Closed P rank K) (x : Fin n → Bool)
    (t u : ι → Bool) (ht : SolAt P K x t)
    (hs : ∀ i ∈ K, u i = true → opv (P.isAnd i) (srcAt x u (P.src i 0)) (srcAt x u (P.src i 1)) = true) :
    ∀ i ∈ K, u i = true → t i = true := by
  refine fun i => rank_induction rank (fun i => i ∈ K → u i = true → t i = true) ?_ i
  intro i ih hi hui
  rw [ht i hi]
  refine opv_mono _ _ _ _ _ ?_ ?_ (hs i hi hui)
  all_goals
    intro h
    revert h
    generalize hb : P.src i _ = s
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
    generalize P.src i _ = s
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
      opv (P.isAnd a) (srcAt x (fun j => v j x) (P.src a 0)) (srcAt x (fun j => v j x) (P.src a 1)) else v i x
    have hsrc : ∀ i ∈ insert a s, ∀ b x, srcAt x (fun j => v' j x) (P.src i b)
        = srcAt x (fun j => v j x) (P.src i b) := by
      intro i hi b x
      rcases hb : P.src i b with _ | (c | j)
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

open PEqualNP.EdgeOwnership (pairInput)

def dropSrc (n j w : ℕ) : Src n ℕ := if w = n + j then none else srcOf n w

lemma dropSrc_inr (j w t : ℕ) (h : dropSrc n j w = some (Sum.inr t)) :
    w = n + t ∧ t ≠ j := by
  by_cases hw : w = n + j
  · simp [dropSrc, hw] at h
  · have he := srcOf_inr w t (by simpa [dropSrc, hw] using h)
    exact ⟨he, by omega⟩

lemma opnd_mem (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.size) (b : Fin 2) :
    opnd C k b ∈ (gateAt C k).inputs := by
  have hkg : k < C.gates.length := hk
  have hm : gateAt C k ∈ C.gates := by
    exact List.mem_of_getElem? (show C.gates[k]? = some (gateAt C k) by
      simp [gateAt, List.getD_eq_getElem?_getD, hkg])
  have hlen := hC.2.2 _ hm
  have hb : b.val < (gateAt C k).inputs.length := by rw [hlen]; exact b.isLt
  exact List.mem_of_getElem? (show (gateAt C k).inputs[b.val]? = some (opnd C k b) by
    simp [opnd, List.getD_eq_getElem?_getD, hb])

lemma dropSrc_old_le (C : Circuit) (j w : ℕ) (x : Fin n → Bool) :
    srcAt x (fun k => gateVal n C k x) (dropSrc n j w) = true → wireVal n C w x = true := by
  unfold dropSrc
  split_ifs with hw
  · simp [srcAt]
  · rw [srcAt_srcOf]
    exact id

lemma dropSrc_old_eq (C : Circuit) (j w : ℕ) (x : Fin n → Bool)
    (hz : gateVal n C j x = false) :
    srcAt x (fun k => gateVal n C k x) (dropSrc n j w) = wireVal n C w x := by
  unfold dropSrc
  split_ifs with hw
  · subst w
    exact hz.symm
  · exact srcAt_srcOf C w x

lemma drop_edge_zero (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (ho : C.output < n + C.size) (j : ℕ) (hj : j < C.size)
    (hz : ∀ p q, G.Adj p q → gateVal n C j (pairInput p q) = false) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  let K := (Finset.range C.size).erase j
  let P : Prog n ℕ := progOf C fun k b => dropSrc n j (opnd C k b)
  let o : Src n ℕ := dropSrc n j C.output
  have hK : ∀ k ∈ K, k < C.size := fun k hk =>
    Finset.mem_range.mp (Finset.mem_of_mem_erase hk)
  have hclosed : Closed P id K := by
    intro k hk b t ht
    obtain ⟨heq, hne⟩ := dropSrc_inr j (opnd C k b) t ht
    have hkl := hK k hk
    have hback := hC.2.1 k hkl _ (opnd_mem C hC k hkl b)
    refine ⟨Finset.mem_erase.mpr ⟨hne, Finset.mem_range.mpr (by omega)⟩, ?_⟩
    simpa using (show t < k by omega)
  have hout : ∀ t, o = some (Sum.inr t) → t ∈ K := by
    intro t ht
    obtain ⟨heq, hne⟩ := dropSrc_inr j C.output t ht
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨v, hv⟩ := sol_exists P id K hclosed
  have hupper (x : Fin n → Bool) : ∀ k ∈ K, v k x = true → gateVal n C k x = true := by
    apply sol_le P id K hclosed x (fun k => v k x) (fun k => gateVal n C k x) (hv x)
    intro k hk h
    rw [gate_eq C hC k (hK k hk) x]
    exact opv_mono _ _ _ _ _ (dropSrc_old_le C j (opnd C k 0) x)
      (dropSrc_old_le C j (opnd C k 1) x) h
  have houtput_le (x : Fin n → Bool) :
      srcAt x (fun k => v k x) o = true → graphFun G ∅ x = true := by
    intro hx
    have hsource : srcAt x (fun k => gateVal n C k x) o = true := by
      rcases hs : o with _ | (a | t)
      · simp [hs, srcAt] at hx
      · simpa [hs, srcAt] using hx
      · exact hupper x t (hout t hs) (by simpa [hs, srcAt] using hx)
    have hf := dropSrc_old_le C j C.output x hsource
    change circuitFun n C x = true at hf
    rwa [hF] at hf
  have hedges (p q : Fin n) (hpq : G.Adj p q) :
      srcAt (pairInput p q) (fun k => v k (pairInput p q)) o = true := by
    let x := pairInput p q
    have hzero : gateVal n C j x = false := hz p q hpq
    have hbelow : ∀ k ∈ K, gateVal n C k x = true → v k x = true := by
      apply le_sol P id K hclosed x (fun k => v k x) (fun k => gateVal n C k x) (hv x)
      intro k hk h
      change gateVal n C k x = true at h
      change opv (isA (gateAt C k).op)
        (srcAt x (fun t => gateVal n C t x) (dropSrc n j (opnd C k 0)))
        (srcAt x (fun t => gateVal n C t x) (dropSrc n j (opnd C k 1))) = true
      rw [dropSrc_old_eq C j _ x hzero, dropSrc_old_eq C j _ x hzero, ← gate_eq C hC k (hK k hk) x]
      exact h
    have hsource : srcAt x (fun k => gateVal n C k x) o = true := by
      rw [dropSrc_old_eq C j _ x hzero]
      change circuitFun n C x = true
      rw [hF]
      apply (show graphFun G ∅ x = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true by simp [graphFun]).mpr
      exact ⟨p, q, hpq, by simp [x, pairInput], by simp [x, pairInput]⟩
    rcases hs : o with _ | (a | t)
    · simp [hs, srcAt, x] at hsource
    · simpa [hs, srcAt, x] using hsource
    · exact hbelow t (hout t hs) (by simpa [hs, srcAt, x] using hsource)
  have hmono (x y : Fin n → Bool) (hxy : ∀ a, x a = true → y a = true) :
      srcAt x (fun k => v k x) o = true → srcAt y (fun k => v k y) o = true := by
    rcases hs : o with _ | (a | t)
    · exact id
    · exact hxy a
    · exact sol_mono P id K hclosed v hv x y hxy t (hout t hs)
  obtain ⟨D, hD, hsize, hfun⟩ := fold_total P id v K hclosed hv o hout
  refine ⟨D, hD, ?_, funext fun x => ?_⟩
  · have hc := hsize.trans (Finset.card_filter_le K _)
    have hcard : K.card = C.size - 1 := by
      simp [K, Finset.card_erase_of_mem (Finset.mem_range.mpr hj)]
    omega
  · rw [hfun]
    apply Bool.eq_iff_iff.mpr
    refine ⟨houtput_le x, ?_⟩
    intro hx
    have hg : ∃ p q, G.Adj p q ∧ x p = true ∧ x q = true := by
      simpa [graphFun] using hx
    obtain ⟨p, q, hpq, hp, hq⟩ := hg
    apply hmono (pairInput p q) x _ (hedges p q hpq)
    intro a ha
    simp only [pairInput, decide_eq_true_eq] at ha
    rcases ha with rfl | rfl
    · exact hp
    · exact hq

lemma least_gate_hits_edge (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hne : ∃ p q, G.Adj p q)
    (j : ℕ) (hj : j < C.size) :
    ∃ p q, G.Adj p q ∧ gateVal n C j (pairInput p q) = true := by
  classical
  have hout : C.output < n + C.size := by
    obtain ⟨p, q, hpq⟩ := hne
    have ht : circuitFun n C (pairInput p q) = true := by
      rw [hC.2.1]
      apply (show graphFun G ∅ (pairInput p q) = true ↔ ∃ a b, G.Adj a b ∧ pairInput p q a = true ∧ pairInput p q b = true by simp [graphFun]).mpr
      exact ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
    by_contra hbad
    have hlen : (C.wires (List.ofFn (pairInput p q))).length = n + C.size := by
      unfold Circuit.wires
      rw [wires_length, List.length_ofFn]
      rfl
    have hz : (C.wires (List.ofFn (pairInput p q))).getD C.output false = false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega :
        (C.wires (List.ofFn (pairInput p q))).length ≤ C.output)]
    change (C.wires (List.ofFn (pairInput p q))).getD C.output false = true at ht
    exact Bool.false_ne_true (hz.symm.trans ht)
  by_contra hn
  have hz : ∀ p q, G.Adj p q → gateVal n C j (pairInput p q) = false := by
    intro p q hpq
    cases he : gateVal n C j (pairInput p q)
    · rfl
    · exact False.elim (hn ⟨p, q, hpq, he⟩)
  obtain ⟨D, hD, hs, hf⟩ := drop_edge_zero G C hC.1 hC.2.1 hout j hj hz
  have hm := hC.2.2 D hD hf
  omega

lemma least_first_and_adj (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hne : ∃ p q, G.Adj p q)
    (hsize : 0 < C.size) (u v : Fin n) (huv : u ≠ v)
    (hop : (gateAt C 0).op = GateOp.and)
    (hins : (gateAt C 0).inputs = [u.val, v.val]) : G.Adj u v := by
  obtain ⟨p, q, hpq, hgate⟩ := least_gate_hits_edge G C hC hne 0 hsize
  have hval := gate_eq C hC.1 0 hsize (pairInput p q)
  have hu : wireVal n C u.val (pairInput p q) = pairInput p q u :=
    wireVal_lt C u.val u.isLt _
  have hv : wireVal n C v.val (pairInput p q) = pairInput p q v :=
    wireVal_lt C v.val v.isLt _
  simp only [opnd, hins] at hval
  simp [hop, isA, opv, hu, hv] at hval
  rw [hgate] at hval
  have hpv : pairInput p q u = true ∧ pairInput p q v = true := by
    simpa using hval.symm
  simp only [pairInput, decide_eq_true_eq] at hpv
  rcases hpv with ⟨hup | huq, hvp | hvq⟩
  · exact False.elim (huv (hup.trans hvp.symm))
  · simpa [hup, hvq] using hpq
  · simpa [huq, hvp] using hpq.symm
  · exact False.elim (huv (huq.trans hvq.symm))

open scoped BigOperators

def readList (C : Circuit) : List ℕ := C.gates.flatMap Gate.inputs

lemma readList_length (C : Circuit) (hC : IsAO2 n C) :
    (readList C).length = 2 * C.size := by
  have aux (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length = 2) :
      (gs.flatMap Gate.inputs).length = 2 * gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      rw [List.flatMap_cons, List.length_append, h g (by simp),
        ih (fun a ha => h a (by simp [ha]))]
      simp; omega
  exact aux C.gates hC.2.2

lemma readList_bound (C : Circuit) (hC : IsAO2 n C) :
    ∀ w ∈ readList C, w < n + C.size := by
  intro w hw
  obtain ⟨g, hg, hwi⟩ := List.mem_flatMap.mp hw
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hg
  have hgate : gateAt C k = g := by
    simp [gateAt, List.getD_eq_getElem?_getD, hk, heq]
  have hlt := hC.2.1 k hk w (hgate.symm ▸ hwi)
  change k < C.size at hk
  omega

lemma reader_mem (C : Circuit) (j k : ℕ) (hk : k < C.size)
    (hread : n + j ∈ (gateAt C k).inputs) : n + j ∈ readList C := by
  apply List.mem_flatMap.mpr
  refine ⟨gateAt C k, ?_, hread⟩
  have hklen : k < C.gates.length := hk
  exact List.mem_of_getElem? (show C.gates[k]? = some (gateAt C k) by
    simp [gateAt, List.getD_eq_getElem?_getD, hklen])

lemma read_twice_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (ho : n ≤ C.output) (hupper : C.output < n + C.size)
    (hreads : ∀ i : Fin n, 2 ≤ (readList C).count i.val) :
    2 * n ≤ C.size + 1 := by
  classical
  let L := readList C
  let q := C.output - n
  have hq : q < C.size := by dsimp [q]; omega
  have htotal : (∑ w ∈ Finset.range (n + C.size), L.count w) = 2 * C.size := by
    have hsum : (∑ w ∈ Finset.range (n + C.size), (L : Multiset ℕ).count w) = L.length := by
      apply Multiset.sum_count_eq_card
      intro w hw
      exact Finset.mem_range.mpr (readList_bound C hC.1 w hw)
    simpa [L, readList_length C hC.1] using hsum
  have hinputs : 2 * n ≤ ∑ w ∈ Finset.range n, L.count w := by
    have hh : (∑ w ∈ Finset.range n, 2) ≤ ∑ w ∈ Finset.range n, L.count w := by
      apply Finset.sum_le_sum
      intro w hw
      exact hreads ⟨w, Finset.mem_range.mp hw⟩
    simpa [Nat.mul_comm] using hh
  have hgate (j : ℕ) (hj : j ∈ (Finset.range C.size).erase q) :
      1 ≤ L.count (n + j) := by
    obtain ⟨hjq, hj⟩ := Finset.mem_erase.mp hj
    have hjo : C.output ≠ n + j := by
      intro heq
      apply hjq
      dsimp [q]
      omega
    obtain ⟨k, hk, _, hread⟩ := least_has_reader G C hC hupper j (Finset.mem_range.mp hj) hjo
    exact List.count_pos_iff.mpr (reader_mem C j k hk hread)
  have hgates : C.size - 1 ≤ ∑ j ∈ Finset.range C.size, L.count (n + j) := by
    have hsum := Finset.sum_le_sum hgate
    have hcard : ((Finset.range C.size).erase q).card = C.size - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hq), Finset.card_range]
    have hsub : (∑ j ∈ (Finset.range C.size).erase q, L.count (n + j)) ≤
        ∑ j ∈ Finset.range C.size, L.count (n + j) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset q _) (fun _ _ _ => Nat.zero_le _)
    have hh : C.size - 1 ≤ ∑ j ∈ (Finset.range C.size).erase q, L.count (n + j) := by
      simpa [hcard] using hsum
    exact hh.trans hsub
  rw [Finset.sum_range_add] at htotal
  omega

lemma low_read_of_small (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (ho : n ≤ C.output) (hupper : C.output < n + C.size)
    (hsmall : C.size + 1 < 2 * n) :
    ∃ i : Fin n, (readList C).count i.val ≤ 1 := by
  classical
  by_contra h
  push Not at h
  have hreads : ∀ i : Fin n, 2 ≤ (readList C).count i.val := by
    intro i
    have hi := h i
    omega
  have hbound := read_twice_bound G C hC ho hupper hreads
  omega


end Pruning


namespace SingleRead

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma ofFn_get {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD]

lemma fold_get (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    · exact List.getD_append _ _ _ _ hi
    · simp only [step, List.length_append, List.length_singleton]
      omega

lemma append_compare {u : ℕ} {xs ys : List Bool} (hlen : xs.length = ys.length)
    (hxy : ∀ i, i ≠ u → xs.getD i false = true → ys.getD i false = true)
    {a b : Bool} (hab : a = true → b = true) :
    ∀ i, i ≠ u → (xs ++ [a]).getD i false = true → (ys ++ [b]).getD i false = true := by
  intro i hi hx
  by_cases hil : i < xs.length
  · rw [List.getD_append _ _ _ _ hil] at hx
    rw [List.getD_append _ _ _ _ (by omega)]
    exact hxy i hi hx
  · have hyil : ys.length ≤ i := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : xs.length ≤ i)] at hx
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hyil]
    rw [← hlen]
    by_cases he : i = xs.length
    · simpa [he] using hab (by simpa [he] using hx)
    · have hp : 0 < i - xs.length := by omega
      have hz : [a].length ≤ i - xs.length := by simp only [List.length_singleton]; omega
      simp [List.getElem?_eq_none hz] at hx

lemma gate_compare {xs ys : List Bool} {g : Gate}
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hxy : ∀ i ∈ g.inputs, xs.getD i false = true → ys.getD i false = true) :
    g.op.eval (g.inputs.map fun i => xs.getD i false) = true →
      g.op.eval (g.inputs.map fun i => ys.getD i false) = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h i hi
    exact hxy i hi (h i hi)
  · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, hxy i hi hx⟩

lemma fold_compare {u : ℕ} (gs : List Gate) (xs ys : List Bool)
    (hlen : xs.length = ys.length)
    (hxy : ∀ i, i ≠ u → xs.getD i false = true → ys.getD i false = true)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hno : ∀ g ∈ gs, u ∉ g.inputs) :
    ∀ i, i ≠ u → (gs.foldl step xs).getD i false = true →
      (gs.foldl step ys).getD i false = true := by
  induction gs generalizing xs ys with
  | nil => exact hxy
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    · simp [step, hlen]
    · apply append_compare hlen hxy
      apply gate_compare (hop g (by simp))
      intro i hi
      exact hxy i (fun h => hno g (by simp) (h ▸ hi))
    · intro g' hg'
      exact hop g' (by simp [hg'])
    · intro g' hg'
      exact hno g' (by simp [hg'])

lemma graph_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (G.irrefl hab)
    · exact hab
    · exact hab.symm
    · exact False.elim (G.irrefl hab)
  · intro h
    exact ⟨u, v, h, by simp [pairInput], by simp [pairInput]⟩

lemma output_ne {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hfun : circuitFun n C = graphFun G ∅) (u : Fin n) :
    C.output ≠ u.val := by
  intro he
  have h : circuitFun n C (pairInput u u) = true := by
    unfold circuitFun Circuit.eval Circuit.wires
    change (C.gates.foldl step (List.ofFn (pairInput u u))).getD C.output false = true
    rw [he, fold_get _ _ _ (by simp), ofFn_get]
    simp [pairInput]
  rw [hfun] at h
  exact G.irrefl ((graph_pair G u u).1 h)

lemma pair_compare {n : ℕ} (C : Circuit) (u v w : Fin n) (gs : List Gate)
    (hshape : C.gates = { op := GateOp.or, inputs := [u.val, v.val] } :: gs)
    (hao : IsAO2 n C) (hno : ∀ g ∈ gs, u.val ∉ g.inputs)
    (hout : C.output ≠ u.val) :
    circuitFun n C (pairInput u w) = true → circuitFun n C (pairInput v w) = true := by
  have heq (a b : Fin n) (ha : a = u ∨ a = v) :
      step (List.ofFn (pairInput a b)) { op := GateOp.or, inputs := [u.val, v.val] } =
        List.ofFn (pairInput a b) ++ [true] := by
    simp only [step, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
      Bool.or_false, id_eq, ofFn_get]
    congr 1
    rcases ha with rfl | rfl <;> simp [pairInput]
  unfold circuitFun Circuit.eval Circuit.wires
  rw [hshape, List.foldl_cons, List.foldl_cons]
  change (gs.foldl step (step (List.ofFn (pairInput u w)) _)).getD C.output false = true →
    (gs.foldl step (step (List.ofFn (pairInput v w)) _)).getD C.output false = true
  rw [heq u w (Or.inl rfl), heq v w (Or.inr rfl)]
  apply fold_compare gs _ _ (by simp) _ _ hno C.output hout
  · apply append_compare (by simp) _ (fun h => h)
    intro i hi hx
    by_cases hin : i < n
    · let j : Fin n := ⟨i, hin⟩
      change (List.ofFn (pairInput u w)).getD j.val false = true at hx
      change (List.ofFn (pairInput v w)).getD j.val false = true
      rw [ofFn_get] at hx ⊢
      simp only [pairInput, decide_eq_true_eq] at hx ⊢
      rcases hx with h | h
      · exact False.elim (hi (congrArg Fin.val h))
      · exact Or.inr h
    · simp [List.getD_eq_getElem?_getD, hin] at hx
  · intro g hg
    exact hao.1 g (by rw [hshape]; simp [hg])

lemma first_or_single_read {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u v : Fin n) (gs : List Gate)
    (hshape : C.gates = { op := GateOp.or, inputs := [u.val, v.val] } :: gs)
    (hao : IsAO2 n C) (hno : ∀ g ∈ gs, u.val ∉ g.inputs)
    (hfun : circuitFun n C = graphFun G ∅) :
    ¬ G.Adj u v ∧ G.neighborSet u ⊆ G.neighborSet v := by
  have hc (w : Fin n) (hw : G.Adj u w) : G.Adj v w := by
    apply (graph_pair G v w).1
    rw [← hfun]
    apply pair_compare C u v w gs hshape hao hno (output_ne G C hfun u)
    rw [hfun]
    exact (graph_pair G u w).2 hw
  exact ⟨fun huv => G.irrefl (hc v huv), hc⟩

lemma first_or_single_read_degree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u v : Fin n) (gs : List Gate) (huv : u ≠ v)
    (hshape : C.gates = { op := GateOp.or, inputs := [u.val, v.val] } :: gs)
    (hao : IsAO2 n C) (hno : ∀ g ∈ gs, u.val ∉ g.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G) :
    G.degree u ≤ 1 := by
  have hsub := (first_or_single_read G C u v gs hshape hao hno hfun).2
  have hcard : (G.neighborFinset u).card ≤
      (Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w).card := by
    apply Finset.card_le_card
    intro w hw
    have huw := (G.mem_neighborFinset u w).1 hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨huw, hsub huw⟩
  rw [G.card_neighborFinset_eq_degree] at hcard
  exact hcard.trans (hfour u v huv)

lemma first_or_second_read {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u v : Fin n) (gs : List Gate) (huv : u ≠ v)
    (hshape : C.gates = { op := GateOp.or, inputs := [u.val, v.val] } :: gs)
    (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hfour : NoFourCycle G) (hdeg : 2 ≤ G.degree u) :
    ∃ g ∈ gs, u.val ∈ g.inputs := by
  by_contra h
  push Not at h
  have hd := first_or_single_read_degree G C u v gs huv hshape hao h hfun hfour
  omega

lemma fold_length (gs : List Gate) (xs : List Bool) :
    (gs.foldl step xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

lemma pair_input_compare {n : ℕ} (u v w : Fin n) :
    ∀ i, i ≠ u.val → (List.ofFn (pairInput u w)).getD i false = true →
      (List.ofFn (pairInput v w)).getD i false = true := by
  intro i hi hx
  by_cases hin : i < n
  · let j : Fin n := ⟨i, hin⟩
    change (List.ofFn (pairInput u w)).getD j.val false = true at hx
    change (List.ofFn (pairInput v w)).getD j.val false = true
    rw [ofFn_get] at hx ⊢
    simp only [pairInput, decide_eq_true_eq] at hx ⊢
    rcases hx with h | h
    · exact False.elim (hi (congrArg Fin.val h))
    · exact Or.inr h
  · simp [List.getD_eq_getElem?_getD, hin] at hx

lemma singleton_input_compare {n : ℕ} (v w : Fin n) :
    ∀ i, (List.ofFn (pairInput v v)).getD i false = true →
      (List.ofFn (pairInput v w)).getD i false = true := by
  intro i hx
  by_cases hin : i < n
  · let j : Fin n := ⟨i, hin⟩
    change (List.ofFn (pairInput v v)).getD j.val false = true at hx
    change (List.ofFn (pairInput v w)).getD j.val false = true
    rw [ofFn_get] at hx ⊢
    simp only [pairInput, decide_eq_true_eq, or_self] at hx
    simp [pairInput, hx]
  · simp [List.getD_eq_getElem?_getD, hin] at hx

lemma arbitrary_or_pair_compare {n : ℕ} (C : Circuit) (u v w : Fin n)
    (pre post : List Gate) (g : Gate) (t : ℕ) (huv : u ≠ v)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hsupport : (C.wires (List.ofFn (pairInput v v))).getD t false = true)
    (hout : C.output ≠ u.val) :
    circuitFun n C (pairInput u w) = true → circuitFun n C (pairInput v w) = true := by
  have htmem : t ∈ g.inputs := by rcases hinputs with h | h <;> simp [h]
  have hgate : gateAt C pre.length = g := by
    simp [gateAt, hshape, List.getD_eq_getElem?_getD]
  have ht : t < n + pre.length := by
    apply hao.2.1 pre.length (by simp [hshape])
    rwa [hgate]
  have hs : (pre.foldl step (List.ofFn (pairInput v v))).getD t false = true := by
    unfold Circuit.wires at hsupport
    rw [hshape, List.foldl_append] at hsupport
    change ((g :: post).foldl step (pre.foldl step (List.ofFn (pairInput v v)))).getD t false = true at hsupport
    rw [fold_get _ _ _ (by simpa [fold_length] using ht)] at hsupport
    exact hsupport
  have htn : t ≠ u.val := by
    intro he
    rw [he, fold_get _ _ _ (by simp), ofFn_get] at hs
    simp [pairInput, huv] at hs
  have hpre : ∀ q ∈ pre, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact hao.1 q (by rw [hshape]; simp [hq])
  have hnpre : ∀ q ∈ pre, u.val ∉ q.inputs := by
    intro q hq
    exact hno q (by simp [hq])
  have hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact hao.1 q (by rw [hshape]; simp [hq])
  have hnpost : ∀ q ∈ post, u.val ∉ q.inputs := by
    intro q hq
    exact hno q (by simp [hq])
  have httrue : (pre.foldl step (List.ofFn (pairInput v w))).getD t false = true := by
    apply fold_compare pre _ _ (by simp) _ hpre hnpre t htn hs
    intro i _ hi
    exact singleton_input_compare v w i hi
  have hright : g.op.eval (g.inputs.map fun i =>
      (pre.foldl step (List.ofFn (pairInput v w))).getD i false) = true := by
    rcases hinputs with hi | hi <;>
      simp only [hop, hi, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
        List.any_nil, id_eq, Bool.or_false, httrue, Bool.or_true, Bool.true_or]
  unfold circuitFun Circuit.eval Circuit.wires
  rw [hshape, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
  change (post.foldl step (step (pre.foldl step (List.ofFn (pairInput u w))) g)).getD C.output false = true →
    (post.foldl step (step (pre.foldl step (List.ofFn (pairInput v w))) g)).getD C.output false = true
  apply fold_compare post _ _ (by simp [step, fold_length]) _ hpost hnpost C.output hout
  apply append_compare (by simp [fold_length])
  · exact fold_compare pre _ _ (by simp) (pair_input_compare u v w) hpre hnpre
  · intro _
    exact hright

lemma arbitrary_or_single_read {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u v : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ) (huv : u ≠ v)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hsupport : (C.wires (List.ofFn (pairInput v v))).getD t false = true)
    (hfun : circuitFun n C = graphFun G ∅) :
    ¬ G.Adj u v ∧ G.neighborSet u ⊆ G.neighborSet v := by
  have hc (w : Fin n) (hw : G.Adj u w) : G.Adj v w := by
    apply (graph_pair G v w).1
    rw [← hfun]
    apply arbitrary_or_pair_compare C u v w pre post g t huv hshape hop hinputs hao hno hsupport
      (output_ne G C hfun u)
    rw [hfun]
    exact (graph_pair G u w).2 hw
  exact ⟨fun huv => G.irrefl (hc v huv), hc⟩

lemma arbitrary_or_single_read_degree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u v : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ) (huv : u ≠ v)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hsupport : (C.wires (List.ofFn (pairInput v v))).getD t false = true)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G) :
    G.degree u ≤ 1 := by
  have hsub := (arbitrary_or_single_read G C u v pre post g t huv hshape hop hinputs hao hno hsupport hfun).2
  have hcard : (G.neighborFinset u).card ≤
      (Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w).card := by
    apply Finset.card_le_card
    intro w hw
    have huw := (G.mem_neighborFinset u w).1 hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨huw, hsub huw⟩
  rw [G.card_neighborFinset_eq_degree] at hcard
  exact hcard.trans (hfour u v huv)

lemma arbitrary_or_other_singleton_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (hdeg : 2 ≤ G.degree u) :
    ∀ v : Fin n, v ≠ u → (C.wires (List.ofFn (pairInput v v))).getD t false = false := by
  intro v hv
  apply Bool.eq_false_iff.mpr
  intro hs
  have hd := arbitrary_or_single_read_degree G C u v pre post g t (Ne.symm hv)
    hshape hop hinputs hao hno hs hfun hfour
  omega

lemma arbitrary_or_other_singletons_empty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (hdeg : 2 ≤ G.degree u) (htu : t ≠ u.val) :
    ∀ v : Fin n, (C.wires (List.ofFn (pairInput v v))).getD t false = false := by
  intro v
  by_cases hv : v ≠ u
  · exact arbitrary_or_other_singleton_false G C u pre post g t hshape hop hinputs hao hno hfun hfour hdeg v hv
  · have hvu : v = u := by tauto
    subst v
    apply Bool.eq_false_iff.mpr
    intro hs
    have hpos : 0 < (G.neighborFinset u).card := by rw [G.card_neighborFinset_eq_degree]; omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
    have huw := (G.mem_neighborFinset u w).1 hw
    have hwu : w ≠ u := by intro h; subst w; exact G.irrefl huw
    have htmem : t ∈ g.inputs := by rcases hinputs with h | h <;> simp [h]
    have hgate : gateAt C pre.length = g := by simp [gateAt, hshape, List.getD_eq_getElem?_getD]
    have ht : t < n + pre.length := by
      apply hao.2.1 pre.length (by simp [hshape])
      rwa [hgate]
    have transport (a : Fin n) :
        (C.wires (List.ofFn (pairInput a a))).getD t false =
          (pre.foldl step (List.ofFn (pairInput a a))).getD t false := by
      unfold Circuit.wires
      rw [hshape, List.foldl_append]
      change ((g :: post).foldl step (pre.foldl step (List.ofFn (pairInput a a)))).getD t false =
        (pre.foldl step (List.ofFn (pairInput a a))).getD t false
      exact fold_get _ _ _ (by simpa [fold_length] using ht)
    rw [transport] at hs
    have hpre : ∀ q ∈ pre, q.op = GateOp.and ∨ q.op = GateOp.or := by
      intro q hq
      exact hao.1 q (by rw [hshape]; simp [hq])
    have hnpre : ∀ q ∈ pre, u.val ∉ q.inputs := by
      intro q hq
      exact hno q (by simp [hq])
    have hwtrue : (pre.foldl step (List.ofFn (pairInput w w))).getD t false = true := by
      apply fold_compare pre _ _ (by simp) _ hpre hnpre t htu hs
      intro i hi hx
      exact pair_input_compare u w w i hi (singleton_input_compare u w i hx)
    have hwfalse := arbitrary_or_other_singleton_false G C u pre post g t hshape hop hinputs
      hao hno hfun hfour hdeg w hwu
    rw [transport, hwtrue] at hwfalse
    cases hwfalse

lemma ofFn_compare_away {n : ℕ} (u : Fin n) (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, i ≠ u → x i = true → y i = true) :
    ∀ i : ℕ, i ≠ u.val → (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
  intro i hi hx
  by_cases hin : i < n
  · let j : Fin n := ⟨i, hin⟩
    change (List.ofFn x).getD j.val false = true at hx
    change (List.ofFn y).getD j.val false = true
    rw [ofFn_get] at hx ⊢
    exact hxy j (fun h => hi (congrArg Fin.val h)) hx
  · simp [List.getD_eq_getElem?_getD, hin] at hx

lemma operand_prefix_value {n : ℕ} (C : Circuit) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hao : IsAO2 n C) (htmem : t ∈ g.inputs)
    (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD t false = (pre.foldl step (List.ofFn x)).getD t false := by
  have hgate : gateAt C pre.length = g := by simp [gateAt, hshape, List.getD_eq_getElem?_getD]
  have ht : t < n + pre.length := by
    apply hao.2.1 pre.length (by simp [hshape])
    rwa [hgate]
  unfold Circuit.wires
  rw [hshape, List.foldl_append]
  change ((g :: post).foldl step (pre.foldl step (List.ofFn x))).getD t false =
    (pre.foldl step (List.ofFn x)).getD t false
  exact fold_get _ _ _ (by simpa [fold_length] using ht)

lemma other_wire_compare {n : ℕ} (C : Circuit) (u : Fin n)
    (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (htmem : t ∈ g.inputs)
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (htu : t ≠ u.val) (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, i ≠ u → x i = true → y i = true) :
    (C.wires (List.ofFn x)).getD t false = true → (C.wires (List.ofFn y)).getD t false = true := by
  rw [operand_prefix_value C pre post g t hshape hao htmem x,
    operand_prefix_value C pre post g t hshape hao htmem y]
  apply fold_compare pre _ _ (by simp) (ofFn_compare_away u x y hxy) _ _ t htu
  · intro q hq
    exact hao.1 q (by rw [hshape]; simp [hq])
  · intro q hq
    exact hno q (by simp [hq])

lemma sole_or_transfer {n : ℕ} (C : Circuit) (u : Fin n)
    (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hout : C.output ≠ u.val) (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, i ≠ u → x i = true → y i = true)
    (hsupport : (C.wires (List.ofFn y)).getD t false = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  have htmem : t ∈ g.inputs := by rcases hinputs with h | h <;> simp [h]
  have httrue : (pre.foldl step (List.ofFn y)).getD t false = true := by
    rw [← operand_prefix_value C pre post g t hshape hao htmem y]
    exact hsupport
  have hpre : ∀ q ∈ pre, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact hao.1 q (by rw [hshape]; simp [hq])
  have hnpre : ∀ q ∈ pre, u.val ∉ q.inputs := by
    intro q hq
    exact hno q (by simp [hq])
  have hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact hao.1 q (by rw [hshape]; simp [hq])
  have hnpost : ∀ q ∈ post, u.val ∉ q.inputs := by
    intro q hq
    exact hno q (by simp [hq])
  have hright : g.op.eval (g.inputs.map fun i => (pre.foldl step (List.ofFn y)).getD i false) = true := by
    rcases hinputs with hi | hi <;>
      simp only [hop, hi, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
        List.any_nil, id_eq, Bool.or_false, httrue, Bool.or_true, Bool.true_or]
  unfold circuitFun Circuit.eval Circuit.wires
  rw [hshape, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
  change (post.foldl step (step (pre.foldl step (List.ofFn x)) g)).getD C.output false = true →
    (post.foldl step (step (pre.foldl step (List.ofFn y)) g)).getD C.output false = true
  apply fold_compare post _ _ (by simp [step, fold_length]) _ hpost hnpost C.output hout
  apply append_compare (by simp [fold_length])
  · exact fold_compare pre _ _ (by simp) (ofFn_compare_away u x y hxy) hpre hnpre
  · intro _
    exact hright

lemma sole_or_neighbor_multiplier {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) :
    ∀ w : Fin n, G.Adj u w → ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD t false = true → x w = true → graphFun G ∅ x = true := by
  intro w huw x ht hx
  rw [← hfun]
  refine sole_or_transfer C u pre post g t hshape hop hinputs hao hno (output_ne G C hfun u)
    (pairInput u w) x ?_ ht ?_
  · intro i hi hp
    simp only [pairInput, decide_eq_true_eq] at hp
    rcases hp with h | h
    · exact False.elim (hi h)
    · rw [h]
      exact hx
  · rw [hfun]
    exact (graph_pair G u w).2 huw

def tripleInput {n : ℕ} (a b w : Fin n) : Fin n → Bool :=
  fun i => decide (i = a ∨ i = b ∨ i = w)

lemma graph_triple {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b w : Fin n) (hab : ¬ G.Adj a b) :
    graphFun G ∅ (tripleInput a b w) = true → G.Adj a w ∨ G.Adj b w := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_true_eq]
  rintro ⟨i, j, hij, hi, hj⟩
  simp only [tripleInput, decide_eq_true_eq] at hi hj
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
  · exact False.elim (G.irrefl hij)
  · exact False.elim (hab hij)
  · exact Or.inl hij
  · exact False.elim (hab hij.symm)
  · exact False.elim (G.irrefl hij)
  · exact Or.inr hij
  · exact Or.inl hij.symm
  · exact Or.inr hij.symm
  · exact False.elim (G.irrefl hij)

lemma sole_or_nonedge_pair_forces_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (htu : t ≠ u.val) (a b : Fin n) (hau : a ≠ u) (hbu : b ≠ u)
    (hab : ¬ G.Adj a b)
    (hs : (C.wires (List.ofFn (pairInput a b))).getD t false = true) :
    G.degree u ≤ 2 := by
  have htmem : t ∈ g.inputs := by rcases hinputs with h | h <;> simp [h]
  have hcover (w : Fin n) (huw : G.Adj u w) : G.Adj a w ∨ G.Adj b w := by
    apply graph_triple G a b w hab
    apply sole_or_neighbor_multiplier G C u pre post g t hshape hop hinputs hao hno hfun w huw
    · apply other_wire_compare C u pre post g t hshape htmem hao hno htu
        (pairInput a b) (tripleInput a b w) _ hs
      intro i _ hi
      simp only [pairInput, decide_eq_true_eq] at hi
      simp only [tripleInput, decide_eq_true_eq]
      rcases hi with hi | hi
      · exact Or.inl hi
      · exact Or.inr (Or.inl hi)
    · simp [tripleInput]
  let A : Finset (Fin n) := Finset.univ.filter fun w => G.Adj u w ∧ G.Adj a w
  let B : Finset (Fin n) := Finset.univ.filter fun w => G.Adj u w ∧ G.Adj b w
  have hsub : G.neighborFinset u ⊆ A ∪ B := by
    intro w hw
    have huw := (G.mem_neighborFinset u w).1 hw
    rcases hcover w huw with ha | hb
    · exact Finset.mem_union_left _ (by simp [A, huw, ha])
    · exact Finset.mem_union_right _ (by simp [B, huw, hb])
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le A B)
  have hA : A.card ≤ 1 := hfour u a (Ne.symm hau)
  have hB : B.card ≤ 1 := hfour u b (Ne.symm hbu)
  rw [G.card_neighborFinset_eq_degree] at hc
  omega

lemma sole_or_rejects_nonedge_pairs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (hdeg : 3 ≤ G.degree u) (htu : t ≠ u.val) :
    ∀ a b : Fin n, ¬ G.Adj a b → (C.wires (List.ofFn (pairInput a b))).getD t false = false := by
  intro a b hab
  apply Bool.eq_false_iff.mpr
  intro hs
  have htmem : t ∈ g.inputs := by rcases hinputs with h | h <;> simp [h]
  have hempty := arbitrary_or_other_singletons_empty G C u pre post g t hshape hop hinputs
    hao hno hfun hfour (by omega) htu
  have hau : a ≠ u := by
    intro he
    subst a
    have hbtrue : (C.wires (List.ofFn (pairInput b b))).getD t false = true := by
      apply other_wire_compare C u pre post g t hshape htmem hao hno htu
        (pairInput u b) (pairInput b b) _ hs
      intro i hi hp
      simp only [pairInput, decide_eq_true_eq] at hp ⊢
      rcases hp with hp | hp
      · exact False.elim (hi hp)
      · exact Or.inl hp
    rw [hempty b] at hbtrue
    cases hbtrue
  have hbu : b ≠ u := by
    intro he
    subst b
    have hatrue : (C.wires (List.ofFn (pairInput a a))).getD t false = true := by
      apply other_wire_compare C u pre post g t hshape htmem hao hno htu
        (pairInput a u) (pairInput a a) _ hs
      intro i hi hp
      simp only [pairInput, decide_eq_true_eq] at hp ⊢
      rcases hp with hp | hp
      · exact Or.inl hp
      · exact False.elim (hi hp)
    rw [hempty a] at hatrue
    cases hatrue
  have hd := sole_or_nonedge_pair_forces_two G C u pre post g t hshape hop hinputs hao hno
    hfun hfour htu a b hau hbu hab hs
  omega

def setInput {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ S)

lemma graph_insert_independent {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (hind : ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b) (w : Fin n) :
    graphFun G ∅ (setInput (insert w S)) = true → ∃ a ∈ S, G.Adj a w := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_true_eq]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [setInput, decide_eq_true_eq, Finset.mem_insert] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact False.elim (G.irrefl hab)
  · exact ⟨b, hb, hab.symm⟩
  · exact ⟨a, ha, hab⟩
  · exact False.elim (hind a ha b hb hab)

lemma sole_or_independent_support_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G) (htu : t ≠ u.val)
    (S : Finset (Fin n)) (huS : u ∉ S) (hind : ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b)
    (hs : (C.wires (List.ofFn (setInput S))).getD t false = true) :
    G.degree u ≤ S.card := by
  have htmem : t ∈ g.inputs := by rcases hinputs with h | h <;> simp [h]
  have hcover (w : Fin n) (huw : G.Adj u w) : ∃ a ∈ S, G.Adj a w := by
    apply graph_insert_independent G S hind w
    apply sole_or_neighbor_multiplier G C u pre post g t hshape hop hinputs hao hno hfun w huw
    · apply other_wire_compare C u pre post g t hshape htmem hao hno htu
        (setInput S) (setInput (insert w S)) _ hs
      intro i _ hi
      simp only [setInput, decide_eq_true_eq] at hi ⊢
      exact Finset.mem_insert_of_mem hi
    · simp [setInput]
  let A : Fin n → Finset (Fin n) := fun a => Finset.univ.filter fun w => G.Adj u w ∧ G.Adj a w
  have hsub : G.neighborFinset u ⊆ S.biUnion A := by
    intro w hw
    have huw := (G.mem_neighborFinset u w).1 hw
    obtain ⟨a, ha, haw⟩ := hcover w huw
    exact Finset.mem_biUnion.mpr ⟨a, ha, by simp [A, huw, haw]⟩
  have hsum : (∑ a ∈ S, (A a).card) ≤ ∑ a ∈ S, 1 := by
    apply Finset.sum_le_sum
    intro a ha
    apply hfour u a
    intro he
    exact huS (he ▸ ha)
  have hc := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  rw [G.card_neighborFinset_eq_degree] at hc
  exact hc.trans (by simpa using hsum)

lemma sole_or_independent_support_erase_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G) (htu : t ≠ u.val)
    (S : Finset (Fin n)) (hind : ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b)
    (hs : (C.wires (List.ofFn (setInput S))).getD t false = true) :
    G.degree u ≤ (S.erase u).card := by
  have htmem : t ∈ g.inputs := by rcases hinputs with h | h <;> simp [h]
  apply sole_or_independent_support_bound G C u pre post g t hshape hop hinputs hao hno hfun hfour htu
    (S.erase u) (by simp)
  · intro a ha b hb
    exact hind a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
  · apply other_wire_compare C u pre post g t hshape htmem hao hno htu
      (setInput S) (setInput (S.erase u)) _ hs
    intro i hi hS
    simp only [setInput, decide_eq_true_eq] at hS ⊢
    exact Finset.mem_erase.mpr ⟨hi, hS⟩

lemma sole_reader_transfer {n : ℕ} (C : Circuit) (u : Fin n)
    (pre post : List Gate) (g : Gate)
    (hshape : C.gates = pre ++ g :: post)
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hout : C.output ≠ u.val) (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, i ≠ u → x i = true → y i = true)
    (hgate : g.op.eval (g.inputs.map fun i => (pre.foldl step (List.ofFn x)).getD i false) = true →
      g.op.eval (g.inputs.map fun i => (pre.foldl step (List.ofFn y)).getD i false) = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  have hpre : ∀ q ∈ pre, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact hao.1 q (by rw [hshape]; simp [hq])
  have hnpre : ∀ q ∈ pre, u.val ∉ q.inputs := by
    intro q hq
    exact hno q (by simp [hq])
  have hpost : ∀ q ∈ post, q.op = GateOp.and ∨ q.op = GateOp.or := by
    intro q hq
    exact hao.1 q (by rw [hshape]; simp [hq])
  have hnpost : ∀ q ∈ post, u.val ∉ q.inputs := by
    intro q hq
    exact hno q (by simp [hq])
  unfold circuitFun Circuit.eval Circuit.wires
  rw [hshape, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons]
  change (post.foldl step (step (pre.foldl step (List.ofFn x)) g)).getD C.output false = true →
    (post.foldl step (step (pre.foldl step (List.ofFn y)) g)).getD C.output false = true
  apply fold_compare post _ _ (by simp [step, fold_length]) _ hpost hnpost C.output hout
  apply append_compare (by simp [fold_length])
  · exact fold_compare pre _ _ (by simp) (ofFn_compare_away u x y hxy) hpre hnpre
  · exact hgate

lemma sole_and_neighbor_singleton {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.and)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (htu : t ≠ u.val) :
    ∀ w : Fin n, G.Adj u w → (C.wires (List.ofFn (pairInput w w))).getD t false = true := by
  intro w huw
  by_contra hbad
  have htmem : t ∈ g.inputs := by rcases hinputs with h | h <;> simp [h]
  have hxy : ∀ i : Fin n, i ≠ u → pairInput u w i = true → pairInput w w i = true := by
    intro i hi hp
    simp only [pairInput, decide_eq_true_eq] at hp ⊢
    rcases hp with h | h
    · exact False.elim (hi h)
    · exact Or.inl h
  have hsrcfalse : (C.wires (List.ofFn (pairInput u w))).getD t false = false := by
    apply Bool.eq_false_iff.mpr
    intro hs
    exact hbad (other_wire_compare C u pre post g t hshape htmem hao hno htu
      (pairInput u w) (pairInput w w) hxy hs)
  have hprefalse : (pre.foldl step (List.ofFn (pairInput u w))).getD t false = false := by
    rw [← operand_prefix_value C pre post g t hshape hao htmem]
    exact hsrcfalse
  have hgatefalse : g.op.eval (g.inputs.map fun i =>
      (pre.foldl step (List.ofFn (pairInput u w))).getD i false) = false := by
    rcases hinputs with hi | hi <;>
      simp only [hop, hi, List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
        List.all_nil, id_eq, Bool.and_true, hprefalse, Bool.and_false, Bool.false_and]
  have houttrue : circuitFun n C (pairInput w w) = true := by
    apply sole_reader_transfer C u pre post g hshape hao hno (output_ne G C hfun u)
      (pairInput u w) (pairInput w w) hxy
    · intro h
      rw [hgatefalse] at h
      cases h
    · rw [hfun]
      exact (graph_pair G u w).2 huw
  rw [hfun] at houttrue
  exact G.irrefl ((graph_pair G w w).1 houttrue)

end SingleRead

end PEqualNP.Outside.L_meta_3566
