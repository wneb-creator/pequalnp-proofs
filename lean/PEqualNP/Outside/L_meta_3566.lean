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

end SingleRead

end PEqualNP.Outside.L_meta_3566
