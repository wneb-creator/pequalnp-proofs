import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

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

namespace PEqualNP.Outside.L_meta_3566.InputReads

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open Pruning SingleRead

lemma nonisolated_read (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (u : Fin n) (hne : ∃ v, G.Adj u v) : u.val ∈ readList C := by
  classical
  by_contra hn
  obtain ⟨v, huv⟩ := hne
  have hno : ∀ g ∈ C.gates, u.val ∉ g.inputs := by
    intro g hg hread
    exact hn (List.mem_flatMap.mpr ⟨g, hg, hread⟩)
  have htransfer := fold_compare C.gates (List.ofFn (pairInput u v))
    (List.ofFn (pairInput v v)) (by simp) (pair_input_compare u v v)
    hao.1 hno C.output (output_ne G C hfun u)
  change circuitFun n C (pairInput u v) = true →
    circuitFun n C (pairInput v v) = true at htransfer
  rw [hfun] at htransfer
  exact G.irrefl ((graph_pair G v v).mp (htransfer ((graph_pair G u v).mpr huv)))

lemma output_lower (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hfun : circuitFun n C = graphFun G ∅) : n ≤ C.output := by
  by_contra hn
  let u : Fin n := ⟨C.output, by omega⟩
  exact output_ne G C hfun u rfl

lemma output_upper (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hfun : circuitFun n C = graphFun G ∅)
    (hne : ∃ p q, G.Adj p q) : C.output < n + C.size := by
  obtain ⟨p, q, hpq⟩ := hne
  have ht : circuitFun n C (pairInput p q) = true := by
    rw [hfun]
    exact (graph_pair G p q).mpr hpq
  by_contra hbad
  have hlen : (C.wires (List.ofFn (pairInput p q))).length = n + C.size := by
    unfold Circuit.wires
    rw [Pruning.wires_length, List.length_ofFn]
    rfl
  have hz : (C.wires (List.ofFn (pairInput p q))).getD C.output false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega :
      (C.wires (List.ofFn (pairInput p q))).length ≤ C.output)]
  change (C.wires (List.ofFn (pairInput p q))).getD C.output false = true at ht
  exact Bool.false_ne_true (hz.symm.trans ht)

lemma single_read_of_small (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (hnonisolated : ∀ u : Fin n, ∃ v, G.Adj u v)
    (hsmall : C.size + 1 < 2 * n) :
    ∃ u : Fin n, (readList C).count u.val = 1 := by
  have hn : 0 < n := by omega
  obtain ⟨v, hv⟩ := hnonisolated ⟨0, hn⟩
  have hne : ∃ u v, G.Adj u v := ⟨⟨0, hn⟩, v, hv⟩
  obtain ⟨u, hu⟩ := low_read_of_small G C hC (output_lower G C hC.2.1)
    (output_upper G C hC.2.1 hne) hsmall
  have hpos := List.count_pos_iff.mpr (nonisolated_read G C hC.1 hC.2.1 u (hnonisolated u))
  exact ⟨u, by omega⟩

lemma single_read_decomposition (C : Circuit) (hao : IsAO2 n C) (u : Fin n)
    (hcount : (readList C).count u.val = 1) :
    ∃ pre post : List Gate, ∃ g : Gate, ∃ t : ℕ,
      C.gates = pre ++ g :: post ∧
      (g.inputs = [u.val, t] ∨ g.inputs = [t, u.val]) ∧ t ≠ u.val ∧
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      (∀ q ∈ pre ++ post, u.val ∉ q.inputs) := by
  have hmem : u.val ∈ readList C := List.count_pos_iff.mp (by omega)
  obtain ⟨g, hg, hugin⟩ := List.mem_flatMap.mp hmem
  obtain ⟨pre, post, hshape⟩ := List.mem_iff_append.mp hg
  have hglen := hao.2.2 g hg
  obtain ⟨a, b, hin⟩ := List.length_eq_two.mp hglen
  have hsplit : (pre.flatMap Gate.inputs).count u.val + g.inputs.count u.val +
      (post.flatMap Gate.inputs).count u.val = 1 := by
    simpa [readList, hshape, List.flatMap_append, List.flatMap_cons, List.count_append,
      Nat.add_assoc] using hcount
  have hgpos : 0 < g.inputs.count u.val := List.count_pos_iff.mpr hugin
  have hgcount : g.inputs.count u.val = 1 := by omega
  have hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs := by
    have hz : ((pre ++ post).flatMap Gate.inputs).count u.val = 0 := by
      simp only [List.flatMap_append, List.count_append]
      omega
    intro q hq huq
    exact (List.count_eq_zero.mp hz) (List.mem_flatMap.mpr ⟨q, hq, huq⟩)
  have huab : u.val = a ∨ u.val = b := by simpa [hin] using hugin
  have hab : a ≠ b := by
    intro heq
    subst b
    have hua : u.val = a := huab.elim id id
    simp [hin, ← hua] at hgcount
  rcases huab with hua | hub
  · refine ⟨pre, post, g, b, hshape, Or.inl ?_, ?_, hao.1 g hg, hno⟩
    · simpa [hua] using hin
    · intro he
      exact hab (hua.symm.trans he.symm)
  · refine ⟨pre, post, g, a, hshape, Or.inr ?_, ?_, hao.1 g hg, hno⟩
    · simpa [hub] using hin
    · intro he
      exact hab (he.trans hub)

lemma small_single_reader (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (hnonisolated : ∀ u : Fin n, ∃ v, G.Adj u v)
    (hsmall : C.size + 1 < 2 * n) :
    ∃ u : Fin n, ∃ pre post : List Gate, ∃ g : Gate, ∃ t : ℕ,
      C.gates = pre ++ g :: post ∧
      (g.inputs = [u.val, t] ∨ g.inputs = [t, u.val]) ∧ t ≠ u.val ∧
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      (∀ q ∈ pre ++ post, u.val ∉ q.inputs) := by
  obtain ⟨u, hu⟩ := single_read_of_small G C hC hnonisolated hsmall
  exact ⟨u, single_read_decomposition C hC.1 u hu⟩

end PEqualNP.Outside.L_meta_3566.InputReads

namespace PEqualNP.Outside.L_meta_3566.Pruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open scoped BigOperators
variable {n : ℕ}

lemma read_sum_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (ho : n ≤ C.output) (hupper : C.output < n + C.size) :
    (∑ w ∈ Finset.range n, (readList C).count w) ≤ C.size + 1 := by
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
  dsimp [L] at htotal hgates
  omega

lemma read_set_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (ho : n ≤ C.output) (hupper : C.output < n + C.size)
    (S : Finset (Fin n)) (hreads : ∀ i ∈ S, 2 ≤ (readList C).count i.val) :
    2 * S.card ≤ C.size + 1 := by
  have hsum : 2 * S.card ≤ ∑ i : Fin n, (readList C).count i.val := by
    calc
      2 * S.card = ∑ i ∈ S, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ S, (readList C).count i.val := Finset.sum_le_sum hreads
      _ ≤ ∑ i : Fin n, (readList C).count i.val :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun _ _ _ => Nat.zero_le _)
  have heq := Fin.sum_univ_eq_sum_range (fun w => (readList C).count w) n
  change (∑ i : Fin n, (readList C).count i.val) = _ at heq
  rw [heq] at hsum
  exact hsum.trans (read_sum_bound G C hC ho hupper)

end PEqualNP.Outside.L_meta_3566.Pruning

namespace PEqualNP.Outside.L_meta_3566.Subcubic

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open scoped BigOperators
variable {n : ℕ}

def active (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset (Fin n) :=
  Finset.univ.filter fun v => 0 < G.degree v

lemma adj_mem_active (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (huv : G.Adj u v) : u ∈ active G := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv.degree_pos_left⟩

lemma subcubic_edges (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) :
    2 * G.edgeFinset.card ≤ 3 * (active G).card := by
  have heq : (∑ v ∈ active G, G.degree v) = ∑ v : Fin n, G.degree v := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro v hv hn
    have hnot : ¬ 0 < G.degree v := by simpa [active] using hn
    omega
  have hle : (∑ v ∈ active G, G.degree v) ≤ ∑ v ∈ active G, 3 := by
    exact Finset.sum_le_sum fun v _ => hdeg v
  rw [heq, G.sum_degrees_eq_twice_card_edges] at hle
  simpa [Nat.mul_comm] using hle

lemma bipartite_cover (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hb : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v) :
    ∃ T : Finset (Fin n), CoverPromise.IsVertexCover G T ∧
      2 * T.card ≤ (active G).card := by
  classical
  obtain ⟨c, hc⟩ := hb
  let A := (active G).filter fun v => c v = false
  let B := active G \ A
  have ha : A ⊆ active G := Finset.filter_subset _ _
  have hcard : B.card + A.card = (active G).card := Finset.card_sdiff_add_card_eq_card ha
  have hAcov : CoverPromise.IsVertexCover G A := by
    intro u v huv
    have hu := adj_mem_active G u v huv
    have hv := adj_mem_active G v u huv.symm
    have hn := hc u v huv
    cases hcu : c u <;> cases hcv : c v <;> simp_all [A]
  have hBcov : CoverPromise.IsVertexCover G B := by
    intro u v huv
    have hu := adj_mem_active G u v huv
    have hv := adj_mem_active G v u huv.symm
    have hn := hc u v huv
    cases hcu : c u <;> cases hcv : c v <;> simp_all [A, B]
  by_cases hab : A.card ≤ B.card
  · exact ⟨A, hAcov, by omega⟩
  · exact ⟨B, hBcov, by omega⟩

lemma subcubic_cover (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hb : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v)
    (hdeg : ∀ v, G.degree v ≤ 3) :
    ∃ T : Finset (Fin n), CoverPromise.IsVertexCover G T ∧
      G.edgeFinset.card + T.card ≤ 2 * (active G).card := by
  obtain ⟨T, hT, hs⟩ := bipartite_cover G hb
  have he := subcubic_edges G hdeg
  exact ⟨T, hT, by omega⟩

lemma lower_of_two_reads (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hb : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v)
    (hdeg : ∀ v, G.degree v ≤ 3)
    (C : Circuit) (hC : IsLeastAO G C)
    (ho : n ≤ C.output) (hupper : C.output < n + C.size)
    (hreads : ∀ v ∈ active G, 2 ≤ (Pruning.readList C).count v.val) :
    ∃ T : Finset (Fin n), CoverPromise.IsVertexCover G T ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  obtain ⟨T, hT, hs⟩ := subcubic_cover G hb hdeg
  have hr := Pruning.read_set_bound G C hC ho hupper (active G) hreads
  exact ⟨T, hT, hs.trans hr⟩

end PEqualNP.Outside.L_meta_3566.Subcubic


namespace PEqualNP.Outside.L_meta_3566.Subcubic

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open Pruning InputReads

lemma active_single_reader_of_small (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (hne : ∃ u v, G.Adj u v)
    (hsmall : C.size + 1 < 2 * (active G).card) :
    ∃ u ∈ active G, (readList C).count u.val = 1 := by
  by_contra hn
  have hreads : ∀ u ∈ active G, 2 ≤ (readList C).count u.val := by
    intro u hu
    have hdeg : 0 < G.degree u := (Finset.mem_filter.mp hu).2
    have hpos := List.count_pos_iff.mpr (nonisolated_read G C hC.1 hC.2.1 u
      ((G.degree_pos_iff_exists_adj u).mp hdeg))
    have hnot : (readList C).count u.val ≠ 1 := by
      intro he
      exact hn ⟨u, hu, he⟩
    omega
  have hb := read_set_bound G C hC (output_lower G C hC.2.1)
    (output_upper G C hC.2.1 hne) (active G) hreads
  omega

lemma subcubic_lower_or_single_reader (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hb : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v)
    (hdeg : ∀ v, G.degree v ≤ 3)
    (C : Circuit) (hC : IsLeastAO G C) (hne : ∃ u v, G.Adj u v) :
    (∃ T : Finset (Fin n), CoverPromise.IsVertexCover G T ∧
      G.edgeFinset.card + T.card ≤ C.size + 1) ∨
    (∃ u ∈ active G, ∃ pre post : List Gate, ∃ g : Gate, ∃ t : ℕ,
      C.gates = pre ++ g :: post ∧
      (g.inputs = [u.val, t] ∨ g.inputs = [t, u.val]) ∧ t ≠ u.val ∧
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      (∀ q ∈ pre ++ post, u.val ∉ q.inputs)) := by
  by_cases hsmall : C.size + 1 < 2 * (active G).card
  · obtain ⟨u, hu, hc⟩ := active_single_reader_of_small G C hC hne hsmall
    exact Or.inr ⟨u, hu, single_read_decomposition C hC.1 u hc⟩
  · obtain ⟨T, hT, hbound⟩ := subcubic_cover G hb hdeg
    exact Or.inl ⟨T, hT, by omega⟩

end PEqualNP.Outside.L_meta_3566.Subcubic

namespace PEqualNP.Outside.L_meta_3566.GateSavings

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_3566.Pruning

variable {n : ℕ}

def cutInput (z : Fin n) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i = z then false else x i

def cutSrc (z : Fin n) (w : ℕ) : Src n ℕ := if w = z.val then none else srcOf n w

lemma cutSrc_inr (z : Fin n) (w j : ℕ) (h : cutSrc z w = some (Sum.inr j)) : w = n + j := by
  by_cases hz : w = z.val
  · simp [cutSrc, hz] at h
  · exact srcOf_inr w j (by simpa [cutSrc, hz] using h)

lemma cutSrc_value (C : Circuit) (z : Fin n) (w : ℕ) (x : Fin n → Bool) :
    srcAt x (fun k => gateVal n C k (cutInput z x)) (cutSrc z w) =
      wireVal n C w (cutInput z x) := by
  by_cases hz : w = z.val
  · subst w
    rw [wireVal_lt C z.val z.isLt]
    simp [cutSrc, srcAt, cutInput]
  · have heq : srcAt x (fun k => gateVal n C k (cutInput z x)) (cutSrc z w) =
        srcAt (cutInput z x) (fun k => gateVal n C k (cutInput z x)) (srcOf n w) := by
      simp only [cutSrc, hz, ite_false]
      unfold srcOf
      split_ifs with hw
      · have hne : (⟨w, hw⟩ : Fin n) ≠ z := by intro he; exact hz (congrArg Fin.val he)
        simp [srcAt, cutInput, hne]
      · rfl
    rw [heq, srcAt_srcOf]

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

lemma restrict_false_saves (C : Circuit) (hC : IsAO2 n C) (ho : C.output < n + C.size)
    (z : Fin n) (E : Finset ℕ) (hE : E ⊆ Finset.range C.size)
    (hzero : ∀ k ∈ E, ∃ b : Fin 2,
      wireVal n C (opnd C k b) (cutInput z (fun _ => true)) = false) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + E.card ≤ C.size ∧
      circuitFun n D = fun x => circuitFun n C (cutInput z x) := by
  classical
  let K := Finset.range C.size
  let P : Prog n ℕ := progOf C fun k b => cutSrc z (opnd C k b)
  let v : ℕ → (Fin n → Bool) → Bool := fun k x => gateVal n C k (cutInput z x)
  let o : Src n ℕ := cutSrc z C.output
  have hclosed : Closed P id K := by
    intro k hk b j hj
    have he := cutSrc_inr z (opnd C k b) j hj
    have hkl : k < C.size := Finset.mem_range.mp hk
    have hb := hC.2.1 k hkl _ (opnd_mem C hC k hkl b)
    exact ⟨Finset.mem_range.mpr (by omega), by simpa using (show j < k by omega)⟩
  have hsol : Sol P K v := by
    intro x k hk
    change gateVal n C k (cutInput z x) = opv (isA (gateAt C k).op)
      (srcAt x (fun j => gateVal n C j (cutInput z x)) (cutSrc z (opnd C k 0)))
      (srcAt x (fun j => gateVal n C j (cutInput z x)) (cutSrc z (opnd C k 1)))
    rw [cutSrc_value, cutSrc_value]
    exact gate_eq C hC k (Finset.mem_range.mp hk) (cutInput z x)
  have hout : ∀ j, o = some (Sum.inr j) → j ∈ K := by
    intro j hj
    have he := cutSrc_inr z C.output j hj
    exact Finset.mem_range.mpr (by omega)
  obtain ⟨D, hD, hs, hf⟩ := fold_total P id v K hclosed hsol o hout
  have hsub : kept P v K ⊆ K \ E := by
    intro k hk
    obtain ⟨hkK, ha, hb⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_sdiff.mpr ⟨hkK, ?_⟩
    intro hkE
    obtain ⟨b, hz⟩ := hzero k hkE
    have hboth : ∀ c : Fin 2, srcAt (fun _ => true) (fun j => v j (fun _ => true)) (P.src k c) = true := by
      intro c
      fin_cases c
      · exact ha
      · exact hb
    have hc := hboth b
    change srcAt (fun _ => true) (fun j => gateVal n C j (cutInput z (fun _ => true)))
      (cutSrc z (opnd C k b)) = true at hc
    rw [cutSrc_value, hz] at hc
    cases hc
  have hcount := Finset.card_le_card hsub
  have hcard : (K \ E).card + E.card = C.size := by
    simpa [K] using Finset.card_sdiff_add_card_eq_card hE
  refine ⟨D, hD, by omega, ?_⟩
  funext x
  rw [hf x]
  exact cutSrc_value C z C.output x

lemma exists_opnd_of_mem (C : Circuit) (hC : IsAO2 n C) (k : ℕ) (hk : k < C.size)
    (w : ℕ) (hw : w ∈ (gateAt C k).inputs) : ∃ b : Fin 2, opnd C k b = w := by
  have hkg : k < C.gates.length := hk
  have hm : gateAt C k ∈ C.gates := by
    exact List.mem_of_getElem? (show C.gates[k]? = some (gateAt C k) by
      simp [gateAt, List.getD_eq_getElem?_getD, hkg])
  have hlen := hC.2.2 _ hm
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hw
  let b : Fin 2 := ⟨i, by omega⟩
  refine ⟨b, ?_⟩
  simp [opnd, b, List.getD_eq_getElem?_getD, hi, he]

lemma input_zero (C : Circuit) (z : Fin n) :
    wireVal n C z.val (cutInput z (fun _ => true)) = false := by
  rw [wireVal_lt C z.val z.isLt]
  simp [cutInput]

lemma and_reader_zero (C : Circuit) (hC : IsAO2 n C) (z : Fin n) (j : ℕ)
    (hj : j < C.size) (hand : (gateAt C j).op = GateOp.and)
    (hread : z.val ∈ (gateAt C j).inputs) :
    gateVal n C j (cutInput z (fun _ => true)) = false := by
  obtain ⟨b, hb⟩ := exists_opnd_of_mem C hC j hj z.val hread
  rw [gate_eq C hC j hj, hand]
  change (wireVal n C (opnd C j 0) (cutInput z (fun _ => true)) &&
    wireVal n C (opnd C j 1) (cutInput z (fun _ => true))) = false
  have hb01 : b = 0 ∨ b = 1 := by omega
  rcases hb01 with hb0 | hb1
  · rw [hb0] at hb
    rw [hb, input_zero]
    rfl
  · rw [hb1] at hb
    rw [hb, input_zero]
    exact Bool.and_false _

lemma restrict_and_reader_saves (C : Circuit) (hC : IsAO2 n C)
    (ho : C.output < n + C.size) (z : Fin n) (j : ℕ)
    (hj : j < C.size) (hand : (gateAt C j).op = GateOp.and)
    (hread : z.val ∈ (gateAt C j).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + 1 + (readers n C j).card ≤ C.size ∧
      circuitFun n D = fun x => circuitFun n C (cutInput z x) := by
  classical
  have hjnot : j ∉ readers n C j := by
    intro h
    have hr := (Finset.mem_filter.mp h).2
    have hb := hC.2.1 j hj (n + j) hr
    omega
  have hsubset : insert j (readers n C j) ⊆ Finset.range C.size := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact Finset.mem_range.mpr hj
    · exact (Finset.mem_filter.mp hk).1
  have hz : gateVal n C j (cutInput z (fun _ => true)) = false :=
    and_reader_zero C hC z j hj hand hread
  have hzero : ∀ k ∈ insert j (readers n C j), ∃ b : Fin 2,
      wireVal n C (opnd C k b) (cutInput z (fun _ => true)) = false := by
    intro k hk
    rcases Finset.mem_insert.mp hk with he | hk
    · subst k
      obtain ⟨b, hb⟩ := exists_opnd_of_mem C hC j hj z.val hread
      exact ⟨b, by rw [hb]; exact input_zero C z⟩
    · obtain ⟨hklen, hkr⟩ := Finset.mem_filter.mp hk
      obtain ⟨b, hb⟩ := exists_opnd_of_mem C hC k (Finset.mem_range.mp hklen) (n + j) hkr
      refine ⟨b, ?_⟩
      rw [hb]
      exact hz
  obtain ⟨D, hD, hs, hf⟩ := restrict_false_saves C hC ho z _ hsubset hzero
  rw [Finset.card_insert_of_notMem hjnot] at hs
  exact ⟨D, hD, by omega, hf⟩

lemma restrict_and_reader_two (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (ho : C.output < n + C.size)
    (z : Fin n) (j : ℕ) (hj : j < C.size) (hjo : C.output ≠ n + j)
    (hand : (gateAt C j).op = GateOp.and) (hread : z.val ∈ (gateAt C j).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + 2 ≤ C.size ∧
      circuitFun n D = fun x => circuitFun n C (cutInput z x) := by
  obtain ⟨k, hk, _, hkr⟩ := least_has_reader G C hC ho j hj hjo
  have hmem : k ∈ readers n C j := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkr⟩
  have hpos : 0 < (readers n C j).card := Finset.card_pos.mpr ⟨k, hmem⟩
  obtain ⟨D, hD, hs, hf⟩ := restrict_and_reader_saves C hC.1 ho z j hj hand hread
  exact ⟨D, hD, by omega, hf⟩

lemma cut_adj (G : SimpleGraph (Fin n)) (z a b : Fin n) :
    (G.deleteEdges (G.incidenceSet z)).Adj a b ↔ G.Adj a b ∧ a ≠ z ∧ b ≠ z := by
  rw [SimpleGraph.deleteEdges_adj, SimpleGraph.mk'_mem_incidenceSet_iff]
  constructor
  · rintro ⟨hab, hn⟩
    exact ⟨hab, fun h => hn ⟨hab, Or.inl h.symm⟩, fun h => hn ⟨hab, Or.inr h.symm⟩⟩
  · rintro ⟨hab, haz, hbz⟩
    exact ⟨hab, fun h => h.2.elim (fun hza => haz hza.symm) (fun hzb => hbz hzb.symm)⟩

lemma graph_cutInput (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (z : Fin n) :
    (fun x => graphFun G ∅ (cutInput z x)) =
      (fun y : Fin n → Bool => @decide (∃ a b : Fin n,
        (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a = true ∧ y b = true)
        (Classical.propDecidable _)) := by
  classical
  funext x
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
  congr 1
  apply propext
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have haz : a ≠ z := by intro h; subst a; simp [cutInput] at ha
    have hbz : b ≠ z := by intro h; subst b; simp [cutInput] at hb
    refine ⟨a, b, (cut_adj G z a b).2 ⟨hab, haz, hbz⟩, ?_, ?_⟩
    · simpa [cutInput, haz] using ha
    · simpa [cutInput, hbz] using hb
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨hab, haz, hbz⟩ := (cut_adj G z a b).1 hab
    exact ⟨a, b, hab, by simpa [cutInput, haz] using ha, by simpa [cutInput, hbz] using hb⟩

lemma reader_bound_peel (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (ho : C.output < n + C.size) (z : Fin n) (j : ℕ)
    (hj : j < C.size) (hand : (gateAt C j).op = GateOp.and)
    (hread : z.val ∈ (gateAt C j).inputs)
    (hbase : G.degree z ≤ 1 + (readers n C j).card)
    (hbonus : (∃ S : Finset (Fin n), CoverPromise.IsVertexCover
        (G.deleteEdges (G.incidenceSet z)) S ∧
        ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card < T.card) →
      G.degree z ≤ (readers n C j).card) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D =
      (fun y : Fin n → Bool => @decide (∃ a b : Fin n,
        (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a = true ∧ y b = true)
        (Classical.propDecidable _)) ∧ D.size + G.degree z ≤ C.size ∧
      ((∃ S : Finset (Fin n), CoverPromise.IsVertexCover
        (G.deleteEdges (G.incidenceSet z)) S ∧
        ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card < T.card) →
        D.size + G.degree z + 1 ≤ C.size) := by
  obtain ⟨D, hD, hs, hf⟩ := restrict_and_reader_saves C hC ho z j hj hand hread
  refine ⟨D, hD, ?_, by omega, ?_⟩
  · rw [hf, hfun]
    exact graph_cutInput G z
  · intro hd
    have hb := hbonus hd
    omega

lemma least_reader_peel (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C0 : Circuit) (hC0 : IsLeastAO G C0) (ho : C0.output < n + C0.size)
    (z : Fin n) (hpos : 0 < G.degree z) (j : ℕ)
    (hj : j < C0.size) (hand : (gateAt C0 j).op = GateOp.and)
    (hread : z.val ∈ (gateAt C0 j).inputs)
    (hbase : G.degree z ≤ 1 + (readers n C0 j).card)
    (hbonus : (∃ S : Finset (Fin n), CoverPromise.IsVertexCover
        (G.deleteEdges (G.incidenceSet z)) S ∧
        ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card < T.card) →
      G.degree z ≤ (readers n C0 j).card) :
    ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : Circuit, IsAO2 n C →
      circuitFun n C = graphFun G ∅ → ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D =
      (fun y : Fin n → Bool => @decide (∃ a b : Fin n,
        (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a = true ∧ y b = true)
        (Classical.propDecidable _)) ∧ D.size + G.degree z ≤ C.size ∧
      ((∃ S : Finset (Fin n), CoverPromise.IsVertexCover
        (G.deleteEdges (G.incidenceSet z)) S ∧
        ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card < T.card) →
        D.size + G.degree z + 1 ≤ C.size) := by
  obtain ⟨D, hD, hf, hs, hb⟩ := reader_bound_peel G C0 hC0.1 hC0.2.1 ho z j hj hand hread hbase hbonus
  refine ⟨z, hpos, fun C hC hF => ?_⟩
  have hmin := hC0.2.2 C hC hF
  exact ⟨D, hD, hf, hs.trans hmin, fun h => (hb h).trans hmin⟩

end PEqualNP.Outside.L_meta_3566.GateSavings

namespace PEqualNP.Outside.L_meta_3566.WeightedReads

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open Pruning InputReads
open scoped BigOperators
variable {n : ℕ}

lemma weighted_degree_sum (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (r : Fin n → ℕ) (S : Finset (Fin n))
    (hlocal : ∀ v, G.degree v + (if v ∈ S then 1 else 0) ≤ 2 * r v) :
    2 * G.edgeFinset.card + S.card ≤ 2 * ∑ v : Fin n, r v := by
  classical
  have hsum : (∑ v : Fin n, (G.degree v + (if v ∈ S then 1 else 0))) ≤
      ∑ v : Fin n, 2 * r v := Finset.sum_le_sum (fun v _ => hlocal v)
  have hleft : (∑ v : Fin n, (G.degree v + (if v ∈ S then 1 else 0))) =
      2 * G.edgeFinset.card + S.card := by
    rw [Finset.sum_add_distrib, G.sum_degrees_eq_twice_card_edges]
    simp
  have hright : (∑ v : Fin n, 2 * r v) = 2 * ∑ v : Fin n, r v := by
    rw [Finset.mul_sum]
  rwa [hleft, hright] at hsum

lemma weighted_budget (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (r : Fin n → ℕ) (S T : Finset (Fin n)) (B : ℕ)
    (hcard : 2 * T.card ≤ S.card)
    (hlocal : ∀ v, G.degree v + (if v ∈ S then 1 else 0) ≤ 2 * r v)
    (hsum : (∑ v : Fin n, r v) ≤ B) :
    G.edgeFinset.card + T.card ≤ B := by
  have h := weighted_degree_sum G r S hlocal
  omega

lemma weighted_read_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hne : ∃ u v, G.Adj u v)
    (S T : Finset (Fin n)) (hcard : 2 * T.card ≤ S.card)
    (hlocal : ∀ v, G.degree v + (if v ∈ S then 1 else 0) ≤
      2 * (readList C).count v.val) :
    G.edgeFinset.card + T.card ≤ C.size + 1 := by
  apply weighted_budget G (fun v => (readList C).count v.val) S T (C.size + 1) hcard hlocal
  have hsum := read_sum_bound G C hC (output_lower G C hC.2.1)
    (output_upper G C hC.2.1 hne)
  have heq := Fin.sum_univ_eq_sum_range (fun w => (readList C).count w) n
  change (∑ v : Fin n, (readList C).count v.val) = _ at heq
  rwa [heq]

lemma weighted_cover_budget (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hne : ∃ u v, G.Adj u v)
    (S T : Finset (Fin n)) (hT : CoverPromise.IsVertexCover G T)
    (hcard : 2 * T.card ≤ S.card)
    (hlocal : ∀ v, G.degree v + (if v ∈ S then 1 else 0) ≤
      2 * (readList C).count v.val) :
    CoverPromise.IsVertexCover G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 :=
  ⟨hT, weighted_read_bound G C hC hne S T hcard hlocal⟩

lemma low_read_endpoint (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hne : ∃ u v, G.Adj u v)
    (S T : Finset (Fin n)) (hT : CoverPromise.IsVertexCover G T)
    (hcard : 2 * T.card ≤ S.card)
    (hsmall : C.size + 1 < G.edgeFinset.card + T.card) :
    ∃ v : Fin n, 2 * (readList C).count v.val <
      G.degree v + (if v ∈ S then 1 else 0) := by
  classical
  by_contra hn
  have hlocal : ∀ v, G.degree v + (if v ∈ S then 1 else 0) ≤
      2 * (readList C).count v.val := by
    intro v
    exact Nat.le_of_not_gt (fun h => hn ⟨v, h⟩)
  have h := (weighted_cover_budget G C hC hne S T hT hcard hlocal).2
  omega

lemma low_read_active_vertex (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hne : ∃ u v, G.Adj u v)
    (S T : Finset (Fin n)) (hT : CoverPromise.IsVertexCover G T)
    (hcard : 2 * T.card ≤ S.card) (hS : ∀ v ∈ S, 0 < G.degree v)
    (hsmall : C.size + 1 < G.edgeFinset.card + T.card) :
    ∃ v : Fin n, 0 < G.degree v ∧ 2 * (readList C).count v.val <
      G.degree v + (if v ∈ S then 1 else 0) := by
  obtain ⟨v, hv⟩ := low_read_endpoint G C hC hne S T hT hcard hsmall
  refine ⟨v, ?_, hv⟩
  by_cases hmem : v ∈ S
  · exact hS v hmem
  · simp only [ite_eq_right hmem, Nat.add_zero] at hv
    omega

end PEqualNP.Outside.L_meta_3566.WeightedReads

namespace PEqualNP.Outside.L_meta_3566.SoleAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_3566.SingleRead

variable {n : ℕ}

def SoleAndReader (C : Circuit) (u : Fin n) : Prop :=
  ∃ pre post : List Gate, ∃ g : Gate, ∃ t : ℕ,
    C.gates = pre ++ g :: post ∧ g.op = GateOp.and ∧
    (g.inputs = [u.val, t] ∨ g.inputs = [t, u.val]) ∧ t ≠ u.val ∧
    ∀ q ∈ pre ++ post, u.val ∉ q.inputs

lemma append_false_away (xs : List Bool) (u : ℕ)
    (hxs : ∀ i, i ≠ u → xs.getD i false = false) :
    ∀ i, i ≠ u → (xs ++ [false]).getD i false = false := by
  intro i hi
  by_cases hil : i < xs.length
  · rw [List.getD_append _ _ _ _ hil]
    exact hxs i hi
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_not_gt hil)]
    cases i - xs.length <;> simp

lemma gate_false_away (xs : List Bool) (u : ℕ) (g : Gate)
    (hxs : ∀ i, i ≠ u → xs.getD i false = false)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2)
    (hread : (g.op = GateOp.and ∧ ∃ a ∈ g.inputs, a ≠ u) ∨ u ∉ g.inputs) :
    g.op.eval (g.inputs.map fun i => xs.getD i false) = false := by
  rcases hread with ⟨hand, a, ha, hne⟩ | hno
  · apply Bool.eq_false_iff.mpr
    simp only [hand, GateOp.eval, List.all_map]
    intro h
    have ht := (List.all_eq_true.mp h) a ha
    change xs.getD a false = true at ht
    rw [hxs a hne] at ht
    cases ht
  · obtain ⟨a, b, hin⟩ := List.length_eq_two.mp hlen
    have ha : a ≠ u := by intro he; exact hno (by simp [hin, he])
    have hb : b ≠ u := by intro he; exact hno (by simp [hin, he])
    rcases hop with hop | hop <;>
      simp only [hop, hin, List.map_cons, List.map_nil, hxs a ha, hxs b hb, GateOp.eval,
        List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
        Bool.false_and, Bool.false_or]

lemma fold_false_away (gs : List Gate) (u : ℕ) (xs : List Bool)
    (hxs : ∀ i, i ≠ u → xs.getD i false = false)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : ∀ g ∈ gs, g.inputs.length = 2)
    (hread : ∀ g ∈ gs, (g.op = GateOp.and ∧ ∃ a ∈ g.inputs, a ≠ u) ∨ u ∉ g.inputs) :
    ∀ i, i ≠ u → (gs.foldl step xs).getD i false = false := by
  induction gs generalizing xs with
  | nil => exact hxs
  | cons g gs ih =>
    rw [List.foldl_cons]
    apply ih
    · have hg := gate_false_away xs u g hxs (hop g (by simp)) (hlen g (by simp)) (hread g (by simp))
      simpa only [step, hg] using append_false_away xs u hxs
    · intro q hq
      exact hop q (by simp [hq])
    · intro q hq
      exact hlen q (by simp [hq])
    · intro q hq
      exact hread q (by simp [hq])

lemma sole_and_wire_singleton_false (C : Circuit) (hao : IsAO2 n C) (u : Fin n)
    (hr : SoleAndReader C u) :
    ∀ w : ℕ, w ≠ u.val → (C.wires (List.ofFn (pairInput u u))).getD w false = false := by
  obtain ⟨pre, post, g, t, hshape, hand, hin, htu, hno⟩ := hr
  change ∀ w : ℕ, w ≠ u.val → (C.gates.foldl step (List.ofFn (pairInput u u))).getD w false = false
  refine fold_false_away C.gates u.val _ ?_ hao.1 hao.2.2 ?_
  · intro i hi
    by_cases hil : i < n
    · let j : Fin n := ⟨i, hil⟩
      have hj : j ≠ u := by intro h; exact hi (congrArg Fin.val h)
      change (List.ofFn (pairInput u u)).getD j.val false = false
      rw [ofFn_get]
      simp [pairInput, hj]
    · simp [List.getD_eq_getElem?_getD, hil]
  · intro q hq
    rw [hshape] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inr (hno q (List.mem_append_left _ hq))
    · rcases List.mem_cons.mp hq with he | hq
      · subst q
        exact Or.inl ⟨hand, t, by rcases hin with h | h <;> simp [h], htu⟩
      · exact Or.inr (hno q (List.mem_append_right _ hq))

lemma adjacent_sole_and_degree (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (u v : Fin n) (hu : SoleAndReader C u) (hv : SoleAndReader C v) (huv : G.Adj u v) :
    G.degree u ≤ 1 := by
  obtain ⟨pre, post, g, t, hshape, hand, hin, htu, hno⟩ := hu
  have hs := sole_and_neighbor_singleton G C u pre post g t hshape hand hin hao hno hfun htu
  have htv : t = v.val := by
    by_contra hne
    have hz := sole_and_wire_singleton_false C hao v hv t hne
    have ht := hs v huv
    rw [hz] at ht
    cases ht
  have hsub : G.neighborFinset u ⊆ {v} := by
    intro w hw
    have ht := hs w ((G.mem_neighborFinset u w).1 hw)
    have hwv : w = v := by
      rw [htv] at ht
      change wireVal n C v.val (pairInput w w) = true at ht
      rw [PEqualNP.Outside.L_meta_3566.Pruning.wireVal_lt C v.val v.isLt] at ht
      have hvw : v = w := by
        simpa only [pairInput, decide_eq_true_eq, or_self] using ht
      exact hvw.symm
    simpa using hwv
  have hc := Finset.card_le_card hsub
  simpa [G.card_neighborFinset_eq_degree] using hc

lemma high_degree_sole_and_independent (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅) :
    ∀ u v : Fin n, 2 ≤ G.degree u → SoleAndReader C u → SoleAndReader C v → ¬ G.Adj u v := by
  intro u v hd hu hv huv
  have hlow := adjacent_sole_and_degree G C hao hfun u v hu hv huv
  omega

end PEqualNP.Outside.L_meta_3566.SoleAnd

namespace PEqualNP.Outside.L_meta_3566.MobiusKantor

/-- GP(8,3): outer vertices 0..7, inner vertices 8..15. -/
abbrev graph : SimpleGraph (Fin 16) :=
  SimpleGraph.fromRel fun u v =>
    (u.val < 8 ∧ v.val < 8 ∧ (u.val + 1) % 8 = v.val) ∨
    (u.val < 8 ∧ v.val = u.val + 8) ∨
    (8 ≤ u.val ∧ 8 ≤ v.val ∧ 8 + (u.val - 8 + 3) % 8 = v.val)

/-- Exact edge list of the independent search fixture. -/
def fixtureEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 7), (0, 8), (1, 2), (1, 9), (2, 3), (2, 10), (3, 4), (3, 11), (4, 5), (4, 12), (5, 6), (5, 13), (6, 7), (6, 14), (7, 15), (8, 11), (8, 13), (9, 12), (9, 14), (10, 13), (10, 15), (11, 14), (12, 15)]

lemma graph_eq_fixture : graph = PEqualNP.EdgeOwnership.edgeGraph 16 fixtureEdges := by
  ext u v
  revert u v
  decide

abbrev color (v : Fin 16) : Bool :=
  decide ((v.val < 8 ∧ v.val % 2 = 0) ∨ (8 ≤ v.val ∧ v.val % 2 = 1))

lemma bipartite : ∀ u v : Fin 16, graph.Adj u v → color u ≠ color v := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma no_four : PEqualNP.TopForm.NoFourCycle graph := by
  decide

lemma degree_three : ∀ z : Fin 16, graph.degree z = 3 := by
  decide

lemma edges_twenty_four : graph.edgeFinset.card = 24 := by
  decide

abbrev outer (i : Fin 8) : Fin 16 := ⟨i.val, by omega⟩
abbrev inner (i : Fin 8) : Fin 16 := ⟨i.val + 8, by omega⟩

lemma spokes : ∀ i : Fin 8, graph.Adj (outer i) (inner i) := by
  decide

lemma cover_lower (S : Finset (Fin 16))
    (hS : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover graph S) :
    8 ≤ S.card := by
  let f (i : Fin 8) : Fin 16 := if outer i ∈ S then outer i else inner i
  have hmem (i : Fin 8) : f i ∈ S := by
    dsimp [f]
    split_ifs with h
    · exact h
    · exact (hS _ _ (spokes i)).resolve_left h
  have hfmod (i : Fin 8) : (f i).val % 8 = i.val := by
    dsimp [f]
    split_ifs <;> dsimp [outer, inner] <;> omega
  have hinj : Function.Injective (fun i : Fin 8 => (⟨f i, hmem i⟩ : S)) := by
    intro i j hij
    have heq : f i = f j := congrArg Subtype.val hij
    have hi := hfmod i
    have hj := hfmod j
    apply Fin.ext
    rw [heq] at hi
    omega
  have hc := Fintype.card_le_of_injective _ hinj
  simpa using hc

abbrev cover : Finset (Fin 16) := {0, 2, 4, 6, 9, 11, 13, 15}

lemma cover_valid : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover graph cover := by
  unfold PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
  decide

lemma cover_card : cover.card = 8 := by
  decide

lemma cover_minimum : PEqualNP.MetaComplexity.NestedCover.IsMinCover graph cover := by
  exact ⟨cover_valid, fun S hS => by simpa only [cover_card] using cover_lower S hS⟩

abbrev cutCover (z : Fin 16) : Finset (Fin 16) :=
  Finset.univ.filter (fun v => color v = color z ∧ v ≠ z)

set_option synthInstance.maxSize 1000 in
lemma cut_cover_valid : ∀ z : Fin 16,
    PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
      (graph.deleteEdges (graph.incidenceSet z)) (cutCover z) := by
  unfold PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
  simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.mk'_mem_incidenceSet_iff]
  decide

lemma cut_cover_card : ∀ z : Fin 16, (cutCover z).card = 7 := by
  decide

lemma cut_cover_lower (z : Fin 16) (S : Finset (Fin 16))
    (hS : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
      (graph.deleteEdges (graph.incidenceSet z)) S) :
    7 ≤ S.card := by
  have hfull : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover graph (insert z S) := by
    intro a b hab
    by_cases hza : z = a
    · exact Or.inl (by simp [← hza])
    by_cases hzb : z = b
    · exact Or.inr (by simp [← hzb])
    have hcut : (graph.deleteEdges (graph.incidenceSet z)).Adj a b := by
      simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.mk'_mem_incidenceSet_iff]
      exact ⟨hab, fun h => h.2.elim hza hzb⟩
    rcases hS a b hcut with ha | hb
    · exact Or.inl (Finset.mem_insert_of_mem ha)
    · exact Or.inr (Finset.mem_insert_of_mem hb)
  have h := cover_lower (insert z S) hfull
  have hcard := Finset.card_insert_le z S
  omega

lemma cut_cover_minimum (z : Fin 16) :
    PEqualNP.MetaComplexity.NestedCover.IsMinCover
      (graph.deleteEdges (graph.incidenceSet z)) (cutCover z) := by
  exact ⟨cut_cover_valid z, fun S hS => by
    simpa only [cut_cover_card] using cut_cover_lower z S hS⟩

end PEqualNP.Outside.L_meta_3566.MobiusKantor


namespace PEqualNP.Outside.L_meta_3566.MobiusKantor

def symmetry (z v : Fin 16) : Fin 16 :=
  if z.val < 8 then
    ⟨(if v.val < 8 then 0 else 8) + (v.val % 8 + z.val) % 8, by split_ifs <;> omega⟩
  else
    ⟨(if v.val < 8 then 8 else 0) + (3 * (v.val % 8) + z.val % 8) % 8,
      by split_ifs <;> omega⟩

lemma symmetry_zero : ∀ z : Fin 16, symmetry z 0 = z := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma symmetry_bijective : ∀ z : Fin 16, Function.Bijective (symmetry z) := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma symmetry_adj : ∀ z u v : Fin 16,
    graph.Adj (symmetry z u) (symmetry z v) ↔ graph.Adj u v := by decide

end PEqualNP.Outside.L_meta_3566.MobiusKantor

namespace PEqualNP.Outside.L_meta_3566.ActiveReads

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_3566.Pruning
open PEqualNP.Outside.L_meta_3566.GateSavings

variable {n : ℕ}

lemma restrict_read_saves_one (C : Circuit) (hC : IsAO2 n C)
    (ho : C.output < n + C.size) (z : Fin n) (hread : z.val ∈ readList C) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + 1 ≤ C.size ∧
      circuitFun n D = fun x => circuitFun n C (cutInput z x) := by
  classical
  obtain ⟨g, hg, hzg⟩ := List.mem_flatMap.mp hread
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hg
  have hj' : j < C.size := hj
  have hgate : gateAt C j = g := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj, he]
  obtain ⟨b, hb⟩ := exists_opnd_of_mem C hC j hj' z.val (by rwa [hgate])
  have hsub : ({j} : Finset ℕ) ⊆ Finset.range C.size := by
    intro k hk
    have hk' : k = j := Finset.mem_singleton.mp hk
    subst k
    exact Finset.mem_range.mpr hj'
  have hzero : ∀ k ∈ ({j} : Finset ℕ), ∃ b : Fin 2,
      wireVal n C (opnd C k b) (cutInput z (fun _ => true)) = false := by
    intro k hk
    have hk' : k = j := Finset.mem_singleton.mp hk
    subst k
    exact ⟨b, by rw [hb]; exact input_zero C z⟩
  obtain ⟨D, hD, hs, hf⟩ := restrict_false_saves C hC ho z {j} hsub hzero
  exact ⟨D, hD, by simpa using hs, hf⟩

lemma graph_cutInput_of_isolated (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (hiso : ∀ v, ¬ G.Adj z v) :
    (fun x => graphFun G ∅ (cutInput z x)) = graphFun G ∅ := by
  classical
  funext x
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
  congr 1
  apply propext
  have hne : ∀ a b, G.Adj a b → a ≠ z ∧ b ≠ z := by
    intro a b hab
    exact ⟨fun h => hiso b (h ▸ hab), fun h => hiso a (h ▸ hab.symm)⟩
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨haz, hbz⟩ := hne a b hab
    exact ⟨a, b, hab, by simpa [cutInput, haz] using ha,
      by simpa [cutInput, hbz] using hb⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨haz, hbz⟩ := hne a b hab
    exact ⟨a, b, hab, by simpa [cutInput, haz] using ha,
      by simpa [cutInput, hbz] using hb⟩

lemma least_read_nonisolated (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hne : ∃ p q, G.Adj p q)
    (z : Fin n) (hread : z.val ∈ readList C) : ∃ v, G.Adj z v := by
  classical
  by_contra hiso
  push Not at hiso
  obtain ⟨D, hD, hs, hf⟩ := restrict_read_saves_one C hC.1
    (InputReads.output_upper G C hC.2.1 hne) z hread
  have hDF : circuitFun n D = graphFun G ∅ := by
    rw [hf, hC.2.1]
    exact graph_cutInput_of_isolated G z hiso
  have hmin := hC.2.2 D hD hDF
  omega

lemma least_read_iff_degree_pos (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hne : ∃ p q, G.Adj p q) (z : Fin n) :
    z.val ∈ readList C ↔ 0 < G.degree z := by
  rw [G.degree_pos_iff_exists_adj]
  exact ⟨least_read_nonisolated G C hC hne z,
    InputReads.nonisolated_read G C hC.1 hC.2.1 z⟩

end PEqualNP.Outside.L_meta_3566.ActiveReads

namespace PEqualNP.Outside.L_meta_3566.LCF18

/-- Numeric edge list of the 18-cycle with chord steps [5,7,-7,7,-7,-5] repeated. -/
def fixtureEdges : List (ℕ × ℕ) :=
  [(0, 1), (0, 5), (0, 17), (1, 2), (1, 8), (2, 3), (2, 13), (3, 4), (3, 10), (4, 5), (4, 15), (5, 6), (6, 7), (6, 11), (7, 8), (7, 14), (8, 9), (9, 10), (9, 16), (10, 11), (11, 12), (12, 13), (12, 17), (13, 14), (14, 15), (15, 16), (16, 17)]

abbrev graph : SimpleGraph (Fin 18) := PEqualNP.EdgeOwnership.edgeGraph 18 fixtureEdges

abbrev color (v : Fin 18) : Bool :=
  decide (v.val % 2 = 0)

lemma bipartite : ∀ u v : Fin 18, graph.Adj u v → color u ≠ color v := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma no_four : PEqualNP.TopForm.NoFourCycle graph := by
  decide

lemma degree_three : ∀ z : Fin 18, graph.degree z = 3 := by
  decide

lemma edges_twenty_seven : graph.edgeFinset.card = 27 := by
  decide

abbrev matchEven (i : Fin 9) : Fin 18 := ⟨2 * i.val, by omega⟩
abbrev matchOdd (i : Fin 9) : Fin 18 := ⟨2 * i.val + 1, by omega⟩

lemma hamilton_matching : ∀ i : Fin 9, graph.Adj (matchEven i) (matchOdd i) := by
  decide

lemma cover_lower (S : Finset (Fin 18))
    (hS : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover graph S) :
    9 ≤ S.card := by
  let f (i : Fin 9) : Fin 18 := if matchEven i ∈ S then matchEven i else matchOdd i
  have hmem (i : Fin 9) : f i ∈ S := by
    dsimp [f]
    split_ifs with h
    · exact h
    · exact (hS _ _ (hamilton_matching i)).resolve_left h
  have hfdiv (i : Fin 9) : (f i).val / 2 = i.val := by
    dsimp [f]
    split_ifs <;> dsimp [matchEven, matchOdd] <;> omega
  have hinj : Function.Injective (fun i : Fin 9 => (⟨f i, hmem i⟩ : S)) := by
    intro i j hij
    have heq : f i = f j := congrArg Subtype.val hij
    have hi := hfdiv i
    have hj := hfdiv j
    apply Fin.ext
    rw [heq] at hi
    omega
  have hc := Fintype.card_le_of_injective _ hinj
  simpa using hc

abbrev cover : Finset (Fin 18) := {0, 2, 4, 6, 8, 10, 12, 14, 16}

lemma cover_valid : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover graph cover := by
  unfold PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
  decide

lemma cover_card : cover.card = 9 := by
  decide

lemma cover_minimum : PEqualNP.MetaComplexity.NestedCover.IsMinCover graph cover := by
  exact ⟨cover_valid, fun S hS => by simpa only [cover_card] using cover_lower S hS⟩

abbrev cutCover (z : Fin 18) : Finset (Fin 18) :=
  Finset.univ.filter (fun v => color v = color z ∧ v ≠ z)

set_option synthInstance.maxSize 1000 in
lemma cut_cover_valid : ∀ z : Fin 18,
    PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
      (graph.deleteEdges (graph.incidenceSet z)) (cutCover z) := by
  unfold PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
  simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.mk'_mem_incidenceSet_iff]
  decide

lemma cut_cover_card : ∀ z : Fin 18, (cutCover z).card = 8 := by
  decide

lemma cut_cover_lower (z : Fin 18) (S : Finset (Fin 18))
    (hS : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover
      (graph.deleteEdges (graph.incidenceSet z)) S) :
    8 ≤ S.card := by
  have hfull : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover graph (insert z S) := by
    intro a b hab
    by_cases hza : z = a
    · exact Or.inl (by simp [← hza])
    by_cases hzb : z = b
    · exact Or.inr (by simp [← hzb])
    have hcut : (graph.deleteEdges (graph.incidenceSet z)).Adj a b := by
      simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.mk'_mem_incidenceSet_iff]
      exact ⟨hab, fun h => h.2.elim hza hzb⟩
    rcases hS a b hcut with ha | hb
    · exact Or.inl (Finset.mem_insert_of_mem ha)
    · exact Or.inr (Finset.mem_insert_of_mem hb)
  have h := cover_lower (insert z S) hfull
  have hcard := Finset.card_insert_le z S
  omega

lemma cut_cover_minimum (z : Fin 18) :
    PEqualNP.MetaComplexity.NestedCover.IsMinCover
      (graph.deleteEdges (graph.incidenceSet z)) (cutCover z) := by
  exact ⟨cut_cover_valid z, fun S hS => by
    simpa only [cut_cover_card] using cut_cover_lower z S hS⟩

end PEqualNP.Outside.L_meta_3566.LCF18


namespace PEqualNP.Outside.L_meta_3566.NoRawReader

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge
open Pruning SingleRead InputReads

variable {n : ℕ}

lemma sole_and_raw_degree (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u v : Fin n) (pre post : List Gate) (g : Gate)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.and)
    (hinputs : g.inputs = [u.val, v.val] ∨ g.inputs = [v.val, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (huv : u ≠ v) :
    G.degree u ≤ 1 := by
  have hvu : v.val ≠ u.val := by
    intro he
    exact huv (Fin.ext he.symm)
  have hs := sole_and_neighbor_singleton G C u pre post g v.val
    hshape hop hinputs hao hno hfun hvu
  have hsub : G.neighborFinset u ⊆ {v} := by
    intro w hw
    have ht := hs w ((G.mem_neighborFinset u w).1 hw)
    change wireVal n C v.val (pairInput w w) = true at ht
    rw [wireVal_lt C v.val v.isLt] at ht
    have hvw : v = w := by
      simpa only [pairInput, decide_eq_true_eq, or_self] using ht
    simpa using hvw.symm
  have hc := Finset.card_le_card hsub
  simpa [G.card_neighborFinset_eq_degree] using hc

lemma sole_reader_other_not_input (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (htu : t ≠ u.val) (hao : IsAO2 n C)
    (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅)
    (hfour : NoFourCycle G) (hdeg : 2 ≤ G.degree u) :
    n ≤ t := by
  by_contra hsmall
  let v : Fin n := ⟨t, by omega⟩
  have huv : u ≠ v := by
    intro he
    exact htu (congrArg Fin.val he.symm)
  have hg : g ∈ C.gates := by rw [hshape]; simp
  have hin : g.inputs = [u.val, v.val] ∨ g.inputs = [v.val, u.val] := hinputs
  rcases hao.1 g hg with hand | hor
  · have hd := sole_and_raw_degree G C u v pre post g hshape hand hin hao hno hfun huv
    omega
  · have hs : (C.wires (List.ofFn (pairInput v v))).getD t false = true := by
      change wireVal n C v.val (pairInput v v) = true
      rw [wireVal_lt C v.val v.isLt]
      simp [pairInput]
    have hd := arbitrary_or_single_read_degree G C u v pre post g t huv
      hshape hor hinputs hao hno hs hfun hfour
    omega

lemma single_read_internal_operand (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hfour : NoFourCycle G) (u : Fin n) (hdeg : 2 ≤ G.degree u)
    (hcount : (readList C).count u.val = 1) :
    ∃ pre post : List Gate, ∃ g : Gate, ∃ t : ℕ,
      C.gates = pre ++ g :: post ∧
      (g.inputs = [u.val, t] ∨ g.inputs = [t, u.val]) ∧ n ≤ t ∧
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      (∀ q ∈ pre ++ post, u.val ∉ q.inputs) := by
  obtain ⟨pre, post, g, t, hshape, hin, htu, hop, hno⟩ :=
    single_read_decomposition C hao u hcount
  exact ⟨pre, post, g, t, hshape, hin,
    sole_reader_other_not_input G C u pre post g t hshape hin htu hao hno hfun hfour hdeg,
    hop, hno⟩

end PEqualNP.Outside.L_meta_3566.NoRawReader

namespace PEqualNP.Outside.L_meta_3566.LowReaderFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_3566.Pruning
open scoped BigOperators

variable {n : ℕ}

lemma readList_count_sum (C : Circuit) (w : ℕ) :
    (readList C).count w = ∑ j ∈ Finset.range C.size, (gateAt C j).inputs.count w := by
  unfold readList
  rw [List.count_flatMap]
  have hh : C.gates.map (List.count w ∘ Gate.inputs) =
      List.ofFn (fun j : Fin C.size => (gateAt C j.val).inputs.count w) := by
    conv_lhs => rw [← List.ofFn_get C.gates, List.map_ofFn]
    congr 1
    funext j
    simp [gateAt, List.getD_eq_getElem?_getD, j.isLt]
  rw [hh, Fin.sum_ofFn]
  exact Fin.sum_univ_eq_sum_range (fun j => (gateAt C j).inputs.count w) C.size

lemma readers_card_le_count (C : Circuit) (j : ℕ) :
    (readers n C j).card ≤ (readList C).count (n + j) := by
  classical
  rw [readList_count_sum]
  have hsum : (∑ k ∈ readers n C j, 1) ≤
      ∑ k ∈ readers n C j, (gateAt C k).inputs.count (n + j) := by
    apply Finset.sum_le_sum
    intro k hk
    exact List.count_pos_iff.mpr (Finset.mem_filter.mp hk).2
  have hsub : (∑ k ∈ readers n C j, (gateAt C k).inputs.count (n + j)) ≤
      ∑ k ∈ Finset.range C.size, (gateAt C k).inputs.count (n + j) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro a ha hna
    exact Nat.zero_le _
  have hsum' : (readers n C j).card ≤
      ∑ k ∈ readers n C j, (gateAt C k).inputs.count (n + j) := by simpa using hsum
  exact hsum'.trans hsub

lemma charged_once_budget (n s q : ℕ) (r : ℕ → ℕ) (hq : q < s)
    (htotal : (∑ w ∈ Finset.range (n + s), r w) = 2 * s)
    (hpositive : ∀ u : Fin n, 1 ≤ r u.val)
    (hlive : ∀ j < s, j ≠ q → 1 ≤ r (n + j))
    (f : Fin n → ℕ)
    (hvalid : ∀ u : Fin n, r u.val = 1 → f u < s)
    (hinj : ∀ u v : Fin n, r u.val = 1 → r v.val = 1 → f u = f v → u = v)
    (hcharge : ∀ u : Fin n, r u.val = 1 → 2 ≤ r (n + f u)) :
    2 * n ≤ s + 1 := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun u => r u.val = 1)
  let J : Finset ℕ := S.image f
  have hJsub : J ⊆ Finset.range s := by
    intro j hj
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (hvalid u (Finset.mem_filter.mp hu).2)
  have hJcard : J.card = S.card := by
    apply Finset.card_image_iff.mpr
    intro u hu v hv he
    exact hinj u v (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2 he
  have hinputs : 2 * n ≤ (∑ u : Fin n, r u.val) + S.card := by
    have hp : ∀ u : Fin n, 2 ≤ r u.val + if u ∈ S then 1 else 0 := by
      intro u
      by_cases hu : u ∈ S
      · have hc := (Finset.mem_filter.mp hu).2
        simp only [hu, ite_true]
        omega
      · have hc : r u.val ≠ 1 := by intro he; exact hu (Finset.mem_filter.mpr ⟨by simp, he⟩)
        have hpos := hpositive u
        simp only [hu, ite_false]
        omega
    have hs := Finset.sum_le_sum (fun (u : Fin n) (_ : u ∈ Finset.univ) => hp u)
    simpa [Finset.sum_add_distrib, Finset.sum_ite_mem, Nat.mul_comm] using hs
  have hinternal : s + J.card ≤ (∑ j ∈ Finset.range s, r (n + j)) + 1 := by
    have hp : ∀ j ∈ Finset.range s,
        1 + (if j ∈ J then 1 else 0) ≤ r (n + j) + if j = q then 1 else 0 := by
      intro j hj
      by_cases hJ : j ∈ J
      · obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hJ
        have hc := hcharge u (Finset.mem_filter.mp hu).2
        rw [he] at hc
        split_ifs <;> omega
      · by_cases he : j = q
        · subst j
          simp [hJ]
        · have hc := hlive j (Finset.mem_range.mp hj) he
          simp only [hJ, he, ite_false]
          omega
    have hs := Finset.sum_le_sum hp
    have hinter : Finset.range s ∩ J = J := Finset.inter_eq_right.mpr hJsub
    simpa [Finset.sum_add_distrib, Finset.sum_ite_mem, hinter, Finset.mem_range.mpr hq] using hs
  rw [hJcard] at hinternal
  rw [Fin.sum_univ_eq_sum_range] at hinputs
  rw [Finset.sum_range_add] at htotal
  omega

lemma least_charged_once_slots_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (ho : n ≤ C.output) (hupper : C.output < n + C.size)
    (hpositive : ∀ u : Fin n, 1 ≤ (readList C).count u.val)
    (f : Fin n → ℕ)
    (hvalid : ∀ u : Fin n, (readList C).count u.val = 1 → f u < C.size)
    (hinj : ∀ u v : Fin n, (readList C).count u.val = 1 →
      (readList C).count v.val = 1 → f u = f v → u = v)
    (hslots : ∀ u : Fin n, (readList C).count u.val = 1 → 2 ≤ (readList C).count (n + f u)) :
    2 * n ≤ C.size + 1 := by
  classical
  let q := C.output - n
  have hq : q < C.size := by dsimp [q]; omega
  have htotal : (∑ w ∈ Finset.range (n + C.size), (readList C).count w) = 2 * C.size := by
    have hsum : (∑ w ∈ Finset.range (n + C.size), ((readList C) : Multiset ℕ).count w) =
        (readList C).length := by
      apply Multiset.sum_count_eq_card
      intro w hw
      exact Finset.mem_range.mpr (readList_bound C hC.1 w hw)
    simpa [readList_length C hC.1] using hsum
  apply charged_once_budget n C.size q ((readList C).count) hq htotal hpositive
    ?_ f hvalid hinj ?_
  · intro j hj hjq
    have hjo : C.output ≠ n + j := by intro he; apply hjq; dsimp [q]; omega
    obtain ⟨k, hk, _, hr⟩ := least_has_reader G C hC hupper j hj hjo
    exact List.count_pos_iff.mpr (reader_mem C j k hk hr)
  · intro u hu
    exact hslots u hu

lemma least_charged_once_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (ho : n ≤ C.output) (hupper : C.output < n + C.size)
    (hpositive : ∀ u : Fin n, 1 ≤ (readList C).count u.val)
    (f : Fin n → ℕ)
    (hvalid : ∀ u : Fin n, (readList C).count u.val = 1 → f u < C.size)
    (hinj : ∀ u v : Fin n, (readList C).count u.val = 1 →
      (readList C).count v.val = 1 → f u = f v → u = v)
    (hfanout : ∀ u : Fin n, (readList C).count u.val = 1 → 2 ≤ (readers n C (f u)).card) :
    2 * n ≤ C.size + 1 := by
  apply least_charged_once_slots_bound G C hC ho hupper hpositive f hvalid hinj
  intro u hu
  exact (hfanout u hu).trans (readers_card_le_count C (f u))

lemma least_once_reader_low_fanout (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (ho : n ≤ C.output) (hupper : C.output < n + C.size)
    (hpositive : ∀ u : Fin n, 1 ≤ (readList C).count u.val)
    (f : Fin n → ℕ)
    (hvalid : ∀ u : Fin n, (readList C).count u.val = 1 → f u < C.size)
    (hinj : ∀ u v : Fin n, (readList C).count u.val = 1 →
      (readList C).count v.val = 1 → f u = f v → u = v)
    (hsmall : C.size + 1 < 2 * n) :
    ∃ u : Fin n, (readList C).count u.val = 1 ∧ (readers n C (f u)).card ≤ 1 := by
  by_contra hn
  push Not at hn
  have hfanout : ∀ u : Fin n, (readList C).count u.val = 1 → 2 ≤ (readers n C (f u)).card := by
    intro u hu
    have hh := hn u hu
    omega
  have hb := least_charged_once_bound G C hC ho hupper hpositive f hvalid hinj hfanout
  omega

lemma least_once_reader_low_slots (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (ho : n ≤ C.output) (hupper : C.output < n + C.size)
    (hpositive : ∀ u : Fin n, 1 ≤ (readList C).count u.val)
    (f : Fin n → ℕ)
    (hvalid : ∀ u : Fin n, (readList C).count u.val = 1 → f u < C.size)
    (hinj : ∀ u v : Fin n, (readList C).count u.val = 1 →
      (readList C).count v.val = 1 → f u = f v → u = v)
    (hsmall : C.size + 1 < 2 * n) :
    ∃ u : Fin n, (readList C).count u.val = 1 ∧ (readList C).count (n + f u) ≤ 1 := by
  by_contra hn
  push Not at hn
  have hfanout : ∀ u : Fin n, (readList C).count u.val = 1 → 2 ≤ (readList C).count (n + f u) := by
    intro u hu
    have hh := hn u hu
    omega
  have hb := least_charged_once_slots_bound G C hC ho hupper hpositive f hvalid hinj hfanout
  omega

end PEqualNP.Outside.L_meta_3566.LowReaderFrontier

namespace PEqualNP.Outside.L_meta_3566.LowReaderFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_3566.Pruning

variable {n : ℕ}

lemma single_reader_index_internal (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hfour : NoFourCycle G) (u : Fin n) (hdeg : 2 ≤ G.degree u)
    (hcount : (readList C).count u.val = 1) :
    ∃ j < C.size, ∃ t : ℕ, n ≤ t ∧
      ((gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val]) := by
  obtain ⟨pre, post, g, t, hshape, hin, htn, _, _⟩ :=
    NoRawReader.single_read_internal_operand G C hao hfun hfour u hdeg hcount
  have hj : pre.length < C.size := by
    change pre.length < C.gates.length
    rw [hshape, List.length_append, List.length_cons]
    omega
  have hgate : gateAt C pre.length = g := by
    simp [gateAt, hshape, List.getD_eq_getElem?_getD]
  exact ⟨pre.length, hj, t, htn, by simpa [hgate] using hin⟩

lemma sole_reader_map (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hfour : NoFourCycle G) (hdeg : ∀ u : Fin n, 2 ≤ G.degree u) :
    ∃ f : Fin n → ℕ,
      (∀ u : Fin n, (readList C).count u.val = 1 → f u < C.size ∧
        ∃ t : ℕ, n ≤ t ∧
          ((gateAt C (f u)).inputs = [u.val, t] ∨ (gateAt C (f u)).inputs = [t, u.val])) ∧
      (∀ u v : Fin n, (readList C).count u.val = 1 → (readList C).count v.val = 1 →
        f u = f v → u = v) := by
  classical
  have hex : ∀ u : Fin n, ∃ j : ℕ, (readList C).count u.val = 1 → j < C.size ∧
      ∃ t : ℕ, n ≤ t ∧
        ((gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val]) := by
    intro u
    by_cases hu : (readList C).count u.val = 1
    · obtain ⟨j, hj, t, ht, hin⟩ := single_reader_index_internal G C hao hfun hfour u (hdeg u) hu
      exact ⟨j, fun _ => ⟨hj, t, ht, hin⟩⟩
    · exact ⟨0, fun h => False.elim (hu h)⟩
  choose f hf using hex
  refine ⟨f, hf, ?_⟩
  intro u v hu hv he
  obtain ⟨_, t, htn, hin⟩ := hf u hu
  obtain ⟨_, t', _, hin'⟩ := hf v hv
  have hvmem : v.val ∈ (gateAt C (f u)).inputs := by
    rw [he]
    rcases hin' with h | h <;> simp [h]
  have hvut : v.val = u.val ∨ v.val = t := by
    rcases hin with h | h
    · simpa [h] using hvmem
    · simpa [h, or_comm] using hvmem
  have hne : v.val ≠ t := by have hvn := v.isLt; omega
  exact Fin.ext ((hvut.resolve_right hne).symm)

lemma graph_once_reader_low_fanout (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (hfour : NoFourCycle G) (hdeg : ∀ u : Fin n, 2 ≤ G.degree u)
    (hsmall : C.size + 1 < 2 * n) :
    ∃ u : Fin n, ∃ j < C.size, (readList C).count u.val = 1 ∧
      (readers n C j).card ≤ 1 ∧ ∃ t : ℕ, n ≤ t ∧
        ((gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val]) := by
  have hn : 0 < n := by omega
  let u0 : Fin n := ⟨0, hn⟩
  have hne : ∃ u v, G.Adj u v := by
    obtain ⟨v, hv⟩ := (G.degree_pos_iff_exists_adj u0).mp (by have hh := hdeg u0; omega)
    exact ⟨u0, v, hv⟩
  have hpositive : ∀ u : Fin n, 1 ≤ (readList C).count u.val := by
    intro u
    apply List.count_pos_iff.mpr
    apply InputReads.nonisolated_read G C hC.1 hC.2.1 u
    apply (G.degree_pos_iff_exists_adj u).mp
    have hh := hdeg u
    omega
  obtain ⟨f, hf, hinj⟩ := sole_reader_map G C hC.1 hC.2.1 hfour hdeg
  obtain ⟨u, hu, hfanout⟩ := least_once_reader_low_fanout G C hC
    (InputReads.output_lower G C hC.2.1) (InputReads.output_upper G C hC.2.1 hne)
    hpositive f (fun u hu => (hf u hu).1) hinj hsmall
  obtain ⟨hj, t, htn, hin⟩ := hf u hu
  exact ⟨u, f u, hj, hu, hfanout, t, htn, hin⟩

lemma graph_once_reader_low_slots (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (hfour : NoFourCycle G) (hdeg : ∀ u : Fin n, 2 ≤ G.degree u)
    (hsmall : C.size + 1 < 2 * n) :
    ∃ u : Fin n, ∃ j < C.size, (readList C).count u.val = 1 ∧
      u.val ∈ (gateAt C j).inputs ∧ (readList C).count (n + j) ≤ 1 ∧ ∃ t : ℕ, n ≤ t ∧
        ((gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val]) := by
  have hn : 0 < n := by omega
  let u0 : Fin n := ⟨0, hn⟩
  have hne : ∃ u v, G.Adj u v := by
    obtain ⟨v, hv⟩ := (G.degree_pos_iff_exists_adj u0).mp (by have hh := hdeg u0; omega)
    exact ⟨u0, v, hv⟩
  have hpositive : ∀ u : Fin n, 1 ≤ (readList C).count u.val := by
    intro u
    apply List.count_pos_iff.mpr
    apply InputReads.nonisolated_read G C hC.1 hC.2.1 u
    apply (G.degree_pos_iff_exists_adj u).mp
    have hh := hdeg u
    omega
  obtain ⟨f, hf, hinj⟩ := sole_reader_map G C hC.1 hC.2.1 hfour hdeg
  obtain ⟨u, hu, hfanout⟩ := least_once_reader_low_slots G C hC
    (InputReads.output_lower G C hC.2.1) (InputReads.output_upper G C hC.2.1 hne)
    hpositive f (fun u hu => (hf u hu).1) hinj hsmall
  obtain ⟨hj, t, htn, hin⟩ := hf u hu
  have hread : u.val ∈ (gateAt C (f u)).inputs := by
    rcases hin with h | h <;> simp [h]
  exact ⟨u, f u, hj, hu, hread, hfanout, t, htn, hin⟩

end PEqualNP.Outside.L_meta_3566.LowReaderFrontier

namespace PEqualNP.Outside.L_meta_3566.ReaderNonoutput

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge
open Pruning SingleRead

variable {n : ℕ}

lemma edge_avoiding_vertex (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdeg : ∀ v : Fin n, 2 ≤ G.degree v) (u : Fin n) :
    ∃ v w : Fin n, G.Adj v w ∧ v ≠ u ∧ w ≠ u := by
  classical
  have hpos : 0 < (G.neighborFinset u).card := by
    rw [G.card_neighborFinset_eq_degree]
    have hd := hdeg u
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  have huv := (G.mem_neighborFinset u v).1 hv
  have hvu : v ≠ u := by intro he; subst v; exact G.irrefl huv
  have hnot : ¬ G.neighborFinset v ⊆ {u} := by
    intro hsub
    have hc := Finset.card_le_card hsub
    have hd := hdeg v
    simp only [Finset.card_singleton, G.card_neighborFinset_eq_degree] at hc
    omega
  obtain ⟨w, hw, hwu⟩ := Finset.not_subset.mp hnot
  exact ⟨v, w, (G.mem_neighborFinset v w).1 hw, hvu, by simpa using hwu⟩

lemma primary_reader_not_output (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hdeg : ∀ v : Fin n, 2 ≤ G.degree v) (u : Fin n) (j : ℕ)
    (hj : j < C.size) (hread : u.val ∈ (gateAt C j).inputs) :
    C.output ≠ n + j := by
  intro hout
  have hmem : gateAt C j ∈ C.gates := by
    exact List.mem_of_getElem? (show C.gates[j]? = some (gateAt C j) by
      simp [gateAt, List.getD_eq_getElem?_getD, show j < C.gates.length from hj])
  obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (hao.2.2 _ hmem)
  have hu : u.val = a ∨ u.val = b := by simpa [hin] using hread
  have houtfun (x : Fin n → Bool) : gateVal n C j x = circuitFun n C x := by
    change (C.wires (List.ofFn x)).getD (n + j) false =
      (C.wires (List.ofFn x)).getD C.output false
    rw [hout]
  rcases hao.1 _ hmem with hand | hor
  · obtain ⟨v, w, hvw, hvu, hwu⟩ := edge_avoiding_vertex G hdeg u
    have hfalse : wireVal n C u.val (pairInput v w) = false := by
      rw [wireVal_lt C u.val u.isLt]
      simp [pairInput, Ne.symm hvu, Ne.symm hwu]
    have heq := gate_eq C hao j hj (pairInput v w)
    rw [houtfun, hfun] at heq
    have ht := (graph_pair G v w).2 hvw
    rw [ht] at heq
    rcases hu with hu | hu <;> simp [opnd, hin, hand, isA, opv, ← hu, hfalse] at heq
  · have htrue : wireVal n C u.val (pairInput u u) = true := by
      rw [wireVal_lt C u.val u.isLt]
      simp [pairInput]
    have heq := gate_eq C hao j hj (pairInput u u)
    rw [houtfun, hfun] at heq
    have hf : graphFun G ∅ (pairInput u u) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact G.irrefl ((graph_pair G u u).1 ht)
    rw [hf] at heq
    rcases hu with hu | hu <;> simp [opnd, hin, hor, isA, opv, ← hu, htrue] at heq

end PEqualNP.Outside.L_meta_3566.ReaderNonoutput

namespace PEqualNP.Outside.L_meta_3566.LowReaderFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_3566.Pruning

variable {n : ℕ}

lemma graph_once_reader_one_slot (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (hfour : NoFourCycle G) (hdeg : ∀ u : Fin n, 2 ≤ G.degree u)
    (hsmall : C.size + 1 < 2 * n) :
    ∃ u : Fin n, ∃ j < C.size, (readList C).count u.val = 1 ∧
      u.val ∈ (gateAt C j).inputs ∧ (readList C).count (n + j) = 1 ∧
      ∃ t : ℕ, n ≤ t ∧
        ((gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val]) := by
  obtain ⟨u, j, hj, hu, hread, hslots, t, htn, hin⟩ :=
    graph_once_reader_low_slots G C hC hfour hdeg hsmall
  have hne : ∃ a b, G.Adj a b := by
    obtain ⟨v, hv⟩ := (G.degree_pos_iff_exists_adj u).mp (by have hh := hdeg u; omega)
    exact ⟨u, v, hv⟩
  have hno := ReaderNonoutput.primary_reader_not_output G C hC.1 hC.2.1 hdeg u j hj hread
  obtain ⟨k, hk, _, hr⟩ := least_has_reader G C hC
    (InputReads.output_upper G C hC.2.1 hne) j hj hno
  have hpos := List.count_pos_iff.mpr (reader_mem C j k hk hr)
  exact ⟨u, j, hj, hu, hread, by omega, t, htn, hin⟩

end PEqualNP.Outside.L_meta_3566.LowReaderFrontier


namespace PEqualNP.Outside.L_meta_3566.LeaflessReaderNonoutput

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge
open Pruning SingleRead

variable {n : ℕ}

lemma edge_avoiding_vertex (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdeg : ∀ v : Fin n, 0 < G.degree v → 2 ≤ G.degree v)
    (u : Fin n) (hupos : 0 < G.degree u) :
    ∃ v w : Fin n, G.Adj v w ∧ v ≠ u ∧ w ≠ u := by
  classical
  have hpos : 0 < (G.neighborFinset u).card := by
    rw [G.card_neighborFinset_eq_degree]
    exact hupos
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  have huv := (G.mem_neighborFinset u v).1 hv
  have hvu : v ≠ u := by intro he; subst v; exact G.irrefl huv
  have hnot : ¬ G.neighborFinset v ⊆ {u} := by
    intro hsub
    have hc := Finset.card_le_card hsub
    have hvpos : 0 < G.degree v :=
      (G.degree_pos_iff_exists_adj v).mpr ⟨u, huv.symm⟩
    have hd := hdeg v hvpos
    simp only [Finset.card_singleton, G.card_neighborFinset_eq_degree] at hc
    omega
  obtain ⟨w, hw, hwu⟩ := Finset.not_subset.mp hnot
  exact ⟨v, w, (G.mem_neighborFinset v w).1 hw, hvu, by simpa using hwu⟩

lemma primary_reader_not_output (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hdeg : ∀ v : Fin n, 0 < G.degree v → 2 ≤ G.degree v)
    (u : Fin n) (hupos : 0 < G.degree u) (j : ℕ)
    (hj : j < C.size) (hread : u.val ∈ (gateAt C j).inputs) :
    C.output ≠ n + j := by
  intro hout
  have hmem : gateAt C j ∈ C.gates := by
    exact List.mem_of_getElem? (show C.gates[j]? = some (gateAt C j) by
      simp [gateAt, List.getD_eq_getElem?_getD, show j < C.gates.length from hj])
  obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (hao.2.2 _ hmem)
  have hu : u.val = a ∨ u.val = b := by simpa [hin] using hread
  have houtfun (x : Fin n → Bool) : gateVal n C j x = circuitFun n C x := by
    change (C.wires (List.ofFn x)).getD (n + j) false =
      (C.wires (List.ofFn x)).getD C.output false
    rw [hout]
  rcases hao.1 _ hmem with hand | hor
  · obtain ⟨v, w, hvw, hvu, hwu⟩ := edge_avoiding_vertex G hdeg u hupos
    have hfalse : wireVal n C u.val (pairInput v w) = false := by
      rw [wireVal_lt C u.val u.isLt]
      simp [pairInput, Ne.symm hvu, Ne.symm hwu]
    have heq := gate_eq C hao j hj (pairInput v w)
    rw [houtfun, hfun] at heq
    have ht := (graph_pair G v w).2 hvw
    rw [ht] at heq
    rcases hu with hu | hu <;> simp [opnd, hin, hand, isA, opv, ← hu, hfalse] at heq
  · have htrue : wireVal n C u.val (pairInput u u) = true := by
      rw [wireVal_lt C u.val u.isLt]
      simp [pairInput]
    have heq := gate_eq C hao j hj (pairInput u u)
    rw [houtfun, hfun] at heq
    have hf : graphFun G ∅ (pairInput u u) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact G.irrefl ((graph_pair G u u).1 ht)
    rw [hf] at heq
    rcases hu with hu | hu <;> simp [opnd, hin, hor, isA, opv, ← hu, htrue] at heq

end PEqualNP.Outside.L_meta_3566.LeaflessReaderNonoutput

namespace PEqualNP.Outside.L_meta_3566.ActiveFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open Pruning LowReaderFrontier
open scoped BigOperators

variable {n : ℕ}

lemma charged_subset_budget (n s q : ℕ) (r : ℕ → ℕ) (A : Finset (Fin n))
    (hq : q < s) (htotal : (∑ w ∈ Finset.range (n + s), r w) = 2 * s)
    (hpositive : ∀ u ∈ A, 1 ≤ r u.val)
    (hlive : ∀ j < s, j ≠ q → 1 ≤ r (n + j)) (f : Fin n → ℕ)
    (hvalid : ∀ u ∈ A, r u.val = 1 → f u < s)
    (hinj : ∀ u ∈ A, ∀ v ∈ A, r u.val = 1 → r v.val = 1 → f u = f v → u = v)
    (hcharge : ∀ u ∈ A, r u.val = 1 → 2 ≤ r (n + f u)) :
    2 * A.card ≤ s + 1 := by
  classical
  let S := A.filter (fun u => r u.val = 1)
  let J := S.image f
  have hJsub : J ⊆ Finset.range s := by
    intro j hj
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨huA, huone⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_range.mpr (hvalid u huA huone)
  have hJcard : J.card = S.card := by
    apply Finset.card_image_iff.mpr
    intro u hu v hv he
    obtain ⟨huA, huone⟩ := Finset.mem_filter.mp hu
    obtain ⟨hvA, hvone⟩ := Finset.mem_filter.mp hv
    exact hinj u huA v hvA huone hvone he
  have hinputs : 2 * A.card ≤ (∑ u : Fin n, r u.val) + S.card := by
    have hp : ∀ u ∈ A, 2 ≤ r u.val + if u ∈ S then 1 else 0 := by
      intro u huA
      by_cases hu : u ∈ S
      · have hc := (Finset.mem_filter.mp hu).2
        simp only [hu, ite_true]
        omega
      · have hc : r u.val ≠ 1 := by
          intro he
          exact hu (Finset.mem_filter.mpr ⟨huA, he⟩)
        have hpos := hpositive u huA
        simp only [hu, ite_false]
        omega
    have hs := Finset.sum_le_sum hp
    have hinter : A ∩ S = S := Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
    have hs' : 2 * A.card ≤ (∑ u ∈ A, r u.val) + S.card := by
      simpa [Finset.sum_add_distrib, Finset.sum_ite_mem, hinter, Nat.mul_comm] using hs
    have hsub : (∑ u ∈ A, r u.val) ≤ ∑ u : Fin n, r u.val :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A) (fun _ _ _ => Nat.zero_le _)
    omega
  have hinternal : s + J.card ≤ (∑ j ∈ Finset.range s, r (n + j)) + 1 := by
    have hp : ∀ j ∈ Finset.range s,
        1 + (if j ∈ J then 1 else 0) ≤ r (n + j) + if j = q then 1 else 0 := by
      intro j hj
      by_cases hJ : j ∈ J
      · obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hJ
        obtain ⟨huA, huone⟩ := Finset.mem_filter.mp hu
        have hc := hcharge u huA huone
        rw [he] at hc
        split_ifs <;> omega
      · by_cases he : j = q
        · subst j
          simp [hJ]
        · have hc := hlive j (Finset.mem_range.mp hj) he
          simp only [hJ, he, ite_false]
          omega
    have hs := Finset.sum_le_sum hp
    have hinter : Finset.range s ∩ J = J := Finset.inter_eq_right.mpr hJsub
    simpa [Finset.sum_add_distrib, Finset.sum_ite_mem, hinter, Finset.mem_range.mpr hq] using hs
  rw [hJcard] at hinternal
  rw [Fin.sum_univ_eq_sum_range] at hinputs
  rw [Finset.sum_range_add] at htotal
  omega

lemma least_subset_once_low_slots (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (ho : n ≤ C.output) (hupper : C.output < n + C.size)
    (A : Finset (Fin n)) (hpositive : ∀ u ∈ A, 1 ≤ (readList C).count u.val)
    (f : Fin n → ℕ)
    (hvalid : ∀ u ∈ A, (readList C).count u.val = 1 → f u < C.size)
    (hinj : ∀ u ∈ A, ∀ v ∈ A, (readList C).count u.val = 1 →
      (readList C).count v.val = 1 → f u = f v → u = v)
    (hsmall : C.size + 1 < 2 * A.card) :
    ∃ u ∈ A, (readList C).count u.val = 1 ∧ (readList C).count (n + f u) ≤ 1 := by
  classical
  by_contra hn
  push Not at hn
  let q := C.output - n
  have hq : q < C.size := by dsimp [q]; omega
  have htotal : (∑ w ∈ Finset.range (n + C.size), (readList C).count w) = 2 * C.size := by
    have hsum : (∑ w ∈ Finset.range (n + C.size), ((readList C) : Multiset ℕ).count w) =
        (readList C).length := by
      apply Multiset.sum_count_eq_card
      intro w hw
      exact Finset.mem_range.mpr (readList_bound C hC.1 w hw)
    simpa [readList_length C hC.1] using hsum
  have hb := charged_subset_budget n C.size q ((readList C).count) A hq htotal hpositive
    (fun j hj hjq => ?_) f hvalid hinj (fun u huA hu => by have hh := hn u huA hu; omega)
  · omega
  · have hjo : C.output ≠ n + j := by intro he; apply hjq; dsimp [q]; omega
    obtain ⟨k, hk, _, hr⟩ := least_has_reader G C hC hupper j hj hjo
    exact List.count_pos_iff.mpr (reader_mem C j k hk hr)

lemma subset_sole_reader_map (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hfour : NoFourCycle G) (A : Finset (Fin n)) (hdeg : ∀ u ∈ A, 2 ≤ G.degree u) :
    ∃ f : Fin n → ℕ,
      (∀ u ∈ A, (readList C).count u.val = 1 → f u < C.size ∧
        ∃ t : ℕ, n ≤ t ∧
          ((gateAt C (f u)).inputs = [u.val, t] ∨ (gateAt C (f u)).inputs = [t, u.val])) ∧
      (∀ u ∈ A, ∀ v ∈ A, (readList C).count u.val = 1 →
        (readList C).count v.val = 1 → f u = f v → u = v) := by
  classical
  have hex : ∀ u : Fin n, ∃ j : ℕ, u ∈ A → (readList C).count u.val = 1 →
      j < C.size ∧ ∃ t : ℕ, n ≤ t ∧
        ((gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val]) := by
    intro u
    by_cases huA : u ∈ A
    · by_cases hu : (readList C).count u.val = 1
      · obtain ⟨j, hj, t, ht, hin⟩ :=
          single_reader_index_internal G C hao hfun hfour u (hdeg u huA) hu
        exact ⟨j, fun _ _ => ⟨hj, t, ht, hin⟩⟩
      · exact ⟨0, fun _ h => False.elim (hu h)⟩
    · exact ⟨0, fun h _ => False.elim (huA h)⟩
  choose f hf using hex
  refine ⟨f, hf, ?_⟩
  intro u huA v hvA hu hv he
  obtain ⟨_, t, htn, hin⟩ := hf u huA hu
  obtain ⟨_, t', _, hin'⟩ := hf v hvA hv
  have hvmem : v.val ∈ (gateAt C (f u)).inputs := by
    rw [he]
    rcases hin' with h | h <;> simp [h]
  have hvut : v.val = u.val ∨ v.val = t := by
    rcases hin with h | h
    · simpa [h] using hvmem
    · simpa [h, or_comm] using hvmem
  have hne : v.val ≠ t := by have hvn := v.isLt; omega
  exact Fin.ext ((hvut.resolve_right hne).symm)

lemma active_once_reader_low_slots (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hfour : NoFourCycle G)
    (hdeg : ∀ u : Fin n, 0 < G.degree u → 2 ≤ G.degree u)
    (hsmall : C.size + 1 < 2 * (Subcubic.active G).card) :
    ∃ u ∈ Subcubic.active G, ∃ j < C.size, (readList C).count u.val = 1 ∧
      u.val ∈ (gateAt C j).inputs ∧ (readList C).count (n + j) ≤ 1 ∧
      ∃ t : ℕ, n ≤ t ∧
        ((gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val]) := by
  classical
  have hmem : ∀ u : Fin n, u ∈ Subcubic.active G ↔ 0 < G.degree u := by
    intro u
    simp [Subcubic.active]
  have hne : ∃ u v, G.Adj u v := by
    have hcard : 0 < (Subcubic.active G).card := by omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hcard
    obtain ⟨v, hv⟩ := (G.degree_pos_iff_exists_adj u).mp ((hmem u).mp hu)
    exact ⟨u, v, hv⟩
  have hpositive : ∀ u ∈ Subcubic.active G, 1 ≤ (readList C).count u.val := by
    intro u hu
    apply List.count_pos_iff.mpr
    apply InputReads.nonisolated_read G C hC.1 hC.2.1 u
    exact (G.degree_pos_iff_exists_adj u).mp ((hmem u).mp hu)
  obtain ⟨f, hf, hinj⟩ := subset_sole_reader_map G C hC.1 hC.2.1 hfour
    (Subcubic.active G) (fun u hu => hdeg u ((hmem u).mp hu))
  obtain ⟨u, huA, hu, hslots⟩ := least_subset_once_low_slots G C hC
    (InputReads.output_lower G C hC.2.1) (InputReads.output_upper G C hC.2.1 hne)
    (Subcubic.active G) hpositive f (fun u huA hu => (hf u huA hu).1) hinj hsmall
  obtain ⟨hj, t, htn, hin⟩ := hf u huA hu
  have hread : u.val ∈ (gateAt C (f u)).inputs := by
    rcases hin with h | h <;> simp [h]
  exact ⟨u, huA, f u, hj, hu, hread, hslots, t, htn, hin⟩

lemma active_once_reader_one_slot (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hfour : NoFourCycle G)
    (hdeg : ∀ u : Fin n, 0 < G.degree u → 2 ≤ G.degree u)
    (hsmall : C.size + 1 < 2 * (Subcubic.active G).card) :
    ∃ u ∈ Subcubic.active G, ∃ j < C.size, (readList C).count u.val = 1 ∧
      u.val ∈ (gateAt C j).inputs ∧ (readList C).count (n + j) = 1 ∧
      ∃ t : ℕ, n ≤ t ∧
        ((gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val]) := by
  obtain ⟨u, huA, j, hj, hu, hread, hslots, t, htn, hin⟩ :=
    active_once_reader_low_slots G C hC hfour hdeg hsmall
  have hupos : 0 < G.degree u := by simpa [Subcubic.active] using huA
  have hne : ∃ a b, G.Adj a b := by
    obtain ⟨v, hv⟩ := (G.degree_pos_iff_exists_adj u).mp hupos
    exact ⟨u, v, hv⟩
  have hno := LeaflessReaderNonoutput.primary_reader_not_output G C hC.1 hC.2.1
    hdeg u hupos j hj hread
  obtain ⟨k, hk, _, hr⟩ := least_has_reader G C hC
    (InputReads.output_upper G C hC.2.1 hne) j hj hno
  have hpos := List.count_pos_iff.mpr (reader_mem C j k hk hr)
  exact ⟨u, huA, j, hj, hu, hread, by omega, t, htn, hin⟩

lemma subcubic_lower_or_one_slot_frontier (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hb : ∃ c : Fin n → Bool, ∀ u v, G.Adj u v → c u ≠ c v)
    (hfour : NoFourCycle G) (hupper : ∀ u : Fin n, G.degree u ≤ 3)
    (hlower : ∀ u : Fin n, 0 < G.degree u → 2 ≤ G.degree u)
    (C : Circuit) (hC : IsLeastAO G C) :
    (∃ T : Finset (Fin n), CoverPromise.IsVertexCover G T ∧
      G.edgeFinset.card + T.card ≤ C.size + 1) ∨
    (∃ u ∈ Subcubic.active G, ∃ j < C.size, (readList C).count u.val = 1 ∧
      u.val ∈ (gateAt C j).inputs ∧ (readList C).count (n + j) = 1 ∧
      ∃ t : ℕ, n ≤ t ∧
        ((gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])) := by
  by_cases hsmall : C.size + 1 < 2 * (Subcubic.active G).card
  · exact Or.inr (active_once_reader_one_slot G C hC hfour hlower hsmall)
  · obtain ⟨T, hT, hbound⟩ := Subcubic.subcubic_cover G hb hupper
    exact Or.inl ⟨T, hT, by omega⟩

end PEqualNP.Outside.L_meta_3566.ActiveFrontier


namespace PEqualNP.Outside.L_meta_3566.OneSlotSuccessor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open Pruning LowReaderFrontier
open scoped BigOperators

variable {n : ℕ}

lemma one_read_unique_index (C : Circuit) (w : ℕ)
    (hcount : (readList C).count w = 1) (j k : ℕ)
    (hj : j < C.size) (hk : k < C.size)
    (hjr : w ∈ (gateAt C j).inputs) (hkr : w ∈ (gateAt C k).inputs) : j = k := by
  classical
  by_contra hne
  have hsub : ({j, k} : Finset ℕ) ⊆ Finset.range C.size := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Finset.mem_range.mpr hj
    · exact Finset.mem_range.mpr hk
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun (i : ℕ) (_ : i ∈ Finset.range C.size) (_ : i ∉ ({j, k} : Finset ℕ)) =>
      Nat.zero_le ((gateAt C i).inputs.count w))
  have hpj := List.count_pos_iff.mpr hjr
  have hpk := List.count_pos_iff.mpr hkr
  rw [← readList_count_sum C w, hcount] at hs
  simp only [Finset.sum_pair hne] at hs
  omega

lemma one_read_gate_count (C : Circuit) (w : ℕ)
    (hcount : (readList C).count w = 1) (j : ℕ)
    (hj : j < C.size) (hread : w ∈ (gateAt C j).inputs) :
    (gateAt C j).inputs.count w = 1 := by
  have hle : (gateAt C j).inputs.count w ≤
      ∑ i ∈ Finset.range C.size, (gateAt C i).inputs.count w :=
    Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count w))
      (Finset.mem_range.mpr hj)
  rw [← readList_count_sum C w, hcount] at hle
  have hpos := List.count_pos_iff.mpr hread
  omega

lemma one_slot_successor (C : Circuit) (hao : IsAO2 n C) (j : ℕ)
    (hcount : (readList C).count (n + j) = 1) :
    ∃ k < C.size, j < k ∧ ∃ t : ℕ, t ≠ n + j ∧
      ((gateAt C k).inputs = [n + j, t] ∨ (gateAt C k).inputs = [t, n + j]) ∧
      (∀ i < C.size, i ≠ k → n + j ∉ (gateAt C i).inputs) := by
  have hmem : n + j ∈ readList C := List.count_pos_iff.mp (by omega)
  obtain ⟨g, hg, hgin⟩ := List.mem_flatMap.mp hmem
  obtain ⟨pre, post, hshape⟩ := List.mem_iff_append.mp hg
  let k := pre.length
  have hk : k < C.size := by
    change pre.length < C.gates.length
    rw [hshape, List.length_append, List.length_cons]
    omega
  have hgate : gateAt C k = g := by
    simp [gateAt, k, hshape, List.getD_eq_getElem?_getD]
  have hread : n + j ∈ (gateAt C k).inputs := by simpa [hgate] using hgin
  have hjk : j < k := by
    have hh := hao.2.1 k hk (n + j) hread
    omega
  have hc := one_read_gate_count C (n + j) hcount k hk hread
  obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (hao.2.2 g hg)
  have huab : n + j = a ∨ n + j = b := by simpa [hin] using hgin
  have hab : a ≠ b := by
    intro heq
    subst b
    have hua : n + j = a := huab.elim id id
    simp [hgate, hin, ← hua] at hc
  have hno : ∀ i < C.size, i ≠ k → n + j ∉ (gateAt C i).inputs := by
    intro i hi hne hir
    exact hne (one_read_unique_index C (n + j) hcount i k hi hk hir hread)
  rcases huab with hua | hub
  · refine ⟨k, hk, hjk, b, ?_, Or.inl ?_, hno⟩
    · intro he
      exact hab (hua.symm.trans he.symm)
    · simpa [hgate, hua] using hin
  · refine ⟨k, hk, hjk, a, ?_, Or.inr ?_, hno⟩
    · intro he
      exact hab (he.trans hub)
    · simpa [hgate, hub] using hin

end PEqualNP.Outside.L_meta_3566.OneSlotSuccessor


namespace PEqualNP.Outside.L_meta_3566.ANDRotationEvaluation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge
open Pruning

variable {n : ℕ}

lemma gate_eq_eval (C : Circuit) (hao : IsAO2 n C) (j : ℕ)
    (hj : j < C.size) (x : Fin n → Bool) :
    gateVal n C j x = (gateAt C j).op.eval
      ((gateAt C j).inputs.map (fun w => wireVal n C w x)) := by
  have hmem : gateAt C j ∈ C.gates := by
    exact List.mem_of_getElem? (show C.gates[j]? = some (gateAt C j) by
      simp [gateAt, List.getD_eq_getElem?_getD, show j < C.gates.length from hj])
  obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (hao.2.2 _ hmem)
  have heq := gate_eq C hao j hj x
  rcases hao.1 _ hmem with hand | hor
  · simpa [opnd, hin, hand, isA, opv, GateOp.eval] using heq
  · simpa [opnd, hin, hor, isA, opv, GateOp.eval] using heq

lemma wireVal_eq_of_solution (C : Circuit) (hao : IsAO2 n C)
    (x : Fin n → Bool) (V : ℕ → Bool)
    (hinput : ∀ i : Fin n, V i.val = x i)
    (hgate : ∀ j < C.size,
      V (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map V)) :
    ∀ w < n + C.size, wireVal n C w x = V w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hin : w < n
    · rw [wireVal_lt C w hin]
      exact (hinput ⟨w, hin⟩).symm
    · let j := w - n
      have hwj : n + j = w := by dsimp [j]; omega
      have hj : j < C.size := by dsimp [j]; omega
      rw [← hwj]
      change gateVal n C j x = V (n + j)
      rw [gate_eq_eval C hao j hj x, hgate j hj]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hib := hao.2.1 j hj i hi
      apply ih i
      · omega
      · omega

end PEqualNP.Outside.L_meta_3566.ANDRotationEvaluation

namespace PEqualNP.Outside.L_meta_3566.AndRotation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3566.Pruning

variable {n : ℕ}

def perm (j k i : ℕ) : ℕ :=
  if i = j then k - 1 else if j < i ∧ i < k then i - 1 else i

def inv (j k i : ℕ) : ℕ :=
  if i = k - 1 then j else if j ≤ i ∧ i < k - 1 then i + 1 else i

lemma inv_perm (j k i : ℕ) (hjk : j < k) : inv j k (perm j k i) = i := by
  unfold inv perm
  split_ifs <;> omega

lemma perm_inv (j k i : ℕ) (hjk : j < k) : perm j k (inv j k i) = i := by
  unfold inv perm
  split_ifs <;> omega

lemma perm_lt (j k s i : ℕ) (hjk : j < k) (hks : k < s) (hi : i < s) : perm j k i < s := by
  unfold perm
  split_ifs <;> omega

lemma inv_lt (j k s i : ℕ) (hjk : j < k) (hks : k < s) (hi : i < s) : inv j k i < s := by
  unfold inv
  split_ifs <;> omega

lemma perm_injective (j k : ℕ) (hjk : j < k) : Function.Injective (perm j k) := by
  intro a b he
  have hh := congrArg (inv j k) he
  simpa [inv_perm j k a hjk, inv_perm j k b hjk] using hh

lemma perm_j (j k : ℕ) : perm j k j = k - 1 := by simp [perm]
lemma perm_k (j k : ℕ) (hjk : j < k) : perm j k k = k := by simp [perm, Nat.ne_of_gt hjk]

def rename (n j k w : ℕ) : ℕ :=
  if w < n then w else n + perm j k (w - n)

lemma rename_input (j k : ℕ) (u : Fin n) : rename n j k u.val = u.val := by
  simp [rename, u.isLt]

lemma rename_gate (n j k i : ℕ) : rename n j k (n + i) = n + perm j k i := by
  simp [rename]

lemma rename_bound (n j k s w : ℕ) (hjk : j < k) (hks : k < s) (hw : w < n + s) :
    rename n j k w < n + s := by
  unfold rename
  split_ifs with hwn
  · omega
  · have hi : w - n < s := by omega
    have hh := perm_lt j k s (w - n) hjk hks hi
    omega

lemma rename_before_rotated (n j k w : ℕ) (hjk : j < k)
    (hw : w < n + k) (hne : w ≠ n + j) :
    rename n j k w < n + (k - 1) := by
  unfold rename perm
  split_ifs <;> omega

lemma rename_before_perm (n j k i w : ℕ) (hjk : j < k)
    (hij : i ≠ j) (hw : w < n + i) (hne : w ≠ n + j) :
    rename n j k w < n + perm j k i := by
  unfold rename perm
  split_ifs <;> omega

def newGate (C : Circuit) (u : Fin n) (j k t r i : ℕ) : Gate :=
  if i = k - 1 then ⟨GateOp.and, [rename n j k t, rename n j k r]⟩
  else if i = k then ⟨GateOp.and, [u.val, n + (k - 1)]⟩
  else let g := gateAt C (inv j k i)
    ⟨g.op, g.inputs.map (rename n j k)⟩

def rotate (C : Circuit) (u : Fin n) (j k t r : ℕ) : Circuit :=
  ⟨List.ofFn (fun i : Fin C.size => newGate C u j k t r i.val), rename n j k C.output⟩

lemma rotate_size (C : Circuit) (u : Fin n) (j k t r : ℕ) :
    (rotate C u j k t r).size = C.size := by simp [rotate, Circuit.size]

lemma rotate_gateAt (C : Circuit) (u : Fin n) (j k t r i : ℕ) (hi : i < C.size) :
    gateAt (rotate C u j k t r) i = newGate C u j k t r i := by
  simp [rotate, gateAt, List.getD_eq_getElem?_getD, hi]

lemma old_gate_mem (C : Circuit) (i : ℕ) (hi : i < C.size) : gateAt C i ∈ C.gates := by
  exact List.mem_of_getElem? (show C.gates[i]? = some (gateAt C i) by
    simp [gateAt, List.getD_eq_getElem?_getD, show i < C.gates.length from hi])

lemma rotate_ao (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t r : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (ht : t < n + j) (hr : r < n + k) (hrne : r ≠ n + j)
    (honly : ∀ i < C.size, i ≠ k → n + j ∉ (gateAt C i).inputs) :
    IsAO2 n (rotate C u j k t r) := by
  have hnGate (i : ℕ) (hi : i < C.size) :
      (newGate C u j k t r i).op = GateOp.and ∨
      (newGate C u j k t r i).op = GateOp.or := by
    unfold newGate
    split_ifs
    · exact Or.inl rfl
    · exact Or.inl rfl
    · change (gateAt C (inv j k i)).op = GateOp.and ∨ (gateAt C (inv j k i)).op = GateOp.or
      exact hao.1 _ (old_gate_mem C _ (inv_lt j k C.size i hjk hk hi))
  have hnLen (i : ℕ) (hi : i < C.size) : (newGate C u j k t r i).inputs.length = 2 := by
    unfold newGate
    split_ifs
    · rfl
    · rfl
    · simpa using hao.2.2 _ (old_gate_mem C _ (inv_lt j k C.size i hjk hk hi))
  have hnBack (i : ℕ) (hi : i < C.size) (w : ℕ)
      (hw : w ∈ (newGate C u j k t r i).inputs) : w < n + i := by
    unfold newGate at hw
    split_ifs at hw with hi0 hi1
    · have hwt : t ≠ n + j := by omega
      have htt : t < n + k := by omega
      have htb := rename_before_rotated n j k t hjk htt hwt
      have hrb := rename_before_rotated n j k r hjk hr hrne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · have hu := u.isLt
        omega
      · omega
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      let q := inv j k i
      have hq : q < C.size := inv_lt j k C.size i hjk hk hi
      have hqj : q ≠ j := by
        intro he
        have hh := perm_inv j k i hjk
        change perm j k q = i at hh
        rw [he, perm_j] at hh
        exact hi0 hh.symm
      have hqk : q ≠ k := by
        intro he
        have hh := perm_inv j k i hjk
        change perm j k q = i at hh
        rw [he, perm_k j k hjk] at hh
        exact hi1 hh.symm
      have hvq : v < n + q := hao.2.1 q hq v hv
      have hvj : v ≠ n + j := by intro he; exact honly q hq hqk (he ▸ hv)
      have hh := rename_before_perm n j k q v hjk hqj hvq hvj
      simpa only [q, perm_inv j k i hjk] using hh
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact hnGate i.val i.isLt
  · intro i hi w hw
    change i < (rotate C u j k t r).size at hi
    rw [rotate_size] at hi
    change w ∈ (gateAt (rotate C u j k t r) i).inputs at hw
    rw [rotate_gateAt C u j k t r i hi] at hw
    exact hnBack i hi w hw
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact hnLen i.val i.isLt

end PEqualNP.Outside.L_meta_3566.AndRotation

namespace PEqualNP.Outside.L_meta_3566.AndRotation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3566.Pruning
open PEqualNP.Outside.L_meta_3566.ANDRotationEvaluation

variable {n : ℕ}

def unrename (n j k w : ℕ) : ℕ :=
  if w < n then w else n + inv j k (w - n)

lemma unrename_rename (n j k w : ℕ) (hjk : j < k) :
    unrename n j k (rename n j k w) = w := by
  by_cases hw : w < n
  · simp [rename, unrename, hw]
  · simp only [rename, hw, ite_false]
    simp only [unrename, Nat.not_lt.mpr (Nat.le_add_right _ _), ite_false, Nat.add_sub_cancel_left]
    rw [inv_perm j k (w - n) hjk]
    omega

lemma rename_eq_new_j (n j k w : ℕ) (hjk : j < k) :
    rename n j k w = n + (k - 1) ↔ w = n + j := by
  constructor
  · intro he
    have hh := congrArg (unrename n j k) he
    rw [unrename_rename n j k w hjk] at hh
    simpa [unrename, inv] using hh
  · rintro rfl
    rw [rename_gate, perm_j]

def values (C : Circuit) (j k t r : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  if w = n + (k - 1) then wireVal n C t x && wireVal n C r x
  else wireVal n C (unrename n j k w) x

lemma values_rename (C : Circuit) (j k t r w : ℕ) (hjk : j < k) (x : Fin n → Bool) :
    values C j k t r x (rename n j k w) =
      if w = n + j then wireVal n C t x && wireVal n C r x else wireVal n C w x := by
  unfold values
  simp only [rename_eq_new_j n j k w hjk, unrename_rename n j k w hjk]

lemma values_input (C : Circuit) (j k t r : ℕ) (hjk : j < k)
    (x : Fin n → Bool) (u : Fin n) : values C j k t r x u.val = x u := by
  have hu : u.val ≠ n + j := by have hh := u.isLt; omega
  have hh := values_rename C j k t r u.val hjk x
  rw [rename_input, ite_eq_right hu, wireVal_lt C u.val u.isLt] at hh
  exact hh

lemma values_new_j (C : Circuit) (j k t r : ℕ) (x : Fin n → Bool) :
    values C j k t r x (n + (k - 1)) = (wireVal n C t x && wireVal n C r x) := by
  simp [values]

lemma values_new_k (C : Circuit) (j k t r : ℕ) (hjk : j < k) (x : Fin n → Bool) :
    values C j k t r x (n + k) = gateVal n C k x := by
  have hkj : n + k ≠ n + j := by omega
  have hh := values_rename C j k t r (n + k) hjk x
  rw [rename_gate, perm_k j k hjk, ite_eq_right hkj] at hh
  exact hh

lemma and_gate_value (C : Circuit) (hao : IsAO2 n C) (i a b : ℕ)
    (hi : i < C.size) (hop : (gateAt C i).op = GateOp.and)
    (hin : (gateAt C i).inputs = [a, b] ∨ (gateAt C i).inputs = [b, a])
    (x : Fin n → Bool) :
    gateVal n C i x = (wireVal n C a x && wireVal n C b x) := by
  rw [gate_eq_eval C hao i hi x]
  rcases hin with hin | hin <;> simp [hop, hin, GateOp.eval, Bool.and_comm]

lemma values_solution (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t r : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.and)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, r] ∨ (gateAt C k).inputs = [r, n + j])
    (ht : t < n + j) (hrne : r ≠ n + j)
    (honly : ∀ i < C.size, i ≠ k → n + j ∉ (gateAt C i).inputs)
    (x : Fin n → Bool) :
    ∀ i < C.size, values C j k t r x (n + i) =
      (newGate C u j k t r i).op.eval
        ((newGate C u j k t r i).inputs.map (values C j k t r x)) := by
  intro i hi
  by_cases hi0 : i = k - 1
  · subst i
    have htn : t ≠ n + j := by omega
    simp [newGate, values_new_j, values_rename C j k t r t hjk x,
      values_rename C j k t r r hjk x, htn, hrne, GateOp.eval]
  · by_cases hi1 : i = k
    · subst i
      have hk0 : k ≠ k - 1 := by omega
      have hj : j < C.size := by omega
      have hvg := and_gate_value C hao j u.val t hj hjop hjinputs x
      have hvk := and_gate_value C hao k (n + j) r hk hkop hkinputs x
      change gateVal n C k x = (gateVal n C j x && wireVal n C r x) at hvk
      rw [hvg, wireVal_lt C u.val u.isLt] at hvk
      simp only [newGate, hk0, ite_false, ite_true, List.map_cons, List.map_nil,
        GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
        values_new_k C j k t r hjk x, values_new_j, values_input C j k t r hjk x u]
      simpa only [Bool.and_assoc] using hvk
    · let q := inv j k i
      have hq : q < C.size := inv_lt j k C.size i hjk hk hi
      have hqk : q ≠ k := by
        intro he
        have hh := perm_inv j k i hjk
        change perm j k q = i at hh
        rw [he, perm_k j k hjk] at hh
        exact hi1 hh.symm
      have hvi : values C j k t r x (n + i) = gateVal n C q x := by
        have hi0' : n + i ≠ n + (k - 1) := by omega
        simp only [values, hi0', ite_false, unrename,
          Nat.not_lt.mpr (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
        rfl
      have hm : (gateAt C q).inputs.map (fun w => values C j k t r x (rename n j k w)) =
          (gateAt C q).inputs.map (fun w => wireVal n C w x) := by
        apply List.map_congr_left
        intro w hw
        have hwn : w ≠ n + j := by intro he; exact honly q hq hqk (he ▸ hw)
        rw [values_rename C j k t r w hjk x, ite_eq_right hwn]
      rw [hvi]
      simp only [newGate, hi0, hi1, ite_false, List.map_map]
      change gateVal n C q x = (gateAt C q).op.eval
        ((gateAt C q).inputs.map (fun w => values C j k t r x (rename n j k w)))
      rw [hm]
      exact gate_eq_eval C hao q hq x

lemma rotate_wire_values (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t r : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.and)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, r] ∨ (gateAt C k).inputs = [r, n + j])
    (ht : t < n + j) (hr : r < n + k) (hrne : r ≠ n + j)
    (honly : ∀ i < C.size, i ≠ k → n + j ∉ (gateAt C i).inputs)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n + C.size) :
    wireVal n (rotate C u j k t r) (rename n j k w) x =
      if w = n + j then wireVal n C t x && wireVal n C r x else wireVal n C w x := by
  have hnew := rotate_ao C hao u j k t r hjk hk ht hr hrne honly
  have hsol : ∀ i < (rotate C u j k t r).size,
      values C j k t r x (n + i) =
        (gateAt (rotate C u j k t r) i).op.eval
          ((gateAt (rotate C u j k t r) i).inputs.map (values C j k t r x)) := by
    intro i hi
    rw [rotate_size] at hi
    rw [rotate_gateAt C u j k t r i hi]
    exact values_solution C hao u j k t r hjk hk hjop hjinputs hkop hkinputs ht hrne honly x i hi
  have hh := wireVal_eq_of_solution (rotate C u j k t r) hnew x (values C j k t r x)
    (values_input C j k t r hjk x) hsol (rename n j k w)
    (by rw [rotate_size]; exact rename_bound n j k C.size w hjk hk hw)
  rw [values_rename C j k t r w hjk x] at hh
  exact hh

lemma rotate_circuitFun (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t r : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.and)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, r] ∨ (gateAt C k).inputs = [r, n + j])
    (ht : t < n + j) (hr : r < n + k) (hrne : r ≠ n + j)
    (honly : ∀ i < C.size, i ≠ k → n + j ∉ (gateAt C i).inputs)
    (hout : C.output < n + C.size) (houtj : C.output ≠ n + j) :
    circuitFun n (rotate C u j k t r) = circuitFun n C := by
  funext x
  have hh := rotate_wire_values C hao u j k t r hjk hk hjop hjinputs hkop hkinputs
    ht hr hrne honly x C.output hout
  rw [ite_eq_right houtj] at hh
  exact hh

end PEqualNP.Outside.L_meta_3566.AndRotation

namespace PEqualNP.Outside.L_meta_3566.AndRotationCounts

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open Pruning AndRotation LowReaderFrontier
open scoped BigOperators

variable {n : ℕ}

lemma rename_injective (n j k : ℕ) (hjk : j < k) :
    Function.Injective (rename n j k) := by
  intro a b he
  have hh := congrArg (unrename n j k) he
  simpa only [unrename_rename n j k a hjk, unrename_rename n j k b hjk] using hh

lemma sum_perm (j k s : ℕ) (hjk : j < k) (hk : k < s) (f : ℕ → ℕ) :
    (∑ i ∈ Finset.range s, f i) = ∑ i ∈ Finset.range s, f (perm j k i) := by
  apply Finset.sum_bij (fun i _ => inv j k i)
  · intro i hi
    exact Finset.mem_range.mpr (inv_lt j k s i hjk hk (Finset.mem_range.mp hi))
  · intro i hi z hz he
    have hh := congrArg (perm j k) he
    simpa only [perm_inv j k i hjk, perm_inv j k z hjk] using hh
  · intro i hi
    exact ⟨perm j k i,
      Finset.mem_range.mpr (perm_lt j k s i hjk hk (Finset.mem_range.mp hi)),
      inv_perm j k i hjk⟩
  · intro i hi
    rw [perm_inv j k i hjk]

lemma sum_eq_of_pair (S : Finset ℕ) (j k : ℕ) (hj : j ∈ S) (hk : k ∈ S) (hjk : j ≠ k)
    (f g : ℕ → ℕ)
    (hrest : ∀ i ∈ S, i ≠ j → i ≠ k → f i = g i)
    (hpair : f j + f k = g j + g k) :
    (∑ i ∈ S, f i) = ∑ i ∈ S, g i := by
  have hk' : k ∈ S.erase j := Finset.mem_erase.mpr ⟨hjk.symm, hk⟩
  have hf := Finset.sum_erase_add S f hj
  have hg := Finset.sum_erase_add S g hj
  have hfk := Finset.sum_erase_add (S.erase j) f hk'
  have hgk := Finset.sum_erase_add (S.erase j) g hk'
  have hmiddle : (∑ i ∈ (S.erase j).erase k, f i) = ∑ i ∈ (S.erase j).erase k, g i := by
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hik, hi'⟩ := Finset.mem_erase.mp hi
    obtain ⟨hij, hiS⟩ := Finset.mem_erase.mp hi'
    exact hrest i hiS hij hik
  omega

lemma rotate_readList_count (C : Circuit) (u : Fin n) (j k t r : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkinputs : (gateAt C k).inputs = [n + j, r] ∨ (gateAt C k).inputs = [r, n + j])
    (w : ℕ) :
    (readList (rotate C u j k t r)).count (rename n j k w) = (readList C).count w := by
  classical
  let f : ℕ → ℕ := fun i => (newGate C u j k t r i).inputs.count (rename n j k w)
  let g : ℕ → ℕ := fun i => (gateAt C i).inputs.count w
  have hleft : (readList (rotate C u j k t r)).count (rename n j k w) =
      ∑ i ∈ Finset.range C.size, f i := by
    rw [readList_count_sum, rotate_size]
    apply Finset.sum_congr rfl
    intro i hi
    rw [rotate_gateAt C u j k t r i (Finset.mem_range.mp hi)]
  rw [hleft, sum_perm j k C.size hjk hk f, readList_count_sum]
  apply sum_eq_of_pair (Finset.range C.size) j k
    (Finset.mem_range.mpr (by omega)) (Finset.mem_range.mpr hk) (Nat.ne_of_lt hjk)
      (fun i => f (perm j k i)) g
  · intro i hi hij hik
    have hpi0 : perm j k i ≠ k - 1 := by
      intro he
      exact hij (AndRotation.perm_injective j k hjk (he.trans (perm_j j k).symm))
    have hpi1 : perm j k i ≠ k := by
      intro he
      exact hik (AndRotation.perm_injective j k hjk (he.trans (perm_k j k hjk).symm))
    simp only [f, g, newGate, hpi0, hpi1, ite_false, inv_perm j k i hjk]
    exact List.count_map_of_injective _ _ (rename_injective n j k hjk) w
  · have hk0 : k ≠ k - 1 := by omega
    have hmap (l : List ℕ) : (l.map (rename n j k)).count (rename n j k w) = l.count w :=
      List.count_map_of_injective l _ (rename_injective n j k hjk) w
    have hjnew : f (perm j k j) = ([t, r].map (rename n j k)).count (rename n j k w) := by
      simp [f, newGate, perm_j]
    have hknew : f (perm j k k) = ([u.val, n + j].map (rename n j k)).count (rename n j k w) := by
      simp [f, newGate, perm_k j k hjk, hk0, rename_input, rename_gate, perm_j]
    rw [hjnew, hknew, hmap, hmap]
    rcases hjinputs with hjinputs | hjinputs <;>
      rcases hkinputs with hkinputs | hkinputs <;>
      simp [g, hjinputs, hkinputs, List.count_cons, Nat.add_comm, Nat.add_left_comm]

lemma rotate_input_count (C : Circuit) (u v : Fin n) (j k t r : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkinputs : (gateAt C k).inputs = [n + j, r] ∨ (gateAt C k).inputs = [r, n + j]) :
    (readList (rotate C u j k t r)).count v.val = (readList C).count v.val := by
  have hh := rotate_readList_count C u j k t r hjk hk hjinputs hkinputs v.val
  simpa only [rename_input] using hh

end PEqualNP.Outside.L_meta_3566.AndRotationCounts

namespace PEqualNP.Outside.L_meta_3566.PrivateSuccessorSingleton

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open Pruning ANDRotationEvaluation

variable {n : ℕ}

lemma prefix_wire_singleton_false (C : Circuit) (hao : IsAO2 n C)
    (u : Fin n) (j k : ℕ) (hk : k ≤ C.size)
    (hsole : ∀ i < C.size, i ≠ j → u.val ∉ (gateAt C i).inputs)
    (hprivate : ∀ i < C.size, i ≠ k → n + j ∉ (gateAt C i).inputs) :
    ∀ w < n + k, w ≠ u.val → w ≠ n + j →
      wireVal n C w (pairInput u u) = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwu hwj
    by_cases hin : w < n
    · rw [wireVal_lt C w hin]
      have hne : (⟨w, hin⟩ : Fin n) ≠ u := by
        intro he
        exact hwu (congrArg Fin.val he)
      simp [pairInput, hne]
    · let i := w - n
      have hwi : n + i = w := by dsimp [i]; omega
      have hik : i < k := by omega
      have hi : i < C.size := by omega
      have hij : i ≠ j := by intro he; apply hwj; omega
      have himem : gateAt C i ∈ C.gates := by
        exact List.mem_of_getElem? (show C.gates[i]? = some (gateAt C i) by
          simp [gateAt, List.getD_eq_getElem?_getD, show i < C.gates.length from hi])
      have hoperand (v : ℕ) (hv : v ∈ (gateAt C i).inputs) :
          wireVal n C v (pairInput u u) = false := by
        have hvb := hao.2.1 i hi v hv
        apply ih v
        · omega
        · omega
        · intro he
          exact hsole i hi hij (he ▸ hv)
        · intro he
          exact hprivate i hi (by omega) (he ▸ hv)
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hao.2.2 _ himem)
      have ha := hoperand a (by simp [hab])
      have hb := hoperand b (by simp [hab])
      rw [← hwi]
      change gateVal n C i (pairInput u u) = false
      rw [gate_eq_eval C hao i hi]
      rcases hao.1 _ himem with hop | hop <;> simp [hop, hab, GateOp.eval, ha, hb]

lemma other_operand_singleton_false (C : Circuit) (hao : IsAO2 n C)
    (u : Fin n) (j k s : ℕ) (hjk : j < k) (hk : k < C.size)
    (hsole : ∀ i < C.size, i ≠ j → u.val ∉ (gateAt C i).inputs)
    (hprivate : ∀ i < C.size, i ≠ k → n + j ∉ (gateAt C i).inputs)
    (hs : s < n + k) (hsne : s ≠ n + j) (hsmem : s ∈ (gateAt C k).inputs) :
    wireVal n C s (pairInput u u) = false := by
  have hsu : s ≠ u.val := by
    intro he
    exact hsole k hk (by omega) (he ▸ hsmem)
  exact prefix_wire_singleton_false C hao u j k (Nat.le_of_lt hk) hsole hprivate s hs hsu hsne

end PEqualNP.Outside.L_meta_3566.PrivateSuccessorSingleton

namespace PEqualNP.Outside.L_meta_3566.AvailableProductExchange

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3566.Pruning
open PEqualNP.Outside.L_meta_3566.AndRotation
open PEqualNP.Outside.L_meta_3566.ANDRotationEvaluation

variable {n : ℕ}

def newGate (C : Circuit) (u : Fin n) (j k s q i : ℕ) : Gate :=
  if i = k - 1 then ⟨GateOp.and, [u.val, rename n j k s]⟩
  else if i = k then ⟨GateOp.or, [n + (k - 1), rename n j k q]⟩
  else let g := gateAt C (inv j k i)
    ⟨g.op, g.inputs.map (rename n j k)⟩

def exchange (C : Circuit) (u : Fin n) (j k s q : ℕ) : Circuit :=
  ⟨List.ofFn (fun i : Fin C.size => newGate C u j k s q i.val), rename n j k C.output⟩

lemma exchange_size (C : Circuit) (u : Fin n) (j k s q : ℕ) :
    (exchange C u j k s q).size = C.size := by simp [exchange, Circuit.size]

lemma exchange_gateAt (C : Circuit) (u : Fin n) (j k s q i : ℕ) (hi : i < C.size) :
    gateAt (exchange C u j k s q) i = newGate C u j k s q i := by
  simp [exchange, gateAt, List.getD_eq_getElem?_getD, hi]

lemma exchange_ao (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (honly : ∀ i < C.size, i ≠ k → n + j ∉ (gateAt C i).inputs) :
    IsAO2 n (exchange C u j k s q) := by
  have hnGate (i : ℕ) (hi : i < C.size) :
      (newGate C u j k s q i).op = GateOp.and ∨
      (newGate C u j k s q i).op = GateOp.or := by
    unfold newGate
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
    · change (gateAt C (inv j k i)).op = GateOp.and ∨ (gateAt C (inv j k i)).op = GateOp.or
      exact hao.1 _ (old_gate_mem C _ (inv_lt j k C.size i hjk hk hi))
  have hnLen (i : ℕ) (hi : i < C.size) : (newGate C u j k s q i).inputs.length = 2 := by
    unfold newGate
    split_ifs
    · rfl
    · rfl
    · simpa using hao.2.2 _ (old_gate_mem C _ (inv_lt j k C.size i hjk hk hi))
  have hnBack (i : ℕ) (hi : i < C.size) (w : ℕ)
      (hw : w ∈ (newGate C u j k s q i).inputs) : w < n + i := by
    unfold newGate at hw
    split_ifs at hw with hi0 hi1
    · have hsb := rename_before_rotated n j k s hjk hs hsne
      have hu := u.isLt
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> omega
    · have hqb := rename_before_rotated n j k q hjk hq hqne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> omega
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      let a := inv j k i
      have ha : a < C.size := inv_lt j k C.size i hjk hk hi
      have haj : a ≠ j := by
        intro he
        have hh := perm_inv j k i hjk
        change perm j k a = i at hh
        rw [he, perm_j] at hh
        exact hi0 hh.symm
      have hak : a ≠ k := by
        intro he
        have hh := perm_inv j k i hjk
        change perm j k a = i at hh
        rw [he, perm_k j k hjk] at hh
        exact hi1 hh.symm
      have hva : v < n + a := hao.2.1 a ha v hv
      have hvj : v ≠ n + j := by intro he; exact honly a ha hak (he ▸ hv)
      have hh := rename_before_perm n j k a v hjk haj hva hvj
      simpa only [a, perm_inv j k i hjk] using hh
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact hnGate i.val i.isLt
  · intro i hi w hw
    change i < (exchange C u j k s q).size at hi
    rw [exchange_size] at hi
    change w ∈ (gateAt (exchange C u j k s q) i).inputs at hw
    rw [exchange_gateAt C u j k s q i hi] at hw
    exact hnBack i hi w hw
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact hnLen i.val i.isLt

lemma or_gate_value (C : Circuit) (hao : IsAO2 n C) (i a b : ℕ)
    (hi : i < C.size) (hop : (gateAt C i).op = GateOp.or)
    (hin : (gateAt C i).inputs = [a, b] ∨ (gateAt C i).inputs = [b, a])
    (x : Fin n → Bool) :
    gateVal n C i x = (wireVal n C a x || wireVal n C b x) := by
  rw [gate_eq_eval C hao i hi x]
  rcases hin with hin | hin <;> simp [hop, hin, GateOp.eval, Bool.or_comm]

lemma values_solution (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hsne : s ≠ n + j) (hqne : q ≠ n + j)
    (honly : ∀ i < C.size, i ≠ k → n + j ∉ (gateAt C i).inputs)
    (x : Fin n → Bool) (hproduct : wireVal n C q x = (wireVal n C t x && wireVal n C s x)) :
    ∀ i < C.size, values C j k u.val s x (n + i) =
      (newGate C u j k s q i).op.eval
        ((newGate C u j k s q i).inputs.map (values C j k u.val s x)) := by
  intro i hi
  by_cases hi0 : i = k - 1
  · subst i
    simp [newGate, values_new_j, values_input C j k u.val s hjk x u,
      values_rename C j k u.val s s hjk x, hsne, GateOp.eval, wireVal_lt C u.val u.isLt]
  · by_cases hi1 : i = k
    · subst i
      have hk0 : k ≠ k - 1 := by omega
      have hj : j < C.size := by omega
      have hvg := or_gate_value C hao j u.val t hj hjop hjinputs x
      have hvk := and_gate_value C hao k (n + j) s hk hkop hkinputs x
      change gateVal n C k x = (gateVal n C j x && wireVal n C s x) at hvk
      rw [hvg] at hvk
      simp only [newGate, hk0, ite_false, ite_true, List.map_cons, List.map_nil,
        GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
        values_new_k C j k u.val s hjk x, values_new_j,
        values_rename C j k u.val s q hjk x, hqne, hproduct]
      simpa only [Bool.and_or_distrib_right] using hvk
    · let a := inv j k i
      have ha : a < C.size := inv_lt j k C.size i hjk hk hi
      have hak : a ≠ k := by
        intro he
        have hh := perm_inv j k i hjk
        change perm j k a = i at hh
        rw [he, perm_k j k hjk] at hh
        exact hi1 hh.symm
      have hvi : values C j k u.val s x (n + i) = gateVal n C a x := by
        have hi0' : n + i ≠ n + (k - 1) := by omega
        simp only [values, hi0', ite_false, unrename,
          Nat.not_lt.mpr (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
        rfl
      have hm : (gateAt C a).inputs.map (fun w => values C j k u.val s x (rename n j k w)) =
          (gateAt C a).inputs.map (fun w => wireVal n C w x) := by
        apply List.map_congr_left
        intro w hw
        have hwn : w ≠ n + j := by intro he; exact honly a ha hak (he ▸ hw)
        rw [values_rename C j k u.val s w hjk x, ite_eq_right hwn]
      rw [hvi]
      simp only [newGate, hi0, hi1, ite_false, List.map_map]
      change gateVal n C a x = (gateAt C a).op.eval
        ((gateAt C a).inputs.map (fun w => values C j k u.val s x (rename n j k w)))
      rw [hm]
      exact gate_eq_eval C hao a ha x

lemma exchange_wire_values (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (honly : ∀ i < C.size, i ≠ k → n + j ∉ (gateAt C i).inputs)
    (x : Fin n → Bool) (hproduct : wireVal n C q x = (wireVal n C t x && wireVal n C s x))
    (w : ℕ) (hw : w < n + C.size) :
    wireVal n (exchange C u j k s q) (rename n j k w) x =
      if w = n + j then wireVal n C u.val x && wireVal n C s x else wireVal n C w x := by
  have hnew := exchange_ao C hao u j k s q hjk hk hs hsne hq hqne honly
  have hsol : ∀ i < (exchange C u j k s q).size,
      values C j k u.val s x (n + i) =
        (gateAt (exchange C u j k s q) i).op.eval
          ((gateAt (exchange C u j k s q) i).inputs.map (values C j k u.val s x)) := by
    intro i hi
    rw [exchange_size] at hi
    rw [exchange_gateAt C u j k s q i hi]
    exact values_solution C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs hsne hqne honly x hproduct i hi
  have hh := wireVal_eq_of_solution (exchange C u j k s q) hnew x (values C j k u.val s x)
    (values_input C j k u.val s hjk x) hsol (rename n j k w)
    (by rw [exchange_size]; exact rename_bound n j k C.size w hjk hk hw)
  rw [values_rename C j k u.val s w hjk x] at hh
  exact hh

lemma exchange_circuitFun (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (honly : ∀ i < C.size, i ≠ k → n + j ∉ (gateAt C i).inputs)
    (hproduct : ∀ x : Fin n → Bool, wireVal n C q x = (wireVal n C t x && wireVal n C s x))
    (hout : C.output < n + C.size) (houtj : C.output ≠ n + j) :
    circuitFun n (exchange C u j k s q) = circuitFun n C := by
  funext x
  have hh := exchange_wire_values C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
    hs hsne hq hqne honly x (hproduct x) C.output hout
  rw [ite_eq_right houtj] at hh
  exact hh

end PEqualNP.Outside.L_meta_3566.AvailableProductExchange

namespace PEqualNP.Outside.L_meta_3566.AvailableProductExchange

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3566.Pruning
open PEqualNP.Outside.L_meta_3566.AndRotation
open PEqualNP.Outside.L_meta_3566.AndRotationCounts
open scoped BigOperators

variable {n : ℕ}

lemma exchange_op_at_perm (C : Circuit) (u : Fin n) (j k s q i : ℕ)
    (hjk : j < k) (hk : k < C.size) (hi : i < C.size) :
    (gateAt (exchange C u j k s q) (perm j k i)).op =
      if i = j then GateOp.and else if i = k then GateOp.or else (gateAt C i).op := by
  rw [exchange_gateAt C u j k s q _ (perm_lt j k C.size i hjk hk hi)]
  by_cases hij : i = j
  · subst i
    simp [newGate, perm_j]
  · by_cases hik : i = k
    · subst i
      have hk0 : k ≠ k - 1 := by omega
      simp [newGate, perm_k j k hjk, hk0, hij]
    · have hpi0 : perm j k i ≠ k - 1 := by
        intro he
        exact hij (AndRotation.perm_injective j k hjk (he.trans (perm_j j k).symm))
      have hpi1 : perm j k i ≠ k := by
        intro he
        exact hik (AndRotation.perm_injective j k hjk (he.trans (perm_k j k hjk).symm))
      simp [newGate, hpi0, hpi1, inv_perm j k i hjk, hij, hik]

lemma exchange_gate_values (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (x : Fin n → Bool) (hproduct : wireVal n C q x = (wireVal n C t x && wireVal n C s x))
    (i : ℕ) (hi : i < C.size) :
    gateVal n (exchange C u j k s q) (perm j k i) x =
      if i = j then wireVal n C u.val x && wireVal n C s x else gateVal n C i x := by
  have hh := exchange_wire_values C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
    hs hsne hq hqne honly x hproduct (n + i) (by omega)
  rw [rename_gate] at hh
  simpa only [gateVal, wireVal, Nat.add_left_cancel_iff] using hh

lemma new_and_implies_old_and (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (x : Fin n → Bool) (hnew : (wireVal n C u.val x && wireVal n C s x) = true) :
    gateVal n C k x = true := by
  have hvg := or_gate_value C hao j u.val t (by omega) hjop hjinputs x
  have hvk := and_gate_value C hao k (n + j) s hk hkop hkinputs x
  change gateVal n C k x = (gateVal n C j x && wireVal n C s x) at hvk
  cases hu : wireVal n C u.val x <;> cases hs : wireVal n C s x <;>
    simp_all

def trueGateCount (n : ℕ) (C : Circuit) (x : Fin n → Bool) : ℕ :=
  ∑ i ∈ Finset.range C.size, if gateVal n C i x then 1 else 0

lemma exchange_gate_truth_le (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (x : Fin n → Bool) (hproduct : wireVal n C q x = (wireVal n C t x && wireVal n C s x))
    (i : ℕ) (hi : i < C.size) :
    (if gateVal n (exchange C u j k s q) (perm j k i) x then 1 else 0) ≤
      (if gateVal n C i x then 1 else 0) := by
  rw [exchange_gate_values C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
    hs hsne hq hqne honly x hproduct i hi]
  by_cases hij : i = j
  · subst i
    rw [or_gate_value C hao j u.val t (by omega) hjop hjinputs x]
    cases hu : wireVal n C u.val x <;> cases ht : wireVal n C t x <;>
      cases hss : wireVal n C s x <;> simp
  · simp [hij]

lemma exchange_trueGateCount_le (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (x : Fin n → Bool) (hproduct : wireVal n C q x = (wireVal n C t x && wireVal n C s x)) :
    trueGateCount n (exchange C u j k s q) x ≤ trueGateCount n C x := by
  unfold trueGateCount
  rw [exchange_size, sum_perm j k C.size hjk hk]
  apply Finset.sum_le_sum
  intro i hi
  exact exchange_gate_truth_le C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
    hs hsne hq hqne honly x hproduct i (Finset.mem_range.mp hi)

lemma exchange_trueGateCount_strict (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (x : Fin n → Bool) (hproduct : wireVal n C q x = (wireVal n C t x && wireVal n C s x))
    (hxu : x u = true) (hxs : wireVal n C s x = false) :
    trueGateCount n (exchange C u j k s q) x < trueGateCount n C x := by
  unfold trueGateCount
  rw [exchange_size, sum_perm j k C.size hjk hk]
  apply Finset.sum_lt_sum
  · intro i hi
    exact exchange_gate_truth_le C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
      hs hsne hq hqne honly x hproduct i (Finset.mem_range.mp hi)
  · refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
    rw [exchange_gate_values C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
      hs hsne hq hqne honly x hproduct j (by omega)]
    rw [or_gate_value C hao j u.val t (by omega) hjop hjinputs x]
    simp [wireVal_lt C u.val u.isLt, hxu, hxs]

end PEqualNP.Outside.L_meta_3566.AvailableProductExchange

namespace PEqualNP.Outside.L_meta_3566.AvailableProductExchange

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3566.Pruning

variable {n : ℕ}

lemma exchange_trueGateCount_singleton_strict (C : Circuit) (hao : IsAO2 n C)
    (u : Fin n) (j k t s q : ℕ) (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (hsole : ∀ i < C.size, i ≠ j → u.val ∉ (gateAt C i).inputs)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (hproduct : wireVal n C q (pairInput u u) =
      (wireVal n C t (pairInput u u) && wireVal n C s (pairInput u u))) :
    trueGateCount n (exchange C u j k s q) (pairInput u u) <
      trueGateCount n C (pairInput u u) := by
  have hsmem : s ∈ (gateAt C k).inputs := by
    rcases hkinputs with h | h <;> simp [h]
  have hzero := PrivateSuccessorSingleton.other_operand_singleton_false C hao u j k s
    hjk hk hsole honly hs hsne hsmem
  exact exchange_trueGateCount_strict C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
    hs hsne hq hqne honly (pairInput u u) hproduct (by simp [pairInput]) hzero

end PEqualNP.Outside.L_meta_3566.AvailableProductExchange

namespace PEqualNP.Outside.L_meta_3566.AvailableProductExchange

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3566.Pruning
open PEqualNP.Outside.L_meta_3566.AndRotation

variable {n : ℕ}

noncomputable def negativeAnds (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter (fun i => (gateAt C i).op = GateOp.and ∧
    ∃ x : Fin n → Bool, F x = false ∧ gateVal n C i x = true)

lemma mem_negativeAnds (C : Circuit) (F : (Fin n → Bool) → Bool) (i : ℕ) :
    i ∈ negativeAnds n C F ↔ i < C.size ∧ (gateAt C i).op = GateOp.and ∧
      ∃ x : Fin n → Bool, F x = false ∧ gateVal n C i x = true := by
  classical
  simp [negativeAnds]

lemma exchange_negativeAnds_card_le (C : Circuit) (hao : IsAO2 n C)
    (F : (Fin n → Bool) → Bool) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (hproduct : ∀ x : Fin n → Bool, wireVal n C q x = (wireVal n C t x && wireVal n C s x)) :
    (negativeAnds n (exchange C u j k s q) F).card ≤ (negativeAnds n C F).card := by
  classical
  let D := exchange C u j k s q
  let f : ℕ → ℕ := fun i => Equiv.swap j k (inv j k i)
  have hfinj : Function.Injective f := by
    intro a b he
    have hinv := (Equiv.swap j k).injective he
    have hh := congrArg (perm j k) hinv
    simpa only [perm_inv j k a hjk, perm_inv j k b hjk] using hh
  have hsub : (negativeAnds n D F).image f ⊆ negativeAnds n C F := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hiD, hop, x, hFx, hx⟩ := (mem_negativeAnds D F i).mp hi
    have hiC : i < C.size := by simpa only [D, exchange_size] using hiD
    let a := inv j k i
    have ha : a < C.size := inv_lt j k C.size i hjk hk hiC
    have hpi : perm j k a = i := perm_inv j k i hjk
    have htag := exchange_op_at_perm C u j k s q a hjk hk ha
    rw [hpi] at htag
    have hval := exchange_gate_values C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
      hs hsne hq hqne honly x (hproduct x) a ha
    rw [hpi] at hval
    by_cases haj : a = j
    · have hf : f i = k := by
        change Equiv.swap j k a = k
        simp [haj]
      rw [hf]
      apply (mem_negativeAnds C F k).mpr
      refine ⟨hk, hkop, x, hFx, ?_⟩
      have hnew : (wireVal n C u.val x && wireVal n C s x) = true := by
        simpa only [haj, ite_true] using hval.symm.trans hx
      exact new_and_implies_old_and C hao u j k t s hjk hk hjop hjinputs hkop hkinputs x hnew
    · by_cases hak : a = k
      · have hfalse : GateOp.or = GateOp.and := by
          simpa only [hak, Nat.ne_of_gt hjk, ite_false, ite_true] using htag.symm.trans hop
        cases hfalse
      · have hf : f i = a := by
          change Equiv.swap j k a = a
          simp [Equiv.swap_apply_def, haj, hak]
        rw [hf]
        apply (mem_negativeAnds C F a).mpr
        refine ⟨ha, ?_, x, hFx, ?_⟩
        · simpa only [haj, hak, ite_false] using htag.symm.trans hop
        · simpa only [haj, ite_false] using hval.symm.trans hx
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hfinj] using hc

end PEqualNP.Outside.L_meta_3566.AvailableProductExchange


namespace PEqualNP.Outside.L_meta_3566.FrontierWireCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open Pruning
open scoped BigOperators

variable {n : ℕ}

def bit (b : Bool) : ℕ := if b = true then 1 else 0

lemma count_true_sum (L : List Bool) : L.count true = (L.map bit).sum := by
  induction L with
  | nil => rfl
  | cons b L ih => cases b <;> simp [bit, ih, Nat.add_comm]

lemma count_true_ofFn {s : ℕ} (f : Fin s → Bool) :
    (List.ofFn f).count true = ∑ i : Fin s, bit (f i) := by
  rw [count_true_sum, List.map_ofFn, Fin.sum_ofFn]
  rfl

lemma wires_eq_ofFn (C : Circuit) (x : Fin n → Bool) :
    C.wires (List.ofFn x) = List.ofFn (fun i : Fin (n + C.size) => wireVal n C i.val x) := by
  have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
    unfold Circuit.wires
    rw [Pruning.wires_length, List.length_ofFn]
    rfl
  apply List.ext_getElem
  · simpa using hlen
  · intro i hi hj
    simp only [List.getElem_ofFn, wireVal, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some]

lemma wire_count (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).count true =
      (List.ofFn x).count true + ∑ i ∈ Finset.range C.size, bit (gateVal n C i x) := by
  rw [wires_eq_ofFn, count_true_ofFn,
    Fin.sum_univ_eq_sum_range (fun w => bit (wireVal n C w x)) (n + C.size),
    Finset.sum_range_add]
  congr 1
  rw [count_true_ofFn,
    ← Fin.sum_univ_eq_sum_range (fun w => bit (wireVal n C w x)) n]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg bit (wireVal_lt C i.val i.isLt x)

lemma sum_one_changed {α : Type*} [Fintype α] [DecidableEq α]
    (f g : α → ℕ) (p : α ≃ α) (a : α)
    (hsame : ∀ i, i ≠ a → g (p i) = f i) :
    (∑ i, g i) + f a = (∑ i, f i) + g (p a) := by
  have hp : (∑ i, g (p i)) = ∑ i, g i := Equiv.sum_comp p g
  have hpoint : ∀ i, g (p i) + (if i = a then f a else 0) =
      f i + (if i = a then g (p a) else 0) := by
    intro i
    by_cases hi : i = a
    · subst i
      simp [Nat.add_comm]
    · simp [hi, hsame i hi]
  have hh := Finset.sum_congr (rfl : (Finset.univ : Finset α) = Finset.univ)
    (fun i _ => hpoint i)
  simpa [Finset.sum_add_distrib, hp] using hh

end PEqualNP.Outside.L_meta_3566.FrontierWireCount

namespace PEqualNP.Outside.L_meta_3566.AvailableProductWireMass

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open Pruning AvailableProductExchange
open scoped BigOperators

variable {n : ℕ}

lemma wire_count (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).count true =
      (List.ofFn x).count true + trueGateCount n C x := by
  simpa [FrontierWireCount.bit, trueGateCount] using FrontierWireCount.wire_count C x

lemma wire_count_le (C D : Circuit) (x : Fin n → Bool)
    (h : trueGateCount n D x ≤ trueGateCount n C x) :
    (D.wires (List.ofFn x)).count true ≤ (C.wires (List.ofFn x)).count true := by
  rw [wire_count, wire_count]
  omega

lemma wire_count_lt (C D : Circuit) (x : Fin n → Bool)
    (h : trueGateCount n D x < trueGateCount n C x) :
    (D.wires (List.ofFn x)).count true < (C.wires (List.ofFn x)).count true := by
  rw [wire_count, wire_count]
  omega

noncomputable def negativeMass (F : (Fin n → Bool) → Bool) (C : Circuit) : ℕ :=
  ∑ x : Fin n → Bool, if F x = false then (C.wires (List.ofFn x)).count true else 0

lemma exchange_negative_mass_strict (F : (Fin n → Bool) → Bool)
    (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (hsole : ∀ i < C.size, i ≠ j → u.val ∉ (gateAt C i).inputs)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (hproduct : ∀ x, wireVal n C q x = (wireVal n C t x && wireVal n C s x))
    (hunit : F (pairInput u u) = false) :
    negativeMass F (exchange C u j k s q) < negativeMass F C := by
  classical
  unfold negativeMass
  apply Finset.sum_lt_sum
  · intro x hx
    by_cases hFx : F x = false
    · simp only [hFx, ite_true]
      apply wire_count_le
      exact exchange_trueGateCount_le C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
        hs hsne hq hqne honly x (hproduct x)
    · simp [hFx]
  · refine ⟨pairInput u u, Finset.mem_univ _, ?_⟩
    simp only [hunit, ite_true]
    apply wire_count_lt
    exact exchange_trueGateCount_singleton_strict C hao u j k t s q hjk hk
      hjop hjinputs hkop hkinputs hs hsne hq hqne hsole honly (hproduct _)

lemma same_size_improvement (F : (Fin n → Bool) → Bool)
    (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (hsole : ∀ i < C.size, i ≠ j → u.val ∉ (gateAt C i).inputs)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (hproduct : ∀ x, wireVal n C q x = (wireVal n C t x && wireVal n C s x))
    (hunit : F (pairInput u u) = false)
    (hout : C.output < n + C.size) (houtj : C.output ≠ n + j) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size ∧ circuitFun n D = circuitFun n C ∧
      (negativeAnds n D F).card ≤ (negativeAnds n C F).card ∧
      negativeMass F D < negativeMass F C := by
  refine ⟨exchange C u j k s q, ?_, exchange_size C u j k s q, ?_, ?_, ?_⟩
  · exact exchange_ao C hao u j k s q hjk hk hs hsne hq hqne honly
  · exact exchange_circuitFun C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
      hs hsne hq hqne honly hproduct hout houtj
  · exact exchange_negativeAnds_card_le C hao F u j k t s q hjk hk hjop hjinputs hkop hkinputs
      hs hsne hq hqne honly hproduct
  · exact exchange_negative_mass_strict F C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
      hs hsne hq hqne hsole honly hproduct hunit

lemma unavailable_product_of_minimum (F : (Fin n → Bool) → Bool)
    (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j)
    (hsole : ∀ i < C.size, i ≠ j → u.val ∉ (gateAt C i).inputs)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (hunit : F (pairInput u u) = false)
    (hout : C.output < n + C.size) (houtj : C.output ≠ n + j)
    (hmin : ∀ D : Circuit, IsAO2 n D → D.size = C.size →
      circuitFun n D = circuitFun n C → (negativeAnds n D F).card ≤ (negativeAnds n C F).card →
      negativeMass F C ≤ negativeMass F D) :
    ¬ ∃ q : ℕ, q < n + k ∧ q ≠ n + j ∧
      ∀ x, wireVal n C q x = (wireVal n C t x && wireVal n C s x) := by
  rintro ⟨q, hq, hqne, hproduct⟩
  obtain ⟨D, hD, hsize, hfun, hjunk, hmass⟩ := same_size_improvement F C hao u j k t s q
    hjk hk hjop hjinputs hkop hkinputs hs hsne hq hqne hsole honly hproduct hunit hout houtj
  exact (Nat.not_lt_of_ge (hmin D hD hsize hfun hjunk)) hmass

end PEqualNP.Outside.L_meta_3566.AvailableProductWireMass


namespace PEqualNP.Outside.L_meta_3566.AvailableProductMass

lemma exchange (z t s q : Bool) (hq : q = (t && s)) :
    ((z && s) || q) = ((z || t) && s) := by
  subst q
  cases z <;> cases t <;> cases s <;> decide

lemma first_le (z t s : Bool) : (z && s) = true → (z || t) = true := by
  cases z <;> cases t <;> cases s <;> decide

lemma and_le (z t s : Bool) : (z && s) = true → ((z || t) && s) = true := by
  cases z <;> cases t <;> cases s <;> decide

lemma strict_at_singleton (t : Bool) :
    (true || t) = true ∧ (true && false) = false := by
  cases t <;> decide

noncomputable def mass {α : Type*} (N : Finset α) (f : α → Bool) : ℕ :=
  (N.filter fun x => f x = true).card

lemma new_and_clean {α : Type*} (F z t s : α → Bool)
    (hold : ∀ x, ((z x || t x) && s x) = true → F x = true) :
    ∀ x, (z x && s x) = true → F x = true := by
  intro x hx
  exact hold x (and_le (z x) (t x) (s x) hx)

lemma pair_mass_strict {α : Type*} (N : Finset α) (z t s q : α → Bool)
    (hq : ∀ x, q x = (t x && s x))
    (w : α) (hw : w ∈ N) (hzw : z w = true) (hsw : s w = false) :
    mass N (fun x => z x && s x) + mass N (fun x => (z x && s x) || q x) <
      mass N (fun x => z x || t x) + mass N (fun x => (z x || t x) && s x) := by
  classical
  have hsecond : (fun x => (z x && s x) || q x) =
      (fun x => (z x || t x) && s x) := by
    funext x
    exact exchange (z x) (t x) (s x) (q x) (hq x)
  rw [hsecond]
  have hsub : (N.filter fun x => (z x && s x) = true) ⊆
      (N.filter fun x => (z x || t x) = true) := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxn, hx⟩
    exact Finset.mem_filter.mpr ⟨hxn, first_le (z x) (t x) (s x) hx⟩
  have hne : (N.filter fun x => (z x && s x) = true) ≠
      (N.filter fun x => (z x || t x) = true) := by
    intro heq
    have hwold : w ∈ N.filter fun x => (z x || t x) = true := by
      simp [hw, hzw]
    rw [← heq] at hwold
    simpa [hzw, hsw] using (Finset.mem_filter.mp hwold).2
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  simpa only [mass] using Nat.add_lt_add_right hlt
    (mass N (fun x => (z x || t x) && s x))

lemma pair_mass_strict_of_t_le_s {α : Type*} (N : Finset α) (z t s : α → Bool)
    (hts : ∀ x, t x = true → s x = true)
    (w : α) (hw : w ∈ N) (hzw : z w = true) (hsw : s w = false) :
    mass N (fun x => z x && s x) + mass N (fun x => (z x && s x) || t x) <
      mass N (fun x => z x || t x) + mass N (fun x => (z x || t x) && s x) := by
  apply pair_mass_strict N z t s t ?_ w hw hzw hsw
  intro x
  cases ht : t x
  · simp
  · simp [hts x ht]

end PEqualNP.Outside.L_meta_3566.AvailableProductMass


namespace PEqualNP.Outside.L_meta_3566.TwoGateObstruction

/-- false denotes OR and true denotes AND. -/
def applyOp (op a b : Bool) : Bool := if op then a && b else a || b

def twoGate (op₀ op₁ : Bool) (a₀ b₀ : Fin 3) (a₁ b₁ : Fin 4)
    (x : Fin 3 → Bool) : Bool :=
  let y := applyOp op₀ (x a₀) (x b₀)
  let w (i : Fin 4) := if h : i.val < 3 then x ⟨i.val, h⟩ else y
  applyOp op₁ (w a₁) (w b₁)

def input (z t s : Bool) (i : Fin 3) : Bool :=
  if i = 0 then z else if i = 1 then t else s

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
set_option synthInstance.maxSize 2000 in
lemma classify_cube : ∀ (op₀ op₁ : Bool) (a₀ b₀ : Fin 3) (a₁ b₁ : Fin 4),
    (∀ z t s : Bool, twoGate op₀ op₁ a₀ b₀ a₁ b₁ (input z t s) = ((z || t) && s)) →
    op₀ = false ∧ ((a₀ = 0 ∧ b₀ = 1) ∨ (a₀ = 1 ∧ b₀ = 0)) ∧
      op₁ = true ∧ ((a₁ = 2 ∧ b₁ = 3) ∨ (a₁ = 3 ∧ b₁ = 2)) := by
  decide

lemma classify (op₀ op₁ : Bool) (a₀ b₀ : Fin 3) (a₁ b₁ : Fin 4)
    (h : ∀ x : Fin 3 → Bool, twoGate op₀ op₁ a₀ b₀ a₁ b₁ x = ((x 0 || x 1) && x 2)) :
    op₀ = false ∧ ((a₀ = 0 ∧ b₀ = 1) ∨ (a₀ = 1 ∧ b₀ = 0)) ∧
      op₁ = true ∧ ((a₁ = 2 ∧ b₁ = 3) ∨ (a₁ = 3 ∧ b₁ = 2)) := by
  apply classify_cube
  intro z t s
  simpa [input] using h (input z t s)

end PEqualNP.Outside.L_meta_3566.TwoGateObstruction


namespace PEqualNP.Outside.L_meta_3566.ANDRotationComparison

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open Pruning ANDRotationEvaluation

variable {n : ℕ}

lemma gate_eval_monotone (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (V W : ℕ → Bool) (hVW : ∀ i ∈ g.inputs, V i = true → W i = true) :
    g.op.eval (g.inputs.map V) = true → g.op.eval (g.inputs.map W) = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h i hi
    exact hVW i hi (h i hi)
  · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, hV⟩
    exact ⟨i, hi, hVW i hi hV⟩

lemma wireVal_le_of_supersolution (C : Circuit) (hao : IsAO2 n C)
    (x : Fin n → Bool) (V : ℕ → Bool)
    (hinput : ∀ i : Fin n, x i = true → V i.val = true)
    (hgate : ∀ j < C.size,
      (gateAt C j).op.eval ((gateAt C j).inputs.map V) = true → V (n + j) = true) :
    ∀ w < n + C.size, wireVal n C w x = true → V w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw htrue
    by_cases hin : w < n
    · rw [wireVal_lt C w hin] at htrue
      exact hinput ⟨w, hin⟩ htrue
    · let j := w - n
      have hwj : n + j = w := by dsimp [j]; omega
      have hj : j < C.size := by dsimp [j]; omega
      have hmem : gateAt C j ∈ C.gates := by
        exact List.mem_of_getElem? (show C.gates[j]? = some (gateAt C j) by
          simp [gateAt, List.getD_eq_getElem?_getD, show j < C.gates.length from hj])
      have heval : (gateAt C j).op.eval
          ((gateAt C j).inputs.map (fun i => wireVal n C i x)) = true := by
        rw [← gate_eq_eval C hao j hj x]
        change wireVal n C (n + j) x = true
        simpa only [hwj] using htrue
      rw [← hwj]
      apply hgate j hj
      apply gate_eval_monotone (gateAt C j) (hao.1 _ hmem) (fun i => wireVal n C i x) V
      · intro i hi hval
        have hib := hao.2.1 j hj i hi
        exact ih i (by omega) (by omega) hval
      · exact heval

lemma wireVal_ge_of_subsolution (C : Circuit) (hao : IsAO2 n C)
    (x : Fin n → Bool) (V : ℕ → Bool)
    (hinput : ∀ i : Fin n, V i.val = true → x i = true)
    (hgate : ∀ j < C.size,
      V (n + j) = true → (gateAt C j).op.eval ((gateAt C j).inputs.map V) = true) :
    ∀ w < n + C.size, V w = true → wireVal n C w x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw htrue
    by_cases hin : w < n
    · rw [wireVal_lt C w hin]
      exact hinput ⟨w, hin⟩ htrue
    · let j := w - n
      have hwj : n + j = w := by dsimp [j]; omega
      have hj : j < C.size := by dsimp [j]; omega
      have hmem : gateAt C j ∈ C.gates := by
        exact List.mem_of_getElem? (show C.gates[j]? = some (gateAt C j) by
          simp [gateAt, List.getD_eq_getElem?_getD, show j < C.gates.length from hj])
      rw [← hwj] at htrue ⊢
      change gateVal n C j x = true
      rw [gate_eq_eval C hao j hj x]
      apply gate_eval_monotone (gateAt C j) (hao.1 _ hmem) V (fun i => wireVal n C i x)
      · intro i hi hval
        have hib := hao.2.1 j hj i hi
        exact ih i (by omega) (by omega) hval
      · exact hgate j hj htrue

lemma ao2_wire_mono (C : Circuit) (hao : IsAO2 n C) (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, x i = true → y i = true) (w : ℕ) (hw : w < n + C.size) :
    wireVal n C w x = true → wireVal n C w y = true := by
  refine wireVal_ge_of_subsolution C hao y (fun i => wireVal n C i x) ?_ ?_ w hw
  · intro i hi
    rw [wireVal_lt C i.val i.isLt] at hi
    exact hxy i hi
  · intro j hj ht
    rw [← gate_eq_eval C hao j hj x]
    exact ht

end PEqualNP.Outside.L_meta_3566.ANDRotationComparison


namespace PEqualNP.Outside.L_meta_3566.WeakProductExchange

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3566.Pruning
open PEqualNP.Outside.L_meta_3566.AndRotation
open PEqualNP.Outside.L_meta_3566.ANDRotationEvaluation
open PEqualNP.Outside.L_meta_3566.ANDRotationComparison
open PEqualNP.Outside.L_meta_3566.AvailableProductExchange

variable {n : ℕ}

lemma values_eq_except_consumer (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k s q : ℕ)
    (hjk : j < k) (hk : k < C.size) (hsne : s ≠ n + j)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (x : Fin n → Bool) (i : ℕ) (hi : i < C.size) (hik : i ≠ k) :
    values C j k u.val s x (n + i) =
      (AvailableProductExchange.newGate C u j k s q i).op.eval
        ((AvailableProductExchange.newGate C u j k s q i).inputs.map (values C j k u.val s x)) := by
  by_cases hi0 : i = k - 1
  · subst i
    simp [AvailableProductExchange.newGate, values_new_j, values_input C j k u.val s hjk x u,
      values_rename C j k u.val s s hjk x, hsne, GateOp.eval, wireVal_lt C u.val u.isLt]
  · let a := inv j k i
    have ha : a < C.size := inv_lt j k C.size i hjk hk hi
    have hak : a ≠ k := by
      intro he
      have hh := perm_inv j k i hjk
      change perm j k a = i at hh
      rw [he, perm_k j k hjk] at hh
      exact hik hh.symm
    have hvi : values C j k u.val s x (n + i) = gateVal n C a x := by
      have hi0' : n + i ≠ n + (k - 1) := by omega
      simp only [values, hi0', ite_false, unrename,
        Nat.not_lt.mpr (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      rfl
    have hm : (gateAt C a).inputs.map (fun w => values C j k u.val s x (rename n j k w)) =
        (gateAt C a).inputs.map (fun w => wireVal n C w x) := by
      apply List.map_congr_left
      intro w hw
      have hwn : w ≠ n + j := by intro he; exact honly a ha hak (he ▸ hw)
      rw [values_rename C j k u.val s w hjk x, ite_eq_right hwn]
    rw [hvi]
    simp only [AvailableProductExchange.newGate, hi0, hik, ite_false, List.map_map]
    change gateVal n C a x = (gateAt C a).op.eval
      ((gateAt C a).inputs.map (fun w => values C j k u.val s x (rename n j k w)))
    rw [hm]
    exact gate_eq_eval C hao a ha x

lemma values_consumer_eval (C : Circuit) (u : Fin n) (j k s q : ℕ)
    (hjk : j < k) (hqne : q ≠ n + j) (x : Fin n → Bool) :
    (AvailableProductExchange.newGate C u j k s q k).op.eval
      ((AvailableProductExchange.newGate C u j k s q k).inputs.map (values C j k u.val s x)) =
      ((wireVal n C u.val x && wireVal n C s x) || wireVal n C q x) := by
  have hk0 : k ≠ k - 1 := by omega
  simp [AvailableProductExchange.newGate, hk0, GateOp.eval, values_new_j,
    values_rename C j k u.val s q hjk x, hqne]

lemma consumer_old_value (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (x : Fin n → Bool) :
    gateVal n C k x = ((wireVal n C u.val x || wireVal n C t x) && wireVal n C s x) := by
  have hjv := or_gate_value C hao j u.val t (by omega) hjop hjinputs x
  have hkv := and_gate_value C hao k (n + j) s hk hkop hkinputs x
  change gateVal n C k x = (gateVal n C j x && wireVal n C s x) at hkv
  rw [hjv] at hkv
  exact hkv

lemma values_supersolution (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hsne : s ≠ n + j) (hqne : q ≠ n + j)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (x : Fin n → Bool)
    (hupper : wireVal n C q x = true → (wireVal n C t x && wireVal n C s x) = true) :
    ∀ i < C.size, (AvailableProductExchange.newGate C u j k s q i).op.eval
      ((AvailableProductExchange.newGate C u j k s q i).inputs.map (values C j k u.val s x)) = true →
        values C j k u.val s x (n + i) = true := by
  intro i hi ht
  by_cases hik : i = k
  · subst i
    rw [values_consumer_eval C u j k s q hjk hqne x] at ht
    rw [values_new_k C j k u.val s hjk x,
      consumer_old_value C hao u j k t s hjk hk hjop hjinputs hkop hkinputs x]
    cases hu : wireVal n C u.val x <;> cases htv : wireVal n C t x <;>
      cases hsv : wireVal n C s x <;> cases hqv : wireVal n C q x <;> simp_all
  · rw [values_eq_except_consumer C hao u j k s q hjk hk hsne honly x i hi hik]
    exact ht

lemma values_subsolution (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hsne : s ≠ n + j) (hqne : q ≠ n + j)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (x : Fin n → Bool)
    (hlower : x u = false → (wireVal n C t x && wireVal n C s x) = true → wireVal n C q x = true) :
    ∀ i < C.size, values C j k u.val s x (n + i) = true →
      (AvailableProductExchange.newGate C u j k s q i).op.eval
        ((AvailableProductExchange.newGate C u j k s q i).inputs.map (values C j k u.val s x)) = true := by
  intro i hi ht
  by_cases hik : i = k
  · subst i
    rw [values_consumer_eval C u j k s q hjk hqne x]
    rw [values_new_k C j k u.val s hjk x,
      consumer_old_value C hao u j k t s hjk hk hjop hjinputs hkop hkinputs x] at ht
    rw [wireVal_lt C u.val u.isLt] at ht ⊢
    cases hu : x u <;> cases htv : wireVal n C t x <;>
      cases hsv : wireVal n C s x <;> cases hqv : wireVal n C q x <;> simp_all
  · rw [← values_eq_except_consumer C hao u j k s q hjk hk hsne honly x i hi hik]
    exact ht

lemma exchange_wire_upper (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (x : Fin n → Bool)
    (hupper : wireVal n C q x = true → (wireVal n C t x && wireVal n C s x) = true)
    (w : ℕ) (hw : w < n + C.size) :
    wireVal n (exchange C u j k s q) (rename n j k w) x = true →
      (if w = n + j then wireVal n C u.val x && wireVal n C s x else wireVal n C w x) = true := by
  have hnew := exchange_ao C hao u j k s q hjk hk hs hsne hq hqne honly
  have hsol : ∀ i < (exchange C u j k s q).size,
      (gateAt (exchange C u j k s q) i).op.eval
        ((gateAt (exchange C u j k s q) i).inputs.map (values C j k u.val s x)) = true →
          values C j k u.val s x (n + i) = true := by
    intro i hi
    rw [exchange_size] at hi
    rw [exchange_gateAt C u j k s q i hi]
    exact values_supersolution C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
      hsne hqne honly x hupper i hi
  have hh := wireVal_le_of_supersolution (exchange C u j k s q) hnew x (values C j k u.val s x)
    (fun i hi => by rw [values_input C j k u.val s hjk x i]; exact hi) hsol (rename n j k w)
    (by rw [exchange_size]; exact rename_bound n j k C.size w hjk hk hw)
  rw [values_rename C j k u.val s w hjk x] at hh
  exact hh

lemma exchange_wire_lower (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (x : Fin n → Bool)
    (hlower : x u = false → (wireVal n C t x && wireVal n C s x) = true → wireVal n C q x = true)
    (w : ℕ) (hw : w < n + C.size) :
    (if w = n + j then wireVal n C u.val x && wireVal n C s x else wireVal n C w x) = true →
      wireVal n (exchange C u j k s q) (rename n j k w) x = true := by
  have hnew := exchange_ao C hao u j k s q hjk hk hs hsne hq hqne honly
  have hsol : ∀ i < (exchange C u j k s q).size,
      values C j k u.val s x (n + i) = true →
        (gateAt (exchange C u j k s q) i).op.eval
          ((gateAt (exchange C u j k s q) i).inputs.map (values C j k u.val s x)) = true := by
    intro i hi
    rw [exchange_size] at hi
    rw [exchange_gateAt C u j k s q i hi]
    exact values_subsolution C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
      hsne hqne honly x hlower i hi
  have hh := wireVal_ge_of_subsolution (exchange C u j k s q) hnew x (values C j k u.val s x)
    (fun i hi => by rw [values_input C j k u.val s hjk x i] at hi; exact hi) hsol (rename n j k w)
    (by rw [exchange_size]; exact rename_bound n j k C.size w hjk hk hw)
  rw [values_rename C j k u.val s w hjk x] at hh
  exact hh

lemma exchange_graphFun (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (u : Fin n) (j k t s q : ℕ) (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (hnegative : ∀ x : Fin n → Bool, graphFun G ∅ x = false → wireVal n C q x = true →
      (wireVal n C t x && wireVal n C s x) = true)
    (hedges : ∀ a b : Fin n, G.Adj a b → a ≠ u → b ≠ u →
      (wireVal n C t (pairInput a b) && wireVal n C s (pairInput a b)) = true →
        wireVal n C q (pairInput a b) = true)
    (hout : C.output < n + C.size) (houtj : C.output ≠ n + j) :
    circuitFun n (exchange C u j k s q) = graphFun G ∅ := by
  have hnew := exchange_ao C hao u j k s q hjk hk hs hsne hq hqne honly
  have hupperout : (exchange C u j k s q).output < n + (exchange C u j k s q).size := by
    change rename n j k C.output < n + (exchange C u j k s q).size
    rw [exchange_size]
    exact rename_bound n j k C.size C.output hjk hk hout
  have hedgetrue : ∀ a b : Fin n, G.Adj a b → circuitFun n (exchange C u j k s q) (pairInput a b) = true := by
    intro a b hab
    have hlow : pairInput a b u = false →
        (wireVal n C t (pairInput a b) && wireVal n C s (pairInput a b)) = true →
          wireVal n C q (pairInput a b) = true := by
      intro hu ht
      have hau : a ≠ u := by intro he; subst a; simp [pairInput] at hu
      have hbu : b ≠ u := by intro he; subst b; simp [pairInput] at hu
      exact hedges a b hab hau hbu ht
    have hh := exchange_wire_lower C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
      hs hsne hq hqne honly (pairInput a b) hlow C.output hout
    rw [ite_eq_right houtj] at hh
    apply hh
    change circuitFun n C (pairInput a b) = true
    rw [hfun]
    exact (SingleRead.graph_pair G a b).mpr hab
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hDx
    by_contra hnot
    have hFx : graphFun G ∅ x = false := Bool.eq_false_iff.mpr hnot
    have hh := exchange_wire_upper C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
      hs hsne hq hqne honly x (hnegative x hFx) C.output hout hDx
    rw [ite_eq_right houtj] at hh
    change circuitFun n C x = true at hh
    rw [hfun, hFx] at hh
    cases hh
  · intro hFx
    have hex : ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
      simpa [graphFun] using hFx
    obtain ⟨a, b, hab, ha, hb⟩ := hex
    have hxy : ∀ i : Fin n, pairInput a b i = true → x i = true := by
      intro i hi
      simp only [pairInput, decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
    exact ao2_wire_mono (exchange C u j k s q) hnew (pairInput a b) x hxy
      (exchange C u j k s q).output hupperout (hedgetrue a b hab)

end PEqualNP.Outside.L_meta_3566.WeakProductExchange


namespace PEqualNP.Outside.L_meta_3566.WeakProductExchange

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3566.Pruning
open PEqualNP.Outside.L_meta_3566.AndRotation
open PEqualNP.Outside.L_meta_3566.AndRotationCounts
open PEqualNP.Outside.L_meta_3566.AvailableProductExchange
open scoped BigOperators

variable {n : ℕ}

lemma exchange_gate_upper (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (x : Fin n → Bool)
    (hupper : wireVal n C q x = true → (wireVal n C t x && wireVal n C s x) = true)
    (i : ℕ) (hi : i < C.size) :
    gateVal n (exchange C u j k s q) (perm j k i) x = true →
      (if i = j then wireVal n C u.val x && wireVal n C s x else gateVal n C i x) = true := by
  have hh := exchange_wire_upper C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
    hs hsne hq hqne honly x hupper (n + i) (by omega)
  rw [rename_gate] at hh
  simpa only [gateVal, wireVal, Nat.add_left_cancel_iff] using hh

lemma exchange_gate_truth_le (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (x : Fin n → Bool)
    (hupper : wireVal n C q x = true → (wireVal n C t x && wireVal n C s x) = true)
    (i : ℕ) (hi : i < C.size) :
    (if gateVal n (exchange C u j k s q) (perm j k i) x then 1 else 0) ≤
      (if gateVal n C i x then 1 else 0) := by
  have himp : gateVal n (exchange C u j k s q) (perm j k i) x = true → gateVal n C i x = true := by
    intro hD
    have hv := exchange_gate_upper C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
      hs hsne hq hqne honly x hupper i hi hD
    by_cases hij : i = j
    · subst i
      rw [or_gate_value C hao j u.val t (by omega) hjop hjinputs x]
      cases hu : wireVal n C u.val x <;> cases hss : wireVal n C s x <;> simp_all
    · simpa only [hij, ite_false] using hv
  cases hD : gateVal n (exchange C u j k s q) (perm j k i) x <;>
    cases hC : gateVal n C i x <;> simp_all

lemma exchange_trueGateCount_le (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (x : Fin n → Bool)
    (hupper : wireVal n C q x = true → (wireVal n C t x && wireVal n C s x) = true) :
    trueGateCount n (exchange C u j k s q) x ≤ trueGateCount n C x := by
  unfold trueGateCount
  rw [exchange_size, sum_perm j k C.size hjk hk]
  apply Finset.sum_le_sum
  intro i hi
  exact exchange_gate_truth_le C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
    hs hsne hq hqne honly x hupper i (Finset.mem_range.mp hi)

lemma exchange_trueGateCount_strict (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (x : Fin n → Bool)
    (hupper : wireVal n C q x = true → (wireVal n C t x && wireVal n C s x) = true)
    (hxu : x u = true) (hxs : wireVal n C s x = false) :
    trueGateCount n (exchange C u j k s q) x < trueGateCount n C x := by
  unfold trueGateCount
  rw [exchange_size, sum_perm j k C.size hjk hk]
  apply Finset.sum_lt_sum
  · intro i hi
    exact exchange_gate_truth_le C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
      hs hsne hq hqne honly x hupper i (Finset.mem_range.mp hi)
  · refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
    have hfalse : gateVal n (exchange C u j k s q) (perm j k j) x = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have hv := exchange_gate_upper C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
        hs hsne hq hqne honly x hupper j (by omega) ht
      simp [hxs] at hv
    rw [hfalse, or_gate_value C hao j u.val t (by omega) hjop hjinputs x]
    simp [wireVal_lt C u.val u.isLt, hxu]

lemma exchange_trueGateCount_singleton_strict (C : Circuit) (hao : IsAO2 n C)
    (u : Fin n) (j k t s q : ℕ) (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (hsole : ∀ i < C.size, i ≠ j → u.val ∉ (gateAt C i).inputs)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (hupper : wireVal n C q (pairInput u u) = true →
      (wireVal n C t (pairInput u u) && wireVal n C s (pairInput u u)) = true) :
    trueGateCount n (exchange C u j k s q) (pairInput u u) <
      trueGateCount n C (pairInput u u) := by
  have hsmem : s ∈ (gateAt C k).inputs := by
    rcases hkinputs with h | h <;> simp [h]
  have hzero := PrivateSuccessorSingleton.other_operand_singleton_false C hao u j k s
    hjk hk hsole honly hs hsne hsmem
  exact exchange_trueGateCount_strict C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
    hs hsne hq hqne honly (pairInput u u) hupper (by simp [pairInput]) hzero

end PEqualNP.Outside.L_meta_3566.WeakProductExchange


namespace PEqualNP.Outside.L_meta_3566.WeakProductExchange

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_3566.Pruning
open PEqualNP.Outside.L_meta_3566.AndRotation
open PEqualNP.Outside.L_meta_3566.AvailableProductExchange

variable {n : ℕ}

lemma exchange_negativeAnds_card_le (C : Circuit) (hao : IsAO2 n C)
    (F : (Fin n → Bool) → Bool) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (hnegative : ∀ x : Fin n → Bool, F x = false → wireVal n C q x = true →
      (wireVal n C t x && wireVal n C s x) = true) :
    (negativeAnds n (exchange C u j k s q) F).card ≤ (negativeAnds n C F).card := by
  classical
  let D := exchange C u j k s q
  let f : ℕ → ℕ := fun i => Equiv.swap j k (inv j k i)
  have hfinj : Function.Injective f := by
    intro a b he
    have hinv := (Equiv.swap j k).injective he
    have hh := congrArg (perm j k) hinv
    simpa only [perm_inv j k a hjk, perm_inv j k b hjk] using hh
  have hsub : (negativeAnds n D F).image f ⊆ negativeAnds n C F := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hiD, hop, x, hFx, hx⟩ := (mem_negativeAnds D F i).mp hi
    have hiC : i < C.size := by simpa only [D, exchange_size] using hiD
    let a := inv j k i
    have ha : a < C.size := inv_lt j k C.size i hjk hk hiC
    have hpi : perm j k a = i := perm_inv j k i hjk
    have htag := exchange_op_at_perm C u j k s q a hjk hk ha
    rw [hpi] at htag
    have hupper := exchange_wire_upper C hao u j k t s q hjk hk hjop hjinputs hkop hkinputs
      hs hsne hq hqne honly x (hnegative x hFx) (n + a) (by omega)
    rw [rename_gate, hpi] at hupper
    have hval : (if a = j then wireVal n C u.val x && wireVal n C s x
        else gateVal n C a x) = true := by
      simpa only [gateVal, wireVal, Nat.add_left_cancel_iff] using hupper hx
    by_cases haj : a = j
    · have hf : f i = k := by
        change Equiv.swap j k a = k
        simp [haj]
      rw [hf]
      apply (mem_negativeAnds C F k).mpr
      refine ⟨hk, hkop, x, hFx, ?_⟩
      have hnew : (wireVal n C u.val x && wireVal n C s x) = true := by
        simpa only [haj, ite_true] using hval
      exact new_and_implies_old_and C hao u j k t s hjk hk hjop hjinputs hkop hkinputs x hnew
    · by_cases hak : a = k
      · have hfalse : GateOp.or = GateOp.and := by
          simpa only [hak, Nat.ne_of_gt hjk, ite_false, ite_true] using htag.symm.trans hop
        cases hfalse
      · have hf : f i = a := by
          change Equiv.swap j k a = a
          simp [Equiv.swap_apply_def, haj, hak]
        rw [hf]
        apply (mem_negativeAnds C F a).mpr
        refine ⟨ha, ?_, x, hFx, ?_⟩
        · simpa only [haj, hak, ite_false] using htag.symm.trans hop
        · simpa only [haj, ite_false] using hval
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hfinj] using hc

end PEqualNP.Outside.L_meta_3566.WeakProductExchange

namespace PEqualNP.Outside.L_meta_3566.WeakAvailableProductWireMass

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open Pruning AvailableProductExchange AvailableProductWireMass

variable {n : ℕ}

lemma exchange_negative_mass_strict (F : (Fin n → Bool) → Bool)
    (C : Circuit) (hao : IsAO2 n C) (u : Fin n) (j k t s q : ℕ)
    (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (hsole : ∀ i < C.size, i ≠ j → u.val ∉ (gateAt C i).inputs)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (hnegative : ∀ x, F x = false → wireVal n C q x = true →
      (wireVal n C t x && wireVal n C s x) = true)
    (hunit : F (pairInput u u) = false) :
    negativeMass F (exchange C u j k s q) < negativeMass F C := by
  classical
  unfold negativeMass
  apply Finset.sum_lt_sum
  · intro x hx
    by_cases hFx : F x = false
    · simp only [hFx, ite_true]
      apply wire_count_le
      exact WeakProductExchange.exchange_trueGateCount_le C hao u j k t s q hjk hk
        hjop hjinputs hkop hkinputs hs hsne hq hqne honly x (hnegative x hFx)
    · simp [hFx]
  · refine ⟨pairInput u u, Finset.mem_univ _, ?_⟩
    simp only [hunit, ite_true]
    apply wire_count_lt
    exact WeakProductExchange.exchange_trueGateCount_singleton_strict C hao u j k t s q hjk hk
      hjop hjinputs hkop hkinputs hs hsne hq hqne hsole honly (hnegative _ hunit)

lemma same_size_graph_improvement (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (u : Fin n) (j k t s q : ℕ) (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j) (hq : q < n + k) (hqne : q ≠ n + j)
    (hsole : ∀ i < C.size, i ≠ j → u.val ∉ (gateAt C i).inputs)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (hnegative : ∀ x, graphFun G ∅ x = false → wireVal n C q x = true →
      (wireVal n C t x && wireVal n C s x) = true)
    (hedges : ∀ a b, G.Adj a b → a ≠ u → b ≠ u →
      (wireVal n C t (pairInput a b) && wireVal n C s (pairInput a b)) = true →
      wireVal n C q (pairInput a b) = true)
    (hout : C.output < n + C.size) (houtj : C.output ≠ n + j) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size ∧ circuitFun n D = graphFun G ∅ ∧
      (negativeAnds n D (graphFun G ∅)).card ≤ (negativeAnds n C (graphFun G ∅)).card ∧
      negativeMass (graphFun G ∅) D < negativeMass (graphFun G ∅) C := by
  have hunit : graphFun G ∅ (pairInput u u) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact G.irrefl ((SingleRead.graph_pair G u u).mp h)
  refine ⟨exchange C u j k s q, ?_, exchange_size C u j k s q, ?_, ?_, ?_⟩
  · exact exchange_ao C hao u j k s q hjk hk hs hsne hq hqne honly
  · exact WeakProductExchange.exchange_graphFun G C hao hfun u j k t s q hjk hk
      hjop hjinputs hkop hkinputs hs hsne hq hqne honly hnegative hedges hout houtj
  · exact WeakProductExchange.exchange_negativeAnds_card_le C hao (graphFun G ∅)
      u j k t s q hjk hk hjop hjinputs hkop hkinputs hs hsne hq hqne honly hnegative
  · exact exchange_negative_mass_strict (graphFun G ∅) C hao u j k t s q hjk hk
      hjop hjinputs hkop hkinputs hs hsne hq hqne hsole honly hnegative hunit

end PEqualNP.Outside.L_meta_3566.WeakAvailableProductWireMass


namespace PEqualNP.Outside.L_meta_3566.LeastOutputValidity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge
open Pruning

variable {n : ℕ}

lemma least_output_upper_of_size_pos (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hsize : 0 < C.size) :
    C.output < n + C.size := by
  by_contra hbad
  have hfalse (x : Fin n → Bool) : circuitFun n C x = false := by
    have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
      unfold Circuit.wires
      rw [wires_length, List.length_ofFn]
      rfl
    change (C.wires (List.ofFn x)).getD C.output false = false
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega :
      (C.wires (List.ofFn x)).length ≤ C.output)]
  let D : Circuit := ⟨[], n⟩
  have hD : IsAO2 n D := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp [D] at hg
    · intro j hj
      simp [D] at hj
    · intro g hg
      simp [D] at hg
  have hDfalse (x : Fin n → Bool) : circuitFun n D x = false := by
    simp [D, circuitFun, Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]
  have hDfun : circuitFun n D = graphFun G ∅ := by
    rw [← hC.2.1]
    funext x
    exact (hDfalse x).trans (hfalse x).symm
  have hminimal := hC.2.2 D hD hDfun
  have hDsize : D.size = 0 := rfl
  rw [hDsize] at hminimal
  omega

end PEqualNP.Outside.L_meta_3566.LeastOutputValidity

namespace PEqualNP.Outside.L_meta_3566.WeakAvailableProductWitness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open Pruning AvailableProductExchange AvailableProductWireMass

variable {n : ℕ}

lemma negative_separation_of_output_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (hmin : ∀ D : Circuit, IsLeastAO G D → negativeMass (graphFun G ∅) C ≤ negativeMass (graphFun G ∅) D)
    (u : Fin n) (j k t s : ℕ) (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j)
    (hsole : ∀ i < C.size, i ≠ j → u.val ∉ (gateAt C i).inputs)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs)
    (hout : C.output < n + C.size) :
    ∃ x : Fin n → Bool, graphFun G ∅ x = false ∧
      wireVal n C t x = true ∧ wireVal n C s x = false := by
  classical
  have htmem : t ∈ (gateAt C j).inputs := by
    rcases hjinputs with h | h <;> simp [h]
  have ht : t < n + j := hC.1.2.1 j (by simpa only [Circuit.size] using Nat.lt_trans hjk hk) t htmem
  have houtj : C.output ≠ n + j := by
    intro he
    have hv := or_gate_value C hC.1 j u.val t (by omega) hjop hjinputs (pairInput u u)
    have hfalse : graphFun G ∅ (pairInput u u) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      exact G.irrefl ((SingleRead.graph_pair G u u).mp h)
    have hfun := congrFun hC.2.1 (pairInput u u)
    change wireVal n C C.output (pairInput u u) = _ at hfun
    rw [he] at hfun
    change gateVal n C j (pairInput u u) = _ at hfun
    rw [hv, wireVal_lt C u.val u.isLt] at hfun
    simp [pairInput, hfalse] at hfun
  by_contra hno
  have hnegative : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      wireVal n C t x = true → (wireVal n C t x && wireVal n C s x) = true := by
    intro x hFx htx
    have hsx : wireVal n C s x = true := by
      cases hf : wireVal n C s x with
      | false => exact False.elim (hno ⟨x, hFx, htx, hf⟩)
      | true => rfl
    simp [htx, hsx]
  obtain ⟨D, hD, hsize, hfun, hjunk, hmass⟩ :=
    WeakAvailableProductWireMass.same_size_graph_improvement G C hC.1 hC.2.1 u j k t s t
      hjk hk hjop hjinputs hkop hkinputs hs hsne (by omega) (by omega) hsole honly
      hnegative (by intro a b hab hau hbu hts; cases ht : wireVal n C t (pairInput a b) <;> simp_all) hout houtj
  have hDleast : IsLeastAO G D := by
    refine ⟨hD, hfun, ?_⟩
    intro E hE hEF
    rw [hsize]
    exact hC.2.2 E hE hEF
  exact (Nat.not_lt_of_ge (hmin D hDleast)) hmass


lemma negative_separation (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (hmin : ∀ D : Circuit, IsLeastAO G D → negativeMass (graphFun G ∅) C ≤ negativeMass (graphFun G ∅) D)
    (u : Fin n) (j k t s : ℕ) (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j)
    (hsole : ∀ i < C.size, i ≠ j → u.val ∉ (gateAt C i).inputs)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs) :
    ∃ x : Fin n → Bool, graphFun G ∅ x = false ∧
      wireVal n C t x = true ∧ wireVal n C s x = false := by
  exact negative_separation_of_output_bound G C hC hmin u j k t s hjk hk
    hjop hjinputs hkop hkinputs hs hsne hsole honly
    (LeastOutputValidity.least_output_upper_of_size_pos G C hC (by omega))

end PEqualNP.Outside.L_meta_3566.WeakAvailableProductWitness
namespace PEqualNP.Outside.L_meta_3566.WeakAvailableProductWitness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open Pruning AvailableProductExchange AvailableProductWireMass

variable {n : ℕ}

lemma negative_separation_reverse (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C)
    (hmin : ∀ D : Circuit, IsLeastAO G D → negativeMass (graphFun G ∅) C ≤ negativeMass (graphFun G ∅) D)
    (u : Fin n) (j k t s : ℕ) (hjk : j < k) (hk : k < C.size)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjinputs : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkinputs : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hs : s < n + k) (hsne : s ≠ n + j)
    (hsole : ∀ i < C.size, i ≠ j → u.val ∉ (gateAt C i).inputs)
    (honly : ∀ a < C.size, a ≠ k → n + j ∉ (gateAt C a).inputs) :
    ∃ x : Fin n → Bool, graphFun G ∅ x = false ∧
      wireVal n C s x = true ∧ wireVal n C t x = false := by
  classical
  have hout := LeastOutputValidity.least_output_upper_of_size_pos G C hC (by omega)
  have houtj : C.output ≠ n + j := by
    intro he
    have hv := or_gate_value C hC.1 j u.val t (by omega) hjop hjinputs (pairInput u u)
    have hfalse : graphFun G ∅ (pairInput u u) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      exact G.irrefl ((SingleRead.graph_pair G u u).mp h)
    have hfun := congrFun hC.2.1 (pairInput u u)
    change wireVal n C C.output (pairInput u u) = _ at hfun
    rw [he] at hfun
    change gateVal n C j (pairInput u u) = _ at hfun
    rw [hv, wireVal_lt C u.val u.isLt] at hfun
    simp [pairInput, hfalse] at hfun
  by_contra hno
  have hnegative : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      wireVal n C s x = true → (wireVal n C t x && wireVal n C s x) = true := by
    intro x hFx hsx
    have htx : wireVal n C t x = true := by
      cases hf : wireVal n C t x with
      | false => exact False.elim (hno ⟨x, hFx, hsx, hf⟩)
      | true => rfl
    simp [htx, hsx]
  obtain ⟨D, hD, hsize, hfun, hjunk, hmass⟩ :=
    WeakAvailableProductWireMass.same_size_graph_improvement G C hC.1 hC.2.1 u j k t s s
      hjk hk hjop hjinputs hkop hkinputs hs hsne hs hsne hsole honly
      hnegative (by intro a b hab hau hbu hts; cases ht : wireVal n C s (pairInput a b) <;> simp_all) hout houtj
  have hDleast : IsLeastAO G D := by
    refine ⟨hD, hfun, ?_⟩
    intro E hE hEF
    rw [hsize]
    exact hC.2.2 E hE hEF
  exact (Nat.not_lt_of_ge (hmin D hDleast)) hmass

end PEqualNP.Outside.L_meta_3566.WeakAvailableProductWitness


namespace PEqualNP.Outside.L_meta_3566.SoleOrColor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open Pruning SingleRead

variable {n : ℕ}

lemma covering_pair_same_colors (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Bool) (hc : ∀ v w, G.Adj v w → c v ≠ c w)
    (hfour : NoFourCycle G) (u a b : Fin n) (hau : a ≠ u) (hbu : b ≠ u)
    (hdeg : 2 ≤ G.degree u)
    (hcover : ∀ w, G.Adj u w → G.Adj a w ∨ G.Adj b w) :
    c a = c u ∧ c b = c u := by
  have one (a b : Fin n) (hbu : b ≠ u)
      (hcover : ∀ w, G.Adj u w → G.Adj a w ∨ G.Adj b w) : c a = c u := by
    by_contra hne
    have hsub : G.neighborFinset u ⊆
        Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj b w) := by
      intro w hw
      have huw := (G.mem_neighborFinset u w).mp hw
      have hbw : G.Adj b w := by
        rcases hcover w huw with haw | hbw
        · have huv := hc u w huw
          have hav := hc a w haw
          cases hcu : c u <;> cases hca : c a <;> cases hcw : c w <;> simp_all
        · exact hbw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, huw, hbw⟩
    have hh := (Finset.card_le_card hsub).trans (hfour u b (Ne.symm hbu))
    rw [G.card_neighborFinset_eq_degree] at hh
    omega
  exact ⟨one a b hbu hcover, one b a hau (fun w hw => (hcover w hw).symm)⟩

lemma accepted_nonedge_pair_colors (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Bool) (hc : ∀ v w, G.Adj v w → c v ≠ c w)
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (hdeg : 2 ≤ G.degree u) (htu : t ≠ u.val)
    (a b : Fin n) (hab : ¬ G.Adj a b)
    (hs : wireVal n C t (pairInput a b) = true) :
    a ≠ u ∧ b ≠ u ∧ c a = c u ∧ c b = c u := by
  have htmem : t ∈ g.inputs := by rcases hinputs with h | h <;> simp [h]
  have hempty := arbitrary_or_other_singletons_empty G C u pre post g t hshape hop hinputs
    hao hno hfun hfour hdeg htu
  change ∀ v : Fin n, wireVal n C t (pairInput v v) = false at hempty
  have hau : a ≠ u := by
    intro he
    subst a
    have hbtrue : wireVal n C t (pairInput b b) = true := by
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
    have hatrue : wireVal n C t (pairInput a a) = true := by
      apply other_wire_compare C u pre post g t hshape htmem hao hno htu
        (pairInput a u) (pairInput a a) _ hs
      intro i hi hp
      simp only [pairInput, decide_eq_true_eq] at hp ⊢
      rcases hp with hp | hp
      · exact Or.inl hp
      · exact False.elim (hi hp)
    rw [hempty a] at hatrue
    cases hatrue
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
  exact ⟨hau, hbu, covering_pair_same_colors G c hc hfour u a b hau hbu hdeg hcover⟩

lemma raw_product_has_one_u_side (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Bool) (hc : ∀ v w, G.Adj v w → c v ≠ c w)
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G)
    (hdeg : 2 ≤ G.degree u) (htu : t ≠ u.val)
    (A B : Finset (Fin n))
    (hprod : ∀ a ∈ A, ∀ b ∈ B, wireVal n C t (pairInput a b) = true) :
    (∀ a ∈ A, c a = c u) ∨ (∀ b ∈ B, c b = c u) := by
  classical
  by_cases hA : ∀ a ∈ A, c a = c u
  · exact Or.inl hA
  · right
    push Not at hA
    obtain ⟨a, ha, hca⟩ := hA
    intro b hb
    by_contra hcb
    have hcolor : c a = c b := by
      cases hua : c u <;> cases haa : c a <;> cases hbb : c b <;> simp_all
    have hab : ¬ G.Adj a b := by
      intro hab
      exact hc a b hab hcolor
    obtain ⟨_, _, hleft, _⟩ := accepted_nonedge_pair_colors G c hc C u pre post g t
      hshape hop hinputs hao hno hfun hfour hdeg htu a b hab (hprod a ha b hb)
    exact hca hleft

end PEqualNP.Outside.L_meta_3566.SoleOrColor

namespace PEqualNP.Outside.L_meta_3566.SoleAndSetZero

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge
open Pruning SingleRead ANDRotationEvaluation

variable {n : ℕ}

lemma internal_false_of_reader_condition (C : Circuit) (hao : IsAO2 n C)
    (S : Finset (Fin n))
    (hread : ∀ i < C.size, ∀ u ∈ S, u.val ∈ (gateAt C i).inputs →
      (gateAt C i).op = GateOp.and ∧ ∃ t ∈ (gateAt C i).inputs, n ≤ t) :
    ∀ w, n ≤ w → w < n + C.size → wireVal n C w (setInput S) = false := by
  classical
  let V : ℕ → Bool := fun w => if h : w < n then setInput S ⟨w, h⟩ else false
  have hVzero (w : ℕ) (hw : n ≤ w) : V w = false := by
    simp [V, Nat.not_lt.mpr hw]
  have hVtrue (w : ℕ) (hw : V w = true) : ∃ u ∈ S, u.val = w := by
    by_cases hn : w < n
    · refine ⟨⟨w, hn⟩, ?_, rfl⟩
      simpa [V, hn, setInput] using hw
    · simp [V, hn] at hw
  have hinput (u : Fin n) : V u.val = setInput S u := by
    simp [V, u.isLt]
  have hgate (i : ℕ) (hi : i < C.size) :
      V (n + i) = (gateAt C i).op.eval ((gateAt C i).inputs.map V) := by
    rw [hVzero (n + i) (by omega)]
    symm
    apply Bool.eq_false_iff.mpr
    intro ht
    have hmem : gateAt C i ∈ C.gates := by
      exact List.mem_of_getElem? (show C.gates[i]? = some (gateAt C i) by
        simp [gateAt, List.getD_eq_getElem?_getD, show i < C.gates.length from hi])
    rcases hao.1 _ hmem with hand | hor
    · have hall : ∀ a ∈ (gateAt C i).inputs, V a = true := by
        simpa only [hand, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] using ht
      obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (hao.2.2 _ hmem)
      have hamem : a ∈ (gateAt C i).inputs := by simp [hin]
      obtain ⟨u, hu, hua⟩ := hVtrue a (hall a hamem)
      have humem : u.val ∈ (gateAt C i).inputs := by simpa only [hua] using hamem
      obtain ⟨hop, t, htm, htn⟩ := hread i hi u hu humem
      have htv := hall t htm
      rw [hVzero t htn] at htv
      cases htv
    · have hex : ∃ a ∈ (gateAt C i).inputs, V a = true := by
        simpa only [hor, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] using ht
      obtain ⟨a, ha, hVa⟩ := hex
      obtain ⟨u, hu, hua⟩ := hVtrue a hVa
      have humem : u.val ∈ (gateAt C i).inputs := by simpa only [hua] using ha
      have hbad := (hread i hi u hu humem).1
      rw [hor] at hbad
      cases hbad
  intro w hn hw
  exact (wireVal_eq_of_solution C hao (setInput S) V hinput hgate w hw).trans (hVzero w hn)

end PEqualNP.Outside.L_meta_3566.SoleAndSetZero


namespace PEqualNP.Outside.L_meta_3566.SoleAndGateCondition

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open Pruning SoleAnd

variable {n : ℕ}

lemma sole_and_reader_gate (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (u : Fin n) (hreader : SoleAndReader C u) (hdeg : 2 ≤ G.degree u)
    (i : ℕ) (hi : i < C.size) (hread : u.val ∈ (gateAt C i).inputs) :
    (gateAt C i).op = GateOp.and ∧ ∃ t ∈ (gateAt C i).inputs, n ≤ t := by
  obtain ⟨pre, post, g, t, hshape, hand, hin, htu, hno⟩ := hreader
  have heq : gateAt C i = g := by
    have hmem : gateAt C i ∈ C.gates := by
      exact List.mem_of_getElem? (show C.gates[i]? = some (gateAt C i) by
        simp [gateAt, List.getD_eq_getElem?_getD, show i < C.gates.length from hi])
    rw [hshape] at hmem
    rcases List.mem_append.mp hmem with hpre | htail
    · exact False.elim (hno _ (List.mem_append_left _ hpre) hread)
    · rcases List.mem_cons.mp htail with he | hpost
      · exact he
      · exact False.elim (hno _ (List.mem_append_right _ hpost) hread)
  have htn : n ≤ t := by
    by_contra hbad
    let v : Fin n := ⟨t, by omega⟩
    have huv : u ≠ v := by
      intro he
      exact htu (congrArg Fin.val he.symm)
    have hd := NoRawReader.sole_and_raw_degree G C u v pre post g hshape hand hin
      hao hno hfun huv
    omega
  refine ⟨by rw [heq]; exact hand, t, ?_, htn⟩
  rw [heq]
  rcases hin with hin | hin <;> simp [hin]

lemma sole_and_set_gate_condition (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (S : Finset (Fin n)) (hS : ∀ u ∈ S, SoleAndReader C u)
    (hdeg : ∀ u ∈ S, 2 ≤ G.degree u) :
    ∀ i < C.size, ∀ u ∈ S, u.val ∈ (gateAt C i).inputs →
      (gateAt C i).op = GateOp.and ∧ ∃ t ∈ (gateAt C i).inputs, n ≤ t := by
  intro i hi u hu hread
  exact sole_and_reader_gate G C hao hfun u (hS u hu) (hdeg u hu) i hi hread

end PEqualNP.Outside.L_meta_3566.SoleAndGateCondition

namespace PEqualNP.Outside.L_meta_3566.SoleAndSetZero

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge
open Pruning SingleRead SoleAnd

variable {n : ℕ}

lemma internal_false_on_sole_and_set (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (S : Finset (Fin n)) (hS : ∀ u ∈ S, SoleAndReader C u)
    (hdeg : ∀ u ∈ S, 2 ≤ G.degree u) :
    ∀ w, n ≤ w → w < n + C.size → wireVal n C w (setInput S) = false := by
  exact internal_false_of_reader_condition C hao S
    (SoleAndGateCondition.sole_and_set_gate_condition G C hao hfun S hS hdeg)

lemma accepted_internal_has_nonsole_and (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (S : Finset (Fin n)) (hdeg : ∀ u ∈ S, 2 ≤ G.degree u)
    (w : ℕ) (hwn : n ≤ w) (hw : w < n + C.size)
    (htrue : wireVal n C w (setInput S) = true) :
    ∃ u ∈ S, ¬ SoleAndReader C u := by
  classical
  by_contra hno
  have hS : ∀ u ∈ S, SoleAndReader C u := by
    intro u hu
    by_contra hbad
    exact hno ⟨u, hu, hbad⟩
  have hfalse := internal_false_on_sole_and_set G C hao hfun S hS hdeg w hwn hw
  rw [hfalse] at htrue
  cases htrue

end PEqualNP.Outside.L_meta_3566.SoleAndSetZero

namespace PEqualNP.Outside.L_meta_3566.SoleOrColorSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open Pruning SingleRead
open scoped BigOperators

variable {n : ℕ}

lemma same_color_of_common_neighbor (G : SimpleGraph (Fin n))
    (c : Fin n → Bool) (hc : ∀ v w, G.Adj v w → c v ≠ c w)
    (u a w : Fin n) (huw : G.Adj u w) (haw : G.Adj a w) : c a = c u := by
  have hu := hc u w huw
  have ha := hc a w haw
  cases hcu : c u <;> cases hca : c a <;> cases hcw : c w <;> simp_all

lemma color_cover_injection (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Bool) (hc : ∀ v w, G.Adj v w → c v ≠ c w)
    (hfour : NoFourCycle G) (u : Fin n) (S : Finset (Fin n)) (huS : u ∉ S)
    (hcover : ∀ w, G.Adj u w → ∃ a ∈ S, G.Adj a w) :
    ∃ f : {w : Fin n // G.Adj u w} → {a : Fin n // a ∈ S.filter (fun a => c a = c u)},
      Function.Injective f ∧ ∀ w, G.Adj (f w).val w.val := by
  classical
  have hcov (w : {w : Fin n // G.Adj u w}) :
      ∃ a : Fin n, a ∈ S.filter (fun a => c a = c u) ∧ G.Adj a w.val := by
    obtain ⟨a, ha, haw⟩ := hcover w.val w.property
    exact ⟨a, Finset.mem_filter.mpr
      ⟨ha, same_color_of_common_neighbor G c hc u a w.val w.property haw⟩, haw⟩
  choose f hf using hcov
  let F : {w : Fin n // G.Adj u w} → {a : Fin n // a ∈ S.filter (fun a => c a = c u)} :=
    fun w => ⟨f w, (hf w).1⟩
  refine ⟨F, ?_, fun w => (hf w).2⟩
  intro w z he
  have hsame : f w = f z := congrArg Subtype.val he
  apply Subtype.ext
  have hua : u ≠ f w := by
    intro heq
    exact huS (heq ▸ (Finset.mem_filter.mp (hf w).1).1)
  apply (Finset.card_le_one.mp (hfour u (f w) hua)) w.val
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w.property, (hf w).2⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨z.property, hsame ▸ (hf z).2⟩

lemma degree_le_color_cover (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Bool) (hc : ∀ v w, G.Adj v w → c v ≠ c w)
    (hfour : NoFourCycle G) (u : Fin n) (S : Finset (Fin n)) (huS : u ∉ S)
    (hcover : ∀ w, G.Adj u w → ∃ a ∈ S, G.Adj a w) :
    G.degree u ≤ (S.filter fun a => c a = c u).card := by
  let T := S.filter fun a => c a = c u
  let A : Fin n → Finset (Fin n) := fun a => Finset.univ.filter fun w => G.Adj u w ∧ G.Adj a w
  have hsub : G.neighborFinset u ⊆ T.biUnion A := by
    intro w hw
    have huw := (G.mem_neighborFinset u w).mp hw
    obtain ⟨a, ha, haw⟩ := hcover w huw
    have haT : a ∈ T := Finset.mem_filter.mpr
      ⟨ha, same_color_of_common_neighbor G c hc u a w huw haw⟩
    exact Finset.mem_biUnion.mpr ⟨a, haT, by simp [A, huw, haw]⟩
  have hsum : (∑ a ∈ T, (A a).card) ≤ ∑ a ∈ T, 1 := by
    apply Finset.sum_le_sum
    intro a ha
    apply hfour u a
    intro he
    have haS : a ∈ S := (Finset.mem_filter.mp ha).1
    exact huS (he ▸ haS)
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  rw [G.card_neighborFinset_eq_degree] at hcard
  exact hcard.trans (by simpa only [Finset.sum_const, smul_eq_mul, mul_one] using hsum)

lemma sole_or_independent_support_color_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Bool) (hc : ∀ v w, G.Adj v w → c v ≠ c w)
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G) (htu : t ≠ u.val)
    (S : Finset (Fin n)) (huS : u ∉ S) (hind : ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b)
    (hs : wireVal n C t (setInput S) = true) :
    G.degree u ≤ (S.filter fun a => c a = c u).card := by
  have htmem : t ∈ g.inputs := by rcases hinputs with h | h <;> simp [h]
  apply degree_le_color_cover G c hc hfour u S huS
  intro w huw
  apply graph_insert_independent G S hind w
  apply sole_or_neighbor_multiplier G C u pre post g t hshape hop hinputs hao hno hfun w huw
  · apply other_wire_compare C u pre post g t hshape htmem hao hno htu
      (setInput S) (setInput (insert w S)) _ hs
    intro i _ hi
    simp only [setInput, decide_eq_true_eq] at hi ⊢
    exact Finset.mem_insert_of_mem hi
  · simp [setInput]

lemma sole_or_independent_support_erase_color_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Bool) (hc : ∀ v w, G.Adj v w → c v ≠ c w)
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (hfour : NoFourCycle G) (htu : t ≠ u.val)
    (S : Finset (Fin n)) (hind : ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b)
    (hs : wireVal n C t (setInput S) = true) :
    G.degree u ≤ ((S.erase u).filter fun a => c a = c u).card := by
  have htmem : t ∈ g.inputs := by rcases hinputs with h | h <;> simp [h]
  apply sole_or_independent_support_color_bound G c hc C u pre post g t hshape hop hinputs
    hao hno hfun hfour htu (S.erase u) (by simp)
  · intro a ha b hb
    exact hind a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
  · apply other_wire_compare C u pre post g t hshape htmem hao hno htu
      (setInput S) (setInput (S.erase u)) _ hs
    intro i hi hS
    simp only [setInput, decide_eq_true_eq] at hS ⊢
    exact Finset.mem_erase.mpr ⟨hi, hS⟩

end PEqualNP.Outside.L_meta_3566.SoleOrColorSupport

namespace PEqualNP.Outside.L_meta_3566.NegativeMetrics

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

lemma negativeAnds_eq_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) :
    AvailableProductExchange.negativeAnds n C (graphFun G ∅) = PEqualNP.TopForm.junk G C := by
  classical
  ext i
  simp [AvailableProductExchange.negativeAnds, PEqualNP.TopForm.junk,
    PEqualNP.TopForm.gatesWhere, PEqualNP.CleanedNonEdge.IsDirtyAnd,
    PEqualNP.CleanedNonEdge.IsDirty, Circuit.size, and_left_comm, and_comm]

end PEqualNP.Outside.L_meta_3566.NegativeMetrics
