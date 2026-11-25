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

namespace PEqualNP.Outside.L_meta_3566.InPlaceAndReassociate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge
open Pruning ANDRotationEvaluation AndRotation

variable {n : ℕ}

def newGate (n : ℕ) (C : Circuit) (q k A B R i : ℕ) : Gate :=
  if i = q then ⟨GateOp.and, [A, R]⟩
  else if i = k then ⟨GateOp.and, [n + q, B]⟩
  else gateAt C i

def reassoc (n : ℕ) (C : Circuit) (q k A B R : ℕ) : Circuit :=
  ⟨List.ofFn (fun i : Fin C.size => newGate n C q k A B R i.val), C.output⟩

lemma reassoc_size (C : Circuit) (q k A B R : ℕ) :
    (reassoc n C q k A B R).size = C.size := by simp [reassoc, Circuit.size]

lemma reassoc_gateAt (C : Circuit) (q k A B R i : ℕ) (hi : i < C.size) :
    gateAt (reassoc n C q k A B R) i = newGate n C q k A B R i := by
  simp [reassoc, gateAt, List.getD_eq_getElem?_getD, hi]

lemma reassoc_ao (C : Circuit) (hao : IsAO2 n C) (q k A B R : ℕ)
    (hqk : q < k) (_hk : k < C.size)
    (hA : A < n + q) (hB : B < n + q) (hR : R < n + q) :
    IsAO2 n (reassoc n C q k A B R) := by
  have hOp (i : ℕ) (hi : i < C.size) :
      (newGate n C q k A B R i).op = GateOp.and ∨
      (newGate n C q k A B R i).op = GateOp.or := by
    unfold newGate
    split_ifs
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact hao.1 _ (old_gate_mem C i hi)
  have hLen (i : ℕ) (hi : i < C.size) :
      (newGate n C q k A B R i).inputs.length = 2 := by
    unfold newGate
    split_ifs
    · rfl
    · rfl
    · exact hao.2.2 _ (old_gate_mem C i hi)
  have hBack (i : ℕ) (hi : i < C.size) (w : ℕ)
      (hw : w ∈ (newGate n C q k A B R i).inputs) : w < n + i := by
    unfold newGate at hw
    split_ifs at hw with hiq hik
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> omega
    · exact hao.2.1 i hi w hw
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact hOp i.val i.isLt
  · intro i hi w hw
    change i < (reassoc n C q k A B R).size at hi
    rw [reassoc_size] at hi
    change w ∈ (gateAt (reassoc n C q k A B R) i).inputs at hw
    rw [reassoc_gateAt C q k A B R i hi] at hw
    exact hBack i hi w hw
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    exact hLen i.val i.isLt

def model (C : Circuit) (q A R : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  if w = n + q then wireVal n C A x && wireVal n C R x else wireVal n C w x

lemma model_eq_before (C : Circuit) (q A R : ℕ) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n + q) : model C q A R x w = wireVal n C w x := by
  simp [model, Nat.ne_of_lt hw]

lemma reassoc_model (C : Circuit) (hao : IsAO2 n C) (q k A B R : ℕ)
    (hqk : q < k) (hk : k < C.size)
    (hqop : (gateAt C q).op = GateOp.and)
    (hqin : (gateAt C q).inputs = [A, B] ∨ (gateAt C q).inputs = [B, A])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkin : (gateAt C k).inputs = [n + q, R] ∨ (gateAt C k).inputs = [R, n + q])
    (hA : A < n + q) (hB : B < n + q) (hR : R < n + q)
    (honly : ∀ i < C.size, i ≠ k → n + q ∉ (gateAt C i).inputs)
    (x : Fin n → Bool) :
    ∀ i < C.size, model C q A R x (n + i) =
      (newGate n C q k A B R i).op.eval
        ((newGate n C q k A B R i).inputs.map (model C q A R x)) := by
  intro i hi
  by_cases hiq : i = q
  · subst i
    simp [newGate, model, Nat.ne_of_lt hA, Nat.ne_of_lt hR, GateOp.eval]
  by_cases hik : i = k
  · subst i
    have hqv := and_gate_value C hao q A B (by omega) hqop hqin x
    have hkv := and_gate_value C hao k (n + q) R hk hkop hkin x
    have hqwire : wireVal n C (n + q) x = (wireVal n C A x && wireVal n C B x) := hqv
    have hkwire : wireVal n C (n + k) x =
        ((wireVal n C A x && wireVal n C B x) && wireVal n C R x) := by
      change gateVal n C k x = _
      rw [hkv, hqwire]
    simp [newGate, model, Nat.ne_of_gt hqk, Nat.ne_of_lt hB,
      hkwire, GateOp.eval, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
  · rw [show model C q A R x (n + i) = gateVal n C i x by simp [model, hiq, wireVal, gateVal]]
    rw [gate_eq_eval C hao i hi x]
    simp only [newGate, hiq, hik, ite_false]
    congr 1
    apply List.map_congr_left
    intro w hw
    have hwq : w ≠ n + q := by intro he; exact honly i hi hik (he ▸ hw)
    simp [model, hwq]

lemma reassoc_wire_valid (C : Circuit) (hao : IsAO2 n C) (q k A B R : ℕ)
    (hqk : q < k) (hk : k < C.size)
    (hqop : (gateAt C q).op = GateOp.and)
    (hqin : (gateAt C q).inputs = [A, B] ∨ (gateAt C q).inputs = [B, A])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkin : (gateAt C k).inputs = [n + q, R] ∨ (gateAt C k).inputs = [R, n + q])
    (hA : A < n + q) (hB : B < n + q) (hR : R < n + q)
    (honly : ∀ i < C.size, i ≠ k → n + q ∉ (gateAt C i).inputs)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n + C.size) :
    wireVal n (reassoc n C q k A B R) w x = model C q A R x w := by
  have hnew := reassoc_ao C hao q k A B R hqk hk hA hB hR
  apply wireVal_eq_of_solution (reassoc n C q k A B R) hnew x (model C q A R x)
  · intro u
    rw [model_eq_before C q A R x u.val (by have hu := u.isLt; omega)]
    exact wireVal_lt C u.val u.isLt x
  · intro i hi
    rw [reassoc_size] at hi
    rw [reassoc_gateAt C q k A B R i hi]
    exact reassoc_model C hao q k A B R hqk hk hqop hqin hkop hkin hA hB hR honly x i hi
  · simpa only [reassoc_size] using hw

lemma wireVal_outside (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : wireVal n C w x = false := by
  have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
    unfold Circuit.wires
    rw [wires_length, List.length_ofFn]
    rfl
  change (C.wires (List.ofFn x)).getD w false = false
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega :
    (C.wires (List.ofFn x)).length ≤ w)]

lemma reassoc_wire (C : Circuit) (hao : IsAO2 n C) (q k A B R : ℕ)
    (hqk : q < k) (hk : k < C.size)
    (hqop : (gateAt C q).op = GateOp.and)
    (hqin : (gateAt C q).inputs = [A, B] ∨ (gateAt C q).inputs = [B, A])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkin : (gateAt C k).inputs = [n + q, R] ∨ (gateAt C k).inputs = [R, n + q])
    (hA : A < n + q) (hB : B < n + q) (hR : R < n + q)
    (honly : ∀ i < C.size, i ≠ k → n + q ∉ (gateAt C i).inputs)
    (x : Fin n → Bool) (w : ℕ) :
    wireVal n (reassoc n C q k A B R) w x =
      if w = n + q then wireVal n C A x && wireVal n C R x else wireVal n C w x := by
  by_cases hw : w < n + C.size
  · exact reassoc_wire_valid C hao q k A B R hqk hk hqop hqin hkop hkin hA hB hR honly x w hw
  · have hwq : w ≠ n + q := by omega
    rw [ite_eq_right hwq, wireVal_outside C x w (by omega),
      wireVal_outside (reassoc n C q k A B R) x w (by rw [reassoc_size]; omega)]

lemma reassoc_fun (C : Circuit) (hao : IsAO2 n C) (q k A B R : ℕ)
    (hqk : q < k) (hk : k < C.size)
    (hqop : (gateAt C q).op = GateOp.and)
    (hqin : (gateAt C q).inputs = [A, B] ∨ (gateAt C q).inputs = [B, A])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkin : (gateAt C k).inputs = [n + q, R] ∨ (gateAt C k).inputs = [R, n + q])
    (hA : A < n + q) (hB : B < n + q) (hR : R < n + q)
    (honly : ∀ i < C.size, i ≠ k → n + q ∉ (gateAt C i).inputs)
    (hout : C.output ≠ n + q) :
    circuitFun n (reassoc n C q k A B R) = circuitFun n C := by
  funext x
  change wireVal n (reassoc n C q k A B R) C.output x = wireVal n C C.output x
  rw [reassoc_wire C hao q k A B R hqk hk hqop hqin hkop hkin hA hB hR honly x C.output,
    ite_eq_right hout]

end PEqualNP.Outside.L_meta_3566.InPlaceAndReassociate

namespace PEqualNP.Outside.L_meta_3566.InPlaceAndReassociate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge
open Pruning AvailableProductExchange
open scoped BigOperators

variable {n : ℕ}

lemma reassoc_gate_values (C : Circuit) (hao : IsAO2 n C) (q k A B R : ℕ)
    (hqk : q < k) (hk : k < C.size)
    (hqop : (gateAt C q).op = GateOp.and)
    (hqin : (gateAt C q).inputs = [A, B] ∨ (gateAt C q).inputs = [B, A])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkin : (gateAt C k).inputs = [n + q, R] ∨ (gateAt C k).inputs = [R, n + q])
    (hA : A < n + q) (hB : B < n + q) (hR : R < n + q)
    (honly : ∀ i < C.size, i ≠ k → n + q ∉ (gateAt C i).inputs)
    (x : Fin n → Bool) (i : ℕ) :
    gateVal n (reassoc n C q k A B R) i x =
      if i = q then wireVal n C A x && wireVal n C R x else gateVal n C i x := by
  have hh := reassoc_wire C hao q k A B R hqk hk hqop hqin hkop hkin hA hB hR honly x (n + i)
  simpa only [gateVal, wireVal, Nat.add_left_cancel_iff] using hh

lemma sum_replace_coordinate (S : Finset ℕ) (q : ℕ) (hq : q ∈ S) (f g : ℕ → ℕ)
    (hsame : ∀ i ∈ S, i ≠ q → f i = g i) :
    (∑ i ∈ S, f i) + g q = (∑ i ∈ S, g i) + f q := by
  have hf := Finset.sum_erase_add S f hq
  have hg := Finset.sum_erase_add S g hq
  have hrest : (∑ i ∈ S.erase q, f i) = ∑ i ∈ S.erase q, g i := by
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨hiq, hiS⟩ := Finset.mem_erase.mp hi
    exact hsame i hiS hiq
  omega

lemma reassoc_trueGateCount_balance (C : Circuit) (hao : IsAO2 n C) (q k A B R : ℕ)
    (hqk : q < k) (hk : k < C.size)
    (hqop : (gateAt C q).op = GateOp.and)
    (hqin : (gateAt C q).inputs = [A, B] ∨ (gateAt C q).inputs = [B, A])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkin : (gateAt C k).inputs = [n + q, R] ∨ (gateAt C k).inputs = [R, n + q])
    (hA : A < n + q) (hB : B < n + q) (hR : R < n + q)
    (honly : ∀ i < C.size, i ≠ k → n + q ∉ (gateAt C i).inputs)
    (x : Fin n → Bool) :
    trueGateCount n (reassoc n C q k A B R) x + FrontierWireCount.bit (gateVal n C q x) =
      trueGateCount n C x + FrontierWireCount.bit (wireVal n C A x && wireVal n C R x) := by
  have hprofile := reassoc_gate_values C hao q k A B R hqk hk hqop hqin hkop hkin hA hB hR honly x
  have hbalance := sum_replace_coordinate (Finset.range C.size) q
    (Finset.mem_range.mpr (by omega))
    (fun i => FrontierWireCount.bit (gateVal n (reassoc n C q k A B R) i x))
    (fun i => FrontierWireCount.bit (gateVal n C i x)) (by
      intro i hi hiq
      rw [hprofile i, ite_eq_right hiq])
  rw [hprofile q, ite_eq_left rfl] at hbalance
  simpa only [trueGateCount, reassoc_size, FrontierWireCount.bit] using hbalance

lemma reassoc_wire_count_balance (C : Circuit) (hao : IsAO2 n C) (q k A B R : ℕ)
    (hqk : q < k) (hk : k < C.size)
    (hqop : (gateAt C q).op = GateOp.and)
    (hqin : (gateAt C q).inputs = [A, B] ∨ (gateAt C q).inputs = [B, A])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkin : (gateAt C k).inputs = [n + q, R] ∨ (gateAt C k).inputs = [R, n + q])
    (hA : A < n + q) (hB : B < n + q) (hR : R < n + q)
    (honly : ∀ i < C.size, i ≠ k → n + q ∉ (gateAt C i).inputs)
    (x : Fin n → Bool) :
    ((reassoc n C q k A B R).wires (List.ofFn x)).count true + FrontierWireCount.bit (gateVal n C q x) =
      (C.wires (List.ofFn x)).count true + FrontierWireCount.bit (wireVal n C A x && wireVal n C R x) := by
  have hh := reassoc_trueGateCount_balance C hao q k A B R hqk hk hqop hqin hkop hkin
    hA hB hR honly x
  rw [AvailableProductWireMass.wire_count, AvailableProductWireMass.wire_count]
  omega

end PEqualNP.Outside.L_meta_3566.InPlaceAndReassociate


namespace PEqualNP.Outside.L_meta_3566.TwoRowReassociation

def rowTrueCount (a b : Bool) : ℕ := (if a then 1 else 0) + (if b then 1 else 0)

def selectedPair (chooseA a b r : Bool) : Bool := if chooseA then a && r else b && r

lemma clean_two_rows_strict :
    ∀ a0 b0 r0 a1 b1 r1 : Bool,
      ((a0 && b0) && r0) = false → ((a1 && b1) && r1) = false →
      (a0 && b0) = true ∨ (a1 && b1) = true →
      ∃ chooseA : Bool,
        selectedPair chooseA a0 b0 r0 = false ∧
        selectedPair chooseA a1 b1 r1 = false ∧
        rowTrueCount (selectedPair chooseA a0 b0 r0) (selectedPair chooseA a1 b1 r1) = 0 ∧
        rowTrueCount (selectedPair chooseA a0 b0 r0) (selectedPair chooseA a1 b1 r1) <
          rowTrueCount (a0 && b0) (a1 && b1) := by
  decide

end PEqualNP.Outside.L_meta_3566.TwoRowReassociation

namespace PEqualNP.Outside.L_meta_3566.InPlaceAndReassociate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge
open Pruning AvailableProductExchange

variable {n : ℕ}

lemma reassoc_op (C : Circuit) (q k A B R i : ℕ) (hi : i < C.size)
    (hqop : (gateAt C q).op = GateOp.and) (hkop : (gateAt C k).op = GateOp.and) :
    (gateAt (reassoc n C q k A B R) i).op = (gateAt C i).op := by
  rw [reassoc_gateAt C q k A B R i hi]
  unfold newGate
  split_ifs with hiq hik
  · subst i
    exact hqop.symm
  · subst i
    exact hkop.symm
  · rfl

lemma reassoc_negativeAnds_subset (C : Circuit) (hao : IsAO2 n C)
    (F : (Fin n → Bool) → Bool) (q k A B R : ℕ)
    (hqk : q < k) (hk : k < C.size)
    (hqop : (gateAt C q).op = GateOp.and)
    (hqin : (gateAt C q).inputs = [A, B] ∨ (gateAt C q).inputs = [B, A])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkin : (gateAt C k).inputs = [n + q, R] ∨ (gateAt C k).inputs = [R, n + q])
    (hA : A < n + q) (hB : B < n + q) (hR : R < n + q)
    (honly : ∀ i < C.size, i ≠ k → n + q ∉ (gateAt C i).inputs)
    (hqdirty : q ∈ negativeAnds n C F) :
    negativeAnds n (reassoc n C q k A B R) F ⊆ negativeAnds n C F := by
  classical
  intro i hi
  by_cases hiq : i = q
  · exact hiq ▸ hqdirty
  obtain ⟨hiD, hop, x, hFx, hx⟩ := (mem_negativeAnds (reassoc n C q k A B R) F i).mp hi
  have hiC : i < C.size := by simpa only [reassoc_size] using hiD
  apply (mem_negativeAnds C F i).mpr
  refine ⟨hiC, ?_, x, hFx, ?_⟩
  · rw [← reassoc_op C q k A B R i hiC hqop hkop]
    exact hop
  · have he := reassoc_wire C hao q k A B R hqk hk hqop hqin hkop hkin hA hB hR honly x (n + i)
    simp only [Nat.add_left_cancel_iff, hiq, ite_false] at he
    change gateVal n (reassoc n C q k A B R) i x = gateVal n C i x at he
    rw [← he]
    exact hx

lemma reassoc_negativeAnds_card_le (C : Circuit) (hao : IsAO2 n C)
    (F : (Fin n → Bool) → Bool) (q k A B R : ℕ)
    (hqk : q < k) (hk : k < C.size)
    (hqop : (gateAt C q).op = GateOp.and)
    (hqin : (gateAt C q).inputs = [A, B] ∨ (gateAt C q).inputs = [B, A])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkin : (gateAt C k).inputs = [n + q, R] ∨ (gateAt C k).inputs = [R, n + q])
    (hA : A < n + q) (hB : B < n + q) (hR : R < n + q)
    (honly : ∀ i < C.size, i ≠ k → n + q ∉ (gateAt C i).inputs)
    (hqdirty : q ∈ negativeAnds n C F) :
    (negativeAnds n (reassoc n C q k A B R) F).card ≤ (negativeAnds n C F).card := by
  exact Finset.card_le_card (reassoc_negativeAnds_subset C hao F q k A B R hqk hk hqop hqin
    hkop hkin hA hB hR honly hqdirty)

end PEqualNP.Outside.L_meta_3566.InPlaceAndReassociate

namespace PEqualNP.Outside.L_meta_3566.InPlaceAndReassociate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge
open Pruning AndRotation FrontierWireCount TwoRowReassociation AvailableProductExchange

variable {n : ℕ}

lemma reassoc_two_rows_strict (C : Circuit) (hao : IsAO2 n C) (q k A B R : ℕ)
    (hqk : q < k) (hk : k < C.size)
    (hqop : (gateAt C q).op = GateOp.and)
    (hqin : (gateAt C q).inputs = [A, B] ∨ (gateAt C q).inputs = [B, A])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkin : (gateAt C k).inputs = [n + q, R] ∨ (gateAt C k).inputs = [R, n + q])
    (hA : A < n + q) (hB : B < n + q) (hR : R < n + q)
    (honly : ∀ i < C.size, i ≠ k → n + q ∉ (gateAt C i).inputs)
    (x y : Fin n → Bool)
    (hxnew : (wireVal n C A x && wireVal n C R x) = false)
    (hynew : (wireVal n C A y && wireVal n C R y) = false)
    (hpositive : gateVal n C q x = true ∨ gateVal n C q y = true) :
    ((reassoc n C q k A B R).wires (List.ofFn x)).count true +
        ((reassoc n C q k A B R).wires (List.ofFn y)).count true <
      (C.wires (List.ofFn x)).count true + (C.wires (List.ofFn y)).count true := by
  have hx := reassoc_wire_count_balance C hao q k A B R hqk hk hqop hqin hkop hkin hA hB hR honly x
  have hy := reassoc_wire_count_balance C hao q k A B R hqk hk hqop hqin hkop hkin hA hB hR honly y
  have hzx : bit (wireVal n C A x && wireVal n C R x) = 0 := by rw [hxnew]; rfl
  have hzy : bit (wireVal n C A y && wireVal n C R y) = 0 := by rw [hynew]; rfl
  rw [hzx] at hx
  rw [hzy] at hy
  have hpos : 0 < bit (gateVal n C q x) + bit (gateVal n C q y) := by
    cases hqx : gateVal n C q x <;> cases hqy : gateVal n C q y <;> simp_all [bit]
  omega

lemma exists_two_rows_strict (C : Circuit) (hao : IsAO2 n C) (q k A B R : ℕ)
    (hqk : q < k) (hk : k < C.size)
    (hqop : (gateAt C q).op = GateOp.and)
    (hqin : (gateAt C q).inputs = [A, B] ∨ (gateAt C q).inputs = [B, A])
    (hkop : (gateAt C k).op = GateOp.and)
    (hkin : (gateAt C k).inputs = [n + q, R] ∨ (gateAt C k).inputs = [R, n + q])
    (hA : A < n + q) (hB : B < n + q) (hR : R < n + q)
    (honly : ∀ i < C.size, i ≠ k → n + q ∉ (gateAt C i).inputs)
    (hout : C.output ≠ n + q) (x y : Fin n → Bool)
    (hcleanx : gateVal n C k x = false) (hcleany : gateVal n C k y = false)
    (hpositive : gateVal n C q x = true ∨ gateVal n C q y = true) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size ∧ circuitFun n D = circuitFun n C ∧
      (∀ z w, w ≠ n + q → wireVal n D w z = wireVal n C w z) ∧
      (∀ F : (Fin n → Bool) → Bool, q ∈ negativeAnds n C F →
        negativeAnds n D F ⊆ negativeAnds n C F) ∧
      (D.wires (List.ofFn x)).count true + (D.wires (List.ofFn y)).count true <
        (C.wires (List.ofFn x)).count true + (C.wires (List.ofFn y)).count true := by
  have hqvalue (z : Fin n → Bool) : gateVal n C q z =
      (wireVal n C A z && wireVal n C B z) :=
    and_gate_value C hao q A B (by omega) hqop hqin z
  have hkvalue (z : Fin n → Bool) : gateVal n C k z =
      ((wireVal n C A z && wireVal n C B z) && wireVal n C R z) := by
    rw [and_gate_value C hao k (n + q) R hk hkop hkin z]
    change (gateVal n C q z && wireVal n C R z) = _
    rw [hqvalue]
  obtain ⟨chooseA, hzeroX, hzeroY, hzeroCount, hstrict⟩ := clean_two_rows_strict
    (wireVal n C A x) (wireVal n C B x) (wireVal n C R x)
    (wireVal n C A y) (wireVal n C B y) (wireVal n C R y)
    (by simpa only [hkvalue x] using hcleanx)
    (by simpa only [hkvalue y] using hcleany)
    (by simpa only [hqvalue x, hqvalue y] using hpositive)
  have hbranch (P Q : ℕ)
      (hin : (gateAt C q).inputs = [P, Q] ∨ (gateAt C q).inputs = [Q, P])
      (hP : P < n + q) (hQ : Q < n + q)
      (hPx : (wireVal n C P x && wireVal n C R x) = false)
      (hPy : (wireVal n C P y && wireVal n C R y) = false) :
      ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size ∧ circuitFun n D = circuitFun n C ∧
        (∀ z w, w ≠ n + q → wireVal n D w z = wireVal n C w z) ∧
        (∀ F : (Fin n → Bool) → Bool, q ∈ negativeAnds n C F →
          negativeAnds n D F ⊆ negativeAnds n C F) ∧
        (D.wires (List.ofFn x)).count true + (D.wires (List.ofFn y)).count true <
          (C.wires (List.ofFn x)).count true + (C.wires (List.ofFn y)).count true := by
    refine ⟨reassoc n C q k P Q R, reassoc_ao C hao q k P Q R hqk hk hP hQ hR,
      reassoc_size C q k P Q R, ?_, ?_, ?_, ?_⟩
    · exact reassoc_fun C hao q k P Q R hqk hk hqop hin hkop hkin hP hQ hR honly hout
    · intro z w hw
      rw [reassoc_wire C hao q k P Q R hqk hk hqop hin hkop hkin hP hQ hR honly z w,
        ite_eq_right hw]
    · intro F hqdirty
      exact reassoc_negativeAnds_subset C hao F q k P Q R hqk hk hqop hin hkop hkin
        hP hQ hR honly hqdirty
    · exact reassoc_two_rows_strict C hao q k P Q R hqk hk hqop hin hkop hkin hP hQ hR
        honly x y hPx hPy hpositive
  cases chooseA with
  | false =>
    apply hbranch B A (hqin.elim Or.inr Or.inl) hB hA
    · simpa only [selectedPair, Bool.false_eq_true, ite_false] using hzeroX
    · simpa only [selectedPair, Bool.false_eq_true, ite_false] using hzeroY
  | true =>
    apply hbranch A B hqin hA hB
    · simpa only [selectedPair, ite_true] using hzeroX
    · simpa only [selectedPair, ite_true] using hzeroY

end PEqualNP.Outside.L_meta_3566.InPlaceAndReassociate

namespace PEqualNP.Outside.L_meta_3566.SoleOrColor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open Pruning SingleRead

variable {n : ℕ}

lemma opposite_color_graph_false (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Bool) (hc : ∀ v w, G.Adj v w → c v ≠ c w) (u : Fin n) :
    graphFun G ∅ (fun v => decide (c v ≠ c u)) = false := by
  apply Bool.eq_false_iff.mpr
  intro htrue
  have hex : ∃ a b, G.Adj a b ∧ c a ≠ c u ∧ c b ≠ c u := by
    simpa [graphFun] using htrue
  obtain ⟨a, b, hab, ha, hb⟩ := hex
  have hne := hc a b hab
  cases hua : c u <;> cases haa : c a <;> cases hbb : c b <;> simp_all

lemma source_opposite_color_false (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Bool) (hc : ∀ v w, G.Adj v w → c v ≠ c w)
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (w : Fin n) (huw : G.Adj u w) :
    wireVal n C t (fun v => decide (c v ≠ c u)) = false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  have htrue := sole_or_neighbor_multiplier G C u pre post g t hshape hop hinputs hao hno
    hfun w huw (fun v => decide (c v ≠ c u)) ht
    (by simpa using (Ne.symm (hc u w huw)))
  rw [opposite_color_graph_false G c hc u] at htrue
  cases htrue

lemma source_opposite_support_false (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Bool) (hc : ∀ v w, G.Adj v w → c v ≠ c w)
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (w : Fin n) (huw : G.Adj u w)
    (x : Fin n → Bool) (hsupport : ∀ v, x v = true → c v ≠ c u) :
    wireVal n C t x = false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  by_cases htu : t = u.val
  · rw [htu, wireVal_lt C u.val u.isLt] at ht
    exact hsupport u ht rfl
  · have htmem : t ∈ g.inputs := by rcases hinputs with h | h <;> simp [h]
    have hlarge := other_wire_compare C u pre post g t hshape htmem hao hno htu
      x (fun v => decide (c v ≠ c u)) (fun v _ hv => by simpa using hsupport v hv) ht
    change wireVal n C t (fun v => decide (c v ≠ c u)) = true at hlarge
    rw [source_opposite_color_false G c hc C u pre post g t hshape hop hinputs hao hno
      hfun w huw] at hlarge
    cases hlarge

lemma raw_product_one_color_of_neighbor (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Bool) (hc : ∀ v w, G.Adj v w → c v ≠ c w)
    (C : Circuit) (u : Fin n) (pre post : List Gate) (g : Gate) (t : ℕ)
    (hshape : C.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hinputs : g.inputs = [u.val, t] ∨ g.inputs = [t, u.val])
    (hao : IsAO2 n C) (hno : ∀ q ∈ pre ++ post, u.val ∉ q.inputs)
    (hfun : circuitFun n C = graphFun G ∅) (w : Fin n) (huw : G.Adj u w)
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
    have hz := source_opposite_support_false G c hc C u pre post g t hshape hop hinputs
      hao hno hfun w huw (pairInput a b) (by
        intro v hv
        simp only [pairInput, decide_eq_true_eq] at hv
        rcases hv with rfl | rfl
        · exact hca
        · exact hcb)
    rw [hprod a ha b hb] at hz
    cases hz

end PEqualNP.Outside.L_meta_3566.SoleOrColor

namespace PEqualNP.Outside.L_meta_3566.PrivateAndMasking

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge
open Pruning

variable {n : ℕ}

lemma gate_eq_eval_of_readsBack (C : Circuit) (hC : ReadsBack n C)
    (j : ℕ) (hj : j < C.size) (x : Fin n → Bool) :
    gateVal n C j x = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i => wireVal n C i x) := by
  have hj' : j < C.gates.length := hj
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    have h := List.take_append_drop j C.gates
    rw [List.drop_eq_getElem_cons hj'] at h
    have e : C.gates[j] = gateAt C j := by
      simp [gateAt, List.getD_eq_getElem?_getD, hj']
    rw [e] at h
    exact h.symm
  have htake : (C.gates.take j).length = j := by simp; omega
  have hold : ∀ w < n + j, wireVal n C w x = wireVal n ⟨C.gates.take j, 0⟩ w x := by
    intro w hw
    unfold wireVal Circuit.wires
    conv_lhs => rw [hsplit, List.foldl_append]
    rw [wires_prefix]
    rw [wires_length, htake]
    simpa using hw
  have hnew : gateVal n C j x = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i => wireVal n ⟨C.gates.take j, 0⟩ i x) := by
    rw [← wireVal_new, htake]
    unfold gateVal wireVal Circuit.wires
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    rw [wires_prefix]
    · simp [List.foldl_append]
    · rw [List.length_append, wires_length, htake, List.length_ofFn]; simp
  rw [hnew]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (hold i (hC j hj i hi)).symm

lemma wireVal_eq_of_readsBack_solution (C : Circuit) (hC : ReadsBack n C)
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
      rw [gate_eq_eval_of_readsBack C hC j hj x, hgate j hj]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hib := hC j hj i hi
      apply ih i
      · omega
      · omega

def disable (C : Circuit) (j : ℕ) : Circuit :=
  ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩

lemma disable_size (C : Circuit) (j : ℕ) : (disable C j).size = C.size := by
  simp [disable, Circuit.size]

lemma disable_gateAt (C : Circuit) (j i : ℕ) :
    gateAt (disable C j) i = if j = i then ⟨GateOp.or, []⟩ else gateAt C i := by
  simp only [gateAt, disable, List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs <;> simp_all

lemma disable_readsBack (C : Circuit) (hC : ReadsBack n C) (j : ℕ) :
    ReadsBack n (disable C j) := by
  intro i hi w hw
  have hiC : i < C.size := by simpa [disable, Circuit.size] using hi
  rw [disable_gateAt] at hw
  split_ifs at hw with he
  · simp at hw
  · exact hC i hiC w hw

lemma disable_wire_eq_away (C : Circuit) (hC : ReadsBack n C)
    (j k s : ℕ)
    (hop : (gateAt C k).op = GateOp.and)
    (hin : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hsj : s ≠ n + j)
    (hprivate : ∀ i < C.size, i ≠ k → n + j ∉ (gateAt C i).inputs)
    (x : Fin n → Bool) (hs : wireVal n C s x = false) :
    ∀ w < n + C.size, w ≠ n + j →
      wireVal n (disable C j) w x = wireVal n C w x := by
  let V : ℕ → Bool := fun w => if w = n + j then false else wireVal n C w x
  have hinput (u : Fin n) : V u.val = x u := by
    have hu : u.val ≠ n + j := by have := u.isLt; omega
    simp only [V, ite_eq_right hu]
    exact wireVal_lt C u.val u.isLt x
  have hgate (i : ℕ) (hi : i < (disable C j).size) :
      V (n + i) = (gateAt (disable C j) i).op.eval
        ((gateAt (disable C j) i).inputs.map V) := by
    have hiC : i < C.size := by simpa [disable_size] using hi
    rw [disable_gateAt]
    by_cases hji : j = i
    · subst i
      simp [V, GateOp.eval]
    · simp only [ite_eq_right hji]
      have hnji : n + i ≠ n + j := by omega
      rw [show V (n + i) = wireVal n C (n + i) x by simp only [V, ite_eq_right hnji]]
      change gateVal n C i x = _
      rw [gate_eq_eval_of_readsBack C hC i hiC x]
      by_cases hik : i = k
      · subst i
        rcases hin with hin | hin <;>
          simp [hin, hop, V, hsj, hs, GateOp.eval]
      · congr 1
        apply List.map_congr_left
        intro w hw
        have hne : w ≠ n + j := by
          intro he
          exact hprivate i hiC hik (he ▸ hw)
        simp [V, hne]
  intro w hw hne
  have hD := wireVal_eq_of_readsBack_solution (disable C j)
    (disable_readsBack C hC j) x V hinput hgate w (by simpa [disable_size] using hw)
  simpa [V, hne] using hD

lemma disable_output_eq_of_private_and_false (C : Circuit) (hC : ReadsBack n C)
    (j k s : ℕ)
    (hop : (gateAt C k).op = GateOp.and)
    (hin : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hsj : s ≠ n + j)
    (hprivate : ∀ i < C.size, i ≠ k → n + j ∉ (gateAt C i).inputs)
    (hout : C.output < n + C.size) (hoj : C.output ≠ n + j)
    (x : Fin n → Bool) (hs : wireVal n C s x = false) :
    circuitFun n (disable C j) x = circuitFun n C x := by
  exact disable_wire_eq_away C hC j k s hop hin hsj hprivate x hs
    C.output hout hoj

lemma disable_wire_eq_of_gate_false (C : Circuit) (hC : ReadsBack n C)
    (j : ℕ) (x : Fin n → Bool) (hjfalse : gateVal n C j x = false) :
    ∀ w < n + C.size, wireVal n (disable C j) w x = wireVal n C w x := by
  intro w hw
  refine wireVal_eq_of_readsBack_solution (disable C j) (disable_readsBack C hC j)
    x (fun w => wireVal n C w x) ?_ ?_ w (by simpa [disable_size] using hw)
  · intro u
    exact wireVal_lt C u.val u.isLt x
  · intro i hi
    have hiC : i < C.size := by simpa [disable_size] using hi
    rw [disable_gateAt]
    by_cases hji : j = i
    · subst i
      simpa [GateOp.eval, gateVal, wireVal] using hjfalse
    · simp only [ite_eq_right hji]
      exact gate_eq_eval_of_readsBack C hC i hiC x

lemma private_and_pivotal_true (C : Circuit) (hC : ReadsBack n C)
    (j k s : ℕ)
    (hop : (gateAt C k).op = GateOp.and)
    (hin : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hsj : s ≠ n + j)
    (hprivate : ∀ i < C.size, i ≠ k → n + j ∉ (gateAt C i).inputs)
    (hout : C.output < n + C.size) (hoj : C.output ≠ n + j)
    (x : Fin n → Bool) (htrue : circuitFun n C x = true)
    (hpivotal : circuitFun n (disable C j) x = false) :
    gateVal n C j x = true ∧ wireVal n C s x = true := by
  constructor
  · apply Bool.eq_true_of_not_eq_false
    intro hf
    have he := disable_wire_eq_of_gate_false C hC j x hf C.output hout
    change circuitFun n (disable C j) x = circuitFun n C x at he
    rw [hpivotal, htrue] at he
    cases he
  · apply Bool.eq_true_of_not_eq_false
    intro hf
    have he := disable_output_eq_of_private_and_false C hC j k s
      hop hin hsj hprivate hout hoj x hf
    rw [hpivotal, htrue] at he
    cases he

lemma private_or_and_noninput_edge (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (u : Fin n) (j k t s : ℕ) (hj : j < C.size)
    (hjor : (gateAt C j).op = GateOp.or)
    (hjin : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkand : (gateAt C k).op = GateOp.and)
    (hkin : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hsj : s ≠ n + j)
    (hprivate : ∀ i < C.size, i ≠ k → n + j ∉ (gateAt C i).inputs)
    (hout : C.output < n + C.size) (hoj : C.output ≠ n + j)
    (hpivotal : ∃ a b : Fin n, G.Adj a b ∧
      circuitFun n (disable C j) (pairInput a b) = false ∧ pairInput a b u = false) :
    ∃ a b : Fin n, G.Adj a b ∧ a ≠ u ∧ b ≠ u ∧
      wireVal n C t (pairInput a b) = true ∧ wireVal n C s (pairInput a b) = true := by
  obtain ⟨a, b, hab, hp, hu⟩ := hpivotal
  have htrue : circuitFun n C (pairInput a b) = true := by
    rw [hfun]
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩
  obtain ⟨hjtrue, hstrue⟩ := private_and_pivotal_true C hao.2.1 j k s
    hkand hkin hsj hprivate hout hoj (pairInput a b) htrue hp
  have hufalse : wireVal n C u.val (pairInput a b) = false := by
    rw [wireVal_lt C u.val u.isLt]
    exact hu
  have httrue : wireVal n C t (pairInput a b) = true := by
    rw [gate_eq_eval_of_readsBack C hao.2.1 j hj (pairInput a b)] at hjtrue
    rcases hjin with hin | hin <;>
      simpa [hjor, hin, GateOp.eval, hufalse] using hjtrue
  refine ⟨a, b, hab, ?_, ?_, httrue, hstrue⟩
  · intro he
    subst a
    simp [pairInput] at hu
  · intro he
    subst b
    simp [pairInput] at hu

lemma output_bound_of_true (C : Circuit) (x : Fin n → Bool)
    (hx : circuitFun n C x = true) : C.output < n + C.size := by
  by_contra hbad
  have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
    unfold Circuit.wires
    rw [wires_length, List.length_ofFn]
    rfl
  have hfalse : (C.wires (List.ofFn x)).getD C.output false = false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega :
      (C.wires (List.ofFn x)).length ≤ C.output)]
  change (C.wires (List.ofFn x)).getD C.output false = true at hx
  rw [hfalse] at hx
  cases hx

lemma or_raw_output_ne (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (u : Fin n) (j t : ℕ) (hj : j < C.size)
    (hop : (gateAt C j).op = GateOp.or)
    (hin : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val]) :
    C.output ≠ n + j := by
  intro he
  have hfalse : graphFun G ∅ (pairInput u u) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact G.irrefl ((SingleRead.graph_pair G u u).mp h)
  have hv := congrFun hfun (pairInput u u)
  change wireVal n C C.output (pairInput u u) = _ at hv
  rw [he] at hv
  change gateVal n C j (pairInput u u) = _ at hv
  rw [gate_eq_eval_of_readsBack C hao.2.1 j hj (pairInput u u)] at hv
  have hu : wireVal n C u.val (pairInput u u) = true := by
    rw [wireVal_lt C u.val u.isLt]
    simp [pairInput]
  rcases hin with hin | hin <;> simp [hop, hin, GateOp.eval, hu, hfalse] at hv

lemma private_or_and_noninput_edge_auto_output
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (u : Fin n) (j k t s : ℕ) (hj : j < C.size)
    (hjor : (gateAt C j).op = GateOp.or)
    (hjin : (gateAt C j).inputs = [u.val, t] ∨ (gateAt C j).inputs = [t, u.val])
    (hkand : (gateAt C k).op = GateOp.and)
    (hkin : (gateAt C k).inputs = [n + j, s] ∨ (gateAt C k).inputs = [s, n + j])
    (hsj : s ≠ n + j)
    (hprivate : ∀ i < C.size, i ≠ k → n + j ∉ (gateAt C i).inputs)
    (hpivotal : ∃ a b : Fin n, G.Adj a b ∧
      circuitFun n (disable C j) (pairInput a b) = false ∧ pairInput a b u = false) :
    ∃ a b : Fin n, G.Adj a b ∧ a ≠ u ∧ b ≠ u ∧
      wireVal n C t (pairInput a b) = true ∧ wireVal n C s (pairInput a b) = true := by
  have hout : C.output < n + C.size := by
    obtain ⟨a, b, hab, _⟩ := hpivotal
    apply output_bound_of_true C (pairInput a b)
    rw [hfun, SingleRead.graph_pair]
    exact hab
  exact private_or_and_noninput_edge G C hao hfun u j k t s hj hjor hjin
    hkand hkin hsj hprivate hout (or_raw_output_ne G C hao hfun u j t hj hjor hjin) hpivotal

end PEqualNP.Outside.L_meta_3566.PrivateAndMasking

namespace PEqualNP.Outside.L_meta_3566.PrivateOrAbsorb

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open Pruning SingleRead ANDRotationEvaluation ANDRotationComparison GateSavings

variable {n : ℕ}

lemma transport (C : Circuit) (hao : IsAO2 n C) (a u : Fin n) (h j : ℕ)
    (hj : j < C.size) (hjor : (gateAt C j).op = GateOp.or)
    (hju : u.val ∈ (gateAt C j).inputs)
    (haonly : ∀ k < C.size, a.val ∈ (gateAt C k).inputs → k = h)
    (hhonly : ∀ k < C.size, n + h ∈ (gateAt C k).inputs → k = j)
    (ho : C.output < n + C.size) (hoa : C.output ≠ a.val) (hoh : C.output ≠ n + h)
    (x y : Fin n → Bool) (hyu : y u = true)
    (hxy : ∀ v : Fin n, v ≠ a → x v = true → y v = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  let V : ℕ → Bool := fun w => if w = a.val ∨ w = n + h then true else wireVal n C w y
  have hVinput : ∀ v : Fin n, x v = true → V v.val = true := by
    intro v hv
    by_cases hva : v = a
    · simp [V, hva]
    · have hval : v.val ≠ a.val := fun he => hva (Fin.ext he)
      have hhigh : v.val ≠ n + h := by have := v.isLt; omega
      simp only [V, hval, hhigh, or_self, ite_false]
      rw [wireVal_lt C v.val v.isLt]
      exact hxy v hva hv
  have hjtrue : wireVal n C (n + j) y = true := by
    change gateVal n C j y = true
    rw [gate_eq_eval C hao j hj y]
    simp only [hjor, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq]
    exact ⟨u.val, hju, by simpa [wireVal_lt C u.val u.isLt] using hyu⟩
  have hVgate : ∀ k < C.size,
      (gateAt C k).op.eval ((gateAt C k).inputs.map V) = true → V (n + k) = true := by
    intro k hk hval
    by_cases hkh : k = h
    · simp [V, hkh]
    · have hhigh : n + k ≠ a.val := by have := a.isLt; omega
      have hne : n + k ≠ n + h := by omega
      simp only [V, hhigh, hne, or_self, ite_false]
      by_cases hkj : k = j
      · simpa [hkj] using hjtrue
      · have hmap : (gateAt C k).inputs.map V =
            (gateAt C k).inputs.map (fun w => wireVal n C w y) := by
          apply List.map_congr_left
          intro w hw
          have hwa : w ≠ a.val := by
            intro he
            exact hkh (haonly k hk (he ▸ hw))
          have hwh : w ≠ n + h := by
            intro he
            exact hkj (hhonly k hk (he ▸ hw))
          simp [V, hwa, hwh]
        rw [hmap] at hval
        change gateVal n C k y = true
        rwa [gate_eq_eval C hao k hk y]
  intro hx
  have hVout := wireVal_le_of_supersolution C hao x V hVinput hVgate C.output ho hx
  change wireVal n C C.output y = true
  simpa [V, hoa, hoh] using hVout

lemma neighbor_inclusion (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (a u : Fin n) (h j : ℕ) (hj : j < C.size)
    (hjor : (gateAt C j).op = GateOp.or) (hju : u.val ∈ (gateAt C j).inputs)
    (haonly : ∀ k < C.size, a.val ∈ (gateAt C k).inputs → k = h)
    (hhonly : ∀ k < C.size, n + h ∈ (gateAt C k).inputs → k = j)
    (hoh : C.output ≠ n + h) :
    ∀ v, G.Adj a v → G.Adj u v := by
  intro v hav
  have ho := InputReads.output_upper G C hfun ⟨a, v, hav⟩
  have ht := transport C hao a u h j hj hjor hju haonly hhonly ho
    (output_ne G C hfun a) hoh (pairInput a v) (pairInput u v) (by simp [pairInput])
    (by
      intro w hwa hw
      simp only [pairInput, decide_eq_true_eq] at hw ⊢
      rcases hw with hw | hw
      · exact False.elim (hwa hw)
      · exact Or.inr hw)
  rw [hfun] at ht
  exact (graph_pair G u v).mp (ht ((graph_pair G a v).mpr hav))

lemma degree_le_one (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hfour : NoFourCycle G) (a u : Fin n) (hau : a ≠ u) (h j : ℕ) (hj : j < C.size)
    (hjor : (gateAt C j).op = GateOp.or) (hju : u.val ∈ (gateAt C j).inputs)
    (haonly : ∀ k < C.size, a.val ∈ (gateAt C k).inputs → k = h)
    (hhonly : ∀ k < C.size, n + h ∈ (gateAt C k).inputs → k = j)
    (hoh : C.output ≠ n + h) : G.degree a ≤ 1 := by
  have hincl := neighbor_inclusion G C hao hfun a u h j hj hjor hju haonly hhonly hoh
  have hsub : G.neighborFinset a ⊆ Finset.univ.filter (fun v => G.Adj a v ∧ G.Adj u v) := by
    intro v hv
    have hav := (G.mem_neighborFinset a v).mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hav, hincl v hav⟩
  have hc := (Finset.card_le_card hsub).trans (hfour a u hau)
  simpa only [G.card_neighborFinset_eq_degree] using hc

lemma wire_reach_le (C : Circuit) (hao : IsAO2 n C) {p q : ℕ}
    (hpath : Relation.ReflTransGen (WireStep n C) p q) : q ≤ p := by
  induction hpath using Relation.ReflTransGen.trans_induction_on with
  | refl p => exact le_rfl
  | @single p q hpq =>
      obtain ⟨i, hi, hpi, hread⟩ := hpq
      have hlt := hao.2.1 i hi q hread
      omega
  | trans hpq hqr ihpq ihqr => exact ihqr.trans ihpq

lemma least_output_ne_of_later_reader (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (h j : ℕ) (hj : j < C.size)
    (hread : n + h ∈ (gateAt C j).inputs) : C.output ≠ n + h := by
  classical
  have hhj : h < j := by
    have hlt := hC.1.2.1 j hj (n + h) hread
    omega
  have ho := LeastOutputValidity.least_output_upper_of_size_pos G C hC (by omega)
  have hlive : j ∈ liveGates n C := by
    rw [least_all_live G C hC ho]
    exact Finset.mem_range.mpr hj
  have hpath := (Finset.mem_filter.mp hlive).2
  have hle := wire_reach_le C hC.1 hpath
  intro hout
  rw [hout] at hle
  omega

lemma least_source_has_two_readers (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hfour : NoFourCycle G)
    (a u : Fin n) (h j : ℕ) (hj : j < C.size)
    (hjor : (gateAt C j).op = GateOp.or) (hju : u.val ∈ (gateAt C j).inputs)
    (hjh : n + h ∈ (gateAt C j).inputs)
    (haonly : ∀ k < C.size, a.val ∈ (gateAt C k).inputs → k = h)
    (hdeg : 2 ≤ G.degree a) : 2 ≤ (readers n C h).card := by
  classical
  have hhj : h < j := by
    have hlt := hC.1.2.1 j hj (n + h) hjh
    omega
  have hau : a ≠ u := by
    intro he
    subst u
    have heq := haonly j hj hju
    omega
  have hjmem : j ∈ readers n C h := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hjh⟩
  by_contra hsmall
  have hcard : (readers n C h).card ≤ 1 := by omega
  have hhone : ∀ k < C.size, n + h ∈ (gateAt C k).inputs → k = j := by
    intro k hk hkr
    have hkmem : k ∈ readers n C h := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkr⟩
    exact Finset.card_le_one.mp hcard k hkmem j hjmem
  have hc := degree_le_one G C hC.1 hC.2.1 hfour a u hau h j hj hjor hju haonly hhone
    (least_output_ne_of_later_reader G C hC h j hj hjh)
  omega

lemma restrict_source_saves_three (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hfour : NoFourCycle G)
    (a u : Fin n) (h j : ℕ) (hj : j < C.size)
    (hjor : (gateAt C j).op = GateOp.or) (hju : u.val ∈ (gateAt C j).inputs)
    (hjh : n + h ∈ (gateAt C j).inputs)
    (haonly : ∀ k < C.size, a.val ∈ (gateAt C k).inputs → k = h)
    (hdeg : 2 ≤ G.degree a) (hhand : (gateAt C h).op = GateOp.and)
    (hha : a.val ∈ (gateAt C h).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + 3 ≤ C.size ∧
      circuitFun n D = fun x => graphFun G ∅ (cutInput a x) := by
  have hhj : h < j := by
    have hlt := hC.1.2.1 j hj (n + h) hjh
    omega
  have hr := least_source_has_two_readers G C hC hfour a u h j hj hjor hju hjh haonly hdeg
  have ho := LeastOutputValidity.least_output_upper_of_size_pos G C hC (by omega)
  obtain ⟨D, hD, hs, hf⟩ := GateSavings.restrict_and_reader_saves C hC.1 ho a h
    (by omega) hhand hha
  refine ⟨D, hD, by omega, ?_⟩
  simpa only [hC.2.1] using hf

end PEqualNP.Outside.L_meta_3566.PrivateOrAbsorb

namespace PEqualNP.Outside.L_meta_3566.FourGateRestriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge
open Pruning GateSavings

variable {n : ℕ}

lemma and_false_of_false_input (C : Circuit) (hao : IsAO2 n C)
    (i w : ℕ) (hi : i < C.size) (hop : (gateAt C i).op = GateOp.and)
    (hread : w ∈ (gateAt C i).inputs) (x : Fin n → Bool)
    (hfalse : wireVal n C w x = false) : gateVal n C i x = false := by
  obtain ⟨b, hb⟩ := exists_opnd_of_mem C hao i hi w hread
  rw [gate_eq C hao i hi, hop]
  change (wireVal n C (opnd C i 0) x && wireVal n C (opnd C i 1) x) = false
  have hcases : b = 0 ∨ b = 1 := by omega
  rcases hcases with h | h
  · rw [h] at hb
    rw [hb, hfalse]
    rfl
  · rw [h] at hb
    rw [hb, hfalse]
    exact Bool.and_false _

lemma restrict_four_of_chain (C : Circuit) (hao : IsAO2 n C)
    (hout : C.output < n + C.size) (a u : Fin n) (H j k l : ℕ)
    (hH : H < C.size) (hj : j < C.size) (hk : k < C.size) (hl : l < C.size)
    (hHop : (gateAt C H).op = GateOp.and)
    (haH : a.val ∈ (gateAt C H).inputs)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjin : (gateAt C j).inputs = [u.val, n + H] ∨
      (gateAt C j).inputs = [n + H, u.val])
    (hkop : (gateAt C k).op = GateOp.and)
    (hHk : n + H ∈ (gateAt C k).inputs)
    (hkl : n + k ∈ (gateAt C l).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + 4 ≤ C.size ∧
      circuitFun n D = fun x => circuitFun n C (cutInput a x) := by
  classical
  have hHj : n + H ∈ (gateAt C j).inputs := by
    rcases hjin with hin | hin <;> simp [hin]
  have hHjlt : H < j := by have := hao.2.1 j hj _ hHj; omega
  have hHklt : H < k := by have := hao.2.1 k hk _ hHk; omega
  have hkllt : k < l := by have := hao.2.1 l hl _ hkl; omega
  have hjk : j ≠ k := by
    intro he
    subst k
    rw [hjop] at hkop
    cases hkop
  have hjl : j ≠ l := by
    intro he
    rw [← he] at hkl
    have hmem : n + k = u.val ∨ n + k = n + H := by
      rcases hjin with hin | hin
      · simpa [hin] using hkl
      · have hh : n + k = n + H ∨ n + k = u.val := by simpa [hin] using hkl
        exact hh.symm
    have hu := u.isLt
    rcases hmem with hmem | hmem <;> omega
  let E : Finset ℕ := {H, j, k, l}
  have hEcard : E.card = 4 := by
    simp [E, Nat.ne_of_lt hHjlt, Nat.ne_of_lt hHklt,
      Nat.ne_of_lt (Nat.lt_trans hHklt hkllt), hjk, hjl, Nat.ne_of_lt hkllt]
  have hE : E ⊆ Finset.range C.size := by
    intro i hi
    have his : i = H ∨ i = j ∨ i = k ∨ i = l := by simpa [E] using hi
    rcases his with rfl | rfl | rfl | rfl <;> exact Finset.mem_range.mpr (by assumption)
  have hzH : gateVal n C H (cutInput a (fun _ => true)) = false :=
    and_reader_zero C hao a H hH hHop haH
  have hzk : gateVal n C k (cutInput a (fun _ => true)) = false :=
    and_false_of_false_input C hao k (n + H) hk hkop hHk _ hzH
  have hzero (i : ℕ) (hi : i ∈ E) : ∃ b : Fin 2,
      wireVal n C (opnd C i b) (cutInput a (fun _ => true)) = false := by
    have of_input (w : ℕ) (hilen : i < C.size) (hread : w ∈ (gateAt C i).inputs)
        (hfalse : wireVal n C w (cutInput a (fun _ => true)) = false) :
        ∃ b : Fin 2, wireVal n C (opnd C i b) (cutInput a (fun _ => true)) = false := by
      obtain ⟨b, hb⟩ := exists_opnd_of_mem C hao i hilen w hread
      exact ⟨b, by rw [hb]; exact hfalse⟩
    have his : i = H ∨ i = j ∨ i = k ∨ i = l := by simpa [E] using hi
    rcases his with rfl | rfl | rfl | rfl
    · exact of_input a.val hH haH (input_zero C a)
    · exact of_input (n + H) hj hHj hzH
    · exact of_input (n + H) hk hHk hzH
    · exact of_input (n + k) hl hkl hzk
  obtain ⟨D, hD, hsize, hfun⟩ := restrict_false_saves C hao hout a E hE hzero
  rw [hEcard] at hsize
  exact ⟨D, hD, hsize, hfun⟩

lemma and_chain_output_ne_of_avoiding_edge
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (a : Fin n) (H k : ℕ) (hH : H < C.size) (hk : k < C.size)
    (hHop : (gateAt C H).op = GateOp.and) (haH : a.val ∈ (gateAt C H).inputs)
    (hkop : (gateAt C k).op = GateOp.and) (hHk : n + H ∈ (gateAt C k).inputs)
    (havoid : ∃ p q : Fin n, G.Adj p q ∧ p ≠ a ∧ q ≠ a) :
    C.output ≠ n + k := by
  obtain ⟨p, q, hpq, hpa, hqa⟩ := havoid
  have ha : wireVal n C a.val (pairInput p q) = false := by
    rw [wireVal_lt C a.val a.isLt]
    simp [pairInput, Ne.symm hpa, Ne.symm hqa]
  have hzH := and_false_of_false_input C hao H a.val hH hHop haH _ ha
  have hzk := and_false_of_false_input C hao k (n + H) hk hkop hHk _ hzH
  intro he
  have htrue : circuitFun n C (pairInput p q) = true := by
    rw [hfun]
    exact (SingleRead.graph_pair G p q).mpr hpq
  change wireVal n C C.output (pairInput p q) = true at htrue
  rw [he] at htrue
  change gateVal n C k (pairInput p q) = true at htrue
  rw [hzk] at htrue
  cases htrue

lemma restrict_four_of_least (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (a u : Fin n) (H j k : ℕ)
    (hH : H < C.size) (hj : j < C.size) (hk : k < C.size)
    (hHop : (gateAt C H).op = GateOp.and) (haH : a.val ∈ (gateAt C H).inputs)
    (hjop : (gateAt C j).op = GateOp.or)
    (hjin : (gateAt C j).inputs = [u.val, n + H] ∨
      (gateAt C j).inputs = [n + H, u.val])
    (hkop : (gateAt C k).op = GateOp.and) (hHk : n + H ∈ (gateAt C k).inputs)
    (havoid : ∃ p q : Fin n, G.Adj p q ∧ p ≠ a ∧ q ≠ a) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + 4 ≤ C.size ∧
      circuitFun n D = fun x => circuitFun n C (cutInput a x) := by
  have hout := InputReads.output_upper G C hC.2.1 (by
    obtain ⟨p, q, hpq, _⟩ := havoid
    exact ⟨p, q, hpq⟩)
  have hko := and_chain_output_ne_of_avoiding_edge G C hC.1 hC.2.1 a H k hH hk
    hHop haH hkop hHk havoid
  obtain ⟨l, hl, _, hkl⟩ := least_has_reader G C hC hout k hk hko
  exact restrict_four_of_chain C hC.1 hout a u H j k l hH hj hk hl
    hHop haH hjop hjin hkop hHk hkl

end PEqualNP.Outside.L_meta_3566.FourGateRestriction

namespace PEqualNP.Outside.L_meta_3566.UniformSavingPeel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership
open Pruning GateSavings

variable {n : ℕ}

def UniformPeel (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (z : Fin n) : Prop :=
  ∀ C : Circuit, IsAO2 n C → circuitFun n C = graphFun G ∅ →
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D =
      (fun y : Fin n → Bool => @decide (∃ a b : Fin n,
        (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a = true ∧ y b = true)
        (Classical.propDecidable _)) ∧ D.size + G.degree z ≤ C.size ∧
      ((∃ S : Finset (Fin n), CoverPromise.IsVertexCover
        (G.deleteEdges (G.incidenceSet z)) S ∧
        ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card < T.card) →
        D.size + G.degree z + 1 ≤ C.size)

lemma of_saving (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C0 : Circuit) (hC0 : IsLeastAO G C0) (z : Fin n) (D : Circuit)
    (hD : IsAO2 n D)
    (hfun : circuitFun n D = fun x => circuitFun n C0 (cutInput z x))
    (hs : D.size + G.degree z + 1 ≤ C0.size) : UniformPeel G z := by
  intro C hC hF
  have hmin := hC0.2.2 C hC hF
  refine ⟨D, hD, ?_, by omega, fun _ => by omega⟩
  rw [hfun, hC0.2.1]
  exact graph_cutInput G z

lemma three_gate_source (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C0 : Circuit) (hC0 : IsLeastAO G C0) (hfour : NoFourCycle G)
    (a u : Fin n) (h j : ℕ) (hj : j < C0.size)
    (hjor : (gateAt C0 j).op = GateOp.or) (hju : u.val ∈ (gateAt C0 j).inputs)
    (hjh : n + h ∈ (gateAt C0 j).inputs)
    (haonly : ∀ k < C0.size, a.val ∈ (gateAt C0 k).inputs → k = h)
    (hdeg : G.degree a = 2) (hhand : (gateAt C0 h).op = GateOp.and)
    (hha : a.val ∈ (gateAt C0 h).inputs) :
    ∃ z : Fin n, 0 < G.degree z ∧ UniformPeel G z := by
  obtain ⟨D, hD, hs, hf⟩ := PrivateOrAbsorb.restrict_source_saves_three G C0 hC0 hfour
    a u h j hj hjor hju hjh haonly (by omega) hhand hha
  refine ⟨a, by omega, of_saving G C0 hC0 a D hD ?_ (by omega)⟩
  simpa only [hC0.2.1] using hf

lemma four_gate_source (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C0 : Circuit) (hC0 : IsLeastAO G C0) (a u : Fin n) (H j k : ℕ)
    (hH : H < C0.size) (hj : j < C0.size) (hk : k < C0.size)
    (hHop : (gateAt C0 H).op = GateOp.and) (haH : a.val ∈ (gateAt C0 H).inputs)
    (hjop : (gateAt C0 j).op = GateOp.or)
    (hjin : (gateAt C0 j).inputs = [u.val, n + H] ∨
      (gateAt C0 j).inputs = [n + H, u.val])
    (hkop : (gateAt C0 k).op = GateOp.and) (hHk : n + H ∈ (gateAt C0 k).inputs)
    (havoid : ∃ p q : Fin n, G.Adj p q ∧ p ≠ a ∧ q ≠ a)
    (hpos : 0 < G.degree a) (hdeg : G.degree a ≤ 3) :
    ∃ z : Fin n, 0 < G.degree z ∧ UniformPeel G z := by
  obtain ⟨D, hD, hs, hf⟩ := FourGateRestriction.restrict_four_of_least G C0 hC0 a u H j k
    hH hj hk hHop haH hjop hjin hkop hHk havoid
  exact ⟨a, hpos, of_saving G C0 hC0 a D hD hf (by omega)⟩

end PEqualNP.Outside.L_meta_3566.UniformSavingPeel

namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def IndependentSupport {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v

def MaximalIndependentSupport {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : Prop :=
  IndependentSupport G S ∧ ∀ T : Finset (Fin n),
    IndependentSupport G T → S ⊆ T → T = S

def supportInput {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ S)

lemma independent_extension {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (hS : IndependentSupport G S) :
    ∃ T : Finset (Fin n), S ⊆ T ∧ MaximalIndependentSupport G T := by
  classical
  let A : Finset (Finset (Fin n)) := Finset.univ.filter fun T =>
    S ⊆ T ∧ IndependentSupport G T
  have hA : S ∈ A := by simp [A, hS]
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image A Finset.card ⟨S, hA⟩
  have hT' : S ⊆ T ∧ IndependentSupport G T := by simpa [A] using hT
  refine ⟨T, hT'.1, hT'.2, ?_⟩
  intro U hU hTU
  have hUA : U ∈ A := by simp [A, hT'.1.trans hTU, hU]
  exact (Finset.eq_of_subset_of_card_le hTU (hmax U hUA)).symm

lemma graphFun_empty_true_iff {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graphFun_pair_true {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {u v : Fin n} (huv : G.Adj u v) :
    graphFun G ∅ (pairInput u v) = true := by
  apply (graphFun_empty_true_iff G _).2
  exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

lemma graphFun_independent_false {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {S : Finset (Fin n)} (hS : IndependentSupport G S) :
    graphFun G ∅ (supportInput S) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨u, v, huv, hu, hv⟩ := (graphFun_empty_true_iff G _).mp h
  exact hS u (by simpa [supportInput] using hu) v
    (by simpa [supportInput] using hv) huv

lemma bool_true_of_le {a b : Bool} (hab : a ≤ b) (ha : a = true) : b = true := by
  cases a <;> cases b <;> simp_all [Bool.le_iff_imp]

lemma bool_false_of_le {a b : Bool} (hab : a ≤ b) (hb : b = false) : a = false := by
  cases a <;> cases b <;> simp_all [Bool.le_iff_imp]

lemma graphFun_boundary_iff {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f : (Fin n → Bool) → Bool) (hf : Monotone f) :
    f = graphFun G ∅ ↔
      (∀ u v, G.Adj u v → f (pairInput u v) = true) ∧
      (∀ S : Finset (Fin n), MaximalIndependentSupport G S →
        f (supportInput S) = false) := by
  classical
  constructor
  · intro h
    subst f
    exact ⟨fun _ _ huv => graphFun_pair_true G huv,
      fun _ hS => graphFun_independent_false G hS.1⟩
  · rintro ⟨hpos, hneg⟩
    funext x
    by_cases hx : graphFun G ∅ x = true
    · obtain ⟨u, v, huv, hu, hv⟩ := (graphFun_empty_true_iff G x).mp hx
      have hpx : pairInput u v ≤ x := by
        intro i
        apply Bool.le_iff_imp.mpr
        intro hi
        have hi' : i = u ∨ i = v := by simpa [pairInput] using hi
        rcases hi' with rfl | rfl
        · exact hu
        · exact hv
      exact (bool_true_of_le (hf hpx) (hpos u v huv)).trans hx.symm
    · let S : Finset (Fin n) := Finset.univ.filter fun i => x i = true
      have hS : IndependentSupport G S := by
        intro u hu v hv huv
        apply hx
        exact (graphFun_empty_true_iff G x).2
          ⟨u, v, huv, (Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hv).2⟩
      obtain ⟨T, hST, hT⟩ := independent_extension G S hS
      have hxT : x ≤ supportInput T := by
        intro i
        apply Bool.le_iff_imp.mpr
        intro hi
        simpa [supportInput] using hST (by simp [S, hi])
      have hfx : f x = false := bool_false_of_le (hf hxT) (hneg T hT)
      have hgx : graphFun G ∅ x = false := Bool.eq_false_iff.mpr hx
      exact hfx.trans hgx.symm

end PEqualNP.Outside.L_meta_3566

namespace PEqualNP.Outside.L_meta_3566.Splice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma stepWire_getD_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (stepWire w g).getD i false = w.getD i false := by
  simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma stepWire_getD_len (w : List Bool) (g : Gate) :
    (stepWire w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [stepWire, List.getD_eq_getElem?_getD]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

def shiftDown (wOld u : ℕ) : ℕ :=
  if wOld < u then u - 1 else u

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs.take j = pre ∧ gs.drop (j + 1) = post ∧
        gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl, rfl, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def aliasWire (wOld wNew u : ℕ) : ℕ :=
  if u = wOld then wNew else shiftDown wOld u

def aliasGate (wOld wNew : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (aliasWire wOld wNew)⟩

def dropDup (n : ℕ) (C : Circuit) (j i : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (aliasGate (n + j) i),
    aliasWire (n + j) i C.output⟩

lemma dropDup_length (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) :
    (dropDup n C j i).gates.length + 1 = C.gates.length := by
  simp only [dropDup, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

lemma dropDup_mem (n : ℕ) (C : Circuit) (j i : ℕ) (g : Gate)
    (hg : g ∈ (dropDup n C j i).gates) :
    ∃ g0 ∈ C.gates, g = g0 ∨ g = aliasGate (n + j) i g0 := by
  rcases List.mem_append.mp hg with h | h
  · exact ⟨g, List.mem_of_mem_take h, Or.inl rfl⟩
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp h
    exact ⟨g0, List.mem_of_mem_drop hg0, Or.inr rfl⟩

lemma dropDup_gateAt_lt (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length)
    (hk : k < j) : gateAt (dropDup n C j i) k = gateAt C k := by
  have h1 : k < (C.gates.take j).length := by rw [List.length_take]; omega
  simp only [gateAt, dropDup, List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  rw [List.getElem?_take_of_lt hk]

lemma dropDup_gateAt_ge (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length)
    (hjk : j ≤ k) (hk : k + 1 < C.gates.length) :
    gateAt (dropDup n C j i) k = aliasGate (n + j) i (gateAt C (k + 1)) := by
  have h1 : (C.gates.take j).length ≤ k := by rw [List.length_take]; omega
  have h2 : (C.gates.take j).length = j := by rw [List.length_take]; omega
  have h3 : j + 1 + (k - j) = k + 1 := by omega
  simp only [gateAt, dropDup, List.getD_eq_getElem?_getD, List.getElem?_append_right h1, h2,
    List.getElem?_map, List.getElem?_drop, h3]
  rw [List.getElem?_eq_getElem hk]
  rfl

lemma aliasWire_lt (m i u b : ℕ) (hi : i < m) (hm : m ≤ b) (hu : u < b + 1) :
    aliasWire m i u < b := by
  unfold aliasWire shiftDown
  split_ifs <;> omega

lemma dropDup_readsBack (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length)
    (hi : i < n + j) (hrb : ReadsBack n C) : ReadsBack n (dropDup n C j i) := by
  intro k hk u hu
  have hlen := dropDup_length n C j i hj
  by_cases hkj : k < j
  · rw [dropDup_gateAt_lt n C j i k hj hkj] at hu
    exact hrb k (by omega) u hu
  · rw [dropDup_gateAt_ge n C j i k hj (by omega) (by omega)] at hu
    obtain ⟨u0, hu0, rfl⟩ := List.mem_map.mp hu
    have := hrb (k + 1) (by omega) u0 hu0
    exact aliasWire_lt (n + j) i u0 (n + k) hi (by omega) (by omega)

lemma aliasWire_init {m i : ℕ} (_hi : i < m) (u : ℕ) :
    aliasWire m i u = if u = m then i else if u < m then u else u - 1 := by
  simp only [aliasWire, shiftDown]
  split_ifs <;> omega

lemma alias_initial {R : Bool → Bool → Prop} (hr : ∀ b, R b b)
    (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length)
    (h : R (g.op.eval (g.inputs.map fun k => w.getD k false)) (w.getD i false)) :
    ∀ u, R ((stepWire w g).getD u false) (w.getD (aliasWire w.length i u) false) := by
  intro u
  rw [aliasWire_init hi]
  by_cases he : u = w.length
  · subst u
    rw [ite_eq_left rfl, stepWire_getD_len]
    exact h
  · rw [ite_eq_right he]
    by_cases hl : u < w.length
    · rw [ite_eq_left hl, stepWire_getD_lt w g u hl]
      exact hr _
    · rw [ite_eq_right hl]
      rw [getD_ge_length _ _ (by simp [stepWire]; omega),
        getD_ge_length _ _ (by omega)]
      exact hr false

lemma alias_rel_step {R : Bool → Bool → Prop} (hr : ∀ b, R b b)
    (m i : ℕ) (hi : i < m) (a b : List Bool) (hlen : a.length = b.length + 1)
    (hm : m ≤ b.length) (g : Gate)
    (hmono : ∀ (f h : ℕ → Bool), (∀ u, R (f u) (h u)) →
      R (g.op.eval (g.inputs.map f)) (g.op.eval (g.inputs.map h)))
    (hab : ∀ u, R (a.getD u false) (b.getD (aliasWire m i u) false)) :
    ∀ u, R ((stepWire a g).getD u false)
      ((stepWire b (aliasGate m i g)).getD (aliasWire m i u) false) := by
  intro u
  by_cases hl : u < a.length
  · rw [stepWire_getD_lt a g u hl,
      stepWire_getD_lt b (aliasGate m i g) (aliasWire m i u)
        (aliasWire_lt m i u b.length hi hm (by omega))]
    exact hab u
  · by_cases he : u = a.length
    · subst u
      have hs : aliasWire m i a.length = b.length := by
        simp only [aliasWire, shiftDown]
        split_ifs <;> omega
      rw [hs, stepWire_getD_len, stepWire_getD_len]
      simpa only [aliasGate, List.map_map, Function.comp_def] using hmono
        (fun k => a.getD k false) (fun k => b.getD (aliasWire m i k) false) hab
    · have hs : (stepWire b (aliasGate m i g)).length ≤ aliasWire m i u := by
        simp only [stepWire, List.length_append, List.length_singleton, aliasWire, shiftDown]
        split_ifs <;> omega
      rw [getD_ge_length _ _ (by simp [stepWire]; omega), getD_ge_length _ _ hs]
      exact hr false

lemma alias_rel_post {R : Bool → Bool → Prop} (hr : ∀ b, R b b)
    (m i : ℕ) (hi : i < m) (a b : List Bool) (hlen : a.length = b.length + 1)
    (hm : m ≤ b.length) (gs : List Gate)
    (hmono : ∀ g ∈ gs, ∀ (f h : ℕ → Bool), (∀ u, R (f u) (h u)) →
      R (g.op.eval (g.inputs.map f)) (g.op.eval (g.inputs.map h)))
    (hab : ∀ u, R (a.getD u false) (b.getD (aliasWire m i u) false)) :
    ∀ u, R ((gs.foldl stepWire a).getD u false)
      (((gs.map (aliasGate m i)).foldl stepWire b).getD (aliasWire m i u) false) := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    simp only [List.foldl_cons, List.map_cons]
    apply ih (stepWire a g) (stepWire b (aliasGate m i g))
    · simp [stepWire, hlen]
    · simp [stepWire]; omega
    · intro g hg
      exact hmono g (by simp [hg])
    · exact alias_rel_step hr m i hi a b hlen hm g (hmono g (by simp)) hab

lemma dropDup_rel {R : Bool → Bool → Prop} (hr : ∀ b, R b b)
    (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (hmono : ∀ g ∈ C.gates, ∀ (f h : ℕ → Bool), (∀ u, R (f u) (h u)) →
      R (g.op.eval (g.inputs.map f)) (g.op.eval (g.inputs.map h)))
    (x : Fin n → Bool)
    (hx : R ((C.wires (List.ofFn x)).getD (n + j) false)
      ((C.wires (List.ofFn x)).getD i false)) :
    R (circuitFun n C x) (circuitFun n (dropDup n C j i) x) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, htake, hdrop, _⟩ := split_gates C.gates j hj
  have hw0_len : (pre.foldl stepWire (List.ofFn x)).length = n + j := by
    rw [foldl_stepWire_length, List.length_ofFn, hpre_len]
  rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons] at hx
  rw [foldl_stepWire_getD_lt post _ i (by rw [stepWire, List.length_append, hw0_len]; omega),
    foldl_stepWire_getD_lt post _ (n + j)
      (by rw [stepWire, List.length_append, hw0_len, List.length_singleton]; omega),
    stepWire_getD_lt _ _ i (by omega)] at hx
  have hx2 := stepWire_getD_len (pre.foldl stepWire (List.ofFn x)) gj
  rw [hw0_len] at hx2
  rw [hx2] at hx
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hr0 := alias_initial hr w0 gj i (by dsimp [w0]; omega) hx
  have hrpost := alias_rel_post hr w0.length i (by dsimp [w0]; omega)
    (stepWire w0 gj) w0 (by simp [stepWire]) (le_refl _) post
    (fun g hg => hmono g (hgs ▸ by simp [hg])) hr0 C.output
  dsimp only [w0] at hrpost
  rw [hw0_len] at hrpost
  simp only [circuitFun, Circuit.eval, dropDup, wires_eq_foldl]
  rw [htake, hdrop, hgs, List.foldl_append, List.foldl_cons, List.foldl_append]
  exact hrpost

lemma bool_and_rel {a b c d : Bool} (hab : a ≤ b) (hcd : c ≤ d) :
    (a && c) ≤ (b && d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

lemma bool_or_rel {a b c d : Bool} (hab : a ≤ b) (hcd : c ≤ d) :
    (a || c) ≤ (b || d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

lemma ao_eval_mono (g : Gate) (hao : g.op = GateOp.and ∨ g.op = GateOp.or)
    (f h : ℕ → Bool) (hfh : ∀ u, f u ≤ h u) :
    g.op.eval (g.inputs.map f) ≤ g.op.eval (g.inputs.map h) := by
  obtain ⟨op, inputs⟩ := g
  rcases hao with rfl | rfl
  · simp only [GateOp.eval]
    induction inputs with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.all_cons, id_eq]
      exact bool_and_rel (hfh a) ih
  · simp only [GateOp.eval]
    induction inputs with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.any_cons, id_eq]
      exact bool_or_rel (hfh a) ih

lemma dropDup_le (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length)
    (hi : i < n + j) (hao : AndOrOnly C) (x : Fin n → Bool)
    (hx : (C.wires (List.ofFn x)).getD (n + j) false ≤
      (C.wires (List.ofFn x)).getD i false) :
    circuitFun n C x ≤ circuitFun n (dropDup n C j i) x :=
  dropDup_rel (fun _ => le_refl _) n C j i hj hi
    (fun g hg => ao_eval_mono g (hao g hg)) x hx

lemma dropDup_ge (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length)
    (hi : i < n + j) (hao : AndOrOnly C) (x : Fin n → Bool)
    (hx : (C.wires (List.ofFn x)).getD i false ≤
      (C.wires (List.ofFn x)).getD (n + j) false) :
    circuitFun n (dropDup n C j i) x ≤ circuitFun n C x :=
  dropDup_rel (R := fun a b => b ≤ a) (fun _ => le_refl _) n C j i hj hi
    (fun g hg f h hfh => ao_eval_mono g (hao g hg) h f hfh) x hx

lemma dropDup_ao (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length)
    (hi : i < n + j) (hAO : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.TopForm.IsAO2 n (dropDup n C j i) := by
  obtain ⟨hao, hrb, h2⟩ := hAO
  refine ⟨?_, dropDup_readsBack n C j i hj hi hrb, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, h | h⟩ := dropDup_mem n C j i g hg
    · rw [h]; exact hao g0 hg0
    · rw [h]; exact hao g0 hg0
  · intro g hg
    obtain ⟨g0, hg0, h | h⟩ := dropDup_mem n C j i g hg
    · rw [h]; exact h2 g0 hg0
    · rw [h]; simp only [aliasGate, List.length_map]; exact h2 g0 hg0

lemma stepWire_mono (g : Gate) (hao : g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (hlen : a.length = b.length)
    (hab : ∀ u, a.getD u false ≤ b.getD u false) :
    ∀ u, (stepWire a g).getD u false ≤ (stepWire b g).getD u false := by
  intro u
  by_cases hl : u < a.length
  · rw [stepWire_getD_lt _ _ _ hl, stepWire_getD_lt _ _ _ (by omega)]
    exact hab u
  · by_cases he : u = a.length
    · rw [he, stepWire_getD_len, hlen, stepWire_getD_len]
      exact ao_eval_mono g hao _ _ hab
    · rw [getD_ge_length _ _ (by simp [stepWire]; omega),
        getD_ge_length _ _ (by simp [stepWire]; omega)]

lemma foldl_mono (gs : List Gate) (hao : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (hlen : a.length = b.length)
    (hab : ∀ u, a.getD u false ≤ b.getD u false) :
    ∀ u, (gs.foldl stepWire a).getD u false ≤ (gs.foldl stepWire b).getD u false := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    simp only [List.foldl_cons]
    exact ih (fun g hg => hao g (by simp [hg]))
      (stepWire a g) (stepWire b g) (by simp [stepWire, hlen])
      (stepWire_mono g (hao g (by simp)) a b hlen hab)

lemma circuitFun_monotone (n : ℕ) (C : Circuit) (hao : AndOrOnly C) :
    Monotone (circuitFun n C) := by
  intro x y hxy
  apply foldl_mono C.gates hao (List.ofFn x) (List.ofFn y) (by simp)
  intro u
  by_cases hu : u < n
  · rw [List.getD_eq_getElem _ _ (by simpa), List.getD_eq_getElem _ _ (by simpa)]
    simpa using hxy ⟨u, hu⟩
  · rw [getD_ge_length _ _ (by simpa using Nat.le_of_not_gt hu),
      getD_ge_length _ _ (by simpa using Nat.le_of_not_gt hu)]

end PEqualNP.Outside.L_meta_3566.Splice

namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma dropDup_boundary_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (hpos : ∀ u v, G.Adj u v →
      (C.wires (List.ofFn (pairInput u v))).getD (n + j) false ≤
      (C.wires (List.ofFn (pairInput u v))).getD i false)
    (hneg : ∀ S : Finset (Fin n), MaximalIndependentSupport G S →
      (C.wires (List.ofFn (supportInput S))).getD i false ≤
      (C.wires (List.ofFn (supportInput S))).getD (n + j) false) :
    circuitFun n (Splice.dropDup n C j i) = graphFun G ∅ := by
  apply (graphFun_boundary_iff G _
    (Splice.circuitFun_monotone n _ (Splice.dropDup_ao n C j i hj hi hAO).1)).2
  constructor
  · intro u v huv
    apply bool_true_of_le (Splice.dropDup_le n C j i hj hi hAO.1 _ (hpos u v huv))
    rw [hfun]
    exact graphFun_pair_true G huv
  · intro S hS
    apply bool_false_of_le (Splice.dropDup_ge n C j i hj hi hAO.1 _ (hneg S hS))
    rw [hfun]
    exact graphFun_independent_false G hS.1

lemma least_boundary_separation {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C)
    (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j) :
    (∃ u v, G.Adj u v ∧
      (C.wires (List.ofFn (pairInput u v))).getD (n + j) false = true ∧
      (C.wires (List.ofFn (pairInput u v))).getD i false = false) ∨
    ∃ S : Finset (Fin n), MaximalIndependentSupport G S ∧
      (C.wires (List.ofFn (supportInput S))).getD (n + j) false = false ∧
      (C.wires (List.ofFn (supportInput S))).getD i false = true := by
  classical
  by_contra hbad
  have hfun : circuitFun n (Splice.dropDup n C j i) = graphFun G ∅ := by
    apply dropDup_boundary_correct G C hLeast.1 hLeast.2.1 j i hj hi
    · intro u v huv
      apply Bool.le_iff_imp.mpr
      intro hg
      by_contra hh
      exact hbad (Or.inl ⟨u, v, huv, hg, Bool.eq_false_iff.mpr hh⟩)
    · intro S hS
      apply Bool.le_iff_imp.mpr
      intro hh
      by_contra hg
      exact hbad (Or.inr ⟨S, hS, Bool.eq_false_iff.mpr hg, hh⟩)
  have hsize := hLeast.2.2 _ (Splice.dropDup_ao n C j i hj hi hLeast.1) hfun
  have hlength := Splice.dropDup_length n C j i hj
  simp only [Circuit.size] at hsize
  omega

end PEqualNP.Outside.L_meta_3566

namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm Splice

lemma gate_wire_eval {n : ℕ} (C : Circuit) (hrb : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        (C.wires (List.ofFn x)).getD i false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, _, _, hgj⟩ := split_gates C.gates j hj
  have hw0_len : (pre.foldl stepWire (List.ofFn x)).length = n + j := by
    rw [foldl_stepWire_length, List.length_ofFn, hpre_len]
  have hgate : gateAt C j = gj := by
    simpa only [gateAt, List.getD_eq_getElem _ _ hj] using hgj
  have hpre : ∀ i, i < n + j →
      (C.wires (List.ofFn x)).getD i false =
        (pre.foldl stepWire (List.ofFn x)).getD i false := by
    intro i hi
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons,
      foldl_stepWire_getD_lt _ _ _ (by simp [stepWire, hw0_len]<;> omega),
      stepWire_getD_lt _ _ _ (by omega)]
  have hm : (gateAt C j).inputs.map (fun i => (C.wires (List.ofFn x)).getD i false) =
      (gateAt C j).inputs.map (fun i => (pre.foldl stepWire (List.ofFn x)).getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact hpre i (hrb j hj i hi)
  rw [hm, hgate, wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons,
    foldl_stepWire_getD_lt _ _ _ (by simp [stepWire, hw0_len]<;> omega)]
  rw [← hw0_len, stepWire_getD_len]

lemma or_input_le_gate {n : ℕ} (C : Circuit) (hrb : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (i : ℕ) (hi : i ∈ (gateAt C j).inputs) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD i false ≤
      (C.wires (List.ofFn x)).getD (n + j) false := by
  rw [gate_wire_eval C hrb j hj x, hop]
  apply Bool.le_iff_imp.mpr
  intro h
  simp only [GateOp.eval, List.any_eq_true, List.mem_map]
  exact ⟨true, ⟨i, hi, h⟩, rfl⟩

end PEqualNP.Outside.L_meta_3566

namespace PEqualNP.Outside.L_meta_3566.MixedColor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩


lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha

lemma binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
end PEqualNP.Outside.L_meta_3566.MixedColor

namespace PEqualNP.Outside.L_meta_3566.WireFacts

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm

lemma wire_monotone {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (w : ℕ) :
    Monotone (fun x : Fin n → Bool => (C.wires (List.ofFn x)).getD w false) := by
  change Monotone (circuitFun n {C with output := w})
  exact Splice.circuitFun_monotone n {C with output := w} hAO.1

end PEqualNP.Outside.L_meta_3566.WireFacts

namespace PEqualNP.Outside.L_meta_3566.AndChild

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

lemma not_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C)
    (j i : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = .and) (hi : i ∈ (gateAt C j).inputs) :
    ¬ (∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD i false = true → graphFun G ∅ x = true) := by
  intro hbelow
  have hib : i < n + j := hLeast.1.2.1 j hj i hi
  rcases least_boundary_separation G C hLeast j i hj hib with
    ⟨u, v, _, hgate, hchild⟩ | ⟨S, hS, _, hchild⟩
  · have hchild' :=
      (((MixedColor.val_and (n := n) (C := C) (x := List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))
        (by simp) hj hop).mp hgate) i hi).2
    change (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD i false = true at hchild'
    rw [hchild] at hchild'
    cases hchild'
  · have hf := hbelow (supportInput S) hchild
    rw [graphFun_independent_false G hS.1] at hf
    cases hf

end PEqualNP.Outside.L_meta_3566.AndChild

namespace PEqualNP.Outside.L_meta_3566.OrCharge

lemma frontier_bound {α : Type*} [DecidableEq α]
    (F : ℕ → Finset α) (Q : Finset ℕ) (good : ℕ → Prop)
    (K : ℕ)
    (hstep : ∀ w < K, good w → 1 < (F w).card →
      ∃ A : Finset ℕ, (∀ v ∈ A, v < w ∧ good v) ∧
        F w ⊆ A.biUnion F ∧ A.card ≤ 1 + (if w ∈ Q then 1 else 0))
    (W : Finset ℕ) (hW : ∀ w ∈ W, w < K ∧ good w) :
    (W.biUnion F).card ≤ ((Finset.range K).filter (· ∈ Q)).card + W.card := by
  classical
  induction K generalizing W with
  | zero =>
      have hw : W = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        exact Nat.not_lt_zero w (hW w hw).1
      simp [hw]
  | succ K ih =>
      have hstep' : ∀ w < K, good w → 1 < (F w).card →
          ∃ A : Finset ℕ, (∀ v ∈ A, v < w ∧ good v) ∧
            F w ⊆ A.biUnion F ∧ A.card ≤ 1 + (if w ∈ Q then 1 else 0) := by
        intro w hw
        exact hstep w (by omega)
      have hcount : ((Finset.range (K + 1)).filter (· ∈ Q)).card =
          ((Finset.range K).filter (· ∈ Q)).card + (if K ∈ Q then 1 else 0) := by
        rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs with hK
        · rw [Finset.card_insert_of_notMem]
          simp
        · simp
      by_cases hKW : K ∈ W
      · have hEr : ∀ w ∈ W.erase K, w < K ∧ good w := by
          intro w hw
          obtain ⟨hwne, hwW⟩ := Finset.mem_erase.mp hw
          obtain ⟨hwlt, hwg⟩ := hW w hwW
          exact ⟨by omega, hwg⟩
        have hWcard : (W.erase K).card + 1 = W.card := Finset.card_erase_add_one hKW
        by_cases hsmall : (F K).card ≤ 1
        · have ih' := ih hstep' (W.erase K) hEr
          have hcover : W.biUnion F = F K ∪ (W.erase K).biUnion F := by
            have he := congrArg (fun T : Finset ℕ => T.biUnion F) (Finset.insert_erase hKW).symm
            simpa only [Finset.biUnion_insert] using he
          have hc : (W.biUnion F).card ≤ (F K).card + ((W.erase K).biUnion F).card := by
            rw [hcover]
            exact Finset.card_union_le _ _
          rw [hcount]
          split_ifs <;> omega
        · obtain ⟨A, hA, hsub, hAc⟩ := hstep K (by omega) (hW K hKW).2 (by omega)
          let W' := W.erase K ∪ A
          have hW' : ∀ w ∈ W', w < K ∧ good w := by
            intro w hw
            rcases Finset.mem_union.mp hw with hw | hw
            · exact hEr w hw
            · exact hA w hw
          have hcover : W.biUnion F ⊆ W'.biUnion F := by
            intro a ha
            obtain ⟨w, hw, ha⟩ := Finset.mem_biUnion.mp ha
            by_cases hwK : w = K
            · subst w
              obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hsub ha)
              exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
            · exact Finset.mem_biUnion.mpr ⟨w,
                Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwK, hw⟩), ha⟩
          have ih' := ih hstep' W' hW'
          have hc := Finset.card_le_card hcover
          have hWc : W'.card ≤ (W.erase K).card + A.card := Finset.card_union_le _ _
          rw [hcount]
          split_ifs at hAc ⊢ <;> omega
      · have hW' : ∀ w ∈ W, w < K ∧ good w := by
          intro w hw
          obtain ⟨hwlt, hwg⟩ := hW w hw
          have hwne : w ≠ K := by
            intro h
            subst w
            contradiction
          exact ⟨by omega, hwg⟩
        have ih' := ih hstep' W hW'
        rw [hcount]
        split_ifs <;> omega

end PEqualNP.Outside.L_meta_3566.OrCharge

namespace PEqualNP.Outside.L_meta_3566.OrCharge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

def wire {n : ℕ} (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

end PEqualNP.Outside.L_meta_3566.OrCharge

namespace PEqualNP.Outside.L_meta_3566.SemanticPurity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership

def W (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma W_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    W n C w x = x ⟨w, hw⟩ := by
  exact MixedColor.val_ofFn C x ⟨w, hw⟩

lemma W_gate {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (a b : ℕ) (hab : (gateAt C j).inputs = [a, b]) (x : Fin n → Bool) :
    W n C (n + j) x = (gateAt C j).op.eval [W n C a x, W n C b x] := by
  rw [W, gate_wire_eval C hAO.2.1 j hj x, hab]
  rfl

lemma wire_one {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (w : ℕ) (hw : w < n + C.gates.length) : W n C w (fun _ => true) = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwi : w < n
    · exact W_input C w hwi (fun _ => true)
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    obtain ⟨a, b, hab⟩ := MixedColor.binaryInputs hAO hj
    have ha : a < n + j := hAO.2.1 j hj a (by simp [hab])
    have hb : b < n + j := hAO.2.1 j hj b (by simp [hab])
    rw [W_gate C hAO j hj a b hab, ih a ha (by omega), ih b hb (by omega)]
    rcases hAO.1 (gateAt C j) (MixedColor.gateAt_mem hj) with hop | hop <;>
      simp [hop, GateOp.eval]

lemma not_equal_earlier {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (j i : ℕ)
    (hj : j < C.gates.length) (hi : i < n + j) :
    W n C (n + j) ≠ W n C i := by
  intro heq
  rcases least_boundary_separation G C hLeast j i hj hi with ⟨u,v,_,hu,hv⟩ | ⟨S,_,hu,hv⟩
  · have h := congrFun heq (pairInput u v)
    simp only [W] at h
    rw [hu, hv] at h
    cases h
  · have h := congrFun heq (supportInput S)
    simp only [W] at h
    rw [hu, hv] at h
    cases h

end PEqualNP.Outside.L_meta_3566.SemanticPurity

namespace PEqualNP.Outside.L_meta_3566.TopFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership OrCharge

noncomputable def leaves {n : ℕ} (C : Circuit) (w : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter fun j => (gateAt C j).op = .and ∧
    Relation.ReflTransGen (MixedColor.OrStep n C) w (n + j)

def BelowWire {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, wire C w x = true → graphFun G ∅ x = true

lemma leaves_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    leaves (n := n) C w = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨_, _, hpath⟩ := Finset.mem_filter.mp hj
  rcases Relation.ReflTransGen.cases_head hpath with he | ⟨v, hs, _⟩
  · omega
  · obtain ⟨k, _, he, _, _, _⟩ := hs
    omega

lemma leaves_not_or {n : ℕ} (C : Circuit) (j : ℕ)
    (hop : (gateAt C j).op ≠ .or) :
    leaves (n := n) C (n + j) ⊆ {j} := by
  classical
  intro k hk
  obtain ⟨_, _, hpath⟩ := Finset.mem_filter.mp hk
  rcases Relation.ReflTransGen.cases_head hpath with he | ⟨v, hs, _⟩
  · exact Finset.mem_singleton.mpr (by omega)
  · obtain ⟨r, _, he, hor, _, _⟩ := hs
    have hrj : r = j := by omega
    subst r
    exact (hop hor).elim

lemma leaves_or {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = .or) :
    leaves (n := n) C (n + j) = (gateAt C j).inputs.toFinset.biUnion (leaves (n := n) C) := by
  classical
  ext k
  constructor
  · intro hk
    obtain ⟨hklt, hkand, hpath⟩ := Finset.mem_filter.mp hk
    rcases Relation.ReflTransGen.cases_head hpath with he | ⟨v, hs, hrest⟩
    · have hkj : k = j := by omega
      subst k
      rw [hop] at hkand
      cases hkand
    · obtain ⟨r, _, he, _, hvin, _⟩ := hs
      have hrj : r = j := by omega
      subst r
      exact Finset.mem_biUnion.mpr ⟨v, List.mem_toFinset.mpr hvin,
        Finset.mem_filter.mpr ⟨hklt, hkand, hrest⟩⟩
  · intro hk
    obtain ⟨v, hv, hk⟩ := Finset.mem_biUnion.mp hk
    obtain ⟨hklt, hkand, hrest⟩ := Finset.mem_filter.mp hk
    have hvin := List.mem_toFinset.mp hv
    apply Finset.mem_filter.mpr
    refine ⟨hklt, hkand, Relation.ReflTransGen.head ?_ hrest⟩
    exact ⟨j, hj, rfl, hop, hvin, hAO.2.1 j hj v hvin⟩

lemma leaf_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (w j : ℕ) (hw : BelowWire G C w) (hj : j ∈ leaves (n := n) C w) :
    BelowF G C j := by
  classical
  obtain ⟨_, _, hpath⟩ := Finset.mem_filter.mp hj
  intro x hx
  apply hw x
  exact MixedColor.orStep_up (n := n) (by simp) hpath hx

lemma leaves_card_le_orT {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (w : ℕ) (hw : w < n + C.size)
    (hbelow : BelowWire G C w) :
    (leaves (n := n) C w).card ≤ (orT G C).card + 1 := by
  classical
  let Q := (orT G C).image (fun j => n + j)
  have hstep : ∀ v < n + C.size, BelowWire G C v → 1 < (leaves (n := n) C v).card →
      ∃ A : Finset ℕ, (∀ u ∈ A, u < v ∧ BelowWire G C u) ∧
        leaves (n := n) C v ⊆ A.biUnion (leaves (n := n) C) ∧
        A.card ≤ 1 + (if v ∈ Q then 1 else 0) := by
    intro v hv hvg hlarge
    have hn : n ≤ v := by
      by_contra hn
      rw [leaves_input C v (by omega), Finset.card_empty] at hlarge
      omega
    let j := v - n
    have hj : j < C.gates.length := by
      change v - n < C.gates.length
      change v < n + C.gates.length at hv
      omega
    have hvj : n + j = v := by omega
    have hgmem := MixedColor.gateAt_mem hj
    have hor : (gateAt C j).op = .or := by
      rcases hAO.1 _ hgmem with hand | hor
      · have hc := Finset.card_le_card (leaves_not_or (n := n) C j (by rw [hand]; intro h; cases h))
        rw [hvj, Finset.card_singleton] at hc
        omega
      · exact hor
    have hvQ : v ∈ Q := by
      apply Finset.mem_image.mpr
      refine ⟨j, ?_, hvj⟩
      simp only [orT, gatesWhere, Finset.mem_filter, Finset.mem_range]
      refine ⟨hj, hor, ?_⟩
      intro x hx
      apply hvg x
      change wire C (n + j) x = true at hx
      simpa only [hvj] using hx
    refine ⟨(gateAt C j).inputs.toFinset, ?_, ?_, ?_⟩
    · intro u hu
      have huin := List.mem_toFinset.mp hu
      refine ⟨by have h := hAO.2.1 j hj u huin; omega, ?_⟩
      intro x hx
      apply hvg x
      have hle := or_input_le_gate C hAO.2.1 j hj hor u huin x
      rw [hvj] at hle
      exact Bool.le_iff_imp.mp hle hx
    · rw [← hvj, leaves_or C hAO j hj hor]
    · rw [if_pos hvQ]
      exact (List.toFinset_card_le _).trans (by have hh := hAO.2.2 _ hgmem; omega)
  have h := frontier_bound (leaves (n := n) C) Q (BelowWire G C) (n + C.size)
    hstep {w} (by simpa using And.intro hw hbelow)
  have hfilter : (Finset.range (n + C.size)).filter (· ∈ Q) = Q := by
    ext v
    constructor
    · exact fun hv => (Finset.mem_filter.mp hv).2
    · intro hv
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
      have hjparts : j < C.gates.length ∧ (gateAt C j).op = .or ∧ BelowF G C j := by
        simpa only [orT, gatesWhere, Finset.mem_filter, Finset.mem_range] using hj
      have hjlt := hjparts.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by change n + j < n + C.gates.length; omega),
        Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
  have hcard : Q.card = (orT G C).card :=
    Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)
  simpa [hfilter, hcard] using h

end PEqualNP.Outside.L_meta_3566.TopFrontier

namespace PEqualNP.Outside.L_meta_3566.TopFrontierCoverage

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership MixedColor


lemma input_not_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u : Fin n) :
    ¬ (∀ x : Fin n → Bool, val C (List.ofFn x) u.val = true → graphFun G ∅ x = true) := by
  intro h
  have hsingle : val C (List.ofFn (pairInput u u)) u.val = true := by
    rw [val_ofFn]
    simp [pairInput]
  have hf := (graphFun_pair G u u).mp (h (pairInput u u) hsingle)
  exact G.irrefl hf

lemma true_below_reaches_and {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (x : Fin n → Bool) (w : ℕ)
    (hbelow : ∀ y : Fin n → Bool, val C (List.ofFn y) w = true → graphFun G ∅ y = true)
    (htrue : val C (List.ofFn x) w = true) :
    ∃ j < C.gates.length, (gateAt C j).op = .and ∧
      Relation.ReflTransGen (OrStep n C) w (n + j) ∧
      val C (List.ofFn x) (n + j) = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have hn : n ≤ w := by
      by_contra h
      exact input_not_below G C ⟨w, by omega⟩ hbelow
    have hvalid : w < n + C.gates.length := by
      by_contra h
      rw [val_ge (n := n) (by simp) (by omega)] at htrue
      cases htrue
    let j := w - n
    have hj : j < C.gates.length := by dsimp [j]; omega
    have hw : w = n + j := by dsimp [j]; omega
    rcases hAO.1 _ (gateAt_mem hj) with hop | hop
    · exact ⟨j, hj, hop, by rw [hw], by simpa only [hw] using htrue⟩
    · obtain ⟨i, hi, hib, hit⟩ := (val_or (n := n) (C := C) (x := List.ofFn x) (by simp) hj hop).mp
        (by simpa only [hw] using htrue)
      have hstep : OrStep n C w i := ⟨j, hj, hw, hop, hi, hib⟩
      have hbelow_i : ∀ y : Fin n → Bool, val C (List.ofFn y) i = true → graphFun G ∅ y = true := by
        intro y hy
        exact hbelow y (orStep_up (by simp) (Relation.ReflTransGen.single hstep) hy)
      obtain ⟨k, hk, hkop, hpath, hkt⟩ := ih i (by omega) hbelow_i hit
      exact ⟨k, hk, hkop, Relation.ReflTransGen.head hstep hpath, hkt⟩

lemma reached_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (w j : ℕ)
    (hbelow : ∀ y : Fin n → Bool, val C (List.ofFn y) w = true → graphFun G ∅ y = true)
    (hreach : Relation.ReflTransGen (OrStep n C) w (n + j)) : BelowF G C j := by
  intro x hx
  exact hbelow x (orStep_up (by simp) hreach hx)

lemma edge_reaches_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (a b : Fin n) (hab : G.Adj a b) :
    ∃ j ∈ tops G C, Relation.ReflTransGen (OrStep n C) C.output (n + j) ∧
      gateVal n C j (pairInput a b) = true := by
  classical
  have hb : ∀ y : Fin n → Bool, val C (List.ofFn y) C.output = true → graphFun G ∅ y = true := by
    intro y hy
    change circuitFun n C y = true at hy
    simpa only [hfun] using hy
  have ht : val C (List.ofFn (pairInput a b)) C.output = true := by
    change circuitFun n C (pairInput a b) = true
    rw [hfun]
    exact (graphFun_pair G a b).mpr hab
  obtain ⟨j, hj, hop, hr, hv⟩ := true_below_reaches_and G C hAO (pairInput a b) C.output hb ht
  refine ⟨j, ?_, hr, hv⟩
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
  exact ⟨hj, hop, reached_below G C C.output j hb hr⟩

end PEqualNP.Outside.L_meta_3566.TopFrontierCoverage

namespace PEqualNP.Outside.L_meta_3566.ParallelRewrite

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma value_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    value C x w = x ⟨w, hw⟩ :=
  MixedColor.val_ofFn C x ⟨w, hw⟩

lemma value_missing {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : value C x w = false :=
  MixedColor.val_ge (n := n) (C := C) (x := List.ofFn x) (by simp) hw

lemma value_gate {n : ℕ} (C : Circuit) (hback : ReadsBack n C)
    (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    value C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (value C x)) :=
  gate_wire_eval C hback j hj x

lemma wire_relation {n : ℕ} (C D : Circuit)
    (hsize : D.gates.length = C.gates.length)
    (hC : ReadsBack n C) (hD : ReadsBack n D) (x : Fin n → Bool)
    (R : ℕ → Bool → Bool → Prop)
    (hinput : ∀ w (hw : w < n), R w (x ⟨w, hw⟩) (x ⟨w, hw⟩))
    (hmissing : ∀ w, n + C.gates.length ≤ w → R w false false)
    (hstep : ∀ j, j < C.gates.length →
      (∀ i, i < n + j → R i (value C x i) (value D x i)) →
      R (n + j)
        ((gateAt C j).op.eval ((gateAt C j).inputs.map (value C x)))
        ((gateAt D j).op.eval ((gateAt D j).inputs.map (value D x)))) :
    ∀ w, R w (value C x w) (value D x w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · rw [value_input C x w hw, value_input D x w hw]
      exact hinput w hw
    by_cases hlim : w < n + C.gates.length
    · let j := w - n
      have hj : j < C.gates.length := by dsimp [j]; omega
      have hjD : j < D.gates.length := by omega
      have heq : n + j = w := by dsimp [j]; omega
      rw [← heq, value_gate C hC x j hj, value_gate D hD x j hjD]
      apply hstep j hj
      intro i hi
      exact ih i (by omega)
    · have hge : n + C.gates.length ≤ w := by omega
      rw [value_missing C x w hge, value_missing D x w (by omega)]
      exact hmissing w hge

lemma preserve_closed_wires {n : ℕ} (C D : Circuit)
    (hsize : D.gates.length = C.gates.length)
    (hC : ReadsBack n C) (hD : ReadsBack n D)
    (P : ℕ → Prop)
    (hsame : ∀ j, j < C.gates.length → P (n + j) → gateAt D j = gateAt C j)
    (hclosed : ∀ j, j < C.gates.length → P (n + j) →
      ∀ i ∈ (gateAt C j).inputs, P i) :
    ∀ x : Fin n → Bool, ∀ w, P w → value D x w = value C x w := by
  intro x
  apply wire_relation C D hsize hC hD x (fun w a b => P w → b = a)
  · intro w hw _
    rfl
  · intro w hw _
    rfl
  · intro j hj ih hp
    rw [hsame j hj hp]
    apply congrArg (gateAt C j).op.eval
    apply List.map_congr_left
    intro i hi
    exact ih i (hC j hj i hi) (hclosed j hj hp i hi)

def rewrite (C : Circuit) (f : Fin C.gates.length → Gate) : Circuit :=
  ⟨List.ofFn f, C.output⟩

lemma rewrite_length (C : Circuit) (f : Fin C.gates.length → Gate) :
    (rewrite C f).gates.length = C.gates.length := by simp [rewrite]

lemma rewrite_size (C : Circuit) (f : Fin C.gates.length → Gate) :
    (rewrite C f).size = C.size := by simp [Circuit.size, rewrite]

lemma rewrite_gate (C : Circuit) (f : Fin C.gates.length → Gate)
    (j : ℕ) (hj : j < C.gates.length) :
    gateAt (rewrite C f) j = f ⟨j, hj⟩ := by
  simp [rewrite, gateAt, List.getD_eq_getElem?_getD, hj]

lemma rewrite_ao {n : ℕ} (C : Circuit) (f : Fin C.gates.length → Gate)
    (hop : ∀ j, (f j).op = .and ∨ (f j).op = .or)
    (hbinary : ∀ j, (f j).inputs.length = 2)
    (hback : ∀ j, ∀ w ∈ (f j).inputs, w < n + j.val) :
    IsAO2 n (rewrite C f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    change g ∈ List.ofFn f at hg
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
    exact hop j
  · intro j hj w hw
    have hj' : j < C.gates.length := by simpa only [rewrite_length] using hj
    rw [rewrite_gate C f j hj'] at hw
    exact hback ⟨j, hj'⟩ w hw
  · intro g hg
    change g ∈ List.ofFn f at hg
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
    exact hbinary j

end PEqualNP.Outside.L_meta_3566.ParallelRewrite

namespace PEqualNP.Outside.L_meta_3566.LeastGateLive

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm SemanticPurity ParallelRewrite

lemma output_or_later_reader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length) :
    C.output = n + j ∨ ∃ k, j < k ∧ k < C.gates.length ∧
      n + j ∈ (gateAt C k).inputs := by
  classical
  by_contra h
  have hout : C.output ≠ n + j := fun he => h (Or.inl he)
  have hreader : ∀ k, k < C.gates.length → n + j ∉ (gateAt C k).inputs := by
    intro k hk hin
    have hlt := hLeast.1.2.1 k hk (n + j) hin
    exact h (Or.inr ⟨k, by omega, hk, hin⟩)
  obtain ⟨a, b, hab⟩ := MixedColor.binaryInputs hLeast.1 hj
  have ha : a < n + j := hLeast.1.2.1 j hj a (by simp [hab])
  let f : Fin C.gates.length → Gate := fun k =>
    if k.val = j then ⟨.or, [a, a]⟩ else gateAt C k.val
  let D := rewrite C f
  have hlen : D.gates.length = C.gates.length := rewrite_length C f
  have hsize : D.size = C.size := rewrite_size C f
  have hgate (k : ℕ) (hk : k < C.gates.length) :
      gateAt D k = if k = j then ⟨.or, [a, a]⟩ else gateAt C k := by
    exact rewrite_gate C f k hk
  have hAO : IsAO2 n D := by
    apply rewrite_ao C f
    · intro k
      by_cases hk : k.val = j
      · simp [f, hk]
      · simpa [f, hk] using hLeast.1.1 _ (MixedColor.gateAt_mem k.isLt)
    · intro k
      by_cases hk : k.val = j
      · simp [f, hk]
      · simpa [f, hk] using hLeast.1.2.2 _ (MixedColor.gateAt_mem k.isLt)
    · intro k i hi
      by_cases hk : k.val = j
      · simp only [f, ite_eq_left hk, List.mem_cons, List.not_mem_nil, or_false, or_self] at hi
        subst i
        simpa only [hk] using ha
      · simp only [f, ite_eq_right hk] at hi
        exact hLeast.1.2.1 k.val k.isLt i hi
  have hstable : ∀ x : Fin n → Bool, ∀ z, z ≠ n + j → value D x z = value C x z := by
    intro x
    apply wire_relation C D hlen hLeast.1.2.1 hAO.2.1 x
      (fun z old new => z ≠ n + j → new = old)
    · intro z hz _
      rfl
    · intro z hz _
      rfl
    · intro k hk ih hne
      have hkj : k ≠ j := by omega
      rw [hgate k hk, ite_eq_right hkj]
      apply congrArg (gateAt C k).op.eval
      apply List.map_congr_left
      intro i hi
      exact ih i (hLeast.1.2.1 k hk i hi) (fun he => hreader k hk (he ▸ hi))
  have hfun : circuitFun n D = graphFun G ∅ := by
    rw [← hLeast.2.1]
    funext x
    change value D x C.output = value C x C.output
    exact hstable x C.output hout
  have hLD : IsLeastAO G D := by
    refine ⟨hAO, hfun, ?_⟩
    intro E hE hEf
    rw [hsize]
    exact hLeast.2.2 E hE hEf
  apply not_equal_earlier G D hLD j a (by omega) ha
  funext x
  change value D x (n + j) = value D x a
  rw [value_gate D hAO.2.1 x j (by omega), hgate j hj, ite_eq_left rfl]
  simp [GateOp.eval]

end PEqualNP.Outside.L_meta_3566.LeastGateLive

namespace PEqualNP.Outside.L_meta_3566.JunkPurity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership SemanticPurity

lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, _, _, hgk⟩ := Splice.split_gates C.gates k hk
  have hga : gateAt C k = gk := by simpa only [gateAt, List.getD_eq_getElem _ _ hk] using hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h

lemma cone_step {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) {i j k : ℕ}
    (hk : k < C.gates.length) (hm : n + j ∈ (gateAt C k).inputs)
    (hi : i = j ∨ InCone n C i j) : InCone n C i k := by
  apply (inCone_iff n C i k hk).mpr
  refine ⟨n + j, hm, by omega, hAO.2.1 k hk _ hm, ?_⟩
  simpa using hi

lemma cone_trans {n : ℕ} (C : Circuit) {i j k : ℕ}
    (hk : k < C.gates.length) (hij : InCone n C i j) (hjk : InCone n C j k) :
    InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    obtain ⟨w, hw, hn, hlt, heq | hc⟩ := (inCone_iff n C j k hk).mp hjk
    · exact (inCone_iff n C i k hk).mpr ⟨w, hw, hn, hlt, Or.inr (heq ▸ hij)⟩
    · exact (inCone_iff n C i k hk).mpr
        ⟨w, hw, hn, hlt, Or.inr (ih (w-n) (by omega) (by omega) hc)⟩

lemma reaches_and_or_output {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (hlive : ∀ j, j < C.gates.length → C.output = n+j ∨
      ∃ k, j < k ∧ k < C.gates.length ∧ n+j ∈ (gateAt C k).inputs) :
    ∀ j, j < C.gates.length →
      Relation.ReflTransGen (MixedColor.OrStep n C) C.output (n+j) ∨
      ∃ k w, k < C.gates.length ∧ (gateAt C k).op = .and ∧
        w ∈ (gateAt C k).inputs ∧ Relation.ReflTransGen (MixedColor.OrStep n C) w (n+j) := by
  intro j hj
  have haux : ∀ d j, C.gates.length-j = d → j < C.gates.length →
      Relation.ReflTransGen (MixedColor.OrStep n C) C.output (n+j) ∨
      ∃ k w, k < C.gates.length ∧ (gateAt C k).op = .and ∧
        w ∈ (gateAt C k).inputs ∧ Relation.ReflTransGen (MixedColor.OrStep n C) w (n+j) := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro j hd hj
      rcases hlive j hj with hout | ⟨k,hjk,hk,hread⟩
      · left; rw [hout]
      · rcases hAO.1 _ (MixedColor.gateAt_mem hk) with ha | ho
        · exact Or.inr ⟨k,n+j,hk,ha,hread,.refl⟩
        · have hs : MixedColor.OrStep n C (n+k) (n+j) :=
            ⟨k,hk,rfl,ho,hread,by omega⟩
          rcases ih (C.gates.length-k) (by omega) k rfl hk with hp | ⟨a,w,ha,hop,hw,hp⟩
          · exact Or.inl (hp.tail hs)
          · exact Or.inr ⟨a,w,ha,hop,hw,hp.tail hs⟩
  exact haux _ j rfl hj

end PEqualNP.Outside.L_meta_3566.JunkPurity

namespace PEqualNP.Outside.L_meta_3566.AliasErase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership Splice ParallelRewrite

lemma wire_eq {n : ℕ} (C : Circuit) (j s : ℕ) (hj : j < C.gates.length)
    (hs : s < n + j) (heq : ∀ x : Fin n → Bool, value C x (n + j) = value C x s)
    (x : Fin n → Bool) (w : ℕ) :
    value C x w = value (dropDup n C j s) x (aliasWire (n + j) s w) := by
  let Cw : Circuit := { C with output := w }
  have hmono : ∀ g ∈ Cw.gates, ∀ f h : ℕ → Bool, (∀ u, f u = h u) →
      g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map h) := by
    intro g hg f h he
    congr 1
    exact List.map_congr_left (fun u _ => he u)
  have hr := dropDup_rel (R := Eq) (fun _ => rfl) n Cw j s hj hs hmono x (heq x)
  exact hr

lemma function_eq {n : ℕ} (C : Circuit) (j s : ℕ) (hj : j < C.gates.length)
    (hs : s < n + j) (heq : ∀ x : Fin n → Bool, value C x (n + j) = value C x s) :
    circuitFun n (dropDup n C j s) = circuitFun n C := by
  funext x
  exact (wire_eq C j s hj hs heq x C.output).symm

def oldIndex (j k : ℕ) : ℕ := if k < j then k else k + 1

lemma oldIndex_injective (j : ℕ) : Function.Injective (oldIndex j) := by
  intro a b h
  unfold oldIndex at h
  split_ifs at h <;> omega

lemma gate_eq {n : ℕ} (C : Circuit) (j s : ℕ) (hj : j < C.gates.length)
    (k : ℕ) (hk : k < (dropDup n C j s).gates.length) :
    (gateAt (dropDup n C j s) k).op = (gateAt C (oldIndex j k)).op := by
  have hlen := dropDup_length n C j s hj
  by_cases hkj : k < j
  · rw [dropDup_gateAt_lt n C j s k hj hkj]
    simp [oldIndex, hkj]
  · rw [dropDup_gateAt_ge n C j s k hj (by omega) (by omega)]
    simp [aliasGate, oldIndex, hkj]

lemma mapped_wire {n : ℕ} (j s k : ℕ) :
    aliasWire (n + j) s (n + oldIndex j k) = n + k := by
  unfold oldIndex aliasWire shiftDown
  split_ifs <;> omega

lemma mem_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) :
    j ∈ junk G C ↔ (gateAt C j).op = .and ∧ j < C.gates.length ∧
      ∃ x : Fin n → Bool, value C x (n + j) = true ∧ graphFun G ∅ x = false := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr h.2.1, h⟩

lemma junk_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j s : ℕ) (hj : j < C.gates.length) (hs : s < n + j)
    (heq : ∀ x : Fin n → Bool, value C x (n + j) = value C x s) :
    (junk G (dropDup n C j s)).card ≤ (junk G C).card := by
  classical
  have hlen := dropDup_length n C j s hj
  have hm : (junk G (dropDup n C j s)).image (oldIndex j) ⊆ junk G C := by
    intro i hi
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    have hkd := (mem_junk G (dropDup n C j s) k).mp hk
    have hki := hkd.2.1
    have hi : oldIndex j k < C.gates.length := by unfold oldIndex; split_ifs <;> omega
    apply (mem_junk G C (oldIndex j k)).mpr
    refine ⟨?_, hi, ?_⟩
    · rw [← gate_eq C j s hj k hki]
      exact hkd.1
    · obtain ⟨x, hx, hg⟩ := hkd.2.2
      refine ⟨x, ?_, hg⟩
      have hw := wire_eq C j s hj hs heq x (n + oldIndex j k)
      rw [mapped_wire] at hw
      exact hw.trans hx
  have hc := Finset.card_le_card hm
  rw [Finset.card_image_of_injective _ (oldIndex_injective j)] at hc
  exact hc

lemma erase_family {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (J : Finset ℕ) (C : Circuit) (hC : IsAO2 n C)
    (hJ : J ⊆ Finset.range C.size) (s : ℕ)
    (hs : ∀ j ∈ J, s < n + j)
    (heq : ∀ j ∈ J, ∀ x : Fin n → Bool, value C x (n + j) = value C x s) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧
      D.size + J.card ≤ C.size ∧ (junk G D).card ≤ (junk G C).card := by
  classical
  induction J using Finset.strongInductionOn generalizing C
  rename_i J ih
  by_cases hne : J.Nonempty
  · let j := J.max' hne
    have hjJ : j ∈ J := Finset.max'_mem J hne
    have hj : j < C.gates.length := Finset.mem_range.mp (hJ hjJ)
    have hsj := hs j hjJ
    let E := dropDup n C j s
    have hE : IsAO2 n E := dropDup_ao n C j s hj hsj hC
    have hlen : E.size + 1 = C.size := dropDup_length n C j s hj
    have hklt : ∀ k ∈ J.erase j, k < j := by
      intro k hk
      have hm := Finset.le_max' J k (Finset.mem_of_mem_erase hk)
      have hn := (Finset.mem_erase.mp hk).1
      omega
    have hJE : J.erase j ⊆ Finset.range E.size := by
      intro k hk
      have hkj := hklt k hk
      apply Finset.mem_range.mpr
      change j < C.size at hj
      omega
    have heqE : ∀ k ∈ J.erase j, ∀ x : Fin n → Bool, value E x (n + k) = value E x s := by
      intro k hk x
      have hkj := hklt k hk
      have hwk := wire_eq C j s hj hsj (heq j hjJ) x (n + k)
      have hws := wire_eq C j s hj hsj (heq j hjJ) x s
      have hkmap : aliasWire (n + j) s (n + k) = n + k := by unfold aliasWire shiftDown; split_ifs <;> omega
      have hsmap : aliasWire (n + j) s s = s := by unfold aliasWire shiftDown; split_ifs <;> omega
      rw [hkmap] at hwk
      rw [hsmap] at hws
      exact hwk.symm.trans ((heq k (Finset.mem_of_mem_erase hk) x).trans hws)
    obtain ⟨D, hD, hf, hsz, hjunk⟩ := ih (J.erase j) (Finset.erase_ssubset hjJ) E hE hJE
      (fun k hk => hs k (Finset.mem_of_mem_erase hk)) heqE
    refine ⟨D, hD, hf.trans (function_eq C j s hj hsj (heq j hjJ)), ?_, ?_⟩
    · have hcard := Finset.card_erase_add_one hjJ
      omega
    · exact hjunk.trans (junk_le G C j s hj hsj (heq j hjJ))
  · have hz : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst J
    exact ⟨C, hC, rfl, by simp, le_rfl⟩

end PEqualNP.Outside.L_meta_3566.AliasErase

namespace PEqualNP.Outside.L_meta_3566.LeastGateLiveExtras

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

lemma last_gate_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hpos : 0 < C.size) :
    C.output = n + (C.gates.length - 1) := by
  have hp : 0 < C.gates.length := hpos
  rcases LeastGateLive.output_or_later_reader G C hLeast (C.gates.length - 1) (by omega) with
    h | ⟨k, hlt, hk, _⟩
  · exact h
  · omega

end PEqualNP.Outside.L_meta_3566.LeastGateLiveExtras

namespace PEqualNP.Outside.L_meta_3566.DeadSet

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

def neutralize (C : Circuit) (J : Finset ℕ) : Circuit :=
  rewrite C (fun j => if j.val ∈ J then ⟨.and, [0, 0]⟩ else gateAt C j.val)

lemma length (C : Circuit) (J : Finset ℕ) : (neutralize C J).gates.length = C.gates.length :=
  rewrite_length C _

lemma size (C : Circuit) (J : Finset ℕ) : (neutralize C J).size = C.size :=
  rewrite_size C _

lemma gate (C : Circuit) (J : Finset ℕ) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (neutralize C J) j = if j ∈ J then ⟨.and, [0, 0]⟩ else gateAt C j :=
  rewrite_gate C _ j hj

lemma ao {n : ℕ} (C : Circuit) (J : Finset ℕ) (hn : 0 < n) (hC : IsAO2 n C) :
    IsAO2 n (neutralize C J) := by
  apply rewrite_ao C _
  · intro j
    split_ifs
    · exact Or.inl rfl
    · exact hC.1 _ (MixedColor.gateAt_mem j.isLt)
  · intro j
    split_ifs
    · rfl
    · exact hC.2.2 _ (MixedColor.gateAt_mem j.isLt)
  · intro j w hw
    split_ifs at hw
    · have hw0 : w = 0 := by simpa using hw
      omega
    · exact hC.2.1 j j.isLt w hw

lemma retained {n : ℕ} (C : Circuit) (J : Finset ℕ) (hn : 0 < n) (hC : IsAO2 n C)
    (hclosed : ∀ j, j < C.gates.length → j ∉ J → ∀ k ∈ J,
      n + k ∉ (gateAt C j).inputs) :
    ∀ x : Fin n → Bool, ∀ w, (w < n ∨ w - n ∉ J) →
      value (neutralize C J) x w = value C x w := by
  apply preserve_closed_wires C (neutralize C J) (length C J) hC.2.1 (ao C J hn hC).2.1
    (fun w => w < n ∨ w - n ∉ J)
  · intro j hj hp
    have hjn : j ∉ J := by simpa using hp
    rw [gate C J j hj, ite_eq_right hjn]
  · intro j hj hp i hi
    have hjn : j ∉ J := by simpa using hp
    by_cases hin : i < n
    · exact Or.inl hin
    · right
      intro hiJ
      have he : n + (i - n) = i := by omega
      exact hclosed j hj hjn (i - n) hiJ (by simpa only [he] using hi)

lemma aliases {n : ℕ} (C : Circuit) (J : Finset ℕ) (hn : 0 < n) (hC : IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hjJ : j ∈ J) (x : Fin n → Bool) :
    value (neutralize C J) x (n + j) = value (neutralize C J) x 0 := by
  have hD := ao C J hn hC
  rw [value_gate _ hD.2.1 x j (by rw [length]; exact hj), gate C J j hj, ite_eq_left hjJ]
  simp [GateOp.eval]

end PEqualNP.Outside.L_meta_3566.DeadSet

namespace PEqualNP.Outside.L_meta_3566.AppendFactor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

def appendGate (n : ℕ) (C : Circuit) (g : Gate) : Circuit :=
  ⟨C.gates ++ [g], n + C.gates.length⟩

lemma appendGate_length (n : ℕ) (C : Circuit) (g : Gate) :
    (appendGate n C g).gates.length = C.gates.length + 1 := by simp [appendGate]

lemma appendGate_size (n : ℕ) (C : Circuit) (g : Gate) :
    (appendGate n C g).size = C.size + 1 := by simp [Circuit.size, appendGate]

lemma appendGate_old (n : ℕ) (C : Circuit) (g : Gate) (j : ℕ) (hj : j < C.gates.length) :
    gateAt (appendGate n C g) j = gateAt C j := by
  simp only [appendGate, gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma appendGate_last (n : ℕ) (C : Circuit) (g : Gate) :
    gateAt (appendGate n C g) C.gates.length = g := by
  simp [appendGate, gateAt, List.getD_eq_getElem?_getD]

lemma appendGate_ao {n : ℕ} (C : Circuit) (g : Gate) (hC : IsAO2 n C)
    (hop : g.op = .and ∨ g.op = .or) (h2 : g.inputs.length = 2)
    (hback : ∀ w ∈ g.inputs, w < n + C.gates.length) : IsAO2 n (appendGate n C g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact hC.1 f hf
    · have he : f = g := by simpa using hf
      subst f
      exact hop
  · intro j hj w hw
    rw [appendGate_length] at hj
    by_cases hjl : j < C.gates.length
    · rw [appendGate_old n C g j hjl] at hw
      exact hC.2.1 j hjl w hw
    · have he : j = C.gates.length := by omega
      subst j
      rw [appendGate_last] at hw
      exact hback w hw
  · intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact hC.2.2 f hf
    · have he : f = g := by simpa using hf
      subst f
      exact h2

lemma appendGate_preserves {n : ℕ} (C : Circuit) (g : Gate) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n + C.gates.length) :
    value (appendGate n C g) x w = value C x w := by
  unfold value
  rw [Splice.wires_eq_foldl, Splice.wires_eq_foldl]
  change ((C.gates ++ [g]).foldl Splice.stepWire (List.ofFn x)).getD w false = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  apply Splice.stepWire_getD_lt
  rw [Splice.foldl_stepWire_length, List.length_ofFn]
  exact hw

lemma appendGate_value {n : ℕ} (C : Circuit) (g : Gate) (x : Fin n → Bool) :
    circuitFun n (appendGate n C g) x = g.op.eval (g.inputs.map (value C x)) := by
  change ((appendGate n C g).wires (List.ofFn x)).getD (n + C.gates.length) false = _
  rw [Splice.wires_eq_foldl]
  change ((C.gates ++ [g]).foldl Splice.stepWire (List.ofFn x)).getD (n + C.gates.length) false = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hl : (C.gates.foldl Splice.stepWire (List.ofFn x)).length = n + C.gates.length := by
    rw [Splice.foldl_stepWire_length, List.length_ofFn]
  rw [← hl, Splice.stepWire_getD_len]
  rfl

lemma appendGate_output_valid (n : ℕ) (C : Circuit) (g : Gate) :
    (appendGate n C g).output < n + (appendGate n C g).gates.length := by
  simp [appendGate]

def orGate (a b : ℕ) : Gate := ⟨.or, [a, b]⟩

def andGate (a b : ℕ) : Gate := ⟨.and, [a, b]⟩

def appendOrs (n : ℕ) (C : Circuit) : List ℕ → Circuit
  | [] => C
  | w :: ws => appendOrs n (appendGate n C (orGate C.output w)) ws

lemma appendOrs_size (n : ℕ) (C : Circuit) (ws : List ℕ) :
    (appendOrs n C ws).size = C.size + ws.length := by
  induction ws generalizing C with
  | nil => simp [appendOrs]
  | cons w ws ih =>
    rw [appendOrs, ih, appendGate_size]
    simp only [List.length_cons]
    omega

lemma appendOrs_preserves {n : ℕ} (C : Circuit) (ws : List ℕ) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n + C.gates.length) :
    value (appendOrs n C ws) x w = value C x w := by
  induction ws generalizing C with
  | nil => rfl
  | cons a ws ih =>
    rw [appendOrs, ih _ (by rw [appendGate_length]; omega)]
    exact appendGate_preserves C _ x w hw

lemma appendOrs_ao {n : ℕ} (C : Circuit) (ws : List ℕ) (hC : IsAO2 n C)
    (hout : C.output < n + C.gates.length)
    (hws : ∀ w ∈ ws, w < n + C.gates.length) : IsAO2 n (appendOrs n C ws) := by
  induction ws generalizing C with
  | nil => exact hC
  | cons w ws ih =>
    apply ih
    · apply appendGate_ao C (orGate C.output w) hC (Or.inr rfl) rfl
      intro i hi
      simp only [orGate, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi
      · subst i
        exact hout
      · subst i
        exact hws w (by simp)
    · exact appendGate_output_valid _ _ _
    · intro i hi
      rw [appendGate_length]
      have := hws i (by simp [hi])
      omega

lemma any_congr_on {α : Type*} (l : List α) (f g : α → Bool) :
    (∀ a ∈ l, f a = g a) → l.any f = l.any g := by
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro heq
    simp only [List.any_cons]
    rw [heq a (by simp), ih (fun b hb => heq b (by simp [hb]))]

lemma appendOrs_value {n : ℕ} (C : Circuit) (ws : List ℕ)
    (hws : ∀ w ∈ ws, w < n + C.gates.length) (x : Fin n → Bool) :
    circuitFun n (appendOrs n C ws) x =
      (circuitFun n C x || ws.any (fun w => value C x w)) := by
  induction ws generalizing C with
  | nil => simp [appendOrs]
  | cons w ws ih =>
    rw [appendOrs, ih _ (by
      intro i hi
      rw [appendGate_length]
      have := hws i (by simp [hi])
      omega)]
    rw [appendGate_value]
    simp only [orGate, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
    have heq : ws.any (fun i => value (appendGate n C (orGate C.output w)) x i) =
        ws.any (fun i => value C x i) := by
      apply any_congr_on
      intro i hi
      rw [appendGate_preserves C _ x i (hws i (by simp [hi]))]
    simp only [orGate] at heq
    rw [heq]
    exact Bool.or_assoc _ _ _

def factor (n : ℕ) (C : Circuit) (h a b : ℕ) : Circuit :=
  let D := appendGate n C (orGate a b)
  appendGate n D (andGate h D.output)

def appendFactorOr (n : ℕ) (C : Circuit) (h a b : ℕ) (rest : List ℕ) : Circuit :=
  appendOrs n (factor n C h a b) rest

lemma factor_size (n : ℕ) (C : Circuit) (h a b : ℕ) :
    (factor n C h a b).size = C.size + 2 := by
  simp [factor, appendGate_size]

lemma factor_preserves {n : ℕ} (C : Circuit) (h a b : ℕ) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n + C.gates.length) :
    value (factor n C h a b) x w = value C x w := by
  unfold factor
  rw [appendGate_preserves _ _ x w (by rw [appendGate_length]; omega), appendGate_preserves C _ x w hw]

lemma factor_ao {n : ℕ} (C : Circuit) (h a b : ℕ) (hC : IsAO2 n C)
    (hh : h < n + C.gates.length) (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) :
    IsAO2 n (factor n C h a b) := by
  have hD : IsAO2 n (appendGate n C (orGate a b)) := by
    apply appendGate_ao C _ hC (Or.inr rfl) rfl
    intro w hw
    simp only [orGate, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> assumption
  apply appendGate_ao _ _ hD (Or.inl rfl) rfl
  intro w hw
  simp only [andGate, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · rw [appendGate_length]
    omega
  · exact appendGate_output_valid _ _ _

lemma factor_output_valid (n : ℕ) (C : Circuit) (h a b : ℕ) :
    (factor n C h a b).output < n + (factor n C h a b).gates.length :=
  appendGate_output_valid _ _ _

lemma factor_value {n : ℕ} (C : Circuit) (h a b : ℕ)
    (hh : h < n + C.gates.length) (x : Fin n → Bool) :
    circuitFun n (factor n C h a b) x =
      (value C x h && (value C x a || value C x b)) := by
  unfold factor
  rw [appendGate_value]
  simp only [andGate, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    id_eq, Bool.and_true]
  rw [appendGate_preserves C _ x h hh]
  change (value C x h && circuitFun n (appendGate n C (orGate a b)) x) = _
  rw [appendGate_value]
  simp [orGate, GateOp.eval]

lemma appendFactorOr_size (n : ℕ) (C : Circuit) (h a b : ℕ) (rest : List ℕ) :
    (appendFactorOr n C h a b rest).size = C.size + 2 + rest.length := by
  rw [appendFactorOr, appendOrs_size, factor_size]

lemma appendFactorOr_preserves {n : ℕ} (C : Circuit) (h a b : ℕ) (rest : List ℕ)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n + C.gates.length) :
    value (appendFactorOr n C h a b rest) x w = value C x w := by
  rw [appendFactorOr, appendOrs_preserves _ _ x w (by
    change w < n + (factor n C h a b).size
    rw [factor_size]
    change w < n + C.size at hw
    omega)]
  exact factor_preserves C h a b x w hw

lemma appendFactorOr_ao {n : ℕ} (C : Circuit) (h a b : ℕ) (rest : List ℕ) (hC : IsAO2 n C)
    (hh : h < n + C.gates.length) (ha : a < n + C.gates.length) (hb : b < n + C.gates.length)
    (hrest : ∀ w ∈ rest, w < n + C.gates.length) : IsAO2 n (appendFactorOr n C h a b rest) := by
  apply appendOrs_ao _ _ (factor_ao C h a b hC hh ha hb) (factor_output_valid _ _ _ _ _)
  intro w hw
  change w < n + (factor n C h a b).size
  rw [factor_size]
  have := hrest w hw
  change w < n + C.size at this
  omega

lemma appendFactorOr_value {n : ℕ} (C : Circuit) (h a b : ℕ) (rest : List ℕ)
    (hh : h < n + C.gates.length) (hrest : ∀ w ∈ rest, w < n + C.gates.length)
    (x : Fin n → Bool) :
    circuitFun n (appendFactorOr n C h a b rest) x =
      ((value C x h && (value C x a || value C x b)) || rest.any (fun w => value C x w)) := by
  rw [appendFactorOr, appendOrs_value _ _ (by
    intro w hw
    change w < n + (factor n C h a b).size
    rw [factor_size]
    have := hrest w hw
    change w < n + C.size at this
    omega), factor_value C h a b hh x]
  congr 1
  apply any_congr_on
  intro w hw
  exact factor_preserves C h a b x w (hrest w hw)

end PEqualNP.Outside.L_meta_3566.AppendFactor

namespace PEqualNP.Outside.L_meta_3566.AppendFactor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma and_partner {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = .and)
    (w : ℕ) (hw : w ∈ (gateAt C j).inputs) :
    ∃ v, v ∈ (gateAt C j).inputs ∧ w < n + j ∧ v < n + j ∧
      ∀ x : Fin n → Bool, value C x (n + j) = (value C x w && value C x v) := by
  have hwb := hC.2.1 j hj w hw
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hC.2.2 _ (MixedColor.gateAt_mem hj))
  have hw' : w = a ∨ w = b := by simpa [hab] using hw
  rcases hw' with rfl | rfl
  · have hbm : b ∈ (gateAt C j).inputs := by simp [hab]
    refine ⟨b, hbm, hwb, hC.2.1 j hj b hbm, ?_⟩
    intro x
    rw [value_gate C hC.2.1 x j hj, hop, hab]
    simp [GateOp.eval]
  · have ham : a ∈ (gateAt C j).inputs := by simp [hab]
    refine ⟨a, ham, hwb, hC.2.1 j hj a ham, ?_⟩
    intro x
    rw [value_gate C hC.2.1 x j hj, hop, hab]
    simp [GateOp.eval, Bool.and_comm]

end PEqualNP.Outside.L_meta_3566.AppendFactor

namespace PEqualNP.Outside.L_meta_3566.TopFrontierIdentity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership SemanticPurity

lemma wire_true_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (w : ℕ)
    (hbelow : ∀ y : Fin n → Bool, W n C w y = true → graphFun G ∅ y = true)
    (x : Fin n → Bool) :
    W n C w x = true ↔ ∃ j ∈ TopFrontier.leaves (n := n) C w, gateVal n C j x = true := by
  classical
  constructor
  · intro hx
    obtain ⟨j,hj,hop,hpath,htrue⟩ := TopFrontierCoverage.true_below_reaches_and G C hAO x w hbelow hx
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hop,hpath⟩,htrue⟩
  · rintro ⟨j,hj,htrue⟩
    obtain ⟨_,_,hpath⟩ := Finset.mem_filter.mp hj
    exact MixedColor.orStep_up (by simp) hpath htrue

lemma output_true_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (x : Fin n → Bool) : circuitFun n C x = true ↔
      ∃ j ∈ TopFrontier.leaves (n := n) C C.output, gateVal n C j x = true := by
  apply wire_true_iff G C hAO C.output
  intro y hy
  change circuitFun n C y = true at hy
  simpa only [hfun] using hy

lemma output_eq_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (x : Fin n → Bool) : circuitFun n C x =
      (TopFrontier.leaves (n := n) C C.output).toList.any (fun j => gateVal n C j x) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [List.any_eq_true,Finset.mem_toList] using output_true_iff G C hAO hfun x

lemma clean_wire_has_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (w : ℕ) (hw : w < n+C.gates.length)
    (hbelow : ∀ y : Fin n → Bool, W n C w y = true → graphFun G ∅ y = true) :
    ∃ j ∈ tops G C, Relation.ReflTransGen (MixedColor.OrStep n C) w (n+j) := by
  classical
  obtain ⟨j,hj,hop,hpath,_⟩ := TopFrontierCoverage.true_below_reaches_and G C hAO
    (fun _ => true) w hbelow (wire_one C hAO w hw)
  refine ⟨j,?_,hpath⟩
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range]
  exact ⟨hj,hop,TopFrontierCoverage.reached_below G C w j hbelow hpath⟩

end PEqualNP.Outside.L_meta_3566.TopFrontierIdentity

namespace PEqualNP.Outside.L_meta_3566.CommonTopClosure

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership SemanticPurity

lemma or_path_cone {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) {w i : ℕ}
    (hp : Relation.ReflTransGen (MixedColor.OrStep n C) w (n+i)) :
    ∃ j, w = n+j ∧ (i = j ∨ InCone n C i j) := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨i,rfl,Or.inl rfl⟩
  | head hs _ ih =>
    obtain ⟨k,hk,rfl,_,hw,_⟩ := hs
    obtain ⟨j,rfl,hi⟩ := ih
    exact ⟨k,rfl,Or.inr (JunkPurity.cone_step C hAO hk hw hi)⟩

lemma top_path_not_and_input {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C)
    {i k w : ℕ} (hi : i < C.gates.length) (hia : (gateAt C i).op = .and)
    (hic : BelowF G C i) (hk : k < C.gates.length) (hka : (gateAt C k).op = .and)
    (hw : w ∈ (gateAt C k).inputs)
    (hp : Relation.ReflTransGen (MixedColor.OrStep n C) w (n+i)) : False := by
  obtain ⟨j,rfl,hcone⟩ := or_path_cone C hAO hp
  exact hTF i hi k hk hia hic hka (JunkPurity.cone_step C hAO hk hw hcone)

lemma above_top_reaches_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C)
    {i j : ℕ} (hi : i < C.gates.length) (hia : (gateAt C i).op = .and)
    (hic : BelowF G C i) (hj : j < C.gates.length)
    (hp : Relation.ReflTransGen (MixedColor.OrStep n C) (n+j) (n+i)) :
    Relation.ReflTransGen (MixedColor.OrStep n C) C.output (n+j) := by
  rcases JunkPurity.reaches_and_or_output C hLeast.1
      (LeastGateLive.output_or_later_reader G C hLeast) j hj with ho | ⟨k,w,hk,hka,hw,hpath⟩
  · exact ho
  · exact (top_path_not_and_input G C hLeast.1 hTF hi hia hic hk hka hw
      (hpath.trans hp)).elim

lemma top_reaches_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C)
    {i : ℕ} (hi : i ∈ tops G C) :
    Relation.ReflTransGen (MixedColor.OrStep n C) C.output (n+i) := by
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at hi
  exact above_top_reaches_output G C hLeast hTF hi.1 hi.2.1 hi.2.2 hi.1 .refl

lemma tops_eq_output_frontier {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C) :
    tops G C = TopFrontier.leaves (n := n) C C.output := by
  classical
  ext i
  constructor
  · intro hi
    have hp := top_reaches_output G C hLeast hTF hi
    simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi.1,hi.2.1,hp⟩
  · intro hi
    have hic := TopFrontier.leaf_below G C C.output i (by
      intro x hx
      change circuitFun n C x = true at hx
      simpa only [hLeast.2.1] using hx) hi
    obtain ⟨hib,hia,_⟩ := Finset.mem_filter.mp hi
    simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range]
    exact ⟨Finset.mem_range.mp hib,hia,hic⟩

lemma clean_reader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C)
    {i j : ℕ} (hi : i < C.gates.length) (hic : BelowF G C i)
    (hj : j < C.gates.length) (hread : n+i ∈ (gateAt C j).inputs) :
    (gateAt C j).op = .or ∧ BelowF G C j := by
  have hjo : (gateAt C j).op = .or := by
    rcases hLeast.1.1 _ (MixedColor.gateAt_mem hj) with ha | ho
    · exact (AndChild.not_below G C hLeast j (n+i) hj ha hread hic).elim
    · exact ho
  obtain ⟨k,hk,hp⟩ := TopFrontierIdentity.clean_wire_has_top G C hLeast.1 (n+i) (by omega) hic
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at hk
  have hstep : MixedColor.OrStep n C (n+j) (n+i) :=
    ⟨j,hj,rfl,hjo,hread,hLeast.1.2.1 j hj _ hread⟩
  have hout := above_top_reaches_output G C hLeast hTF hk.1 hk.2.1 hk.2.2 hj
    (Relation.ReflTransGen.head hstep hp)
  refine ⟨hjo,?_⟩
  intro x hx
  have ho : circuitFun n C x = true := MixedColor.orStep_up (by simp) hout hx
  simpa only [hLeast.2.1] using ho

lemma clean_reader_mem_orT {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C)
    {i j : ℕ} (hi : i < C.gates.length) (hic : BelowF G C i)
    (hj : j < C.gates.length) (hread : n+i ∈ (gateAt C j).inputs) : j ∈ orT G C := by
  classical
  simp only [orT,gatesWhere,Finset.mem_filter,Finset.mem_range]
  exact ⟨hj,clean_reader G C hLeast hTF hi hic hj hread⟩

lemma clean_set_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C) (J : Finset ℕ)
    (hOR : orT G C ⊆ J) (hclean : ∀ i ∈ J, i < C.gates.length ∧ BelowF G C i)
    {j : ℕ} (hj : j < C.gates.length) (hjJ : j ∉ J) :
    ∀ i ∈ J, n+i ∉ (gateAt C j).inputs := by
  intro i hi hread
  obtain ⟨hib,hic⟩ := hclean i hi
  exact hjJ (hOR (clean_reader_mem_orT G C hLeast hTF hib hic hj hread))

lemma common_top_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C)
    {a b : ℕ} (ha : a ∈ tops G C) (hb : b ∈ tops G C)
    {j : ℕ} (hj : j < C.gates.length) (hjJ : j ∉ orT G C ∪ {a,b}) :
    ∀ i ∈ orT G C ∪ {a,b}, n+i ∉ (gateAt C j).inputs := by
  classical
  apply clean_set_closed G C hLeast hTF (orT G C ∪ {a,b}) Finset.subset_union_left _ hj hjJ
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · simp only [orT,gatesWhere,Finset.mem_filter,Finset.mem_range] at hi
    exact ⟨hi.1,hi.2.2⟩
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at ha
      exact ⟨ha.1,ha.2.2⟩
    · simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at hb
      exact ⟨hb.1,hb.2.2⟩

end PEqualNP.Outside.L_meta_3566.CommonTopClosure

namespace PEqualNP.Outside.L_meta_3566.CommonTopSets

lemma mem_remaining (T : Finset ℕ) (a b x : ℕ) :
    x ∈ (T.erase a).erase b ↔ x ∈ T ∧ x ≠ a ∧ x ≠ b := by
  simp only [Finset.mem_erase]
  constructor
  · rintro ⟨hxb, hxa, hxT⟩
    exact ⟨hxT, hxa, hxb⟩
  · rintro ⟨hxT, hxa, hxb⟩
    exact ⟨hxb, hxa, hxT⟩

lemma remaining_card (T : Finset ℕ) (a b : ℕ)
    (hab : a ≠ b) (ha : a ∈ T) (hb : b ∈ T) :
    ((T.erase a).erase b).card + 2 = T.card := by
  have hba : b ∈ T.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have h1 := Finset.card_erase_add_one ha
  have h2 := Finset.card_erase_add_one hba
  omega

lemma selected_card (T O : Finset ℕ) (a b : ℕ)
    (hab : a ≠ b) (ha : a ∈ T) (hb : b ∈ T) (hdis : Disjoint T O) :
    (O ∪ {a, b}).card = O.card + 2 := by
  have hpair : Disjoint O ({a, b} : Finset ℕ) := by
    apply Finset.disjoint_left.mpr
    intro x hxO hxab
    have hxT : x ∈ T := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxab
      rcases hxab with rfl | rfl <;> assumption
    exact Finset.disjoint_left.mp hdis hxT hxO
  rw [Finset.card_union_of_disjoint hpair]
  simp [hab]

lemma remaining_disjoint_selected (T O : Finset ℕ) (a b : ℕ) (hdis : Disjoint T O) :
    Disjoint ((T.erase a).erase b) (O ∪ {a, b}) := by
  apply Finset.disjoint_left.mpr
  intro x hxR hxJ
  obtain ⟨hxT, hxa, hxb⟩ := (mem_remaining T a b x).mp hxR
  rcases Finset.mem_union.mp hxJ with hxO | hxab
  · exact Finset.disjoint_left.mp hdis hxT hxO
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxab
    exact hxab.elim hxa hxb

lemma cardinal_budget (T O : Finset ℕ) (a b : ℕ)
    (hab : a ≠ b) (ha : a ∈ T) (hb : b ∈ T) (hdis : Disjoint T O)
    (hbound : T.card ≤ O.card + 1) :
    2 + ((T.erase a).erase b).card + 1 ≤ (O ∪ {a, b}).card := by
  have hT := remaining_card T a b hab ha hb
  have hJ := selected_card T O a b hab ha hb hdis
  omega

lemma mem_decomposition (T : Finset ℕ) (a b x : ℕ) (ha : a ∈ T) (hb : b ∈ T) :
    x ∈ T ↔ x = a ∨ x = b ∨ x ∈ (T.erase a).erase b := by
  constructor
  · intro hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    by_cases hxb : x = b
    · exact Or.inr (Or.inl hxb)
    exact Or.inr (Or.inr ((mem_remaining T a b x).mpr ⟨hx, hxa, hxb⟩))
  · rintro (rfl | rfl | hx)
    · exact ha
    · exact hb
    · exact ((mem_remaining T a b x).mp hx).1

lemma exists_decomposition (T : Finset ℕ) (a b : ℕ) (ha : a ∈ T) (hb : b ∈ T)
    (P : ℕ → Prop) :
    (∃ x ∈ T, P x) ↔ P a ∨ P b ∨ ∃ x ∈ (T.erase a).erase b, P x := by
  constructor
  · rintro ⟨x, hx, hp⟩
    rcases (mem_decomposition T a b x ha hb).mp hx with rfl | rfl | hxR
    · exact Or.inl hp
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr ⟨x, hxR, hp⟩)
  · rintro (hp | hp | ⟨x, hxR, hp⟩)
    · exact ⟨a, ha, hp⟩
    · exact ⟨b, hb, hp⟩
    · exact ⟨x, ((mem_remaining T a b x).mp hxR).1, hp⟩

end PEqualNP.Outside.L_meta_3566.CommonTopSets

namespace PEqualNP.Outside.L_meta_3566.CommonTopFactorIdentity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma any_decomposition (T : Finset ℕ) (i j : ℕ) (hi : i ∈ T) (hj : j ∈ T) (f : ℕ → Bool) :
    T.toList.any f = ((f i || f j) || ((T.erase i).erase j).toList.any f) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [List.any_eq_true,Finset.mem_toList,Bool.or_eq_true,or_assoc] using
    CommonTopSets.exists_decomposition T i j hi hj (fun k => f k = true)

lemma factor_output_profiles {n : ℕ} (C : Circuit) (T : Finset ℕ) (i j H A B : ℕ)
    (hi : i ∈ T) (hj : j ∈ T)
    (houtput : ∀ x : Fin n → Bool, circuitFun n C x = T.toList.any (fun k => gateVal n C k x))
    (hival : ∀ x : Fin n → Bool, gateVal n C i x = (value C x H && value C x A))
    (hjval : ∀ x : Fin n → Bool, gateVal n C j x = (value C x H && value C x B)) :
    ∀ x : Fin n → Bool, circuitFun n C x =
      ((value C x H && (value C x A || value C x B)) ||
        (((T.erase i).erase j).toList.map (fun k => n+k)).any (value C x)) := by
  intro x
  rw [houtput,any_decomposition T i j hi hj,hival,hjval]
  simp only [List.any_map]
  change (((value C x H && value C x A) || (value C x H && value C x B)) ||
      ((T.erase i).erase j).toList.any (fun k => value C x (n+k))) =
    ((value C x H && (value C x A || value C x B)) ||
      ((T.erase i).erase j).toList.any (fun k => value C x (n+k)))
  cases value C x H <;> simp

end PEqualNP.Outside.L_meta_3566.CommonTopFactorIdentity

namespace PEqualNP.Outside.L_meta_3566.TopFactorCompiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma factor_closed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (J : Finset ℕ) (hn : 0 < n) (hC : IsAO2 n C)
    (hJ : J ⊆ Finset.range C.size)
    (hclosed : ∀ j, j < C.gates.length → j ∉ J → ∀ k ∈ J,
      n + k ∉ (gateAt C j).inputs)
    (h a b : ℕ) (rest : List ℕ)
    (hh : h < n + C.gates.length) (ha : a < n + C.gates.length) (hb : b < n + C.gates.length)
    (hrest : ∀ w ∈ rest, w < n + C.gates.length)
    (hkeep : h < n ∨ h - n ∉ J) (hkeepa : a < n ∨ a - n ∉ J)
    (hkeepb : b < n ∨ b - n ∉ J)
    (hkeepr : ∀ w ∈ rest, w < n ∨ w - n ∉ J)
    (houtput : ∀ x : Fin n → Bool, circuitFun n C x =
      ((value C x h && (value C x a || value C x b)) || rest.any (fun w => value C x w)))
    (hbudget : 2 + rest.length + 1 ≤ J.card) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧ D.size + 1 ≤ C.size := by
  classical
  let B := DeadSet.neutralize C J
  let E := AppendFactor.appendFactorOr n B h a b rest
  have hB : IsAO2 n B := DeadSet.ao C J hn hC
  have hlen : B.gates.length = C.gates.length := DeadSet.length C J
  have hE : IsAO2 n E := AppendFactor.appendFactorOr_ao B h a b rest hB
    (by simpa only [hlen] using hh) (by simpa only [hlen] using ha)
    (by simpa only [hlen] using hb) (fun w hw => by simpa only [hlen] using hrest w hw)
  have hsize : E.size = C.size + 2 + rest.length := by
    rw [AppendFactor.appendFactorOr_size, DeadSet.size]
  have hpres : ∀ x : Fin n → Bool, ∀ w, (w < n ∨ w - n ∉ J) →
      value B x w = value C x w := DeadSet.retained C J hn hC hclosed
  have hfun : circuitFun n E = circuitFun n C := by
    funext x
    rw [AppendFactor.appendFactorOr_value B h a b rest (by simpa only [hlen] using hh)
      (fun w hw => by simpa only [hlen] using hrest w hw) x]
    have hr : rest.any (fun w => value B x w) = rest.any (fun w => value C x w) := by
      have hm : rest.map (fun w => value B x w) = rest.map (fun w => value C x w) :=
        List.map_congr_left (fun w hw => hpres x w (hkeepr w hw))
      simpa only [List.any_map, Function.comp_def, id_eq] using congrArg (fun xs : List Bool => xs.any id) hm
    rw [hpres x h hkeep, hpres x a hkeepa, hpres x b hkeepb, hr]
    exact (houtput x).symm
  have hJE : J ⊆ Finset.range E.size := by
    intro j hj
    have hjC := Finset.mem_range.mp (hJ hj)
    apply Finset.mem_range.mpr
    omega
  have halias : ∀ j ∈ J, ∀ x : Fin n → Bool, value E x (n + j) = value E x 0 := by
    intro j hj x
    have hjC : j < C.gates.length := Finset.mem_range.mp (hJ hj)
    have hval := DeadSet.aliases C J hn hC j hjC hj x
    have hw : n + j < n + B.gates.length := by rw [hlen]; omega
    have hz : 0 < n + B.gates.length := by omega
    rw [AppendFactor.appendFactorOr_preserves B h a b rest x (n + j) hw,
      AppendFactor.appendFactorOr_preserves B h a b rest x 0 hz]
    exact hval
  obtain ⟨D, hD, hf, hs, _⟩ := AliasErase.erase_family G J E hE hJE 0
    (fun j _ => by omega) halias
  refine ⟨D, hD, hf.trans hfun, ?_⟩
  omega

end PEqualNP.Outside.L_meta_3566.TopFactorCompiler

namespace PEqualNP.Outside.L_meta_3566.CommonTopFactor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma no_shared_operand {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C)
    {i j : ℕ} (hi : i ∈ tops G C) (hj : j ∈ tops G C) (hij : i ≠ j)
    (w : ℕ) (hwi : w ∈ (gateAt C i).inputs) : w ∉ (gateAt C j).inputs := by
  classical
  intro hwj
  have hi' := hi
  have hj' := hj
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at hi' hj'
  obtain ⟨a,hai,hwiB,haB,hival⟩ := AppendFactor.and_partner C hLeast.1 i hi'.1 hi'.2.1 w hwi
  obtain ⟨b,hbj,_,hbB,hjval⟩ := AppendFactor.and_partner C hLeast.1 j hj'.1 hj'.2.1 w hwj
  have hpos : 0 < C.gates.length := by omega
  have hn : 0 < n := by
    obtain ⟨u,v,huv⟩ := MixedColor.binaryInputs hLeast.1 hpos
    have hu := hLeast.1.2.1 0 hpos u (by simp [huv])
    omega
  have hout : C.output < n + C.gates.length := by
    rw [LeastGateLiveExtras.last_gate_output G C hLeast hpos]
    omega
  let J := orT G C ∪ {i,j}
  let R := ((tops G C).erase i).erase j
  let rest := R.toList.map (fun k => n+k)
  have hclean : ∀ k ∈ J, k < C.gates.length ∧ BelowF G C k := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · simp only [orT,gatesWhere,Finset.mem_filter,Finset.mem_range] at hk
      exact ⟨hk.1,hk.2.2⟩
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact ⟨hi'.1,hi'.2.2⟩
      · exact ⟨hj'.1,hj'.2.2⟩
  have hJ : J ⊆ Finset.range C.size := by
    intro k hk
    exact Finset.mem_range.mpr (hclean k hk).1
  have hclosed : ∀ k, k < C.gates.length → k ∉ J →
      ∀ l ∈ J, n+l ∉ (gateAt C k).inputs := by
    intro k hk hkJ
    exact CommonTopClosure.common_top_closed G C hLeast hTF hi hj hk hkJ
  have hkeep : ∀ k, k < C.gates.length → (gateAt C k).op = .and →
      ∀ u ∈ (gateAt C k).inputs, u < n ∨ u-n ∉ J := by
    intro k hk hka u hu
    by_cases hun : u < n
    · exact Or.inl hun
    · right
      intro huJ
      have huc := (hclean (u-n) huJ).2
      apply AndChild.not_below G C hLeast k u hk hka hu
      intro x hx
      apply huc x
      change value C x (n+(u-n)) = true
      change value C x u = true at hx
      have heq : n+(u-n) = u := by omega
      simpa only [heq] using hx
  have hdis : Disjoint (tops G C) (orT G C) := by
    apply Finset.disjoint_left.mpr
    intro k hkT hkO
    simp only [tops,orT,gatesWhere,Finset.mem_filter,Finset.mem_range] at hkT hkO
    have hf := hkT.2.1.symm.trans hkO.2.1
    cases hf
  have hRdis : Disjoint R J := CommonTopSets.remaining_disjoint_selected _ _ i j hdis
  have hrest : ∀ u ∈ rest, u < n + C.gates.length := by
    intro u hu
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hu
    have hkT := ((CommonTopSets.mem_remaining (tops G C) i j k).mp (Finset.mem_toList.mp hk)).1
    simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at hkT
    omega
  have hkeepr : ∀ u ∈ rest, u < n ∨ u-n ∉ J := by
    intro u hu
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hu
    right
    simpa only [Nat.add_sub_cancel_left] using
      (Finset.disjoint_left.mp hRdis (Finset.mem_toList.mp hk))
  have houtput : ∀ x : Fin n → Bool, circuitFun n C x =
      ((value C x w && (value C x a || value C x b)) || rest.any (value C x)) := by
    apply CommonTopFactorIdentity.factor_output_profiles C (tops G C) i j w a b hi hj
    · intro x
      rw [CommonTopClosure.tops_eq_output_frontier G C hLeast hTF]
      exact TopFrontierIdentity.output_eq_or G C hLeast.1 hLeast.2.1 x
    · exact hival
    · exact hjval
  have hbound : (tops G C).card ≤ (orT G C).card + 1 := by
    rw [CommonTopClosure.tops_eq_output_frontier G C hLeast hTF]
    apply TopFrontier.leaves_card_le_orT G C hLeast.1 C.output hout
    intro x hx
    change circuitFun n C x = true at hx
    simpa only [hLeast.2.1] using hx
  have hbudget : 2 + rest.length + 1 ≤ J.card := by
    simpa only [rest,List.length_map,Finset.length_toList] using
      CommonTopSets.cardinal_budget (tops G C) (orT G C) i j hij hi hj hdis hbound
  obtain ⟨D,hD,hfun,hsize⟩ := TopFactorCompiler.factor_closed G C J hn hLeast.1 hJ hclosed
    w a b rest (by omega) (by omega) (by omega) hrest
    (hkeep i hi'.1 hi'.2.1 w hwi) (hkeep i hi'.1 hi'.2.1 a hai)
    (hkeep j hj'.1 hj'.2.1 b hbj) hkeepr houtput hbudget
  have hmin := hLeast.2.2 D hD (hfun.trans hLeast.2.1)
  omega

end PEqualNP.Outside.L_meta_3566.CommonTopFactor

namespace PEqualNP.Outside.L_meta_3566.MaxDirtyConsumer

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma reader_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) {q : ℕ} (hdirty : ¬ BelowF G C q)
    (hmax : ∀ k, q < k → k < C.gates.length → BelowF G C k)
    {j : ℕ} (hj : j < C.gates.length) (hread : n+q ∈ (gateAt C j).inputs) :
    q < j ∧ j ∈ tops G C := by
  classical
  have hqj : q < j := by have := hAO.2.1 j hj _ hread; omega
  have hjc := hmax j hqj hj
  have hja : (gateAt C j).op = .and := by
    rcases hAO.1 _ (MixedColor.gateAt_mem hj) with ha | ho
    · exact ha
    · exfalso
      apply hdirty
      intro x hx
      apply hjc x
      exact (MixedColor.val_or (n := n) (C := C) (x := List.ofFn x) (by simp) hj ho).mpr
        ⟨n+q,hread,hAO.2.1 j hj _ hread,hx⟩
  refine ⟨hqj,?_⟩
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range]
  exact ⟨hj,hja,hjc⟩

lemma clean_reader_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) {q j : ℕ} (hdirty : ¬ BelowF G C q)
    (hj : j < C.gates.length) (hjc : BelowF G C j) (hja : (gateAt C j).op = .and)
    (hread : n+q ∈ (gateAt C j).inputs) : (gateAt C j).inputs.count (n+q) = 1 := by
  obtain ⟨a,b,hab⟩ := MixedColor.binaryInputs hAO hj
  have hmem : n+q = a ∨ n+q = b := by simpa [hab] using hread
  have hne : a ≠ b := by
    intro heq
    subst b
    have hqa : n+q = a := hmem.elim id id
    apply hdirty
    intro x hx
    apply hjc x
    change value C x (n+j) = true
    rw [value_gate C hAO.2.1 x j hj,hja,hab,← hqa]
    change value C x (n+q) = true at hx
    simp [GateOp.eval,hx]
  rw [hab]
  rcases hmem with hqa | hqb
  · rw [← hqa] at hne ⊢
    simp [hne]
  · rw [← hqb] at hne ⊢
    simp [hne,hne.symm]

lemma dirty_not_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hfun : circuitFun n C = graphFun G ∅)
    {q : ℕ} (hdirty : ¬ BelowF G C q) : C.output ≠ n+q := by
  intro hout
  apply hdirty
  intro x hx
  have hc : circuitFun n C x = true := by
    change value C x C.output = true
    rw [hout]
    exact hx
  simpa only [hfun] using hc

lemma unique_consumer {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C)
    {q : ℕ} (hq : q < C.gates.length) (hdirty : ¬ BelowF G C q)
    (hmax : ∀ k, q < k → k < C.gates.length → BelowF G C k) :
    ∃ j, q < j ∧ j < C.gates.length ∧ j ∈ tops G C ∧
      (gateAt C j).inputs.count (n+q) = 1 ∧
      ∀ k, k < C.gates.length → n+q ∈ (gateAt C k).inputs → k = j := by
  classical
  have hnotout := dirty_not_output G C hLeast.2.1 hdirty
  obtain ⟨j,hqj,hj,hread⟩ := (LeastGateLive.output_or_later_reader G C hLeast q hq).resolve_left hnotout
  have hjtop := (reader_top G C hLeast.1 hdirty hmax hj hread).2
  have hj' := hjtop
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at hj'
  refine ⟨j,hqj,hj,hjtop,clean_reader_count G C hLeast.1 hdirty hj hj'.2.2 hj'.2.1 hread,?_⟩
  intro k hk hkr
  by_contra hkj
  have hktop := (reader_top G C hLeast.1 hdirty hmax hk hkr).2
  exact CommonTopFactor.no_shared_operand G C hLeast hTF hktop hjtop hkj (n+q) hkr hread

end PEqualNP.Outside.L_meta_3566.MaxDirtyConsumer

namespace PEqualNP.Outside.L_meta_3566.MaxDirtyConsumerExtras

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma earlier_partner {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) {q : ℕ} (hdirty : ¬ BelowF G C q)
    (hmax : ∀ k, q < k → k < C.gates.length → BelowF G C k)
    {j : ℕ} (hj : j < C.gates.length) (hread : n+q ∈ (gateAt C j).inputs) :
    ∃ r, r < n+q ∧ r ≠ n+q ∧ r ∈ (gateAt C j).inputs ∧
      ((gateAt C j).inputs = [n+q,r] ∨ (gateAt C j).inputs = [r,n+q]) ∧
      ∀ x : Fin n → Bool, value C x (n+j) = (value C x (n+q) && value C x r) := by
  classical
  have hjtop := (MaxDirtyConsumer.reader_top G C hLeast.1 hdirty hmax hj hread).2
  simp only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] at hjtop
  have hcount := MaxDirtyConsumer.clean_reader_count G C hLeast.1 hdirty hj hjtop.2.2 hjtop.2.1 hread
  obtain ⟨a,b,hab⟩ := MixedColor.binaryInputs hLeast.1 hj
  have hmem : n+q = a ∨ n+q = b := by simpa [hab] using hread
  obtain ⟨r,hshape⟩ : ∃ r, (gateAt C j).inputs = [n+q,r] ∨
      (gateAt C j).inputs = [r,n+q] := by
    rcases hmem with hqa | hqb
    · exact ⟨b,Or.inl (hqa ▸ hab)⟩
    · exact ⟨a,Or.inr (hqb ▸ hab)⟩
  have hrmem : r ∈ (gateAt C j).inputs := by
    rcases hshape with hs | hs <;> simp [hs]
  have hrne : r ≠ n+q := by
    intro heq
    subst r
    have hs : (gateAt C j).inputs = [n+q,n+q] := hshape.elim id id
    simp [hs] at hcount
  have hrl : r < n+q := by
    by_contra hrl
    have hnr : n ≤ r := by omega
    have hqr : q < r-n := by omega
    have hrback := hLeast.1.2.1 j hj r hrmem
    have hrc := hmax (r-n) hqr (by omega)
    apply AndChild.not_below G C hLeast j r hj hjtop.2.1 hrmem
    intro x hx
    apply hrc x
    change value C x (n+(r-n)) = true
    change value C x r = true at hx
    have heq : n+(r-n) = r := by omega
    simpa only [heq] using hx
  refine ⟨r,hrl,hrne,hrmem,hshape,?_⟩
  intro x
  rw [value_gate C hLeast.1.2.1 x j hj,hjtop.2.1]
  rcases hshape with hs | hs <;> simp [hs,GateOp.eval,Bool.and_comm]

lemma private_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hLeast : IsLeastAO G C) (hTF : TopForm G C)
    {q : ℕ} (hq : q < C.gates.length) (hdirty : ¬ BelowF G C q)
    (hmax : ∀ k, q < k → k < C.gates.length → BelowF G C k) :
    ∃ j r, q < j ∧ j < C.gates.length ∧ j ∈ tops G C ∧ r < n+q ∧ r ≠ n+q ∧
      ((gateAt C j).inputs = [n+q,r] ∨ (gateAt C j).inputs = [r,n+q]) ∧
      (∀ x : Fin n → Bool, value C x (n+j) = (value C x (n+q) && value C x r)) ∧
      C.output ≠ n+q ∧
      (∀ k, k < C.gates.length → k ≠ j → n+q ∉ (gateAt C k).inputs) ∧
      (gateAt C j).inputs.count (n+q) = 1 := by
  obtain ⟨j,hqj,hj,hjt,hcount,hu⟩ := MaxDirtyConsumer.unique_consumer G C hLeast hTF hq hdirty hmax
  have hread : n+q ∈ (gateAt C j).inputs := by
    by_contra hnot
    have hz := List.count_eq_zero.mpr hnot
    omega
  obtain ⟨r,hr,hrne,_,hshape,hvalue⟩ := earlier_partner G C hLeast hdirty hmax hj hread
  refine ⟨j,r,hqj,hj,hjt,hr,hrne,hshape,hvalue,
    MaxDirtyConsumer.dirty_not_output G C hLeast.2.1 hdirty,?_,hcount⟩
  intro k hk hkj hkr
  exact hkj (hu k hk hkr)

end PEqualNP.Outside.L_meta_3566.MaxDirtyConsumerExtras

namespace PEqualNP.Outside.L_meta_3566.LastDirtyAndFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma path_true {n : ℕ} {C : Circuit} {q w : ℕ}
    (hp : Relation.ReflTransGen (MixedColor.OrStep n C) w (n+q))
    (x : Fin n → Bool) (hx : gateVal n C q x = true) : value C x w = true :=
  MixedColor.orStep_up (by simp) hp hx

lemma partner_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) {q j w r : ℕ}
    (hj : j < C.gates.length) (hja : (gateAt C j).op = .and) (hjc : BelowF G C j)
    (hinputs : (gateAt C j).inputs = [w,r] ∨ (gateAt C j).inputs = [r,w])
    (hp : Relation.ReflTransGen (MixedColor.OrStep n C) w (n+q))
    (x : Fin n → Bool) (hqx : gateVal n C q x = true) (hneg : graphFun G ∅ x = false) :
    value C x r = false := by
  by_contra hr
  have hrx : value C x r = true := by cases he : value C x r <;> simp_all
  have hwx := path_true hp x hqx
  have hjx : gateVal n C j x = true := by
    change value C x (n+j) = true
    rw [value_gate C hAO.2.1 x j hj,hja]
    rcases hinputs with hs | hs <;> simp [hs,GateOp.eval,hwx,hrx]
  have hf := hjc x hjx
  rw [hneg] at hf
  cases hf

lemma partner_not_reaches {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) {q j w r : ℕ} (hdirty : ¬ BelowF G C q)
    (hj : j < C.gates.length) (hja : (gateAt C j).op = .and) (hjc : BelowF G C j)
    (hinputs : (gateAt C j).inputs = [w,r] ∨ (gateAt C j).inputs = [r,w])
    (hp : Relation.ReflTransGen (MixedColor.OrStep n C) w (n+q)) :
    ¬ Relation.ReflTransGen (MixedColor.OrStep n C) r (n+q) := by
  intro hrp
  apply hdirty
  intro x hqx
  by_contra hneg
  have hrf := partner_false G C hAO hj hja hjc hinputs hp x hqx (Bool.eq_false_iff.mpr hneg)
  have hrt := path_true hrp x hqx
  rw [hrf] at hrt
  cases hrt

end PEqualNP.Outside.L_meta_3566.LastDirtyAndFrontier

namespace PEqualNP.Outside.L_meta_3566.LastDirtyAndDependency

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma cone_lt {n : ℕ} (C : Circuit) {q k : ℕ} (hk : k < C.gates.length)
    (hc : InCone n C q k) : q < k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    obtain ⟨w,_,hn,hw,hq | hq⟩ := (JunkPurity.inCone_iff n C q k hk).mp hc
    · omega
    · have := ih (w-n) (by omega) (by omega) hq
      omega

lemma cone_to_or_path {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C) {q j : ℕ}
    (hlast : ∀ k, q < k → k < C.gates.length → (gateAt C k).op = .and → BelowF G C k)
    (hj : j < C.gates.length) (hja : (gateAt C j).op = .and)
    {k : ℕ} (hk : k < C.gates.length) (hkj : InCone n C k j)
    (hqk : q = k ∨ InCone n C q k) :
    Relation.ReflTransGen (MixedColor.OrStep n C) (n+k) (n+q) := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rcases hqk with rfl | hqk
    · rfl
    have hqkl := cone_lt C hk hqk
    rcases hAO.1 _ (MixedColor.gateAt_mem hk) with ha | ho
    · exact (hTF k hk j hj ha (hlast k hqkl hk ha) hja hkj).elim
    · obtain ⟨w,hw,hn,hwk,hqw⟩ := (JunkPurity.inCone_iff n C q k hk).mp hqk
      have hwc : InCone n C (w-n) k :=
        (JunkPurity.inCone_iff n C (w-n) k hk).mpr ⟨w,hw,hn,hwk,Or.inl rfl⟩
      have hwj := JunkPurity.cone_trans C hj hwc hkj
      have hp := ih (w-n) (by omega) (by omega) hwj hqw
      apply Relation.ReflTransGen.head ⟨k,hk,rfl,ho,hw,hwk⟩
      have heq : n+(w-n) = w := by omega
      simpa only [heq] using hp

lemma partner_no_dependency {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTF : TopForm G C) {q j w r : ℕ}
    (hdirty : ¬ BelowF G C q)
    (hlast : ∀ k, q < k → k < C.gates.length → (gateAt C k).op = .and → BelowF G C k)
    (hj : j < C.gates.length) (hja : (gateAt C j).op = .and) (hjc : BelowF G C j)
    (hinputs : (gateAt C j).inputs = [w,r] ∨ (gateAt C j).inputs = [r,w])
    (hp : Relation.ReflTransGen (MixedColor.OrStep n C) w (n+q)) :
    r ≠ n+q ∧ (n ≤ r → ¬ InCone n C q (r-n)) := by
  have hnot := LastDirtyAndFrontier.partner_not_reaches G C hAO hdirty hj hja hjc hinputs hp
  constructor
  · intro heq
    rw [heq] at hnot
    exact hnot .refl
  · intro hn hc
    have hrmem : r ∈ (gateAt C j).inputs := by
      rcases hinputs with hs | hs <;> simp [hs]
    have hrj := hAO.2.1 j hj r hrmem
    have hrcone : InCone n C (r-n) j :=
      (JunkPurity.inCone_iff n C (r-n) j hj).mpr ⟨r,hrmem,hn,hrj,Or.inl rfl⟩
    have hpath := cone_to_or_path G C hAO hTF hlast hj hja (by omega) hrcone (Or.inr hc)
    have heq : n+(r-n) = r := by omega
    exact hnot (by simpa only [heq] using hpath)

end PEqualNP.Outside.L_meta_3566.LastDirtyAndDependency

namespace PEqualNP.Outside.L_meta_3566.PrivateInputIndependence

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma wire_eq {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (H : ℕ) (a : Fin n)
    (hsole : ∀ j, j < C.gates.length → a.val ∈ (gateAt C j).inputs → j = H)
    (x y : Fin n → Bool) (hxy : ∀ v, v ≠ a → x v = y v)
    (w : ℕ) (hwa : w ≠ a.val)
    (hno : w ≠ n+H ∧ (n ≤ w → ¬ InCone n C H (w-n))) : value C x w = value C y w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · rw [value_input C x w hwn,value_input C y w hwn]
      apply hxy
      intro heq
      exact hwa (congrArg Fin.val heq)
    by_cases hwlen : w < n+C.gates.length
    · let k := w-n
      have hk : k < C.gates.length := by dsimp [k]; omega
      have hw : w = n+k := by dsimp [k]; omega
      have hkH : k ≠ H := by intro heq; apply hno.1; omega
      have hanc : ¬ InCone n C H k := hno.2 (by omega)
      rw [hw,value_gate C hAO.2.1 x k hk,value_gate C hAO.2.1 y k hk]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hub : u < w := by have := hAO.2.1 k hk u hu; omega
      apply ih u hub
      · intro heq
        subst u
        exact hkH (hsole k hk hu)
      · constructor
        · intro heq
          subst u
          exact hanc (JunkPurity.cone_step C hAO hk hu (Or.inl rfl))
        · intro hnu hcu
          exact hanc ((JunkPurity.inCone_iff n C H k hk).mpr
            ⟨u,hu,hnu,hAO.2.1 k hk u hu,Or.inr hcu⟩)
    · rw [value_missing C x w (by omega),value_missing C y w (by omega)]

end PEqualNP.Outside.L_meta_3566.PrivateInputIndependence

namespace PEqualNP.Outside.L_meta_3566.ReaderDegreeCount

open PEqualNP.TopForm

lemma neighbors_card_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (a : Fin n) {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (v : ι → Fin n)
    (hne : ∀ j ∈ J, v j ≠ a)
    (hcover : ∀ c, G.Adj a c → ∃ j ∈ J, G.Adj (v j) c) :
    (Finset.univ.filter (G.Adj a)).card ≤ J.card := by
  classical
  let S : ι → Finset (Fin n) := fun j =>
    Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj (v j) c)
  have hsub : Finset.univ.filter (G.Adj a) ⊆ J.biUnion S := by
    intro c hc
    obtain ⟨j, hj, hv⟩ := hcover c (Finset.mem_filter.mp hc).2
    exact Finset.mem_biUnion.mpr ⟨j, hj,
      Finset.mem_filter.mpr ⟨Finset.mem_univ c, (Finset.mem_filter.mp hc).2, hv⟩⟩
  calc
    (Finset.univ.filter (G.Adj a)).card ≤ (J.biUnion S).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ J, (S j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ J, 1 := Finset.sum_le_sum (fun j hj => h4 a (v j) (hne j hj).symm)
    _ = J.card := by simp

end PEqualNP.Outside.L_meta_3566.ReaderDegreeCount

namespace PEqualNP.Outside.L_meta_3566.PrivateReaderTransport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership ParallelRewrite

lemma edge_top_dependency {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (H : ℕ) (a : Fin n) (hdirty : ¬ BelowF G C H)
    (hsole : ∀ j, j < C.gates.length → a.val ∈ (gateAt C j).inputs → j = H)
    (c : Fin n) (hac : G.Adj a c) :
    ∃ k ∈ tops G C, gateVal n C k (pairInput a c) = true ∧ InCone n C H k := by
  classical
  obtain ⟨k,hk,_,htrue⟩ := TopFrontierCoverage.edge_reaches_top G C hAO hfun a c hac
  have hkd := MixedColor.topData hk
  have hkH : k ≠ H := by intro heq; subst k; exact hdirty hkd.2.2
  refine ⟨k,hk,htrue,?_⟩
  by_contra hno
  have he := PrivateInputIndependence.wire_eq C hAO H a hsole (pairInput a c) (pairInput c c)
    (by intro v hva; simp [pairInput,hva]) (n+k) (by have := a.isLt; omega)
    ⟨by omega,by simpa using hno⟩
  have hsingle : gateVal n C k (pairInput c c) = true := by
    change value C (pairInput c c) (n+k) = true
    rw [← he]
    exact htrue
  exact G.irrefl ((MixedColor.graphFun_pair G c c).mp (hkd.2.2 _ hsingle))

lemma leaf_ne_private {n : ℕ} (C : Circuit) (H : ℕ) (a : Fin n)
    (hHa : (gateAt C H).op = .and)
    (hsole : ∀ j, j < C.gates.length → a.val ∈ (gateAt C j).inputs → j = H)
    {j T : ℕ} (hj : j < C.gates.length) (hjo : (gateAt C j).op = .or)
    (hT : T ∈ (gateAt C j).inputs) {v : Fin n} (hv : v ∈ orIn n C T) : v ≠ a := by
  intro heq
  subst v
  simp only [orIn,Finset.mem_filter,Finset.mem_univ,true_and] at hv
  rcases hv with hv | ⟨k,hk,_,hko,hka⟩
  · have hjH := hsole j hj (hv ▸ hT)
    rw [hjH,hHa] at hjo
    cases hjo
  · have hkH := hsole k hk hka
    rw [hkH,hHa] at hko
    cases hko

lemma neighbor_transport {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅) (hTF : TopForm G C)
    (H : ℕ) (a : Fin n) (hdirty : ¬ BelowF G C H)
    (hsole : ∀ j, j < C.gates.length → a.val ∈ (gateAt C j).inputs → j = H)
    (hlast : ∀ k, H < k → k < C.gates.length → (gateAt C k).op = .and → BelowF G C k)
    (hreadOR : ∀ j ∈ readers n C H, (gateAt C j).op = .or)
    (T : ℕ → ℕ) (v : ℕ → Fin n)
    (hleaf : ∀ j ∈ readers n C H, T j ∈ (gateAt C j).inputs ∧ v j ∈ orIn n C (T j))
    (c : Fin n) (hac : G.Adj a c) : ∃ j ∈ readers n C H, G.Adj (v j) c := by
  classical
  obtain ⟨k,hkT,hkt,hHk⟩ := edge_top_dependency G C hAO hfun H a hdirty hsole c hac
  obtain ⟨hk,hka,hkc⟩ := MixedColor.topData hkT
  have hkH : k ≠ H := by intro heq; subst k; exact hdirty hkc
  obtain ⟨w,hwm,hnw,hwk,hHw⟩ := (JunkPurity.inCone_iff n C H k hk).mp hHk
  have hwcone : InCone n C (w-n) k :=
    (JunkPurity.inCone_iff n C (w-n) k hk).mpr ⟨w,hwm,hnw,hwk,Or.inl rfl⟩
  have hwpath := LastDirtyAndDependency.cone_to_or_path G C hAO hTF hlast hk hka
    (by omega) hwcone hHw
  have hw_eq : n+(w-n) = w := by omega
  rw [hw_eq] at hwpath
  obtain ⟨u,z,huz⟩ := MixedColor.binaryInputs hAO hk
  have hwuz : w = u ∨ w = z := by simpa [huz] using hwm
  obtain ⟨r,hshape⟩ : ∃ r, (gateAt C k).inputs = [w,r] ∨ (gateAt C k).inputs = [r,w] := by
    rcases hwuz with hwu | hwz
    · exact ⟨z,Or.inl (hwu ▸ huz)⟩
    · exact ⟨u,Or.inr (hwz ▸ huz)⟩
  have hrmem : r ∈ (gateAt C k).inputs := by rcases hshape with hs | hs <;> simp [hs]
  have hrno := LastDirtyAndDependency.partner_no_dependency G C hAO hTF hdirty hlast
    hk hka hkc hshape hwpath
  have hrna : r ≠ a.val := by
    intro heq
    subst r
    exact hkH (hsole k hk hrmem)
  have hrt : value C (pairInput a c) r = true :=
    ((MixedColor.val_and (n := n) (C := C) (x := List.ofFn (pairInput a c))
      (by simp) hk hka).mp hkt r hrmem).2
  have hre := PrivateInputIndependence.wire_eq C hAO H a hsole (pairInput a c) (pairInput c c)
    (by intro z hza; simp [pairInput,hza]) r hrna hrno
  have hrs : value C (pairInput c c) r = true := by rw [← hre]; exact hrt
  rcases Relation.ReflTransGen.cases_tail hwpath with hwH | ⟨z,hpre,hstep⟩
  · have hkr : k ∈ readers n C H := by
      simp only [readers,Finset.mem_filter,Finset.mem_range]
      exact ⟨hk,hwH ▸ hwm⟩
    have hko := hreadOR k hkr
    rw [hka] at hko
    cases hko
  · obtain ⟨j,hj,rfl,hjo,hjH,_⟩ := hstep
    have hjr : j ∈ readers n C H := by
      simp only [readers,Finset.mem_filter,Finset.mem_range]
      exact ⟨hj,hjH⟩
    obtain ⟨hTj,hvj⟩ := hleaf j hjr
    have hTval : value C (pairInput (v j) c) (T j) = true :=
      MixedColor.reach_var_val _ _ _ (MixedColor.mem_orIn_reach (v j) hvj)
        (MixedColor.pairInput_left (v j) c)
    have hjval : value C (pairInput (v j) c) (n+j) = true :=
      (MixedColor.val_or (n := n) (C := C) (x := List.ofFn (pairInput (v j) c))
        (by simp) hj hjo).mpr ⟨T j,hTj,hAO.2.1 j hj _ hTj,hTval⟩
    have hwval : value C (pairInput (v j) c) w = true := MixedColor.orStep_up (by simp) hpre hjval
    have hmono : pairInput c c ≤ pairInput (v j) c := by
      intro z
      by_cases hzc : z = c <;> simp [pairInput,hzc]
    have hrval : value C (pairInput (v j) c) r = true :=
      Bool.le_iff_imp.mp ((WireFacts.wire_monotone C hAO r) hmono) hrs
    have hkval : gateVal n C k (pairInput (v j) c) = true := by
      change value C (pairInput (v j) c) (n+k) = true
      rw [value_gate C hAO.2.1 _ k hk,hka]
      rcases hshape with hs | hs <;> simp [hs,GateOp.eval,hwval,hrval]
    exact ⟨j,hjr,(MixedColor.graphFun_pair G (v j) c).mp (hkc _ hkval)⟩

end PEqualNP.Outside.L_meta_3566.PrivateReaderTransport

namespace PEqualNP.Outside.L_meta_3566.PrivateReaderDegree

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma degree_le_readers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hTF : TopForm G C) (h4 : NoFourCycle G) (H : ℕ) (a : Fin n)
    (hHa : (gateAt C H).op = .and) (hdirty : ¬ BelowF G C H)
    (hsole : ∀ j, j < C.gates.length → a.val ∈ (gateAt C j).inputs → j = H)
    (hlast : ∀ k, H < k → k < C.gates.length → (gateAt C k).op = .and → BelowF G C k)
    (hreadOR : ∀ j ∈ readers n C H, (gateAt C j).op = .or)
    (hraw : ∀ j ∈ readers n C H, ∃ T ∈ (gateAt C j).inputs, (orIn n C T).Nonempty) :
    G.degree a ≤ (readers n C H).card := by
  classical
  have hex : ∀ j : ℕ, ∃ T : ℕ, ∃ v : Fin n, j ∈ readers n C H →
      T ∈ (gateAt C j).inputs ∧ v ∈ orIn n C T := by
    intro j
    by_cases hj : j ∈ readers n C H
    · obtain ⟨T,hT,v,hv⟩ := hraw j hj
      exact ⟨T,v,fun _ => ⟨hT,hv⟩⟩
    · exact ⟨0,a,fun h => (hj h).elim⟩
  choose T v hdata using hex
  have hne : ∀ j ∈ readers n C H, v j ≠ a := by
    intro j hj
    have hjl : j < C.gates.length := (Finset.mem_filter.mp hj).1 |> Finset.mem_range.mp
    exact PrivateReaderTransport.leaf_ne_private C H a hHa hsole hjl (hreadOR j hj)
      (hdata j hj).1 (hdata j hj).2
  have hcover := PrivateReaderTransport.neighbor_transport G C hAO hfun hTF H a hdirty
    hsole hlast hreadOR T v hdata
  rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
  exact ReaderDegreeCount.neighbors_card_le G h4 a (readers n C H) v hne hcover

end PEqualNP.Outside.L_meta_3566.PrivateReaderDegree

namespace PEqualNP.Outside.L_meta_3566.UniformSavingPeel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.EdgeOwnership

variable {n : ℕ}

lemma all_or_source (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C0 : Circuit) (hC0 : IsLeastAO G C0) (hTF : TopForm G C0) (hfour : NoFourCycle G)
    (a : Fin n) (H : ℕ) (hH : H < C0.size)
    (hHand : (gateAt C0 H).op = GateOp.and) (hHa : a.val ∈ (gateAt C0 H).inputs)
    (hpos : 0 < G.degree a) (hdirty : ¬ BelowF G C0 H)
    (hsole : ∀ j, j < C0.gates.length → a.val ∈ (gateAt C0 j).inputs → j = H)
    (hlast : ∀ k, H < k → k < C0.gates.length →
      (gateAt C0 k).op = GateOp.and → BelowF G C0 k)
    (hreadOR : ∀ j ∈ readers n C0 H, (gateAt C0 j).op = GateOp.or)
    (hraw : ∀ j ∈ readers n C0 H, ∃ T ∈ (gateAt C0 j).inputs,
      (orIn n C0 T).Nonempty) :
    ∃ z : Fin n, 0 < G.degree z ∧ UniformPeel G z := by
  have hr := PrivateReaderDegree.degree_le_readers G C0 hC0.1 hC0.2.1 hTF hfour H a
    hHand hdirty hsole hlast hreadOR hraw
  have ho := LeastOutputValidity.least_output_upper_of_size_pos G C0 hC0 (by omega)
  obtain ⟨z, hz, hp⟩ := GateSavings.least_reader_peel G C0 hC0 ho a hpos H hH hHand hHa
    (by omega) (fun _ => hr)
  exact ⟨z, hz, hp⟩

end PEqualNP.Outside.L_meta_3566.UniformSavingPeel
