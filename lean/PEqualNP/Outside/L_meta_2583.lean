import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583


namespace Consensus

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

def appendBinary (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op, [a, b]⟩], n + C.gates.length⟩

lemma appendBinary_size (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (appendBinary n C op a b).size = C.size + 1 := by
  simp [appendBinary, Circuit.size]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  generalize C.gates = gs
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp
    omega

lemma appendBinary_wires (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ)
    (x : List Bool) :
    (appendBinary n C op a b).wires x =
      C.wires x ++ [op.eval [(C.wires x).getD a false, (C.wires x).getD b false]] := by
  simp [appendBinary, Circuit.wires, List.foldl_append]

lemma appendBinary_eval (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ)
    (x : List Bool) (hx : x.length = n) :
    (appendBinary n C op a b).eval x =
      op.eval [(C.wires x).getD a false, (C.wires x).getD b false] := by
  unfold Circuit.eval
  rw [appendBinary_wires]
  change (C.wires x ++ [_]).getD (n + C.gates.length) false = _
  have hlen := wires_length C x
  rw [hx] at hlen
  rw [← hlen]
  simp [List.getD_eq_getElem?_getD]

lemma appendBinary_old_wire (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ)
    (x : List Bool) (hx : x.length = n) (w : ℕ) (hw : w < n + C.gates.length) :
    ((appendBinary n C op a b).wires x).getD w false = (C.wires x).getD w false := by
  rw [appendBinary_wires]
  have hlen := wires_length C x
  rw [hx] at hlen
  have hw' : w < (C.wires x).length := by omega
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hw']

lemma appendBinary_isAO2 (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ)
    (hC : IsAO2 n C) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) :
    IsAO2 n (appendBinary n C op a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [appendBinary, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hC.1 g hg
    · exact hop
  · intro j hj i hi
    change j < (C.gates ++ [(⟨op, [a, b]⟩ : Gate)]).length at hj
    change i ∈ ((C.gates ++ [(⟨op, [a, b]⟩ : Gate)]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hjC : j < C.gates.length
    · have heq : (C.gates ++ [(⟨op, [a, b]⟩ : Gate)]).getD j (⟨GateOp.or, []⟩ : Gate) =
          C.gates.getD j ⟨GateOp.or, []⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hjC]
      rw [heq] at hi
      exact hC.2.1 j hjC i hi
    · have hj' : j = C.gates.length := by simp only [List.length_append, List.length_singleton] at hj; omega
      subst j
      simp [List.getD_eq_getElem?_getD] at hi
      rcases hi with rfl | rfl <;> assumption
  · intro g hg
    simp only [appendBinary, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hC.2.2 g hg
    · rfl

lemma bool_consensus (a b c d : Bool) :
    (((a || c) && (b || d)) && (b || c)) = ((b && (a || c)) || (c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

def consensusOriginal (n : ℕ) (C : Circuit) (a b c d : ℕ) : Circuit :=
  let s := n + C.gates.length
  let C₁ := appendBinary n C GateOp.or a c
  let C₂ := appendBinary n C₁ GateOp.or b d
  let C₃ := appendBinary n C₂ GateOp.and s (s + 1)
  let C₄ := appendBinary n C₃ GateOp.or b c
  appendBinary n C₄ GateOp.and (s + 2) (s + 3)

def consensusReplacement (n : ℕ) (C : Circuit) (a b c d : ℕ) : Circuit :=
  let s := n + C.gates.length
  let C₁ := appendBinary n C GateOp.or a c
  let C₂ := appendBinary n C₁ GateOp.and b s
  let C₃ := appendBinary n C₂ GateOp.and c d
  appendBinary n C₃ GateOp.or (s + 1) (s + 2)

lemma consensus_sizes (n : ℕ) (C : Circuit) (a b c d : ℕ) :
    (consensusOriginal n C a b c d).size = C.size + 5 ∧
    (consensusReplacement n C a b c d).size = C.size + 4 := by
  simp [consensusOriginal, consensusReplacement, appendBinary, Circuit.size]

lemma consensusOriginal_isAO2 (n : ℕ) (C : Circuit) (a b c d : ℕ)
    (hC : IsAO2 n C) (ha : a < n + C.gates.length) (hb : b < n + C.gates.length)
    (hc : c < n + C.gates.length) (hd : d < n + C.gates.length) :
    IsAO2 n (consensusOriginal n C a b c d) := by
  unfold consensusOriginal
  dsimp only
  repeat' apply appendBinary_isAO2
  all_goals first
    | exact hC
    | exact Or.inl rfl
    | exact Or.inr rfl
    | assumption
    | (simp only [appendBinary, List.length_append, List.length_cons, List.length_nil]; omega)

lemma consensusReplacement_isAO2 (n : ℕ) (C : Circuit) (a b c d : ℕ)
    (hC : IsAO2 n C) (ha : a < n + C.gates.length) (hb : b < n + C.gates.length)
    (hc : c < n + C.gates.length) (hd : d < n + C.gates.length) :
    IsAO2 n (consensusReplacement n C a b c d) := by
  unfold consensusReplacement
  dsimp only
  repeat' apply appendBinary_isAO2
  all_goals first
    | exact hC
    | exact Or.inl rfl
    | exact Or.inr rfl
    | assumption
    | (simp only [appendBinary, List.length_append, List.length_cons, List.length_nil]; omega)

lemma consensus_eval (n : ℕ) (C : Circuit) (a b c d : ℕ)
    (_ha : a < n + C.gates.length) (hb : b < n + C.gates.length)
    (hc : c < n + C.gates.length) (hd : d < n + C.gates.length)
    (x : List Bool) (hx : x.length = n) :
    (consensusOriginal n C a b c d).eval x =
      (consensusReplacement n C a b c d).eval x := by
  unfold consensusOriginal consensusReplacement
  simp only [appendBinary_eval n _ _ _ _ x hx, appendBinary_wires]
  have hlen : (C.wires x).length = n + C.gates.length := by rw [wires_length, hx]
  simp (disch := (simp only [List.length_append, List.length_singleton, hlen]; omega)) only [List.getD_append, List.getD_append_right,
    List.length_append, List.length_singleton, hlen,
    Nat.sub_self,
    List.getD_cons_zero, GateOp.eval, List.any_cons, List.any_nil,
    List.all_cons, List.all_nil, Bool.or_false, Bool.and_true, id_eq]
  exact bool_consensus _ _ _ _

lemma consensus_replacement (n : ℕ) (C : Circuit) (a b c d : ℕ)
    (hC : IsAO2 n C) (ha : a < n + C.gates.length) (hb : b < n + C.gates.length)
    (hc : c < n + C.gates.length) (hd : d < n + C.gates.length) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + 1 = (consensusOriginal n C a b c d).size ∧
      ∀ x : List Bool, x.length = n → D.eval x = (consensusOriginal n C a b c d).eval x := by
  refine ⟨consensusReplacement n C a b c d,
    consensusReplacement_isAO2 n C a b c d hC ha hb hc hd, ?_, ?_⟩
  · obtain ⟨ho, hr⟩ := consensus_sizes n C a b c d
    omega
  · intro x hx
    exact (consensus_eval n C a b c d ha hb hc hd x hx).symm

end Consensus

namespace Cnf

open Finset

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

def Covers (T : Finset (Fin n)) : Prop :=
  ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T

lemma cover_erase_failure (T : Finset (Fin n))
    (hT : Covers G T) (hmin : ∀ S, Covers G S → T.card ≤ S.card) {u : Fin n} (hu : u ∈ T) :
    ∃ v, G.Adj u v ∧ v ∉ T := by
  by_contra h
  push Not at h
  have hc : Covers G (T.erase u) := by
    intro a b hab
    by_cases ha : a = u
    · subst a
      right
      exact mem_erase.mpr ⟨hab.ne', h b hab⟩
    by_cases hb : b = u
    · subst b
      left
      exact mem_erase.mpr ⟨hab.ne, h a hab.symm⟩
    rcases hT a b hab with hat | hbt
    · exact Or.inl (mem_erase.mpr ⟨ha, hat⟩)
    · exact Or.inr (mem_erase.mpr ⟨hb, hbt⟩)
  have hh := hmin _ hc
  have he := card_erase_add_one hu
  omega

lemma cover_swap (T : Finset (Fin n)) (hT : Covers G T) (u : Fin n) :
    Covers G (T.erase u ∪ G.neighborFinset u) := by
  intro a b hab
  rcases hT a b hab with ha | hb
  · by_cases hau : a = u
    · subst a
      exact Or.inr (mem_union_right _ (G.mem_neighborFinset u b |>.mpr hab))
    · exact Or.inl (mem_union_left _ (mem_erase.mpr ⟨hau, ha⟩))
  · by_cases hbu : b = u
    · subst b
      exact Or.inl (mem_union_right _ (G.mem_neighborFinset u a |>.mpr hab.symm))
    · exact Or.inr (mem_union_left _ (mem_erase.mpr ⟨hbu, hb⟩))

lemma not_mem_swap (T : Finset (Fin n)) (u : Fin n) :
    u ∉ T.erase u ∪ G.neighborFinset u := by
  simp

lemma neighbor_subset_clause (T C : Finset (Fin n)) (u : Fin n)
    (hC : Covers G C) (hsub : C ⊆ T.erase u ∪ G.neighborFinset u) :
    G.neighborFinset u ⊆ C := by
  intro v hv
  rcases hC u v (G.mem_neighborFinset u v |>.mp hv) with hu | hv
  · exact False.elim (not_mem_swap G T u (hsub hu))
  · exact hv

lemma outside_clause (T C : Finset (Fin n)) (u : Fin n)
    (hC : Covers G C) (hsub : C ⊆ T.erase u ∪ G.neighborFinset u) :
    C \ T = G.neighborFinset u \ T := by
  apply Finset.Subset.antisymm
  · intro v hv
    rcases mem_sdiff.mp hv with ⟨hvC, hvT⟩
    rcases mem_union.mp (hsub hvC) with hvE | hvN
    · exact False.elim (hvT (mem_of_mem_erase hvE))
    · exact mem_sdiff.mpr ⟨hvN, hvT⟩
  · exact sdiff_subset_sdiff_left T (neighbor_subset_clause G T C u hC hsub)

lemma common_neighbor_unique (hfour : PEqualNP.TopForm.NoFourCycle G)
    {u v a b : Fin n} (huv : u ≠ v)
    (hua : G.Adj u a) (hva : G.Adj v a)
    (hub : G.Adj u b) (hvb : G.Adj v b) : a = b := by
  apply Finset.card_le_one.mp (hfour u v huv)
  · exact mem_filter.mpr ⟨mem_univ _, hua, hva⟩
  · exact mem_filter.mpr ⟨mem_univ _, hub, hvb⟩

lemma no_edge_with_common_neighbor (s : Fin n → Bool)
    (hs : ∀ a b, G.Adj a b → s a ≠ s b)
    {u v w : Fin n} (huw : G.Adj u w) (hvw : G.Adj v w) : ¬ G.Adj u v := by
  intro huv
  have h1 := hs u w huw
  have h2 := hs v w hvw
  have h3 := hs u v huv
  cases hsu : s u <;> cases hsv : s v <;> cases hsw : s w <;> simp_all

lemma cover_double_swap (T : Finset (Fin n)) (hT : Covers G T)
    (u v w : Fin n) (huv : ¬ G.Adj u v)
    (hu : ∀ a, G.Adj u a → a ∉ T → a = w)
    (hv : ∀ a, G.Adj v a → a ∉ T → a = w) :
    Covers G (insert w ((T.erase u).erase v)) := by
  have hneigh : ∀ x a, (x = u ∨ x = v) → G.Adj x a →
      a ∈ insert w ((T.erase u).erase v) := by
    intro x a hx hxa
    rcases hx with rfl | rfl
    · by_cases ha : a ∈ T
      · apply mem_insert_of_mem
        apply mem_erase.mpr
        refine ⟨?_, mem_erase.mpr ⟨hxa.ne', ha⟩⟩
        rintro rfl
        exact huv hxa
      · rw [hu a hxa ha]
        exact mem_insert_self _ _
    · by_cases ha : a ∈ T
      · apply mem_insert_of_mem
        apply mem_erase.mpr
        refine ⟨hxa.ne', mem_erase.mpr ⟨?_, ha⟩⟩
        rintro rfl
        exact huv hxa.symm
      · rw [hv a hxa ha]
        exact mem_insert_self _ _
  intro a b hab
  rcases hT a b hab with ha | hb
  · by_cases hau : a = u ∨ a = v
    · exact Or.inr (hneigh a b hau hab)
    · left
      simp only [not_or] at hau
      exact mem_insert_of_mem (mem_erase.mpr ⟨hau.2, mem_erase.mpr ⟨hau.1, ha⟩⟩)
  · by_cases hbu : b = u ∨ b = v
    · exact Or.inl (hneigh b a hbu hab.symm)
    · right
      simp only [not_or] at hbu
      exact mem_insert_of_mem (mem_erase.mpr ⟨hbu.2, mem_erase.mpr ⟨hbu.1, hb⟩⟩)

lemma swap_clauses_injective (T : Finset (Fin n)) (hT : Covers G T)
    (hmin : ∀ S, Covers G S → T.card ≤ S.card)
    (s : Fin n → Bool) (hs : ∀ a b, G.Adj a b → s a ≠ s b)
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    {u v : Fin n} (hu : u ∈ T) (hv : v ∈ T)
    (C D : Finset (Fin n)) (hC : Covers G C) (hD : Covers G D)
    (hsubC : C ⊆ T.erase u ∪ G.neighborFinset u)
    (hsubD : D ⊆ T.erase v ∪ G.neighborFinset v)
    (hCD : C = D) : u = v := by
  by_contra huv
  have hout : G.neighborFinset u \ T = G.neighborFinset v \ T := by
    rw [← outside_clause G T C u hC hsubC, ← outside_clause G T D v hD hsubD, hCD]
  obtain ⟨w, huw, hwT⟩ := cover_erase_failure G T hT hmin hu
  have hvw : G.Adj v w := by
    have hw : w ∈ G.neighborFinset u \ T := mem_sdiff.mpr ⟨G.mem_neighborFinset u w |>.mpr huw, hwT⟩
    rw [hout] at hw
    exact G.mem_neighborFinset v w |>.mp (mem_sdiff.mp hw).1
  have husingle : ∀ a, G.Adj u a → a ∉ T → a = w := by
    intro a hua haT
    have ha : a ∈ G.neighborFinset u \ T := mem_sdiff.mpr ⟨G.mem_neighborFinset u a |>.mpr hua, haT⟩
    rw [hout] at ha
    exact common_neighbor_unique G hfour huv hua
      (G.mem_neighborFinset v a |>.mp (mem_sdiff.mp ha).1) huw hvw
  have hvsingle : ∀ a, G.Adj v a → a ∉ T → a = w := by
    intro a hva haT
    have ha : a ∈ G.neighborFinset v \ T := mem_sdiff.mpr ⟨G.mem_neighborFinset v a |>.mpr hva, haT⟩
    rw [← hout] at ha
    exact husingle a (G.mem_neighborFinset u a |>.mp (mem_sdiff.mp ha).1) haT
  have hnew := cover_double_swap G T hT u v w
    (no_edge_with_common_neighbor G s hs huw hvw) husingle hvsingle
  have hsize := hmin _ hnew
  have hwE : w ∉ (T.erase u).erase v := by
    intro hw
    exact hwT (mem_of_mem_erase (mem_of_mem_erase hw))
  have hvE : v ∈ T.erase u := mem_erase.mpr ⟨Ne.symm huv, hv⟩
  have h1 := card_erase_add_one hu
  have h2 := card_erase_add_one hvE
  rw [card_insert_of_notMem hwE] at hsize
  omega

lemma clause_family_bound (T : Finset (Fin n)) (hT : Covers G T)
    (hmin : ∀ S, Covers G S → T.card ≤ S.card)
    (s : Fin n → Bool) (hs : ∀ a b, G.Adj a b → s a ≠ s b)
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (F : Finset (Finset (Fin n)))
    (hcover : ∀ U ∈ F, Covers G U)
    (hcomplete : ∀ U, Covers G U → ∃ W ∈ F, W ⊆ U) :
    T.card + ∑ u ∈ T, (G.neighborFinset u).card ≤ ∑ W ∈ F, W.card := by
  classical
  have hchoices : ∀ u : Fin n, ∃ W ∈ F, W ⊆ T.erase u ∪ G.neighborFinset u := by
    intro u
    exact hcomplete _ (cover_swap G T hT u)
  choose C hCF hCsub using hchoices
  have hTmem : T ∈ F := by
    obtain ⟨W, hWF, hWT⟩ := hcomplete T hT
    have hcard := hmin W (hcover W hWF)
    have heq : W = T := eq_of_subset_of_card_le hWT hcard
    rwa [heq] at hWF
  have hinj : Set.InjOn C (T : Set (Fin n)) := by
    intro u hu v hv heq
    exact swap_clauses_injective G T hT hmin s hs hfour hu hv
      (C u) (C v) (hcover _ (hCF u)) (hcover _ (hCF v)) (hCsub u) (hCsub v) heq
  have hnot : T ∉ T.image C := by
    rintro h
    obtain ⟨u, hu, heq⟩ := mem_image.mp h
    have hbad : u ∈ C u := heq.symm ▸ hu
    exact not_mem_swap G T u (hCsub u hbad)
  have hsubset : insert T (T.image C) ⊆ F := by
    intro W hW
    rcases mem_insert.mp hW with rfl | hW
    · exact hTmem
    · obtain ⟨u, _, rfl⟩ := mem_image.mp hW
      exact hCF u
  have hdeg : (∑ u ∈ T, (G.neighborFinset u).card) ≤ ∑ u ∈ T, (C u).card := by
    apply Finset.sum_le_sum
    intro u hu
    exact card_le_card (neighbor_subset_clause G T (C u) u (hcover _ (hCF u)) (hCsub u))
  calc T.card + ∑ u ∈ T, (G.neighborFinset u).card
      ≤ T.card + ∑ u ∈ T, (C u).card := Nat.add_le_add_left hdeg _
    _ = ∑ W ∈ insert T (T.image C), W.card := by
      rw [sum_insert hnot, sum_image hinj]
    _ ≤ ∑ W ∈ F, W.card :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => Nat.zero_le _)

lemma edges_le_cover_degrees (T : Finset (Fin n)) (hT : Covers G T) :
    G.edgeFinset.card ≤ ∑ u ∈ T, (G.neighborFinset u).card := by
  classical
  have hsub : G.edgeFinset ⊆ T.biUnion (fun u => G.incidenceFinset u) := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := by simpa using he
      rcases hT u v huv with hu | hv
      · apply mem_biUnion.mpr
        refine ⟨u, hu, ?_⟩
        rw [G.incidenceFinset_eq_filter]
        exact mem_filter.mpr ⟨he, by simp⟩
      · apply mem_biUnion.mpr
        refine ⟨v, hv, ?_⟩
        rw [G.incidenceFinset_eq_filter]
        exact mem_filter.mpr ⟨he, by simp⟩
  calc G.edgeFinset.card ≤ (T.biUnion (fun u => G.incidenceFinset u)).card := card_le_card hsub
    _ ≤ ∑ u ∈ T, (G.incidenceFinset u).card := card_biUnion_le
    _ = ∑ u ∈ T, (G.neighborFinset u).card := by simp

lemma clause_family_edge_bound (T : Finset (Fin n)) (hT : Covers G T)
    (hmin : ∀ S, Covers G S → T.card ≤ S.card)
    (s : Fin n → Bool) (hs : ∀ a b, G.Adj a b → s a ≠ s b)
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (F : Finset (Finset (Fin n)))
    (hcover : ∀ U ∈ F, Covers G U)
    (hcomplete : ∀ U, Covers G U → ∃ W ∈ F, W ⊆ U) :
    T.card + G.edgeFinset.card ≤ ∑ W ∈ F, W.card := by
  exact le_trans (Nat.add_le_add_left (edges_le_cover_degrees G T hT) _)
    (clause_family_bound G T hT hmin s hs hfour F hcover hcomplete)

lemma cnf_clause_properties (F : Finset (Finset (Fin n)))
    (hF : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    (∀ W ∈ F, Covers G W) ∧
    (∀ U, Covers G U → ∃ W ∈ F, W ⊆ U) := by
  classical
  constructor
  · intro W hWF u v huv
    let x : Fin n → Bool := fun a => decide (a = u ∨ a = v)
    have hx : ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true :=
      ⟨u, v, huv, by simp [x], by simp [x]⟩
    obtain ⟨a, haW, hax⟩ := (hF x).mpr hx W hWF
    have ha : a = u ∨ a = v := by simpa [x] using hax
    rcases ha with rfl | rfl
    · exact Or.inl haW
    · exact Or.inr haW
  · intro U hU
    by_contra h
    push Not at h
    let x : Fin n → Bool := fun a => decide (a ∉ U)
    have hx : ∀ W ∈ F, ∃ u ∈ W, x u = true := by
      intro W hWF
      obtain ⟨u, huW, huU⟩ := Finset.not_subset.mp (h W hWF)
      exact ⟨u, huW, by simp [x, huU]⟩
    obtain ⟨u, v, huv, hu, hv⟩ := (hF x).mp hx
    have huU : u ∉ U := by simpa [x] using hu
    have hvU : v ∉ U := by simpa [x] using hv
    exact (hU u v huv).elim huU hvU

lemma cnf_literal_lower_bound (T : Finset (Fin n)) (hT : Covers G T)
    (hmin : ∀ S, Covers G S → T.card ≤ S.card)
    (s : Fin n → Bool) (hs : ∀ a b, G.Adj a b → s a ≠ s b)
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (F : Finset (Finset (Fin n)))
    (hF : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    T.card + G.edgeFinset.card ≤ ∑ W ∈ F, W.card := by
  obtain ⟨hcover, hcomplete⟩ := cnf_clause_properties G F hF
  exact clause_family_edge_bound G T hT hmin s hs hfour F hcover hcomplete

end Cnf

namespace NeighborCover

open Finset

lemma cover_by_distinct_neighborhoods {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hfour : PEqualNP.TopForm.NoFourCycle G)
    (P : Finset (Fin n)) (hP : ∀ u v, G.Adj u v → u ∈ P ∨ v ∈ P) :
    ∃ T : Finset (Fin n),
      (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ (P.image (fun u => G.neighborFinset u)).card := by
  classical
  let R := P.image (fun u => G.neighborFinset u)
  have hcentre : ∀ S ∈ R, ∃ c : Fin n,
      ∀ u ∈ P, G.neighborFinset u = S → ∀ v, G.Adj u v → u = c ∨ v = c := by
    intro S hSR
    obtain ⟨u₀, hu₀, hu₀S⟩ := mem_image.mp hSR
    by_cases hsmall : S.card ≤ 1
    · by_cases hnonempty : S.Nonempty
      · obtain ⟨c, hcS⟩ := hnonempty
        refine ⟨c, ?_⟩
        intro u hu huS v huv
        right
        apply card_le_one.mp hsmall
        · rw [← huS]
          exact G.mem_neighborFinset u v |>.mpr huv
        · exact hcS
      · refine ⟨u₀, ?_⟩
        intro u hu huS v huv
        exfalso
        apply hnonempty
        refine ⟨v, ?_⟩
        rw [← huS]
        exact G.mem_neighborFinset u v |>.mpr huv
    · refine ⟨u₀, ?_⟩
      intro u hu huS v huv
      left
      by_contra hne
      have hsub : S ⊆ univ.filter (fun w => G.Adj u w ∧ G.Adj u₀ w) := by
        intro w hw
        apply mem_filter.mpr
        refine ⟨mem_univ _, ?_, ?_⟩
        · apply G.mem_neighborFinset u w |>.mp
          rwa [huS]
        · apply G.mem_neighborFinset u₀ w |>.mp
          rwa [hu₀S]
      exact hsmall (le_trans (card_le_card hsub) (hfour u u₀ hne))
  let c : {S // S ∈ R} → Fin n := fun S => Classical.choose (hcentre S.val S.property)
  let T := R.attach.image c
  refine ⟨T, ?_, ?_⟩
  · intro u v huv
    have hcover : ∀ a ∈ P, ∀ b, G.Adj a b → a ∈ T ∨ b ∈ T := by
      intro a ha b hab
      let S : {S // S ∈ R} := ⟨G.neighborFinset a, mem_image.mpr ⟨a, ha, rfl⟩⟩
      have hc : c S ∈ T := mem_image.mpr ⟨S, mem_attach R S, rfl⟩
      have hpair := Classical.choose_spec (hcentre S.val S.property) a ha rfl b hab
      change a = c S ∨ b = c S at hpair
      rcases hpair with heq | heq
      · exact Or.inl (heq ▸ hc)
      · exact Or.inr (heq ▸ hc)
    rcases hP u v huv with hu | hv
    · exact hcover u hu v huv
    · exact Or.symm (hcover v hv u huv.symm)
  · calc T.card ≤ R.attach.card := card_image_le
      _ = R.card := card_attach

end NeighborCover

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.CircuitMoves PEqualNP.TopForm PEqualNP.ReadK

def obstructionCircuit : Circuit :=
  { gates := [⟨GateOp.or, [0, 2]⟩,
              ⟨GateOp.or, [1, 3]⟩,
              ⟨GateOp.and, [4, 5]⟩,
              ⟨GateOp.or, [1, 2]⟩,
              ⟨GateOp.and, [6, 7]⟩]
    output := 8 }

lemma obstruction_ao2 : IsAO2 4 obstructionCircuit := by decide

def obstructionReplacement : Circuit :=
  { gates := [⟨GateOp.or, [0, 2]⟩,
              ⟨GateOp.and, [1, 4]⟩,
              ⟨GateOp.and, [2, 3]⟩,
              ⟨GateOp.or, [5, 6]⟩]
    output := 7 }

lemma obstruction_replacement_ao2 : IsAO2 4 obstructionReplacement := by decide

lemma obstruction_replacement_semantics :
    ∀ z : Fin 4 → Bool,
      circuitFun 4 obstructionReplacement z = circuitFun 4 obstructionCircuit z := by decide

lemma obstruction_replacement_read_one : IsReadK 4 obstructionReplacement 1 := by decide

lemma obstruction_replacement_smaller :
    obstructionReplacement.size < obstructionCircuit.size := by decide

lemma obstruction_no_four_cycle : NoFourCycle (edgeGraph 4 [(0, 1), (1, 2), (2, 3)]) := by decide

lemma obstruction_bipartite :
    ∀ u v : Fin 4, (edgeGraph 4 [(0, 1), (1, 2), (2, 3)]).Adj u v →
      decide (u.val % 2 = 0) ≠ decide (v.val % 2 = 0) := by decide

lemma obstruction_semantics :
    ∀ z : Fin 4 → Bool,
      circuitFun 4 obstructionCircuit z = graphFun (edgeGraph 4 [(0, 1), (1, 2), (2, 3)]) ∅ z := by decide

lemma obstruction_residual_nonbelow :
    ∀ i : Fin 4, ¬ WireBelowOutput 4 obstructionCircuit (4 + i.val) := by decide

lemma obstruction_top_form : TopForm (edgeGraph 4 [(0, 1), (1, 2), (2, 3)]) obstructionCircuit := by decide

lemma obstruction_size : obstructionCircuit.size = 5 := rfl

lemma obstruction_disjoint_edges :
    gateVal 4 obstructionCircuit 4 (pairInput 0 1) = true ∧
    gateVal 4 obstructionCircuit 4 (pairInput 2 3) = true := by decide

lemma obstruction_pair_prime :
    IsPrimeImplicant 4 obstructionCircuit ({0, 1} : Finset (Fin 4)) := by decide

lemma obstruction_pair_repeated :
    readsAtMost obstructionCircuit 4 (setList ({0, 1} : Finset (Fin 4))) 1 = false := by
  decide

lemma obstruction_not_read_one : ¬ IsReadK 4 obstructionCircuit 1 := by
  intro h
  have hp := h ({0, 1} : Finset (Fin 4)) obstruction_pair_prime
  rw [obstruction_pair_repeated] at hp
  contradiction

lemma obstruction_no_lift (D : Circuit) : ¬ Lift 4 obstructionCircuit D := by
  rintro ⟨m, hm, p, hp, h, hh, hnh, hgate, hbelow, heq⟩
  have hm' : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by
    have : m < 5 := hm
    omega
  rcases hm' with rfl | rfl | rfl | rfl | rfl <;>
    simp [obstructionCircuit] at hgate <;> omega

lemma obstruction_junkdrop_changes (D : Circuit)
    (hdrop : JunkDrop 4 obstructionCircuit D) :
    ∃ z : Fin 4 → Bool,
      circuitFun 4 obstructionCircuit z = true ∧ circuitFun 4 D z = false := by
  rcases hdrop with ⟨j, hj, u, hu, w, hw, hn, q, hq, r, hr, hsource, htarget⟩
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by
    have : j < 5 := hj
    omega
  rcases hj' with rfl | rfl | rfl | rfl | rfl
  · simp [obstructionCircuit] at htarget
  · simp [obstructionCircuit] at htarget
  · simp [obstructionCircuit] at htarget
    rcases htarget with ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩
    · simp [obstructionCircuit] at hsource
      rcases hsource with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨pairInput 2 3, by decide, by decide⟩
      · exact ⟨pairInput 0 1, by decide, by decide⟩
    · simp [obstructionCircuit] at hsource
      rcases hsource with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨pairInput 2 3, by decide, by decide⟩
      · exact ⟨pairInput 0 1, by decide, by decide⟩
  · simp [obstructionCircuit] at htarget
  · simp [obstructionCircuit] at htarget
    rcases htarget with ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩
    · simp [obstructionCircuit] at hsource
      rcases hsource with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨pairInput 2 3, by decide, by decide⟩
      · exact ⟨pairInput 0 1, by decide, by decide⟩
    · simp [obstructionCircuit] at hsource

lemma obstruction_no_preserving_junkdrop (D : Circuit) :
    JunkDrop 4 obstructionCircuit D →
      ¬ (∀ z : Fin 4 → Bool, circuitFun 4 D z = circuitFun 4 obstructionCircuit z) := by
  intro hd heq
  obtain ⟨z, hc, hd⟩ := obstruction_junkdrop_changes D hd
  have hz := heq z
  rw [hc, hd] at hz
  contradiction

lemma union_card_le_relation {α β : Type*} {s : Finset α} {t : Finset β}
    (r : α → β → Prop)
    (hs : ∀ a ∈ s, ∃ b, b ∈ t ∧ r a b)
    (ht : ∀ b ∈ t, ({ a ∈ s | r a b } : Set α).Subsingleton) : s.card ≤ t.card := by
  classical
  let f : s → t := fun a => ⟨(hs a a.property).choose, (hs a a.property).choose_spec.1⟩
  apply Finset.card_le_card_of_injective (f := f)
  intro a b hab
  apply Subtype.ext
  have hab' : (f a).val = (f b).val := congrArg Subtype.val hab
  apply ht (f a) (f a).property
  · exact ⟨a.property, (hs a a.property).choose_spec.2⟩
  · refine ⟨b.property, ?_⟩
    rw [hab']
    exact (hs b b.property).choose_spec.2

def unionGood {v c : ℕ} (n m : ℕ) (T : ℕ → Finset (Fin v))
    (S : Fin c → Finset (Fin v)) (a : Fin c) (u : Fin v) (j : ℕ) : Prop :=
  j < m ∧ T (n + j) ⊆ S a ∧ u ∈ T (n + j) ∧ ∃ u0 ∈ T (n + j), u0 < u

lemma union_good_large {v c n m : ℕ} {T : ℕ → Finset (Fin v)}
    {S : Fin c → Finset (Fin v)} {a : Fin c} {u : Fin v} {j : ℕ}
    (hg : unionGood n m T S a u j) : 2 ≤ (T (n + j)).card := by
  obtain ⟨u0, hu0, hlt⟩ := hg.2.2.2
  have hc : 1 < (T (n + j)).card :=
    Finset.one_lt_card.2 ⟨u0, hu0, u, hg.2.2.1, ne_of_lt hlt⟩
  omega

lemma union_no_below {v c n m : ℕ} (T : ℕ → Finset (Fin v))
    (S : Fin c → Finset (Fin v))
    (hin : ∀ w < n, (T w).card ≤ 1) (a : Fin c) (u : Fin v) (j w : ℕ)
    (hj : j < m) (hw : w < n + j)
    (hsub : T w ⊆ S a) (hu : u ∈ T w)
    (hmin : ∀ j', j' < j → ¬ unionGood n m T S a u j') :
    ∀ t ∈ T w, ¬ t < u := by
  intro t ht hlt
  by_cases hwn : w < n
  · have heq := Finset.card_le_one.1 (hin w hwn) t ht u hu
    exact (ne_of_lt hlt) heq
  · obtain ⟨j', rfl⟩ : ∃ j', w = n + j' := ⟨w - n, by omega⟩
    exact hmin j' (by omega) ⟨by omega, hsub, hu, t, ht, hlt⟩

lemma union_no_lt_aux {v c n m : ℕ} (T : ℕ → Finset (Fin v))
    (S : Fin c → Finset (Fin v))
    (hin : ∀ w < n, (T w).card ≤ 1) (a : Fin c) (u u' : Fin v) (j x y : ℕ)
    (hj : j < m) (hx : x < n + j) (hy : y < n + j)
    (hT : T (n + j) = T x ∪ T y)
    (hg : unionGood n m T S a u j)
    (hmin : ∀ j', j' < j → ¬ unionGood n m T S a u j')
    (hmin' : ∀ j', j' < j → ¬ unionGood n m T S a u' j')
    (hlt : u < u') (hu'x : u' ∈ T x) : False := by
  obtain ⟨_, hsub, hu, u0, hu0, hu0lt⟩ := hg
  have hsubx : T x ⊆ S a :=
    fun t ht => hsub (by rw [hT]; exact Finset.mem_union_left _ ht)
  have hsuby : T y ⊆ S a :=
    fun t ht => hsub (by rw [hT]; exact Finset.mem_union_right _ ht)
  have h1 := union_no_below T S hin a u' j x hj hx hsubx hu'x hmin'
  rw [hT, Finset.mem_union] at hu hu0
  rcases hu with hux | huy
  · exact h1 u hux hlt
  · have h2 := union_no_below T S hin a u j y hj hy hsuby huy hmin
    rcases hu0 with h | h
    · exact h1 u0 h (lt_trans hu0lt hlt)
    · exact h2 u0 h hu0lt

lemma union_no_lt {v c n m : ℕ} (T : ℕ → Finset (Fin v))
    (S : Fin c → Finset (Fin v))
    (hin : ∀ w < n, (T w).card ≤ 1)
    (hgate : ∀ j < m, 2 ≤ (T (n + j)).card →
      ∃ x y, x < n + j ∧ y < n + j ∧ T (n + j) = T x ∪ T y)
    (a : Fin c) (u u' : Fin v) (j : ℕ)
    (hg : unionGood n m T S a u j) (hg' : unionGood n m T S a u' j)
    (hmin : ∀ j', j' < j → ¬ unionGood n m T S a u j')
    (hmin' : ∀ j', j' < j → ¬ unionGood n m T S a u' j')
    (hlt : u < u') : False := by
  obtain ⟨x, y, hx, hy, hT⟩ := hgate j hg.1 (union_good_large hg)
  have hu' := hg'.2.2.1
  rw [hT, Finset.mem_union] at hu'
  rcases hu' with h | h
  · exact union_no_lt_aux T S hin a u u' j x y hg.1 hx hy hT hg hmin hmin' hlt h
  · exact union_no_lt_aux T S hin a u u' j y x hg.1 hy hx
      (by rw [hT, Finset.union_comm]) hg hmin hmin' hlt h

lemma union_inj_core {v c n m : ℕ} (T : ℕ → Finset (Fin v))
    (S : Fin c → Finset (Fin v))
    (hin : ∀ w < n, (T w).card ≤ 1)
    (hgate : ∀ j < m, 2 ≤ (T (n + j)).card →
      ∃ x y, x < n + j ∧ y < n + j ∧ T (n + j) = T x ∪ T y)
    (hdis : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    (a b : Fin c) (u u' : Fin v) (j : ℕ)
    (hg : unionGood n m T S a u j) (hg' : unionGood n m T S b u' j)
    (hmin : ∀ j', j' < j → ¬ unionGood n m T S a u j')
    (hmin' : ∀ j', j' < j → ¬ unionGood n m T S b u' j') :
    a = b ∧ u = u' := by
  have hab : a = b := by
    by_contra hne
    obtain ⟨_, hsub, hu, u0, hu0, hu0lt⟩ := hg
    have heq := Finset.card_le_one.1 (hdis a b hne) u0
      (Finset.mem_inter.2 ⟨hsub hu0, hg'.2.1 hu0⟩) u
      (Finset.mem_inter.2 ⟨hsub hu, hg'.2.1 hu⟩)
    exact (ne_of_lt hu0lt) heq
  subst hab
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy u u' with h | h | h
  · exact (union_no_lt T S hin hgate a u u' j hg hg' hmin hmin' h).elim
  · exact h
  · exact (union_no_lt T S hin hgate a u' u j hg' hg hmin' hmin h).elim

lemma union_leaf_min {v c n m : ℕ} (T : ℕ → Finset (Fin v))
    (S : Fin c → Finset (Fin v))
    (hin : ∀ w < n, (T w).card ≤ 1)
    (hout : ∀ a, ∃ w < n + m, T w = S a)
    (a : Fin c) (u : Fin v) (hu : u ∈ S a)
    (hng : ¬ ∃ j, unionGood n m T S a u j) :
    ∀ t ∈ S a, ¬ t < u := by
  intro t ht hlt
  obtain ⟨w, hw, hT⟩ := hout a
  by_cases hwn : w < n
  · have heq := Finset.card_le_one.1 (hin w hwn) t (hT.symm ▸ ht) u (hT.symm ▸ hu)
    exact (ne_of_lt hlt) heq
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    exact hng ⟨j, by omega, by rw [hT], by rw [hT]; exact hu,
      t, by rw [hT]; exact ht, hlt⟩

lemma union_network_count {v c n m : ℕ} (T : ℕ → Finset (Fin v))
    (S : Fin c → Finset (Fin v))
    (hin : ∀ w < n, (T w).card ≤ 1)
    (hgate : ∀ j < m, 2 ≤ (T (n + j)).card →
      ∃ x y, x < n + j ∧ y < n + j ∧ T (n + j) = T x ∪ T y)
    (hdis : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    (hout : ∀ a, ∃ w < n + m, T w = S a) :
    ((Finset.univ : Finset (Fin c)).sigma S).card ≤
      ((Finset.range m).filter fun j => 2 ≤ (T (n + j)).card ∧ ∃ a, T (n + j) ⊆ S a).card + c := by
  classical
  let P := (Finset.univ : Finset (Fin c)).sigma S
  have hQ : (P.filter fun q => ∃ j, unionGood n m T S q.1 q.2 j).card ≤
      ((Finset.range m).filter fun j => 2 ≤ (T (n + j)).card ∧ ∃ a, T (n + j) ⊆ S a).card := by
    refine union_card_le_relation
      (fun q j => unionGood n m T S q.1 q.2 j ∧
        ∀ j', j' < j → ¬ unionGood n m T S q.1 q.2 j') ?_ ?_
    · intro q hq
      obtain ⟨_, hex⟩ := Finset.mem_filter.1 hq
      have hg := Nat.find_spec hex
      refine ⟨Nat.find hex, ?_, hg, fun j' hj' => Nat.find_min hex hj'⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hg.1, ?_, q.1, hg.2.1⟩
      obtain ⟨u0, hu0, hlt⟩ := hg.2.2.2
      have hc : 1 < (T (n + Nat.find hex)).card :=
        Finset.one_lt_card.2 ⟨u0, hu0, q.2, hg.2.2.1, ne_of_lt hlt⟩
      omega
    · intro j _ q hq q' hq'
      obtain ⟨a, u⟩ := q
      obtain ⟨b, u'⟩ := q'
      obtain ⟨_, hg, hmin⟩ := hq
      obtain ⟨_, hg', hmin'⟩ := hq'
      obtain ⟨h1, h2⟩ := union_inj_core T S hin hgate hdis a b u u' j hg hg' hmin hmin'
      subst h1; subst h2; rfl
  have hR : (P.filter fun q => ¬ ∃ j, unionGood n m T S q.1 q.2 j).card ≤ c := by
    suffices hh : (P.filter fun q => ¬ ∃ j, unionGood n m T S q.1 q.2 j).card ≤
        (Finset.univ : Finset (Fin c)).card by simpa using hh
    refine union_card_le_relation (fun q a => q.1 = a) ?_ ?_
    · intro q hq
      exact ⟨q.1, Finset.mem_univ _, rfl⟩
    · intro a ha q hq q' hq'
      obtain ⟨b, u⟩ := q
      obtain ⟨b', u'⟩ := q'
      obtain ⟨hq1, rfl⟩ := hq
      obtain ⟨hq1', rfl⟩ := hq'
      have hu := (Finset.mem_sigma.1 (Finset.mem_filter.1 hq1).1).2
      have hu' := (Finset.mem_sigma.1 (Finset.mem_filter.1 hq1').1).2
      have h1 := union_leaf_min T S hin hout _ u hu (Finset.mem_filter.1 hq1).2
      have h2 := union_leaf_min T S hin hout _ u' hu' (Finset.mem_filter.1 hq1').2
      have huu : u = u' := le_antisymm (not_lt.1 (h1 u' hu')) (not_lt.1 (h2 u hu))
      subst huu; rfl
  change P.card ≤ _
  have hsplit := Finset.card_filter_add_card_filter_not (s := P)
    (fun q => ∃ j, unionGood n m T S q.1 q.2 j)
  omega


lemma union_network_uniform {v c n m q : ℕ} (T : ℕ → Finset (Fin v))
    (S : Fin c → Finset (Fin v))
    (hin : ∀ w < n, (T w).card ≤ 1)
    (hgate : ∀ j < m, 2 ≤ (T (n + j)).card →
      ∃ x y, x < n + j ∧ y < n + j ∧ T (n + j) = T x ∪ T y)
    (hdis : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    (hout : ∀ a, ∃ w < n + m, T w = S a)
    (hcard : ∀ a, (S a).card = q + 1) :
    c * q ≤ ((Finset.range m).filter fun j =>
      2 ≤ (T (n + j)).card ∧ ∃ a, T (n + j) ⊆ S a).card := by
  classical
  have hc := union_network_count T S hin hgate hdis hout
  simp [Finset.card_sigma, hcard] at hc
  rw [Nat.mul_add, Nat.mul_one] at hc
  omega

lemma union_network_one_target {v n m : ℕ} (T : ℕ → Finset (Fin v))
    (S : Finset (Fin v))
    (hin : ∀ w < n, (T w).card ≤ 1)
    (hgate : ∀ j < m, 2 ≤ (T (n + j)).card →
      ∃ x y, x < n + j ∧ y < n + j ∧ T (n + j) = T x ∪ T y)
    (hout : ∃ w < n + m, T w = S) :
    S.card ≤ ((Finset.range m).filter fun j =>
      2 ≤ (T (n + j)).card ∧ T (n + j) ⊆ S).card + 1 := by
  classical
  have hc := union_network_count T (fun _ : Fin 1 => S) hin hgate
    (fun a b hne => (hne (Subsingleton.elim a b)).elim) (fun _ => hout)
  simpa [Finset.card_sigma] using hc

lemma union_network_projected_bound {v N n m q : ℕ} (T : ℕ → Finset (Fin v))
    (P L : Finset (Fin v)) (S : Fin N → Finset (Fin v))
    (hin : ∀ w < n, (T w).card ≤ 1)
    (hgate : ∀ j < m, 2 ≤ (T (n + j)).card →
      ∃ x y, x < n + j ∧ y < n + j ∧ T (n + j) = T x ∪ T y)
    (hdis : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    (hout : ∀ a, ∃ w < n + m, T w ∩ L = S a)
    (hcard : ∀ a, (S a).card = q + 1)
    (hpoint : ∃ w < n + m, T w = P)
    (hPcard : P.card = N) (hPL : Disjoint P L) :
    N * (q + 1) ≤
      ((Finset.range m).filter fun j => 2 ≤ (T (n + j)).card).card + 1 := by
  classical
  let U : ℕ → Finset (Fin v) := fun w => T w ∩ L
  have hUin : ∀ w < n, (U w).card ≤ 1 := by
    intro w hw
    exact le_trans (Finset.card_le_card Finset.inter_subset_left) (hin w hw)
  have hUgate : ∀ j < m, 2 ≤ (U (n + j)).card → ∃ x y,
      x < n + j ∧ y < n + j ∧ U (n + j) = U x ∪ U y := by
    intro j hj hlarge
    have hfull : 2 ≤ (T (n + j)).card :=
      le_trans hlarge (Finset.card_le_card Finset.inter_subset_left)
    obtain ⟨x, y, hx, hy, ht⟩ := hgate j hj hfull
    refine ⟨x, y, hx, hy, ?_⟩
    dsimp [U]
    rw [ht, Finset.union_inter_distrib_right]
  let A := (Finset.range m).filter fun j =>
    2 ≤ (U (n + j)).card ∧ ∃ a, U (n + j) ⊆ S a
  let B := (Finset.range m).filter fun j =>
    2 ≤ (T (n + j)).card ∧ T (n + j) ⊆ P
  have hA : N * q ≤ A.card :=
    union_network_uniform U S hUin hUgate hdis hout hcard
  have hB : N ≤ B.card + 1 := by
    have hb := union_network_one_target T P hin hgate hpoint
    rwa [hPcard] at hb
  have hd : Disjoint A B := by
    refine Finset.disjoint_left.2 ?_
    intro j hjA hjB
    have hlarge := (Finset.mem_filter.1 hjA).2.1
    have hsub := (Finset.mem_filter.1 hjB).2.2
    have hd' : Disjoint (T (n + j)) L := Finset.disjoint_left.2
      (fun a ha haL => Finset.disjoint_left.1 hPL (hsub ha) haL)
    change 2 ≤ (T (n + j) ∩ L).card at hlarge
    rw [Finset.disjoint_iff_inter_eq_empty.1 hd', Finset.card_empty] at hlarge
    omega
  have hbound : A.card + B.card ≤
      ((Finset.range m).filter fun j => 2 ≤ (T (n + j)).card).card := by
    rw [← Finset.card_union_of_disjoint hd]
    apply Finset.card_le_card
    refine Finset.union_subset ?_ ?_
    · intro j hj
      obtain ⟨hjm, hlarge, _⟩ := Finset.mem_filter.1 hj
      exact Finset.mem_filter.2 ⟨hjm,
        le_trans hlarge (Finset.card_le_card Finset.inter_subset_left)⟩
    · intro j hj
      obtain ⟨hjm, hlarge, _⟩ := Finset.mem_filter.1 hj
      exact Finset.mem_filter.2 ⟨hjm, hlarge⟩
  rw [Nat.mul_add, Nat.mul_one]
  omega

namespace OrCircuitBridge

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

lemma T_input_card {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (T C w : Finset (Fin n)).card ≤ 1 := by
  rw [T_input C w hw]
  simp

lemma support_network {n : ℕ} (C : Circuit) (fam : Finset (Finset (Fin n)))
    (hC : IsOrCircuitFor n C fam) :
    ∃ U : ℕ → Finset (Fin n),
      (∀ w < n, (U w).card ≤ 1) ∧
      (∀ j < C.gates.length, 2 ≤ (U (n + j)).card →
        ∃ a b, a < n + j ∧ b < n + j ∧ U (n + j) = U a ∪ U b) ∧
      (∀ s ∈ fam, ∃ w < n + C.gates.length, U w = s) := by
  refine ⟨T C, T_input_card C, ?_, ?_⟩
  · intro j hj _
    exact T_gate C hC.1 j hj
  · intro s hs
    obtain ⟨w, hw, hc⟩ := hC.2 s hs
    exact ⟨w, hw, T_computes C w s hc⟩

lemma has_or_cost_network {n k : ℕ} (fam : Finset (Finset (Fin n)))
    (hcost : HasOrCost n fam k) :
    ∃ m ≤ k, ∃ U : ℕ → Finset (Fin n),
      (∀ w < n, (U w).card ≤ 1) ∧
      (∀ j < m, 2 ≤ (U (n + j)).card →
        ∃ a b, a < n + j ∧ b < n + j ∧ U (n + j) = U a ∪ U b) ∧
      (∀ s ∈ fam, ∃ w < n + m, U w = s) := by
  obtain ⟨C, hc, hk⟩ := hcost
  exact ⟨C.gates.length, hk, support_network C fam hc⟩

end OrCircuitBridge

namespace OrCircuitBridge

open PEqualNP.SharedBlockCost

lemma has_or_cost_projected {n N k q : ℕ} (fam : Finset (Finset (Fin n)))
    (P L : Finset (Fin n)) (S : Fin N → Finset (Fin n))
    (hcost : HasOrCost n fam k) (hpoint : P ∈ fam)
    (hout : ∀ a, ∃ s ∈ fam, s ∩ L = S a)
    (hdis : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    (hcard : ∀ a, (S a).card = q + 1)
    (hPcard : P.card = N) (hPL : Disjoint P L) :
    N * (q + 1) ≤ k + 1 := by
  classical
  obtain ⟨m, hmk, U, hin, hgate, hfamily⟩ := has_or_cost_network fam hcost
  have htargets : ∀ a, ∃ w < n + m, U w ∩ L = S a := by
    intro a
    obtain ⟨s, hs, hproj⟩ := hout a
    obtain ⟨w, hw, heq⟩ := hfamily s hs
    exact ⟨w, hw, heq ▸ hproj⟩
  have hb := PEqualNP.Outside.L_meta_2583.union_network_projected_bound
    U P L S hin hgate hdis htargets hcard (hfamily P hpoint) hPcard hPL
  have hle : ((Finset.range m).filter fun j => 2 ≤ (U (n + j)).card).card ≤ m := by
    exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
  omega

lemma has_or_cost_with_clauses {n N k q : ℕ} (fam : Finset (Finset (Fin n)))
    (P L : Finset (Fin n)) (S : Fin N → Finset (Fin n))
    (hcost : HasOrCost n fam k) (hpoint : P ∈ fam)
    (hout : ∀ a, ∃ s ∈ fam, s ∩ L = S a)
    (hdis : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    (hcard : ∀ a, (S a).card = q + 1)
    (hPcard : P.card = N) (hPL : Disjoint P L)
    (hclauses : N + 1 ≤ fam.card) :
    N * (q + 2) ≤ k + fam.card := by
  have hb := has_or_cost_projected fam P L S hcost hpoint hout hdis hcard hPcard hPL
  simp only [Nat.mul_add, Nat.mul_one] at hb
  rw [Nat.mul_add, Nat.mul_two]
  omega

end OrCircuitBridge

namespace PlaneCnf

open Finset
open PEqualNP.Outside.L_meta_2583

variable {v : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]

lemma neighbor_not_point (P : Finset (Fin v))
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    {u w : Fin v} (hu : u ∈ P) (hw : w ∈ G.neighborFinset u) : w ∉ P := by
  intro hwP
  exact hP u hu w hwP (G.mem_neighborFinset u w |>.mp hw)

lemma point_cover_minimal (P W : Finset (Fin v))
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hnonempty : ∀ u ∈ P, (G.neighborFinset u).Nonempty)
    (hW : Cnf.Covers G W) (hWP : W ⊆ P) : P ⊆ W := by
  intro u hu
  obtain ⟨w, hw⟩ := hnonempty u hu
  rcases hW u w (G.mem_neighborFinset u w |>.mp hw) with h | h
  · exact h
  · exact (neighbor_not_point G P hP hu hw (hWP h)).elim

lemma neighbor_outside_neighbor
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    {u w : Fin v} (huw : u ≠ w) (hw : 2 ≤ (G.neighborFinset w).card) :
    ∃ z, G.Adj w z ∧ ¬ G.Adj u z := by
  by_contra hn
  push Not at hn
  have hsub : G.neighborFinset w ⊆
      (Finset.univ.filter fun z => G.Adj u z ∧ G.Adj w z) := by
    intro z hz
    have hwz := G.mem_neighborFinset w z |>.mp hz
    exact mem_filter.mpr ⟨mem_univ _, hn z hwz, hwz⟩
  have hc := Finset.card_le_card hsub
  have hbound := hfour u w huw
  omega

lemma swap_cover_minimal (P W : Finset (Fin v))
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hdegree : ∀ u ∈ P, 2 ≤ (G.neighborFinset u).card)
    {u : Fin v} (hu : u ∈ P) (hW : Cnf.Covers G W)
    (hsub : W ⊆ P.erase u ∪ G.neighborFinset u) :
    P.erase u ∪ G.neighborFinset u ⊆ W := by
  intro w hw
  rcases mem_union.mp hw with hw | hw
  · obtain ⟨hwu, hwP⟩ := mem_erase.mp hw
    obtain ⟨z, hwz, huz⟩ := neighbor_outside_neighbor G hfour (Ne.symm hwu)
      (hdegree w hwP)
    rcases hW w z hwz with hwW | hzW
    · exact hwW
    · have hzP : z ∉ P := neighbor_not_point G P hP hwP
        (G.mem_neighborFinset w z |>.mpr hwz)
      rcases mem_union.mp (hsub hzW) with hz | hz
      · exact (hzP (mem_of_mem_erase hz)).elim
      · exact (huz (G.mem_neighborFinset u z |>.mp hz)).elim
  · exact Cnf.neighbor_subset_clause G P W u hW hsub hw

lemma cnf_required_clauses (P : Finset (Fin v))
    (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hdegree : ∀ u ∈ P, 2 ≤ (G.neighborFinset u).card)
    (F : Finset (Finset (Fin v)))
    (hF : ∀ x : Fin v → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) ↔
      ∃ u w, G.Adj u w ∧ x u = true ∧ x w = true) :
    P ∈ F ∧ ∀ u ∈ P, P.erase u ∪ G.neighborFinset u ∈ F := by
  obtain ⟨hFc, hcomplete⟩ := Cnf.cnf_clause_properties G F hF
  constructor
  · obtain ⟨W, hWF, hWP⟩ := hcomplete P hcover
    have hPW : P ⊆ W := point_cover_minimal G P W hP
      (fun u hu => card_pos.mp (by have := hdegree u hu; omega)) (hFc W hWF) hWP
    exact (Finset.Subset.antisymm hWP hPW) ▸ hWF
  · intro u hu
    obtain ⟨W, hWF, hWK⟩ := hcomplete _ (Cnf.cover_swap G P hcover u)
    have hKW := swap_cover_minimal G P W hP hfour hdegree hu (hFc W hWF) hWK
    exact (Finset.Subset.antisymm hWK hKW) ▸ hWF

lemma swap_injective (P : Finset (Fin v))
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hdegree : ∀ u ∈ P, 2 ≤ (G.neighborFinset u).card) :
    Set.InjOn (fun u => P.erase u ∪ G.neighborFinset u) (P : Set (Fin v)) := by
  intro u hu w hw heq
  change P.erase u ∪ G.neighborFinset u = P.erase w ∪ G.neighborFinset w at heq
  by_contra huw
  have hsub : G.neighborFinset u ⊆
      (Finset.univ.filter fun z => G.Adj u z ∧ G.Adj w z) := by
    intro z hz
    have hzP := neighbor_not_point G P hP hu hz
    have hzK : z ∈ P.erase w ∪ G.neighborFinset w := by
      rw [← heq]
      exact mem_union_right _ hz
    have hzw : z ∈ G.neighborFinset w := by
      rcases mem_union.mp hzK with hzE | hzW
      · exact (hzP (mem_of_mem_erase hzE)).elim
      · exact hzW
    exact mem_filter.mpr ⟨mem_univ _, G.mem_neighborFinset u z |>.mp hz,
      G.mem_neighborFinset w z |>.mp hzw⟩
  have hc := card_le_card hsub
  have hb := hfour u w huw
  have hd := hdegree u hu
  omega

lemma cnf_clause_card (P : Finset (Fin v))
    (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hdegree : ∀ u ∈ P, 2 ≤ (G.neighborFinset u).card)
    (F : Finset (Finset (Fin v)))
    (hF : ∀ x : Fin v → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) ↔
      ∃ u w, G.Adj u w ∧ x u = true ∧ x w = true) :
    P.card + 1 ≤ F.card := by
  classical
  obtain ⟨hPF, hKF⟩ := cnf_required_clauses G P hcover hP hfour hdegree F hF
  let K : Fin v → Finset (Fin v) := fun u => P.erase u ∪ G.neighborFinset u
  have hnot : P ∉ P.image K := by
    rintro h
    obtain ⟨u, hu, heq⟩ := mem_image.mp h
    have huK : u ∈ K u := heq.symm ▸ hu
    exact Cnf.not_mem_swap G P u huK
  have hsub : insert P (P.image K) ⊆ F := by
    intro W hW
    rcases mem_insert.mp hW with rfl | hW
    · exact hPF
    · obtain ⟨u, hu, rfl⟩ := mem_image.mp hW
      exact hKF u hu
  have hc := card_le_card hsub
  rw [card_insert_of_notMem hnot, card_image_of_injOn (swap_injective G P hP hfour hdegree)] at hc
  exact hc

lemma shared_cnf_size_lower_bound (P : Finset (Fin v)) (q k : ℕ) (hq : 1 ≤ q)
    (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hdegree : ∀ u ∈ P, (G.neighborFinset u).card = q + 1)
    (F : Finset (Finset (Fin v)))
    (hF : ∀ x : Fin v → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) ↔
      ∃ u w, G.Adj u w ∧ x u = true ∧ x w = true)
    (hcost : PEqualNP.SharedBlockCost.HasOrCost v F k) :
    P.card * (q + 2) ≤ k + F.card := by
  classical
  have hdegree2 : ∀ u ∈ P, 2 ≤ (G.neighborFinset u).card := by
    intro u hu
    rw [hdegree u hu]
    omega
  obtain ⟨hPF, hKF⟩ := cnf_required_clauses G P hcover hP hfour hdegree2 F hF
  let e : Fin P.card ≃o P := P.orderIsoOfFin rfl
  let S : Fin P.card → Finset (Fin v) := fun a => G.neighborFinset (e a).val
  let L := Finset.univ \ P
  have hout : ∀ a, ∃ W ∈ F, W ∩ L = S a := by
    intro a
    refine ⟨P.erase (e a).val ∪ G.neighborFinset (e a).val, hKF _ (e a).property, ?_⟩
    ext z
    simp only [mem_inter, mem_union, L, mem_sdiff, mem_univ, true_and, S]
    constructor
    · rintro ⟨hz | hz, hzn⟩
      · exact (hzn (mem_of_mem_erase hz)).elim
      · exact hz
    · intro hz
      exact ⟨Or.inr hz, neighbor_not_point G P hP (e a).property hz⟩
  have hdis : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1 := by
    intro a b hab
    have he : (e a).val ≠ (e b).val := by
      intro heq
      exact hab (e.injective (Subtype.ext heq))
    have hh := hfour (e a).val (e b).val he
    have hs : S a ∩ S b =
        Finset.univ.filter (fun z => G.Adj (e a).val z ∧ G.Adj (e b).val z) := by
      ext z
      simp [S]
    rwa [hs]
  have hcard : ∀ a, (S a).card = q + 1 := fun a => hdegree _ (e a).property
  have hPL : Disjoint P L := by
    refine Finset.disjoint_left.mpr ?_
    intro z hz hzL
    exact (mem_sdiff.mp hzL).2 hz
  exact OrCircuitBridge.has_or_cost_with_clauses F P L S hcost hPF hout hdis hcard rfl hPL
    (cnf_clause_card G P hcover hP hfour hdegree2 F hF)

end PlaneCnf

end PEqualNP.Outside.L_meta_2583
