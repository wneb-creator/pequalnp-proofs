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

namespace OrCircuitBridge

open PEqualNP.SharedBlockCost

lemma nonuniform_projected_count {v c n m : ℕ} (T : ℕ → Finset (Fin v))
    (P L : Finset (Fin v)) (S : Fin c → Finset (Fin v))
    (hin : ∀ w < n, (T w).card ≤ 1)
    (hgate : ∀ j < m, 2 ≤ (T (n + j)).card →
      ∃ x y, x < n + j ∧ y < n + j ∧ T (n + j) = T x ∪ T y)
    (hdis : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    (hout : ∀ a, ∃ w < n + m, T w ∩ L = S a)
    (hpoint : ∃ w < n + m, T w = P)
    (hPcard : c ≤ P.card) (hPL : Disjoint P L) :
    ((Finset.univ : Finset (Fin c)).sigma S).card ≤
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
  have hA : ((Finset.univ : Finset (Fin c)).sigma S).card ≤ A.card + c :=
    PEqualNP.Outside.L_meta_2583.union_network_count U S hUin hUgate hdis hout
  have hB : c ≤ B.card + 1 :=
    le_trans hPcard (PEqualNP.Outside.L_meta_2583.union_network_one_target T P hin hgate hpoint)
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
  omega

lemma has_or_cost_nonuniform {n c k : ℕ} (fam : Finset (Finset (Fin n)))
    (P L : Finset (Fin n)) (S : Fin c → Finset (Fin n))
    (hcost : HasOrCost n fam k) (hpoint : P ∈ fam)
    (hout : ∀ a, ∃ s ∈ fam, s ∩ L = S a)
    (hdis : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    (hPcard : c ≤ P.card) (hPL : Disjoint P L) :
    ((Finset.univ : Finset (Fin c)).sigma S).card ≤ k + 1 := by
  classical
  obtain ⟨m, hmk, U, hin, hgate, hfamily⟩ := has_or_cost_network fam hcost
  have htargets : ∀ a, ∃ w < n + m, U w ∩ L = S a := by
    intro a
    obtain ⟨s, hs, hproj⟩ := hout a
    obtain ⟨w, hw, heq⟩ := hfamily s hs
    exact ⟨w, hw, heq ▸ hproj⟩
  have hb := nonuniform_projected_count U P L S hin hgate hdis htargets
    (hfamily P hpoint) hPcard hPL
  have hle : ((Finset.range m).filter fun j => 2 ≤ (U (n + j)).card).card ≤ m := by
    exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
  omega

end OrCircuitBridge

namespace RelativeCnf

open Finset
open PEqualNP.Outside.L_meta_2583

variable {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj]

lemma relative_clause_properties (F : Finset (Finset (Fin n)))
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ u v, H.Adj u v →
      ∀ W ∈ F, ∃ a ∈ W, a = u ∨ a = v) :
    (∀ W ∈ F, Cnf.Covers H W) ∧
    (∀ U, Cnf.Covers G U → ∃ W ∈ F, W ⊆ U) := by
  classical
  constructor
  · intro W hWF u v huv
    obtain ⟨a, haW, ha⟩ := haccept u v huv W hWF
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
    obtain ⟨u, v, huv, hu, hv⟩ := hsafe x hx
    have huU : u ∉ U := by simpa [x] using hu
    have hvU : v ∉ U := by simpa [x] using hv
    exact (hU u v huv).elim huU hvU

lemma relative_neighbor_not_point (P : Finset (Fin n))
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) {u w : Fin n} (hu : u ∈ P)
    (hw : w ∈ H.neighborFinset u) : w ∉ P := by
  intro hwP
  exact hP u hu w hwP (hHG (H.mem_neighborFinset u w |>.mp hw))

lemma relative_base_clause (P A : Finset (Fin n))
    (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) (hAP : A ⊆ P)
    (hactive : ∀ u ∈ A, (H.neighborFinset u).Nonempty)
    (F : Finset (Finset (Fin n)))
    (hFc : ∀ W ∈ F, Cnf.Covers H W)
    (hcomplete : ∀ U, Cnf.Covers G U → ∃ W ∈ F, W ⊆ U) :
    ∃ W ∈ F, W ⊆ P ∧ A ⊆ W := by
  obtain ⟨W, hWF, hWP⟩ := hcomplete P hcover
  refine ⟨W, hWF, hWP, ?_⟩
  intro u hu
  obtain ⟨w, hw⟩ := hactive u hu
  rcases hFc W hWF u w (H.mem_neighborFinset u w |>.mp hw) with huW | hwW
  · exact huW
  · exact (relative_neighbor_not_point G H P hP hHG (hAP hu) hw (hWP hwW)).elim

lemma relative_point_clause (P : Finset (Fin n))
    (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) {u : Fin n} (hu : u ∈ P)
    (F : Finset (Finset (Fin n)))
    (hFc : ∀ W ∈ F, Cnf.Covers H W)
    (hcomplete : ∀ U, Cnf.Covers G U → ∃ W ∈ F, W ⊆ U) :
    ∃ W ∈ F, W ⊆ P.erase u ∪ G.neighborFinset u ∧
      H.neighborFinset u ⊆ W \ P ∧ W \ P ⊆ G.neighborFinset u := by
  obtain ⟨W, hWF, hWK⟩ := hcomplete _ (Cnf.cover_swap G P hcover u)
  refine ⟨W, hWF, hWK, ?_, ?_⟩
  · intro w hw
    have hwP := relative_neighbor_not_point G H P hP hHG hu hw
    have huW : u ∉ W := fun h => Cnf.not_mem_swap G P u (hWK h)
    have hwW : w ∈ W := (hFc W hWF u w (H.mem_neighborFinset u w |>.mp hw)).resolve_left huW
    exact mem_sdiff.mpr ⟨hwW, hwP⟩
  · intro w hw
    obtain ⟨hwW, hwP⟩ := mem_sdiff.mp hw
    rcases mem_union.mp (hWK hwW) with hwE | hwN
    · exact (hwP (mem_of_mem_erase hwE)).elim
    · exact hwN

lemma relative_projection_inter (hfour : PEqualNP.TopForm.NoFourCycle G)
    {u v : Fin n} (huv : u ≠ v) {S T : Finset (Fin n)}
    (hS : S ⊆ G.neighborFinset u) (hT : T ⊆ G.neighborFinset v) :
    (S ∩ T).card ≤ 1 := by
  apply le_trans (Finset.card_le_card ?_) (hfour u v huv)
  intro w hw
  obtain ⟨hwS, hwT⟩ := mem_inter.mp hw
  exact mem_filter.mpr ⟨mem_univ _, G.mem_neighborFinset u w |>.mp (hS hwS),
    G.mem_neighborFinset v w |>.mp (hT hwT)⟩

lemma active_points_cover (P : Finset (Fin n)) (hcover : Cnf.Covers G P)
    (hHG : H ≤ G) :
    Cnf.Covers H (P.filter fun u => (H.neighborFinset u).Nonempty) := by
  intro u v huv
  rcases hcover u v (hHG huv) with huP | hvP
  · exact Or.inl (mem_filter.mpr ⟨huP, v, H.mem_neighborFinset u v |>.mpr huv⟩)
  · exact Or.inr (mem_filter.mpr ⟨hvP, u, H.mem_neighborFinset v u |>.mpr huv.symm⟩)

lemma relative_shared_cnf_edge_bound (P : Finset (Fin n))
    (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (F : Finset (Finset (Fin n))) (k : ℕ)
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ u v, H.Adj u v →
      ∀ W ∈ F, ∃ a ∈ W, a = u ∨ a = v)
    (hcost : PEqualNP.SharedBlockCost.HasOrCost n F k) :
    H.edgeFinset.card ≤ k + 1 := by
  classical
  obtain ⟨hFc, hcomplete⟩ := relative_clause_properties G H F hsafe haccept
  let A := P.filter fun u => (H.neighborFinset u).Nonempty
  have hAP : A ⊆ P := filter_subset _ _
  have hactive : ∀ u ∈ A, (H.neighborFinset u).Nonempty :=
    fun _ hu => (mem_filter.mp hu).2
  obtain ⟨W₀, hW₀F, hW₀P, hAW₀⟩ :=
    relative_base_clause G H P A hcover hP hHG hAP hactive F hFc hcomplete
  let e : Fin A.card ≃o A := A.orderIsoOfFin rfl
  have hchoices : ∀ a : Fin A.card, ∃ W ∈ F,
      W ⊆ P.erase (e a).val ∪ G.neighborFinset (e a).val ∧
      H.neighborFinset (e a).val ⊆ W \ P ∧
      W \ P ⊆ G.neighborFinset (e a).val := by
    intro a
    exact relative_point_clause G H P hcover hP hHG (hAP (e a).property) F hFc hcomplete
  choose K hKF hKswap hKlow hKhigh using hchoices
  let S : Fin A.card → Finset (Fin n) := fun a => K a \ P
  let L := univ \ P
  have hout : ∀ a, ∃ W ∈ F, W ∩ L = S a := by
    intro a
    refine ⟨K a, hKF a, ?_⟩
    ext z
    simp [S, L]
  have hdis : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1 := by
    intro a b hab
    have he : (e a).val ≠ (e b).val := by
      intro heq
      exact hab (e.injective (Subtype.ext heq))
    exact relative_projection_inter G hfour he (hKhigh a) (hKhigh b)
  have hW₀L : Disjoint W₀ L := by
    apply Finset.disjoint_left.mpr
    intro z hz hzL
    exact (mem_sdiff.mp hzL).2 (hW₀P hz)
  have hb := OrCircuitBridge.has_or_cost_nonuniform F W₀ L S hcost hW₀F hout hdis
    (card_le_card hAW₀) hW₀L
  have hsum : (∑ u ∈ A, (H.neighborFinset u).card) =
      ∑ a : Fin A.card, (H.neighborFinset (e a).val).card := by
    refine Finset.sum_bij (fun u hu => e.symm ⟨u, hu⟩)
      (fun _ _ => mem_univ _) ?_ ?_ ?_
    · intro u hu v hv heq
      have hh := e.symm.injective heq
      exact congrArg Subtype.val hh
    · intro a ha
      exact ⟨(e a).val, (e a).property, by simp⟩
    · intro u hu
      rw [e.apply_symm_apply]
  have hedge := Cnf.edges_le_cover_degrees H A (active_points_cover G H P hcover hHG)
  have hsize : H.edgeFinset.card ≤ (univ.sigma S).card := by
    rw [Finset.card_sigma]
    rw [hsum] at hedge
    apply le_trans hedge
    apply Finset.sum_le_sum
    intro a ha
    exact card_le_card (hKlow a)
  exact le_trans hsize hb

lemma relative_shared_cnf_edge_bound_semantic (P : Finset (Fin n))
    (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (F : Finset (Finset (Fin n))) (k : ℕ)
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ x : Fin n → Bool,
      (∃ u v, H.Adj u v ∧ x u = true ∧ x v = true) →
      ∀ W ∈ F, ∃ u ∈ W, x u = true)
    (hcost : PEqualNP.SharedBlockCost.HasOrCost n F k) :
    H.edgeFinset.card ≤ k + 1 := by
  apply relative_shared_cnf_edge_bound G H P hcover hP hHG hfour F k hsafe ?_ hcost
  intro u v huv W hWF
  let x : Fin n → Bool := fun a => decide (a = u ∨ a = v)
  have hx : ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true :=
    ⟨u, v, huv, by simp [x], by simp [x]⟩
  obtain ⟨a, haW, ha⟩ := haccept x hx W hWF
  exact ⟨a, haW, by simpa [x] using ha⟩

end RelativeCnf

namespace RelativeCnf

open Finset
open PEqualNP.Outside.L_meta_2583

variable {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj]

lemma cover_from_clause_projections (A P : Finset (Fin n))
    (hA : Cnf.Covers H A) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (K : Fin n → Finset (Fin n))
    (hlow : ∀ u ∈ A, H.neighborFinset u ⊆ K u \ P)
    (hhigh : ∀ u ∈ A, K u \ P ⊆ G.neighborFinset u) :
    ∃ T : Finset (Fin n), Cnf.Covers H T ∧ T.card ≤ (A.image K).card := by
  classical
  let R := A.image K
  have hcentre : ∀ W ∈ R, ∃ c : Fin n,
      ∀ u ∈ A, K u = W → ∀ v, H.Adj u v → u = c ∨ v = c := by
    intro W hWR
    obtain ⟨u₀, hu₀, hu₀W⟩ := mem_image.mp hWR
    by_cases hsmall : (W \ P).card ≤ 1
    · by_cases hnonempty : (W \ P).Nonempty
      · obtain ⟨c, hcW⟩ := hnonempty
        refine ⟨c, ?_⟩
        intro u hu huW v huv
        right
        apply card_le_one.mp hsmall
        · rw [← huW]
          exact hlow u hu (H.mem_neighborFinset u v |>.mpr huv)
        · exact hcW
      · refine ⟨u₀, ?_⟩
        intro u hu huW v huv
        exfalso
        apply hnonempty
        refine ⟨v, ?_⟩
        rw [← huW]
        exact hlow u hu (H.mem_neighborFinset u v |>.mpr huv)
    · refine ⟨u₀, ?_⟩
      intro u hu huW v huv
      left
      by_contra hne
      have hsub : W \ P ⊆ univ.filter (fun w => G.Adj u w ∧ G.Adj u₀ w) := by
        intro w hw
        apply mem_filter.mpr
        refine ⟨mem_univ _, ?_, ?_⟩
        · apply G.mem_neighborFinset u w |>.mp
          apply hhigh u hu
          rwa [huW]
        · apply G.mem_neighborFinset u₀ w |>.mp
          apply hhigh u₀ hu₀
          rwa [hu₀W]
      exact hsmall (le_trans (card_le_card hsub) (hfour u u₀ hne))
  let c : {W // W ∈ R} → Fin n := fun W => Classical.choose (hcentre W.val W.property)
  let T := R.attach.image c
  refine ⟨T, ?_, ?_⟩
  · intro u v huv
    have hcover : ∀ a ∈ A, ∀ b, H.Adj a b → a ∈ T ∨ b ∈ T := by
      intro a ha b hab
      let W : {W // W ∈ R} := ⟨K a, mem_image.mpr ⟨a, ha, rfl⟩⟩
      have hc : c W ∈ T := mem_image.mpr ⟨W, mem_attach R W, rfl⟩
      have hpair := Classical.choose_spec (hcentre W.val W.property) a ha rfl b hab
      change a = c W ∨ b = c W at hpair
      rcases hpair with heq | heq
      · exact Or.inl (heq ▸ hc)
      · exact Or.inr (heq ▸ hc)
    rcases hA u v huv with hu | hv
    · exact hcover u hu v huv
    · exact Or.symm (hcover v hv u huv.symm)
  · calc T.card ≤ R.attach.card := card_image_le
      _ = R.card := card_attach

lemma relative_shared_cnf_cover_bound (P : Finset (Fin n))
    (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (F : Finset (Finset (Fin n))) (k : ℕ)
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ u v, H.Adj u v →
      ∀ W ∈ F, ∃ a ∈ W, a = u ∨ a = v)
    (hcost : PEqualNP.SharedBlockCost.HasOrCost n F k) :
    ∃ T : Finset (Fin n), Cnf.Covers H T ∧ H.edgeFinset.card + T.card ≤ k + F.card := by
  classical
  obtain ⟨hFc, hcomplete⟩ := relative_clause_properties G H F hsafe haccept
  let A := P.filter fun u => (H.neighborFinset u).Nonempty
  have hAP : A ⊆ P := filter_subset _ _
  have hactive : ∀ u ∈ A, (H.neighborFinset u).Nonempty :=
    fun _ hu => (mem_filter.mp hu).2
  obtain ⟨W₀, hW₀F, hW₀P, hAW₀⟩ :=
    relative_base_clause G H P A hcover hP hHG hAP hactive F hFc hcomplete
  have hchoices : ∀ u : Fin n, ∃ W ∈ F, W ⊆ P.erase u ∪ G.neighborFinset u := by
    intro u
    exact hcomplete _ (Cnf.cover_swap G P hcover u)
  choose K hKF hKsub using hchoices
  have hlow : ∀ u ∈ A, H.neighborFinset u ⊆ K u \ P := by
    intro u hu w hw
    have huK : u ∉ K u := fun h => Cnf.not_mem_swap G P u (hKsub u h)
    have hwK : w ∈ K u :=
      (hFc (K u) (hKF u) u w (H.mem_neighborFinset u w |>.mp hw)).resolve_left huK
    exact mem_sdiff.mpr ⟨hwK, relative_neighbor_not_point G H P hP hHG (hAP hu) hw⟩
  have hhigh : ∀ u ∈ A, K u \ P ⊆ G.neighborFinset u := by
    intro u hu w hw
    obtain ⟨hwK, hwP⟩ := mem_sdiff.mp hw
    rcases mem_union.mp (hKsub u hwK) with hwE | hwN
    · exact (hwP (mem_of_mem_erase hwE)).elim
    · exact hwN
  have hnot : W₀ ∉ A.image K := by
    rintro h
    obtain ⟨u, hu, huW₀⟩ := mem_image.mp h
    obtain ⟨w, hw⟩ := hactive u hu
    obtain ⟨hwK, hwP⟩ := mem_sdiff.mp (hlow u hu hw)
    rw [huW₀] at hwK
    exact hwP (hW₀P hwK)
  have hsub : insert W₀ (A.image K) ⊆ F := by
    intro W hW
    rcases mem_insert.mp hW with rfl | hW
    · exact hW₀F
    · obtain ⟨u, hu, rfl⟩ := mem_image.mp hW
      exact hKF u
  obtain ⟨T, hT, hTcard⟩ := cover_from_clause_projections G H A P
    (active_points_cover G H P hcover hHG) hfour K hlow hhigh
  have hFcard := card_le_card hsub
  rw [card_insert_of_notMem hnot] at hFcard
  have hedge := relative_shared_cnf_edge_bound G H P hcover hP hHG hfour F k hsafe haccept hcost
  refine ⟨T, hT, ?_⟩
  omega

lemma relative_shared_cnf_cover_bound_semantic (P : Finset (Fin n))
    (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (F : Finset (Finset (Fin n))) (k : ℕ)
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ x : Fin n → Bool,
      (∃ u v, H.Adj u v ∧ x u = true ∧ x v = true) →
      ∀ W ∈ F, ∃ u ∈ W, x u = true)
    (hcost : PEqualNP.SharedBlockCost.HasOrCost n F k) :
    ∃ T : Finset (Fin n), Cnf.Covers H T ∧ H.edgeFinset.card + T.card ≤ k + F.card := by
  apply relative_shared_cnf_cover_bound G H P hcover hP hHG hfour F k hsafe ?_ hcost
  intro u v huv W hWF
  let x : Fin n → Bool := fun a => decide (a = u ∨ a = v)
  have hx : ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true :=
    ⟨u, v, huv, by simp [x], by simp [x]⟩
  obtain ⟨a, haW, ha⟩ := haccept x hx W hWF
  exact ⟨a, haW, by simpa [x] using ha⟩

end RelativeCnf

namespace MatchingSurplus

open Finset

variable {r : ℕ} (I : Fin r → Fin r → Prop) [DecidableRel I]

def Independent (S : Finset (Bool × Fin r)) : Prop :=
  ∀ a b, (false, a) ∈ S → (true, b) ∈ S → ¬ I a b

def points : Finset (Bool × Fin r) := univ.image fun a => (false, a)

def lines : Finset (Bool × Fin r) := univ.image fun a => (true, a)

def witness (i : Fin r) : Finset (Bool × Fin r) :=
  insert (true, i) ((univ.filter fun a => ¬ I a i).image fun a => (false, a))

lemma mem_points (a : Fin r) : (false, a) ∈ points (r := r) := by simp [points]

lemma mem_lines (a : Fin r) : (true, a) ∈ lines (r := r) := by simp [lines]

lemma mem_witness_point (a i : Fin r) : (false, a) ∈ witness I i ↔ ¬ I a i := by
  simp [witness]

lemma mem_witness_line (a i : Fin r) : (true, a) ∈ witness I i ↔ a = i := by
  simp [witness]

lemma points_independent : Independent I (points (r := r)) := by
  intro a b ha hb
  simp [points] at hb

lemma lines_independent : Independent I (lines (r := r)) := by
  intro a b ha hb
  simp [lines] at ha

lemma witness_independent (i : Fin r) : Independent I (witness I i) := by
  intro a b ha hb
  have hbi := (mem_witness_line I b i).mp hb
  subst b
  exact (mem_witness_point I a i).mp ha

lemma clause_count_strict (hr : 3 ≤ r)
    (hdiag : ∀ i, I i i)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (F : Finset (Finset (Bool × Fin r)))
    (hcover : ∀ W ∈ F, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W)
    (hmiss : ∀ S, Independent I S → ∃ W ∈ F, Disjoint W S) :
    r + 2 ≤ F.card := by
  classical
  let B : Option (Fin r) → Finset (Bool × Fin r)
    | none => points
    | some i => witness I i
  have hB : ∀ a, Independent I (B a) := by
    intro a
    cases a with
    | none => exact points_independent I
    | some i => exact witness_independent I i
  have hchoice : ∀ a, ∃ W ∈ F, Disjoint W (B a) := fun a => hmiss _ (hB a)
  choose K hKF hKB using hchoice
  have hline : ∀ i, (true, i) ∈ K none := by
    intro i
    rcases hcover _ (hKF none) i with hp | hl
    · exact (Finset.disjoint_left.mp (hKB none) hp (mem_points i)).elim
    · exact hl
  have hpoint : ∀ i, (false, i) ∈ K (some i) := by
    intro i
    rcases hcover _ (hKF (some i)) i with hp | hl
    · exact hp
    · exact (Finset.disjoint_left.mp (hKB (some i)) hl
        ((mem_witness_line I i i).mpr rfl)).elim
  have hneqnone : ∀ i, K none ≠ K (some i) := by
    intro i heq
    have hp := hpoint i
    rw [← heq] at hp
    exact Finset.disjoint_left.mp (hKB none) hp (mem_points i)
  have hinj : Function.Injective K := by
    intro a b heq
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some j => exact (hneqnone j heq).elim
    | some i =>
      cases b with
      | none => exact (hneqnone i heq.symm).elim
      | some j =>
        congr 1
        by_contra hij
        have hijI : I i j := by
          by_contra hn
          have hp := hpoint i
          rw [heq] at hp
          exact Finset.disjoint_left.mp (hKB (some j)) hp
            ((mem_witness_point I i j).mpr hn)
        have hjiI : I j i := by
          by_contra hn
          have hp := hpoint j
          rw [← heq] at hp
          exact Finset.disjoint_left.mp (hKB (some i)) hp
            ((mem_witness_point I j i).mpr hn)
        exact hfour i j i j hij hij ⟨hdiag i, hijI, hjiI, hdiag j⟩
  have hsub : univ.image K ⊆ F := by
    intro W hW
    obtain ⟨a, _, rfl⟩ := mem_image.mp hW
    exact hKF a
  have hcard : (univ.image K).card = r + 1 := by
    rw [card_image_of_injective _ hinj]
    simp
  by_contra hgoal
  have hupper : F.card ≤ r + 1 := by omega
  have heq : univ.image K = F := eq_of_subset_of_card_le hsub (by omega)
  have hexhaust : ∀ W ∈ F, ∃ a, K a = W := by
    intro W hW
    rw [← heq] at hW
    obtain ⟨a, _, ha⟩ := mem_image.mp hW
    exact ⟨a, ha⟩
  obtain ⟨Wp, hWpF, hWp⟩ := hmiss (lines (r := r)) (lines_independent I)
  obtain ⟨a, ha⟩ := hexhaust Wp hWpF
  have hanone : a ≠ none := by
    intro hnone
    subst a
    let i : Fin r := ⟨0, by omega⟩
    have hl := hline i
    rw [ha] at hl
    exact Finset.disjoint_left.mp hWp hl (mem_lines i)
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hanone
  subst a
  have hallpoints : ∀ i, (false, i) ∈ K (some j) := by
    intro i
    rcases hcover _ (hKF (some j)) i with hp | hl
    · exact hp
    · rw [ha] at hl
      exact (Finset.disjoint_left.mp hWp hl (mem_lines i)).elim
  have huniversal : ∀ i, I i j := by
    intro i
    by_contra hn
    exact Finset.disjoint_left.mp (hKB (some j)) (hallpoints i)
      ((mem_witness_point I i j).mpr hn)
  have hsparse : ∀ i, i ≠ j → ∀ a, a ≠ i → ¬ I a i := by
    intro i hij a hai haiI
    exact hfour i a i j (Ne.symm hai) hij ⟨hdiag i, huniversal i, haiI, huniversal a⟩
  have hrestlines : ∀ i, i ≠ j → ∀ a, a ≠ i → (true, a) ∈ K (some i) := by
    intro i hij a hai
    rcases hcover _ (hKF (some i)) a with hp | hl
    · exact (Finset.disjoint_left.mp (hKB (some i)) hp
        ((mem_witness_point I a i).mpr (hsparse i hij a hai))).elim
    · exact hl
  have htwo : 1 < (univ.erase j : Finset (Fin r)).card := by
    simp
    omega
  obtain ⟨i, hi, k, hk, hik⟩ := Finset.one_lt_card.mp htwo
  have hij : i ≠ j := (mem_erase.mp hi).1
  have hkj : k ≠ j := (mem_erase.mp hk).1
  let S : Finset (Bool × Fin r) := {(false, j), (true, i), (true, k)}
  have hS : Independent I S := by
    intro a b haS hbS
    have haj : a = j := by simpa [S] using haS
    have hbb : b = i ∨ b = k := by simpa [S] using hbS
    subst a
    rcases hbb with hbi | hbk
    · rw [hbi]
      exact hsparse i hij j (Ne.symm hij)
    · rw [hbk]
      exact hsparse k hkj j (Ne.symm hkj)
  obtain ⟨W, hWF, hWS⟩ := hmiss S hS
  obtain ⟨a, ha⟩ := hexhaust W hWF
  have hhit : ∃ z ∈ K a, z ∈ S := by
    cases a with
    | none => exact ⟨(true, i), hline i, by simp [S]⟩
    | some t =>
      by_cases htj : t = j
      · subst t
        exact ⟨(false, j), hallpoints j, by simp [S]⟩
      · by_cases hit : i = t
        · subst t
          exact ⟨(true, k), hrestlines i htj k (Ne.symm hik), by simp [S]⟩
        · exact ⟨(true, i), hrestlines t htj i hit, by simp [S]⟩
  obtain ⟨z, hzK, hzS⟩ := hhit
  rw [ha] at hzK
  exact Finset.disjoint_left.mp hWS hzK hzS

lemma clause_count_strict_semantic (hr : 3 ≤ r)
    (hdiag : ∀ i, I i i)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (F : Finset (Finset (Bool × Fin r)))
    (hcover : ∀ W ∈ F, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W)
    (hsafe : ∀ x : Bool × Fin r → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ i j, I i j ∧ x (false, i) = true ∧ x (true, j) = true) :
    r + 2 ≤ F.card := by
  apply clause_count_strict I hr hdiag hfour F hcover
  intro S hS
  by_contra hn
  push Not at hn
  let x : Bool × Fin r → Bool := fun u => decide (u ∈ S)
  have hx : ∀ W ∈ F, ∃ u ∈ W, x u = true := by
    intro W hWF
    have hint : ∃ u ∈ W, u ∈ S := by
      by_contra hnone
      push Not at hnone
      exact hn W hWF (Finset.disjoint_left.mpr hnone)
    obtain ⟨u, huW, huS⟩ := hint
    exact ⟨u, huW, by simp [x, huS]⟩
  obtain ⟨i, j, hij, hi, hj⟩ := hsafe x hx
  exact hS i j (by simpa [x] using hi) (by simpa [x] using hj) hij

lemma safe_clause_miss {n : ℕ} (G : SimpleGraph (Fin n))
    (F : Finset (Finset (Fin n)))
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (S : Finset (Fin n)) (hS : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v) :
    ∃ W ∈ F, Disjoint W S := by
  classical
  by_contra hn
  push Not at hn
  let x : Fin n → Bool := fun u => decide (u ∈ S)
  have hx : ∀ W ∈ F, ∃ u ∈ W, x u = true := by
    intro W hWF
    have hint : ∃ u ∈ W, u ∈ S := by
      by_contra hnone
      push Not at hnone
      exact hn W hWF (Finset.disjoint_left.mpr hnone)
    obtain ⟨u, huW, huS⟩ := hint
    exact ⟨u, huW, by simp [x, huS]⟩
  obtain ⟨u, v, huv, hu, hv⟩ := hsafe x hx
  exact hS u (by simpa [x] using hu) v (by simpa [x] using hv) huv

lemma graph_matching_clause_count {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hr : 3 ≤ r) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (p l : Fin r → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hpp : ∀ i j, ¬ G.Adj (p i) (p j)) (hll : ∀ i j, ¬ G.Adj (l i) (l j))
    (hdiag : ∀ i, G.Adj (p i) (l i))
    (F : Finset (Finset (Fin n)))
    (hcover : ∀ W ∈ F, ∀ i, p i ∈ W ∨ l i ∈ W)
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    r + 2 ≤ F.card := by
  classical
  let J : Fin r → Fin r → Prop := fun i j => G.Adj (p i) (l j)
  let f : Bool × Fin r → Fin n
    | (false, i) => p i
    | (true, i) => l i
  let Q : Finset (Fin n) → Finset (Bool × Fin r) :=
    fun W => univ.filter fun u => f u ∈ W
  have hJfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (J a c ∧ J a d ∧ J b c ∧ J b d) := by
    intro a b c d hab hcd ⟨hac, had, hbc, hbd⟩
    have hpab : p a ≠ p b := fun heq => hab (hp heq)
    have heq : l c = l d := by
      apply Finset.card_le_one.mp (hfour (p a) (p b) hpab)
      · exact mem_filter.mpr ⟨mem_univ _, hac, hbc⟩
      · exact mem_filter.mpr ⟨mem_univ _, had, hbd⟩
    exact hcd (hl heq)
  have hQcover : ∀ W ∈ F.image Q, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W := by
    intro W hW i
    obtain ⟨V, hVF, rfl⟩ := mem_image.mp hW
    rcases hcover V hVF i with hpW | hlW
    · exact Or.inl (by simpa [Q, f] using hpW)
    · exact Or.inr (by simpa [Q, f] using hlW)
  have hQmiss : ∀ S, Independent J S → ∃ W ∈ F.image Q, Disjoint W S := by
    intro S hS
    have himg : ∀ u ∈ S.image f, ∀ v ∈ S.image f, ¬ G.Adj u v := by
      intro u hu v hv huv
      obtain ⟨⟨tu, iu⟩, hiu, rfl⟩ := mem_image.mp hu
      obtain ⟨⟨tv, iv⟩, hiv, rfl⟩ := mem_image.mp hv
      cases tu <;> cases tv
      · exact hpp iu iv huv
      · exact hS iu iv hiu hiv huv
      · exact hS iv iu hiv hiu huv.symm
      · exact hll iu iv huv
    obtain ⟨W, hWF, hWS⟩ := safe_clause_miss G F hsafe (S.image f) himg
    refine ⟨Q W, mem_image.mpr ⟨W, hWF, rfl⟩, ?_⟩
    apply Finset.disjoint_left.mpr
    intro u huQ huS
    have huW : f u ∈ W := (mem_filter.mp huQ).2
    have huImg : f u ∈ S.image f := mem_image.mpr ⟨u, huS, rfl⟩
    exact Finset.disjoint_left.mp hWS huW huImg
  have hb := clause_count_strict J hr hdiag hJfour (F.image Q) hQcover hQmiss
  exact le_trans hb card_image_le

end MatchingSurplus

namespace MatchingCounterexample

abbrev cycleGraph : SimpleGraph (Fin 8) :=
  PEqualNP.EdgeOwnership.edgeGraph 8
    [(0, 4), (0, 5), (1, 5), (1, 6), (2, 6), (2, 7), (3, 7), (3, 4)]

def clauses : Finset (Finset (Fin 8)) :=
  {{0, 1, 2, 3}, {2, 3, 4, 5}, {0, 3, 5, 6},
    {0, 1, 6, 7}, {1, 2, 4, 7}, {4, 5, 6, 7}}

lemma cycle_no_four_cycle : PEqualNP.TopForm.NoFourCycle cycleGraph := by decide

lemma cycle_bipartite : ∀ u v : Fin 8, cycleGraph.Adj u v →
    decide (u.val < 4) ≠ decide (v.val < 4) := by decide

lemma cycle_contains_matching : ∀ i : Fin 4,
    cycleGraph.Adj (Fin.castAdd 4 i) (Fin.natAdd 4 i) := by decide

lemma clauses_card : clauses.card = 6 := by decide

set_option maxRecDepth 10000 in
lemma clauses_accept_matching : ∀ i : Fin 4, ∀ W ∈ clauses,
    Fin.castAdd 4 i ∈ W ∨ Fin.natAdd 4 i ∈ W := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
lemma clauses_safe : ∀ x : Fin 8 → Bool,
    (∀ W ∈ clauses, ∃ u ∈ W, x u = true) →
    ∃ u v, cycleGraph.Adj u v ∧ x u = true ∧ x v = true := by decide

lemma clauses_below_two_r_minus_one : clauses.card < 2 * 4 - 1 := by decide

end MatchingCounterexample

namespace RelativeCnf

lemma relative_shared_cnf_matching_surplus {n r : ℕ}
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (P : Finset (Fin n)) (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hr : 3 ≤ r) (p l : Fin r → Fin n)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (hpP : ∀ i, p i ∈ P) (hdiag : ∀ i, H.Adj (p i) (l i))
    (F : Finset (Finset (Fin n))) (k : ℕ)
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ u v, H.Adj u v →
      ∀ W ∈ F, ∃ a ∈ W, a = u ∨ a = v)
    (hcost : PEqualNP.SharedBlockCost.HasOrCost n F k) :
    H.edgeFinset.card + r + 1 ≤ k + F.card := by
  have hlP : ∀ i, l i ∉ P := by
    intro i hi
    exact hP (p i) (hpP i) (l i) hi (hHG (hdiag i))
  have hll : ∀ i j, ¬ G.Adj (l i) (l j) := by
    intro i j hij
    exact (hcover _ _ hij).elim (hlP i) (hlP j)
  have hFc := (relative_clause_properties G H F hsafe haccept).1
  have hclauses := MatchingSurplus.graph_matching_clause_count G hr hfour p l hp hl
    (fun i j => hP (p i) (hpP i) (p j) (hpP j)) hll
    (fun i => hHG (hdiag i)) F (fun W hW i => hFc W hW _ _ (hdiag i)) hsafe
  have hedge := relative_shared_cnf_edge_bound G H P hcover hP hHG hfour F k hsafe haccept hcost
  omega

end RelativeCnf

namespace MatchingDouble

open Finset
open PEqualNP.Outside.L_meta_2583.MatchingSurplus

variable {r : ℕ} (I : Fin r → Fin r → Prop) [DecidableRel I]

def rowWitness (j : Fin r) : Finset (Bool × Fin r) :=
  insert (false, j) ((univ.filter fun b => ¬ I j b).image fun b => (true, b))

def colTest : Option (Fin r) → Finset (Bool × Fin r)
  | none => points
  | some i => witness I i

def rowTest : Option (Fin r) → Finset (Bool × Fin r)
  | none => lines
  | some j => rowWitness I j

lemma mem_row_point (a j : Fin r) : (false, a) ∈ rowWitness I j ↔ a = j := by
  simp [rowWitness]

lemma mem_row_line (a j : Fin r) : (true, a) ∈ rowWitness I j ↔ ¬ I j a := by
  simp [rowWitness]

lemma row_witness_independent (j : Fin r) : Independent I (rowWitness I j) := by
  intro a b ha hb
  have haj := (mem_row_point I a j).mp ha
  subst a
  exact (mem_row_line I b j).mp hb

lemma column_separation
    (hdiag : ∀ i, I i i)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (a b : Option (Fin r)) (hab : a ≠ b) :
    ∃ k, (false, k) ∈ colTest I a ∪ colTest I b ∧
      (true, k) ∈ colTest I a ∪ colTest I b := by
  cases a with
  | none =>
    cases b with
    | none => exact (hab rfl).elim
    | some j =>
      refine ⟨j, mem_union_left _ (mem_points j), ?_⟩
      exact mem_union_right _ ((mem_witness_line I j j).mpr rfl)
  | some i =>
    cases b with
    | none =>
      refine ⟨i, mem_union_right _ (mem_points i), ?_⟩
      exact mem_union_left _ ((mem_witness_line I i i).mpr rfl)
    | some j =>
      have hij : i ≠ j := fun heq => hab (congrArg some heq)
      by_cases hijI : I i j
      · have hji : ¬ I j i := fun hjiI =>
          hfour i j i j hij hij ⟨hdiag i, hijI, hjiI, hdiag j⟩
        exact ⟨j, mem_union_left _ ((mem_witness_point I j i).mpr hji),
          mem_union_right _ ((mem_witness_line I j j).mpr rfl)⟩
      · exact ⟨i, mem_union_right _ ((mem_witness_point I i j).mpr hijI),
          mem_union_left _ ((mem_witness_line I i i).mpr rfl)⟩

lemma row_separation
    (hdiag : ∀ i, I i i)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (a b : Option (Fin r)) (hab : a ≠ b) :
    ∃ k, (false, k) ∈ rowTest I a ∪ rowTest I b ∧
      (true, k) ∈ rowTest I a ∪ rowTest I b := by
  cases a with
  | none =>
    cases b with
    | none => exact (hab rfl).elim
    | some j =>
      exact ⟨j, mem_union_right _ ((mem_row_point I j j).mpr rfl),
        mem_union_left _ (mem_lines j)⟩
  | some i =>
    cases b with
    | none =>
      exact ⟨i, mem_union_left _ ((mem_row_point I i i).mpr rfl),
        mem_union_right _ (mem_lines i)⟩
    | some j =>
      have hij : i ≠ j := fun heq => hab (congrArg some heq)
      by_cases hijI : I i j
      · have hji : ¬ I j i := fun hjiI =>
          hfour i j i j hij hij ⟨hdiag i, hijI, hjiI, hdiag j⟩
        exact ⟨i, mem_union_left _ ((mem_row_point I i i).mpr rfl),
          mem_union_right _ ((mem_row_line I i j).mpr hji)⟩
      · exact ⟨j, mem_union_right _ ((mem_row_point I j j).mpr rfl),
          mem_union_left _ ((mem_row_line I j i).mpr hijI)⟩

lemma cross_separation (hr : 0 < r)
    (hcross : ∀ i j, ∃ k, ¬ I k i ∧ ¬ I j k)
    (a b : Option (Fin r)) :
    ∃ k, (false, k) ∈ colTest I a ∪ rowTest I b ∧
      (true, k) ∈ colTest I a ∪ rowTest I b := by
  let z : Fin r := ⟨0, hr⟩
  cases a with
  | none =>
    cases b with
    | none => exact ⟨z, mem_union_left _ (mem_points z), mem_union_right _ (mem_lines z)⟩
    | some j =>
      obtain ⟨k, _, hjk⟩ := hcross z j
      exact ⟨k, mem_union_left _ (mem_points k),
        mem_union_right _ ((mem_row_line I k j).mpr hjk)⟩
  | some i =>
    cases b with
    | none =>
      obtain ⟨k, hki, _⟩ := hcross i z
      exact ⟨k, mem_union_left _ ((mem_witness_point I k i).mpr hki),
        mem_union_right _ (mem_lines k)⟩
    | some j =>
      obtain ⟨k, hki, hjk⟩ := hcross i j
      exact ⟨k, mem_union_left _ ((mem_witness_point I k i).mpr hki),
        mem_union_right _ ((mem_row_line I k j).mpr hjk)⟩

lemma clause_count_double (hr : 0 < r)
    (hdiag : ∀ i, I i i)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (hcross : ∀ i j, ∃ k, ¬ I k i ∧ ¬ I j k)
    (F : Finset (Finset (Bool × Fin r)))
    (hcover : ∀ W ∈ F, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W)
    (hmiss : ∀ S, Independent I S → ∃ W ∈ F, Disjoint W S) :
    2 * r + 2 ≤ F.card := by
  classical
  let B : Bool × Option (Fin r) → Finset (Bool × Fin r)
    | (false, a) => colTest I a
    | (true, a) => rowTest I a
  have hB : ∀ a, Independent I (B a) := by
    rintro ⟨t, a⟩
    cases t with
    | false =>
      cases a with
      | none => exact points_independent I
      | some i => exact witness_independent I i
    | true =>
      cases a with
      | none => exact lines_independent I
      | some i => exact row_witness_independent I i
  have hsep : ∀ a b, a ≠ b → ∃ k,
      (false, k) ∈ B a ∪ B b ∧ (true, k) ∈ B a ∪ B b := by
    rintro ⟨ta, a⟩ ⟨tb, b⟩ hab
    cases ta <;> cases tb
    · exact column_separation I hdiag hfour a b (fun h => hab (congrArg (Prod.mk false) h))
    · exact cross_separation I hr hcross a b
    · simpa only [B, Finset.union_comm] using cross_separation I hr hcross b a
    · exact row_separation I hdiag hfour a b (fun h => hab (congrArg (Prod.mk true) h))
  have hchoice : ∀ a, ∃ W ∈ F, Disjoint W (B a) := fun a => hmiss _ (hB a)
  choose K hKF hKB using hchoice
  have hinj : Function.Injective K := by
    intro a b heq
    by_contra hab
    obtain ⟨k, hkp, hkl⟩ := hsep a b hab
    have hdis : Disjoint (K a) (B a ∪ B b) := by
      apply Finset.disjoint_left.mpr
      intro z hzK hzB
      rcases mem_union.mp hzB with hza | hzb
      · exact Finset.disjoint_left.mp (hKB a) hzK hza
      · rw [heq] at hzK
        exact Finset.disjoint_left.mp (hKB b) hzK hzb
    rcases hcover _ (hKF a) k with hkpK | hklK
    · exact Finset.disjoint_left.mp hdis hkpK hkp
    · exact Finset.disjoint_left.mp hdis hklK hkl
  have hsub : univ.image K ⊆ F := by
    intro W hW
    obtain ⟨a, _, rfl⟩ := mem_image.mp hW
    exact hKF a
  have hcard : (univ.image K).card = 2 * r + 2 := by
    rw [card_image_of_injective _ hinj]
    simp [Nat.mul_add]
  have hc := card_le_card hsub
  rwa [hcard] at hc

lemma cross_of_degree_sum
    (hdegree : ∀ i j,
      (univ.filter fun k => I k i).card + (univ.filter fun k => I j k).card < r) :
    ∀ i j, ∃ k, ¬ I k i ∧ ¬ I j k := by
  classical
  intro i j
  by_contra hn
  have hsub : (univ : Finset (Fin r)) ⊆
      (univ.filter fun k => I k i) ∪ (univ.filter fun k => I j k) := by
    intro k hk
    by_cases hki : I k i
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hki⟩)
    · have hjk : I j k := by
        by_contra hjk
        exact hn ⟨k, hki, hjk⟩
      exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hjk⟩)
  have hc := card_le_card hsub
  have hu := card_union_le (univ.filter fun k => I k i) (univ.filter fun k => I j k)
  have hd := hdegree i j
  simp only [card_univ, Fintype.card_fin] at hc
  omega

lemma clause_count_degree_bound (d : ℕ) (hr : 2 * d < r)
    (hdiag : ∀ i, I i i)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (hcol : ∀ i, (univ.filter fun k => I k i).card ≤ d)
    (hrow : ∀ j, (univ.filter fun k => I j k).card ≤ d)
    (F : Finset (Finset (Bool × Fin r)))
    (hcover : ∀ W ∈ F, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W)
    (hmiss : ∀ S, Independent I S → ∃ W ∈ F, Disjoint W S) :
    2 * r + 2 ≤ F.card := by
  apply clause_count_double I (by omega) hdiag hfour ?_ F hcover hmiss
  apply cross_of_degree_sum I
  intro i j
  have hc := hcol i
  have hrw := hrow j
  omega

lemma graph_matching_clause_count_double {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hr : 0 < r) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (p l : Fin r → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hpp : ∀ i j, ¬ G.Adj (p i) (p j)) (hll : ∀ i j, ¬ G.Adj (l i) (l j))
    (hdiag : ∀ i, G.Adj (p i) (l i))
    (hcross : ∀ i j, ∃ k, ¬ G.Adj (p k) (l i) ∧ ¬ G.Adj (p j) (l k))
    (F : Finset (Finset (Fin n)))
    (hcover : ∀ W ∈ F, ∀ i, p i ∈ W ∨ l i ∈ W)
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    2 * r + 2 ≤ F.card := by
  classical
  let J : Fin r → Fin r → Prop := fun i j => G.Adj (p i) (l j)
  let f : Bool × Fin r → Fin n
    | (false, i) => p i
    | (true, i) => l i
  let Q : Finset (Fin n) → Finset (Bool × Fin r) :=
    fun W => univ.filter fun u => f u ∈ W
  have hJfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (J a c ∧ J a d ∧ J b c ∧ J b d) := by
    intro a b c d hab hcd ⟨hac, had, hbc, hbd⟩
    have hpab : p a ≠ p b := fun heq => hab (hp heq)
    have heq : l c = l d := by
      apply Finset.card_le_one.mp (hfour (p a) (p b) hpab)
      · exact mem_filter.mpr ⟨mem_univ _, hac, hbc⟩
      · exact mem_filter.mpr ⟨mem_univ _, had, hbd⟩
    exact hcd (hl heq)
  have hQcover : ∀ W ∈ F.image Q, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W := by
    intro W hW i
    obtain ⟨V, hVF, rfl⟩ := mem_image.mp hW
    rcases hcover V hVF i with hpW | hlW
    · exact Or.inl (by simpa [Q, f] using hpW)
    · exact Or.inr (by simpa [Q, f] using hlW)
  have hQmiss : ∀ S, Independent J S → ∃ W ∈ F.image Q, Disjoint W S := by
    intro S hS
    have himg : ∀ u ∈ S.image f, ∀ v ∈ S.image f, ¬ G.Adj u v := by
      intro u hu v hv huv
      obtain ⟨⟨tu, iu⟩, hiu, rfl⟩ := mem_image.mp hu
      obtain ⟨⟨tv, iv⟩, hiv, rfl⟩ := mem_image.mp hv
      cases tu <;> cases tv
      · exact hpp iu iv huv
      · exact hS iu iv hiu hiv huv
      · exact hS iv iu hiv hiu huv.symm
      · exact hll iu iv huv
    obtain ⟨W, hWF, hWS⟩ := safe_clause_miss G F hsafe (S.image f) himg
    refine ⟨Q W, mem_image.mpr ⟨W, hWF, rfl⟩, ?_⟩
    apply Finset.disjoint_left.mpr
    intro u huQ huS
    have huW : f u ∈ W := (mem_filter.mp huQ).2
    have huImg : f u ∈ S.image f := mem_image.mpr ⟨u, huS, rfl⟩
    exact Finset.disjoint_left.mp hWS huW huImg
  have hb := clause_count_double J hr hdiag hJfour hcross (F.image Q) hQcover hQmiss
  exact le_trans hb card_image_le


lemma graph_matching_clause_count_degree {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (d : ℕ) (hr : 2 * d < r)
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (p l : Fin r → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hpp : ∀ i j, ¬ G.Adj (p i) (p j)) (hll : ∀ i j, ¬ G.Adj (l i) (l j))
    (hdiag : ∀ i, G.Adj (p i) (l i))
    (hcol : ∀ i, (univ.filter fun k => G.Adj (p k) (l i)).card ≤ d)
    (hrow : ∀ j, (univ.filter fun k => G.Adj (p j) (l k)).card ≤ d)
    (F : Finset (Finset (Fin n)))
    (hcover : ∀ W ∈ F, ∀ i, p i ∈ W ∨ l i ∈ W)
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    2 * r + 2 ≤ F.card := by
  apply graph_matching_clause_count_double G (by omega) hfour p l hp hl hpp hll hdiag ?_ F hcover hsafe
  apply cross_of_degree_sum (fun i j => G.Adj (p i) (l j))
  intro i j
  have hc := hcol i
  have hrw := hrow j
  omega

end MatchingDouble

namespace RelativeCnf

lemma relative_shared_cnf_degree_surplus {n r : ℕ}
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (P : Finset (Fin n)) (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (d : ℕ) (hr : 2 * d < r) (p l : Fin r → Fin n)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (hpP : ∀ i, p i ∈ P) (hdiag : ∀ i, H.Adj (p i) (l i))
    (hcol : ∀ i, (Finset.univ.filter fun k => G.Adj (p k) (l i)).card ≤ d)
    (hrow : ∀ j, (Finset.univ.filter fun k => G.Adj (p j) (l k)).card ≤ d)
    (F : Finset (Finset (Fin n))) (k : ℕ)
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ u v, H.Adj u v →
      ∀ W ∈ F, ∃ a ∈ W, a = u ∨ a = v)
    (hcost : PEqualNP.SharedBlockCost.HasOrCost n F k) :
    H.edgeFinset.card + 2 * r + 1 ≤ k + F.card := by
  have hlP : ∀ i, l i ∉ P := by
    intro i hi
    exact hP (p i) (hpP i) (l i) hi (hHG (hdiag i))
  have hll : ∀ i j, ¬ G.Adj (l i) (l j) := by
    intro i j hij
    exact (hcover _ _ hij).elim (hlP i) (hlP j)
  have hFc := (relative_clause_properties G H F hsafe haccept).1
  have hclauses := MatchingDouble.graph_matching_clause_count_degree G d hr hfour p l hp hl
    (fun i j => hP (p i) (hpP i) (p j) (hpP j)) hll
    (fun i => hHG (hdiag i)) hcol hrow F (fun W hW i => hFc W hW _ _ (hdiag i)) hsafe
  have hedge := relative_shared_cnf_edge_bound G H P hcover hP hHG hfour F k hsafe haccept hcost
  omega

end RelativeCnf

namespace OrCircuitBridge

open PEqualNP.SharedBlockCost

lemma multioutput_union_count {v n m B : ℕ} (T : ℕ → Finset (Fin v))
    (P : Fin B → Finset (Fin v))
    (hin : ∀ w < n, (T w).card ≤ 1)
    (hgate : ∀ j < m, 2 ≤ (T (n + j)).card →
      ∃ x y, x < n + j ∧ y < n + j ∧ T (n + j) = T x ∪ T y)
    (hout : ∀ b, ∃ w < n + m, T w = P b) :
    ((Finset.univ : Finset (Fin B)).biUnion P).card ≤
      ((Finset.range m).filter fun j => 2 ≤ (T (n + j)).card ∧
        T (n + j) ⊆ (Finset.univ : Finset (Fin B)).biUnion P).card + B := by
  classical
  let Q := (Finset.univ : Finset (Fin B)).biUnion P
  let S : Fin 1 → Finset (Fin v) := fun _ => Q
  have hsub (b : Fin B) : P b ⊆ Q := by
    intro u hu
    exact Finset.mem_biUnion.2 ⟨b, Finset.mem_univ _, hu⟩
  have hmin (b : Fin B) (u : Fin v) (hu : u ∈ P b)
      (hng : ¬ ∃ j, unionGood n m T S 0 u j) : ∀ t ∈ P b, ¬ t < u := by
    intro t ht hlt
    obtain ⟨w, hw, heq⟩ := hout b
    by_cases hwn : w < n
    · have he := Finset.card_le_one.1 (hin w hwn) t (heq.symm ▸ ht) u (heq.symm ▸ hu)
      exact (ne_of_lt hlt) he
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      apply hng
      refine ⟨j, by omega, ?_, ?_, t, ?_, hlt⟩
      · change T (n + j) ⊆ Q
        rw [heq]
        exact hsub b
      · rwa [heq]
      · rwa [heq]
  have hQ : (Q.filter fun u => ∃ j, unionGood n m T S 0 u j).card ≤
      ((Finset.range m).filter fun j =>
        2 ≤ (T (n + j)).card ∧ T (n + j) ⊆ Q).card := by
    refine union_card_le_relation
      (fun u j => unionGood n m T S 0 u j ∧
        ∀ j', j' < j → ¬ unionGood n m T S 0 u j') ?_ ?_
    · intro u hu
      obtain ⟨_, hex⟩ := Finset.mem_filter.1 hu
      have hg := Nat.find_spec hex
      refine ⟨Nat.find hex, ?_, hg, fun j' hj' => Nat.find_min hex hj'⟩
      exact Finset.mem_filter.2
        ⟨Finset.mem_range.2 hg.1, union_good_large hg, hg.2.1⟩
    · intro j hj u hu u' hu'
      obtain ⟨_, hg, hmn⟩ := hu
      obtain ⟨_, hg', hmn'⟩ := hu'
      exact (union_inj_core T S hin hgate
        (fun a b hne => (hne (Subsingleton.elim a b)).elim)
        0 0 u u' j hg hg' hmn hmn').2
  have hR : (Q.filter fun u => ¬ ∃ j, unionGood n m T S 0 u j).card ≤ B := by
    suffices hh : (Q.filter fun u => ¬ ∃ j, unionGood n m T S 0 u j).card ≤
        (Finset.univ : Finset (Fin B)).card by simpa using hh
    refine union_card_le_relation (fun u b => u ∈ P b) ?_ ?_
    · intro u hu
      exact Finset.mem_biUnion.1 (Finset.mem_filter.1 hu).1
    · intro b hb u hu u' hu'
      obtain ⟨huf, hup⟩ := hu
      obtain ⟨hu'f, hu'p⟩ := hu'
      have h1 := hmin b u hup (Finset.mem_filter.1 huf).2
      have h2 := hmin b u' hu'p (Finset.mem_filter.1 hu'f).2
      exact le_antisymm (not_lt.1 (h1 u' hu'p)) (not_lt.1 (h2 u hup))
  have hsplit := Finset.card_filter_add_card_filter_not (s := Q)
    (fun u => ∃ j, unionGood n m T S 0 u j)
  change Q.card ≤ ((Finset.range m).filter fun j =>
    2 ≤ (T (n + j)).card ∧ T (n + j) ⊆ Q).card + B
  omega

lemma multioutput_projected_count {v c n m B : ℕ} (T : ℕ → Finset (Fin v))
    (P : Fin B → Finset (Fin v)) (L : Finset (Fin v))
    (S : Fin c → Finset (Fin v))
    (hin : ∀ w < n, (T w).card ≤ 1)
    (hgate : ∀ j < m, 2 ≤ (T (n + j)).card →
      ∃ x y, x < n + j ∧ y < n + j ∧ T (n + j) = T x ∪ T y)
    (hdis : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    (hout : ∀ a, ∃ w < n + m, T w ∩ L = S a)
    (hpoint : ∀ b, ∃ w < n + m, T w = P b)
    (hPcard : c ≤ ((Finset.univ : Finset (Fin B)).biUnion P).card)
    (hPL : ∀ b, Disjoint (P b) L) :
    ((Finset.univ : Finset (Fin c)).sigma S).card ≤
      ((Finset.range m).filter fun j => 2 ≤ (T (n + j)).card).card + B := by
  classical
  let U : ℕ → Finset (Fin v) := fun w => T w ∩ L
  let Q := (Finset.univ : Finset (Fin B)).biUnion P
  have hQL : Disjoint Q L := by
    refine Finset.disjoint_left.2 ?_
    intro u hu huL
    obtain ⟨b, hb, hup⟩ := Finset.mem_biUnion.1 hu
    exact Finset.disjoint_left.1 (hPL b) hup huL
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
  let D := (Finset.range m).filter fun j =>
    2 ≤ (T (n + j)).card ∧ T (n + j) ⊆ Q
  have hA : ((Finset.univ : Finset (Fin c)).sigma S).card ≤ A.card + c :=
    union_network_count U S hUin hUgate hdis hout
  have hD : c ≤ D.card + B :=
    le_trans hPcard (multioutput_union_count T P hin hgate hpoint)
  have hd : Disjoint A D := by
    refine Finset.disjoint_left.2 ?_
    intro j hjA hjD
    have hlarge := (Finset.mem_filter.1 hjA).2.1
    have hsub := (Finset.mem_filter.1 hjD).2.2
    have hd' : Disjoint (T (n + j)) L := Finset.disjoint_left.2
      (fun a ha haL => Finset.disjoint_left.1 hQL (hsub ha) haL)
    change 2 ≤ (T (n + j) ∩ L).card at hlarge
    rw [Finset.disjoint_iff_inter_eq_empty.1 hd', Finset.card_empty] at hlarge
    omega
  have hbound : A.card + D.card ≤
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
  omega

lemma has_or_cost_multioutput {n c k B : ℕ} (fam : Finset (Finset (Fin n)))
    (P : Fin B → Finset (Fin n)) (L : Finset (Fin n))
    (S : Fin c → Finset (Fin n))
    (hcost : HasOrCost n fam k) (hpoint : ∀ b, P b ∈ fam)
    (hout : ∀ a, ∃ s ∈ fam, s ∩ L = S a)
    (hdis : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1)
    (hPcard : c ≤ ((Finset.univ : Finset (Fin B)).biUnion P).card)
    (hPL : ∀ b, Disjoint (P b) L) :
    ((Finset.univ : Finset (Fin c)).sigma S).card ≤ k + B := by
  classical
  obtain ⟨m, hmk, U, hin, hgate, hfamily⟩ := has_or_cost_network fam hcost
  have htargets : ∀ a, ∃ w < n + m, U w ∩ L = S a := by
    intro a
    obtain ⟨s, hs, hproj⟩ := hout a
    obtain ⟨w, hw, heq⟩ := hfamily s hs
    exact ⟨w, hw, heq ▸ hproj⟩
  have hb := multioutput_projected_count U P L S hin hgate hdis htargets
    (fun b => hfamily (P b) (hpoint b)) hPcard hPL
  have hle : ((Finset.range m).filter fun j => 2 ≤ (U (n + j)).card).card ≤ m := by
    exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
  omega

end OrCircuitBridge

namespace HeavyRows

lemma forced_point {n m : ℕ} (N : Fin n → Finset (Fin m))
    (hsep : ∀ a b, a ≠ b → (N a ∩ N b).card ≤ 1)
    (a b : Fin n) (hne : a ≠ b) (R : Finset (Fin m))
    (Q : Finset (Fin n)) (L : Finset (Fin m))
    (hrow : R ⊆ N a) (hlarge : 2 ≤ R.card)
    (hline : L ⊆ N b) (hhit : ∀ l ∈ R, a ∈ Q ∨ l ∈ L) : a ∈ Q := by
  by_contra ha
  have hsub : R ⊆ N a ∩ N b := by
    intro l hl
    exact Finset.mem_inter.2 ⟨hrow hl, hline ((hhit l hl).resolve_left ha)⟩
  have hc := le_trans (Finset.card_le_card hsub) (hsep a b hne)
  omega

lemma all_other_heavy_points {n m : ℕ} (N R : Fin n → Finset (Fin m))
    (hsep : ∀ a b, a ≠ b → (N a ∩ N b).card ≤ 1)
    (hrow : ∀ a, R a ⊆ N a) (b : Fin n)
    (Q : Finset (Fin n)) (L : Finset (Fin m))
    (hline : L ⊆ N b)
    (hhit : ∀ a, ∀ l ∈ R a, a ∈ Q ∨ l ∈ L) :
    ((Finset.univ.filter fun a => 2 ≤ (R a).card).erase b) ⊆ Q := by
  intro a ha
  obtain ⟨hne, ha⟩ := Finset.mem_erase.1 ha
  exact forced_point N hsep a b hne (R a) Q L (hrow a)
    (Finset.mem_filter.1 ha).2 hline (hhit a)

end HeavyRows

namespace H8Projected

namespace Repair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

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

def singletonSupport (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => val C (List.ofFn (pairInput u u)) w = true

lemma mem_support {n : ℕ} {C : Circuit} {w : ℕ} {u : Fin n} :
    u ∈ singletonSupport n C w ↔ val C (List.ofFn (pairInput u u)) w = true := by
  simp [singletonSupport]

lemma support_input {n : ℕ} {C : Circuit} (u : Fin n) :
    singletonSupport n C u.val = {u} := by
  ext v
  rw [mem_support, val_ofFn]
  simp [pairInput, eq_comm]

lemma support_or {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    {k : ℕ} (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or) (u : Fin n) :
    u ∈ singletonSupport n C (n + k) ↔
      ∃ w ∈ (gateAt C k).inputs, u ∈ singletonSupport n C w := by
  simp only [mem_support, val_or (by simp : (List.ofFn (pairInput u u)).length = n) hk hop]
  exact ⟨fun ⟨w, hw, _, ht⟩ => ⟨w, hw, ht⟩, fun ⟨w, hw, ht⟩ => ⟨w, hw, rb k hk w hw, ht⟩⟩

lemma gate_op {C : Circuit} (hm : Monotone2 C) {k : ℕ} (hk : k < C.gates.length) :
    (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  simpa using (hm _ (gateAt_mem hk)).1

lemma input_card {C : Circuit} (hm : Monotone2 C) {k : ℕ} (hk : k < C.gates.length) :
    (gateAt C k).inputs.toFinset.card ≤ 2 :=
  (List.toFinset_card_le _).trans (hm _ (gateAt_mem hk)).2

def positiveInputs (n : ℕ) (C : Circuit) (k : ℕ) : Finset ℕ := by
  classical
  exact (gateAt C k).inputs.toFinset.filter fun w => (singletonSupport n C w).Nonempty

lemma mem_positiveInputs {n : ℕ} {C : Circuit} {k w : ℕ} :
    w ∈ positiveInputs n C k ↔ w ∈ (gateAt C k).inputs ∧ (singletonSupport n C w).Nonempty := by
  classical
  simp [positiveInputs]

lemma pair_mono {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {x y : Fin n → Bool} (hxy : ∀ u, x u = true → y u = true) :
    ∀ w, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hinput : w < n
    · let u : Fin n := ⟨w, hinput⟩
      change val C (List.ofFn x) u.val = true at hw
      change val C (List.ofFn y) u.val = true
      rw [val_ofFn] at *
      exact hxy u hw
    · have hwlt : w < n + C.gates.length := by
        by_contra! h
        rw [val_ge (by simp : (List.ofFn x).length = n) h] at hw
        cases hw
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      rcases gate_op hm hk with hop | hop
      · apply (val_and (by simp) hk hop).2
        intro i hi
        obtain ⟨hlt, ht⟩ := (val_and (by simp) hk hop).1 hw i hi
        exact ⟨hlt, ih i hlt ht⟩
      · obtain ⟨i, hi, hlt, ht⟩ := (val_or (by simp) hk hop).1 hw
        exact (val_or (by simp) hk hop).2 ⟨i, hi, hlt, ih i hlt ht⟩

end Repair

namespace PurePointBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_2583.H8Projected.Repair

noncomputable def orPool {n : ℕ} (C : Circuit) (x : Fin n → Bool) (m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range m).filter fun k => (gateAt C k).op = GateOp.or ∧
    1 < (singletonSupport n C (n + k)).card ∧ val C (List.ofFn x) (n + k) = false

lemma mem_orPool {n : ℕ} {C : Circuit} {x : Fin n → Bool} {m k : ℕ} :
    k ∈ orPool C x m ↔ k < m ∧ (gateAt C k).op = GateOp.or ∧
      1 < (singletonSupport n C (n + k)).card ∧ val C (List.ofFn x) (n + k) = false := by
  classical
  simp [orPool]

lemma frontier_budget {n : ℕ} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (x : Fin n → Bool) (m : ℕ) (roots : Finset ℕ)
    (hvalid : ∀ w ∈ roots, w < n + C.gates.length)
    (hfalse : ∀ w ∈ roots, val C (List.ofFn x) w = false)
    (hbound : ∀ w ∈ roots, 1 < (singletonSupport n C w).card → w < n + m) :
    (roots.biUnion (singletonSupport n C)).card ≤ roots.card + (orPool C x m).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have hsmall : ∀ w ∈ roots, (singletonSupport n C w).card ≤ 1 := by
      intro w hw
      by_contra! hb
      have hw' := hbound w hw hb
      have hs := support_input (C := C) (⟨w, by omega⟩ : Fin n)
      simp [hs] at hb
    calc
      _ ≤ ∑ w ∈ roots, (singletonSupport n C w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ roots, 1 := Finset.sum_le_sum hsmall
      _ = _ := by simp [orPool]
  | succ m ih =>
    have hpool : orPool C x m ⊆ orPool C x (m + 1) := by
      intro k hk
      obtain ⟨hk, hh⟩ := mem_orPool.1 hk
      exact mem_orPool.2 ⟨by omega, hh⟩
    by_cases htop : n + m ∈ roots ∧ 1 < (singletonSupport n C (n + m)).card
    · obtain ⟨hmem, hlarge⟩ := htop
      have hmC : m < C.gates.length := by have := hvalid _ hmem; omega
      rcases gate_op hm hmC with hand | hor
      · have hex : ∃ a ∈ (gateAt C m).inputs, val C (List.ofFn x) a = false := by
          by_contra! h
          have ht : val C (List.ofFn x) (n + m) = true :=
            (val_and (by simp) hmC hand).2 fun a ha =>
              ⟨rb m hmC a ha, Bool.eq_true_of_not_eq_false (h a ha)⟩
          rw [hfalse _ hmem] at ht
          cases ht
        obtain ⟨a, ha, hfa⟩ := hex
        let T := roots.erase (n + m) ∪ {a}
        have haback : a < n + m := rb m hmC a ha
        have hTvalid : ∀ w ∈ T, w < n + C.gates.length := by
          intro w hw
          rcases Finset.mem_union.1 hw with hw | hw
          · exact hvalid _ (Finset.mem_of_mem_erase hw)
          · have : w = a := Finset.mem_singleton.1 hw
            omega
        have hTfalse : ∀ w ∈ T, val C (List.ofFn x) w = false := by
          intro w hw
          rcases Finset.mem_union.1 hw with hw | hw
          · exact hfalse _ (Finset.mem_of_mem_erase hw)
          · simpa only [Finset.mem_singleton.1 hw] using hfa
        have hTbound : ∀ w ∈ T, 1 < (singletonSupport n C w).card → w < n + m := by
          intro w hw hcard
          rcases Finset.mem_union.1 hw with hw | hw
          · have hlt := hbound w (Finset.mem_of_mem_erase hw) hcard
            have hne := (Finset.mem_erase.1 hw).1
            omega
          · have : w = a := Finset.mem_singleton.1 hw
            omega
        have hsub : roots.biUnion (singletonSupport n C) ⊆ T.biUnion (singletonSupport n C) := by
          intro u hu
          obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.1 hu
          by_cases he : w = n + m
          · subst w
            have hua : u ∈ singletonSupport n C a := mem_support.2
              ((val_and (by simp) hmC hand).1 (mem_support.1 huw) a ha).2
            exact Finset.mem_biUnion.2 ⟨a, Finset.mem_union_right _ (Finset.mem_singleton_self _), hua⟩
          · exact Finset.mem_biUnion.2 ⟨w, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨he, hw⟩), huw⟩
        have hfirst := (Finset.card_le_card hsub).trans (ih T hTvalid hTfalse hTbound)
        have hTcard := Finset.card_union_le (roots.erase (n + m)) {a}
        have herase := Finset.card_erase_add_one hmem
        have hinc := Finset.card_le_card hpool
        simp only [Finset.card_singleton] at hTcard
        change T.card ≤ (roots.erase (n + m)).card + 1 at hTcard
        omega
      · let P := positiveInputs n C m
        let T := roots.erase (n + m) ∪ P
        have hback : ∀ w ∈ P, w < n + m :=
          fun w hw => rb m hmC w (mem_positiveInputs.1 hw).1
        have hTvalid : ∀ w ∈ T, w < n + C.gates.length := by
          intro w hw
          rcases Finset.mem_union.1 hw with hw | hw
          · exact hvalid _ (Finset.mem_of_mem_erase hw)
          · have := hback w hw
            omega
        have hTfalse : ∀ w ∈ T, val C (List.ofFn x) w = false := by
          intro w hw
          rcases Finset.mem_union.1 hw with hw | hw
          · exact hfalse _ (Finset.mem_of_mem_erase hw)
          · cases hf : val C (List.ofFn x) w with
            | false => rfl
            | true =>
              have ht : val C (List.ofFn x) (n + m) = true :=
                (val_or (by simp) hmC hor).2
                  ⟨w, (mem_positiveInputs.1 hw).1, hback w hw, hf⟩
              rw [hfalse _ hmem] at ht
              cases ht
        have hTbound : ∀ w ∈ T, 1 < (singletonSupport n C w).card → w < n + m := by
          intro w hw hcard
          rcases Finset.mem_union.1 hw with hw | hw
          · have hlt := hbound w (Finset.mem_of_mem_erase hw) hcard
            have hne := (Finset.mem_erase.1 hw).1
            omega
          · exact hback w hw
        have hsub : roots.biUnion (singletonSupport n C) ⊆ T.biUnion (singletonSupport n C) := by
          intro u hu
          obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.1 hu
          by_cases he : w = n + m
          · subst w
            obtain ⟨a, ha, hua⟩ := (support_or rb hmC hor u).1 huw
            exact Finset.mem_biUnion.2 ⟨a, Finset.mem_union_right _
              (mem_positiveInputs.2 ⟨ha, u, hua⟩), hua⟩
          · exact Finset.mem_biUnion.2 ⟨w, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨he, hw⟩), huw⟩
        have hfirst := (Finset.card_le_card hsub).trans (ih T hTvalid hTfalse hTbound)
        have hTcard := Finset.card_union_le (roots.erase (n + m)) P
        have herase := Finset.card_erase_add_one hmem
        have hPc : P.card ≤ 2 := (Finset.card_filter_le _ _).trans (input_card hm hmC)
        have hnew : m ∈ orPool C x (m + 1) :=
          mem_orPool.2 ⟨by omega, hor, hlarge, hfalse _ hmem⟩
        have hn : m ∉ orPool C x m := fun h => (Nat.lt_irrefl m) (mem_orPool.1 h).1
        have hsubpool : insert m (orPool C x m) ⊆ orPool C x (m + 1) :=
          Finset.insert_subset_iff.2 ⟨hnew, hpool⟩
        have hinc := Finset.card_le_card hsubpool
        rw [Finset.card_insert_of_notMem hn] at hinc
        change T.card ≤ (roots.erase (n + m)).card + P.card at hTcard
        omega
    · have hnew : ∀ w ∈ roots, 1 < (singletonSupport n C w).card → w < n + m := by
        intro w hw hw'
        have hlt := hbound w hw hw'
        have hne : w ≠ n + m := fun he => htop ⟨he ▸ hw, he ▸ hw'⟩
        omega
      have hfirst := ih roots hvalid hfalse hnew
      have hinc := Finset.card_le_card hpool
      omega

def complementInput {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool :=
  fun p => decide (p ∉ S)

lemma support_subset_of_false {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {S : Finset (Fin n)} {w : ℕ} (hw : val C (List.ofFn (complementInput S)) w = false) :
    singletonSupport n C w ⊆ S := by
  intro p hp
  by_contra hnot
  have hle : ∀ i, pairInput p p i = true → complementInput S i = true := by
    intro i hi
    have hip : i = p := by simpa [pairInput] using hi
    simp [complementInput, hip, hnot]
  have ht := pair_mono hm hle w (mem_support.1 hp)
  rw [hw] at ht
  cases ht

lemma computes_or_budget {n : ℕ} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (S : Finset (Fin n)) (w : ℕ) (hvalid : w < n + C.gates.length)
    (hcomp : ∀ z : Fin n → Bool, val C (List.ofFn z) w = decide (∃ p ∈ S, z p = true)) :
    S.card - 1 ≤ (orPool C (complementInput S) C.gates.length).card := by
  classical
  have hs : singletonSupport n C w = S := by
    ext p
    rw [mem_support, hcomp]
    simp [pairInput, eq_comm]
  have hf : val C (List.ofFn (complementInput S)) w = false := by
    rw [hcomp]
    simp [complementInput]
  have hb := frontier_budget hm rb (complementInput S) C.gates.length {w}
    (by simpa using hvalid) (by simpa using hf)
    (by intro u hu _; simpa only [Finset.mem_singleton.1 hu] using hvalid)
  simp only [Finset.singleton_biUnion, hs, Finset.card_singleton] at hb
  omega

noncomputable def orGates (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun k => (gateAt C k).op = GateOp.or

end PurePointBudget

namespace ProjectedBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.PurePointBudget

noncomputable def positiveSupportInputs {α : Type*} (C : Circuit)
    (support : ℕ → Finset α) (k : ℕ) : Finset ℕ := by
  classical
  exact (gateAt C k).inputs.toFinset.filter fun w => (support w).Nonempty

lemma mem_positiveSupportInputs {α : Type*} {C : Circuit} {support : ℕ → Finset α}
    {k w : ℕ} : w ∈ positiveSupportInputs C support k ↔
    w ∈ (gateAt C k).inputs ∧ (support w).Nonempty := by
  classical
  simp [positiveSupportInputs]

noncomputable def supportOrPool {n : ℕ} {α : Type*} (C : Circuit)
    (support : ℕ → Finset α) (x : Fin n → Bool) (m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range m).filter fun k => (gateAt C k).op = GateOp.or ∧
    1 < (support (n + k)).card ∧ val C (List.ofFn x) (n + k) = false

lemma mem_supportOrPool {n : ℕ} {α : Type*} {C : Circuit} {support : ℕ → Finset α}
    {x : Fin n → Bool} {m k : ℕ} :
    k ∈ supportOrPool C support x m ↔ k < m ∧ (gateAt C k).op = GateOp.or ∧
      1 < (support (n + k)).card ∧ val C (List.ofFn x) (n + k) = false := by
  classical
  simp [supportOrPool]

lemma support_frontier_budget {n : ℕ} {α : Type*} [DecidableEq α] {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C) (support : ℕ → Finset α)
    (hinput : ∀ w, w < n → (support w).card ≤ 1)
    (hAndSupport : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.and →
      ∀ w ∈ (gateAt C k).inputs, support (n + k) ⊆ support w)
    (hOrSupport : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.or →
      ∀ u, u ∈ support (n + k) ↔ ∃ w ∈ (gateAt C k).inputs, u ∈ support w)
    (x : Fin n → Bool) (m : ℕ) (roots : Finset ℕ)
    (hvalid : ∀ w ∈ roots, w < n + C.gates.length)
    (hfalse : ∀ w ∈ roots, val C (List.ofFn x) w = false)
    (hbound : ∀ w ∈ roots, 1 < (support w).card → w < n + m) :
    (roots.biUnion (support)).card ≤ roots.card + (supportOrPool C support x m).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have hsmall : ∀ w ∈ roots, (support w).card ≤ 1 := by
      intro w hw
      by_contra! hb
      have hw' := hbound w hw hb
      have hs := hinput w (by omega)
      omega
    calc
      _ ≤ ∑ w ∈ roots, (support w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ roots, 1 := Finset.sum_le_sum hsmall
      _ = _ := by simp [supportOrPool]
  | succ m ih =>
    have hpool : supportOrPool C support x m ⊆ supportOrPool C support x (m + 1) := by
      intro k hk
      obtain ⟨hk, hh⟩ := mem_supportOrPool.1 hk
      exact mem_supportOrPool.2 ⟨by omega, hh⟩
    by_cases htop : n + m ∈ roots ∧ 1 < (support (n + m)).card
    · obtain ⟨hmem, hlarge⟩ := htop
      have hmC : m < C.gates.length := by have := hvalid _ hmem; omega
      rcases gate_op hm hmC with hand | hor
      · have hex : ∃ a ∈ (gateAt C m).inputs, val C (List.ofFn x) a = false := by
          by_contra! h
          have ht : val C (List.ofFn x) (n + m) = true :=
            (val_and (by simp) hmC hand).2 fun a ha =>
              ⟨rb m hmC a ha, Bool.eq_true_of_not_eq_false (h a ha)⟩
          rw [hfalse _ hmem] at ht
          cases ht
        obtain ⟨a, ha, hfa⟩ := hex
        let T := roots.erase (n + m) ∪ {a}
        have haback : a < n + m := rb m hmC a ha
        have hTvalid : ∀ w ∈ T, w < n + C.gates.length := by
          intro w hw
          rcases Finset.mem_union.1 hw with hw | hw
          · exact hvalid _ (Finset.mem_of_mem_erase hw)
          · have : w = a := Finset.mem_singleton.1 hw
            omega
        have hTfalse : ∀ w ∈ T, val C (List.ofFn x) w = false := by
          intro w hw
          rcases Finset.mem_union.1 hw with hw | hw
          · exact hfalse _ (Finset.mem_of_mem_erase hw)
          · simpa only [Finset.mem_singleton.1 hw] using hfa
        have hTbound : ∀ w ∈ T, 1 < (support w).card → w < n + m := by
          intro w hw hcard
          rcases Finset.mem_union.1 hw with hw | hw
          · have hlt := hbound w (Finset.mem_of_mem_erase hw) hcard
            have hne := (Finset.mem_erase.1 hw).1
            omega
          · have : w = a := Finset.mem_singleton.1 hw
            omega
        have hsub : roots.biUnion (support) ⊆ T.biUnion (support) := by
          intro u hu
          obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.1 hu
          by_cases he : w = n + m
          · subst w
            have hua : u ∈ support a := hAndSupport m hmC hand a ha huw
            exact Finset.mem_biUnion.2 ⟨a, Finset.mem_union_right _ (Finset.mem_singleton_self _), hua⟩
          · exact Finset.mem_biUnion.2 ⟨w, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨he, hw⟩), huw⟩
        have hfirst := (Finset.card_le_card hsub).trans (ih T hTvalid hTfalse hTbound)
        have hTcard := Finset.card_union_le (roots.erase (n + m)) {a}
        have herase := Finset.card_erase_add_one hmem
        have hinc := Finset.card_le_card hpool
        simp only [Finset.card_singleton] at hTcard
        change T.card ≤ (roots.erase (n + m)).card + 1 at hTcard
        omega
      · let P := positiveSupportInputs C support m
        let T := roots.erase (n + m) ∪ P
        have hback : ∀ w ∈ P, w < n + m :=
          fun w hw => rb m hmC w (mem_positiveSupportInputs.1 hw).1
        have hTvalid : ∀ w ∈ T, w < n + C.gates.length := by
          intro w hw
          rcases Finset.mem_union.1 hw with hw | hw
          · exact hvalid _ (Finset.mem_of_mem_erase hw)
          · have := hback w hw
            omega
        have hTfalse : ∀ w ∈ T, val C (List.ofFn x) w = false := by
          intro w hw
          rcases Finset.mem_union.1 hw with hw | hw
          · exact hfalse _ (Finset.mem_of_mem_erase hw)
          · cases hf : val C (List.ofFn x) w with
            | false => rfl
            | true =>
              have ht : val C (List.ofFn x) (n + m) = true :=
                (val_or (by simp) hmC hor).2
                  ⟨w, (mem_positiveSupportInputs.1 hw).1, hback w hw, hf⟩
              rw [hfalse _ hmem] at ht
              cases ht
        have hTbound : ∀ w ∈ T, 1 < (support w).card → w < n + m := by
          intro w hw hcard
          rcases Finset.mem_union.1 hw with hw | hw
          · have hlt := hbound w (Finset.mem_of_mem_erase hw) hcard
            have hne := (Finset.mem_erase.1 hw).1
            omega
          · exact hback w hw
        have hsub : roots.biUnion (support) ⊆ T.biUnion (support) := by
          intro u hu
          obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.1 hu
          by_cases he : w = n + m
          · subst w
            obtain ⟨a, ha, hua⟩ := (hOrSupport m hmC hor u).1 huw
            exact Finset.mem_biUnion.2 ⟨a, Finset.mem_union_right _
              (mem_positiveSupportInputs.2 ⟨ha, u, hua⟩), hua⟩
          · exact Finset.mem_biUnion.2 ⟨w, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨he, hw⟩), huw⟩
        have hfirst := (Finset.card_le_card hsub).trans (ih T hTvalid hTfalse hTbound)
        have hTcard := Finset.card_union_le (roots.erase (n + m)) P
        have herase := Finset.card_erase_add_one hmem
        have hPc : P.card ≤ 2 := (Finset.card_filter_le _ _).trans (input_card hm hmC)
        have hnew : m ∈ supportOrPool C support x (m + 1) :=
          mem_supportOrPool.2 ⟨by omega, hor, hlarge, hfalse _ hmem⟩
        have hn : m ∉ supportOrPool C support x m := fun h => (Nat.lt_irrefl m) (mem_supportOrPool.1 h).1
        have hsubpool : insert m (supportOrPool C support x m) ⊆ supportOrPool C support x (m + 1) :=
          Finset.insert_subset_iff.2 ⟨hnew, hpool⟩
        have hinc := Finset.card_le_card hsubpool
        rw [Finset.card_insert_of_notMem hn] at hinc
        change T.card ≤ (roots.erase (n + m)).card + P.card at hTcard
        omega
    · have hnew : ∀ w ∈ roots, 1 < (support w).card → w < n + m := by
        intro w hw hw'
        have hlt := hbound w hw hw'
        have hne : w ≠ n + m := fun he => htop ⟨he ▸ hw, he ▸ hw'⟩
        omega
      have hfirst := ih roots hvalid hfalse hnew
      have hinc := Finset.card_le_card hpool
      omega

def projectedSupport (n : ℕ) (C : Circuit) (V : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  singletonSupport n C w ∩ V

lemma projectedSupport_input {n : ℕ} {C : Circuit} (V : Finset (Fin n))
    (w : ℕ) (hw : w < n) : (projectedSupport n C V w).card ≤ 1 := by
  have hs := support_input (C := C) (⟨w, hw⟩ : Fin n)
  calc
    _ ≤ (singletonSupport n C w).card := Finset.card_le_card Finset.inter_subset_left
    _ = 1 := by rw [hs]; rfl

lemma projectedSupport_and {n : ℕ} {C : Circuit} (V : Finset (Fin n))
    {k : ℕ} (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and)
    {w : ℕ} (hw : w ∈ (gateAt C k).inputs) :
    projectedSupport n C V (n + k) ⊆ projectedSupport n C V w := by
  intro p hp
  obtain ⟨hp, hV⟩ := Finset.mem_inter.1 hp
  have ht := ((val_and (by simp) hk hop).1 (mem_support.1 hp) w hw).2
  exact Finset.mem_inter.2 ⟨mem_support.2 ht, hV⟩

lemma projectedSupport_or {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    (V : Finset (Fin n)) {k : ℕ} (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (p : Fin n) :
    p ∈ projectedSupport n C V (n + k) ↔
      ∃ w ∈ (gateAt C k).inputs, p ∈ projectedSupport n C V w := by
  simp only [projectedSupport, Finset.mem_inter, support_or rb hk hop]
  aesop

def projectedComplementInput {n : ℕ} (V S : Finset (Fin n)) : Fin n → Bool :=
  fun p => decide (p ∈ V ∧ p ∉ S)

noncomputable def projectedOrPool {n : ℕ} (C : Circuit) (V S : Finset (Fin n))
    (m : ℕ) : Finset ℕ :=
  supportOrPool C (projectedSupport n C V) (projectedComplementInput V S) m

lemma projectedSupport_subset_of_false {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {V S : Finset (Fin n)} {w : ℕ}
    (hw : val C (List.ofFn (projectedComplementInput V S)) w = false) :
    projectedSupport n C V w ⊆ S ∩ V := by
  intro p hp
  obtain ⟨hp, hpV⟩ := Finset.mem_inter.1 hp
  refine Finset.mem_inter.2 ⟨?_, hpV⟩
  by_contra hnot
  have hle : ∀ i, pairInput p p i = true → projectedComplementInput V S i = true := by
    intro i hi
    have hip : i = p := by simpa [pairInput] using hi
    simp [projectedComplementInput, hip, hpV, hnot]
  have ht := pair_mono hm hle w (mem_support.1 hp)
  rw [hw] at ht
  cases ht

lemma projectedOrPool_disjoint {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {V S T : Finset (Fin n)} (hST : ((S ∩ V) ∩ (T ∩ V)).card ≤ 1) (m : ℕ) :
    Disjoint (projectedOrPool C V S m) (projectedOrPool C V T m) := by
  apply Finset.disjoint_left.2
  intro k hkS hkT
  obtain ⟨_, _, hlarge, hS⟩ := mem_supportOrPool.1 hkS
  obtain ⟨_, _, _, hT⟩ := mem_supportOrPool.1 hkT
  have hsub : projectedSupport n C V (n + k) ⊆ (S ∩ V) ∩ (T ∩ V) :=
    Finset.subset_inter (projectedSupport_subset_of_false hm hS)
      (projectedSupport_subset_of_false hm hT)
  have hcard := (Finset.card_le_card hsub).trans hST
  omega

lemma point_projected_disjoint {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {V W S : Finset (Fin n)} (hWV : Disjoint W V) (m : ℕ) :
    Disjoint (orPool C (complementInput W) m) (projectedOrPool C V S m) := by
  apply Finset.disjoint_left.2
  intro k hkW hkS
  obtain ⟨_, _, _, hW⟩ := mem_orPool.1 hkW
  obtain ⟨_, _, hlarge, _⟩ := mem_supportOrPool.1 hkS
  have hempty : projectedSupport n C V (n + k) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro p hp
    obtain ⟨hp, hpV⟩ := Finset.mem_inter.1 hp
    exact Finset.disjoint_left.1 hWV (support_subset_of_false hm hW hp) hpV
  simp [hempty] at hlarge

lemma computes_projected_or_budget {n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C) (V S : Finset (Fin n))
    (w : ℕ) (hvalid : w < n + C.gates.length)
    (hcomp : ∀ z : Fin n → Bool, val C (List.ofFn z) w = decide (∃ p ∈ S, z p = true)) :
    (S ∩ V).card - 1 ≤ (projectedOrPool C V S C.gates.length).card := by
  classical
  have hs : projectedSupport n C V w = S ∩ V := by
    have hs' : singletonSupport n C w = S := by
      ext p
      rw [mem_support, hcomp]
      simp [pairInput, eq_comm]
    simp [projectedSupport, hs']
  have hf : val C (List.ofFn (projectedComplementInput V S)) w = false := by
    rw [hcomp]
    apply decide_eq_false
    rintro ⟨p, hp, hxp⟩
    have hxp' : p ∈ V ∧ p ∉ S := by simpa [projectedComplementInput] using hxp
    exact hxp'.2 hp
  have hb := support_frontier_budget hm rb (projectedSupport n C V)
    (projectedSupport_input V)
    (fun _ hk hop _ hw => projectedSupport_and V hk hop hw)
    (fun _ hk hop p => projectedSupport_or rb V hk hop p)
    (projectedComplementInput V S) C.gates.length {w}
    (by simpa using hvalid) (by simpa using hf)
    (by intro u hu _; simpa only [Finset.mem_singleton.1 hu] using hvalid)
  simp only [Finset.singleton_biUnion, hs, Finset.card_singleton] at hb
  change (S ∩ V).card - 1 ≤ (supportOrPool C (projectedSupport n C V)
    (projectedComplementInput V S) C.gates.length).card
  omega

lemma split_multioutput_or_budget {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (V : Finset (Fin n)) (S : ι → Finset (Fin n)) (output : ι → ℕ)
    (hvalid : ∀ i, output i < n + C.gates.length)
    (hcomp : ∀ i (z : Fin n → Bool),
      val C (List.ofFn z) (output i) = decide (∃ p ∈ S i, z p = true))
    (hpair : ∀ i j, i ≠ j → ((S i ∩ V) ∩ (S j ∩ V)).card ≤ 1)
    (W : Finset (Fin n)) (w : ℕ) (hWV : Disjoint W V)
    (hwvalid : w < n + C.gates.length)
    (hwcomp : ∀ z : Fin n → Bool, val C (List.ofFn z) w = decide (∃ p ∈ W, z p = true)) :
    (∑ i, ((S i ∩ V).card - 1)) + (W.card - 1) ≤ (orGates C).card := by
  classical
  let pools := fun i => projectedOrPool C V (S i) C.gates.length
  let U := Finset.univ.biUnion pools
  let P := orPool C (complementInput W) C.gates.length
  have hdis : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint pools := by
    intro i _ j _ hij
    exact projectedOrPool_disjoint hm (hpair i j hij) C.gates.length
  have hsum : (∑ i, ((S i ∩ V).card - 1)) ≤ U.card := by
    calc
      _ ≤ ∑ i, (pools i).card := Finset.sum_le_sum fun i _ =>
        computes_projected_or_budget hm rb V (S i) (output i) (hvalid i) (hcomp i)
      _ = _ := (Finset.card_biUnion hdis).symm
  have hpoint : W.card - 1 ≤ P.card :=
    computes_or_budget hm rb W w hwvalid hwcomp
  have hUP : Disjoint U P := by
    apply Finset.disjoint_left.2
    intro k hkU hkP
    obtain ⟨i, _, hki⟩ := Finset.mem_biUnion.1 hkU
    exact Finset.disjoint_left.1 (point_projected_disjoint hm hWV C.gates.length) hkP hki
  have hsub : U ∪ P ⊆ orGates C := by
    intro k hk
    rcases Finset.mem_union.1 hk with hk | hk
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 hk
      obtain ⟨hk, hop, _⟩ := mem_supportOrPool.1 hi
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hop⟩
    · obtain ⟨hk, hop, _⟩ := mem_orPool.1 hk
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hop⟩
  calc
    _ ≤ U.card + P.card := Nat.add_le_add hsum hpoint
    _ = (U ∪ P).card := (Finset.card_union_of_disjoint hUP).symm
    _ ≤ _ := Finset.card_le_card hsub

end ProjectedBudget


end H8Projected

namespace RelativeCnf
open Finset
variable {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj]

lemma relative_circuit_cnf_edge_bound (P : Finset (Fin n))
    (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (F : Finset (Finset (Fin n)))
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ u v, H.Adj u v →
      ∀ W ∈ F, ∃ a ∈ W, a = u ∨ a = v)
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (rb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (hwires : ∀ W ∈ F, ∃ w : ℕ, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool, H8Projected.Repair.val C (List.ofFn x) w =
        decide (∃ u ∈ W, x u = true)) :
    H.edgeFinset.card ≤ (H8Projected.PurePointBudget.orGates C).card + 1 := by
  classical
  obtain ⟨hFc, hcomplete⟩ := relative_clause_properties G H F hsafe haccept
  let A := P.filter fun u => (H.neighborFinset u).Nonempty
  have hAP : A ⊆ P := filter_subset _ _
  have hactive : ∀ u ∈ A, (H.neighborFinset u).Nonempty :=
    fun _ hu => (mem_filter.mp hu).2
  obtain ⟨W₀, hW₀F, hW₀P, hAW₀⟩ :=
    relative_base_clause G H P A hcover hP hHG hAP hactive F hFc hcomplete
  let e : Fin A.card ≃o A := A.orderIsoOfFin rfl
  have hchoices : ∀ a : Fin A.card, ∃ W ∈ F,
      W ⊆ P.erase (e a).val ∪ G.neighborFinset (e a).val ∧
      H.neighborFinset (e a).val ⊆ W \ P ∧
      W \ P ⊆ G.neighborFinset (e a).val := by
    intro a
    exact relative_point_clause G H P hcover hP hHG (hAP (e a).property) F hFc hcomplete
  choose K hKF hKswap hKlow hKhigh using hchoices
  let S : Fin A.card → Finset (Fin n) := fun a => K a \ P
  let L := univ \ P
  have hout : ∀ a, ∃ W ∈ F, W ∩ L = S a := by
    intro a
    refine ⟨K a, hKF a, ?_⟩
    ext z
    simp [S, L]
  have hdis : ∀ a b, a ≠ b → (S a ∩ S b).card ≤ 1 := by
    intro a b hab
    have he : (e a).val ≠ (e b).val := by
      intro heq
      exact hab (e.injective (Subtype.ext heq))
    exact relative_projection_inter G hfour he (hKhigh a) (hKhigh b)
  have hW₀L : Disjoint W₀ L := by
    apply Finset.disjoint_left.mpr
    intro z hz hzL
    exact (mem_sdiff.mp hzL).2 (hW₀P hz)
  have hKL : ∀ a, K a ∩ L = S a := by
    intro a
    ext z
    simp [S, L]
  have hwirechoices : ∀ a : Fin A.card, ∃ w : ℕ, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool, H8Projected.Repair.val C (List.ofFn x) w =
        decide (∃ u ∈ K a, x u = true) := fun a => hwires (K a) (hKF a)
  choose output hvalid hcomp using hwirechoices
  obtain ⟨w, hwvalid, hwcomp⟩ := hwires W₀ hW₀F
  have hb₀ := H8Projected.ProjectedBudget.split_multioutput_or_budget hm rb L K output
    hvalid hcomp (by intro a b hab; simpa only [hKL] using hdis a b hab)
    W₀ w hW₀L hwvalid hwcomp
  have hpositive : ∀ a, 1 ≤ (S a).card := by
    intro a
    obtain ⟨u, hu⟩ := hactive (e a).val (e a).property
    exact Finset.card_pos.mpr ⟨u, hKlow a hu⟩
  have hcount : (univ.sigma S).card =
      (∑ a : Fin A.card, ((K a ∩ L).card - 1)) + A.card := by
    rw [Finset.card_sigma]
    calc
      (∑ a : Fin A.card, (S a).card) =
          ∑ a : Fin A.card, (((K a ∩ L).card - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hKL]
        have hpos := hpositive a
        omega
      _ = _ := by simp [Finset.sum_add_distrib]
  have hAWcard := Finset.card_le_card hAW₀
  have hb : (univ.sigma S).card ≤ (H8Projected.PurePointBudget.orGates C).card + 1 := by
    omega
  have hsum : (∑ u ∈ A, (H.neighborFinset u).card) =
      ∑ a : Fin A.card, (H.neighborFinset (e a).val).card := by
    refine Finset.sum_bij (fun u hu => e.symm ⟨u, hu⟩)
      (fun _ _ => mem_univ _) ?_ ?_ ?_
    · intro u hu v hv heq
      have hh := e.symm.injective heq
      exact congrArg Subtype.val hh
    · intro a ha
      exact ⟨(e a).val, (e a).property, by simp⟩
    · intro u hu
      rw [e.apply_symm_apply]
  have hedge := Cnf.edges_le_cover_degrees H A (active_points_cover G H P hcover hHG)
  have hsize : H.edgeFinset.card ≤ (univ.sigma S).card := by
    rw [Finset.card_sigma]
    rw [hsum] at hedge
    apply le_trans hedge
    apply Finset.sum_le_sum
    intro a ha
    exact card_le_card (hKlow a)
  exact le_trans hsize hb

lemma relative_circuit_cnf_cover_bound (P : Finset (Fin n))
    (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (F : Finset (Finset (Fin n)))
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ u v, H.Adj u v →
      ∀ W ∈ F, ∃ a ∈ W, a = u ∨ a = v)
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (rb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (hwires : ∀ W ∈ F, ∃ w : ℕ, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool, H8Projected.Repair.val C (List.ofFn x) w =
        decide (∃ u ∈ W, x u = true)) :
    ∃ T : Finset (Fin n), Cnf.Covers H T ∧ H.edgeFinset.card + T.card ≤ (H8Projected.PurePointBudget.orGates C).card + F.card := by
  classical
  obtain ⟨hFc, hcomplete⟩ := relative_clause_properties G H F hsafe haccept
  let A := P.filter fun u => (H.neighborFinset u).Nonempty
  have hAP : A ⊆ P := filter_subset _ _
  have hactive : ∀ u ∈ A, (H.neighborFinset u).Nonempty :=
    fun _ hu => (mem_filter.mp hu).2
  obtain ⟨W₀, hW₀F, hW₀P, hAW₀⟩ :=
    relative_base_clause G H P A hcover hP hHG hAP hactive F hFc hcomplete
  have hchoices : ∀ u : Fin n, ∃ W ∈ F, W ⊆ P.erase u ∪ G.neighborFinset u := by
    intro u
    exact hcomplete _ (Cnf.cover_swap G P hcover u)
  choose K hKF hKsub using hchoices
  have hlow : ∀ u ∈ A, H.neighborFinset u ⊆ K u \ P := by
    intro u hu w hw
    have huK : u ∉ K u := fun h => Cnf.not_mem_swap G P u (hKsub u h)
    have hwK : w ∈ K u :=
      (hFc (K u) (hKF u) u w (H.mem_neighborFinset u w |>.mp hw)).resolve_left huK
    exact mem_sdiff.mpr ⟨hwK, relative_neighbor_not_point G H P hP hHG (hAP hu) hw⟩
  have hhigh : ∀ u ∈ A, K u \ P ⊆ G.neighborFinset u := by
    intro u hu w hw
    obtain ⟨hwK, hwP⟩ := mem_sdiff.mp hw
    rcases mem_union.mp (hKsub u hwK) with hwE | hwN
    · exact (hwP (mem_of_mem_erase hwE)).elim
    · exact hwN
  have hnot : W₀ ∉ A.image K := by
    rintro h
    obtain ⟨u, hu, huW₀⟩ := mem_image.mp h
    obtain ⟨w, hw⟩ := hactive u hu
    obtain ⟨hwK, hwP⟩ := mem_sdiff.mp (hlow u hu hw)
    rw [huW₀] at hwK
    exact hwP (hW₀P hwK)
  have hsub : insert W₀ (A.image K) ⊆ F := by
    intro W hW
    rcases mem_insert.mp hW with rfl | hW
    · exact hW₀F
    · obtain ⟨u, hu, rfl⟩ := mem_image.mp hW
      exact hKF u
  obtain ⟨T, hT, hTcard⟩ := cover_from_clause_projections G H A P
    (active_points_cover G H P hcover hHG) hfour K hlow hhigh
  have hFcard := card_le_card hsub
  rw [card_insert_of_notMem hnot] at hFcard
  have hedge := relative_circuit_cnf_edge_bound G H P hcover hP hHG hfour F hsafe haccept C hm rb hwires
  refine ⟨T, hT, ?_⟩
  omega

end RelativeCnf

namespace InducedMatching

open Finset
open PEqualNP.Outside.L_meta_2583.MatchingSurplus

variable {r : ℕ} (I : Fin r → Fin r → Prop) [DecidableRel I]

def IndexIndependent (A : Finset (Fin r)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ I a b

lemma exists_large_independent (d : ℕ) (hdiag : ∀ i, I i i)
    (hcol : ∀ i, (univ.filter fun k => I k i).card ≤ d)
    (hrow : ∀ j, (univ.filter fun k => I j k).card ≤ d) :
    ∃ A : Finset (Fin r), IndexIndependent I A ∧ r ≤ (2 * d - 1) * A.card := by
  classical
  have hex : ∃ k : ℕ, ∃ A : Finset (Fin r), IndexIndependent I A ∧ r - A.card = k := by
    refine ⟨r, ∅, ?_, by simp⟩
    intro a ha
    simp at ha
  obtain ⟨A, hA, hmin⟩ := Nat.find_spec hex
  have hmax : ∀ B, IndexIndependent I B → B.card ≤ A.card := by
    intro B hB
    have hfind := Nat.find_min' hex (show ∃ C : Finset (Fin r),
        IndexIndependent I C ∧ r - C.card = r - B.card from ⟨B, hB, rfl⟩)
    have haCard : A.card ≤ r := by simpa using card_le_univ A
    have hbCard : B.card ≤ r := by simpa using card_le_univ B
    omega
  let R : Fin r → Finset (Fin r) := fun a => univ.filter fun k => I a k
  let C : Fin r → Finset (Fin r) := fun a => univ.filter fun k => I k a
  let N : Fin r → Finset (Fin r) := fun a => R a ∪ C a
  have hself : ∀ a, a ∈ N a := by
    intro a
    exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hdiag a⟩)
  have hcover : (univ : Finset (Fin r)) ⊆ A.biUnion N := by
    intro i hi
    by_contra hn
    have hiA : i ∉ A := fun h => hn (mem_biUnion.mpr ⟨i, h, hself i⟩)
    have hnone : ∀ a ∈ A, ¬ I a i ∧ ¬ I i a := by
      intro a ha
      constructor
      · intro hai
        exact hn (mem_biUnion.mpr ⟨a, ha, mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hai⟩)⟩)
      · intro hia
        exact hn (mem_biUnion.mpr ⟨a, ha, mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hia⟩)⟩)
    have hins : IndexIndependent I (insert i A) := by
      intro a ha b hb hab
      rcases mem_insert.mp ha with hai | haA
      · subst a
        rcases mem_insert.mp hb with hbi | hbA
        · exact (hab hbi.symm).elim
        · exact (hnone b hbA).2
      · rcases mem_insert.mp hb with hbi | hbA
        · rw [hbi]
          exact (hnone a haA).1
        · exact hA a haA b hbA hab
    have hb := hmax _ hins
    rw [card_insert_of_notMem hiA] at hb
    omega
  have hNcard : ∀ a, (N a).card ≤ 2 * d - 1 := by
    intro a
    have hinter : 1 ≤ (R a ∩ C a).card := by
      apply one_le_card.mpr
      exact ⟨a, mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hdiag a⟩,
        mem_filter.mpr ⟨mem_univ _, hdiag a⟩⟩⟩
    have hcard := card_union_add_card_inter (R a) (C a)
    have hc := hcol a
    have hrw := hrow a
    change (C a).card ≤ d at hc
    change (R a).card ≤ d at hrw
    change (R a ∪ C a).card ≤ 2 * d - 1
    omega
  refine ⟨A, hA, ?_⟩
  calc r = (univ : Finset (Fin r)).card := by simp
    _ ≤ (A.biUnion N).card := card_le_card hcover
    _ ≤ ∑ a ∈ A, (N a).card := card_biUnion_le
    _ ≤ ∑ a ∈ A, (2 * d - 1) := sum_le_sum (fun a ha => hNcard a)
    _ = (2 * d - 1) * A.card := by simp [Nat.mul_comm]

lemma independent_clauses_power (A : Finset (Fin r)) (hA : IndexIndependent I A)
    (F : Finset (Finset (Bool × Fin r)))
    (hcover : ∀ W ∈ F, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W)
    (hmiss : ∀ S, Independent I S → ∃ W ∈ F, Disjoint W S) :
    2 ^ A.card ≤ F.card := by
  classical
  let B := {s : Finset (Fin r) // s ∈ A.powerset}
  let S : B → Finset (Bool × Fin r) := fun b =>
    (b.val.image fun i => (false, i)) ∪ ((A \ b.val).image fun i => (true, i))
  have hsubset : ∀ b : B, b.val ⊆ A := fun b => mem_powerset.mp b.property
  have hp : ∀ b : B, ∀ i, (false, i) ∈ S b ↔ i ∈ b.val := by
    intro b i
    simp [S]
  have hl : ∀ b : B, ∀ i, (true, i) ∈ S b ↔ i ∈ A ∧ i ∉ b.val := by
    intro b i
    simp [S]
  have hS : ∀ b : B, Independent I (S b) := by
    intro b i j hi hj
    have hiB := (hp b i).mp hi
    obtain ⟨hjA, hjB⟩ := (hl b j).mp hj
    have hij : i ≠ j := by
      intro heq
      exact hjB (heq ▸ hiB)
    exact hA i (hsubset b hiB) j hjA hij
  have hchoice : ∀ b : B, ∃ W ∈ F, Disjoint W (S b) := fun b => hmiss _ (hS b)
  choose K hKF hKB using hchoice
  have hinj : Function.Injective K := by
    have hmono : ∀ b c : B, K b = K c → b.val ⊆ c.val := by
      intro b c heq i hi
      by_contra hic
      have hiSb : (false, i) ∈ S b := (hp b i).mpr hi
      have hiSc : (true, i) ∈ S c := (hl c i).mpr ⟨hsubset b hi, hic⟩
      rcases hcover (K b) (hKF b) i with hiK | hiK
      · exact Finset.disjoint_left.mp (hKB b) hiK hiSb
      · rw [heq] at hiK
        exact Finset.disjoint_left.mp (hKB c) hiK hiSc
    intro b c heq
    apply Subtype.ext
    exact Finset.Subset.antisymm (hmono b c heq) (hmono c b heq.symm)
  have hsub : A.powerset.attach.image K ⊆ F := by
    intro W hW
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hW
    exact hKF b
  calc 2 ^ A.card = A.powerset.card := (card_powerset A).symm
    _ = (A.powerset.attach.image K).card := by
      rw [card_image_of_injective _ hinj]
      exact card_attach.symm
    _ ≤ F.card := card_le_card hsub

lemma clause_count_degree_exponential (d : ℕ) (hdiag : ∀ i, I i i)
    (hcol : ∀ i, (univ.filter fun k => I k i).card ≤ d)
    (hrow : ∀ j, (univ.filter fun k => I j k).card ≤ d)
    (F : Finset (Finset (Bool × Fin r)))
    (hcover : ∀ W ∈ F, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W)
    (hmiss : ∀ S, Independent I S → ∃ W ∈ F, Disjoint W S) :
    ∃ t : ℕ, r ≤ (2 * d - 1) * t ∧ 2 ^ t ≤ F.card := by
  obtain ⟨A, hA, hbound⟩ := exists_large_independent I d hdiag hcol hrow
  exact ⟨A.card, hbound, independent_clauses_power I A hA F hcover hmiss⟩

lemma graph_matching_clause_count_exponential {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (d : ℕ) (p l : Fin r → Fin n)
    (hpp : ∀ i j, ¬ G.Adj (p i) (p j)) (hll : ∀ i j, ¬ G.Adj (l i) (l j))
    (hdiag : ∀ i, G.Adj (p i) (l i))
    (hcol : ∀ i, (univ.filter fun k => G.Adj (p k) (l i)).card ≤ d)
    (hrow : ∀ j, (univ.filter fun k => G.Adj (p j) (l k)).card ≤ d)
    (F : Finset (Finset (Fin n)))
    (hcover : ∀ W ∈ F, ∀ i, p i ∈ W ∨ l i ∈ W)
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∃ t : ℕ, r ≤ (2 * d - 1) * t ∧ 2 ^ t ≤ F.card := by
  classical
  let J : Fin r → Fin r → Prop := fun i j => G.Adj (p i) (l j)
  let f : Bool × Fin r → Fin n
    | (false, i) => p i
    | (true, i) => l i
  let Q : Finset (Fin n) → Finset (Bool × Fin r) :=
    fun W => univ.filter fun u => f u ∈ W
  have hQcover : ∀ W ∈ F.image Q, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W := by
    intro W hW i
    obtain ⟨V, hVF, rfl⟩ := mem_image.mp hW
    rcases hcover V hVF i with hpW | hlW
    · exact Or.inl (by simpa [Q, f] using hpW)
    · exact Or.inr (by simpa [Q, f] using hlW)
  have hQmiss : ∀ S, Independent J S → ∃ W ∈ F.image Q, Disjoint W S := by
    intro S hS
    have himg : ∀ u ∈ S.image f, ∀ v ∈ S.image f, ¬ G.Adj u v := by
      intro u hu v hv huv
      obtain ⟨⟨tu, iu⟩, hiu, rfl⟩ := mem_image.mp hu
      obtain ⟨⟨tv, iv⟩, hiv, rfl⟩ := mem_image.mp hv
      cases tu <;> cases tv
      · exact hpp iu iv huv
      · exact hS iu iv hiu hiv huv
      · exact hS iv iu hiv hiu huv.symm
      · exact hll iu iv huv
    obtain ⟨W, hWF, hWS⟩ := safe_clause_miss G F hsafe (S.image f) himg
    refine ⟨Q W, mem_image.mpr ⟨W, hWF, rfl⟩, ?_⟩
    apply Finset.disjoint_left.mpr
    intro u huQ huS
    have huW : f u ∈ W := (mem_filter.mp huQ).2
    have huImg : f u ∈ S.image f := mem_image.mpr ⟨u, huS, rfl⟩
    exact Finset.disjoint_left.mp hWS huW huImg
  obtain ⟨t, hbound, hpower⟩ :=
    clause_count_degree_exponential J d hdiag hcol hrow (F.image Q) hQcover hQmiss
  exact ⟨t, hbound, le_trans hpower card_image_le⟩


end InducedMatching

namespace MatchingCertificate

open Finset

lemma witness_family_bound {r m : ℕ} (I : Fin r → Fin r → Prop)
    (S : Fin m → Finset (Bool × Fin r))
    (hind : ∀ i a b, (false, a) ∈ S i → (true, b) ∈ S i → ¬ I a b)
    (hsep : ∀ i j, i ≠ j → ∃ a,
      (false, a) ∈ S i ∪ S j ∧ (true, a) ∈ S i ∪ S j)
    (F : Finset (Finset (Bool × Fin r)))
    (hcover : ∀ W ∈ F, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W)
    (hsafe : ∀ x : Bool × Fin r → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ i j, I i j ∧ x (false, i) = true ∧ x (true, j) = true) :
    m ≤ F.card := by
  classical
  have hmiss : ∀ i, ∃ W ∈ F, Disjoint W (S i) := by
    intro i
    by_contra hn
    push Not at hn
    let x : Bool × Fin r → Bool := fun u => decide (u ∈ S i)
    have hx : ∀ W ∈ F, ∃ u ∈ W, x u = true := by
      intro W hWF
      have hint : ∃ u ∈ W, u ∈ S i := by
        by_contra hnone
        push Not at hnone
        exact hn W hWF (Finset.disjoint_left.mpr hnone)
      obtain ⟨u, huW, huS⟩ := hint
      exact ⟨u, huW, by simp [x, huS]⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hsafe x hx
    exact hind i a b (by simpa [x] using ha) (by simpa [x] using hb) hab
  choose W hWF hdis using hmiss
  let f : Fin m → {W // W ∈ F} := fun i => ⟨W i, hWF i⟩
  have hf : Function.Injective f := by
    intro i j heq
    by_contra hij
    obtain ⟨a, ha, hb⟩ := hsep i j hij
    have he : W i = W j := congrArg Subtype.val heq
    have hd : Disjoint (W i) (S i ∪ S j) := by
      apply Finset.disjoint_union_right.mpr
      exact ⟨hdis i, he ▸ hdis j⟩
    rcases hcover (W i) (hWF i) a with hp | hl
    · exact Finset.disjoint_left.mp hd hp ha
    · exact Finset.disjoint_left.mp hd hl hb
  simpa using Fintype.card_le_of_injective f hf

def maskSet {r : ℕ} (row : ℕ × ℕ) : Finset (Bool × Fin r) :=
  univ.filter fun u => (if u.1 then row.2 else row.1).testBit u.2.val = true

lemma mem_maskSet_point {r : ℕ} (row : ℕ × ℕ) (a : Fin r) :
    (false, a) ∈ maskSet row ↔ row.1.testBit a.val = true := by
  simp [maskSet]

lemma mem_maskSet_line {r : ℕ} (row : ℕ × ℕ) (a : Fin r) :
    (true, a) ∈ maskSet row ↔ row.2.testBit a.val = true := by
  simp [maskSet]

lemma mask_family_bound {r m : ℕ} (I : Fin r → Fin r → Prop)
    (rows : Fin m → ℕ × ℕ)
    (hind : ∀ i a b, (rows i).1.testBit a.val = true →
      (rows i).2.testBit b.val = true → ¬ I a b)
    (hsep : ∀ i j, i ≠ j → ∃ a : Fin r,
      ((rows i).1.testBit a.val = true ∨ (rows j).1.testBit a.val = true) ∧
      ((rows i).2.testBit a.val = true ∨ (rows j).2.testBit a.val = true))
    (F : Finset (Finset (Bool × Fin r)))
    (hcover : ∀ W ∈ F, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W)
    (hsafe : ∀ x : Bool × Fin r → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ i j, I i j ∧ x (false, i) = true ∧ x (true, j) = true) :
    m ≤ F.card := by
  apply witness_family_bound I (fun i => maskSet (rows i)) ?_ ?_ F hcover hsafe
  · intro i a b ha hb
    exact hind i a b ((mem_maskSet_point _ _).mp ha) ((mem_maskSet_line _ _).mp hb)
  · intro i j hij
    obtain ⟨a, ha, hb⟩ := hsep i j hij
    exact ⟨a, by simpa only [Finset.mem_union, mem_maskSet_point] using ha,
      by simpa only [Finset.mem_union, mem_maskSet_line] using hb⟩

end MatchingCertificate

namespace MatchingCertificate

def inc7 (a b : Fin 7) : Prop := a = b ∨ a = b + 1 ∨ a = b + 3

lemma inc7_diagonal (a : Fin 7) : inc7 a a := Or.inl rfl

def rows7 (i : Fin 23) : ℕ × ℕ :=
  ([(0, 127), (1, 46), (2, 92), (4, 57), (5, 40), (8, 114), (10, 80), (16, 101), (20, 33), (29, 32), (32, 75), (33, 10), (39, 8), (40, 66), (58, 64), (64, 23), (66, 20), (78, 16), (80, 5), (83, 4), (105, 2), (116, 1), (127, 0)] : List (ℕ × ℕ)).getD i.val (0, 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma rows7_independent : ∀ (i : Fin 23) (a b : Fin 7),
    (rows7 i).1.testBit a.val = true →
    (rows7 i).2.testBit b.val = true → ¬ inc7 a b := by
  unfold inc7
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma rows7_separated : ∀ (i j : Fin 23), i ≠ j → ∃ a : Fin 7,
    ((rows7 i).1.testBit a.val = true ∨ (rows7 j).1.testBit a.val = true) ∧
    ((rows7 i).2.testBit a.val = true ∨ (rows7 j).2.testBit a.val = true) := by
  decide +kernel

lemma safe_matching_cnf_7_lower
    (F : Finset (Finset (Bool × Fin 7)))
    (hcover : ∀ W ∈ F, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W)
    (hsafe : ∀ x : Bool × Fin 7 → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ i j, inc7 i j ∧ x (false, i) = true ∧ x (true, j) = true) :
    23 ≤ F.card :=
  mask_family_bound inc7 rows7 rows7_independent rows7_separated F hcover hsafe

end MatchingCertificate

namespace MatchingCertificate

def inc13 (a b : Fin 13) : Prop := a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9

lemma inc13_diagonal (a : Fin 13) : inc13 a a := Or.inl rfl

def rows13 (i : Fin 158) : ℕ × ℕ :=
  ([(0, 8191), (1, 3054), (2, 6108), (4, 4025), (5, 2984), (8, 8050), (10, 5968), (16, 7909), (20, 3745), (25, 2656), (32, 7627), (33, 2506), (40, 7490), (50, 5312), (64, 7063), (65, 2950), (66, 5012), (80, 6789), (83, 644), (100, 2433), (101, 2432), (128, 5935), (129, 814), (130, 5900), (132, 1833), (133, 808), (160, 5387), (166, 1288), (200, 4866), (202, 4864), (256, 3679), (257, 2638), (258, 1628), (260, 3609), (264, 3666), (266, 1616), (320, 2583), (321, 2566), (332, 2576), (349, 2560), (400, 1541), (404, 1537), (467, 516), (512, 7358), (514, 5276), (516, 3256), (520, 7218), (528, 7332), (532, 3232), (640, 5166), (642, 5132), (664, 5152), (698, 5120), (800, 3082), (808, 3074), (934, 1032), (1024, 6525), (1027, 332), (1028, 2361), (1032, 6512), (1040, 6245), (1056, 6473), (1064, 6464), (1191, 264), (1280, 2141), (1283, 76), (1284, 2073), (1328, 2113), (1337, 2112), (1396, 2049), (1541, 2088), (1565, 2080), (1600, 6164), (1616, 6148), (1829, 2056), (1868, 2064), (1917, 2048), (2048, 4859), (2049, 746), (2054, 664), (2056, 4722), (2064, 4833), (2073, 608), (2080, 4299), (2081, 202), (2112, 4755), (2128, 4737), (2135, 640), (2382, 528), (2433, 522), (2439, 520), (2505, 514), (2527, 512), (2560, 4282), (2566, 152), (2568, 4146), (2656, 4226), (2674, 4224), (2792, 4098), (2977, 10), (3082, 4176), (3130, 4160), (3200, 4137), (3232, 4105), (3658, 4112), (3717, 40), (3736, 4128), (3834, 4096), (4007, 8), (4096, 1527), (4098, 1492), (4108, 1328), (4112, 1253), (4128, 1475), (4137, 322), (4146, 1216), (4160, 407), (4162, 404), (4224, 1319), (4256, 1283), (4270, 1280), (4329, 258), (4609, 166), (4691, 132), (4737, 38), (4764, 1056), (4866, 1044), (4878, 1040), (5010, 1028), (5054, 1024), (5120, 373), (5132, 304), (5136, 101), (5163, 320), (5312, 261), (5315, 260), (5348, 257), (5359, 256), (5584, 5), (5954, 20), (6099, 4), (6164, 161), (6260, 129), (6400, 83), (6441, 66), (6464, 19), (6677, 160), (6753, 130), (6775, 128), (7145, 2), (7316, 33), (7434, 80), (7472, 65), (7483, 64), (7668, 1), (7837, 32), (8014, 16), (8191, 0)] : List (ℕ × ℕ)).getD i.val (0, 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma rows13_independent : ∀ (i : Fin 158) (a b : Fin 13),
    (rows13 i).1.testBit a.val = true →
    (rows13 i).2.testBit b.val = true → ¬ inc13 a b := by
  unfold inc13
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma rows13_separated : ∀ (i j : Fin 158), i ≠ j → ∃ a : Fin 13,
    ((rows13 i).1.testBit a.val = true ∨ (rows13 j).1.testBit a.val = true) ∧
    ((rows13 i).2.testBit a.val = true ∨ (rows13 j).2.testBit a.val = true) := by
  intro i
  fin_cases i <;> decide +kernel

lemma safe_matching_cnf_13_lower
    (F : Finset (Finset (Bool × Fin 13)))
    (hcover : ∀ W ∈ F, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W)
    (hsafe : ∀ x : Bool × Fin 13 → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ i j, inc13 i j ∧ x (false, i) = true ∧ x (true, j) = true) :
    158 ≤ F.card :=
  mask_family_bound inc13 rows13 rows13_independent rows13_separated F hcover hsafe

end MatchingCertificate

namespace InducedMatching

open Finset
open PEqualNP.Outside.L_meta_2583.MatchingSurplus

variable {r : ℕ} (I : Fin r → Fin r → Prop) [DecidableRel I]

lemma exists_maximum_index_independent :
    ∃ A : Finset (Fin r), IndexIndependent I A ∧
      ∀ B, IndexIndependent I B → B.card ≤ A.card := by
  classical
  have hex : ∃ k : ℕ, ∃ A : Finset (Fin r), IndexIndependent I A ∧ r - A.card = k := by
    refine ⟨r, ∅, ?_, by simp⟩
    intro a ha
    simp at ha
  obtain ⟨A, hA, hmin⟩ := Nat.find_spec hex
  refine ⟨A, hA, ?_⟩
  intro B hB
  have hfind := Nat.find_min' hex (show ∃ C : Finset (Fin r),
      IndexIndependent I C ∧ r - C.card = r - B.card from ⟨B, hB, rfl⟩)
  have haCard : A.card ≤ r := by simpa using card_le_univ A
  have hbCard : B.card ≤ r := by simpa using card_le_univ B
  omega

lemma row_offdiagonal_independent (hdiag : ∀ i, I i i)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (i : Fin r) : IndexIndependent I ((univ.filter fun k => I i k).erase i) := by
  intro a ha b hb hab habI
  obtain ⟨hai, ha⟩ := mem_erase.mp ha
  obtain ⟨hbi, hb⟩ := mem_erase.mp hb
  exact hfour i a a b hai.symm hab
    ⟨(mem_filter.mp ha).2, (mem_filter.mp hb).2, hdiag a, habI⟩

lemma column_offdiagonal_independent (hdiag : ∀ i, I i i)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (i : Fin r) : IndexIndependent I ((univ.filter fun k => I k i).erase i) := by
  intro a ha b hb hab habI
  obtain ⟨hai, ha⟩ := mem_erase.mp ha
  obtain ⟨hbi, hb⟩ := mem_erase.mp hb
  exact hfour a b i b hab hbi.symm
    ⟨(mem_filter.mp ha).2, habI, (mem_filter.mp hb).2, hdiag b⟩

lemma exists_quadratic_independent (hdiag : ∀ i, I i i)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d)) :
    ∃ A : Finset (Fin r), IndexIndependent I A ∧ r ≤ (2 * A.card + 1) * A.card := by
  classical
  obtain ⟨A, hA, hmax⟩ := exists_maximum_index_independent I
  have hcol : ∀ i, (univ.filter fun k => I k i).card ≤ A.card + 1 := by
    intro i
    have hb := hmax _ (column_offdiagonal_independent I hdiag hfour i)
    have heq : ((univ.filter fun k => I k i).erase i).card + 1 =
        (univ.filter fun k => I k i).card :=
      card_erase_add_one (mem_filter.mpr ⟨mem_univ i, hdiag i⟩)
    omega
  have hrow : ∀ i, (univ.filter fun k => I i k).card ≤ A.card + 1 := by
    intro i
    have hb := hmax _ (row_offdiagonal_independent I hdiag hfour i)
    have heq : ((univ.filter fun k => I i k).erase i).card + 1 =
        (univ.filter fun k => I i k).card :=
      card_erase_add_one (mem_filter.mpr ⟨mem_univ i, hdiag i⟩)
    omega
  obtain ⟨B, hB, hbound⟩ := exists_large_independent I (A.card + 1) hdiag hcol hrow
  have hcoef : 2 * (A.card + 1) - 1 = 2 * A.card + 1 := by omega
  rw [hcoef] at hbound
  exact ⟨A, hA, le_trans hbound (Nat.mul_le_mul_left _ (hmax B hB))⟩

lemma clause_count_quadratic_exponential (hdiag : ∀ i, I i i)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (F : Finset (Finset (Bool × Fin r)))
    (hcover : ∀ W ∈ F, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W)
    (hmiss : ∀ S, Independent I S → ∃ W ∈ F, Disjoint W S) :
    ∃ m : ℕ, r ≤ (2 * m + 1) * m ∧ 2 ^ m ≤ F.card := by
  obtain ⟨A, hA, hbound⟩ := exists_quadratic_independent I hdiag hfour
  exact ⟨A.card, hbound, independent_clauses_power I A hA F hcover hmiss⟩

lemma graph_matching_clause_count_quadratic_exponential {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hfour : PEqualNP.TopForm.NoFourCycle G)
    (p l : Fin r → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hpp : ∀ i j, ¬ G.Adj (p i) (p j)) (hll : ∀ i j, ¬ G.Adj (l i) (l j))
    (hdiag : ∀ i, G.Adj (p i) (l i))
    (F : Finset (Finset (Fin n)))
    (hcover : ∀ W ∈ F, ∀ i, p i ∈ W ∨ l i ∈ W)
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∃ m : ℕ, r ≤ (2 * m + 1) * m ∧ 2 ^ m ≤ F.card := by
  classical
  let J : Fin r → Fin r → Prop := fun i j => G.Adj (p i) (l j)
  let f : Bool × Fin r → Fin n
    | (false, i) => p i
    | (true, i) => l i
  let Q : Finset (Fin n) → Finset (Bool × Fin r) :=
    fun W => univ.filter fun u => f u ∈ W
  have hJfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (J a c ∧ J a d ∧ J b c ∧ J b d) := by
    intro a b c d hab hcd ⟨hac, had, hbc, hbd⟩
    have hpab : p a ≠ p b := fun heq => hab (hp heq)
    have heq : l c = l d := by
      apply Finset.card_le_one.mp (hfour (p a) (p b) hpab)
      · exact mem_filter.mpr ⟨mem_univ _, hac, hbc⟩
      · exact mem_filter.mpr ⟨mem_univ _, had, hbd⟩
    exact hcd (hl heq)
  have hQcover : ∀ W ∈ F.image Q, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W := by
    intro W hW i
    obtain ⟨V, hVF, rfl⟩ := mem_image.mp hW
    rcases hcover V hVF i with hpW | hlW
    · exact Or.inl (by simpa [Q, f] using hpW)
    · exact Or.inr (by simpa [Q, f] using hlW)
  have hQmiss : ∀ S, Independent J S → ∃ W ∈ F.image Q, Disjoint W S := by
    intro S hS
    have himg : ∀ u ∈ S.image f, ∀ v ∈ S.image f, ¬ G.Adj u v := by
      intro u hu v hv huv
      obtain ⟨⟨tu, iu⟩, hiu, rfl⟩ := mem_image.mp hu
      obtain ⟨⟨tv, iv⟩, hiv, rfl⟩ := mem_image.mp hv
      cases tu <;> cases tv
      · exact hpp iu iv huv
      · exact hS iu iv hiu hiv huv
      · exact hS iv iu hiv hiu huv.symm
      · exact hll iu iv huv
    obtain ⟨W, hWF, hWS⟩ := safe_clause_miss G F hsafe (S.image f) himg
    refine ⟨Q W, mem_image.mpr ⟨W, hWF, rfl⟩, ?_⟩
    apply Finset.disjoint_left.mpr
    intro u huQ huS
    have huW : f u ∈ W := (mem_filter.mp huQ).2
    have huImg : f u ∈ S.image f := mem_image.mpr ⟨u, huS, rfl⟩
    exact Finset.disjoint_left.mp hWS huW huImg
  obtain ⟨m, hbound, hpower⟩ := clause_count_quadratic_exponential J hdiag hJfour
    (F.image Q) hQcover hQmiss
  exact ⟨m, hbound, le_trans hpower card_image_le⟩


end InducedMatching

namespace H8Projected.SandwichBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.PurePointBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.ProjectedBudget

lemma pure_pool_of_positives {n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C) (H S : Finset (Fin n))
    (w : ℕ) (hvalid : w < n + C.gates.length)
    (hpos : ∀ p ∈ H, val C (List.ofFn (pairInput p p)) w = true)
    (hfalse : val C (List.ofFn (complementInput S)) w = false) :
    H.card - 1 ≤ (orPool C (complementInput S) C.gates.length).card := by
  classical
  have hsub : H ⊆ singletonSupport n C w := fun p hp => mem_support.2 (hpos p hp)
  have hc := Finset.card_le_card hsub
  have hb := frontier_budget hm rb (complementInput S) C.gates.length {w}
    (by simpa using hvalid) (by simpa using hfalse)
    (by intro u hu _; simpa only [Finset.mem_singleton.1 hu] using hvalid)
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at hb
  omega

lemma projected_pool_of_positives {n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C) (V H S : Finset (Fin n))
    (w : ℕ) (hvalid : w < n + C.gates.length) (hHV : H ⊆ V)
    (hpos : ∀ p ∈ H, val C (List.ofFn (pairInput p p)) w = true)
    (hfalse : val C (List.ofFn (projectedComplementInput V S)) w = false) :
    H.card - 1 ≤ (projectedOrPool C V S C.gates.length).card := by
  classical
  have hsub : H ⊆ projectedSupport n C V w := by
    intro p hp
    exact Finset.mem_inter.2 ⟨mem_support.2 (hpos p hp), hHV hp⟩
  have hc := Finset.card_le_card hsub
  have hb := support_frontier_budget hm rb (projectedSupport n C V)
    (projectedSupport_input V)
    (fun _ hk hop _ hw => projectedSupport_and V hk hop hw)
    (fun _ hk hop p => projectedSupport_or rb V hk hop p)
    (projectedComplementInput V S) C.gates.length {w}
    (by simpa using hvalid) (by simpa using hfalse)
    (by intro u hu _; simpa only [Finset.mem_singleton.1 hu] using hvalid)
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at hb
  change H.card - 1 ≤ (supportOrPool C (projectedSupport n C V)
    (projectedComplementInput V S) C.gates.length).card
  omega

lemma sandwich_multioutput_or_budget {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (V : Finset (Fin n)) (H S : ι → Finset (Fin n)) (output : ι → ℕ)
    (hvalid : ∀ i, output i < n + C.gates.length)
    (hHV : ∀ i, H i ⊆ V)
    (hpos : ∀ i, ∀ p ∈ H i, val C (List.ofFn (pairInput p p)) (output i) = true)
    (hfalse : ∀ i, val C (List.ofFn (projectedComplementInput V (S i))) (output i) = false)
    (hpair : ∀ i j, i ≠ j → ((S i ∩ V) ∩ (S j ∩ V)).card ≤ 1)
    (K W : Finset (Fin n)) (w : ℕ) (hWV : Disjoint W V)
    (hwvalid : w < n + C.gates.length)
    (hwpos : ∀ p ∈ K, val C (List.ofFn (pairInput p p)) w = true)
    (hwfalse : val C (List.ofFn (complementInput W)) w = false) :
    (∑ i, ((H i).card - 1)) + (K.card - 1) ≤ (orGates C).card := by
  classical
  let pools := fun i => projectedOrPool C V (S i) C.gates.length
  let U := Finset.univ.biUnion pools
  let P := orPool C (complementInput W) C.gates.length
  have hdis : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint pools := by
    intro i _ j _ hij
    exact projectedOrPool_disjoint hm (hpair i j hij) C.gates.length
  have hsum : (∑ i, ((H i).card - 1)) ≤ U.card := by
    calc
      _ ≤ ∑ i, (pools i).card := Finset.sum_le_sum fun i _ =>
        projected_pool_of_positives hm rb V (H i) (S i) (output i)
          (hvalid i) (hHV i) (hpos i) (hfalse i)
      _ = _ := (Finset.card_biUnion hdis).symm
  have hpoint : K.card - 1 ≤ P.card :=
    pure_pool_of_positives hm rb K W w hwvalid hwpos hwfalse
  have hUP : Disjoint U P := by
    apply Finset.disjoint_left.2
    intro k hkU hkP
    obtain ⟨i, _, hki⟩ := Finset.mem_biUnion.1 hkU
    exact Finset.disjoint_left.1 (point_projected_disjoint hm hWV C.gates.length) hkP hki
  have hsub : U ∪ P ⊆ orGates C := by
    intro k hk
    rcases Finset.mem_union.1 hk with hk | hk
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 hk
      obtain ⟨hk, hop, _⟩ := mem_supportOrPool.1 hi
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hop⟩
    · obtain ⟨hk, hop, _⟩ := mem_orPool.1 hk
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hop⟩
  calc
    _ ≤ U.card + P.card := Nat.add_le_add hsum hpoint
    _ = (U ∪ P).card := (Finset.card_union_of_disjoint hUP).symm
    _ ≤ _ := Finset.card_le_card hsub

end H8Projected.SandwichBudget

namespace H8Projected.GroupedSandwichBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.PurePointBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.ProjectedBudget

lemma pure_grouped_pool_of_positives {n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C) (H S : Finset (Fin n))
    (roots : Finset ℕ) (hvalid : ∀ w ∈ roots, w < n + C.gates.length)
    (hpos : ∀ p ∈ H, ∃ w ∈ roots, val C (List.ofFn (pairInput p p)) w = true)
    (hfalse : ∀ w ∈ roots, val C (List.ofFn (complementInput S)) w = false) :
    H.card ≤ (orPool C (complementInput S) C.gates.length).card + roots.card := by
  classical
  have hsub : H ⊆ roots.biUnion (singletonSupport n C) := by
    intro p hp
    obtain ⟨w, hw, ht⟩ := hpos p hp
    exact Finset.mem_biUnion.2 ⟨w, hw, mem_support.2 ht⟩
  have hb := frontier_budget hm rb (complementInput S) C.gates.length roots
    hvalid hfalse (fun w hw _ => hvalid w hw)
  have hc := Finset.card_le_card hsub
  omega

lemma projected_grouped_pool_of_positives {n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C) (V H S : Finset (Fin n))
    (roots : Finset ℕ) (hvalid : ∀ w ∈ roots, w < n + C.gates.length)
    (hHV : H ⊆ V)
    (hpos : ∀ p ∈ H, ∃ w ∈ roots, val C (List.ofFn (pairInput p p)) w = true)
    (hfalse : ∀ w ∈ roots,
      val C (List.ofFn (projectedComplementInput V S)) w = false) :
    H.card ≤ (projectedOrPool C V S C.gates.length).card + roots.card := by
  classical
  have hsub : H ⊆ roots.biUnion (projectedSupport n C V) := by
    intro p hp
    obtain ⟨w, hw, ht⟩ := hpos p hp
    exact Finset.mem_biUnion.2 ⟨w, hw, Finset.mem_inter.2 ⟨mem_support.2 ht, hHV hp⟩⟩
  have hb := support_frontier_budget hm rb (projectedSupport n C V)
    (projectedSupport_input V)
    (fun _ hk hop _ hw => projectedSupport_and V hk hop hw)
    (fun _ hk hop p => projectedSupport_or rb V hk hop p)
    (projectedComplementInput V S) C.gates.length roots
    hvalid hfalse (fun w hw _ => hvalid w hw)
  have hc := Finset.card_le_card hsub
  change H.card ≤ (supportOrPool C (projectedSupport n C V)
    (projectedComplementInput V S) C.gates.length).card + roots.card
  omega

lemma grouped_sandwich_multioutput_or_budget {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (V : Finset (Fin n)) (H S : ι → Finset (Fin n)) (roots : ι → Finset ℕ)
    (hvalid : ∀ i, ∀ w ∈ roots i, w < n + C.gates.length)
    (hHV : ∀ i, H i ⊆ V)
    (hpos : ∀ i, ∀ p ∈ H i, ∃ w ∈ roots i,
      val C (List.ofFn (pairInput p p)) w = true)
    (hfalse : ∀ i, ∀ w ∈ roots i,
      val C (List.ofFn (projectedComplementInput V (S i))) w = false)
    (hpair : ∀ i j, i ≠ j → ((S i ∩ V) ∩ (S j ∩ V)).card ≤ 1)
    (K W : Finset (Fin n)) (bases : Finset ℕ) (hWV : Disjoint W V)
    (hbvalid : ∀ w ∈ bases, w < n + C.gates.length)
    (hbpos : ∀ p ∈ K, ∃ w ∈ bases, val C (List.ofFn (pairInput p p)) w = true)
    (hbfalse : ∀ w ∈ bases, val C (List.ofFn (complementInput W)) w = false) :
    (∑ i, (H i).card) + K.card ≤
      (orGates C).card + (∑ i, (roots i).card) + bases.card := by
  classical
  let pools := fun i => projectedOrPool C V (S i) C.gates.length
  let U := Finset.univ.biUnion pools
  let P := orPool C (complementInput W) C.gates.length
  have hdis : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint pools := by
    intro i _ j _ hij
    exact projectedOrPool_disjoint hm (hpair i j hij) C.gates.length
  have hsum : (∑ i, (H i).card) ≤ U.card + ∑ i, (roots i).card := by
    calc
      _ ≤ ∑ i, ((pools i).card + (roots i).card) := Finset.sum_le_sum fun i _ =>
        projected_grouped_pool_of_positives hm rb V (H i) (S i) (roots i)
          (hvalid i) (hHV i) (hpos i) (hfalse i)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.card_biUnion hdis]
  have hpoint : K.card ≤ P.card + bases.card :=
    pure_grouped_pool_of_positives hm rb K W bases hbvalid hbpos hbfalse
  have hUP : Disjoint U P := by
    apply Finset.disjoint_left.2
    intro k hkU hkP
    obtain ⟨i, _, hki⟩ := Finset.mem_biUnion.1 hkU
    exact Finset.disjoint_left.1 (point_projected_disjoint hm hWV C.gates.length) hkP hki
  have hsub : U ∪ P ⊆ orGates C := by
    intro k hk
    rcases Finset.mem_union.1 hk with hk | hk
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 hk
      obtain ⟨hk, hop, _⟩ := mem_supportOrPool.1 hi
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hop⟩
    · obtain ⟨hk, hop, _⟩ := mem_orPool.1 hk
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hop⟩
  have htotal : U.card + P.card ≤ (orGates C).card := by
    rw [← Finset.card_union_of_disjoint hUP]
    exact Finset.card_le_card hsub
  omega

lemma grouped_sandwich_no_deficit {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (V : Finset (Fin n)) (H S : ι → Finset (Fin n)) (roots : ι → Finset ℕ)
    (hvalid : ∀ i, ∀ w ∈ roots i, w < n + C.gates.length)
    (hHV : ∀ i, H i ⊆ V)
    (hpos : ∀ i, ∀ p ∈ H i, ∃ w ∈ roots i,
      val C (List.ofFn (pairInput p p)) w = true)
    (hfalse : ∀ i, ∀ w ∈ roots i,
      val C (List.ofFn (projectedComplementInput V (S i))) w = false)
    (hpair : ∀ i j, i ≠ j → ((S i ∩ V) ∩ (S j ∩ V)).card ≤ 1)
    (K W : Finset (Fin n)) (bases : Finset ℕ) (hWV : Disjoint W V)
    (hbvalid : ∀ w ∈ bases, w < n + C.gates.length)
    (hbpos : ∀ p ∈ K, ∃ w ∈ bases, val C (List.ofFn (pairInput p p)) w = true)
    (hbfalse : ∀ w ∈ bases, val C (List.ofFn (complementInput W)) w = false)
    (hbalance : (∑ i, (roots i).card) ≤ K.card) :
    (∑ i, (H i).card) ≤ (orGates C).card + bases.card := by
  have h := grouped_sandwich_multioutput_or_budget hm rb V H S roots hvalid hHV hpos
    hfalse hpair K W bases hWV hbvalid hbpos hbfalse
  omega

end H8Projected.GroupedSandwichBudget

namespace MatchingCertificate

open Finset

lemma graph_cnf_transport {n r m : ℕ} (I : Fin r → Fin r → Prop)
    (hlower : ∀ F : Finset (Finset (Bool × Fin r)),
      (∀ W ∈ F, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W) →
      (∀ x : Bool × Fin r → Bool,
        (∀ W ∈ F, ∃ u ∈ W, x u = true) →
        ∃ i j, I i j ∧ x (false, i) = true ∧ x (true, j) = true) →
      m ≤ F.card)
    (G : SimpleGraph (Fin n)) (p l : Fin r → Fin n)
    (hpp : ∀ i j, ¬ G.Adj (p i) (p j))
    (hll : ∀ i j, ¬ G.Adj (l i) (l j))
    (hcross : ∀ i j, G.Adj (p i) (l j) → I i j)
    (F : Finset (Finset (Fin n)))
    (hcover : ∀ W ∈ F, ∀ i, p i ∈ W ∨ l i ∈ W)
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    m ≤ F.card := by
  classical
  let f : Bool × Fin r → Fin n
    | (false, i) => p i
    | (true, i) => l i
  let Q : Finset (Fin n) → Finset (Bool × Fin r) :=
    fun W => univ.filter fun u => f u ∈ W
  have hQcover : ∀ W ∈ F.image Q, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W := by
    intro W hW i
    obtain ⟨V, hVF, rfl⟩ := mem_image.mp hW
    rcases hcover V hVF i with hpW | hlW
    · exact Or.inl (by simpa [Q, f] using hpW)
    · exact Or.inr (by simpa [Q, f] using hlW)
  have hQsafe : ∀ x : Bool × Fin r → Bool,
      (∀ W ∈ F.image Q, ∃ u ∈ W, x u = true) →
      ∃ i j, I i j ∧ x (false, i) = true ∧ x (true, j) = true := by
    intro x hx
    let y : Fin n → Bool := fun a => decide (∃ u, f u = a ∧ x u = true)
    have hy : ∀ W ∈ F, ∃ a ∈ W, y a = true := by
      intro W hWF
      obtain ⟨u, huQ, hxu⟩ := hx (Q W) (mem_image.mpr ⟨W, hWF, rfl⟩)
      refine ⟨f u, (mem_filter.mp huQ).2, ?_⟩
      simp only [y, decide_eq_true_eq]
      exact ⟨u, rfl, hxu⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hsafe y hy
    obtain ⟨⟨ta, ia⟩, rfl, hxa⟩ : ∃ u, f u = a ∧ x u = true := by
      simpa [y] using ha
    obtain ⟨⟨tb, ib⟩, rfl, hxb⟩ : ∃ u, f u = b ∧ x u = true := by
      simpa [y] using hb
    cases ta <;> cases tb
    · exact False.elim (hpp ia ib hab)
    · exact ⟨ia, ib, hcross ia ib hab, hxa, hxb⟩
    · exact ⟨ib, ia, hcross ib ia hab.symm, hxb, hxa⟩
    · exact False.elim (hll ia ib hab)
  exact le_trans (hlower (F.image Q) hQcover hQsafe) card_image_le

end PEqualNP.Outside.L_meta_2583.MatchingCertificate

namespace PEqualNP.Outside.L_meta_2583.MatchingCertificate

lemma graph_safe_matching_cnf_7_lower {n : ℕ}
    (G : SimpleGraph (Fin n)) (p l : Fin 7 → Fin n)
    (hpp : ∀ i j, ¬ G.Adj (p i) (p j))
    (hll : ∀ i j, ¬ G.Adj (l i) (l j))
    (hcross : ∀ i j, G.Adj (p i) (l j) → inc7 i j)
    (F : Finset (Finset (Fin n)))
    (hcover : ∀ W ∈ F, ∀ i, p i ∈ W ∨ l i ∈ W)
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    23 ≤ F.card :=
  graph_cnf_transport inc7 safe_matching_cnf_7_lower G p l hpp hll hcross F hcover hsafe

lemma graph_safe_matching_cnf_13_lower {n : ℕ}
    (G : SimpleGraph (Fin n)) (p l : Fin 13 → Fin n)
    (hpp : ∀ i j, ¬ G.Adj (p i) (p j))
    (hll : ∀ i j, ¬ G.Adj (l i) (l j))
    (hcross : ∀ i j, G.Adj (p i) (l j) → inc13 i j)
    (F : Finset (Finset (Fin n)))
    (hcover : ∀ W ∈ F, ∀ i, p i ∈ W ∨ l i ∈ W)
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    158 ≤ F.card :=
  graph_cnf_transport inc13 safe_matching_cnf_13_lower G p l hpp hll hcross F hcover hsafe

end MatchingCertificate

end PEqualNP.Outside.L_meta_2583
