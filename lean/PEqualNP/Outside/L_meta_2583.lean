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

def rows13Data : List (ℕ × ℕ) := [(0, 8191), (1, 3054), (2, 6108), (4, 4025), (5, 2984), (8, 8050), (10, 5968), (16, 7909), (20, 3745), (25, 2656), (32, 7627), (33, 2506), (40, 7490), (50, 5312), (64, 7063), (65, 2950), (66, 5012), (80, 6789), (83, 644), (100, 2433), (101, 2432), (128, 5935), (129, 814), (130, 5900), (132, 1833), (133, 808), (160, 5387), (166, 1288), (200, 4866), (202, 4864), (256, 3679), (257, 2638), (258, 1628), (260, 3609), (264, 3666), (266, 1616), (320, 2583), (321, 2566), (332, 2576), (349, 2560), (400, 1541), (404, 1537), (467, 516), (512, 7358), (514, 5276), (516, 3256), (520, 7218), (528, 7332), (532, 3232), (640, 5166), (642, 5132), (664, 5152), (698, 5120), (800, 3082), (808, 3074), (934, 1032), (1024, 6525), (1027, 332), (1028, 2361), (1032, 6512), (1040, 6245), (1056, 6473), (1064, 6464), (1191, 264), (1280, 2141), (1283, 76), (1284, 2073), (1328, 2113), (1337, 2112), (1396, 2049), (1541, 2088), (1565, 2080), (1600, 6164), (1616, 6148), (1829, 2056), (1868, 2064), (1917, 2048), (2048, 4859), (2049, 746), (2054, 664), (2056, 4722), (2064, 4833), (2073, 608), (2080, 4299), (2081, 202), (2112, 4755), (2128, 4737), (2135, 640), (2382, 528), (2433, 522), (2439, 520), (2505, 514), (2527, 512), (2560, 4282), (2566, 152), (2568, 4146), (2656, 4226), (2674, 4224), (2792, 4098), (2977, 10), (3082, 4176), (3130, 4160), (3200, 4137), (3232, 4105), (3658, 4112), (3717, 40), (3736, 4128), (3834, 4096), (4007, 8), (4096, 1527), (4098, 1492), (4108, 1328), (4112, 1253), (4128, 1475), (4137, 322), (4146, 1216), (4160, 407), (4162, 404), (4224, 1319), (4256, 1283), (4270, 1280), (4329, 258), (4609, 166), (4691, 132), (4737, 38), (4764, 1056), (4866, 1044), (4878, 1040), (5010, 1028), (5054, 1024), (5120, 373), (5132, 304), (5136, 101), (5163, 320), (5312, 261), (5315, 260), (5348, 257), (5359, 256), (5584, 5), (5954, 20), (6099, 4), (6164, 161), (6260, 129), (6400, 83), (6441, 66), (6464, 19), (6677, 160), (6753, 130), (6775, 128), (7145, 2), (7316, 33), (7434, 80), (7472, 65), (7483, 64), (7668, 1), (7837, 32), (8014, 16), (8191, 0)]

def rows13 (i : Fin 158) : ℕ × ℕ := rows13Data.getD i.val (0, 0)

namespace ListCheck

lemma shared_bit {r : ℕ} (a b c d : ℕ) (ha : a < 2^r) (hb : b < 2^r)
    (hn : (a ||| b) &&& (c ||| d) ≠ 0) :
    ∃ i : Fin r, (a.testBit i.val = true ∨ b.testBit i.val = true) ∧
      (c.testBit i.val = true ∨ d.testBit i.val = true) := by
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hn
  have hu := Nat.or_lt_two_pow ha hb
  have hz : (a ||| b) &&& (c ||| d) < 2^r := lt_of_le_of_lt Nat.and_le_left hu
  have hir : i < r := by
    by_contra h
    have hri : r ≤ i := by omega
    have hpow : 2^r ≤ 2^i := Nat.pow_le_pow_right (by decide) hri
    have hbit := Nat.ge_two_pow_of_testBit hi
    omega
  refine ⟨⟨i, hir⟩, ?_⟩
  simpa only [Nat.testBit_and, Nat.testBit_or, Bool.and_eq_true, Bool.or_eq_true] using hi

def rowsList : List (ℕ × ℕ) := rows13Data

set_option maxRecDepth 100000 in
lemma rowsList_length : rowsList.length = 158 := rfl

lemma rows13_eq (i : Fin 158) : rows13 i = rowsList.getD i.val (0, 0) := rfl

lemma rows13_mem (i : Fin 158) : rows13 i ∈ rowsList := by
  rw [rows13_eq, List.getD_eq_getElem rowsList (0, 0) (by rw [rowsList_length]; exact i.isLt)]
  exact List.getElem_mem _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma rowsList_bound : ∀ row ∈ rowsList, row.1 < 2^13 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma rowsList_pairwise : rowsList.Pairwise (fun a b =>
    (a.1 ||| b.1) &&& (a.2 ||| b.2) ≠ 0) := by
  decide +kernel

lemma rows_bound (i : Fin 158) : (rows13 i).1 < 2^13 :=
  rowsList_bound _ (rows13_mem i)

lemma row_masks_separated (i j : Fin 158) (hij : i ≠ j) :
    ((rows13 i).1 ||| (rows13 j).1) &&& ((rows13 i).2 ||| (rows13 j).2) ≠ 0 := by
  have hi : i.val < rowsList.length := by rw [rowsList_length]; exact i.isLt
  have hj : j.val < rowsList.length := by rw [rowsList_length]; exact j.isLt
  rw [rows13_eq, rows13_eq, List.getD_eq_getElem rowsList (0, 0) hi,
    List.getD_eq_getElem rowsList (0, 0) hj]
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact rowsList_pairwise.rel_getElem_of_lt hi hj hlt
  · exact (hij (Fin.ext heq)).elim
  · have h := rowsList_pairwise.rel_getElem_of_lt hj hi hgt
    simpa only [Nat.or_comm] using h

lemma rows_separated_fast : ∀ (i j : Fin 158), i ≠ j → ∃ a : Fin 13,
    ((rows13 i).1.testBit a.val = true ∨ (rows13 j).1.testBit a.val = true) ∧
    ((rows13 i).2.testBit a.val = true ∨ (rows13 j).2.testBit a.val = true) := by
  intro i j hij
  exact shared_bit _ _ _ _ (rows_bound i) (rows_bound j) (row_masks_separated i j hij)

def incidence_mask (a : Fin 13) : ℕ :=
  ([5137, 2083, 4166, 141, 282, 564, 1128, 2256, 4512, 833, 1666, 3332, 6664] : List ℕ).getD a.val 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma incidence_mask_spec : ∀ a b : Fin 13,
    (incidence_mask a).testBit b.val = true ↔ inc13 a b := by
  unfold inc13
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma rowsList_independent : ∀ row ∈ rowsList, ∀ a : Fin 13,
    row.1.testBit a.val = true → row.2 &&& incidence_mask a = 0 := by
  decide +kernel

lemma row_masks_independent (i : Fin 158) (a : Fin 13)
    (ha : (rows13 i).1.testBit a.val = true) : (rows13 i).2 &&& incidence_mask a = 0 :=
  rowsList_independent _ (rows13_mem i) a ha

lemma rows_independent_fast : ∀ (i : Fin 158) (a b : Fin 13),
    (rows13 i).1.testBit a.val = true →
    (rows13 i).2.testBit b.val = true → ¬ inc13 a b := by
  intro i a b ha hb hab
  have heq := congrArg (fun x : ℕ => x.testBit b.val) (row_masks_independent i a ha)
  have hbit := (incidence_mask_spec a b).mpr hab
  simp [Nat.testBit_and, hb, hbit] at heq

end ListCheck

lemma rows13_independent : ∀ (i : Fin 158) (a b : Fin 13),
    (rows13 i).1.testBit a.val = true →
    (rows13 i).2.testBit b.val = true → ¬ inc13 a b :=
  ListCheck.rows_independent_fast

lemma rows13_separated : ∀ (i j : Fin 158), i ≠ j → ∃ a : Fin 13,
    ((rows13 i).1.testBit a.val = true ∨ (rows13 j).1.testBit a.val = true) ∧
    ((rows13 i).2.testBit a.val = true ∨ (rows13 j).2.testBit a.val = true) :=
  ListCheck.rows_separated_fast


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

end MatchingCertificate

namespace MatchingCertificate

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

namespace GlobalHeavy

open Finset
open PEqualNP.Outside.L_meta_2583

lemma heavy_clause_count {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (P A : Finset (Fin n)) (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (F : Finset (Finset (Fin n)))
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ u v, H.Adj u v →
      ∀ W ∈ F, ∃ a ∈ W, a = u ∨ a = v)
    (hAP : A ⊆ P) (hheavy : ∀ u ∈ A, 2 ≤ (H.neighborFinset u).card) :
    A.card + 1 ≤ F.card := by
  classical
  obtain ⟨hFc, hcomplete⟩ := RelativeCnf.relative_clause_properties G H F hsafe haccept
  have hactive : ∀ u ∈ A, (H.neighborFinset u).Nonempty := by
    intro u hu
    apply Finset.card_pos.mp
    have hh := hheavy u hu
    omega
  obtain ⟨W₀, hW₀F, hW₀P, hAW₀⟩ :=
    RelativeCnf.relative_base_clause G H P A hcover hP hHG hAP hactive F hFc hcomplete
  have hchoices : ∀ u : Fin n, ∃ W ∈ F, W ⊆ P.erase u ∪ G.neighborFinset u := by
    intro u
    exact hcomplete _ (Cnf.cover_swap G P hcover u)
  choose K hKF hKsub using hchoices
  have hlow : ∀ u ∈ A, H.neighborFinset u ⊆ K u \ P := by
    intro u hu w hw
    have huK : u ∉ K u := fun h => Cnf.not_mem_swap G P u (hKsub u h)
    have hwK : w ∈ K u :=
      (hFc (K u) (hKF u) u w (H.mem_neighborFinset u w |>.mp hw)).resolve_left huK
    exact mem_sdiff.mpr ⟨hwK,
      RelativeCnf.relative_neighbor_not_point G H P hP hHG (hAP hu) hw⟩
  have hhigh : ∀ u ∈ A, K u \ P ⊆ G.neighborFinset u := by
    intro u hu w hw
    obtain ⟨hwK, hwP⟩ := mem_sdiff.mp hw
    rcases mem_union.mp (hKsub u hwK) with hwE | hwN
    · exact (hwP (mem_of_mem_erase hwE)).elim
    · exact hwN
  have hinj : Set.InjOn K A := by
    intro u hu v hv heq
    by_contra huv
    have hsmall := RelativeCnf.relative_projection_inter G hfour huv (hhigh u hu) (hhigh v hv)
    rw [← heq, Finset.inter_self] at hsmall
    have hrow := (Finset.card_le_card (hlow u hu)).trans hsmall
    have hh := hheavy u hu
    omega
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
  have hFcard := card_le_card hsub
  rw [card_insert_of_notMem hnot, card_image_of_injOn hinj] at hFcard
  exact hFcard

end GlobalHeavy

namespace GlobalHeavy

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open H8Projected.Repair H8Projected.PurePointBudget H8Projected.ProjectedBudget

lemma active_source_sum {n B : ℕ} (A : Fin B → Finset (Fin n))
    (wire : Fin B → Fin n → ℕ) :
    (∑ p : Fin n, ((univ.filter fun b : Fin B => p ∈ A b).image fun b => wire b p).card) ≤
      ∑ b : Fin B, (A b).card := by
  classical
  calc
    _ ≤ ∑ p : Fin n, (univ.filter fun b : Fin B => p ∈ A b).card :=
      sum_le_sum fun p _ => card_image_le
    _ = ∑ p : Fin n, ∑ b : Fin B, if p ∈ A b then 1 else 0 := by
      simp only [card_eq_sum_ones, sum_filter]
    _ = ∑ b : Fin B, ∑ p : Fin n, if p ∈ A b then 1 else 0 := sum_comm
    _ = _ := by simp

lemma global_circuit_cnf_family_frontier {n B : ℕ}
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (Hb : Fin B → SimpleGraph (Fin n)) [∀ b, DecidableRel (Hb b).Adj]
    (P : Finset (Fin n)) (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hparts : ∀ u v, H.Adj u v ↔ ∃ b : Fin B, (Hb b).Adj u v)
    (F : Fin B → Finset (Finset (Fin n)))
    (hsafe : ∀ b, ∀ x : Fin n → Bool,
      (∀ W ∈ F b, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ b, ∀ u v, (Hb b).Adj u v →
      ∀ W ∈ F b, ∃ a ∈ W, a = u ∨ a = v)
    (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack n C)
    (hwires : ∀ b, ∀ W ∈ F b, ∃ w : ℕ, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) w = decide (∃ u ∈ W, x u = true)) :
    H.edgeFinset.card + (P.filter fun u => (H.neighborFinset u).Nonempty).card ≤
      (orGates C).card + ∑ b : Fin B,
        ((P.filter fun u => ((Hb b).neighborFinset u).Nonempty).card + 1) := by
  classical
  let A := P.filter fun u => (H.neighborFinset u).Nonempty
  let Ab : Fin B → Finset (Fin n) := fun b =>
    P.filter fun u => ((Hb b).neighborFinset u).Nonempty
  have hAP : A ⊆ P := filter_subset _ _
  have hAbP (b : Fin B) : Ab b ⊆ P := filter_subset _ _
  have hHbG (b : Fin B) : Hb b ≤ G := by
    intro u v huv
    exact hHG ((hparts u v).2 ⟨b, huv⟩)
  have hFc : ∀ b, ∀ W ∈ F b, Cnf.Covers (Hb b) W :=
    fun b => (RelativeCnf.relative_clause_properties G (Hb b) (F b) (hsafe b) (haccept b)).1
  have hcomplete : ∀ b, ∀ U, Cnf.Covers G U → ∃ W ∈ F b, W ⊆ U :=
    fun b => (RelativeCnf.relative_clause_properties G (Hb b) (F b) (hsafe b) (haccept b)).2
  have hbase : ∀ b, ∃ W ∈ F b, W ⊆ P ∧ Ab b ⊆ W := by
    intro b
    exact RelativeCnf.relative_base_clause G (Hb b) P (Ab b) hcover hP (hHbG b)
      (hAbP b) (fun u hu => (mem_filter.1 hu).2) (F b) (hFc b) (hcomplete b)
  choose W₀ hW₀F hW₀P hAbW₀ using hbase
  have hchoices : ∀ b (p : Fin n), ∃ W ∈ F b,
      W ⊆ P.erase p ∪ G.neighborFinset p := by
    intro b p
    exact hcomplete b _ (Cnf.cover_swap G P hcover p)
  choose K hKF hKsub using hchoices
  have hKlow : ∀ b, ∀ p ∈ Ab b, (Hb b).neighborFinset p ⊆ K b p \ P := by
    intro b p hp u hu
    have hpK : p ∉ K b p := fun h => Cnf.not_mem_swap G P p (hKsub b p h)
    have huK : u ∈ K b p :=
      (hFc b (K b p) (hKF b p) p u ((Hb b).mem_neighborFinset p u |>.mp hu)).resolve_left hpK
    exact mem_sdiff.2 ⟨huK,
      RelativeCnf.relative_neighbor_not_point G (Hb b) P hP (hHbG b) (hAbP b hp) hu⟩
  have hKhigh : ∀ b p, K b p \ P ⊆ G.neighborFinset p := by
    intro b p u hu
    obtain ⟨huK, huP⟩ := mem_sdiff.1 hu
    rcases mem_union.1 (hKsub b p huK) with huE | huN
    · exact (huP (mem_of_mem_erase huE)).elim
    · exact huN
  have hkwires : ∀ b p, ∃ w : ℕ, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) w = decide (∃ u ∈ K b p, x u = true) :=
    fun b p => hwires b (K b p) (hKF b p)
  choose kw khvalid khcomp using hkwires
  have hbwires : ∀ b, ∃ w : ℕ, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) w = decide (∃ u ∈ W₀ b, x u = true) :=
    fun b => hwires b (W₀ b) (hW₀F b)
  choose bw bhvalid bhcomp using hbwires
  let V : Finset (Fin n) := univ \ P
  let R : Fin n → Finset ℕ := fun p =>
    (univ.filter fun b : Fin B => p ∈ Ab b).image fun b => kw b p
  let bases : Finset ℕ := univ.image bw
  let E : Fin n → Finset (Fin n) := fun p => if p ∈ A then H.neighborFinset p else ∅
  have hrvalid : ∀ p, ∀ w ∈ R p, w < n + C.gates.length := by
    intro p w hw
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hw
    exact khvalid b p
  have hEV : ∀ p, E p ⊆ V := by
    intro p u hu
    by_cases hp : p ∈ A
    · have huu : u ∈ H.neighborFinset p := by simpa [E, hp] using hu
      exact mem_sdiff.2 ⟨mem_univ _,
        RelativeCnf.relative_neighbor_not_point G H P hP hHG (hAP hp) huu⟩
    · simp [E, hp] at hu
  have hrpos : ∀ p, ∀ u ∈ E p, ∃ w ∈ R p,
      val C (List.ofFn (pairInput u u)) w = true := by
    intro p u hu
    by_cases hp : p ∈ A
    · have huu : u ∈ H.neighborFinset p := by simpa [E, hp] using hu
      obtain ⟨b, hbu⟩ := (hparts p u).1 ((H.mem_neighborFinset p u).1 huu)
      have hpAb : p ∈ Ab b := mem_filter.2 ⟨hAP hp, u, (Hb b).mem_neighborFinset p u |>.2 hbu⟩
      have huK := (mem_sdiff.1 (hKlow b p hpAb ((Hb b).mem_neighborFinset p u |>.2 hbu))).1
      refine ⟨kw b p, mem_image.2 ⟨b, mem_filter.2 ⟨mem_univ _, hpAb⟩, rfl⟩, ?_⟩
      rw [khcomp]
      exact decide_eq_true ⟨u, huK, by simp [pairInput]⟩
    · simp [E, hp] at hu
  have hrfalse : ∀ p, ∀ w ∈ R p,
      val C (List.ofFn (projectedComplementInput V (G.neighborFinset p))) w = false := by
    intro p w hw
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hw
    rw [khcomp]
    apply decide_eq_false
    rintro ⟨u, huK, hu⟩
    have hx : u ∈ V ∧ u ∉ G.neighborFinset p := by
      simpa [projectedComplementInput] using hu
    have huP : u ∉ P := (mem_sdiff.1 hx.1).2
    exact hx.2 (hKhigh b p (mem_sdiff.2 ⟨huK, huP⟩))
  have hpair : ∀ p q, p ≠ q →
      ((G.neighborFinset p ∩ V) ∩ (G.neighborFinset q ∩ V)).card ≤ 1 := by
    intro p q hpq
    exact RelativeCnf.relative_projection_inter G hfour hpq inter_subset_left inter_subset_left
  have hPV : Disjoint P V := by
    apply disjoint_left.2
    intro u huP huV
    exact (mem_sdiff.1 huV).2 huP
  have hbvalid : ∀ w ∈ bases, w < n + C.gates.length := by
    intro w hw
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hw
    exact bhvalid b
  have hbpos : ∀ p ∈ A, ∃ w ∈ bases, val C (List.ofFn (pairInput p p)) w = true := by
    intro p hp
    obtain ⟨u, hu⟩ := (mem_filter.1 hp).2
    obtain ⟨b, hbu⟩ := (hparts p u).1 ((H.mem_neighborFinset p u).1 hu)
    have hpAb : p ∈ Ab b := mem_filter.2
      ⟨hAP hp, u, (Hb b).mem_neighborFinset p u |>.2 hbu⟩
    refine ⟨bw b, mem_image.2 ⟨b, mem_univ _, rfl⟩, ?_⟩
    rw [bhcomp]
    exact decide_eq_true ⟨p, hAbW₀ b hpAb, by simp [pairInput]⟩
  have hbfalse : ∀ w ∈ bases, val C (List.ofFn (complementInput P)) w = false := by
    intro w hw
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hw
    rw [bhcomp]
    apply decide_eq_false
    rintro ⟨u, huW, hu⟩
    have huP : u ∉ P := by simpa [complementInput] using hu
    exact huP (hW₀P b huW)
  have hb := H8Projected.GroupedSandwichBudget.grouped_sandwich_multioutput_or_budget
    hm rb V E (fun p => G.neighborFinset p) R hrvalid hEV hrpos hrfalse hpair
    A P bases hPV hbvalid hbpos hbfalse
  have hroots : (∑ p : Fin n, (R p).card) ≤ ∑ b : Fin B, (Ab b).card :=
    active_source_sum Ab kw
  have hbases : bases.card ≤ B := le_trans card_image_le (by simp)
  have hedge : H.edgeFinset.card ≤ ∑ p : Fin n, (E p).card := by
    have hh := Cnf.edges_le_cover_degrees H A (RelativeCnf.active_points_cover G H P hcover hHG)
    have heq : (∑ p : Fin n, (E p).card) = ∑ p ∈ A, (H.neighborFinset p).card := by
      calc
        _ = ∑ p : Fin n, if p ∈ A then (H.neighborFinset p).card else 0 := by
          apply sum_congr rfl
          intro p hp
          by_cases ha : p ∈ A <;> simp [E, ha]
        _ = _ := by rw [← sum_filter]; simp
    rwa [heq]
  have hsum : (∑ b : Fin B, ((Ab b).card + 1)) = (∑ b : Fin B, (Ab b).card) + B := by
    simp [sum_add_distrib]
  change H.edgeFinset.card + A.card ≤ (orGates C).card + ∑ b : Fin B, ((Ab b).card + 1)
  rw [hsum]
  omega

lemma global_circuit_cnf_heavy_family_budget {n B : ℕ}
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (Hb : Fin B → SimpleGraph (Fin n)) [∀ b, DecidableRel (Hb b).Adj]
    (P : Finset (Fin n)) (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hparts : ∀ u v, H.Adj u v ↔ ∃ b : Fin B, (Hb b).Adj u v)
    (F : Fin B → Finset (Finset (Fin n)))
    (hsafe : ∀ b, ∀ x : Fin n → Bool,
      (∀ W ∈ F b, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ b, ∀ u v, (Hb b).Adj u v →
      ∀ W ∈ F b, ∃ a ∈ W, a = u ∨ a = v)
    (hheavy : ∀ b, ∀ p ∈ P, ((Hb b).neighborFinset p).Nonempty →
      2 ≤ ((Hb b).neighborFinset p).card)
    (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack n C)
    (hwires : ∀ b, ∀ W ∈ F b, ∃ w : ℕ, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) w = decide (∃ u ∈ W, x u = true)) :
    H.edgeFinset.card + (P.filter fun u => (H.neighborFinset u).Nonempty).card ≤
      (orGates C).card + ∑ b : Fin B, (F b).card := by
  classical
  have hf := global_circuit_cnf_family_frontier G H Hb P hcover hP hHG hfour hparts
    F hsafe haccept C hm rb hwires
  have hlocal : ∀ b : Fin B,
      (P.filter fun u => ((Hb b).neighborFinset u).Nonempty).card + 1 ≤ (F b).card := by
    intro b
    have hHbG : Hb b ≤ G := fun u v huv => hHG ((hparts u v).2 ⟨b, huv⟩)
    exact heavy_clause_count G (Hb b) P
      (P.filter fun u => ((Hb b).neighborFinset u).Nonempty)
      hcover hP hHbG hfour (F b) (hsafe b) (haccept b) (filter_subset _ _)
      (fun u hu => hheavy b u (mem_filter.1 hu).1 (mem_filter.1 hu).2)
  exact le_trans hf (Nat.add_le_add_left (sum_le_sum fun b _ => hlocal b) _)

lemma global_circuit_cnf_heavy_family_cover {n B : ℕ}
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (Hb : Fin B → SimpleGraph (Fin n)) [∀ b, DecidableRel (Hb b).Adj]
    (P : Finset (Fin n)) (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hparts : ∀ u v, H.Adj u v ↔ ∃ b : Fin B, (Hb b).Adj u v)
    (F : Fin B → Finset (Finset (Fin n)))
    (hsafe : ∀ b, ∀ x : Fin n → Bool,
      (∀ W ∈ F b, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ b, ∀ u v, (Hb b).Adj u v →
      ∀ W ∈ F b, ∃ a ∈ W, a = u ∨ a = v)
    (hheavy : ∀ b, ∀ p ∈ P, ((Hb b).neighborFinset p).Nonempty →
      2 ≤ ((Hb b).neighborFinset p).card)
    (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack n C)
    (hwires : ∀ b, ∀ W ∈ F b, ∃ w : ℕ, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) w = decide (∃ u ∈ W, x u = true)) :
    ∃ T : Finset (Fin n), Cnf.Covers H T ∧
      H.edgeFinset.card + T.card ≤ (orGates C).card + ∑ b : Fin B, (F b).card := by
  classical
  exact ⟨P.filter (fun u => (H.neighborFinset u).Nonempty),
    RelativeCnf.active_points_cover G H P hcover hHG,
    global_circuit_cnf_heavy_family_budget G H Hb P hcover hP hHG hfour hparts
      F hsafe haccept hheavy C hm rb hwires⟩

end GlobalHeavy

namespace H8Projected.LargeGroupedBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.PurePointBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.ProjectedBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.GroupedSandwichBudget

noncomputable def largeOrGates (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j =>
    (gateAt C j).op = GateOp.or ∧ 1 < (singletonSupport n C (n + j)).card

lemma largeOrGates_subset (n : ℕ) (C : Circuit) : largeOrGates n C ⊆ orGates C := by
  classical
  intro j hj
  obtain ⟨hj, hop, _⟩ := Finset.mem_filter.1 hj
  exact Finset.mem_filter.2 ⟨hj, hop⟩

lemma grouped_large_or_budget {n : ℕ} {ι : Type*}
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
      (largeOrGates n C).card + (∑ i, (roots i).card) + bases.card := by
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
  have hsub : U ∪ P ⊆ largeOrGates n C := by
    intro k hk
    rcases Finset.mem_union.1 hk with hk | hk
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 hk
      obtain ⟨hk, hop, hlarge, _⟩ := mem_supportOrPool.1 hi
      have hfull : 1 < (singletonSupport n C (n + k)).card :=
        lt_of_lt_of_le hlarge (Finset.card_le_card Finset.inter_subset_left)
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hop, hfull⟩
    · obtain ⟨hk, hop, hlarge, _⟩ := mem_orPool.1 hk
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hop, hlarge⟩
  have htotal : U.card + P.card ≤ (largeOrGates n C).card := by
    rw [← Finset.card_union_of_disjoint hUP]
    exact Finset.card_le_card hsub
  omega

end H8Projected.LargeGroupedBudget

namespace GlobalHeavy

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open H8Projected.Repair H8Projected.PurePointBudget H8Projected.ProjectedBudget

lemma global_large_cnf_family_frontier {n B : ℕ}
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (Hb : Fin B → SimpleGraph (Fin n)) [∀ b, DecidableRel (Hb b).Adj]
    (P : Finset (Fin n)) (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hparts : ∀ u v, H.Adj u v ↔ ∃ b : Fin B, (Hb b).Adj u v)
    (F : Fin B → Finset (Finset (Fin n)))
    (hsafe : ∀ b, ∀ x : Fin n → Bool,
      (∀ W ∈ F b, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ b, ∀ u v, (Hb b).Adj u v →
      ∀ W ∈ F b, ∃ a ∈ W, a = u ∨ a = v)
    (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack n C)
    (hwires : ∀ b, ∀ W ∈ F b, ∃ w : ℕ, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) w = decide (∃ u ∈ W, x u = true)) :
    H.edgeFinset.card + (P.filter fun u => (H.neighborFinset u).Nonempty).card ≤
      (H8Projected.LargeGroupedBudget.largeOrGates n C).card + ∑ b : Fin B,
        ((P.filter fun u => ((Hb b).neighborFinset u).Nonempty).card + 1) := by
  classical
  let A := P.filter fun u => (H.neighborFinset u).Nonempty
  let Ab : Fin B → Finset (Fin n) := fun b =>
    P.filter fun u => ((Hb b).neighborFinset u).Nonempty
  have hAP : A ⊆ P := filter_subset _ _
  have hAbP (b : Fin B) : Ab b ⊆ P := filter_subset _ _
  have hHbG (b : Fin B) : Hb b ≤ G := by
    intro u v huv
    exact hHG ((hparts u v).2 ⟨b, huv⟩)
  have hFc : ∀ b, ∀ W ∈ F b, Cnf.Covers (Hb b) W :=
    fun b => (RelativeCnf.relative_clause_properties G (Hb b) (F b) (hsafe b) (haccept b)).1
  have hcomplete : ∀ b, ∀ U, Cnf.Covers G U → ∃ W ∈ F b, W ⊆ U :=
    fun b => (RelativeCnf.relative_clause_properties G (Hb b) (F b) (hsafe b) (haccept b)).2
  have hbase : ∀ b, ∃ W ∈ F b, W ⊆ P ∧ Ab b ⊆ W := by
    intro b
    exact RelativeCnf.relative_base_clause G (Hb b) P (Ab b) hcover hP (hHbG b)
      (hAbP b) (fun u hu => (mem_filter.1 hu).2) (F b) (hFc b) (hcomplete b)
  choose W₀ hW₀F hW₀P hAbW₀ using hbase
  have hchoices : ∀ b (p : Fin n), ∃ W ∈ F b,
      W ⊆ P.erase p ∪ G.neighborFinset p := by
    intro b p
    exact hcomplete b _ (Cnf.cover_swap G P hcover p)
  choose K hKF hKsub using hchoices
  have hKlow : ∀ b, ∀ p ∈ Ab b, (Hb b).neighborFinset p ⊆ K b p \ P := by
    intro b p hp u hu
    have hpK : p ∉ K b p := fun h => Cnf.not_mem_swap G P p (hKsub b p h)
    have huK : u ∈ K b p :=
      (hFc b (K b p) (hKF b p) p u ((Hb b).mem_neighborFinset p u |>.mp hu)).resolve_left hpK
    exact mem_sdiff.2 ⟨huK,
      RelativeCnf.relative_neighbor_not_point G (Hb b) P hP (hHbG b) (hAbP b hp) hu⟩
  have hKhigh : ∀ b p, K b p \ P ⊆ G.neighborFinset p := by
    intro b p u hu
    obtain ⟨huK, huP⟩ := mem_sdiff.1 hu
    rcases mem_union.1 (hKsub b p huK) with huE | huN
    · exact (huP (mem_of_mem_erase huE)).elim
    · exact huN
  have hkwires : ∀ b p, ∃ w : ℕ, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) w = decide (∃ u ∈ K b p, x u = true) :=
    fun b p => hwires b (K b p) (hKF b p)
  choose kw khvalid khcomp using hkwires
  have hbwires : ∀ b, ∃ w : ℕ, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) w = decide (∃ u ∈ W₀ b, x u = true) :=
    fun b => hwires b (W₀ b) (hW₀F b)
  choose bw bhvalid bhcomp using hbwires
  let V : Finset (Fin n) := univ \ P
  let R : Fin n → Finset ℕ := fun p =>
    (univ.filter fun b : Fin B => p ∈ Ab b).image fun b => kw b p
  let bases : Finset ℕ := univ.image bw
  let E : Fin n → Finset (Fin n) := fun p => if p ∈ A then H.neighborFinset p else ∅
  have hrvalid : ∀ p, ∀ w ∈ R p, w < n + C.gates.length := by
    intro p w hw
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hw
    exact khvalid b p
  have hEV : ∀ p, E p ⊆ V := by
    intro p u hu
    by_cases hp : p ∈ A
    · have huu : u ∈ H.neighborFinset p := by simpa [E, hp] using hu
      exact mem_sdiff.2 ⟨mem_univ _,
        RelativeCnf.relative_neighbor_not_point G H P hP hHG (hAP hp) huu⟩
    · simp [E, hp] at hu
  have hrpos : ∀ p, ∀ u ∈ E p, ∃ w ∈ R p,
      val C (List.ofFn (pairInput u u)) w = true := by
    intro p u hu
    by_cases hp : p ∈ A
    · have huu : u ∈ H.neighborFinset p := by simpa [E, hp] using hu
      obtain ⟨b, hbu⟩ := (hparts p u).1 ((H.mem_neighborFinset p u).1 huu)
      have hpAb : p ∈ Ab b := mem_filter.2 ⟨hAP hp, u, (Hb b).mem_neighborFinset p u |>.2 hbu⟩
      have huK := (mem_sdiff.1 (hKlow b p hpAb ((Hb b).mem_neighborFinset p u |>.2 hbu))).1
      refine ⟨kw b p, mem_image.2 ⟨b, mem_filter.2 ⟨mem_univ _, hpAb⟩, rfl⟩, ?_⟩
      rw [khcomp]
      exact decide_eq_true ⟨u, huK, by simp [pairInput]⟩
    · simp [E, hp] at hu
  have hrfalse : ∀ p, ∀ w ∈ R p,
      val C (List.ofFn (projectedComplementInput V (G.neighborFinset p))) w = false := by
    intro p w hw
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hw
    rw [khcomp]
    apply decide_eq_false
    rintro ⟨u, huK, hu⟩
    have hx : u ∈ V ∧ u ∉ G.neighborFinset p := by
      simpa [projectedComplementInput] using hu
    have huP : u ∉ P := (mem_sdiff.1 hx.1).2
    exact hx.2 (hKhigh b p (mem_sdiff.2 ⟨huK, huP⟩))
  have hpair : ∀ p q, p ≠ q →
      ((G.neighborFinset p ∩ V) ∩ (G.neighborFinset q ∩ V)).card ≤ 1 := by
    intro p q hpq
    exact RelativeCnf.relative_projection_inter G hfour hpq inter_subset_left inter_subset_left
  have hPV : Disjoint P V := by
    apply disjoint_left.2
    intro u huP huV
    exact (mem_sdiff.1 huV).2 huP
  have hbvalid : ∀ w ∈ bases, w < n + C.gates.length := by
    intro w hw
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hw
    exact bhvalid b
  have hbpos : ∀ p ∈ A, ∃ w ∈ bases, val C (List.ofFn (pairInput p p)) w = true := by
    intro p hp
    obtain ⟨u, hu⟩ := (mem_filter.1 hp).2
    obtain ⟨b, hbu⟩ := (hparts p u).1 ((H.mem_neighborFinset p u).1 hu)
    have hpAb : p ∈ Ab b := mem_filter.2
      ⟨hAP hp, u, (Hb b).mem_neighborFinset p u |>.2 hbu⟩
    refine ⟨bw b, mem_image.2 ⟨b, mem_univ _, rfl⟩, ?_⟩
    rw [bhcomp]
    exact decide_eq_true ⟨p, hAbW₀ b hpAb, by simp [pairInput]⟩
  have hbfalse : ∀ w ∈ bases, val C (List.ofFn (complementInput P)) w = false := by
    intro w hw
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hw
    rw [bhcomp]
    apply decide_eq_false
    rintro ⟨u, huW, hu⟩
    have huP : u ∉ P := by simpa [complementInput] using hu
    exact huP (hW₀P b huW)
  have hb := H8Projected.LargeGroupedBudget.grouped_large_or_budget
    hm rb V E (fun p => G.neighborFinset p) R hrvalid hEV hrpos hrfalse hpair
    A P bases hPV hbvalid hbpos hbfalse
  have hroots : (∑ p : Fin n, (R p).card) ≤ ∑ b : Fin B, (Ab b).card :=
    active_source_sum Ab kw
  have hbases : bases.card ≤ B := le_trans card_image_le (by simp)
  have hedge : H.edgeFinset.card ≤ ∑ p : Fin n, (E p).card := by
    have hh := Cnf.edges_le_cover_degrees H A (RelativeCnf.active_points_cover G H P hcover hHG)
    have heq : (∑ p : Fin n, (E p).card) = ∑ p ∈ A, (H.neighborFinset p).card := by
      calc
        _ = ∑ p : Fin n, if p ∈ A then (H.neighborFinset p).card else 0 := by
          apply sum_congr rfl
          intro p hp
          by_cases ha : p ∈ A <;> simp [E, ha]
        _ = _ := by rw [← sum_filter]; simp
    rwa [heq]
  have hsum : (∑ b : Fin B, ((Ab b).card + 1)) = (∑ b : Fin B, (Ab b).card) + B := by
    simp [sum_add_distrib]
  change H.edgeFinset.card + A.card ≤ (H8Projected.LargeGroupedBudget.largeOrGates n C).card + ∑ b : Fin B, ((Ab b).card + 1)
  rw [hsum]
  omega

lemma global_large_cnf_heavy_family_budget {n B : ℕ}
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (Hb : Fin B → SimpleGraph (Fin n)) [∀ b, DecidableRel (Hb b).Adj]
    (P : Finset (Fin n)) (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hparts : ∀ u v, H.Adj u v ↔ ∃ b : Fin B, (Hb b).Adj u v)
    (F : Fin B → Finset (Finset (Fin n)))
    (hsafe : ∀ b, ∀ x : Fin n → Bool,
      (∀ W ∈ F b, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ b, ∀ u v, (Hb b).Adj u v →
      ∀ W ∈ F b, ∃ a ∈ W, a = u ∨ a = v)
    (hheavy : ∀ b, ∀ p ∈ P, ((Hb b).neighborFinset p).Nonempty →
      2 ≤ ((Hb b).neighborFinset p).card)
    (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack n C)
    (hwires : ∀ b, ∀ W ∈ F b, ∃ w : ℕ, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) w = decide (∃ u ∈ W, x u = true)) :
    H.edgeFinset.card + (P.filter fun u => (H.neighborFinset u).Nonempty).card ≤
      (H8Projected.LargeGroupedBudget.largeOrGates n C).card + ∑ b : Fin B, (F b).card := by
  classical
  have hf := global_large_cnf_family_frontier G H Hb P hcover hP hHG hfour hparts
    F hsafe haccept C hm rb hwires
  have hlocal : ∀ b : Fin B,
      (P.filter fun u => ((Hb b).neighborFinset u).Nonempty).card + 1 ≤ (F b).card := by
    intro b
    have hHbG : Hb b ≤ G := fun u v huv => hHG ((hparts u v).2 ⟨b, huv⟩)
    exact heavy_clause_count G (Hb b) P
      (P.filter fun u => ((Hb b).neighborFinset u).Nonempty)
      hcover hP hHbG hfour (F b) (hsafe b) (haccept b) (filter_subset _ _)
      (fun u hu => hheavy b u (mem_filter.1 hu).1 (mem_filter.1 hu).2)
  exact le_trans hf (Nat.add_le_add_left (sum_le_sum fun b _ => hlocal b) _)

lemma global_large_cnf_heavy_family_cover {n B : ℕ}
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (Hb : Fin B → SimpleGraph (Fin n)) [∀ b, DecidableRel (Hb b).Adj]
    (P : Finset (Fin n)) (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hparts : ∀ u v, H.Adj u v ↔ ∃ b : Fin B, (Hb b).Adj u v)
    (F : Fin B → Finset (Finset (Fin n)))
    (hsafe : ∀ b, ∀ x : Fin n → Bool,
      (∀ W ∈ F b, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ b, ∀ u v, (Hb b).Adj u v →
      ∀ W ∈ F b, ∃ a ∈ W, a = u ∨ a = v)
    (hheavy : ∀ b, ∀ p ∈ P, ((Hb b).neighborFinset p).Nonempty →
      2 ≤ ((Hb b).neighborFinset p).card)
    (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack n C)
    (hwires : ∀ b, ∀ W ∈ F b, ∃ w : ℕ, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) w = decide (∃ u ∈ W, x u = true)) :
    ∃ T : Finset (Fin n), Cnf.Covers H T ∧
      H.edgeFinset.card + T.card ≤ (H8Projected.LargeGroupedBudget.largeOrGates n C).card + ∑ b : Fin B, (F b).card := by
  classical
  exact ⟨P.filter (fun u => (H.neighborFinset u).Nonempty),
    RelativeCnf.active_points_cover G H P hcover hHG,
    global_large_cnf_heavy_family_budget G H Hb P hcover hP hHG hfour hparts
      F hsafe haccept hheavy C hm rb hwires⟩

end GlobalHeavy

namespace GlobalHeavy

open Finset
open PEqualNP.Outside.L_meta_2583

lemma row_distinct_clause_count {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (P A : Finset (Fin n)) (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (F : Finset (Finset (Fin n)))
    (hsafe : ∀ x : Fin n → Bool,
      (∀ W ∈ F, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ u v, H.Adj u v →
      ∀ W ∈ F, ∃ a ∈ W, a = u ∨ a = v)
    (hAP : A ⊆ P)
    (hactive : ∀ u ∈ A, (H.neighborFinset u).Nonempty)
    (hdistinct : ∀ u ∈ A, ∀ v ∈ A,
      H.neighborFinset u = H.neighborFinset v → u = v) :
    A.card + 1 ≤ F.card := by
  classical
  obtain ⟨hFc, hcomplete⟩ := RelativeCnf.relative_clause_properties G H F hsafe haccept
  obtain ⟨W₀, hW₀F, hW₀P, hAW₀⟩ :=
    RelativeCnf.relative_base_clause G H P A hcover hP hHG hAP hactive F hFc hcomplete
  have hchoices : ∀ u : Fin n, ∃ W ∈ F, W ⊆ P.erase u ∪ G.neighborFinset u := by
    intro u
    exact hcomplete _ (Cnf.cover_swap G P hcover u)
  choose K hKF hKsub using hchoices
  have hlow : ∀ u ∈ A, H.neighborFinset u ⊆ K u \ P := by
    intro u hu w hw
    have huK : u ∉ K u := fun h => Cnf.not_mem_swap G P u (hKsub u h)
    have hwK : w ∈ K u :=
      (hFc (K u) (hKF u) u w (H.mem_neighborFinset u w |>.mp hw)).resolve_left huK
    exact mem_sdiff.mpr ⟨hwK,
      RelativeCnf.relative_neighbor_not_point G H P hP hHG (hAP hu) hw⟩
  have hhigh : ∀ u ∈ A, K u \ P ⊆ G.neighborFinset u := by
    intro u hu w hw
    obtain ⟨hwK, hwP⟩ := mem_sdiff.mp hw
    rcases mem_union.mp (hKsub u hwK) with hwE | hwN
    · exact (hwP (mem_of_mem_erase hwE)).elim
    · exact hwN
  have hinj : Set.InjOn K A := by
    intro u hu v hv heq
    by_contra huv
    have hsmall := RelativeCnf.relative_projection_inter G hfour huv (hhigh u hu) (hhigh v hv)
    rw [← heq, Finset.inter_self] at hsmall
    have huone : 1 ≤ (H.neighborFinset u).card := (hactive u hu).card_pos
    have hvone : 1 ≤ (H.neighborFinset v).card := (hactive v hv).card_pos
    have hueq : H.neighborFinset u = K u \ P :=
      Finset.eq_of_subset_of_card_le (hlow u hu) (hsmall.trans huone)
    have hvsub : H.neighborFinset v ⊆ K u \ P := by
      rw [heq]
      exact hlow v hv
    have hveq : H.neighborFinset v = K u \ P :=
      Finset.eq_of_subset_of_card_le hvsub (hsmall.trans hvone)
    exact huv (hdistinct u hu v hv (hueq.trans hveq.symm))
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
  have hFcard := card_le_card hsub
  rw [card_insert_of_notMem hnot, card_image_of_injOn hinj] at hFcard
  exact hFcard

end GlobalHeavy

namespace GlobalHeavy

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open H8Projected.Repair H8Projected.PurePointBudget H8Projected.ProjectedBudget

lemma global_large_cnf_row_distinct_family_budget {n B : ℕ}
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (Hb : Fin B → SimpleGraph (Fin n)) [∀ b, DecidableRel (Hb b).Adj]
    (P : Finset (Fin n)) (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hparts : ∀ u v, H.Adj u v ↔ ∃ b : Fin B, (Hb b).Adj u v)
    (F : Fin B → Finset (Finset (Fin n)))
    (hsafe : ∀ b, ∀ x : Fin n → Bool,
      (∀ W ∈ F b, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ b, ∀ u v, (Hb b).Adj u v →
      ∀ W ∈ F b, ∃ a ∈ W, a = u ∨ a = v)
    (hrows : ∀ b, ∀ p ∈ P, ∀ q ∈ P,
      ((Hb b).neighborFinset p).Nonempty → ((Hb b).neighborFinset q).Nonempty →
      (Hb b).neighborFinset p = (Hb b).neighborFinset q → p = q)
    (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack n C)
    (hwires : ∀ b, ∀ W ∈ F b, ∃ w : ℕ, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) w = decide (∃ u ∈ W, x u = true)) :
    H.edgeFinset.card + (P.filter fun u => (H.neighborFinset u).Nonempty).card ≤
      (H8Projected.LargeGroupedBudget.largeOrGates n C).card + ∑ b : Fin B, (F b).card := by
  classical
  have hf := global_large_cnf_family_frontier G H Hb P hcover hP hHG hfour hparts
    F hsafe haccept C hm rb hwires
  have hlocal : ∀ b : Fin B,
      (P.filter fun u => ((Hb b).neighborFinset u).Nonempty).card + 1 ≤ (F b).card := by
    intro b
    have hHbG : Hb b ≤ G := fun u v huv => hHG ((hparts u v).2 ⟨b, huv⟩)
    exact row_distinct_clause_count G (Hb b) P
      (P.filter fun u => ((Hb b).neighborFinset u).Nonempty)
      hcover hP hHbG hfour (F b) (hsafe b) (haccept b) (filter_subset _ _)
      (fun u hu => (mem_filter.1 hu).2)
      (fun u hu v hv heq => hrows b u (mem_filter.1 hu).1 v (mem_filter.1 hv).1
        (mem_filter.1 hu).2 (mem_filter.1 hv).2 heq)
  exact le_trans hf (Nat.add_le_add_left (sum_le_sum fun b _ => hlocal b) _)

lemma global_large_cnf_row_distinct_family_cover {n B : ℕ}
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (Hb : Fin B → SimpleGraph (Fin n)) [∀ b, DecidableRel (Hb b).Adj]
    (P : Finset (Fin n)) (hcover : Cnf.Covers G P)
    (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ G.Adj a b)
    (hHG : H ≤ G) (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hparts : ∀ u v, H.Adj u v ↔ ∃ b : Fin B, (Hb b).Adj u v)
    (F : Fin B → Finset (Finset (Fin n)))
    (hsafe : ∀ b, ∀ x : Fin n → Bool,
      (∀ W ∈ F b, ∃ u ∈ W, x u = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ b, ∀ u v, (Hb b).Adj u v →
      ∀ W ∈ F b, ∃ a ∈ W, a = u ∨ a = v)
    (hrows : ∀ b, ∀ p ∈ P, ∀ q ∈ P,
      ((Hb b).neighborFinset p).Nonempty → ((Hb b).neighborFinset q).Nonempty →
      (Hb b).neighborFinset p = (Hb b).neighborFinset q → p = q)
    (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack n C)
    (hwires : ∀ b, ∀ W ∈ F b, ∃ w : ℕ, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) w = decide (∃ u ∈ W, x u = true)) :
    ∃ T : Finset (Fin n), Cnf.Covers H T ∧
      H.edgeFinset.card + T.card ≤
        (H8Projected.LargeGroupedBudget.largeOrGates n C).card + ∑ b : Fin B, (F b).card := by
  classical
  exact ⟨P.filter (fun u => (H.neighborFinset u).Nonempty),
    RelativeCnf.active_points_cover G H P hcover hHG,
    global_large_cnf_row_distinct_family_budget G H Hb P hcover hP hHG hfour hparts
      F hsafe haccept hrows C hm rb hwires⟩

end GlobalHeavy

namespace ThinBlock

open Finset

variable {n : ℕ}

def lines (W : Finset (Bool × Fin n)) : Finset (Fin n) :=
  univ.filter fun l => (true, l) ∈ W

def Accept (F : Finset (Finset (Bool × Fin n))) (p l : Fin n) : Prop :=
  ∀ W ∈ F, (false, p) ∈ W ∨ (true, l) ∈ W

def Thin (F : Finset (Finset (Bool × Fin n))) : Prop :=
  ∀ W ∈ F, (∃ p, (false, p) ∈ W) → (lines W).card ≤ 1

def Safe (I : Fin n → Fin n → Prop) (F : Finset (Finset (Bool × Fin n))) : Prop :=
  ∀ x : Bool × Fin n → Bool, (∀ W ∈ F, ∃ u ∈ W, x u = true) →
    ∃ p l, I p l ∧ x (false, p) = true ∧ x (true, l) = true

lemma accepted_edge (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hsafe : Safe I F)
    {p l : Fin n} (hacc : Accept F p l) : I p l := by
  classical
  let x : Bool × Fin n → Bool := fun u =>
    if u.1 then decide (u.2 = l) else decide (u.2 = p)
  have hh : ∀ W ∈ F, ∃ u ∈ W, x u = true := by
    intro W hW
    rcases hacc W hW with hp | hl
    · exact ⟨(false, p), hp, by simp [x]⟩
    · exact ⟨(true, l), hl, by simp [x]⟩
  obtain ⟨a, b, hab, ha, hb⟩ := hsafe x hh
  have hap : a = p := by simpa [x] using ha
  have hbl : b = l := by simpa [x] using hb
  simpa [hap, hbl] using hab

lemma two_points_active_line (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hthin : Thin F) (hsafe : Safe I F)
    {p q lp lq a l : Fin n} (hp : Accept F p lp) (hq : Accept F q lq)
    (hne : lp ≠ lq) (ha : Accept F a l) : I p l ∨ I q l := by
  classical
  let x : Bool × Fin n → Bool := fun u =>
    if u.1 then decide (u.2 = l) else decide (u.2 = p ∨ u.2 = q)
  have hh : ∀ W ∈ F, ∃ u ∈ W, x u = true := by
    intro W hW
    by_cases hpoint : ∃ z, (false, z) ∈ W
    · by_cases hpW : (false, p) ∈ W
      · exact ⟨(false, p), hpW, by simp [x]⟩
      by_cases hqW : (false, q) ∈ W
      · exact ⟨(false, q), hqW, by simp [x]⟩
      have hlp : (true, lp) ∈ W := (hp W hW).resolve_left hpW
      have hlq : (true, lq) ∈ W := (hq W hW).resolve_left hqW
      have heq : lp = lq := card_le_one.mp (hthin W hW hpoint) lp
        (mem_filter.mpr ⟨mem_univ _, hlp⟩) lq (mem_filter.mpr ⟨mem_univ _, hlq⟩)
      exact (hne heq).elim
    · have hlW : (true, l) ∈ W := (ha W hW).resolve_left (fun h => hpoint ⟨a, h⟩)
      exact ⟨(true, l), hlW, by simp [x]⟩
  obtain ⟨u, v, huv, hu, hv⟩ := hsafe x hh
  have hupq : u = p ∨ u = q := by simpa [x] using hu
  have hvl : v = l := by simpa [x] using hv
  rcases hupq with hup | huq
  · exact Or.inl (by simpa [hup, hvl] using huv)
  · exact Or.inr (by simpa [huq, hvl] using huv)

lemma four_column_obstruction (J : Fin 4 → Fin 4 → Prop)
    (hpair : ∀ a b, a ≠ b → ∀ j, J a j ∨ J b j)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (J a c ∧ J a d ∧ J b c ∧ J b d)) :
    False := by
  classical
  let C : Fin 4 → Finset (Fin 4) := fun j => univ.filter fun i => J i j
  have hcard : ∀ j, 3 ≤ (C j).card := by
    intro j
    have hcomp : (univ \ C j).card ≤ 1 := by
      apply card_le_one.mpr
      intro a ha b hb
      by_contra hab
      have haN : ¬ J a j := by
        intro h
        exact (mem_sdiff.mp ha).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
      have hbN : ¬ J b j := by
        intro h
        exact (mem_sdiff.mp hb).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
      exact (hpair a b hab j).elim haN hbN
    have hsum := card_sdiff_add_card_eq_card (subset_univ (C j))
    have huniv : (univ : Finset (Fin 4)).card = 4 := by simp
    omega
  have hinter : (C 0 ∩ C 1).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    by_contra hab
    exact hfour a b 0 1 hab (by decide)
      ⟨(mem_filter.mp (mem_inter.mp ha).1).2,
       (mem_filter.mp (mem_inter.mp ha).2).2,
       (mem_filter.mp (mem_inter.mp hb).1).2,
       (mem_filter.mp (mem_inter.mp hb).2).2⟩
  have hsum := card_union_add_card_inter (C 0) (C 1)
  have hunion : (C 0 ∪ C 1).card ≤ 4 := by simpa using card_le_univ (C 0 ∪ C 1)
  have h0 := hcard 0
  have h1 := hcard 1
  omega

lemma no_matching_four (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hthin : Thin F) (hsafe : Safe I F)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 4 → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i)) : False := by
  apply four_column_obstruction (fun a b => I (p a) (l b))
  · intro a b hab j
    exact two_points_active_line I F hthin hsafe (hacc a) (hacc b)
      (fun h => hab (hl h)) (hacc j)
  · intro a b c d hab hcd
    exact hfour (p a) (p b) (l c) (l d)
      (fun h => hab (hp h)) (fun h => hcd (hl h))

end ThinBlock

namespace ThinBlock

open Finset

lemma three_patterns (J : Fin 3 → Fin 3 → Prop)
    (hdiag : ∀ i, J i i)
    (hpair : ∀ a b, a ≠ b → ∀ j, J a j ∨ J b j)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (J a c ∧ J a d ∧ J b c ∧ J b d)) :
    (∀ i j, J i j ↔ i = j ∨ i = j + 1) ∨
      (∀ i j, J i j ↔ i = j ∨ i = j + 2) := by
  classical
  have hanti : ∀ a b, a ≠ b → ¬ (J a b ∧ J b a) := by
    intro a b hab ⟨habJ, hbaJ⟩
    exact hfour a b a b hab hab ⟨hdiag a, habJ, hbaJ, hdiag b⟩
  by_cases h01 : J 0 1
  · have h10 : ¬ J 1 0 := fun h => hanti 0 1 (by decide) ⟨h01, h⟩
    have h20 : J 2 0 := (hpair 1 2 (by decide) 0).resolve_left h10
    have h02 : ¬ J 0 2 := fun h => hanti 0 2 (by decide) ⟨h, h20⟩
    have h12 : J 1 2 := (hpair 0 1 (by decide) 2).resolve_left h02
    have h21 : ¬ J 2 1 := fun h => hanti 1 2 (by decide) ⟨h12, h⟩
    right
    intro i j
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      simp [hdiag, h01, h10, h20, h02, h12, h21]
  · have h21 : J 2 1 := (hpair 0 2 (by decide) 1).resolve_left h01
    have h12 : ¬ J 1 2 := fun h => hanti 1 2 (by decide) ⟨h, h21⟩
    have h02 : J 0 2 := (hpair 0 1 (by decide) 2).resolve_right h12
    have h20 : ¬ J 2 0 := fun h => hanti 0 2 (by decide) ⟨h02, h⟩
    have h10 : J 1 0 := (hpair 1 2 (by decide) 0).resolve_right h20
    left
    intro i j
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      simp [hdiag, h01, h10, h20, h02, h12, h21]

lemma two_of_three (P : Fin 3 → Prop)
    (hpair : ∀ a b, a ≠ b → P a ∨ P b) :
    ∃ a b, a ≠ b ∧ P a ∧ P b := by
  classical
  by_cases h0 : P 0
  · by_cases h1 : P 1
    · exact ⟨0, 1, by decide, h0, h1⟩
    · exact ⟨0, 2, by decide, h0, (hpair 1 2 (by decide)).resolve_left h1⟩
  · exact ⟨1, 2, by decide,
      (hpair 0 1 (by decide)).resolve_left h0,
      (hpair 0 2 (by decide)).resolve_left h0⟩

lemma pattern_common_line (J : Fin 3 → Fin 3 → Prop)
    (hshape : (∀ i j, J i j ↔ i = j ∨ i = j + 1) ∨
      (∀ i j, J i j ↔ i = j ∨ i = j + 2)) :
    ∀ a b, a ≠ b → ∃ c, J a c ∧ J b c := by
  intro a b hab
  rcases hshape with hshape | hshape
  · have h : ∀ a b : Fin 3, a ≠ b →
        ∃ c : Fin 3, (a = c ∨ a = c + 1) ∧ (b = c ∨ b = c + 1) := by decide
    obtain ⟨c, ha, hb⟩ := h a b hab
    exact ⟨c, (hshape a c).mpr ha, (hshape b c).mpr hb⟩
  · have h : ∀ a b : Fin 3, a ≠ b →
        ∃ c : Fin 3, (a = c ∨ a = c + 2) ∧ (b = c ∨ b = c + 2) := by decide
    obtain ⟨c, ha, hb⟩ := h a b hab
    exact ⟨c, (hshape a c).mpr ha, (hshape b c).mpr hb⟩

lemma pattern_common_point (J : Fin 3 → Fin 3 → Prop)
    (hshape : (∀ i j, J i j ↔ i = j ∨ i = j + 1) ∨
      (∀ i j, J i j ↔ i = j ∨ i = j + 2)) :
    ∀ a b, a ≠ b → ∃ c, J c a ∧ J c b := by
  intro a b hab
  rcases hshape with hshape | hshape
  · have h : ∀ a b : Fin 3, a ≠ b →
        ∃ c : Fin 3, (c = a ∨ c = a + 1) ∧ (c = b ∨ c = b + 1) := by decide
    obtain ⟨c, ha, hb⟩ := h a b hab
    exact ⟨c, (hshape c a).mpr ha, (hshape c b).mpr hb⟩
  · have h : ∀ a b : Fin 3, a ≠ b →
        ∃ c : Fin 3, (c = a ∨ c = a + 2) ∧ (c = b ∨ c = b + 2) := by decide
    obtain ⟨c, ha, hb⟩ := h a b hab
    exact ⟨c, (hshape c a).mpr ha, (hshape c b).mpr hb⟩

lemma pattern_missing_line (J : Fin 3 → Fin 3 → Prop)
    (hshape : (∀ i j, J i j ↔ i = j ∨ i = j + 1) ∨
      (∀ i j, J i j ↔ i = j ∨ i = j + 2)) : ∀ a, ∃ b, ¬ J a b := by
  intro a
  rcases hshape with hshape | hshape
  · have h : ∀ a : Fin 3, ∃ b : Fin 3, ¬ (a = b ∨ a = b + 1) := by decide
    obtain ⟨b, hb⟩ := h a
    exact ⟨b, fun hj => hb ((hshape a b).mp hj)⟩
  · have h : ∀ a : Fin 3, ∃ b : Fin 3, ¬ (a = b ∨ a = b + 2) := by decide
    obtain ⟨b, hb⟩ := h a
    exact ⟨b, fun hj => hb ((hshape a b).mp hj)⟩

lemma pattern_missing_away (J : Fin 3 → Fin 3 → Prop)
    (hshape : (∀ i j, J i j ↔ i = j ∨ i = j + 1) ∨
      (∀ i j, J i j ↔ i = j ∨ i = j + 2)) :
    ∀ j, ∃ k t, k ≠ j ∧ t ≠ j ∧ ¬ J k t := by
  intro j
  rcases hshape with hshape | hshape
  · have h : ∀ j : Fin 3, ∃ k t : Fin 3,
        k ≠ j ∧ t ≠ j ∧ ¬ (k = t ∨ k = t + 1) := by decide
    obtain ⟨k, t, hk, ht, hkt⟩ := h j
    exact ⟨k, t, hk, ht, fun hJ => hkt ((hshape k t).mp hJ)⟩
  · have h : ∀ j : Fin 3, ∃ k t : Fin 3,
        k ≠ j ∧ t ≠ j ∧ ¬ (k = t ∨ k = t + 2) := by decide
    obtain ⟨k, t, hk, ht, hkt⟩ := h j
    exact ⟨k, t, hk, ht, fun hJ => hkt ((hshape k t).mp hJ)⟩

variable {n : ℕ}

lemma matching_three_patterns (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hthin : Thin F) (hsafe : Safe I F)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i)) :
    (∀ i j, I (p i) (l j) ↔ i = j ∨ i = j + 1) ∨
      (∀ i j, I (p i) (l j) ↔ i = j ∨ i = j + 2) := by
  apply three_patterns (fun i j => I (p i) (l j))
  · exact fun i => accepted_edge I F hsafe (hacc i)
  · intro a b hab j
    exact two_points_active_line I F hthin hsafe (hacc a) (hacc b)
      (fun h => hab (hl h)) (hacc j)
  · intro a b c d hab hcd
    exact hfour (p a) (p b) (l c) (l d)
      (fun h => hab (hp h)) (fun h => hcd (hl h))

lemma pair_dominating_line_mem (I : Fin n → Fin n → Prop)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin n) (hp : Function.Injective p)
    (hshape : (∀ i j, I (p i) (l j) ↔ i = j ∨ i = j + 1) ∨
      (∀ i j, I (p i) (l j) ↔ i = j ∨ i = j + 2))
    (v : Fin n) (hdom : ∀ a b, a ≠ b → I (p a) v ∨ I (p b) v) :
    ∃ k, v = l k := by
  obtain ⟨a, b, hab, hav, hbv⟩ := two_of_three (fun a => I (p a) v) hdom
  obtain ⟨c, hac, hbc⟩ := pattern_common_line (fun a b => I (p a) (l b)) hshape a b hab
  refine ⟨c, ?_⟩
  by_contra hvc
  exact hfour (p a) (p b) v (l c) (fun h => hab (hp h)) hvc ⟨hav, hac, hbv, hbc⟩

lemma no_point_all_three (I : Fin n → Fin n → Prop)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin n) (hl : Function.Injective l)
    (hshape : (∀ i j, I (p i) (l j) ↔ i = j ∨ i = j + 1) ∨
      (∀ i j, I (p i) (l j) ↔ i = j ∨ i = j + 2)) :
    ∀ a, ¬ ∀ i, I a (l i) := by
  intro a hall
  obtain ⟨c, hc0, hc1⟩ := pattern_common_point (fun a b => I (p a) (l b))
    hshape 0 1 (by decide)
  have heq : a = p c := by
    by_contra hne
    exact hfour a (p c) (l 0) (l 1) hne (fun h => (by decide : (0 : Fin 3) ≠ 1) (hl h))
      ⟨hall 0, hall 1, hc0, hc1⟩
  obtain ⟨j, hj⟩ := pattern_missing_line (fun a b => I (p a) (l b)) hshape c
  exact hj (heq ▸ hall j)

lemma matching_three_column_card (I : Fin n → Fin n → Prop) [DecidableRel I]
    (p l : Fin 3 → Fin n)
    (hshape : (∀ i j, I (p i) (l j) ↔ i = j ∨ i = j + 1) ∨
      (∀ i j, I (p i) (l j) ↔ i = j ∨ i = j + 2)) :
    ∀ j, (univ.filter fun i => I (p i) (l j)).card = 2 := by
  classical
  intro j
  rcases hshape with hshape | hshape
  · have h : ∀ j : Fin 3, (univ.filter fun i => i = j ∨ i = j + 1).card = 2 := by decide
    simpa only [hshape] using h j
  · have h : ∀ j : Fin 3, (univ.filter fun i => i = j ∨ i = j + 2).card = 2 := by decide
    simpa only [hshape] using h j

lemma matching_three_active_line (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hthin : Thin F) (hsafe : Safe I F)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i)) {a v : Fin n} (ha : Accept F a v) :
    ∃ j, v = l j := by
  have hshape := matching_three_patterns I F hthin hsafe hfour p l hp hl hacc
  apply pair_dominating_line_mem I hfour p l hp hshape v
  intro i j hij
  exact two_points_active_line I F hthin hsafe (hacc i) (hacc j)
    (fun h => hij (hl h)) ha

lemma matching_three_no_heavy_row (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hthin : Thin F) (hsafe : Safe I F)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i))
    {a u v : Fin n} (hau : Accept F a u) (hav : Accept F a v) : u = v := by
  by_contra huv
  have hshape := matching_three_patterns I F hthin hsafe hfour p l hp hl hacc
  apply no_point_all_three I hfour p l hl hshape a
  intro i
  exact (two_points_active_line I F hthin hsafe hau hav huv (hacc i)).elim id id

lemma matching_three_active_point (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hthin : Thin F) (hsafe : Safe I F)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i)) {a v : Fin n} (ha : Accept F a v) :
    ∃ i, a = p i := by
  classical
  have hshape := matching_three_patterns I F hthin hsafe hfour p l hp hl hacc
  obtain ⟨j, hv⟩ := matching_three_active_line I F hthin hsafe hfour p l hp hl hacc ha
  rw [hv] at ha
  by_contra hn
  have hneq : ∀ i, a ≠ p i := by
    intro i heq
    exact hn ⟨i, heq⟩
  have haj : I a (l j) := accepted_edge I F hsafe ha
  have hno : ∀ t, t ≠ j → ¬ I a (l t) := by
    intro t ht hat
    obtain ⟨c, hcj, hct⟩ := pattern_common_point (fun a b => I (p a) (l b)) hshape j t ht.symm
    exact hfour a (p c) (l j) (l t) (hneq c) (fun h => ht (hl h).symm)
      ⟨haj, hat, hcj, hct⟩
  obtain ⟨k, t, hk, ht, hkt⟩ := pattern_missing_away (fun a b => I (p a) (l b)) hshape j
  have hdom := two_points_active_line I F hthin hsafe ha (hacc k)
    (fun h => hk (hl h).symm) (hacc t)
  exact hdom.elim (hno t ht) hkt

lemma matching_three_classification (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hthin : Thin F) (hsafe : Safe I F)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i)) :
    ∀ a v, Accept F a v ↔ ∃ i, a = p i ∧ v = l i := by
  intro a v
  constructor
  · intro ha
    obtain ⟨i, hai⟩ := matching_three_active_point I F hthin hsafe hfour p l hp hl hacc ha
    have hrow : Accept F (p i) v := by simpa [hai] using ha
    have hvi : v = l i := matching_three_no_heavy_row I F hthin hsafe hfour p l hp hl hacc
      hrow (hacc i)
    exact ⟨i, hai, hvi⟩
  · rintro ⟨i, rfl, rfl⟩
    exact hacc i

end ThinBlock

namespace ThinBlock

open Finset

variable {n : ℕ}

lemma exists_pure_line_clause (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hsafe : Safe I F) :
    ∃ W ∈ F, ¬ ∃ p, (false, p) ∈ W := by
  classical
  by_contra hn
  push Not at hn
  let x : Bool × Fin n → Bool := fun u => !u.1
  have hh : ∀ W ∈ F, ∃ u ∈ W, x u = true := by
    intro W hW
    obtain ⟨p, hp⟩ := hn W hW
    exact ⟨(false, p), hp, by simp [x]⟩
  obtain ⟨p, l, _, _, hl⟩ := hsafe x hh
  simp [x] at hl

lemma exists_pure_point_clause (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hsafe : Safe I F) :
    ∃ W ∈ F, ¬ ∃ l, (true, l) ∈ W := by
  classical
  by_contra hn
  push Not at hn
  let x : Bool × Fin n → Bool := fun u => u.1
  have hh : ∀ W ∈ F, ∃ u ∈ W, x u = true := by
    intro W hW
    obtain ⟨l, hl⟩ := hn W hW
    exact ⟨(true, l), hl, by simp [x]⟩
  obtain ⟨p, l, _, hp, _⟩ := hsafe x hh
  simp [x] at hp

lemma miss_nonedge_pair (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hsafe : Safe I F)
    {p l : Fin n} (hno : ¬ I p l) :
    ∃ W ∈ F, (false, p) ∉ W ∧ (true, l) ∉ W := by
  classical
  by_contra hn
  have ha : Accept F p l := by
    intro W hW
    by_contra h
    push Not at h
    exact hn ⟨W, hW, h.1, h.2⟩
  exact hno (accepted_edge I F hsafe ha)

lemma unique_pure_line_of_five (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hthin : Thin F) (hsafe : Safe I F)
    (p l : Fin 3 → Fin n) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i))
    (hmiss : ∀ i, ∃ j, ¬ I (p i) (l j)) (hcard : F.card = 5) :
    ∃ L ∈ F, (¬ ∃ a, (false, a) ∈ L) ∧
      ∀ W ∈ F, (¬ ∃ a, (false, a) ∈ W) → W = L := by
  classical
  obtain ⟨L, hLF, hL⟩ := exists_pure_line_clause I F hsafe
  obtain ⟨P, hPF, hP⟩ := exists_pure_point_clause I F hsafe
  have hLp : ∀ i, (true, l i) ∈ L := fun i =>
    (hacc i L hLF).resolve_left (fun h => hL ⟨p i, h⟩)
  have hPp : ∀ i, (false, p i) ∈ P := fun i =>
    (hacc i P hPF).resolve_right (fun h => hP ⟨l i, h⟩)
  choose miss hmiss using hmiss
  have hchoice : ∀ i, ∃ W ∈ F,
      (false, p i) ∉ W ∧ (true, l (miss i)) ∉ W := fun i =>
    miss_nonedge_pair I F hsafe (hmiss i)
  choose C hCF hCp hClmiss using hchoice
  have hCl : ∀ i, (true, l i) ∈ C i := fun i =>
    (hacc i (C i) (hCF i)).resolve_left (hCp i)
  have hCpoint : ∀ i, ∃ a, (false, a) ∈ C i := by
    intro i
    by_contra hn
    have hm := hacc (miss i) (C i) (hCF i)
    exact (hm.resolve_left (fun h => hn ⟨p (miss i), h⟩) |> hClmiss i)
  have hCother : ∀ i j, i ≠ j → (false, p j) ∈ C i := by
    intro i j hij
    rcases hacc j (C i) (hCF i) with hpj | hlj
    · exact hpj
    have heq : l i = l j := card_le_one.mp (hthin (C i) (hCF i) (hCpoint i))
      (l i) (mem_filter.mpr ⟨mem_univ _, hCl i⟩)
      (l j) (mem_filter.mpr ⟨mem_univ _, hlj⟩)
    exact (hij (hl heq)).elim
  have hCinj : Function.Injective C := by
    intro i j heq
    by_contra hij
    have hpj := hCother i j hij
    rw [heq] at hpj
    exact hCp j hpj
  let D := (univ : Finset (Fin 3)).image C
  have hDcard : D.card = 3 := by
    simp [D, card_image_of_injective _ hCinj]
  have hPD : P ∉ D := by
    intro hpD
    obtain ⟨i, _, heq⟩ := mem_image.mp hpD
    exact hP ⟨l i, heq ▸ hCl i⟩
  have hLD : L ∉ D := by
    intro hlD
    obtain ⟨i, _, heq⟩ := mem_image.mp hlD
    obtain ⟨a, ha⟩ := hCpoint i
    exact hL ⟨a, heq ▸ ha⟩
  have hPL : P ≠ L := by
    intro heq
    exact hL ⟨p 0, heq ▸ hPp 0⟩
  let K := insert P (insert L D)
  have hKcard : K.card = 5 := by
    simp [K, card_insert_of_notMem, hPD, hLD, hPL, hDcard]
  have hKF : K ⊆ F := by
    intro W hW
    rcases mem_insert.mp hW with heq | hW
    · simpa [heq] using hPF
    rcases mem_insert.mp hW with heq | hW
    · simpa [heq] using hLF
    obtain ⟨i, _, heq⟩ := mem_image.mp hW
    exact heq ▸ hCF i
  have hKeq : K = F := eq_of_subset_of_card_le hKF (by omega)
  refine ⟨L, hLF, hL, ?_⟩
  intro W hWF hWpoint
  have hWK : W ∈ K := hKeq ▸ hWF
  rcases mem_insert.mp hWK with heq | hW
  · exact (hWpoint ⟨p 0, heq.symm ▸ hPp 0⟩).elim
  rcases mem_insert.mp hW with heq | hW
  · exact heq
  obtain ⟨i, _, heq⟩ := mem_image.mp hW
  obtain ⟨a, ha⟩ := hCpoint i
  exact (hWpoint ⟨a, heq ▸ ha⟩).elim

lemma two_points_pure_line_filter (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hthin : Thin F) (hsafe : Safe I F)
    {p q lp lq l : Fin n} (hp : Accept F p lp) (hq : Accept F q lq)
    (hne : lp ≠ lq)
    (hline : ∀ W ∈ F, (¬ ∃ a, (false, a) ∈ W) → (true, l) ∈ W) :
    I p l ∨ I q l := by
  classical
  let x : Bool × Fin n → Bool := fun u =>
    if u.1 then decide (u.2 = l) else decide (u.2 = p ∨ u.2 = q)
  have hh : ∀ W ∈ F, ∃ u ∈ W, x u = true := by
    intro W hW
    by_cases hpoint : ∃ z, (false, z) ∈ W
    · by_cases hpW : (false, p) ∈ W
      · exact ⟨(false, p), hpW, by simp [x]⟩
      by_cases hqW : (false, q) ∈ W
      · exact ⟨(false, q), hqW, by simp [x]⟩
      have hlp : (true, lp) ∈ W := (hp W hW).resolve_left hpW
      have hlq : (true, lq) ∈ W := (hq W hW).resolve_left hqW
      have heq : lp = lq := card_le_one.mp (hthin W hW hpoint) lp
        (mem_filter.mpr ⟨mem_univ _, hlp⟩) lq (mem_filter.mpr ⟨mem_univ _, hlq⟩)
      exact (hne heq).elim
    · exact ⟨(true, l), hline W hW hpoint, by simp [x]⟩
  obtain ⟨u, v, huv, hu, hv⟩ := hsafe x hh
  have hupq : u = p ∨ u = q := by simpa [x] using hu
  have hvl : v = l := by simpa [x] using hv
  rcases hupq with hup | huq
  · exact Or.inl (by simpa [hup, hvl] using huv)
  · exact Or.inr (by simpa [huq, hvl] using huv)

lemma five_contains_matching_line_clause_of_recognition (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hthin : Thin F) (hsafe : Safe I F)
    (p l : Fin 3 → Fin n) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i))
    (hmiss : ∀ i, ∃ j, ¬ I (p i) (l j)) (hcard : F.card = 5)
    (hrecognize : ∀ v, (∀ i j, i ≠ j → I (p i) v ∨ I (p j) v) → ∃ k, v = l k) :
    ((univ : Finset (Fin 3)).image fun i => (true, l i)) ∈ F := by
  classical
  obtain ⟨L, hLF, hLpoint, hLunique⟩ :=
    unique_pure_line_of_five I F hthin hsafe p l hl hacc hmiss hcard
  have hline : ∀ v, (true, v) ∈ L → ∃ k, v = l k := by
    intro v hv
    apply hrecognize v
    intro i j hij
    apply two_points_pure_line_filter I F hthin hsafe (hacc i) (hacc j)
      (fun h => hij (hl h))
    intro W hWF hWpoint
    rw [hLunique W hWF hWpoint]
    exact hv
  have heq : L = ((univ : Finset (Fin 3)).image fun i => (true, l i)) := by
    ext u
    constructor
    · intro hu
      obtain ⟨tag, v⟩ := u
      cases tag
      · exact (hLpoint ⟨v, hu⟩).elim
      · obtain ⟨k, hk⟩ := hline v hu
        exact mem_image.mpr ⟨k, mem_univ _, by simp [hk]⟩
    · intro hu
      obtain ⟨k, _, rfl⟩ := mem_image.mp hu
      exact (hacc k L hLF).resolve_left (fun h => hLpoint ⟨p k, h⟩)
  exact heq ▸ hLF

end ThinBlock

namespace ThinBlock

open Finset

variable {n : ℕ}

lemma five_contains_matching_line_clause (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hthin : Thin F) (hsafe : Safe I F)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i)) (hcard : F.card = 5) :
    ((univ : Finset (Fin 3)).image fun i => (true, l i)) ∈ F := by
  have hshape := matching_three_patterns I F hthin hsafe hfour p l hp hl hacc
  apply five_contains_matching_line_clause_of_recognition I F hthin hsafe p l hl hacc
    (pattern_missing_line (fun a b => I (p a) (l b)) hshape) hcard
  exact pair_dominating_line_mem I hfour p l hp hshape

lemma matching_three_lines_not_neighborhood (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hthin : Thin F) (hsafe : Safe I F)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i)) :
    ∀ a : Fin n, ¬ ∀ v ∈ ((univ : Finset (Fin 3)).image l), I a v := by
  have hshape := matching_three_patterns I F hthin hsafe hfour p l hp hl hacc
  intro a ha
  apply no_point_all_three I hfour p l hl hshape a
  intro i
  exact ha (l i) (mem_image.mpr ⟨i, mem_univ _, rfl⟩)

end ThinBlock

namespace ThinBlock

open Finset

variable {n : ℕ}

lemma point_eq_of_two_matched_lines (I : Fin n → Fin n → Prop)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (l : Fin 3 → Fin n) (hl : Function.Injective l)
    (i j : Fin 3) (hij : i ≠ j) (u v : Fin n)
    (hui : I u (l i)) (huj : I u (l j))
    (hvi : I v (l i)) (hvj : I v (l j)) : u = v := by
  by_contra huv
  exact hfour u v (l i) (l j) huv (fun h => hij (hl h)) ⟨hui, huj, hvi, hvj⟩

lemma cycle_one_same_lines (I : Fin n → Fin n → Prop)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p q l : Fin 3 → Fin n) (hl : Function.Injective l)
    (hp : ∀ i j, I (p i) (l j) ↔ i = j ∨ i = j + 1)
    (hq : (∀ i j, I (q i) (l j) ↔ i = j ∨ i = j + 1) ∨
      (∀ i j, I (q i) (l j) ↔ i = j ∨ i = j + 2)) :
    (∀ i, q i = p i) ∨ (∀ i, q i = p (i + 1)) := by
  have hne1 : ∀ i : Fin 3, i ≠ i + 1 := by decide
  have hne2 : ∀ i : Fin 3, i ≠ i + 2 := by decide
  have h12 : ∀ i : Fin 3, i = i + 1 + 2 := by decide
  have h21 : ∀ i : Fin 3, i = i + 2 + 1 := by decide
  rcases hq with hq | hq
  · left
    intro i
    exact point_eq_of_two_matched_lines I hfour l hl i (i + 2) (hne2 i) (q i) (p i)
      ((hq i i).mpr (Or.inl rfl))
      ((hq i (i + 2)).mpr (Or.inr (h21 i)))
      ((hp i i).mpr (Or.inl rfl))
      ((hp i (i + 2)).mpr (Or.inr (h21 i)))
  · right
    intro i
    exact point_eq_of_two_matched_lines I hfour l hl i (i + 1) (hne1 i) (q i) (p (i + 1))
      ((hq i i).mpr (Or.inl rfl))
      ((hq i (i + 1)).mpr (Or.inr (h12 i)))
      ((hp (i + 1) i).mpr (Or.inr rfl))
      ((hp (i + 1) (i + 1)).mpr (Or.inl rfl))

lemma cycle_two_same_lines (I : Fin n → Fin n → Prop)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p q l : Fin 3 → Fin n) (hl : Function.Injective l)
    (hp : ∀ i j, I (p i) (l j) ↔ i = j ∨ i = j + 2)
    (hq : (∀ i j, I (q i) (l j) ↔ i = j ∨ i = j + 1) ∨
      (∀ i j, I (q i) (l j) ↔ i = j ∨ i = j + 2)) :
    (∀ i, q i = p i) ∨ (∀ i, q i = p (i + 2)) := by
  have hne1 : ∀ i : Fin 3, i ≠ i + 1 := by decide
  have hne2 : ∀ i : Fin 3, i ≠ i + 2 := by decide
  have h12 : ∀ i : Fin 3, i = i + 1 + 2 := by decide
  have h21 : ∀ i : Fin 3, i = i + 2 + 1 := by decide
  rcases hq with hq | hq
  · right
    intro i
    exact point_eq_of_two_matched_lines I hfour l hl i (i + 2) (hne2 i) (q i) (p (i + 2))
      ((hq i i).mpr (Or.inl rfl))
      ((hq i (i + 2)).mpr (Or.inr (h21 i)))
      ((hp (i + 2) i).mpr (Or.inr rfl))
      ((hp (i + 2) (i + 2)).mpr (Or.inl rfl))
  · left
    intro i
    exact point_eq_of_two_matched_lines I hfour l hl i (i + 1) (hne1 i) (q i) (p i)
      ((hq i i).mpr (Or.inl rfl))
      ((hq i (i + 1)).mpr (Or.inr (h12 i)))
      ((hp i i).mpr (Or.inl rfl))
      ((hp i (i + 1)).mpr (Or.inr (h12 i)))

lemma line_triple_has_two_matchings (I : Fin n → Fin n → Prop)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin n) (hl : Function.Injective l)
    (hp : (∀ i j, I (p i) (l j) ↔ i = j ∨ i = j + 1) ∨
      (∀ i j, I (p i) (l j) ↔ i = j ∨ i = j + 2)) :
    ∃ other : Fin 3 → Fin n,
      ((∀ i, other i = p (i + 1)) ∨ (∀ i, other i = p (i + 2))) ∧
      ∀ q : Fin 3 → Fin n,
        ((∀ i j, I (q i) (l j) ↔ i = j ∨ i = j + 1) ∨
          (∀ i j, I (q i) (l j) ↔ i = j ∨ i = j + 2)) →
        (∀ i, q i = p i) ∨ (∀ i, q i = other i) := by
  rcases hp with hp | hp
  · refine ⟨(fun i => p (i + 1)), Or.inl (fun _ => rfl), ?_⟩
    intro q hq
    exact cycle_one_same_lines I hfour p q l hl hp hq
  · refine ⟨(fun i => p (i + 2)), Or.inr (fun _ => rfl), ?_⟩
    intro q hq
    exact cycle_two_same_lines I hfour p q l hl hp hq

lemma thin_blocks_same_line_triple (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hthin : Thin F) (hsafe : Safe I F)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i)) :
    ∃ other : Fin 3 → Fin n,
      ∀ (K : Finset (Finset (Bool × Fin n))) (q : Fin 3 → Fin n),
        Thin K → Safe I K → Function.Injective q →
        (∀ i, Accept K (q i) (l i)) →
        (∀ a v, Accept K a v ↔ ∃ i, a = p i ∧ v = l i) ∨
          (∀ a v, Accept K a v ↔ ∃ i, a = other i ∧ v = l i) := by
  have hshape := matching_three_patterns I F hthin hsafe hfour p l hp hl hacc
  obtain ⟨other, _, hother⟩ := line_triple_has_two_matchings I hfour p l hl hshape
  refine ⟨other, ?_⟩
  intro K q hKthin hKsafe hq hKacc
  have hqshape := matching_three_patterns I K hKthin hKsafe hfour q l hq hl hKacc
  have hclass := matching_three_classification I K hKthin hKsafe hfour q l hq hl hKacc
  rcases hother q hqshape with heq | heq
  · left
    intro a v
    simpa only [heq] using hclass a v
  · right
    intro a v
    simpa only [heq] using hclass a v

end ThinBlock

namespace H8Projected.ExceptionalBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.PurePointBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.GroupedSandwichBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.LargeGroupedBudget

lemma pure_orPool_disjoint {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {S T : Finset (Fin n)} (hst : (S ∩ T).card ≤ 1) (m : ℕ) :
    Disjoint (orPool C (complementInput S) m) (orPool C (complementInput T) m) := by
  classical
  apply Finset.disjoint_left.2
  intro k hkS hkT
  obtain ⟨_, _, hlarge, hS⟩ := mem_orPool.1 hkS
  obtain ⟨_, _, _, hT⟩ := mem_orPool.1 hkT
  have hsub : singletonSupport n C (n + k) ⊆ S ∩ T :=
    Finset.subset_inter (support_subset_of_false hm hS) (support_subset_of_false hm hT)
  have hcard := Finset.card_le_card hsub
  omega

lemma grouped_pure_exceptional_resource_budget {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (H S : ι → Finset (Fin n)) (roots : ι → Finset ℕ)
    (hvalid : ∀ i, ∀ w ∈ roots i, w < n + C.gates.length)
    (hpos : ∀ i, ∀ p ∈ H i, ∃ w ∈ roots i,
      val C (List.ofFn (pairInput p p)) w = true)
    (hfalse : ∀ i, ∀ w ∈ roots i,
      val C (List.ofFn (complementInput (S i))) w = false)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (resources exceptional : Finset ℕ)
    (hlarge : largeOrGates n C ⊆ resources)
    (hexceptional : exceptional ⊆ resources)
    (htrue : ∀ e ∈ exceptional, ∀ i,
      val C (List.ofFn (complementInput (S i))) (n + e) = true) :
    (∑ i, (H i).card) + exceptional.card ≤
      resources.card + ∑ i, (roots i).card := by
  classical
  let pools := fun i => orPool C (complementInput (S i)) C.gates.length
  let U := Finset.univ.biUnion pools
  have hdis : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint pools := by
    intro i _ j _ hij
    exact pure_orPool_disjoint hm (hpair i j hij) C.gates.length
  have hsum : (∑ i, (H i).card) ≤ U.card + ∑ i, (roots i).card := by
    calc
      _ ≤ ∑ i, ((pools i).card + (roots i).card) := Finset.sum_le_sum fun i _ =>
        pure_grouped_pool_of_positives hm rb (H i) (S i) (roots i)
          (hvalid i) (hpos i) (hfalse i)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.card_biUnion hdis]
  have hUE : Disjoint U exceptional := by
    apply Finset.disjoint_left.2
    intro k hkU hkE
    obtain ⟨i, _, hki⟩ := Finset.mem_biUnion.1 hkU
    have hf := (mem_orPool.1 hki).2.2.2
    have ht := htrue k hkE i
    rw [hf] at ht
    cases ht
  have hsub : U ∪ exceptional ⊆ resources := by
    intro k hk
    rcases Finset.mem_union.1 hk with hk | hk
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 hk
      obtain ⟨hk, hop, hlargek, _⟩ := mem_orPool.1 hi
      exact hlarge (Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hop, hlargek⟩)
    · exact hexceptional hk
  have htotal : U.card + exceptional.card ≤ resources.card := by
    rw [← Finset.card_union_of_disjoint hUE]
    exact Finset.card_le_card hsub
  omega

lemma grouped_pure_exceptional_large_or_budget {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (H S : ι → Finset (Fin n)) (roots : ι → Finset ℕ)
    (hvalid : ∀ i, ∀ w ∈ roots i, w < n + C.gates.length)
    (hpos : ∀ i, ∀ p ∈ H i, ∃ w ∈ roots i,
      val C (List.ofFn (pairInput p p)) w = true)
    (hfalse : ∀ i, ∀ w ∈ roots i,
      val C (List.ofFn (complementInput (S i))) w = false)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (exceptional : Finset ℕ) (hexceptional : exceptional ⊆ largeOrGates n C)
    (htrue : ∀ e ∈ exceptional, ∀ i,
      val C (List.ofFn (complementInput (S i))) (n + e) = true) :
    (∑ i, (H i).card) + exceptional.card ≤
      (largeOrGates n C).card + ∑ i, (roots i).card :=
  grouped_pure_exceptional_resource_budget hm rb H S roots hvalid hpos hfalse hpair
    (largeOrGates n C) exceptional (fun _ h => h) hexceptional htrue

lemma grouped_pure_exceptional_or_budget {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (H S : ι → Finset (Fin n)) (roots : ι → Finset ℕ)
    (hvalid : ∀ i, ∀ w ∈ roots i, w < n + C.gates.length)
    (hpos : ∀ i, ∀ p ∈ H i, ∃ w ∈ roots i,
      val C (List.ofFn (pairInput p p)) w = true)
    (hfalse : ∀ i, ∀ w ∈ roots i,
      val C (List.ofFn (complementInput (S i))) w = false)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (exceptional : Finset ℕ) (hexceptional : exceptional ⊆ orGates C)
    (htrue : ∀ e ∈ exceptional, ∀ i,
      val C (List.ofFn (complementInput (S i))) (n + e) = true) :
    (∑ i, (H i).card) + exceptional.card ≤
      (orGates C).card + ∑ i, (roots i).card :=
  grouped_pure_exceptional_resource_budget hm rb H S roots hvalid hpos hfalse hpair
    (orGates C) exceptional (largeOrGates_subset n C) hexceptional htrue

end H8Projected.ExceptionalBudget

namespace H8Projected.LinearRoot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.PurePointBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.LargeGroupedBudget

lemma linear_of_singletons_false {n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (S : Finset (Fin n)) (w : ℕ)
    (hpos : ∀ p ∈ S, val C (List.ofFn (pairInput p p)) w = true)
    (hfalse : val C (List.ofFn (complementInput S)) w = false) :
    ∀ x : Fin n → Bool, val C (List.ofFn x) w = decide (∃ p ∈ S, x p = true) := by
  classical
  intro x
  by_cases hx : ∃ p ∈ S, x p = true
  · simp only [hx, decide_true]
    obtain ⟨p, hp, hxp⟩ := hx
    apply pair_mono hm (w := w) (fun i hi => ?_) (hpos p hp)
    have hi' : i = p := by simpa [pairInput] using hi
    simpa only [hi'] using hxp
  · simp only [hx, decide_false]
    have hle : ∀ i, x i = true → complementInput S i = true := by
      intro i hi
      have hnot : i ∉ S := fun hmem => hx ⟨i, hmem, hi⟩
      simp [complementInput, hnot]
    cases hv : val C (List.ofFn x) w with
    | false => rfl
    | true =>
      have ht := pair_mono hm hle w hv
      rw [hfalse] at ht
      cases ht

lemma linear_support {n : ℕ} {C : Circuit} {S : Finset (Fin n)} {w : ℕ}
    (hcomp : ∀ x : Fin n → Bool,
      val C (List.ofFn x) w = decide (∃ p ∈ S, x p = true)) :
    singletonSupport n C w = S := by
  classical
  ext p
  rw [mem_support, hcomp]
  simp [pairInput, eq_comm]

lemma linear_OR_extraction {n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (S : Finset (Fin n)) (hlarge : 1 < S.card) (w : ℕ)
    (hvalid : w < n + C.gates.length)
    (hcomp : ∀ x : Fin n → Bool,
      val C (List.ofFn x) w = decide (∃ p ∈ S, x p = true)) :
    ∃ j ∈ largeOrGates n C, n + j ≤ w ∧
      ∀ x : Fin n → Bool,
        val C (List.ofFn x) (n + j) = decide (∃ p ∈ S, x p = true) := by
  classical
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hinput : w < n
    · have hs := linear_support hcomp
      have hin := support_input (C := C) (⟨w, hinput⟩ : Fin n)
      rw [hin] at hs
      have hc := congrArg Finset.card hs
      simp only [Finset.card_singleton] at hc
      omega
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      rcases gate_op hm hj with hop | hop
      · have hf : val C (List.ofFn (complementInput S)) (n + j) = false := by
          rw [hcomp]
          simp [complementInput]
        obtain ⟨v, hv, hvf⟩ : ∃ v ∈ (gateAt C j).inputs,
            val C (List.ofFn (complementInput S)) v = false := by
          by_contra! hn
          have ht : val C (List.ofFn (complementInput S)) (n + j) = true :=
            (val_and (by simp) hj hop).2 fun v hv =>
              ⟨rb j hj v hv, by simpa using hn v hv⟩
          rw [hf] at ht
          cases ht
        have hvlt := rb j hj v hv
        have hp : ∀ p ∈ S, val C (List.ofFn (pairInput p p)) v = true := by
          intro p hp
          have ht : val C (List.ofFn (pairInput p p)) (n + j) = true := by
            rw [hcomp]
            simp [pairInput, hp]
          exact ((val_and (by simp) hj hop).1 ht v hv).2
        have hvcomp := linear_of_singletons_false hm S v hp hvf
        obtain ⟨k, hk, hkle, hkcomp⟩ := ih v hvlt (by omega) hvcomp
        exact ⟨k, hk, by omega, hkcomp⟩
      · have hs := linear_support hcomp
        have hjmem : j ∈ largeOrGates n C := by
          apply Finset.mem_filter.2
          exact ⟨Finset.mem_range.2 hj, hop, by simpa only [hs] using hlarge⟩
        exact ⟨j, hjmem, le_rfl, hcomp⟩

end H8Projected.LinearRoot

namespace H8Projected.LinearExceptional

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.PurePointBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.LargeGroupedBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.ExceptionalBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.LinearRoot

lemma distinct_linear_exceptional_gates {n : ℕ} {ι κ : Type*}
    [Fintype κ] [DecidableEq κ] {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (S : ι → Finset (Fin n)) (T : κ → Finset (Fin n))
    (hlarge : ∀ b, 1 < (T b).card) (hdistinct : Function.Injective T)
    (hnot : ∀ b i, ¬ T b ⊆ S i)
    (hwires : ∀ b, ∃ w, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool,
        val C (List.ofFn x) w = decide (∃ p ∈ T b, x p = true)) :
    ∃ exceptional : Finset ℕ, exceptional ⊆ largeOrGates n C ∧
      exceptional.card = Fintype.card κ ∧
      ∀ e ∈ exceptional, ∀ i,
        val C (List.ofFn (complementInput (S i))) (n + e) = true := by
  classical
  have hex : ∀ b, ∃ j ∈ largeOrGates n C,
      ∀ x : Fin n → Bool,
        val C (List.ofFn x) (n + j) = decide (∃ p ∈ T b, x p = true) := by
    intro b
    obtain ⟨w, hw, hc⟩ := hwires b
    obtain ⟨j, hj, _, hcomp⟩ := linear_OR_extraction hm rb (T b) (hlarge b) w hw hc
    exact ⟨j, hj, hcomp⟩
  choose roots hmem hcomp using hex
  have hinj : Function.Injective roots := by
    intro b c hbc
    apply hdistinct
    have hb := linear_support (hcomp b)
    have hc := linear_support (hcomp c)
    rw [hbc] at hb
    exact hb.symm.trans hc
  refine ⟨Finset.univ.image roots, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hj
    exact hmem b
  · rw [Finset.card_image_of_injective _ hinj]
    exact Finset.card_univ
  · intro j hj i
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hj
    rw [hcomp b]
    apply decide_eq_true
    have hx : ∃ p ∈ T b, p ∉ S i := by
      by_contra! h
      exact hnot b i h
    obtain ⟨p, hp, hpn⟩ := hx
    exact ⟨p, hp, by simp [complementInput, hpn]⟩

lemma grouped_pure_distinct_linear_bonus {n : ℕ} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (H S : ι → Finset (Fin n)) (roots : ι → Finset ℕ)
    (hvalid : ∀ i, ∀ w ∈ roots i, w < n + C.gates.length)
    (hpos : ∀ i, ∀ p ∈ H i, ∃ w ∈ roots i,
      val C (List.ofFn (pairInput p p)) w = true)
    (hfalse : ∀ i, ∀ w ∈ roots i,
      val C (List.ofFn (complementInput (S i))) w = false)
    (hpair : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (T : κ → Finset (Fin n))
    (hlarge : ∀ b, 1 < (T b).card) (hdistinct : Function.Injective T)
    (hnot : ∀ b i, ¬ T b ⊆ S i)
    (hwires : ∀ b, ∃ w, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool,
        val C (List.ofFn x) w = decide (∃ p ∈ T b, x p = true)) :
    (∑ i, (H i).card) + Fintype.card κ ≤
      (largeOrGates n C).card + ∑ i, (roots i).card := by
  obtain ⟨exceptional, he, hcard, htrue⟩ :=
    distinct_linear_exceptional_gates hm rb S T hlarge hdistinct hnot hwires
  have h := grouped_pure_exceptional_large_or_budget hm rb H S roots hvalid hpos
    hfalse hpair exceptional he htrue
  simpa only [hcard] using h

end H8Projected.LinearExceptional

namespace StarMatchingLedger

open Finset

lemma assigned_star_matching_cover {n B : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (p l : Fin B → Fin 3 → Fin n)
    (hcover : ∀ u v, G.Adj u v →
      (∃ c ∈ C, ∃ w ∈ L c, (u = c ∧ v = w) ∨ (u = w ∧ v = c)) ∨
      (∃ b i, (u = p b i ∧ v = l b i) ∨ (u = l b i ∧ v = p b i))) :
    ∃ T : Finset (Fin n), Cnf.Covers G T ∧ T.card ≤ C.card + 3 * B := by
  classical
  let U : Finset (Fin n) := univ.biUnion fun b : Fin B => univ.image (p b)
  let T : Finset (Fin n) := C ∪ U
  refine ⟨T, ?_, ?_⟩
  · intro u v huv
    rcases hcover u v huv with hstar | hmatching
    · obtain ⟨c, hc, w, _, horient⟩ := hstar
      have hcT : c ∈ T := mem_union_left U hc
      rcases horient with ⟨huc, _⟩ | ⟨_, hvc⟩
      · exact Or.inl (by simpa [huc] using hcT)
      · exact Or.inr (by simpa [hvc] using hcT)
    · obtain ⟨b, i, horient⟩ := hmatching
      have hpT : p b i ∈ T := mem_union_right C
        (mem_biUnion.mpr ⟨b, mem_univ _, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩)
      rcases horient with ⟨hup, _⟩ | ⟨_, hvp⟩
      · exact Or.inl (by simpa [hup] using hpT)
      · exact Or.inr (by simpa [hvp] using hpT)
  · have hU : U.card ≤ 3 * B := by
      calc U.card ≤ ∑ b : Fin B, (univ.image (p b)).card := card_biUnion_le
        _ ≤ ∑ _b : Fin B, 3 := sum_le_sum fun b _ => by
          simpa using (card_image_le (s := (univ : Finset (Fin 3))) (f := p b))
        _ = 3 * B := by simp [Nat.mul_comm]
    exact le_trans (card_union_le C U) (Nat.add_le_add_left hU C.card)

end StarMatchingLedger

namespace StarMatchingLedger

open Finset

lemma assigned_star_matching_edge_bound {n B : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (p l : Fin B → Fin 3 → Fin n)
    (hcover : ∀ u v, G.Adj u v →
      (∃ c ∈ C, ∃ w ∈ L c, (u = c ∧ v = w) ∨ (u = w ∧ v = c)) ∨
      (∃ b i, (u = p b i ∧ v = l b i) ∨ (u = l b i ∧ v = p b i))) :
    G.edgeFinset.card ≤ (∑ c ∈ C, (L c).card) + 3 * B := by
  classical
  let E0 : Finset (Sym2 (Fin n)) := C.biUnion fun c => (L c).image fun v => s(c, v)
  let E1 : Finset (Sym2 (Fin n)) := univ.biUnion fun b : Fin B =>
    (univ : Finset (Fin 3)).image fun i => s(p b i, l b i)
  have hsub : G.edgeFinset ⊆ E0 ∪ E1 := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := by simpa using he
      rcases hcover u v huv with hs | hm
      · obtain ⟨c, hc, w, hw, heq⟩ := hs
        apply mem_union_left
        apply mem_biUnion.mpr
        refine ⟨c, hc, mem_image.mpr ⟨w, hw, ?_⟩⟩
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
      · obtain ⟨b, i, heq⟩ := hm
        apply mem_union_right
        apply mem_biUnion.mpr
        refine ⟨b, mem_univ _, mem_image.mpr ⟨i, mem_univ _, ?_⟩⟩
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
  have hE0 : E0.card ≤ ∑ c ∈ C, (L c).card := by
    calc E0.card ≤ ∑ c ∈ C, ((L c).image fun v => s(c, v)).card := card_biUnion_le
      _ ≤ ∑ c ∈ C, (L c).card := sum_le_sum fun _ _ => card_image_le
  have hE1 : E1.card ≤ 3 * B := by
    calc E1.card ≤ ∑ b : Fin B,
        ((univ : Finset (Fin 3)).image fun i => s(p b i, l b i)).card := card_biUnion_le
      _ ≤ ∑ _b : Fin B, 3 := sum_le_sum fun b _ => by
        simpa using (card_image_le :
          ((univ : Finset (Fin 3)).image fun i => s(p b i, l b i)).card ≤ univ.card)
      _ = 3 * B := by simp [Nat.mul_comm]
  have hE := le_trans (card_le_card hsub) (card_union_le E0 E1)
  omega

lemma fold_star_matching_budget {edges vertices leaves centers B O t cost : ℕ}
    (hledger : edges + vertices ≤ leaves + centers + 6 * B)
    (hor : leaves + B ≤ O + t) (hcenters : centers ≤ t)
    (hcost : O + 2 * t + 5 * B ≤ cost + 1) : edges + vertices ≤ cost + 1 := by
  omega

lemma assigned_star_matching_cover_ledger {n B : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (p l : Fin B → Fin 3 → Fin n)
    (hcover : ∀ u v, G.Adj u v →
      (∃ c ∈ C, ∃ w ∈ L c, (u = c ∧ v = w) ∨ (u = w ∧ v = c)) ∨
      (∃ b i, (u = p b i ∧ v = l b i) ∨ (u = l b i ∧ v = p b i))) :
    ∃ T : Finset (Fin n), Cnf.Covers G T ∧
      G.edgeFinset.card + T.card ≤ (∑ c ∈ C, (L c).card) + C.card + 6 * B := by
  obtain ⟨T, hT, hTcard⟩ := assigned_star_matching_cover G C L p l hcover
  have hE := assigned_star_matching_edge_bound G C L p l hcover
  exact ⟨T, hT, by omega⟩

lemma assigned_star_matching_source_cost {n B O t cost : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (p l : Fin B → Fin 3 → Fin n)
    (hcover : ∀ u v, G.Adj u v →
      (∃ c ∈ C, ∃ w ∈ L c, (u = c ∧ v = w) ∨ (u = w ∧ v = c)) ∨
      (∃ b i, (u = p b i ∧ v = l b i) ∨ (u = l b i ∧ v = p b i)))
    (hor : (∑ c ∈ C, (L c).card) + B ≤ O + t)
    (hcenters : C.card ≤ t) (hcost : O + 2 * t + 5 * B ≤ cost + 1) :
    ∃ T : Finset (Fin n), Cnf.Covers G T ∧ G.edgeFinset.card + T.card ≤ cost + 1 := by
  obtain ⟨T, hT, hledger⟩ := assigned_star_matching_cover_ledger G C L p l hcover
  exact ⟨T, hT, fold_star_matching_budget hledger hor hcenters hcost⟩

end StarMatchingLedger

namespace StarMatchingLedger

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.LargeGroupedBudget

lemma indexed_gate_cost {n t B : ℕ} (C : Circuit)
    (a : Fin (t + 4 * B) → Fin C.gates.length)
    (z : Fin (t + B - 1) → Fin C.gates.length)
    (ha : Function.Injective a) (hz : Function.Injective z)
    (haop : ∀ i, (gateAt C (a i).val).op = GateOp.and)
    (hzop : ∀ i, (gateAt C (z i).val).op = GateOp.or)
    (hzsmall : ∀ i, (singletonSupport n C (n + (z i).val)).card ≤ 1)
    (hne : 1 ≤ t + B) :
    (largeOrGates n C).card + 2 * t + 5 * B ≤ C.size + 1 := by
  classical
  let A : Finset ℕ := univ.image fun i => (a i).val
  let Z : Finset ℕ := univ.image fun i => (z i).val
  let O := largeOrGates n C
  have ha' : Function.Injective (fun i => (a i).val) := by
    intro i j hij
    exact ha (Fin.ext hij)
  have hz' : Function.Injective (fun i => (z i).val) := by
    intro i j hij
    exact hz (Fin.ext hij)
  have hAcard : A.card = t + 4 * B := by simp [A, card_image_of_injective _ ha']
  have hZcard : Z.card = t + B - 1 := by simp [Z, card_image_of_injective _ hz']
  have hAop : ∀ j ∈ A, (gateAt C j).op = GateOp.and := by
    intro j hj
    obtain ⟨i, _, heq⟩ := mem_image.mp hj
    exact heq ▸ haop i
  have hZop : ∀ j ∈ Z, (gateAt C j).op = GateOp.or := by
    intro j hj
    obtain ⟨i, _, heq⟩ := mem_image.mp hj
    exact heq ▸ hzop i
  have hZsmall : ∀ j ∈ Z, (singletonSupport n C (n + j)).card ≤ 1 := by
    intro j hj
    obtain ⟨i, _, heq⟩ := mem_image.mp hj
    exact heq ▸ hzsmall i
  have hOA : Disjoint O A := by
    apply Finset.disjoint_left.mpr
    intro j hjO hjA
    have hop := (mem_filter.mp hjO).2.1
    rw [hAop j hjA] at hop
    cases hop
  have hOZ : Disjoint O Z := by
    apply Finset.disjoint_left.mpr
    intro j hjO hjZ
    have hlarge := (mem_filter.mp hjO).2.2
    have hsmall := hZsmall j hjZ
    omega
  have hAZ : Disjoint A Z := by
    apply Finset.disjoint_left.mpr
    intro j hjA hjZ
    have hop := hAop j hjA
    rw [hZop j hjZ] at hop
    cases hop
  have hOAZ : Disjoint (O ∪ A) Z := by
    apply Finset.disjoint_left.mpr
    intro j hj hjZ
    rcases mem_union.mp hj with hjO | hjA
    · exact Finset.disjoint_left.mp hOZ hjO hjZ
    · exact Finset.disjoint_left.mp hAZ hjA hjZ
  have hsub : O ∪ A ∪ Z ⊆ range C.gates.length := by
    intro j hj
    rcases mem_union.mp hj with hj | hjZ
    · rcases mem_union.mp hj with hjO | hjA
      · exact (mem_filter.mp hjO).1
      · obtain ⟨i, _, heq⟩ := mem_image.mp hjA
        exact heq ▸ mem_range.mpr (a i).isLt
    · obtain ⟨i, _, heq⟩ := mem_image.mp hjZ
      exact heq ▸ mem_range.mpr (z i).isLt
  have hcount : O.card + A.card + Z.card ≤ C.gates.length := by
    rw [← card_union_of_disjoint hOA, ← card_union_of_disjoint hOAZ]
    simpa using card_le_card hsub
  change O.card + 2 * t + 5 * B ≤ C.gates.length + 1
  omega

lemma assigned_star_matching_gate_cost {n t B : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (centers : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (p l : Fin B → Fin 3 → Fin n)
    (hcover : ∀ u v, G.Adj u v →
      (∃ c ∈ centers, ∃ w ∈ L c, (u = c ∧ v = w) ∨ (u = w ∧ v = c)) ∨
      (∃ b i, (u = p b i ∧ v = l b i) ∨ (u = l b i ∧ v = p b i)))
    (hor : (∑ c ∈ centers, (L c).card) + B ≤ (largeOrGates n C).card + t)
    (hcenters : centers.card ≤ t)
    (a : Fin (t + 4 * B) → Fin C.gates.length)
    (z : Fin (t + B - 1) → Fin C.gates.length)
    (ha : Function.Injective a) (hz : Function.Injective z)
    (haop : ∀ i, (gateAt C (a i).val).op = GateOp.and)
    (hzop : ∀ i, (gateAt C (z i).val).op = GateOp.or)
    (hzsmall : ∀ i, (singletonSupport n C (n + (z i).val)).card ≤ 1)
    (hne : 1 ≤ t + B) :
    ∃ T : Finset (Fin n), Cnf.Covers G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  exact assigned_star_matching_source_cost G centers L p l hcover hor hcenters
    (indexed_gate_cost C a z ha hz haop hzop hzsmall hne)

end StarMatchingLedger

namespace StarMatchingLedger

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.PurePointBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.LargeGroupedBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.LinearExceptional

lemma assigned_star_matching_semantic_cost {n t B : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack n C)
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (centers : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (p l : Fin B → Fin 3 → Fin n)
    (hcover : ∀ u v, G.Adj u v →
      (∃ c ∈ centers, ∃ w ∈ L c, (u = c ∧ v = w) ∨ (u = w ∧ v = c)) ∨
      (∃ b i, (u = p b i ∧ v = l b i) ∨ (u = l b i ∧ v = p b i)))
    (hcenters : centers.card ≤ t)
    (roots : {c : Fin n // c ∈ centers} → Finset ℕ)
    (hvalid : ∀ c, ∀ w ∈ roots c, w < n + C.gates.length)
    (hpos : ∀ c, ∀ v ∈ L c.val, ∃ w ∈ roots c,
      val C (List.ofFn (pairInput v v)) w = true)
    (hfalse : ∀ c, ∀ w ∈ roots c,
      val C (List.ofFn (complementInput (G.neighborFinset c.val))) w = false)
    (hroots : (∑ c : {c : Fin n // c ∈ centers}, (roots c).card) ≤ t)
    (exceptional : Fin B → Finset (Fin n))
    (hlarge : ∀ b, 1 < (exceptional b).card)
    (hdistinct : Function.Injective exceptional)
    (hnot : ∀ b, ∀ c : {c : Fin n // c ∈ centers},
      ¬ exceptional b ⊆ G.neighborFinset c.val)
    (hwires : ∀ b, ∃ w, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool,
        val C (List.ofFn x) w = decide (∃ v ∈ exceptional b, x v = true))
    (a : Fin (t + 4 * B) → Fin C.gates.length)
    (z : Fin (t + B - 1) → Fin C.gates.length)
    (ha : Function.Injective a) (hz : Function.Injective z)
    (haop : ∀ i, (gateAt C (a i).val).op = GateOp.and)
    (hzop : ∀ i, (gateAt C (z i).val).op = GateOp.or)
    (hzsmall : ∀ i, (singletonSupport n C (n + (z i).val)).card ≤ 1)
    (hne : 1 ≤ t + B) :
    ∃ T : Finset (Fin n), Cnf.Covers G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  have hpair : ∀ c d : {c : Fin n // c ∈ centers}, c ≠ d →
      (G.neighborFinset c.val ∩ G.neighborFinset d.val).card ≤ 1 := by
    intro c d hcd
    have heq : G.neighborFinset c.val ∩ G.neighborFinset d.val =
        univ.filter fun w => G.Adj c.val w ∧ G.Adj d.val w := by
      ext w
      simp
    rw [heq]
    exact hfour c.val d.val (fun h => hcd (Subtype.ext h))
  have hbonus := grouped_pure_distinct_linear_bonus hm rb
    (fun c : {c : Fin n // c ∈ centers} => L c.val)
    (fun c : {c : Fin n // c ∈ centers} => G.neighborFinset c.val)
    roots hvalid hpos hfalse hpair exceptional hlarge hdistinct hnot hwires
  have hsum : (∑ c : {c : Fin n // c ∈ centers}, (L c.val).card) =
      ∑ c ∈ centers, (L c).card := Finset.sum_coe_sort centers (fun c => (L c).card)
  rw [hsum, Fintype.card_fin] at hbonus
  have hor : (∑ c ∈ centers, (L c).card) + B ≤ (largeOrGates n C).card + t := by
    omega
  exact assigned_star_matching_gate_cost G C centers L p l hcover hor hcenters
    a z ha hz haop hzop hzsmall hne

end StarMatchingLedger

namespace ThinBlock

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.PurePointBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.LargeGroupedBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.LinearRoot

lemma five_matching_embedded_linear_root {r n : ℕ}
    (I : Fin r → Fin r → Prop)
    (F : Finset (Finset (Bool × Fin r))) (hthin : Thin F) (hsafe : Safe I F)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin r) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i)) (hcard : F.card = 5)
    (e : (Bool × Fin r) ≃ Fin n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcross : ∀ a b, G.Adj (e (false, a)) (e (true, b)) → I a b)
    (hline : ∀ a b, ¬ G.Adj (e (true, a)) (e (true, b)))
    (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack n C)
    (hwires : ∀ W ∈ F, ∃ w, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool,
        val C (List.ofFn x) w = decide (∃ u ∈ W, x (e u) = true)) :
    let S := (univ : Finset (Fin 3)).image (fun i => e (true, l i))
    S.card = 3 ∧ (∀ v, ¬ S ⊆ G.neighborFinset v) ∧
      ∃ j ∈ largeOrGates n C, ∀ x : Fin n → Bool,
        val C (List.ofFn x) (n + j) = decide (∃ v ∈ S, x v = true) := by
  classical
  dsimp only
  let S := (univ : Finset (Fin 3)).image (fun i => e (true, l i))
  have hinj : Function.Injective (fun i : Fin 3 => e (true, l i)) := by
    intro i j hij
    exact hl (congrArg Prod.snd (e.injective hij))
  have hScard : S.card = 3 := by
    simp [S, card_image_of_injective _ hinj]
  have houtside : ∀ v, ¬ S ⊆ G.neighborFinset v := by
    intro v hv
    obtain ⟨⟨tag, a⟩, rfl⟩ := e.surjective v
    cases tag
    · apply matching_three_lines_not_neighborhood I F hthin hsafe hfour p l hp hl hacc a
      intro b hb
      obtain ⟨i, _, rfl⟩ := mem_image.mp hb
      apply hcross a (l i)
      exact (G.mem_neighborFinset _ _).mp (hv (mem_image.mpr ⟨i, mem_univ _, rfl⟩))
    · exact hline a (l 0) ((G.mem_neighborFinset _ _).mp
        (hv (mem_image.mpr ⟨0, mem_univ _, rfl⟩)))
  have hclause := five_contains_matching_line_clause I F hthin hsafe hfour p l hp hl hacc hcard
  obtain ⟨w, hvalid, hw⟩ := hwires _ hclause
  have hcomp : ∀ x : Fin n → Bool,
      val C (List.ofFn x) w = decide (∃ v ∈ S, x v = true) := by
    intro x
    rw [hw]
    congr 1
    apply propext
    simp only [S, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨u, ⟨i, rfl⟩, hi⟩
      exact ⟨e (true, l i), ⟨i, rfl⟩, hi⟩
    · rintro ⟨v, ⟨i, rfl⟩, hi⟩
      exact ⟨(true, l i), ⟨i, rfl⟩, hi⟩
  obtain ⟨j, hj, _, hjcomp⟩ := linear_OR_extraction hm rb S (by omega) w hvalid hcomp
  exact ⟨hScard, houtside, j, hj, hjcomp⟩

end ThinBlock

namespace StarMatchingDedup

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.PurePointBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.LargeGroupedBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.LinearExceptional
open PEqualNP.Outside.L_meta_2583.StarMatchingLedger

def lineSupports {n B : ℕ} (l : Fin B → Fin 3 → Fin n) : Finset (Finset (Fin n)) :=
  univ.image fun b => univ.image (l b)

lemma lineSupports_card_le {n B : ℕ} (l : Fin B → Fin 3 → Fin n) :
    (lineSupports l).card ≤ B := by
  simpa [lineSupports] using
    (card_image_le : (univ.image fun b => univ.image (l b)).card ≤ univ.card)

lemma lineSupports_mem_card {n B : ℕ} (l : Fin B → Fin 3 → Fin n)
    {S : Finset (Fin n)} (hS : S ∈ lineSupports l) : S.card ≤ 3 := by
  obtain ⟨b, _, rfl⟩ := mem_image.1 hS
  simpa using (card_image_le : (univ.image (l b)).card ≤ univ.card)

lemma assigned_star_matching_dedup_cover {n B : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (centers : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (p l : Fin B → Fin 3 → Fin n)
    (hcover : ∀ u v, G.Adj u v →
      (∃ c ∈ centers, ∃ w ∈ L c, (u = c ∧ v = w) ∨ (u = w ∧ v = c)) ∨
      (∃ b i, (u = p b i ∧ v = l b i) ∨ (u = l b i ∧ v = p b i))) :
    ∃ T : Finset (Fin n), Cnf.Covers G T ∧
      T.card ≤ centers.card + 3 * (lineSupports l).card := by
  classical
  let U := (lineSupports l).biUnion id
  refine ⟨centers ∪ U, ?_, ?_⟩
  · intro u v huv
    rcases hcover u v huv with hstar | hmatching
    · obtain ⟨c, hc, w, _, horient⟩ := hstar
      have hcT : c ∈ centers ∪ U := mem_union_left U hc
      rcases horient with ⟨huc, _⟩ | ⟨_, hvc⟩
      · exact Or.inl (by simpa [huc] using hcT)
      · exact Or.inr (by simpa [hvc] using hcT)
    · obtain ⟨b, i, horient⟩ := hmatching
      have hlT : l b i ∈ centers ∪ U := mem_union_right centers
        (mem_biUnion.2 ⟨univ.image (l b), mem_image.2 ⟨b, mem_univ _, rfl⟩,
          mem_image.2 ⟨i, mem_univ _, rfl⟩⟩)
      rcases horient with ⟨_, hvl⟩ | ⟨hul, _⟩
      · exact Or.inr (by simpa [hvl] using hlT)
      · exact Or.inl (by simpa [hul] using hlT)
  · have hU : U.card ≤ 3 * (lineSupports l).card := by
      calc
        U.card ≤ ∑ S ∈ lineSupports l, S.card := card_biUnion_le
        _ ≤ ∑ _S ∈ lineSupports l, 3 := sum_le_sum fun S hS => lineSupports_mem_card l hS
        _ = 3 * (lineSupports l).card := by simp [Nat.mul_comm]
    exact (card_union_le centers U).trans (Nat.add_le_add_left hU centers.card)

lemma assigned_star_matching_dedup_ledger {n B : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (centers : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (p l : Fin B → Fin 3 → Fin n)
    (hcover : ∀ u v, G.Adj u v →
      (∃ c ∈ centers, ∃ w ∈ L c, (u = c ∧ v = w) ∨ (u = w ∧ v = c)) ∨
      (∃ b i, (u = p b i ∧ v = l b i) ∨ (u = l b i ∧ v = p b i))) :
    ∃ T : Finset (Fin n), Cnf.Covers G T ∧
      G.edgeFinset.card + T.card ≤
        (∑ c ∈ centers, (L c).card) + centers.card + 3 * B + 3 * (lineSupports l).card := by
  obtain ⟨T, hT, hc⟩ := assigned_star_matching_dedup_cover G centers L p l hcover
  have he := assigned_star_matching_edge_bound G centers L p l hcover
  exact ⟨T, hT, by omega⟩

lemma fold_dedup_budget {edges vertices leaves centers B Q O t cost : ℕ}
    (hledger : edges + vertices ≤ leaves + centers + 3 * B + 3 * Q)
    (hor : leaves + Q ≤ O + t) (hcenters : centers ≤ t) (hQB : Q ≤ B)
    (hcost : O + 2 * t + 5 * B ≤ cost + 1) : edges + vertices ≤ cost + 1 := by
  omega

lemma assigned_star_matching_dedup_semantic_cost {n t B : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack n C)
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (centers : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (p l : Fin B → Fin 3 → Fin n)
    (hcover : ∀ u v, G.Adj u v →
      (∃ c ∈ centers, ∃ w ∈ L c, (u = c ∧ v = w) ∨ (u = w ∧ v = c)) ∨
      (∃ b i, (u = p b i ∧ v = l b i) ∨ (u = l b i ∧ v = p b i)))
    (hcenters : centers.card ≤ t)
    (roots : {c : Fin n // c ∈ centers} → Finset ℕ)
    (hvalid : ∀ c, ∀ w ∈ roots c, w < n + C.gates.length)
    (hpos : ∀ c, ∀ v ∈ L c.val, ∃ w ∈ roots c,
      val C (List.ofFn (pairInput v v)) w = true)
    (hfalse : ∀ c, ∀ w ∈ roots c,
      val C (List.ofFn (complementInput (G.neighborFinset c.val))) w = false)
    (hroots : (∑ c : {c : Fin n // c ∈ centers}, (roots c).card) ≤ t)
    (hlarge : ∀ b, 1 < (univ.image (l b)).card)
    (hnot : ∀ b, ∀ c : {c : Fin n // c ∈ centers},
      ¬ univ.image (l b) ⊆ G.neighborFinset c.val)
    (hwires : ∀ b, ∃ w, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool,
        val C (List.ofFn x) w = decide (∃ v ∈ univ.image (l b), x v = true))
    (a : Fin (t + 4 * B) → Fin C.gates.length)
    (z : Fin (t + B - 1) → Fin C.gates.length)
    (ha : Function.Injective a) (hz : Function.Injective z)
    (haop : ∀ i, (gateAt C (a i).val).op = GateOp.and)
    (hzop : ∀ i, (gateAt C (z i).val).op = GateOp.or)
    (hzsmall : ∀ i, (singletonSupport n C (n + (z i).val)).card ≤ 1)
    (hne : 1 ≤ t + B) :
    ∃ T : Finset (Fin n), Cnf.Covers G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  have hpair : ∀ c d : {c : Fin n // c ∈ centers}, c ≠ d →
      (G.neighborFinset c.val ∩ G.neighborFinset d.val).card ≤ 1 := by
    intro c d hcd
    have heq : G.neighborFinset c.val ∩ G.neighborFinset d.val =
        univ.filter fun w => G.Adj c.val w ∧ G.Adj d.val w := by
      ext w
      simp
    rw [heq]
    exact hfour c.val d.val (fun h => hcd (Subtype.ext h))
  let Q := lineSupports l
  have hQlarge : ∀ S : {S // S ∈ Q}, 1 < S.val.card := by
    intro S
    obtain ⟨b, _, hb⟩ := mem_image.1 S.property
    simpa only [← hb] using hlarge b
  have hQnot : ∀ S : {S // S ∈ Q}, ∀ c : {c : Fin n // c ∈ centers},
      ¬ S.val ⊆ G.neighborFinset c.val := by
    intro S c
    obtain ⟨b, _, hb⟩ := mem_image.1 S.property
    simpa only [← hb] using hnot b c
  have hQwires : ∀ S : {S // S ∈ Q}, ∃ w, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool,
        val C (List.ofFn x) w = decide (∃ v ∈ S.val, x v = true) := by
    intro S
    obtain ⟨b, _, hb⟩ := mem_image.1 S.property
    simpa only [← hb] using hwires b
  have hbonus := grouped_pure_distinct_linear_bonus hm rb
    (fun c : {c : Fin n // c ∈ centers} => L c.val)
    (fun c : {c : Fin n // c ∈ centers} => G.neighborFinset c.val)
    roots hvalid hpos hfalse hpair (fun S : {S // S ∈ Q} => S.val)
    hQlarge Subtype.val_injective hQnot hQwires
  have hsum : (∑ c : {c : Fin n // c ∈ centers}, (L c.val).card) =
      ∑ c ∈ centers, (L c).card := sum_coe_sort centers (fun c => (L c).card)
  rw [hsum, Fintype.card_coe] at hbonus
  have hor : (∑ c ∈ centers, (L c).card) + Q.card ≤ (largeOrGates n C).card + t := by
    omega
  obtain ⟨T, hT, hledger⟩ := assigned_star_matching_dedup_ledger G centers L p l hcover
  exact ⟨T, hT, fold_dedup_budget hledger hor hcenters (lineSupports_card_le l)
    (indexed_gate_cost C a z ha hz haop hzop hzsmall hne)⟩

end StarMatchingDedup

namespace ThinBlock

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.PurePointBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.LargeGroupedBudget
open PEqualNP.Outside.L_meta_2583.StarMatchingDedup

lemma thin_five_star_matching_cost {r n t B : ℕ}
    (I : Fin r → Fin r → Prop)
    (F : Fin B → Finset (Finset (Bool × Fin r)))
    (hthin : ∀ b, Thin (F b)) (hsafe : ∀ b, Safe I (F b))
    (hIfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin B → Fin 3 → Fin r)
    (hp : ∀ b, Function.Injective (p b)) (hl : ∀ b, Function.Injective (l b))
    (hacc : ∀ b i, Accept (F b) (p b i) (l b i)) (hcard : ∀ b, (F b).card = 5)
    (e : (Bool × Fin r) ≃ Fin n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hcross : ∀ a b, G.Adj (e (false, a)) (e (true, b)) → I a b)
    (hline : ∀ a b, ¬ G.Adj (e (true, a)) (e (true, b)))
    (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack n C)
    (hwires : ∀ b W, W ∈ F b → ∃ w, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool,
        val C (List.ofFn x) w = decide (∃ u ∈ W, x (e u) = true))
    (centers : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (hcover : ∀ u v, G.Adj u v →
      (∃ c ∈ centers, ∃ w ∈ L c, (u = c ∧ v = w) ∨ (u = w ∧ v = c)) ∨
      (∃ b i, (u = e (false, p b i) ∧ v = e (true, l b i)) ∨
        (u = e (true, l b i) ∧ v = e (false, p b i))))
    (hcenters : centers.card ≤ t)
    (roots : {c : Fin n // c ∈ centers} → Finset ℕ)
    (hvalid : ∀ c, ∀ w ∈ roots c, w < n + C.gates.length)
    (hpos : ∀ c, ∀ v ∈ L c.val, ∃ w ∈ roots c,
      val C (List.ofFn (pairInput v v)) w = true)
    (hfalse : ∀ c, ∀ w ∈ roots c,
      val C (List.ofFn (complementInput (G.neighborFinset c.val))) w = false)
    (hroots : (∑ c : {c : Fin n // c ∈ centers}, (roots c).card) ≤ t)
    (a : Fin (t + 4 * B) → Fin C.gates.length)
    (z : Fin (t + B - 1) → Fin C.gates.length)
    (ha : Function.Injective a) (hz : Function.Injective z)
    (haop : ∀ i, (gateAt C (a i).val).op = GateOp.and)
    (hzop : ∀ i, (gateAt C (z i).val).op = GateOp.or)
    (hzsmall : ∀ i, (singletonSupport n C (n + (z i).val)).card ≤ 1)
    (hne : 1 ≤ t + B) :
    ∃ T : Finset (Fin n), Cnf.Covers G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  have hexceptional := fun b => five_matching_embedded_linear_root I (F b)
    (hthin b) (hsafe b) hIfour (p b) (l b) (hp b) (hl b) (hacc b) (hcard b)
    e G hcross hline C hm rb (hwires b)
  apply assigned_star_matching_dedup_semantic_cost G C hm rb hfour centers L
    (fun b i => e (false, p b i)) (fun b i => e (true, l b i)) hcover hcenters
    roots hvalid hpos hfalse hroots ?_ ?_ ?_ a z ha hz haop hzop hzsmall hne
  · intro b
    have h := (hexceptional b).1
    omega
  · intro b c
    exact (hexceptional b).2.1 c.val
  · intro b
    obtain ⟨j, hj, hcomp⟩ := (hexceptional b).2.2
    have hjlt : j < C.gates.length := mem_range.mp (mem_filter.mp hj).1
    exact ⟨n + j, by omega, hcomp⟩

end ThinBlock

open Finset

lemma union_network_ordered_coverage {v n m : ℕ} (T : ℕ → Finset (Fin v))
    (U : Finset (Fin v))
    (hin : ∀ w < n, (T w).card ≤ 1)
    (hgate : ∀ j < m, 2 ≤ (T (n + j)).card →
      ∃ x y, x < n + j ∧ y < n + j ∧ T (n + j) = T x ∪ T y)
    (hcover : ∀ u ∈ U, ∃ w < n + m, u ∈ T w ∧ ∃ a ∈ T w, a < u) :
    U.card ≤ ((range m).filter fun j => 2 ≤ (T (n + j)).card).card := by
  classical
  let S : Fin 1 → Finset (Fin v) := fun _ => univ
  have hex : ∀ u ∈ U, ∃ j, unionGood n m T S 0 u j := by
    intro u hu
    obtain ⟨w, hw, huw, a, haw, hau⟩ := hcover u hu
    by_cases hwin : w < n
    · have heq := card_le_one.mp (hin w hwin) a haw u huw
      exact (ne_of_lt hau heq).elim
    · refine ⟨w - n, ?_⟩
      have hindex : n + (w - n) = w := by omega
      exact ⟨by omega, by simp [S], by simpa [hindex] using huw,
        a, by simpa [hindex] using haw, hau⟩
  apply union_card_le_relation
    (fun u j => unionGood n m T S 0 u j ∧
      ∀ j', j' < j → ¬ unionGood n m T S 0 u j')
  · intro u hu
    have hj := Nat.find_spec (hex u hu)
    exact ⟨Nat.find (hex u hu), mem_filter.mpr ⟨mem_range.mpr hj.1,
      union_good_large hj⟩, hj, fun j' hj' => Nat.find_min (hex u hu) hj'⟩
  · intro j hj u hu u' hu'
    have hh := union_inj_core T S hin hgate
      (fun a b hne => (hne (Subsingleton.elim a b)).elim) 0 0 u u' j
      hu.2.1 hu'.2.1 hu.2.2 hu'.2.2
    exact hh.2

lemma union_network_anchor_bound {v n m : ℕ} (T : ℕ → Finset (Fin v))
    (U : Finset (Fin v))
    (hin : ∀ w < n, (T w).card ≤ 1)
    (hgate : ∀ j < m, 2 ≤ (T (n + j)).card →
      ∃ x y, x < n + j ∧ y < n + j ∧ T (n + j) = T x ∪ T y)
    (hcover : ∀ u ∈ U, ∃ w < n + m, u ∈ T w ∧ ∃ a ∈ T w, a ∉ U) :
    U.card ≤ ((range m).filter fun j => 2 ≤ (T (n + j)).card).card := by
  classical
  let f : Fin v → Fin (v + v) := fun u =>
    if u ∈ U then Fin.natAdd v u else Fin.castAdd v u
  have hf : Function.Injective f := by
    intro u u' heq
    have hv := congrArg Fin.val heq
    have hu := u.isLt
    have hu' := u'.isLt
    by_cases hU : u ∈ U <;> by_cases hU' : u' ∈ U <;>
      simp only [f, hU, hU', ite_true, ite_false, Fin.val_natAdd, Fin.val_castAdd] at hv <;>
      exact Fin.ext (by omega)
  let V : ℕ → Finset (Fin (v + v)) := fun w => (T w).image f
  have hVin : ∀ w < n, (V w).card ≤ 1 := by
    intro w hw
    exact card_image_le.trans (hin w hw)
  have hVgate : ∀ j < m, 2 ≤ (V (n + j)).card →
      ∃ x y, x < n + j ∧ y < n + j ∧ V (n + j) = V x ∪ V y := by
    intro j hj hlarge
    have hTlarge : 2 ≤ (T (n + j)).card := hlarge.trans card_image_le
    obtain ⟨x, y, hx, hy, hxy⟩ := hgate j hj hTlarge
    exact ⟨x, y, hx, hy, by simp [V, hxy, image_union]⟩
  have hVcover : ∀ u ∈ U.image f, ∃ w < n + m,
      u ∈ V w ∧ ∃ a ∈ V w, a < u := by
    intro u hu
    obtain ⟨u, huU, rfl⟩ := mem_image.mp hu
    obtain ⟨w, hw, huw, a, haw, ha⟩ := hcover u huU
    refine ⟨w, hw, mem_image.mpr ⟨u, huw, rfl⟩,
      f a, mem_image.mpr ⟨a, haw, rfl⟩, ?_⟩
    change (f a).val < (f u).val
    simp only [f, ha, huU, ite_true, ite_false, Fin.val_natAdd, Fin.val_castAdd]
    have hal := a.isLt
    omega
  have h := union_network_ordered_coverage V (U.image f) hVin hVgate hVcover
  simpa only [V, card_image_of_injective _ hf] using h

namespace AndClauseAtoms

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair

noncomputable def clauseAtoms {v : ℕ} (n : ℕ) (C : Circuit)
    (tag : ℕ → Option (Fin v)) (w : ℕ) : Finset (Fin v) := by
  classical
  exact match tag w with
  | some a => {a}
  | none => if w < n then ∅ else
      if (gateAt C (w - n)).op = GateOp.and then
        (gateAt C (w - n)).inputs.toFinset.biUnion fun i =>
          if h : i < w then clauseAtoms n C tag i else ∅
      else ∅
termination_by w

lemma clauseAtoms_input {v n : ℕ} (C : Circuit) (tag : ℕ → Option (Fin v))
    {w : ℕ} (hw : w < n) : (clauseAtoms n C tag w).card ≤ 1 := by
  classical
  rw [clauseAtoms]
  cases tag w <;> simp [hw]

lemma clauseAtoms_tagged {v n : ℕ} (C : Circuit) (tag : ℕ → Option (Fin v))
    {w : ℕ} {a : Fin v} (h : tag w = some a) : clauseAtoms n C tag w = {a} := by
  rw [clauseAtoms]
  simp only [h]

lemma clauseAtoms_and {v n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    (tag : ℕ → Option (Fin v)) {j : ℕ} (hj : j < C.gates.length)
    (hnone : tag (n + j) = none) (hop : (gateAt C j).op = GateOp.and) :
    clauseAtoms n C tag (n + j) =
      (gateAt C j).inputs.toFinset.biUnion (clauseAtoms n C tag) := by
  classical
  rw [clauseAtoms]
  have hnot : ¬ n + j < n := by omega
  simp only [hnone, hnot, ite_false, Nat.add_sub_cancel_left, hop, ite_true]
  apply Finset.biUnion_congr rfl
  intro i hi
  exact dite_eq_left (rb j hj i (List.mem_toFinset.1 hi))

lemma clauseAtoms_binary_and_small {v n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    (tag : ℕ → Option (Fin v)) {j x y : ℕ} (hj : j < C.gates.length)
    (hnone : tag (n + j) = none) (hop : (gateAt C j).op = GateOp.and)
    (hinputs : (gateAt C j).inputs = [x, y])
    (hx : clauseAtoms n C tag x = ∅) (hy : (clauseAtoms n C tag y).card ≤ 1) :
    (clauseAtoms n C tag (n + j)).card ≤ 1 := by
  rw [clauseAtoms_and rb tag hj hnone hop]
  simpa [hinputs, hx] using hy

lemma clauseAtoms_large_gate {v n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C) (tag : ℕ → Option (Fin v))
    {j : ℕ} (hj : j < C.gates.length) (hlarge : 2 ≤ (clauseAtoms n C tag (n + j)).card) :
    (gateAt C j).op = GateOp.and ∧
      ∃ x y, x < n + j ∧ y < n + j ∧
        clauseAtoms n C tag (n + j) = clauseAtoms n C tag x ∪ clauseAtoms n C tag y := by
  classical
  have hnone : tag (n + j) = none := by
    cases ht : tag (n + j) with
    | none => rfl
    | some a =>
      rw [clauseAtoms] at hlarge
      simp [ht] at hlarge
  have hop : (gateAt C j).op = GateOp.and := by
    by_contra hn
    rw [clauseAtoms] at hlarge
    simp [hnone, hn] at hlarge
  have hsupport : clauseAtoms n C tag (n + j) =
      (gateAt C j).inputs.toFinset.biUnion (clauseAtoms n C tag) :=
    clauseAtoms_and rb tag hj hnone hop
  refine ⟨hop, ?_⟩
  have hlen := (hm _ (gateAt_mem hj)).2
  cases he : (gateAt C j).inputs with
  | nil =>
    rw [he] at hsupport
    simp at hsupport
    rw [hsupport] at hlarge
    simp at hlarge
  | cons x tail =>
    have hx : x < n + j := rb j hj x (by simp [he])
    cases tail with
    | nil =>
      refine ⟨x, x, hx, hx, ?_⟩
      simpa [he] using hsupport
    | cons y tail =>
      have hy : y < n + j := rb j hj y (by simp [he])
      cases tail with
      | nil =>
        refine ⟨x, y, hx, hy, ?_⟩
        simpa [he] using hsupport
      | cons z rest => simp [he] at hlen

noncomputable def largeClauseAndGates {v : ℕ} (n : ℕ) (C : Circuit)
    (tag : ℕ → Option (Fin v)) : Finset ℕ := by
  classical
  exact (range C.gates.length).filter fun j =>
    (gateAt C j).op = GateOp.and ∧ 2 ≤ (clauseAtoms n C tag (n + j)).card

lemma clause_anchor_and_bound {v n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C) (tag : ℕ → Option (Fin v))
    (U : Finset (Fin v))
    (hcover : ∀ u ∈ U, ∃ w < n + C.gates.length,
      u ∈ clauseAtoms n C tag w ∧ ∃ a ∈ clauseAtoms n C tag w, a ∉ U) :
    U.card ≤ (largeClauseAndGates n C tag).card := by
  classical
  have h := union_network_anchor_bound (clauseAtoms n C tag) U
    (fun _ hw => clauseAtoms_input C tag hw)
    (fun _ hj hlarge => (clauseAtoms_large_gate hm rb tag hj hlarge).2) hcover
  have heq : ((range C.gates.length).filter fun j =>
      2 ≤ (clauseAtoms n C tag (n + j)).card) = largeClauseAndGates n C tag := by
    ext j
    simp only [largeClauseAndGates, mem_filter, mem_range]
    constructor
    · rintro ⟨hj, hlarge⟩
      exact ⟨hj, (clauseAtoms_large_gate hm rb tag hj hlarge).1, hlarge⟩
    · rintro ⟨hj, _, hlarge⟩
      exact ⟨hj, hlarge⟩
  simpa only [heq] using h

noncomputable def andGates (C : Circuit) : Finset ℕ := by
  classical
  exact (range C.gates.length).filter fun j => (gateAt C j).op = GateOp.and

lemma largeClauseAndGates_subset {v : ℕ} (n : ℕ) (C : Circuit)
    (tag : ℕ → Option (Fin v)) : largeClauseAndGates n C tag ⊆ andGates C := by
  classical
  intro j hj
  obtain ⟨hj, hop, _⟩ := mem_filter.1 hj
  exact mem_filter.2 ⟨hj, hop⟩

lemma clause_anchor_with_small_and_bound {v n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C) (tag : ℕ → Option (Fin v))
    (U : Finset (Fin v))
    (hcover : ∀ u ∈ U, ∃ w < n + C.gates.length,
      u ∈ clauseAtoms n C tag w ∧ ∃ a ∈ clauseAtoms n C tag w, a ∉ U)
    (small : Finset ℕ) (hsmall : small ⊆ andGates C)
    (hcard : ∀ j ∈ small, (clauseAtoms n C tag (n + j)).card ≤ 1) :
    U.card + small.card ≤ (andGates C).card := by
  classical
  have hanchor := clause_anchor_and_bound hm rb tag U hcover
  have hdis : Disjoint (largeClauseAndGates n C tag) small := by
    apply Finset.disjoint_left.2
    intro j hj hs
    have hl := (mem_filter.1 hj).2.2
    have hc := hcard j hs
    omega
  have hsub : largeClauseAndGates n C tag ∪ small ⊆ andGates C :=
    union_subset (largeClauseAndGates_subset n C tag) hsmall
  have hcount := card_le_card hsub
  rw [card_union_of_disjoint hdis] at hcount
  omega

end AndClauseAtoms

namespace StarMatchingSharedAnd

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.PurePointBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.LargeGroupedBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.LinearExceptional
open PEqualNP.Outside.L_meta_2583.StarMatchingDedup

def matchingEdges {n B : ℕ} (p l : Fin B → Fin 3 → Fin n) : Finset (Sym2 (Fin n)) :=
  univ.biUnion fun b => univ.image fun i => s(p b i, l b i)

lemma matchingEdges_card_le {n B : ℕ} (p l : Fin B → Fin 3 → Fin n) :
    (matchingEdges p l).card ≤ 3 * B := by
  calc
    _ ≤ ∑ b : Fin B, (univ.image fun i => s(p b i, l b i)).card := card_biUnion_le
    _ ≤ ∑ _b : Fin B, 3 := sum_le_sum fun b _ => by
      simpa using (card_image_le :
        (univ.image fun i => s(p b i, l b i)).card ≤ (univ : Finset (Fin 3)).card)
    _ = 3 * B := by simp [Nat.mul_comm]

lemma shared_and_deficit_sufficient {t M Q A B savings : ℕ}
    (hM : M ≤ 3 * B) (hQ : Q ≤ B) (hA : A + savings = t + 4 * B)
    (hs : savings ≤ 3 * B - M + 2 * (B - Q)) : t + M + 2 * Q ≤ A + B := by
  omega

lemma assigned_star_matching_union_edge_bound {n B : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (centers : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (p l : Fin B → Fin 3 → Fin n)
    (hcover : ∀ u v, G.Adj u v →
      (∃ c ∈ centers, ∃ w ∈ L c, (u = c ∧ v = w) ∨ (u = w ∧ v = c)) ∨
      (∃ b i, (u = p b i ∧ v = l b i) ∨ (u = l b i ∧ v = p b i))) :
    G.edgeFinset.card ≤ (∑ c ∈ centers, (L c).card) + (matchingEdges p l).card := by
  classical
  let E0 : Finset (Sym2 (Fin n)) := centers.biUnion fun c => (L c).image fun v => s(c, v)
  have hsub : G.edgeFinset ⊆ E0 ∪ matchingEdges p l := by
    intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have huv : G.Adj u v := by simpa using he
      rcases hcover u v huv with hs | hm
      · obtain ⟨c, hc, w, hw, heq⟩ := hs
        apply mem_union_left
        apply mem_biUnion.2
        refine ⟨c, hc, mem_image.2 ⟨w, hw, ?_⟩⟩
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
      · obtain ⟨b, i, heq⟩ := hm
        apply mem_union_right
        apply mem_biUnion.2
        refine ⟨b, mem_univ _, mem_image.2 ⟨i, mem_univ _, ?_⟩⟩
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
  have hE0 : E0.card ≤ ∑ c ∈ centers, (L c).card := by
    calc
      E0.card ≤ ∑ c ∈ centers, ((L c).image fun v => s(c, v)).card := card_biUnion_le
      _ ≤ ∑ c ∈ centers, (L c).card := sum_le_sum fun _ _ => card_image_le
  exact (card_le_card hsub).trans ((card_union_le E0 (matchingEdges p l)).trans
    (Nat.add_le_add_right hE0 _))

lemma assigned_star_matching_union_ledger {n B : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (centers : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (p l : Fin B → Fin 3 → Fin n)
    (hcover : ∀ u v, G.Adj u v →
      (∃ c ∈ centers, ∃ w ∈ L c, (u = c ∧ v = w) ∨ (u = w ∧ v = c)) ∨
      (∃ b i, (u = p b i ∧ v = l b i) ∨ (u = l b i ∧ v = p b i))) :
    ∃ T : Finset (Fin n), Cnf.Covers G T ∧
      G.edgeFinset.card + T.card ≤ (∑ c ∈ centers, (L c).card) + centers.card +
        (matchingEdges p l).card + 3 * (lineSupports l).card := by
  obtain ⟨T, hT, hc⟩ := assigned_star_matching_dedup_cover G centers L p l hcover
  have he := assigned_star_matching_union_edge_bound G centers L p l hcover
  exact ⟨T, hT, by omega⟩

lemma indexed_and_small_or_cost {n A Z : ℕ} (C : Circuit)
    (a : Fin A → Fin C.gates.length) (z : Fin Z → Fin C.gates.length)
    (ha : Function.Injective a) (hz : Function.Injective z)
    (haop : ∀ i, (gateAt C (a i).val).op = GateOp.and)
    (hzop : ∀ i, (gateAt C (z i).val).op = GateOp.or)
    (hzsmall : ∀ i, (singletonSupport n C (n + (z i).val)).card ≤ 1) :
    (largeOrGates n C).card + A + Z ≤ C.size := by
  classical
  let An : Finset ℕ := univ.image fun i => (a i).val
  let Zn : Finset ℕ := univ.image fun i => (z i).val
  let O := largeOrGates n C
  have ha' : Function.Injective (fun i => (a i).val) := by
    intro i j hij
    exact ha (Fin.ext hij)
  have hz' : Function.Injective (fun i => (z i).val) := by
    intro i j hij
    exact hz (Fin.ext hij)
  have hAcard : An.card = A := by simp [An, card_image_of_injective _ ha']
  have hZcard : Zn.card = Z := by simp [Zn, card_image_of_injective _ hz']
  have hAop : ∀ j ∈ An, (gateAt C j).op = GateOp.and := by
    intro j hj
    obtain ⟨i, _, heq⟩ := mem_image.1 hj
    exact heq ▸ haop i
  have hZop : ∀ j ∈ Zn, (gateAt C j).op = GateOp.or := by
    intro j hj
    obtain ⟨i, _, heq⟩ := mem_image.1 hj
    exact heq ▸ hzop i
  have hZsmall : ∀ j ∈ Zn, (singletonSupport n C (n + j)).card ≤ 1 := by
    intro j hj
    obtain ⟨i, _, heq⟩ := mem_image.1 hj
    exact heq ▸ hzsmall i
  have hOA : Disjoint O An := by
    apply Finset.disjoint_left.2
    intro j hjO hjA
    have hop := (mem_filter.1 hjO).2.1
    rw [hAop j hjA] at hop
    cases hop
  have hOZ : Disjoint O Zn := by
    apply Finset.disjoint_left.2
    intro j hjO hjZ
    have hlarge := (mem_filter.1 hjO).2.2
    have hsmall := hZsmall j hjZ
    omega
  have hAZ : Disjoint An Zn := by
    apply Finset.disjoint_left.2
    intro j hjA hjZ
    have hop := hAop j hjA
    rw [hZop j hjZ] at hop
    cases hop
  have hOAZ : Disjoint (O ∪ An) Zn := by
    apply Finset.disjoint_left.2
    intro j hj hjZ
    rcases mem_union.1 hj with hjO | hjA
    · exact Finset.disjoint_left.1 hOZ hjO hjZ
    · exact Finset.disjoint_left.1 hAZ hjA hjZ
  have hsub : O ∪ An ∪ Zn ⊆ range C.gates.length := by
    intro j hj
    rcases mem_union.1 hj with hj | hjZ
    · rcases mem_union.1 hj with hjO | hjA
      · exact (mem_filter.1 hjO).1
      · obtain ⟨i, _, heq⟩ := mem_image.1 hjA
        exact heq ▸ mem_range.2 (a i).isLt
    · obtain ⟨i, _, heq⟩ := mem_image.1 hjZ
      exact heq ▸ mem_range.2 (z i).isLt
  have hcount : O.card + An.card + Zn.card ≤ C.gates.length := by
    rw [← card_union_of_disjoint hOA, ← card_union_of_disjoint hOAZ]
    simpa using card_le_card hsub
  change O.card + A + Z ≤ C.gates.length
  omega

lemma fold_shared_and_budget {edges vertices leaves centers B Q M O t A cost : ℕ}
    (hledger : edges + vertices ≤ leaves + centers + M + 3 * Q)
    (hor : leaves + Q ≤ O + t) (hcenters : centers ≤ t)
    (hamort : t + M + 2 * Q ≤ A + B)
    (hcost : O + A + t + B ≤ cost + 1) : edges + vertices ≤ cost + 1 := by
  omega

lemma assigned_star_matching_shared_and_cost {n t B A : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (centers : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (p l : Fin B → Fin 3 → Fin n)
    (hcover : ∀ u v, G.Adj u v →
      (∃ c ∈ centers, ∃ w ∈ L c, (u = c ∧ v = w) ∨ (u = w ∧ v = c)) ∨
      (∃ b i, (u = p b i ∧ v = l b i) ∨ (u = l b i ∧ v = p b i)))
    (hor : (∑ c ∈ centers, (L c).card) + (lineSupports l).card ≤
      (largeOrGates n C).card + t)
    (hcenters : centers.card ≤ t)
    (a : Fin A → Fin C.gates.length) (z : Fin (t + B - 1) → Fin C.gates.length)
    (ha : Function.Injective a) (hz : Function.Injective z)
    (haop : ∀ i, (gateAt C (a i).val).op = GateOp.and)
    (hzop : ∀ i, (gateAt C (z i).val).op = GateOp.or)
    (hzsmall : ∀ i, (singletonSupport n C (n + (z i).val)).card ≤ 1)
    (hne : 1 ≤ t + B)
    (hamort : t + (matchingEdges p l).card + 2 * (lineSupports l).card ≤ A + B) :
    ∃ T : Finset (Fin n), Cnf.Covers G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  obtain ⟨T, hT, hledger⟩ := assigned_star_matching_union_ledger G centers L p l hcover
  have hc := indexed_and_small_or_cost C a z ha hz haop hzop hzsmall
  have hcost : (largeOrGates n C).card + A + t + B ≤ C.size + 1 := by omega
  exact ⟨T, hT, fold_shared_and_budget hledger hor hcenters hamort hcost⟩

end StarMatchingSharedAnd

namespace ThinBlock.MixedEdge

open Finset

variable {n : ℕ}

def pointPart (W : Finset (Bool × Fin n)) : Finset (Fin n) :=
  univ.filter fun p => (false, p) ∈ W

def NamesEdge (I : Fin n → Fin n → Prop) (W : Finset (Bool × Fin n))
    (a s : Fin n) : Prop :=
  2 ≤ (pointPart W).card ∧ (false, a) ∈ W ∧
    ∃ ell, lines W = {ell} ∧ ell ≠ s ∧ I a ell ∧ I a s ∧
      ∀ q, (false, q) ∈ W → I q s

lemma names_edge_unique (I : Fin n → Fin n → Prop)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    {W : Finset (Bool × Fin n)} {a s b t : Fin n}
    (ha : NamesEdge I W a s) (hb : NamesEdge I W b t) : a = b ∧ s = t := by
  classical
  obtain ⟨hcard, haW, ell, hell, hne, haell, has, hpoint⟩ := ha
  obtain ⟨_, hbW, ell', hell', hne', hbell, hbt, hpoint'⟩ := hb
  have hst : s = t := by
    by_contra hst
    have hsmall : (pointPart W).card ≤ 1 := by
      apply card_le_one.mpr
      intro u hu v hv
      by_contra huv
      have huW : (false, u) ∈ W := (mem_filter.mp hu).2
      have hvW : (false, v) ∈ W := (mem_filter.mp hv).2
      exact hfour u v s t huv hst ⟨hpoint u huW, hpoint' u huW,
        hpoint v hvW, hpoint' v hvW⟩
    omega
  have heq : ell = ell' := by simpa using hell.symm.trans hell'
  subst t
  subst ell'
  refine ⟨?_, rfl⟩
  by_contra hab
  exact hfour a b ell s hab hne ⟨haell, has, hbell, hbt⟩

def Decomposition (F : Finset (Finset (Bool × Fin n)))
    (p l : Fin 3 → Fin n) (P L : Finset (Bool × Fin n))
    (C : Fin 3 → Finset (Bool × Fin n)) : Prop :=
  (∀ v, (true, v) ∉ P) ∧
  (∀ v, (false, v) ∉ L) ∧
  F = insert P (insert L (univ.image C)) ∧
  (∀ i, (false, p i) ∈ P) ∧
  (∀ i, (true, l i) ∈ L) ∧
  (∀ i, (false, p i) ∉ C i) ∧
  (∀ i, lines (C i) = {l i}) ∧
  (∀ i j, i ≠ j → (false, p j) ∈ C i)

variable {F : Finset (Finset (Bool × Fin n))} {p l : Fin 3 → Fin n}
  {P L : Finset (Bool × Fin n)} {C : Fin 3 → Finset (Bool × Fin n)}

lemma Decomposition.point_no_lines (d : Decomposition F p l P L C) :
    ∀ v, (true, v) ∉ P := d.1

lemma Decomposition.line_no_points (d : Decomposition F p l P L C) :
    ∀ v, (false, v) ∉ L := d.2.1

lemma Decomposition.exhaust (d : Decomposition F p l P L C) :
    F = insert P (insert L (univ.image C)) := d.2.2.1

lemma Decomposition.point_hits (d : Decomposition F p l P L C) :
    ∀ i, (false, p i) ∈ P := d.2.2.2.1

lemma Decomposition.line_hits (d : Decomposition F p l P L C) :
    ∀ i, (true, l i) ∈ L := d.2.2.2.2.1

lemma Decomposition.mixed_misses (d : Decomposition F p l P L C) :
    ∀ i, (false, p i) ∉ C i := d.2.2.2.2.2.1

lemma Decomposition.mixed_lines (d : Decomposition F p l P L C) :
    ∀ i, lines (C i) = {l i} := d.2.2.2.2.2.2.1

lemma Decomposition.mixed_other (d : Decomposition F p l P L C) :
    ∀ i j, i ≠ j → (false, p j) ∈ C i := d.2.2.2.2.2.2.2

lemma five_decomposition (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hthin : Thin F) (hsafe : Safe I F)
    (p l : Fin 3 → Fin n) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i))
    (hmiss : ∀ i, ∃ j, ¬ I (p i) (l j)) (hcard : F.card = 5) :
    ∃ P L C, Decomposition F p l P L C := by
  classical
  obtain ⟨L, hLF, hL⟩ := exists_pure_line_clause I F hsafe
  obtain ⟨P, hPF, hP⟩ := exists_pure_point_clause I F hsafe
  have hLp : ∀ i, (true, l i) ∈ L := fun i =>
    (hacc i L hLF).resolve_left (fun h => hL ⟨p i, h⟩)
  have hPp : ∀ i, (false, p i) ∈ P := fun i =>
    (hacc i P hPF).resolve_right (fun h => hP ⟨l i, h⟩)
  choose miss hmiss using hmiss
  have hchoice : ∀ i, ∃ W ∈ F,
      (false, p i) ∉ W ∧ (true, l (miss i)) ∉ W := fun i =>
    miss_nonedge_pair I F hsafe (hmiss i)
  choose C hCF hCp hClmiss using hchoice
  have hCl : ∀ i, (true, l i) ∈ C i := fun i =>
    (hacc i (C i) (hCF i)).resolve_left (hCp i)
  have hCpoint : ∀ i, ∃ a, (false, a) ∈ C i := by
    intro i
    by_contra hn
    have hm := hacc (miss i) (C i) (hCF i)
    exact (hm.resolve_left (fun h => hn ⟨p (miss i), h⟩) |> hClmiss i)
  have hCother : ∀ i j, i ≠ j → (false, p j) ∈ C i := by
    intro i j hij
    rcases hacc j (C i) (hCF i) with hpj | hlj
    · exact hpj
    have heq : l i = l j := card_le_one.mp (hthin (C i) (hCF i) (hCpoint i))
      (l i) (mem_filter.mpr ⟨mem_univ _, hCl i⟩)
      (l j) (mem_filter.mpr ⟨mem_univ _, hlj⟩)
    exact (hij (hl heq)).elim
  have hCinj : Function.Injective C := by
    intro i j heq
    by_contra hij
    have hpj := hCother i j hij
    rw [heq] at hpj
    exact hCp j hpj
  let D := (univ : Finset (Fin 3)).image C
  have hDcard : D.card = 3 := by
    simp [D, card_image_of_injective _ hCinj]
  have hPD : P ∉ D := by
    intro hpD
    obtain ⟨i, _, heq⟩ := mem_image.mp hpD
    exact hP ⟨l i, heq ▸ hCl i⟩
  have hLD : L ∉ D := by
    intro hlD
    obtain ⟨i, _, heq⟩ := mem_image.mp hlD
    obtain ⟨a, ha⟩ := hCpoint i
    exact hL ⟨a, heq ▸ ha⟩
  have hPL : P ≠ L := by
    intro heq
    exact hL ⟨p 0, heq ▸ hPp 0⟩
  let K := insert P (insert L D)
  have hKcard : K.card = 5 := by
    simp [K, card_insert_of_notMem, hPD, hLD, hPL, hDcard]
  have hKF : K ⊆ F := by
    intro W hW
    rcases mem_insert.mp hW with heq | hW
    · simpa [heq] using hPF
    rcases mem_insert.mp hW with heq | hW
    · simpa [heq] using hLF
    obtain ⟨i, _, heq⟩ := mem_image.mp hW
    exact heq ▸ hCF i
  have hKeq : K = F := eq_of_subset_of_card_le hKF (by omega)
  refine ⟨P, L, C, (fun v hv => hP ⟨v, hv⟩),
    (fun v hv => hL ⟨v, hv⟩), hKeq.symm, hPp, hLp, hCp, ?_, hCother⟩
  intro i
  ext v
  constructor
  · intro hv
    have heq : v = l i := card_le_one.mp (hthin (C i) (hCF i) (hCpoint i))
      v hv (l i) (mem_filter.mpr ⟨mem_univ _, hCl i⟩)
    simp [heq]
  · intro hv
    have heq : v = l i := by simpa using hv
    rw [heq]
    exact mem_filter.mpr ⟨mem_univ _, hCl i⟩

lemma Decomposition.mixed_mem {F : Finset (Finset (Bool × Fin n))}
    {p l : Fin 3 → Fin n} (d : Decomposition F p l P L C) (i : Fin 3) : C i ∈ F := by
  have h : C i ∈ insert P (insert L (univ.image C)) :=
    mem_insert_of_mem (mem_insert_of_mem (mem_image.mpr ⟨i, mem_univ _, rfl⟩))
  exact Eq.mpr (congrArg (fun S => C i ∈ S) d.exhaust) h

lemma Decomposition.point_part_large {F : Finset (Finset (Bool × Fin n))}
    {p l : Fin 3 → Fin n} (d : Decomposition F p l P L C) (hp : Function.Injective p)
    (i : Fin 3) : 2 ≤ (pointPart (C i)).card := by
  have htwo : ∀ i : Fin 3, ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by decide
  obtain ⟨j, k, hij, hik, hjk⟩ := htwo i
  exact one_lt_card.mpr ⟨p j, mem_filter.mpr ⟨mem_univ _, d.mixed_other i j hij⟩,
    p k, mem_filter.mpr ⟨mem_univ _, d.mixed_other i k hik⟩,
    fun h => hjk (hp h)⟩

lemma Decomposition.point_neighbors (I : Fin n → Fin n → Prop)
    {F : Finset (Finset (Bool × Fin n))} (hsafe : Safe I F)
    {p l : Fin 3 → Fin n} (d : Decomposition F p l P L C)
    {i j : Fin 3} (hno : ¬ I (p i) (l j)) :
    ∀ q, (false, q) ∈ C i → I q (l j) := by
  classical
  intro q hq
  let x : Bool × Fin n → Bool := fun u =>
    if u.1 then decide (u.2 = l j) else decide (u.2 = p i ∨ u.2 = q)
  have hh : ∀ W ∈ F, ∃ u ∈ W, x u = true := by
    intro W hW
    rw [d.exhaust] at hW
    rcases mem_insert.mp hW with rfl | hW
    · exact ⟨(false, p i), d.point_hits i, by simp [x]⟩
    rcases mem_insert.mp hW with rfl | hW
    · exact ⟨(true, l j), d.line_hits j, by simp [x]⟩
    obtain ⟨k, _, rfl⟩ := mem_image.mp hW
    by_cases hki : k = i
    · subst k
      exact ⟨(false, q), hq, by simp [x]⟩
    · exact ⟨(false, p i), d.mixed_other k i hki, by simp [x]⟩
  obtain ⟨a, b, hab, ha, hb⟩ := hsafe x hh
  have hapq : a = p i ∨ a = q := by simpa [x] using ha
  have hbl : b = l j := by simpa [x] using hb
  rcases hapq with hap | haq
  · exact (hno (by simpa [hap, hbl] using hab)).elim
  · simpa [haq, hbl] using hab

lemma pattern_mixed_edge_index (J : Fin 3 → Fin 3 → Prop)
    (hshape : (∀ i j, J i j ↔ i = j ∨ i = j + 1) ∨
      (∀ i j, J i j ↔ i = j ∨ i = j + 2)) :
    ∀ j, ∃ i, i ≠ j ∧ ¬ J i j ∧ J j i := by
  intro j
  rcases hshape with hshape | hshape
  · have h : ∀ j : Fin 3, ∃ i : Fin 3, i ≠ j ∧
        ¬ (i = j ∨ i = j + 1) ∧ (j = i ∨ j = i + 1) := by decide
    obtain ⟨i, hij, hno, hyes⟩ := h j
    exact ⟨i, hij, fun hJ => hno ((hshape i j).mp hJ), (hshape j i).mpr hyes⟩
  · have h : ∀ j : Fin 3, ∃ i : Fin 3, i ≠ j ∧
        ¬ (i = j ∨ i = j + 2) ∧ (j = i ∨ j = i + 2) := by decide
    obtain ⟨i, hij, hno, hyes⟩ := h j
    exact ⟨i, hij, fun hJ => hno ((hshape i j).mp hJ), (hshape j i).mpr hyes⟩

lemma every_matching_edge_named (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hthin : Thin F) (hsafe : Safe I F)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i)) (hcard : F.card = 5) :
    ∀ j, ∃ W ∈ F, NamesEdge I W (p j) (l j) := by
  have hshape := matching_three_patterns I F hthin hsafe hfour p l hp hl hacc
  obtain ⟨P, L, C, d⟩ := five_decomposition I F hthin hsafe p l hl hacc
    (pattern_missing_line (fun a b => I (p a) (l b)) hshape) hcard
  intro j
  obtain ⟨i, hij, hno, hcross⟩ :=
    pattern_mixed_edge_index (fun a b => I (p a) (l b)) hshape j
  refine ⟨C i, d.mixed_mem i, d.point_part_large hp i,
    d.mixed_other i j hij, l i, d.mixed_lines i, ?_, hcross,
    accepted_edge I F hsafe (hacc j), ?_⟩
  · exact fun h => hij (hl h)
  · exact d.point_neighbors I hsafe hno

end ThinBlock.MixedEdge

namespace ThinBlock.MixedEdge

open Finset

variable {n : ℕ}

def mixedClauses (F : Finset (Finset (Bool × Fin n))) : Finset (Finset (Bool × Fin n)) :=
  F.filter fun W => (pointPart W).Nonempty ∧ (lines W).Nonempty

lemma names_edge_is_mixed (I : Fin n → Fin n → Prop)
    {W : Finset (Bool × Fin n)} {a s : Fin n} (h : NamesEdge I W a s) :
    (pointPart W).Nonempty ∧ (lines W).Nonempty := by
  obtain ⟨_, ha, ell, hell, _⟩ := h
  constructor
  · exact ⟨a, mem_filter.mpr ⟨mem_univ _, ha⟩⟩
  · rw [hell]
    exact singleton_nonempty ell

lemma named_edges_le_mixed_clauses (I : Fin n → Fin n → Prop)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (E : Finset (Fin n × Fin n)) (F : Finset (Finset (Bool × Fin n)))
    (hname : ∀ e ∈ E, ∃ W ∈ F, NamesEdge I W e.1 e.2) :
    E.card ≤ (mixedClauses F).card := by
  classical
  have hchoice : ∀ e : {e : Fin n × Fin n // e ∈ E},
      ∃ W ∈ F, NamesEdge I W e.val.1 e.val.2 := fun e => hname e.val e.property
  choose W hWF hWname using hchoice
  have hinj : Function.Injective W := by
    intro e f heq
    have hn := hWname e
    rw [heq] at hn
    obtain ⟨hp, hl⟩ := names_edge_unique I hfour hn (hWname f)
    apply Subtype.ext
    exact Prod.ext hp hl
  have hsub : E.attach.image W ⊆ mixedClauses F := by
    intro V hV
    obtain ⟨e, _, rfl⟩ := mem_image.mp hV
    exact mem_filter.mpr ⟨hWF e, names_edge_is_mixed I (hWname e)⟩
  calc
    E.card = (E.attach.image W).card := by
      rw [card_image_of_injective _ hinj]
      exact card_attach.symm
    _ ≤ (mixedClauses F).card := card_le_card hsub

lemma matching_union_le_mixed_union {B : ℕ} (I : Fin n → Fin n → Prop)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (F : Fin B → Finset (Finset (Bool × Fin n)))
    (hthin : ∀ b, Thin (F b)) (hsafe : ∀ b, Safe I (F b))
    (p l : Fin B → Fin 3 → Fin n)
    (hp : ∀ b, Function.Injective (p b)) (hl : ∀ b, Function.Injective (l b))
    (hacc : ∀ b i, Accept (F b) (p b i) (l b i))
    (hcard : ∀ b, (F b).card = 5) :
    (univ.biUnion fun b : Fin B =>
      (univ : Finset (Fin 3)).image fun i => (p b i, l b i)).card ≤
      (mixedClauses (univ.biUnion F)).card := by
  classical
  apply named_edges_le_mixed_clauses I hfour
  intro e he
  obtain ⟨b, _, he⟩ := mem_biUnion.mp he
  obtain ⟨i, _, rfl⟩ := mem_image.mp he
  obtain ⟨W, hWF, hWname⟩ := every_matching_edge_named I (F b) (hthin b) (hsafe b)
    hfour (p b) (l b) (hp b) (hl b) (hacc b) (hcard b) i
  exact ⟨W, mem_biUnion.mpr ⟨b, mem_univ _, hWF⟩, hWname⟩

end ThinBlock.MixedEdge

namespace ThinBlock.MixedEdge

open Finset

variable {n : ℕ}

def liftLineSet (S : Finset (Fin n)) : Finset (Bool × Fin n) :=
  S.image fun v => (true, v)

def lineBearingClauses (F : Finset (Finset (Bool × Fin n))) : Finset (Finset (Bool × Fin n)) :=
  F.filter fun W => (lines W).Nonempty

lemma lines_lift (S : Finset (Fin n)) : lines (liftLineSet S) = S := by
  ext v
  simp [lines, liftLineSet]

lemma point_part_lift (S : Finset (Fin n)) : pointPart (liftLineSet S) = ∅ := by
  ext v
  simp [pointPart, liftLineSet]

lemma lift_line_injective : Function.Injective (liftLineSet (n := n)) := by
  intro S T h
  have heq := congrArg lines h
  simpa [lines_lift] using heq

lemma pure_point_anchor (I : Fin n → Fin n → Prop)
    (F U : Finset (Finset (Bool × Fin n))) (hsafe : Safe I F)
    (hU : ∀ W ∈ U, (lines W).Nonempty) : ∃ W ∈ F, W ∉ U := by
  obtain ⟨P, hPF, hP⟩ := exists_pure_point_clause I F hsafe
  refine ⟨P, hPF, ?_⟩
  intro hPU
  obtain ⟨v, hv⟩ := hU P hPU
  exact hP ⟨v, (mem_filter.mp hv).2⟩

lemma matching_edges_and_triples_le_line_clauses {B : ℕ} (I : Fin n → Fin n → Prop)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (F : Fin B → Finset (Finset (Bool × Fin n)))
    (hthin : ∀ b, Thin (F b)) (hsafe : ∀ b, Safe I (F b))
    (p l : Fin B → Fin 3 → Fin n)
    (hp : ∀ b, Function.Injective (p b)) (hl : ∀ b, Function.Injective (l b))
    (hacc : ∀ b i, Accept (F b) (p b i) (l b i))
    (hcard : ∀ b, (F b).card = 5) :
    (univ.biUnion fun b : Fin B =>
      (univ : Finset (Fin 3)).image fun i => (p b i, l b i)).card +
      ((univ : Finset (Fin B)).image fun b => (univ : Finset (Fin 3)).image (l b)).card ≤
      (lineBearingClauses (univ.biUnion F)).card := by
  classical
  let FT := univ.biUnion F
  let Q : Finset (Finset (Fin n)) := univ.image fun b : Fin B => univ.image (l b)
  let P := Q.image liftLineSet
  have hPcard : P.card = Q.card := card_image_of_injective _ lift_line_injective
  have hPsub : P ⊆ lineBearingClauses FT := by
    intro W hW
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hW
    obtain ⟨b, _, rfl⟩ := mem_image.mp hS
    have hWF : liftLineSet (univ.image (l b)) ∈ F b := by
      simpa [liftLineSet, Finset.image_image, Function.comp_def] using
        five_contains_matching_line_clause I (F b) (hthin b) (hsafe b) hfour
          (p b) (l b) (hp b) (hl b) (hacc b) (hcard b)
    apply mem_filter.mpr
    refine ⟨mem_biUnion.mpr ⟨b, mem_univ _, hWF⟩, ?_⟩
    rw [lines_lift]
    exact ⟨l b 0, mem_image.mpr ⟨0, mem_univ _, rfl⟩⟩
  have hMsub : mixedClauses FT ⊆ lineBearingClauses FT := by
    intro W hW
    obtain ⟨hWF, _, hline⟩ := mem_filter.mp hW
    exact mem_filter.mpr ⟨hWF, hline⟩
  have hdis : Disjoint (mixedClauses FT) P := by
    apply Finset.disjoint_left.mpr
    intro W hWM hWP
    obtain ⟨S, _, rfl⟩ := mem_image.mp hWP
    have hpnonempty := (mem_filter.mp hWM).2.1
    rw [point_part_lift] at hpnonempty
    exact not_nonempty_empty hpnonempty
  have hcombined : (mixedClauses FT).card + Q.card ≤ (lineBearingClauses FT).card := by
    rw [← hPcard, ← card_union_of_disjoint hdis]
    exact card_le_card (union_subset hMsub hPsub)
  have hM := matching_union_le_mixed_union I hfour F hthin hsafe p l hp hl hacc hcard
  change _ + Q.card ≤ (lineBearingClauses FT).card
  exact le_trans (Nat.add_le_add_right hM Q.card) hcombined

end ThinBlock.MixedEdge

namespace ThinBlock.MixedEdge

open Finset

variable {n B : ℕ}

def familyClauses (F : Fin B → Finset (Finset (Bool × Fin n))) :
    Finset (Finset (Bool × Fin n)) := univ.biUnion F

noncomputable def decodeClause (F : Fin B → Finset (Finset (Bool × Fin n)))
    (i : Fin (familyClauses F).card) : Finset (Bool × Fin n) :=
  ((familyClauses F).equivFin.symm i).val

noncomputable def blockAtoms (F : Fin B → Finset (Finset (Bool × Fin n))) (b : Fin B) :
    Finset (Fin (familyClauses F).card) := by
  classical
  exact univ.filter fun i => decodeClause F i ∈ F b

noncomputable def nonPointAtoms (F : Fin B → Finset (Finset (Bool × Fin n))) :
    Finset (Fin (familyClauses F).card) := by
  classical
  exact univ.filter fun i => (lines (decodeClause F i)).Nonempty

lemma decode_clause_injective (F : Fin B → Finset (Finset (Bool × Fin n))) :
    Function.Injective (decodeClause F) := by
  intro i j hij
  apply (familyClauses F).equivFin.symm.injective
  exact Subtype.ext hij

lemma decode_clause_mem (F : Fin B → Finset (Finset (Bool × Fin n)))
    (i : Fin (familyClauses F).card) : decodeClause F i ∈ familyClauses F :=
  ((familyClauses F).equivFin.symm i).property

lemma exists_decode_clause (F : Fin B → Finset (Finset (Bool × Fin n)))
    {W : Finset (Bool × Fin n)} (hW : W ∈ familyClauses F) :
    ∃ i, decodeClause F i = W := by
  refine ⟨(familyClauses F).equivFin ⟨W, hW⟩, ?_⟩
  simp [decodeClause]

lemma block_atoms_decode (F : Fin B → Finset (Finset (Bool × Fin n))) (b : Fin B) :
    (blockAtoms F b).image (decodeClause F) = F b := by
  classical
  ext W
  constructor
  · intro hW
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hW
    exact (mem_filter.mp hi).2
  · intro hW
    have hWF : W ∈ familyClauses F := mem_biUnion.mpr ⟨b, mem_univ _, hW⟩
    obtain ⟨i, hi⟩ := exists_decode_clause F hWF
    exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, by simpa [hi] using hW⟩, hi⟩

lemma nonpoint_atoms_card (F : Fin B → Finset (Finset (Bool × Fin n))) :
    (nonPointAtoms F).card = (lineBearingClauses (familyClauses F)).card := by
  classical
  have heq : (nonPointAtoms F).image (decodeClause F) = lineBearingClauses (familyClauses F) := by
    ext W
    constructor
    · intro hW
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hW
      exact mem_filter.mpr ⟨decode_clause_mem F i, (mem_filter.mp hi).2⟩
    · intro hW
      obtain ⟨hWF, hline⟩ := mem_filter.mp hW
      obtain ⟨i, hi⟩ := exists_decode_clause F hWF
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, by simpa [hi] using hline⟩, hi⟩
  rw [← heq, card_image_of_injective _ (decode_clause_injective F)]

lemma nonpoint_atoms_anchor (I : Fin n → Fin n → Prop)
    (F : Fin B → Finset (Finset (Bool × Fin n))) (hsafe : ∀ b, Safe I (F b)) :
    ∀ k ∈ nonPointAtoms F, ∃ b, k ∈ blockAtoms F b ∧
      ∃ a ∈ blockAtoms F b, a ∉ nonPointAtoms F := by
  classical
  intro k hk
  obtain ⟨b, _, hkb⟩ := mem_biUnion.mp (decode_clause_mem F k)
  obtain ⟨P, hPF, hP⟩ := exists_pure_point_clause I (F b) (hsafe b)
  have hPall : P ∈ familyClauses F := mem_biUnion.mpr ⟨b, mem_univ _, hPF⟩
  obtain ⟨a, ha⟩ := exists_decode_clause F hPall
  refine ⟨b, mem_filter.mpr ⟨mem_univ _, hkb⟩, a,
    mem_filter.mpr ⟨mem_univ _, by simpa [ha] using hPF⟩, ?_⟩
  intro haU
  have hnonempty : (lines P).Nonempty := by simpa [ha] using (mem_filter.mp haU).2
  obtain ⟨v, hv⟩ := hnonempty
  exact hP ⟨v, (mem_filter.mp hv).2⟩

lemma matching_atoms_count (I : Fin n → Fin n → Prop)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (F : Fin B → Finset (Finset (Bool × Fin n)))
    (hthin : ∀ b, Thin (F b)) (hsafe : ∀ b, Safe I (F b))
    (p l : Fin B → Fin 3 → Fin n)
    (hp : ∀ b, Function.Injective (p b)) (hl : ∀ b, Function.Injective (l b))
    (hacc : ∀ b i, Accept (F b) (p b i) (l b i))
    (hcard : ∀ b, (F b).card = 5) :
    (univ.biUnion fun b : Fin B =>
      (univ : Finset (Fin 3)).image fun i => (p b i, l b i)).card +
      ((univ : Finset (Fin B)).image fun b => (univ : Finset (Fin 3)).image (l b)).card ≤
      (nonPointAtoms F).card := by
  rw [nonpoint_atoms_card]
  exact matching_edges_and_triples_le_line_clauses I hfour F hthin hsafe p l hp hl hacc hcard

lemma mapped_matching_card_le {α : Type*} [DecidableEq α]
    (edge : Fin n → Fin n → α) (p l : Fin B → Fin 3 → Fin n) :
    (univ.biUnion fun b : Fin B =>
      (univ : Finset (Fin 3)).image fun i => edge (p b i) (l b i)).card ≤
    (univ.biUnion fun b : Fin B =>
      (univ : Finset (Fin 3)).image fun i => (p b i, l b i)).card := by
  classical
  let E := univ.biUnion fun b : Fin B =>
    (univ : Finset (Fin 3)).image fun i => (p b i, l b i)
  have hsub : (univ.biUnion fun b : Fin B =>
      (univ : Finset (Fin 3)).image fun i => edge (p b i) (l b i)) ⊆
      E.image (fun e => edge e.1 e.2) := by
    intro v hv
    obtain ⟨b, _, hv⟩ := mem_biUnion.mp hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp hv
    exact mem_image.mpr ⟨(p b i, l b i),
      mem_biUnion.mpr ⟨b, mem_univ _, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩, rfl⟩
  exact le_trans (card_le_card hsub) card_image_le

end ThinBlock.MixedEdge

namespace AnchoredStarMatchingCost

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.LargeGroupedBudget
open PEqualNP.Outside.L_meta_2583.StarMatchingDedup
open PEqualNP.Outside.L_meta_2583.StarMatchingSharedAnd
open PEqualNP.Outside.L_meta_2583.AndClauseAtoms

lemma anchored_and_star_count {v n t : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C) (tag : ℕ → Option (Fin v))
    (U : Finset (Fin v))
    (hcover : ∀ u ∈ U, ∃ w < n + C.gates.length,
      u ∈ clauseAtoms n C tag w ∧ ∃ a ∈ clauseAtoms n C tag w, a ∉ U)
    (a : Fin t → Fin C.gates.length) (ha : Function.Injective a)
    (haop : ∀ i, (gateAt C (a i).val).op = GateOp.and)
    (hasmall : ∀ i, (clauseAtoms n C tag (n + (a i).val)).card ≤ 1) :
    U.card + t ≤ (andGates C).card := by
  classical
  let small : Finset ℕ := univ.image fun i => (a i).val
  have ha' : Function.Injective (fun i => (a i).val) := by
    intro i j hij
    exact ha (Fin.ext hij)
  have hcard : small.card = t := by simp [small, card_image_of_injective _ ha']
  have hsmall : small ⊆ andGates C := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := mem_image.1 hj
    exact mem_filter.2 ⟨mem_range.2 (a i).isLt, haop i⟩
  have hsupport : ∀ j ∈ small, (clauseAtoms n C tag (n + j)).card ≤ 1 := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := mem_image.1 hj
    exact hasmall i
  have h := clause_anchor_with_small_and_bound hm rb tag U hcover small hsmall hsupport
  simpa only [hcard] using h

lemma all_and_small_or_cost {n Z : ℕ} (C : Circuit)
    (z : Fin Z → Fin C.gates.length) (hz : Function.Injective z)
    (hzop : ∀ i, (gateAt C (z i).val).op = GateOp.or)
    (hzsmall : ∀ i, (singletonSupport n C (n + (z i).val)).card ≤ 1) :
    (largeOrGates n C).card + (andGates C).card + Z ≤ C.size := by
  classical
  let O := largeOrGates n C
  let A := andGates C
  let small : Finset ℕ := univ.image fun i => (z i).val
  have hz' : Function.Injective (fun i => (z i).val) := by
    intro i j hij
    exact hz (Fin.ext hij)
  have hcard : small.card = Z := by simp [small, card_image_of_injective _ hz']
  have hsmallop : ∀ j ∈ small, (gateAt C j).op = GateOp.or := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := mem_image.1 hj
    exact hzop i
  have hsmallcard : ∀ j ∈ small, (singletonSupport n C (n + j)).card ≤ 1 := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := mem_image.1 hj
    exact hzsmall i
  have hOA : Disjoint O A := by
    apply Finset.disjoint_left.2
    intro j hjO hjA
    have ho := (mem_filter.1 hjO).2.1
    have ha := (mem_filter.1 hjA).2
    rw [ha] at ho
    cases ho
  have hOsmall : Disjoint O small := by
    apply Finset.disjoint_left.2
    intro j hjO hjS
    have hl := (mem_filter.1 hjO).2.2
    have hs := hsmallcard j hjS
    omega
  have hAsmall : Disjoint A small := by
    apply Finset.disjoint_left.2
    intro j hjA hjS
    have ha := (mem_filter.1 hjA).2
    rw [hsmallop j hjS] at ha
    cases ha
  have hOAsmall : Disjoint (O ∪ A) small := by
    apply Finset.disjoint_left.2
    intro j hj hjS
    rcases mem_union.1 hj with hjO | hjA
    · exact Finset.disjoint_left.1 hOsmall hjO hjS
    · exact Finset.disjoint_left.1 hAsmall hjA hjS
  have hsub : O ∪ A ∪ small ⊆ range C.gates.length := by
    intro j hj
    rcases mem_union.1 hj with hj | hjS
    · rcases mem_union.1 hj with hjO | hjA
      · exact (mem_filter.1 hjO).1
      · exact (mem_filter.1 hjA).1
    · obtain ⟨i, _, rfl⟩ := mem_image.1 hjS
      exact mem_range.2 (z i).isLt
  have hc : O.card + A.card + small.card ≤ C.gates.length := by
    rw [← card_union_of_disjoint hOA, ← card_union_of_disjoint hOAsmall]
    simpa using card_le_card hsub
  change O.card + A.card + Z ≤ C.gates.length
  omega

lemma assigned_star_matching_anchored_cost {v n t B : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack n C)
    (centers : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (p l : Fin B → Fin 3 → Fin n)
    (hcover : ∀ u w, G.Adj u w →
      (∃ c ∈ centers, ∃ q ∈ L c, (u = c ∧ w = q) ∨ (u = q ∧ w = c)) ∨
      (∃ b i, (u = p b i ∧ w = l b i) ∨ (u = l b i ∧ w = p b i)))
    (hor : (∑ c ∈ centers, (L c).card) + (lineSupports l).card ≤
      (largeOrGates n C).card + t)
    (hcenters : centers.card ≤ t)
    (tag : ℕ → Option (Fin v)) (U : Finset (Fin v))
    (hanchors : ∀ u ∈ U, ∃ w < n + C.gates.length,
      u ∈ clauseAtoms n C tag w ∧ ∃ a ∈ clauseAtoms n C tag w, a ∉ U)
    (hU : (matchingEdges p l).card + (lineSupports l).card ≤ U.card)
    (a : Fin t → Fin C.gates.length) (ha : Function.Injective a)
    (haop : ∀ i, (gateAt C (a i).val).op = GateOp.and)
    (hasmall : ∀ i, (clauseAtoms n C tag (n + (a i).val)).card ≤ 1)
    (z : Fin (t + B - 1) → Fin C.gates.length) (hz : Function.Injective z)
    (hzop : ∀ i, (gateAt C (z i).val).op = GateOp.or)
    (hzsmall : ∀ i, (singletonSupport n C (n + (z i).val)).card ≤ 1)
    (hne : 1 ≤ t + B) :
    ∃ T : Finset (Fin n), Cnf.Covers G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  have hand := anchored_and_star_count hm rb tag U hanchors a ha haop hasmall
  have hc := all_and_small_or_cost C z hz hzop hzsmall
  have hQ := lineSupports_card_le l
  obtain ⟨T, hT, hledger⟩ := assigned_star_matching_union_ledger G centers L p l hcover
  exact ⟨T, hT, by omega⟩

end AnchoredStarMatchingCost

namespace AnchoredStarMatchingCost

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.PurePointBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.LargeGroupedBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.LinearExceptional
open PEqualNP.Outside.L_meta_2583.StarMatchingDedup

lemma dedup_neighborhood_or_budget {n t B : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack n C)
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (centers : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (l : Fin B → Fin 3 → Fin n)
    (sources : {c : Fin n // c ∈ centers} → Finset ℕ)
    (hvalid : ∀ c, ∀ w ∈ sources c, w < n + C.gates.length)
    (hpos : ∀ c, ∀ v ∈ L c.val, ∃ w ∈ sources c,
      val C (List.ofFn (pairInput v v)) w = true)
    (hfalse : ∀ c, ∀ w ∈ sources c,
      val C (List.ofFn (complementInput (G.neighborFinset c.val))) w = false)
    (hsources : (∑ c : {c : Fin n // c ∈ centers}, (sources c).card) ≤ t)
    (hlarge : ∀ b, 1 < (univ.image (l b)).card)
    (hnot : ∀ b, ∀ c : {c : Fin n // c ∈ centers},
      ¬ univ.image (l b) ⊆ G.neighborFinset c.val)
    (hwires : ∀ b, ∃ w, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool,
        val C (List.ofFn x) w = decide (∃ v ∈ univ.image (l b), x v = true)) :
    (∑ c ∈ centers, (L c).card) + (lineSupports l).card ≤
      (largeOrGates n C).card + t := by
  classical
  have hpair : ∀ c d : {c : Fin n // c ∈ centers}, c ≠ d →
      (G.neighborFinset c.val ∩ G.neighborFinset d.val).card ≤ 1 := by
    intro c d hcd
    have heq : G.neighborFinset c.val ∩ G.neighborFinset d.val =
        univ.filter fun w => G.Adj c.val w ∧ G.Adj d.val w := by
      ext w
      simp
    rw [heq]
    exact hfour c.val d.val (fun h => hcd (Subtype.ext h))
  let Q := lineSupports l
  have hQlarge : ∀ S : {S // S ∈ Q}, 1 < S.val.card := by
    intro S
    obtain ⟨b, _, hb⟩ := mem_image.1 S.property
    simpa only [← hb] using hlarge b
  have hQnot : ∀ S : {S // S ∈ Q}, ∀ c : {c : Fin n // c ∈ centers},
      ¬ S.val ⊆ G.neighborFinset c.val := by
    intro S c
    obtain ⟨b, _, hb⟩ := mem_image.1 S.property
    simpa only [← hb] using hnot b c
  have hQwires : ∀ S : {S // S ∈ Q}, ∃ w, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool,
        val C (List.ofFn x) w = decide (∃ v ∈ S.val, x v = true) := by
    intro S
    obtain ⟨b, _, hb⟩ := mem_image.1 S.property
    simpa only [← hb] using hwires b
  have hbonus := grouped_pure_distinct_linear_bonus hm rb
    (fun c : {c : Fin n // c ∈ centers} => L c.val)
    (fun c : {c : Fin n // c ∈ centers} => G.neighborFinset c.val)
    sources hvalid hpos hfalse hpair (fun S : {S // S ∈ Q} => S.val)
    hQlarge Subtype.val_injective hQnot hQwires
  have hsum : (∑ c : {c : Fin n // c ∈ centers}, (L c.val).card) =
      ∑ c ∈ centers, (L c).card := sum_coe_sort centers (fun c => (L c).card)
  rw [hsum, Fintype.card_coe] at hbonus
  change (∑ c ∈ centers, (L c).card) + Q.card ≤ (largeOrGates n C).card + t
  omega

end AnchoredStarMatchingCost

namespace ThinBlock

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.PurePointBudget
open PEqualNP.Outside.L_meta_2583.H8Projected.LargeGroupedBudget
open PEqualNP.Outside.L_meta_2583.StarMatchingDedup
open PEqualNP.Outside.L_meta_2583.StarMatchingSharedAnd
open PEqualNP.Outside.L_meta_2583.AndClauseAtoms
open PEqualNP.Outside.L_meta_2583.AnchoredStarMatchingCost
open MixedEdge

lemma lineSupports_map_card_le {r n B : ℕ} (f : Fin r → Fin n)
    (l : Fin B → Fin 3 → Fin r) :
    (lineSupports (fun b i => f (l b i))).card ≤ (lineSupports l).card := by
  have heq : lineSupports (fun b i => f (l b i)) =
      (lineSupports l).image (fun S => S.image f) := by
    simp [lineSupports, image_image, Function.comp_def]
  rw [heq]
  exact card_image_le

lemma thin_five_anchored_shared_and_cost {r n t B v : ℕ}
    (I : Fin r → Fin r → Prop)
    (F : Fin B → Finset (Finset (Bool × Fin r)))
    (hthin : ∀ b, Thin (F b)) (hsafe : ∀ b, Safe I (F b))
    (hIfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin B → Fin 3 → Fin r)
    (hp : ∀ b, Function.Injective (p b)) (hl : ∀ b, Function.Injective (l b))
    (hacc : ∀ b i, Accept (F b) (p b i) (l b i)) (hcard : ∀ b, (F b).card = 5)
    (e : (Bool × Fin r) ≃ Fin n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hcross : ∀ a b, G.Adj (e (false, a)) (e (true, b)) → I a b)
    (hline : ∀ a b, ¬ G.Adj (e (true, a)) (e (true, b)))
    (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack n C)
    (hwires : ∀ b W, W ∈ F b → ∃ w, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool,
        val C (List.ofFn x) w = decide (∃ u ∈ W, x (e u) = true))
    (centers : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (hcover : ∀ u v, G.Adj u v →
      (∃ c ∈ centers, ∃ w ∈ L c, (u = c ∧ v = w) ∨ (u = w ∧ v = c)) ∨
      (∃ b i, (u = e (false, p b i) ∧ v = e (true, l b i)) ∨
        (u = e (true, l b i) ∧ v = e (false, p b i))))
    (hcenters : centers.card ≤ t)
    (sources : {c : Fin n // c ∈ centers} → Finset ℕ)
    (hvalid : ∀ c, ∀ w ∈ sources c, w < n + C.gates.length)
    (hpos : ∀ c, ∀ v ∈ L c.val, ∃ w ∈ sources c,
      val C (List.ofFn (pairInput v v)) w = true)
    (hfalse : ∀ c, ∀ w ∈ sources c,
      val C (List.ofFn (complementInput (G.neighborFinset c.val))) w = false)
    (hsources : (∑ c : {c : Fin n // c ∈ centers}, (sources c).card) ≤ t)
    (encode : Fin (familyClauses F).card → Fin v) (hencode : Function.Injective encode)
    (tag : ℕ → Option (Fin v))
    (houtputs : ∀ b, ∃ w, w < n + C.gates.length ∧
      (blockAtoms F b).image encode ⊆ clauseAtoms n C tag w)
    (a : Fin t → Fin C.gates.length) (ha : Function.Injective a)
    (haop : ∀ i, (gateAt C (a i).val).op = GateOp.and)
    (hasmall : ∀ i, (clauseAtoms n C tag (n + (a i).val)).card ≤ 1)
    (z : Fin (t + B - 1) → Fin C.gates.length) (hz : Function.Injective z)
    (hzop : ∀ i, (gateAt C (z i).val).op = GateOp.or)
    (hzsmall : ∀ i, (singletonSupport n C (n + (z i).val)).card ≤ 1)
    (hne : 1 ≤ t + B) :
    ∃ T : Finset (Fin n), Cnf.Covers G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  have hexceptional := fun b => five_matching_embedded_linear_root I (F b)
    (hthin b) (hsafe b) hIfour (p b) (l b) (hp b) (hl b) (hacc b) (hcard b)
    e G hcross hline C hm rb (hwires b)
  have hor := dedup_neighborhood_or_budget G C hm rb hfour centers L
    (fun b i => e (true, l b i)) sources hvalid hpos hfalse hsources
    (fun b => by have h := (hexceptional b).1; omega)
    (fun b c => (hexceptional b).2.1 c.val)
    (fun b => by
      obtain ⟨j, hj, hcomp⟩ := (hexceptional b).2.2
      have hjlt : j < C.gates.length := mem_range.1 (mem_filter.1 hj).1
      exact ⟨n + j, by omega, hcomp⟩)
  let U := (nonPointAtoms F).image encode
  have hUcard : U.card = (nonPointAtoms F).card := card_image_of_injective _ hencode
  have hanchors : ∀ u ∈ U, ∃ w < n + C.gates.length,
      u ∈ clauseAtoms n C tag w ∧
        ∃ a ∈ clauseAtoms n C tag w, a ∉ U := by
    intro u hu
    obtain ⟨u0, hu0, rfl⟩ := mem_image.1 hu
    obtain ⟨b, hub, a, hab, haU⟩ := nonpoint_atoms_anchor I F hsafe u0 hu0
    obtain ⟨w, hw, hwsub⟩ := houtputs b
    refine ⟨w, hw, hwsub (mem_image.2 ⟨u0, hub, rfl⟩), encode a,
      hwsub (mem_image.2 ⟨a, hab, rfl⟩), ?_⟩
    intro ha
    obtain ⟨a', ha', heq⟩ := mem_image.1 ha
    exact haU ((hencode heq) ▸ ha')
  have hM : (matchingEdges (fun b i => e (false, p b i))
      (fun b i => e (true, l b i))).card ≤
      (univ.biUnion fun b : Fin B =>
        (univ : Finset (Fin 3)).image fun i => (p b i, l b i)).card := by
    exact mapped_matching_card_le (fun u v => s(e (false, u), e (true, v))) p l
  have hQ := lineSupports_map_card_le (fun v => e (true, v)) l
  have hcount := matching_atoms_count I hIfour F hthin hsafe p l hp hl hacc hcard
  have hU : (matchingEdges (fun b i => e (false, p b i))
      (fun b i => e (true, l b i))).card +
      (lineSupports (fun b i => e (true, l b i))).card ≤ U.card := by
    rw [hUcard]
    exact (Nat.add_le_add hM hQ).trans hcount
  exact assigned_star_matching_anchored_cost G C hm rb centers L
    (fun b i => e (false, p b i)) (fun b i => e (true, l b i)) hcover hor hcenters
    tag U hanchors hU a ha haop hasmall z hz hzop hzsmall hne

end ThinBlock

namespace SemanticLinearTag

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.LinearRoot
open PEqualNP.Outside.L_meta_2583.AndClauseAtoms

def IsLinear (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool,
    val C (List.ofFn x) w = decide (∃ p ∈ singletonSupport n C w, x p = true)

noncomputable def semanticTag {v : ℕ} (n : ℕ) (C : Circuit)
    (encode : Finset (Fin n) → Fin v) (w : ℕ) : Option (Fin v) := by
  classical
  exact if n ≤ w ∧ IsLinear n C w then some (encode (singletonSupport n C w)) else none

lemma isLinear_of_computes {n : ℕ} {C : Circuit} {w : ℕ} {S : Finset (Fin n)}
    (hcomp : ∀ x : Fin n → Bool,
      val C (List.ofFn x) w = decide (∃ p ∈ S, x p = true)) : IsLinear n C w := by
  intro x
  rw [linear_support hcomp]
  exact hcomp x

lemma semanticTag_raw {v n : ℕ} (C : Circuit) (encode : Finset (Fin n) → Fin v)
    {w : ℕ} (hw : w < n) : semanticTag n C encode w = none := by
  simp [semanticTag, Nat.not_le.mpr hw]

lemma semanticTag_correct {v n : ℕ} {C : Circuit}
    (encode : Finset (Fin n) → Fin v) {w : ℕ} {a : Fin v}
    (htag : semanticTag n C encode w = some a) :
    ∃ S : Finset (Fin n), a = encode S ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) w = decide (∃ p ∈ S, x p = true) := by
  classical
  by_cases h : n ≤ w ∧ IsLinear n C w
  · have ha : encode (singletonSupport n C w) = a := by
      simpa [semanticTag, h] using htag
    exact ⟨singletonSupport n C w, ha.symm, h.2⟩
  · simp [semanticTag, h] at htag

lemma semanticTag_computes {v n : ℕ} {C : Circuit}
    (encode : Finset (Fin n) → Fin v) {w : ℕ} {S : Finset (Fin n)}
    (hw : n ≤ w)
    (hcomp : ∀ x : Fin n → Bool,
      val C (List.ofFn x) w = decide (∃ p ∈ S, x p = true)) :
    semanticTag n C encode w = some (encode S) := by
  have hlin := isLinear_of_computes hcomp
  simp [semanticTag, hw, hlin, linear_support hcomp]

lemma semantic_atoms_raw {v n : ℕ} (C : Circuit) (encode : Finset (Fin n) → Fin v)
    {w : ℕ} (hw : w < n) : clauseAtoms n C (semanticTag n C encode) w = ∅ := by
  rw [clauseAtoms, semanticTag_raw C encode hw]
  simp only [hw, ite_true]

lemma semantic_atoms_linear_small {v n : ℕ} {C : Circuit}
    (encode : Finset (Fin n) → Fin v) {w : ℕ} {S : Finset (Fin n)}
    (hcomp : ∀ x : Fin n → Bool,
      val C (List.ofFn x) w = decide (∃ p ∈ S, x p = true)) :
    (clauseAtoms n C (semanticTag n C encode) w).card ≤ 1 := by
  by_cases hw : w < n
  · rw [semantic_atoms_raw C encode hw]
    simp
  · have ht := semanticTag_computes encode (by omega : n ≤ w) hcomp
    rw [clauseAtoms_tagged C _ ht]
    simp

lemma semantic_star_and_small {v n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    (encode : Finset (Fin n) → Fin v) {j center leaf : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hinputs : (gateAt C j).inputs = [center, leaf]) (hcenter : center < n)
    (S : Finset (Fin n))
    (hleaf : ∀ x : Fin n → Bool,
      val C (List.ofFn x) leaf = decide (∃ p ∈ S, x p = true)) :
    (clauseAtoms n C (semanticTag n C encode) (n + j)).card ≤ 1 := by
  cases ht : semanticTag n C encode (n + j) with
  | some a =>
    rw [clauseAtoms_tagged C _ ht]
    simp
  | none =>
    exact clauseAtoms_binary_and_small rb _ hj ht hop hinputs
      (semantic_atoms_raw C encode hcenter) (semantic_atoms_linear_small encode hleaf)

lemma semantic_star_and_small_of_inputs {v n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    (encode : Finset (Fin n) → Fin v) {j center leaf : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hinputs : ∀ w ∈ (gateAt C j).inputs, w = center ∨ w = leaf) (hcenter : center < n)
    (S : Finset (Fin n))
    (hleaf : ∀ x : Fin n → Bool,
      val C (List.ofFn x) leaf = decide (∃ p ∈ S, x p = true)) :
    (clauseAtoms n C (semanticTag n C encode) (n + j)).card ≤ 1 := by
  cases ht : semanticTag n C encode (n + j) with
  | some a =>
    rw [clauseAtoms_tagged C _ ht]
    simp
  | none =>
    rw [clauseAtoms_and rb _ hj ht hop]
    have hsub : (gateAt C j).inputs.toFinset.biUnion
        (clauseAtoms n C (semanticTag n C encode)) ⊆
          clauseAtoms n C (semanticTag n C encode) leaf := by
      intro a ha
      obtain ⟨w, hw, haw⟩ := mem_biUnion.1 ha
      rcases hinputs w (List.mem_toFinset.1 hw) with rfl | rfl
      · rw [semantic_atoms_raw C encode hcenter] at haw
        simp at haw
      · exact haw
    exact (card_le_card hsub).trans (semantic_atoms_linear_small encode hleaf)

noncomputable def supportEncoding (n : ℕ) :
    Finset (Fin n) ≃ Fin (Fintype.card (Finset (Fin n))) := Fintype.equivFin _

noncomputable def allLinearTag (n : ℕ) (C : Circuit) :
    ℕ → Option (Fin (Fintype.card (Finset (Fin n)))) :=
  semanticTag n C (supportEncoding n)

lemma supportEncoding_injective (n : ℕ) : Function.Injective (supportEncoding n) :=
  (supportEncoding n).injective

end SemanticLinearTag

namespace SemanticLinearTag

open Finset
open PEqualNP.Outside.L_meta_2583.ThinBlock.MixedEdge

noncomputable def familyClauseEncoding {r n B v : ℕ}
    (F : Fin B → Finset (Finset (Bool × Fin r))) (e : (Bool × Fin r) ≃ Fin n)
    (encode : Finset (Fin n) → Fin v) : Fin (familyClauses F).card → Fin v :=
  fun i => encode ((decodeClause F i).image e)

lemma familyClauseEncoding_injective {r n B v : ℕ}
    (F : Fin B → Finset (Finset (Bool × Fin r))) (e : (Bool × Fin r) ≃ Fin n)
    (encode : Finset (Fin n) → Fin v) (hencode : Function.Injective encode) :
    Function.Injective (familyClauseEncoding F e encode) :=
  hencode.comp ((Finset.image_injective e.injective).comp (decode_clause_injective F))

lemma blockAtoms_familyClauseEncoding {r n B v : ℕ}
    (F : Fin B → Finset (Finset (Bool × Fin r))) (e : (Bool × Fin r) ≃ Fin n)
    (encode : Finset (Fin n) → Fin v) (b : Fin B) :
    (blockAtoms F b).image (familyClauseEncoding F e encode) =
      (F b).image (fun W => encode (W.image e)) := by
  rw [← block_atoms_decode F b, image_image]
  rfl

end SemanticLinearTag

namespace CnfLogic

open Finset

variable {α : Type*}

def Clause (W : Finset α) (x : α → Bool) : Prop := ∃ u ∈ W, x u = true

def Holds (F : Finset (Finset α)) (x : α → Bool) : Prop := ∀ W ∈ F, Clause W x

def Antichain (F : Finset (Finset α)) : Prop :=
  ∀ W ∈ F, ∀ V ∈ F, V ⊆ W → V = W

lemma implies_clause_iff (F : Finset (Finset α)) (S : Finset α) :
    (∀ x : α → Bool, Holds F x → Clause S x) ↔ ∃ W ∈ F, W ⊆ S := by
  classical
  constructor
  · intro himp
    by_contra hn
    push Not at hn
    let x : α → Bool := fun u => decide (u ∉ S)
    have hF : Holds F x := by
      intro W hW
      obtain ⟨u, huW, huS⟩ := Finset.not_subset.mp (hn W hW)
      exact ⟨u, huW, by simpa [x] using huS⟩
    obtain ⟨u, huS, hxu⟩ := himp x hF
    have hu : u ∉ S := by simpa [x] using hxu
    exact hu huS
  · rintro ⟨W, hWF, hWS⟩ x hF
    obtain ⟨u, huW, hxu⟩ := hF W hWF
    exact ⟨u, hWS huW, hxu⟩

lemma fails_complement [DecidableEq α] (F : Finset (Finset α))
    {W : Finset α} (hW : W ∈ F) :
    ¬ Holds F (fun u => decide (u ∉ W)) := by
  intro hF
  obtain ⟨u, huW, hxu⟩ := hF W hW
  have hu : u ∉ W := by simpa using hxu
  exact hu huW

lemma prime_of_antichain (F : Finset (Finset α)) (hanti : Antichain F)
    {W S : Finset α} (hW : W ∈ F) (hSW : S ⊆ W)
    (himp : ∀ x : α → Bool, Holds F x → Clause S x) : W ⊆ S := by
  obtain ⟨V, hVF, hVS⟩ := (implies_clause_iff F S).mp himp
  have hVW : V = W := hanti W hW V hVF (Subset.trans hVS hSW)
  exact hVW ▸ hVS

lemma holds_erase_iff [DecidableEq α] (F : Finset (Finset α)) (W V : Finset α)
    (hVF : V ∈ F) (hVW : V ≠ W) (hsub : V ⊆ W) :
    ∀ x : α → Bool, Holds (F.erase W) x ↔ Holds F x := by
  classical
  intro x
  constructor
  · intro h U hU
    by_cases hUW : U = W
    · obtain ⟨u, huV, hxu⟩ := h V (mem_erase.mpr ⟨hVW, hVF⟩)
      exact ⟨u, hUW.symm ▸ hsub huV, hxu⟩
    · exact h U (mem_erase.mpr ⟨hUW, hU⟩)
  · intro h U hU
    exact h U (mem_erase.mp hU).2

lemma no_unit_of_large_clauses (F : Finset (Finset α))
    (hsize : ∀ W ∈ F, 2 ≤ W.card) :
    ∀ i : α, ∃ x : α → Bool, Holds F x ∧ x i = false := by
  classical
  intro i
  let x : α → Bool := fun u => decide (u ≠ i)
  refine ⟨x, ?_, by simp [x]⟩
  intro W hW
  have hnot : ¬ W ⊆ {i} := by
    intro hsub
    have hc := card_le_card hsub
    have hs := hsize W hW
    simp only [card_singleton] at hc
    omega
  obtain ⟨u, huW, hui⟩ := Finset.not_subset.mp hnot
  exact ⟨u, huW, by simpa [x] using hui⟩

lemma equivalent_antichain_subset (F K : Finset (Finset α))
    (hanti : Antichain F) (hequiv : ∀ x : α → Bool, Holds F x ↔ Holds K x) : F ⊆ K := by
  intro W hWF
  have hKW : ∀ x : α → Bool, Holds K x → Clause W x := fun x hx =>
    (hequiv x).mpr hx W hWF
  obtain ⟨V, hVK, hVW⟩ := (implies_clause_iff K W).mp hKW
  have hFV : ∀ x : α → Bool, Holds F x → Clause V x := fun x hx =>
    (hequiv x).mp hx V hVK
  have hWV := prime_of_antichain F hanti hWF hVW hFV
  have heq : V = W := Subset.antisymm hVW hWV
  exact heq ▸ hVK

lemma antichain_irredundant [DecidableEq α] (F : Finset (Finset α))
    (hanti : Antichain F) {W : Finset α} (hW : W ∈ F) :
    ∃ x : α → Bool, Holds (F.erase W) x ∧ ¬ Clause W x := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨V, hVF, hVW⟩ := (implies_clause_iff (F.erase W) W).mp hn
  have heq := hanti W hW V (mem_erase.mp hVF).2 hVW
  exact (mem_erase.mp hVF).1 heq

end CnfLogic

namespace ThinBlock

open Finset

variable {n : ℕ}

lemma five_le_card_of_matching_three (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hthin : Thin F) (hsafe : Safe I F)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i)) : 5 ≤ F.card := by
  have hshape := matching_three_patterns I F hthin hsafe hfour p l hp hl hacc
  have hmiss := pattern_missing_line (fun a b => I (p a) (l b)) hshape
  classical
  obtain ⟨L, hLF, hL⟩ := exists_pure_line_clause I F hsafe
  obtain ⟨P, hPF, hP⟩ := exists_pure_point_clause I F hsafe
  have hLp : ∀ i, (true, l i) ∈ L := fun i =>
    (hacc i L hLF).resolve_left (fun h => hL ⟨p i, h⟩)
  have hPp : ∀ i, (false, p i) ∈ P := fun i =>
    (hacc i P hPF).resolve_right (fun h => hP ⟨l i, h⟩)
  choose miss hmiss using hmiss
  have hchoice : ∀ i, ∃ W ∈ F,
      (false, p i) ∉ W ∧ (true, l (miss i)) ∉ W := fun i =>
    miss_nonedge_pair I F hsafe (hmiss i)
  choose C hCF hCp hClmiss using hchoice
  have hCl : ∀ i, (true, l i) ∈ C i := fun i =>
    (hacc i (C i) (hCF i)).resolve_left (hCp i)
  have hCpoint : ∀ i, ∃ a, (false, a) ∈ C i := by
    intro i
    by_contra hn
    have hm := hacc (miss i) (C i) (hCF i)
    exact (hm.resolve_left (fun h => hn ⟨p (miss i), h⟩) |> hClmiss i)
  have hCother : ∀ i j, i ≠ j → (false, p j) ∈ C i := by
    intro i j hij
    rcases hacc j (C i) (hCF i) with hpj | hlj
    · exact hpj
    have heq : l i = l j := card_le_one.mp (hthin (C i) (hCF i) (hCpoint i))
      (l i) (mem_filter.mpr ⟨mem_univ _, hCl i⟩)
      (l j) (mem_filter.mpr ⟨mem_univ _, hlj⟩)
    exact (hij (hl heq)).elim
  have hCinj : Function.Injective C := by
    intro i j heq
    by_contra hij
    have hpj := hCother i j hij
    rw [heq] at hpj
    exact hCp j hpj
  let D := (univ : Finset (Fin 3)).image C
  have hDcard : D.card = 3 := by
    simp [D, card_image_of_injective _ hCinj]
  have hPD : P ∉ D := by
    intro hpD
    obtain ⟨i, _, heq⟩ := mem_image.mp hpD
    exact hP ⟨l i, heq ▸ hCl i⟩
  have hLD : L ∉ D := by
    intro hlD
    obtain ⟨i, _, heq⟩ := mem_image.mp hlD
    obtain ⟨a, ha⟩ := hCpoint i
    exact hL ⟨a, heq ▸ ha⟩
  have hPL : P ≠ L := by
    intro heq
    exact hL ⟨p 0, heq ▸ hPp 0⟩
  let K := insert P (insert L D)
  have hKcard : K.card = 5 := by
    simp [K, card_insert_of_notMem, hPD, hLD, hPL, hDcard]
  have hKF : K ⊆ F := by
    intro W hW
    rcases mem_insert.mp hW with heq | hW
    · simpa [heq] using hPF
    rcases mem_insert.mp hW with heq | hW
    · simpa [heq] using hLF
    obtain ⟨i, _, heq⟩ := mem_image.mp hW
    exact heq ▸ hCF i
  have hc := card_le_card hKF
  omega

lemma clause_card_of_matching_three (F : Finset (Finset (Bool × Fin n)))
    (p l : Fin 3 → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i)) : ∀ W ∈ F, 3 ≤ W.card := by
  classical
  intro W hW
  let chosen : Fin 3 → Bool × Fin n := fun i =>
    if (false, p i) ∈ W then (false, p i) else (true, l i)
  have hchosen : ∀ i, chosen i ∈ W := by
    intro i
    by_cases hi : (false, p i) ∈ W
    · simp [chosen, hi]
    · simpa [chosen, hi] using (hacc i W hW).resolve_left hi
  have hinj : Function.Injective chosen := by
    intro i j hij
    by_cases hi : (false, p i) ∈ W
    · by_cases hj : (false, p j) ∈ W
      · apply hp
        simpa [chosen, hi, hj] using congrArg Prod.snd hij
      · simp [chosen, hi, hj] at hij
    · by_cases hj : (false, p j) ∈ W
      · simp [chosen, hi, hj] at hij
      · apply hl
        simpa [chosen, hi, hj] using congrArg Prod.snd hij
  have hsub : univ.image chosen ⊆ W := by
    intro u hu
    obtain ⟨i, _, rfl⟩ := mem_image.mp hu
    exact hchosen i
  have hc := card_le_card hsub
  simpa [card_image_of_injective _ hinj] using hc

lemma five_clause_antichain (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hthin : Thin F) (hsafe : Safe I F)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i)) (hcard : F.card = 5) : CnfLogic.Antichain F := by
  classical
  intro W hWF V hVF hsub
  by_contra hne
  have hthin' : Thin (F.erase W) := by
    intro U hU hpoint
    exact hthin U (mem_erase.mp hU).2 hpoint
  have hsafe' : Safe I (F.erase W) := by
    intro x hx
    apply hsafe x
    exact (CnfLogic.holds_erase_iff F W V hVF hne hsub x).mp hx
  have hacc' : ∀ i, Accept (F.erase W) (p i) (l i) := by
    intro i U hU
    exact hacc i U (mem_erase.mp hU).2
  have hc := five_le_card_of_matching_three I (F.erase W) hthin' hsafe'
    hfour p l hp hl hacc'
  have hcerase : (F.erase W).card = 4 := by simp [card_erase_of_mem hWF, hcard]
  omega

lemma five_clause_prime (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Bool × Fin n))) (hthin : Thin F) (hsafe : Safe I F)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i)) (hcard : F.card = 5)
    {W S : Finset (Bool × Fin n)} (hW : W ∈ F) (hSW : S ⊆ W)
    (himp : ∀ x, CnfLogic.Holds F x → CnfLogic.Clause S x) : W ⊆ S := by
  exact CnfLogic.prime_of_antichain F
    (five_clause_antichain I F hthin hsafe hfour p l hp hl hacc hcard) hW hSW himp

lemma matching_three_no_unit (F : Finset (Finset (Bool × Fin n)))
    (p l : Fin 3 → Fin n) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i)) :
    ∀ u : Bool × Fin n, ∃ x, CnfLogic.Holds F x ∧ x u = false := by
  apply CnfLogic.no_unit_of_large_clauses F
  intro W hW
  have hc := clause_card_of_matching_three F p l hp hl hacc W hW
  omega

end ThinBlock

namespace CnfLogic

open Finset

variable {α β : Type*} [DecidableEq β]

lemma clause_image (W : Finset α) (e : α → β) (x : β → Bool) :
    Clause (W.image e) x ↔ Clause W (fun u => x (e u)) := by
  constructor
  · rintro ⟨v, hv, hx⟩
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hv
    exact ⟨u, hu, hx⟩
  · rintro ⟨u, hu, hx⟩
    exact ⟨e u, mem_image.mpr ⟨u, hu, rfl⟩, hx⟩

lemma holds_image (F : Finset (Finset α)) (e : α → β) (x : β → Bool) :
    Holds (F.image (fun W => W.image e)) x ↔ Holds F (fun u => x (e u)) := by
  constructor
  · intro h W hW
    exact (clause_image W e x).mp (h (W.image e) (mem_image.mpr ⟨W, hW, rfl⟩))
  · intro h V hV
    obtain ⟨W, hW, rfl⟩ := mem_image.mp hV
    exact (clause_image W e x).mpr (h W hW)

lemma antichain_image (F : Finset (Finset α)) (e : α → β)
    (he : Function.Injective e) (hanti : Antichain F) :
    Antichain (F.image (fun W => W.image e)) := by
  intro W hW V hV hsub
  obtain ⟨W₀, hW₀, rfl⟩ := mem_image.mp hW
  obtain ⟨V₀, hV₀, rfl⟩ := mem_image.mp hV
  have hsub₀ : V₀ ⊆ W₀ := by
    intro v hv
    have hv' := hsub (mem_image.mpr ⟨v, hv, rfl⟩)
    obtain ⟨w, hw, heq⟩ := mem_image.mp hv'
    exact he heq ▸ hw
  exact congrArg (fun A : Finset α => A.image e) (hanti W₀ hW₀ V₀ hV₀ hsub₀)

lemma clause_card_image (F : Finset (Finset α)) (e : α → β)
    (he : Function.Injective e) (k : ℕ) (hsize : ∀ W ∈ F, k ≤ W.card) :
    ∀ V ∈ F.image (fun W => W.image e), k ≤ V.card := by
  intro V hV
  obtain ⟨W, hW, rfl⟩ := mem_image.mp hV
  simpa [card_image_of_injective W he] using hsize W hW

lemma family_card_image (F : Finset (Finset α)) (e : α → β)
    (he : Function.Injective e) :
    (F.image (fun W => W.image e)).card = F.card := by
  exact card_image_of_injective F (Finset.image_injective he)

end CnfLogic

namespace AndCorePrime

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.PurePointBudget
open PEqualNP.Outside.L_meta_2583.AndClauseAtoms

/-- A valid wire set closed through untagged AND gates. -/
def CoreClosed {v : ℕ} (n : ℕ) (C : Circuit)
    (tag : ℕ → Option (Fin v)) (R : Finset ℕ) : Prop :=
  (∀ w ∈ R, w < n + C.gates.length) ∧
  ∀ w ∈ R, n ≤ w → tag w = none →
    (gateAt C (w - n)).op = GateOp.and ∧
      ∀ i ∈ (gateAt C (w - n)).inputs, i ∈ R

lemma prime_clause_survives {n v : ℕ} {C : Circuit}
    (rb : ReadsBack n C) (tag : ℕ → Option (Fin v))
    (encode : Finset (Fin n) → Fin v) (R : Finset ℕ)
    (hcore : CoreClosed n C tag R)
    (htag : ∀ w ∈ R, ∀ a, tag w = some a →
      ∃ S : Finset (Fin n), a = encode S ∧
        ∀ x : Fin n → Bool, val C (List.ofFn x) w =
          decide (∃ i ∈ S, x i = true))
    (f : (Fin n → Bool) → Bool) (W : Finset (Fin n)) (hcard : 2 ≤ W.card)
    (hprime : ∀ S : Finset (Fin n), S ⊆ W →
      (∀ x : Fin n → Bool, f x = true → ∃ i ∈ S, x i = true) → W ⊆ S)
    {w : ℕ} (hw : w ∈ R)
    (himp : ∀ x : Fin n → Bool, f x = true → val C (List.ofFn x) w = true)
    (hfalse : val C (List.ofFn (complementInput W)) w = false) :
    encode W ∈ clauseAtoms n C tag w := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    cases ht : tag w with
    | some a =>
      obtain ⟨S, ha, hlinear⟩ := htag w hw a ht
      have hSW : S ⊆ W := by
        intro i hi
        by_contra hnot
        have hp : ∃ j ∈ S, complementInput W j = true :=
          ⟨i, hi, by simp [complementInput, hnot]⟩
        have hv : val C (List.ofFn (complementInput W)) w = true := by
          rw [hlinear]
          simp [hp]
        rw [hfalse] at hv
        cases hv
      have hS : ∀ x : Fin n → Bool, f x = true → ∃ i ∈ S, x i = true := by
        intro x hx
        have hv := himp x hx
        rw [hlinear] at hv
        exact of_decide_eq_true hv
      have heq : S = W := Finset.Subset.antisymm hSW (hprime S hSW hS)
      rw [clauseAtoms_tagged C tag ht, ha, heq]
      simp
    | none =>
      by_cases hin : w < n
      · let i : Fin n := ⟨w, hin⟩
        have hiW : i ∈ W := by
          by_contra hnot
          have hv : val C (List.ofFn (complementInput W)) w = true := by
            change val C (List.ofFn (complementInput W)) i.val = true
            rw [val_ofFn]
            simp [complementInput, hnot]
          rw [hfalse] at hv
          cases hv
        have hsingle : ({i} : Finset (Fin n)) ⊆ W := by simpa using hiW
        have hunit : ∀ x : Fin n → Bool, f x = true →
            ∃ j ∈ ({i} : Finset (Fin n)), x j = true := by
          intro x hx
          refine ⟨i, by simp, ?_⟩
          have hv := himp x hx
          change val C (List.ofFn x) i.val = true at hv
          simpa only [val_ofFn] using hv
        have hle := card_le_card (hprime {i} hsingle hunit)
        simp only [card_singleton] at hle
        omega
      · have hge : n ≤ w := by omega
        have hj : w - n < C.gates.length := by have hv := hcore.1 w hw; omega
        have hw_eq : n + (w - n) = w := Nat.add_sub_of_le hge
        obtain ⟨hop, hchildren⟩ := hcore.2 w hw hge ht
        have hchild : ∃ i ∈ (gateAt C (w - n)).inputs,
            val C (List.ofFn (complementInput W)) i = false := by
          by_contra hnone
          push Not at hnone
          have hv : val C (List.ofFn (complementInput W)) w = true := by
            rw [← hw_eq, val_and (by simp) hj hop]
            intro i hi
            refine ⟨rb (w - n) hj i hi, ?_⟩
            cases hh : val C (List.ofFn (complementInput W)) i with
            | false => exact False.elim (hnone i hi hh)
            | true => rfl
          rw [hfalse] at hv
          cases hv
        obtain ⟨i, hi, hifalse⟩ := hchild
        have hiless : i < w := by simpa only [hw_eq] using rb (w - n) hj i hi
        have hiimp : ∀ x : Fin n → Bool, f x = true → val C (List.ofFn x) i = true := by
          intro x hx
          have hv := himp x hx
          rw [← hw_eq] at hv
          exact ((val_and (by simp) hj hop).1 hv i hi).2
        have hmem := ih i hiless (hchildren i hi) hiimp hifalse
        rw [← hw_eq, clauseAtoms_and rb tag hj (by simpa only [hw_eq] using ht) hop]
        exact mem_biUnion.mpr ⟨i, List.mem_toFinset.mpr hi, hmem⟩

lemma prime_clause_at_root {n v : ℕ} {C : Circuit}
    (rb : ReadsBack n C) (tag : ℕ → Option (Fin v))
    (encode : Finset (Fin n) → Fin v) (R : Finset ℕ)
    (hcore : CoreClosed n C tag R)
    (htag : ∀ w ∈ R, ∀ a, tag w = some a →
      ∃ S : Finset (Fin n), a = encode S ∧
        ∀ x : Fin n → Bool, val C (List.ofFn x) w =
          decide (∃ i ∈ S, x i = true))
    {root : ℕ} (hroot : root ∈ R) (W : Finset (Fin n)) (hcard : 2 ≤ W.card)
    (hclause : ∀ x : Fin n → Bool, val C (List.ofFn x) root = true →
      ∃ i ∈ W, x i = true)
    (hprime : ∀ S : Finset (Fin n), S ⊆ W →
      (∀ x : Fin n → Bool, val C (List.ofFn x) root = true →
        ∃ i ∈ S, x i = true) → W ⊆ S) :
    encode W ∈ clauseAtoms n C tag root := by
  classical
  have hfalse : val C (List.ofFn (complementInput W)) root = false := by
    cases hval : val C (List.ofFn (complementInput W)) root with
    | false => rfl
    | true =>
      obtain ⟨i, hi, htrue⟩ := hclause (complementInput W) hval
      simp [complementInput, hi] at htrue
  exact prime_clause_survives rb tag encode R hcore htag
    (fun x => val C (List.ofFn x) root) W hcard hprime hroot
    (fun _ hx => hx) hfalse

lemma prime_family_at_root {n v : ℕ} {C : Circuit}
    (rb : ReadsBack n C) (tag : ℕ → Option (Fin v))
    (encode : Finset (Fin n) → Fin v) (R : Finset ℕ)
    (hcore : CoreClosed n C tag R)
    (htag : ∀ w ∈ R, ∀ a, tag w = some a →
      ∃ S : Finset (Fin n), a = encode S ∧
        ∀ x : Fin n → Bool, val C (List.ofFn x) w =
          decide (∃ i ∈ S, x i = true))
    {root : ℕ} (hroot : root ∈ R) (F : Finset (Finset (Fin n)))
    (hcard : ∀ W ∈ F, 2 ≤ W.card)
    (hclause : ∀ W ∈ F, ∀ x : Fin n → Bool,
      val C (List.ofFn x) root = true → ∃ i ∈ W, x i = true)
    (hprime : ∀ W ∈ F, ∀ S : Finset (Fin n), S ⊆ W →
      (∀ x : Fin n → Bool, val C (List.ofFn x) root = true →
        ∃ i ∈ S, x i = true) → W ⊆ S) :
    F.image encode ⊆ clauseAtoms n C tag root := by
  classical
  intro a ha
  obtain ⟨W, hW, rfl⟩ := mem_image.mp ha
  exact prime_clause_at_root rb tag encode R hcore htag hroot W (hcard W hW)
    (hclause W hW) (hprime W hW)

end AndCorePrime

namespace AndCorePrime

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.AndClauseAtoms
open PEqualNP.Outside.L_meta_2583.SemanticLinearTag

/-- A shared AND core with exact-linear terminals and valid wire references. -/
def LinearAndCore (n : ℕ) (C : Circuit) (R : Finset ℕ) : Prop :=
  (∀ w ∈ R, w < n + C.gates.length) ∧
  ∀ w ∈ R, n ≤ w → IsLinear n C w ∨
    ((gateAt C (w - n)).op = GateOp.and ∧
      ∀ i ∈ (gateAt C (w - n)).inputs, i ∈ R)

lemma linearAndCore_closed {n v : ℕ} {C : Circuit}
    (encode : Finset (Fin n) → Fin v) {R : Finset ℕ}
    (hcore : LinearAndCore n C R) : CoreClosed n C (semanticTag n C encode) R := by
  classical
  refine ⟨hcore.1, ?_⟩
  intro w hw hge hnone
  rcases hcore.2 w hw hge with hlin | hand
  · simp [semanticTag, hge, hlin] at hnone
  · exact hand

lemma linear_core_prime_family {n v : ℕ} {C : Circuit}
    (rb : ReadsBack n C) (encode : Finset (Fin n) → Fin v)
    (R : Finset ℕ) (hcore : LinearAndCore n C R)
    {root : ℕ} (hroot : root ∈ R) (F : Finset (Finset (Fin n)))
    (hcard : ∀ W ∈ F, 2 ≤ W.card)
    (hclause : ∀ W ∈ F, ∀ x : Fin n → Bool,
      val C (List.ofFn x) root = true → ∃ i ∈ W, x i = true)
    (hprime : ∀ W ∈ F, ∀ S : Finset (Fin n), S ⊆ W →
      (∀ x : Fin n → Bool, val C (List.ofFn x) root = true →
        ∃ i ∈ S, x i = true) → W ⊆ S) :
    F.image encode ⊆ clauseAtoms n C (semanticTag n C encode) root := by
  apply prime_family_at_root rb (semanticTag n C encode) encode R
    (linearAndCore_closed encode hcore) ?_ hroot F hcard hclause hprime
  intro w hw a htag
  exact semanticTag_correct encode htag

end AndCorePrime

namespace AndCorePrime

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.AndClauseAtoms
open PEqualNP.Outside.L_meta_2583.SemanticLinearTag

lemma clause_atom_origin {n v : ℕ} (C : Circuit) (tag : ℕ → Option (Fin v))
    {w : ℕ} {a : Fin v} (hmem : a ∈ clauseAtoms n C tag w) :
    ∃ u ≤ w, tag u = some a := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    cases ht : tag w with
    | some b =>
      rw [clauseAtoms_tagged C tag ht] at hmem
      have hab : a = b := mem_singleton.mp hmem
      exact ⟨w, le_rfl, by simpa only [hab] using ht⟩
    | none =>
      rw [clauseAtoms, ht] at hmem
      by_cases hin : w < n
      · simp [hin] at hmem
      · simp only [hin, ite_false] at hmem
        by_cases hop : (gateAt C (w - n)).op = GateOp.and
        · simp only [hop, ite_true] at hmem
          obtain ⟨i, hi, hai⟩ := mem_biUnion.mp hmem
          by_cases hiw : i < w
          · simp only [hiw, dite_true] at hai
            obtain ⟨u, hui, hu⟩ := ih i hiw hai
            exact ⟨u, hui.trans (Nat.le_of_lt hiw), hu⟩
          · simp [hiw] at hai
        · simp [hop] at hmem

lemma semantic_atom_has_linear_wire {n v : ℕ} {C : Circuit}
    (encode : Finset (Fin n) → Fin v) (hinj : Function.Injective encode)
    {root : ℕ} (hroot : root < n + C.gates.length) (W : Finset (Fin n))
    (hmem : encode W ∈ clauseAtoms n C (semanticTag n C encode) root) :
    ∃ w < n + C.gates.length, ∀ x : Fin n → Bool,
      val C (List.ofFn x) w = decide (∃ i ∈ W, x i = true) := by
  obtain ⟨w, hw, htag⟩ := clause_atom_origin C (semanticTag n C encode) hmem
  obtain ⟨S, hS, hcomp⟩ := semanticTag_correct encode htag
  have hWS : W = S := hinj hS
  exact ⟨w, lt_of_le_of_lt hw hroot, by simpa only [hWS] using hcomp⟩

lemma semantic_family_has_linear_wires {n v : ℕ} {C : Circuit}
    (encode : Finset (Fin n) → Fin v) (hinj : Function.Injective encode)
    {root : ℕ} (hroot : root < n + C.gates.length) (F : Finset (Finset (Fin n)))
    (hcover : F.image encode ⊆ clauseAtoms n C (semanticTag n C encode) root) :
    ∀ W ∈ F, ∃ w < n + C.gates.length, ∀ x : Fin n → Bool,
      val C (List.ofFn x) w = decide (∃ i ∈ W, x i = true) := by
  intro W hW
  exact semantic_atom_has_linear_wire encode hinj hroot W
    (hcover (mem_image.mpr ⟨W, hW, rfl⟩))

end AndCorePrime

namespace AndCorePrime

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.AndClauseAtoms
open PEqualNP.Outside.L_meta_2583.SemanticLinearTag

lemma linear_core_cnf_family {n v : ℕ} {C : Circuit}
    (rb : ReadsBack n C) (encode : Finset (Fin n) → Fin v)
    (R : Finset ℕ) (hcore : LinearAndCore n C R)
    {root : ℕ} (hroot : root ∈ R) (F : Finset (Finset (Fin n)))
    (hcard : ∀ W ∈ F, 2 ≤ W.card) (hanti : CnfLogic.Antichain F)
    (hcnf : ∀ x : Fin n → Bool,
      val C (List.ofFn x) root = true ↔ CnfLogic.Holds F x) :
    F.image encode ⊆ clauseAtoms n C (semanticTag n C encode) root := by
  apply linear_core_prime_family rb encode R hcore hroot F hcard
  · intro W hW x hx
    exact (hcnf x).mp hx W hW
  · intro W hW S hSW himp
    exact CnfLogic.prime_of_antichain F hanti hW hSW
      (fun x hx => himp x ((hcnf x).mpr hx))

lemma linear_core_cnf_certificate {n v : ℕ} {C : Circuit}
    (rb : ReadsBack n C) (encode : Finset (Fin n) → Fin v)
    (hinj : Function.Injective encode)
    (R : Finset ℕ) (hcore : LinearAndCore n C R)
    {root : ℕ} (hroot : root ∈ R) (F : Finset (Finset (Fin n)))
    (hcard : ∀ W ∈ F, 2 ≤ W.card) (hanti : CnfLogic.Antichain F)
    (hcnf : ∀ x : Fin n → Bool,
      val C (List.ofFn x) root = true ↔ CnfLogic.Holds F x) :
    (F.image encode ⊆ clauseAtoms n C (semanticTag n C encode) root) ∧
      ∀ W ∈ F, ∃ w < n + C.gates.length, ∀ x : Fin n → Bool,
        val C (List.ofFn x) w = decide (∃ i ∈ W, x i = true) := by
  have hcover := linear_core_cnf_family rb encode R hcore hroot F hcard hanti hcnf
  exact ⟨hcover, semantic_family_has_linear_wires encode hinj
    (hcore.1 root hroot) F hcover⟩

end AndCorePrime

namespace ThinBlock

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.PurePointBudget
open PEqualNP.Outside.L_meta_2583.AndClauseAtoms
open PEqualNP.Outside.L_meta_2583.SemanticLinearTag
open PEqualNP.Outside.L_meta_2583.AndCorePrime
open MixedEdge

lemma thin_five_linear_core_cost {r n t B : ℕ}
    (I : Fin r → Fin r → Prop)
    (F : Fin B → Finset (Finset (Bool × Fin r)))
    (hthin : ∀ b, Thin (F b)) (hsafe : ∀ b, Safe I (F b))
    (hIfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin B → Fin 3 → Fin r)
    (hp : ∀ b, Function.Injective (p b)) (hl : ∀ b, Function.Injective (l b))
    (hacc : ∀ b i, Accept (F b) (p b i) (l b i)) (hcard : ∀ b, (F b).card = 5)
    (e : (Bool × Fin r) ≃ Fin n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hcross : ∀ a b, G.Adj (e (false, a)) (e (true, b)) → I a b)
    (hline : ∀ a b, ¬ G.Adj (e (true, a)) (e (true, b)))
    (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack n C)
    (blockOutput : Fin B → ℕ) (core : Fin B → Finset ℕ)
    (hcore : ∀ b, LinearAndCore n C (core b))
    (hout : ∀ b, blockOutput b ∈ core b)
    (hcnf : ∀ b, ∀ x : Fin n → Bool,
      val C (List.ofFn x) (blockOutput b) = true ↔ CnfLogic.Holds (F b) (fun u => x (e u)))
    (centers : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (hcover : ∀ u v, G.Adj u v →
      (∃ c ∈ centers, ∃ w ∈ L c, (u = c ∧ v = w) ∨ (u = w ∧ v = c)) ∨
      (∃ b i, (u = e (false, p b i) ∧ v = e (true, l b i)) ∨
        (u = e (true, l b i) ∧ v = e (false, p b i))))
    (hcenters : centers.card ≤ t)
    (sources : {c : Fin n // c ∈ centers} → Finset ℕ)
    (hvalid : ∀ c, ∀ w ∈ sources c, w < n + C.gates.length)
    (hpos : ∀ c, ∀ v ∈ L c.val, ∃ w ∈ sources c,
      val C (List.ofFn (pairInput v v)) w = true)
    (hfalse : ∀ c, ∀ w ∈ sources c,
      val C (List.ofFn (complementInput (G.neighborFinset c.val))) w = false)
    (hsources : (∑ c : {c : Fin n // c ∈ centers}, (sources c).card) ≤ t)
    (a : Fin t → Fin C.gates.length) (ha : Function.Injective a)
    (haop : ∀ i, (gateAt C (a i).val).op = GateOp.and)
    (starCenter : Fin t → Fin n) (starLeaf : Fin t → ℕ)
    (starSet : Fin t → Finset (Fin n))
    (hinputs : ∀ i, ∀ w ∈ (gateAt C (a i).val).inputs,
      w = (starCenter i).val ∨ w = starLeaf i)
    (hleaf : ∀ i, ∀ x : Fin n → Bool,
      val C (List.ofFn x) (starLeaf i) = decide (∃ p ∈ starSet i, x p = true))
    (z : Fin (t + B - 1) → Fin C.gates.length) (hz : Function.Injective z)
    (hzop : ∀ i, (gateAt C (z i).val).op = GateOp.or)
    (hzsmall : ∀ i, (singletonSupport n C (n + (z i).val)).card ≤ 1)
    (hne : 1 ≤ t + B) :
    ∃ T : Finset (Fin n), Cnf.Covers G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  let encode := supportEncoding n
  let tag := semanticTag n C encode
  have hcert : ∀ b,
      ((F b).image (fun W => W.image e)).image encode ⊆
        clauseAtoms n C tag (blockOutput b) ∧
      ∀ W ∈ (F b).image (fun W => W.image e), ∃ w < n + C.gates.length,
        ∀ x : Fin n → Bool,
          val C (List.ofFn x) w = decide (∃ i ∈ W, x i = true) := by
    intro b
    apply linear_core_cnf_certificate rb encode encode.injective (core b)
      (hcore b) (hout b) ((F b).image (fun W => W.image e))
    · apply CnfLogic.clause_card_image (F b) e e.injective 2
      intro W hW
      have hsize := clause_card_of_matching_three (F b) (p b) (l b) (hp b) (hl b) (hacc b) W hW
      omega
    · exact CnfLogic.antichain_image (F b) e e.injective
        (five_clause_antichain I (F b) (hthin b) (hsafe b) hIfour
          (p b) (l b) (hp b) (hl b) (hacc b) (hcard b))
    · intro x
      exact (hcnf b x).trans (CnfLogic.holds_image (F b) e x).symm
  have hwires : ∀ b W, W ∈ F b → ∃ w, w < n + C.gates.length ∧
      ∀ x : Fin n → Bool,
        val C (List.ofFn x) w = decide (∃ u ∈ W, x (e u) = true) := by
    intro b W hW
    obtain ⟨w, hw, hcomp⟩ := (hcert b).2 (W.image e) (mem_image.2 ⟨W, hW, rfl⟩)
    refine ⟨w, hw, ?_⟩
    intro x
    rw [hcomp x]
    exact Bool.decide_congr (CnfLogic.clause_image W e x)
  have houtputs : ∀ b, ∃ w, w < n + C.gates.length ∧
      (blockAtoms F b).image (familyClauseEncoding F e encode) ⊆ clauseAtoms n C tag w := by
    intro b
    refine ⟨blockOutput b, (hcore b).1 _ (hout b), ?_⟩
    rw [blockAtoms_familyClauseEncoding F e encode b]
    simpa only [image_image, Function.comp_def] using (hcert b).1
  have hasmall : ∀ i, (clauseAtoms n C tag (n + (a i).val)).card ≤ 1 := by
    intro i
    exact semantic_star_and_small_of_inputs rb encode (a i).isLt (haop i)
      (hinputs i) (starCenter i).isLt (starSet i) (hleaf i)
  exact thin_five_anchored_shared_and_cost I F hthin hsafe hIfour p l hp hl hacc hcard
    e G hfour hcross hline C hm rb hwires centers L hcover hcenters
    sources hvalid hpos hfalse hsources (familyClauseEncoding F e encode)
    (familyClauseEncoding_injective F e encode encode.injective) tag houtputs
    a ha haop hasmall z hz hzop hzsmall hne

end ThinBlock

namespace ConcreteStarSources

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.H8Projected.PurePointBudget

def centers {n t : ℕ} (center : Fin t → Fin n) : Finset (Fin n) := univ.image center

def leavesAt {n t : ℕ} (center : Fin t → Fin n) (leaves : Fin t → Finset (Fin n))
    (c : Fin n) : Finset (Fin n) := (univ.filter fun i => center i = c).biUnion leaves

def sourcesAt {n t : ℕ} (center : Fin t → Fin n) (source : Fin t → ℕ)
    (c : Fin n) : Finset ℕ := (univ.filter fun i => center i = c).image source

lemma centers_card_le {n t : ℕ} (center : Fin t → Fin n) : (centers center).card ≤ t := by
  simpa [centers] using (card_image_le : (univ.image center).card ≤ univ.card)

lemma grouped_source_count {n t : ℕ} (center : Fin t → Fin n) (source : Fin t → ℕ) :
    (∑ c : {c // c ∈ centers center}, (sourcesAt center source c.val).card) ≤ t := by
  classical
  let S := (univ : Finset {c // c ∈ centers center}).sigma fun c => sourcesAt center source c.val
  have h : S.card ≤ (univ : Finset (Fin t)).card := by
    apply union_card_le_relation (fun cw i => center i = cw.1.val ∧ source i = cw.2)
    · intro cw hcw
      have hw := (mem_sigma.1 hcw).2
      obtain ⟨i, hi, hiw⟩ := mem_image.1 hw
      exact ⟨i, mem_univ _, (mem_filter.1 hi).2, hiw⟩
    · intro i _ cw hcw cw' hcw'
      rcases cw with ⟨c, w⟩
      rcases cw' with ⟨c', w'⟩
      have hc : c = c' := Subtype.ext (hcw.2.1.symm.trans hcw'.2.1)
      have hw : w = w' := hcw.2.2.symm.trans hcw'.2.2
      subst c'
      subst w'
      rfl
  simpa only [S, card_sigma, card_univ, Fintype.card_fin] using h

lemma grouped_sources_valid {n t : ℕ} {C : Circuit}
    (center : Fin t → Fin n) (source : Fin t → ℕ)
    (hvalid : ∀ i, source i < n + C.gates.length) :
    ∀ c : {c // c ∈ centers center}, ∀ w ∈ sourcesAt center source c.val,
      w < n + C.gates.length := by
  intro c w hw
  obtain ⟨i, _, rfl⟩ := mem_image.1 hw
  exact hvalid i

lemma grouped_sources_positive {n t : ℕ} {C : Circuit}
    (center : Fin t → Fin n) (leaves : Fin t → Finset (Fin n)) (source : Fin t → ℕ)
    (hcomp : ∀ i, ∀ x : Fin n → Bool,
      val C (List.ofFn x) (source i) = decide (∃ p ∈ leaves i, x p = true)) :
    ∀ c : {c // c ∈ centers center}, ∀ p ∈ leavesAt center leaves c.val,
      ∃ w ∈ sourcesAt center source c.val, val C (List.ofFn (pairInput p p)) w = true := by
  intro c p hp
  obtain ⟨i, hi, hpi⟩ := mem_biUnion.1 hp
  refine ⟨source i, mem_image.2 ⟨i, hi, rfl⟩, ?_⟩
  rw [hcomp i]
  exact decide_eq_true ⟨p, hpi, by simp [pairInput]⟩

lemma grouped_sources_false {n t : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (center : Fin t → Fin n) (leaves : Fin t → Finset (Fin n)) (source : Fin t → ℕ)
    (hcomp : ∀ i, ∀ x : Fin n → Bool,
      val C (List.ofFn x) (source i) = decide (∃ p ∈ leaves i, x p = true))
    (hadj : ∀ i, ∀ p ∈ leaves i, G.Adj (center i) p) :
    ∀ c : {c // c ∈ centers center}, ∀ w ∈ sourcesAt center source c.val,
      val C (List.ofFn (complementInput (G.neighborFinset c.val))) w = false := by
  intro c w hw
  obtain ⟨i, hi, rfl⟩ := mem_image.1 hw
  have hcenter := (mem_filter.1 hi).2
  rw [hcomp i]
  apply Bool.decide_false
  rintro ⟨p, hp, ht⟩
  have hpn : p ∈ G.neighborFinset c.val := by simpa [hcenter] using hadj i p hp
  simp [complementInput, hpn] at ht

lemma group_star_edge {n t : ℕ} (center : Fin t → Fin n)
    (leaves : Fin t → Finset (Fin n)) (i : Fin t) {p : Fin n} (hp : p ∈ leaves i) :
    center i ∈ centers center ∧ p ∈ leavesAt center leaves (center i) := by
  exact ⟨mem_image.2 ⟨i, mem_univ _, rfl⟩,
    mem_biUnion.2 ⟨i, mem_filter.2 ⟨mem_univ _, rfl⟩, hp⟩⟩

lemma safe_star_leaves_adj {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n))
    (rb : ReadsBack n C) {j leaf : ℕ} (center : Fin n)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hinputs : ∀ w ∈ (gateAt C j).inputs, w = center.val ∨ w = leaf)
    (leaves : Finset (Fin n))
    (hcomp : ∀ x : Fin n → Bool,
      val C (List.ofFn x) leaf = decide (∃ p ∈ leaves, x p = true))
    (hsafe : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + j) = true →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∀ p ∈ leaves, G.Adj center p := by
  intro p hp
  have hout : val C (List.ofFn (pairInput center p)) (n + j) = true := by
    apply (val_and (by simp) hj hop).2
    intro w hw
    refine ⟨rb j hj w hw, ?_⟩
    rcases hinputs w hw with rfl | rfl
    · rw [val_ofFn]
      simp [pairInput]
    · rw [hcomp]
      exact decide_eq_true ⟨p, hp, by simp [pairInput]⟩
  obtain ⟨u, v, huv, hu, hv⟩ := hsafe _ hout
  have hu' : u = center ∨ u = p := by simpa [pairInput] using hu
  have hv' : v = center ∨ v = p := by simpa [pairInput] using hv
  rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
  · simp at huv
  · exact huv
  · exact huv.symm
  · simp at huv

end ConcreteStarSources

namespace ThinBlock

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.AndCorePrime
open PEqualNP.Outside.L_meta_2583.ConcreteStarSources

lemma thin_five_concrete_stars_cost {r n t B : ℕ}
    (I : Fin r → Fin r → Prop)
    (F : Fin B → Finset (Finset (Bool × Fin r)))
    (hthin : ∀ b, Thin (F b)) (hsafe : ∀ b, Safe I (F b))
    (hIfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin B → Fin 3 → Fin r)
    (hp : ∀ b, Function.Injective (p b)) (hl : ∀ b, Function.Injective (l b))
    (hacc : ∀ b i, Accept (F b) (p b i) (l b i)) (hcard : ∀ b, (F b).card = 5)
    (e : (Bool × Fin r) ≃ Fin n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hcross : ∀ a b, G.Adj (e (false, a)) (e (true, b)) → I a b)
    (hline : ∀ a b, ¬ G.Adj (e (true, a)) (e (true, b)))
    (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack n C)
    (blockOutput : Fin B → ℕ) (core : Fin B → Finset ℕ)
    (hcore : ∀ b, LinearAndCore n C (core b)) (hout : ∀ b, blockOutput b ∈ core b)
    (hcnf : ∀ b, ∀ x : Fin n → Bool,
      val C (List.ofFn x) (blockOutput b) = true ↔ CnfLogic.Holds (F b) (fun u => x (e u)))
    (a : Fin t → Fin C.gates.length) (ha : Function.Injective a)
    (haop : ∀ i, (gateAt C (a i).val).op = GateOp.and)
    (starCenter : Fin t → Fin n) (starLeaf : Fin t → ℕ)
    (starSet : Fin t → Finset (Fin n))
    (hinputs : ∀ i, ∀ w ∈ (gateAt C (a i).val).inputs,
      w = (starCenter i).val ∨ w = starLeaf i)
    (hleaf : ∀ i, ∀ x : Fin n → Bool,
      val C (List.ofFn x) (starLeaf i) = decide (∃ p ∈ starSet i, x p = true))
    (hleafvalid : ∀ i, starLeaf i < n + C.gates.length)
    (hstarsafe : ∀ i, ∀ x : Fin n → Bool,
      val C (List.ofFn x) (n + (a i).val) = true →
        ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (hcover : ∀ u v, G.Adj u v →
      (∃ i, ∃ q ∈ starSet i,
        (u = starCenter i ∧ v = q) ∨ (u = q ∧ v = starCenter i)) ∨
      (∃ b i, (u = e (false, p b i) ∧ v = e (true, l b i)) ∨
        (u = e (true, l b i) ∧ v = e (false, p b i))))
    (z : Fin (t + B - 1) → Fin C.gates.length) (hz : Function.Injective z)
    (hzop : ∀ i, (gateAt C (z i).val).op = GateOp.or)
    (hzsmall : ∀ i, (singletonSupport n C (n + (z i).val)).card ≤ 1)
    (hne : 1 ≤ t + B) :
    ∃ T : Finset (Fin n), Cnf.Covers G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  have hadj : ∀ i, ∀ q ∈ starSet i, G.Adj (starCenter i) q := by
    intro i
    exact safe_star_leaves_adj G rb (starCenter i) (a i).isLt (haop i)
      (hinputs i) (starSet i) (hleaf i) (hstarsafe i)
  have hgroupcover : ∀ u v, G.Adj u v →
      (∃ c ∈ centers starCenter, ∃ q ∈ leavesAt starCenter starSet c,
        (u = c ∧ v = q) ∨ (u = q ∧ v = c)) ∨
      (∃ b i, (u = e (false, p b i) ∧ v = e (true, l b i)) ∨
        (u = e (true, l b i) ∧ v = e (false, p b i))) := by
    intro u v huv
    rcases hcover u v huv with hstar | hblock
    · obtain ⟨i, q, hq, horient⟩ := hstar
      have hc := group_star_edge starCenter starSet i hq
      exact Or.inl ⟨starCenter i, hc.1, q, hc.2, horient⟩
    · exact Or.inr hblock
  exact thin_five_linear_core_cost I F hthin hsafe hIfour p l hp hl hacc hcard
    e G hfour hcross hline C hm rb blockOutput core hcore hout hcnf
    (centers starCenter) (leavesAt starCenter starSet) hgroupcover (centers_card_le starCenter)
    (fun c => sourcesAt starCenter starLeaf c.val)
    (grouped_sources_valid starCenter starLeaf hleafvalid)
    (grouped_sources_positive starCenter starSet starLeaf hleaf)
    (grouped_sources_false G starCenter starSet starLeaf hleaf hadj)
    (grouped_source_count starCenter starLeaf)
    a ha haop starCenter starLeaf starSet hinputs hleaf z hz hzop hzsmall hne

end ThinBlock

namespace ThinBlock

open Finset PEqualNP.EdgeOwnership

lemma safe_pair_acceptance {r n : ℕ}
    (I : Fin r → Fin r → Prop) (F : Finset (Finset (Bool × Fin r)))
    (hsafe : Safe I F) (e : Bool × Fin r → Fin n) (he : Function.Injective e)
    (u v : Fin n)
    (hF : CnfLogic.Holds F (fun z => pairInput u v (e z))) :
    ∃ a b, Accept F a b ∧
      ((u = e (false, a) ∧ v = e (true, b)) ∨
       (v = e (false, a) ∧ u = e (true, b))) := by
  obtain ⟨a, b, _, ha, hb⟩ := hsafe _ hF
  have ha' : e (false, a) = u ∨ e (false, a) = v := by
    simpa [pairInput] using ha
  have hb' : e (true, b) = u ∨ e (true, b) = v := by
    simpa [pairInput] using hb
  have hne : e (false, a) ≠ e (true, b) := by
    intro h
    have hbool := congrArg Prod.fst (he h)
    cases hbool
  have horder : (u = e (false, a) ∧ v = e (true, b)) ∨
      (v = e (false, a) ∧ u = e (true, b)) := by
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
    · exact (hne (ha'.trans hb'.symm)).elim
    · exact Or.inl ⟨ha'.symm, hb'.symm⟩
    · exact Or.inr ⟨ha'.symm, hb'.symm⟩
    · exact (hne (ha'.trans hb'.symm)).elim
  refine ⟨a, b, ?_, horder⟩
  intro W hW
  obtain ⟨z, hz, hx⟩ := hF W hW
  have hzu : e z = u ∨ e z = v := by simpa [pairInput] using hx
  have hzab : e z = e (false, a) ∨ e z = e (true, b) := by
    rcases horder with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · simpa only [hu, hv] using hzu
    · simpa only [hu, hv, or_comm] using hzu
  rcases hzab with hp | hl
  · exact Or.inl (he hp ▸ hz)
  · exact Or.inr (he hl ▸ hz)

lemma matching_three_pair_iff {r n : ℕ}
    (I : Fin r → Fin r → Prop) (F : Finset (Finset (Bool × Fin r)))
    (hthin : Thin F) (hsafe : Safe I F)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin r) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i))
    (e : Bool × Fin r → Fin n) (he : Function.Injective e) (u v : Fin n) :
    CnfLogic.Holds F (fun z => pairInput u v (e z)) ↔
      ∃ i, (u = e (false, p i) ∧ v = e (true, l i)) ∨
        (v = e (false, p i) ∧ u = e (true, l i)) := by
  constructor
  · intro hF
    obtain ⟨a, b, hab, horder⟩ := safe_pair_acceptance I F hsafe e he u v hF
    obtain ⟨i, ha, hb⟩ := (matching_three_classification I F hthin hsafe hfour
      p l hp hl hacc a b).mp hab
    exact ⟨i, by simpa only [ha, hb] using horder⟩
  · rintro ⟨i, horder⟩ W hW
    rcases hacc i W hW with hpW | hlW
    · refine ⟨(false, p i), hpW, ?_⟩
      rcases horder with ⟨hu, _⟩ | ⟨hv, _⟩
      · simp [pairInput, hu]
      · simp [pairInput, hv]
    · refine ⟨(true, l i), hlW, ?_⟩
      rcases horder with ⟨_, hv⟩ | ⟨_, hu⟩
      · simp [pairInput, hv]
      · simp [pairInput, hu]

lemma mapped_matching_three_pair_iff {r n : ℕ}
    (I : Fin r → Fin r → Prop) (F : Finset (Finset (Bool × Fin r)))
    (hthin : Thin F) (hsafe : Safe I F)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin r) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i))
    (e : Bool × Fin r → Fin n) (he : Function.Injective e) (u v : Fin n) :
    CnfLogic.Holds (F.image (fun W => W.image e)) (pairInput u v) ↔
      ∃ i, (u = e (false, p i) ∧ v = e (true, l i)) ∨
        (v = e (false, p i) ∧ u = e (true, l i)) := by
  rw [CnfLogic.holds_image]
  exact matching_three_pair_iff I F hthin hsafe hfour p l hp hl hacc e he u v

lemma matching_three_output_pair_iff {r n : ℕ}
    (I : Fin r → Fin r → Prop) (F : Finset (Finset (Bool × Fin r)))
    (hthin : Thin F) (hsafe : Safe I F)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin r) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i))
    (e : Bool × Fin r → Fin n) (he : Function.Injective e)
    (f : (Fin n → Bool) → Bool)
    (hcnf : ∀ x, f x = true ↔ CnfLogic.Holds F (fun z => x (e z)))
    (u v : Fin n) :
    f (pairInput u v) = true ↔
      ∃ i, (u = e (false, p i) ∧ v = e (true, l i)) ∨
        (v = e (false, p i) ∧ u = e (true, l i)) := by
  rw [hcnf]
  exact matching_three_pair_iff I F hthin hsafe hfour p l hp hl hacc e he u v

lemma matching_three_wire_pair_iff {r n : ℕ}
    (I : Fin r → Fin r → Prop) (F : Finset (Finset (Bool × Fin r)))
    (hthin : Thin F) (hsafe : Safe I F)
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin 3 → Fin r) (hp : Function.Injective p) (hl : Function.Injective l)
    (hacc : ∀ i, Accept F (p i) (l i))
    (e : Bool × Fin r → Fin n) (he : Function.Injective e)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ)
    (hcnf : ∀ x, (C.wires (List.ofFn x)).getD w false = true ↔
      CnfLogic.Holds F (fun z => x (e z))) (u v : Fin n) :
    (C.wires (List.ofFn (pairInput u v))).getD w false = true ↔
      ∃ i, (u = e (false, p i) ∧ v = e (true, l i)) ∨
        (v = e (false, p i) ∧ u = e (true, l i)) := by
  exact matching_three_output_pair_iff I F hthin hsafe hfour p l hp hl hacc e he
    (fun x => (C.wires (List.ofFn x)).getD w false) hcnf u v

end ThinBlock

namespace OrFrontier

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair

def OrStep (n : ℕ) (C : Circuit) (child parent : ℕ) : Prop :=
  ∃ j, j < C.gates.length ∧ parent = n + j ∧
    (gateAt C j).op = GateOp.or ∧ child ∈ (gateAt C j).inputs

def OrAncestor (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (OrStep n C)

lemma ancestor_le {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    {w root : ℕ} (h : OrAncestor n C w root) : w ≤ root := by
  induction h with
  | refl => exact le_rfl
  | tail hpath hstep ih =>
    obtain ⟨j, hj, rfl, hop, hi⟩ := hstep
    exact ih.trans (Nat.le_of_lt (rb j hj _ hi))

lemma ancestor_val {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    {w root : ℕ} (h : OrAncestor n C w root) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) w = true) : val C (List.ofFn x) root = true := by
  induction h with
  | refl => exact hv
  | tail hpath hstep ih =>
    obtain ⟨j, hj, rfl, hop, hi⟩ := hstep
    exact (val_or (by simp) hj hop).2 ⟨_, hi, rb j hj _ hi, ih⟩

lemma ancestor_support_empty {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    {w root : ℕ} (h : OrAncestor n C w root)
    (hzero : singletonSupport n C root = ∅) : singletonSupport n C w = ∅ := by
  ext i
  constructor
  · intro hi
    have hroot := ancestor_val rb h (pairInput i i) (mem_support.mp hi)
    have hm : i ∈ singletonSupport n C root := mem_support.mpr hroot
    simpa only [hzero] using hm
  · intro hi
    simp at hi

lemma ancestor_not_input {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    {w root : ℕ} (h : OrAncestor n C w root)
    (hzero : singletonSupport n C root = ∅) : ¬ w < n := by
  intro hw
  let i : Fin n := ⟨w, hw⟩
  have hsupport := ancestor_support_empty rb h hzero
  have hi : i ∈ singletonSupport n C w := by
    apply mem_support.mpr
    change val C (List.ofFn (pairInput i i)) i.val = true
    rw [val_ofFn]
    simp [pairInput]
  rw [hsupport] at hi
  simp at hi

noncomputable def andFrontier (n : ℕ) (C : Circuit) (root : ℕ) :
    Finset (Fin C.gates.length) := by
  classical
  exact univ.filter fun j =>
    (gateAt C j.val).op = GateOp.and ∧ OrAncestor n C (n + j.val) root

lemma mem_andFrontier {n : ℕ} {C : Circuit} {root : ℕ} {j : Fin C.gates.length} :
    j ∈ andFrontier n C root ↔
      (gateAt C j.val).op = GateOp.and ∧ OrAncestor n C (n + j.val) root := by
  classical
  simp [andFrontier]

lemma frontier_val_iff {n : ℕ} {C : Circuit}
    (rb : ReadsBack n C) (hm : Monotone2 C) {root : ℕ}
    (hroot : root < n + C.gates.length) (hzero : singletonSupport n C root = ∅)
    (x : Fin n → Bool) :
    val C (List.ofFn x) root = true ↔
      ∃ j ∈ andFrontier n C root, val C (List.ofFn x) (n + j.val) = true := by
  constructor
  · have hfind : ∀ w, w < n + C.gates.length → OrAncestor n C w root →
        val C (List.ofFn x) w = true →
        ∃ j ∈ andFrontier n C root, val C (List.ofFn x) (n + j.val) = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hvalid hpath hv
        have hge : n ≤ w := Nat.le_of_not_gt (ancestor_not_input rb hpath hzero)
        have hj : w - n < C.gates.length := by omega
        have heq : n + (w - n) = w := Nat.add_sub_of_le hge
        rcases gate_op hm hj with hand | hor
        · refine ⟨⟨w - n, hj⟩, mem_andFrontier.mpr ⟨hand, ?_⟩, ?_⟩
          · simpa only [heq] using hpath
          · simpa only [heq] using hv
        · have hv' : val C (List.ofFn x) (n + (w - n)) = true := by
            simpa only [heq] using hv
          obtain ⟨i, hi, hilt, hiv⟩ := (val_or (by simp) hj hor).1 hv'
          have hiless : i < w := by simpa only [heq] using hilt
          have histep : OrStep n C i w := ⟨w - n, hj, heq.symm, hor, hi⟩
          exact ih i hiless (lt_trans hiless hvalid) (hpath.head histep) hiv
    exact hfind root hroot Relation.ReflTransGen.refl
  · rintro ⟨j, hj, hv⟩
    exact ancestor_val rb (mem_andFrontier.mp hj).2 x hv

end OrFrontier

namespace OrFrontier

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair

noncomputable def frontierAtoms (n : ℕ) (C : Circuit) (root w : ℕ) :
    Finset (Fin C.gates.length) := by
  classical
  exact if OrAncestor n C w root then
    if w < n then ∅ else
      if hj : w - n < C.gates.length then
        if (gateAt C (w - n)).op = GateOp.and then {⟨w - n, hj⟩} else
          if (gateAt C (w - n)).op = GateOp.or then
            (gateAt C (w - n)).inputs.toFinset.biUnion fun i =>
              if hi : i < w then frontierAtoms n C root i else ∅
          else ∅
      else ∅
    else ∅
termination_by w

lemma frontierAtoms_input {n : ℕ} (C : Circuit) (root : ℕ) {w : ℕ} (hw : w < n) :
    frontierAtoms n C root w = ∅ := by
  classical
  rw [frontierAtoms]
  split_ifs <;> simp_all

lemma frontierAtoms_unreachable {n : ℕ} (C : Circuit) (root w : ℕ)
    (h : ¬ OrAncestor n C w root) : frontierAtoms n C root w = ∅ := by
  rw [frontierAtoms]
  simp [h]

lemma frontierAtoms_and {n : ℕ} {C : Circuit} {root j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hr : OrAncestor n C (n + j) root) :
    frontierAtoms n C root (n + j) = {⟨j, hj⟩} := by
  rw [frontierAtoms]
  have hn : ¬ n + j < n := by omega
  simp [hr, hn, hj, hop]

lemma frontierAtoms_or {n : ℕ} {C : Circuit} (rb : ReadsBack n C) {root j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hr : OrAncestor n C (n + j) root) :
    frontierAtoms n C root (n + j) =
      (gateAt C j).inputs.toFinset.biUnion (frontierAtoms n C root) := by
  rw [frontierAtoms]
  have hn : ¬ n + j < n := by omega
  simp only [hr, ite_true, hn, ite_false, Nat.add_sub_cancel_left, hj, dite_true, hop]
  simp only [Nat.add_sub_cancel_left, hop, reduceCtorEq, ite_false]
  apply Finset.biUnion_congr rfl
  intro i hi
  exact dite_eq_left (rb j hj i (List.mem_toFinset.mp hi))

lemma frontierAtoms_step_subset {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    {root child parent : ℕ} (hstep : OrStep n C child parent)
    (hr : OrAncestor n C parent root) :
    frontierAtoms n C root child ⊆ frontierAtoms n C root parent := by
  obtain ⟨j, hj, rfl, hop, hi⟩ := hstep
  rw [frontierAtoms_or rb hj hop hr]
  intro a ha
  exact mem_biUnion.mpr ⟨child, List.mem_toFinset.mpr hi, ha⟩

lemma frontierAtoms_mono {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    {root child parent : ℕ} (hpath : OrAncestor n C child parent) :
    OrAncestor n C parent root →
      frontierAtoms n C root child ⊆ frontierAtoms n C root parent := by
  induction hpath with
  | refl => intro hr; exact Subset.rfl
  | tail hpath hstep ih =>
    intro hr
    exact (ih (hr.head hstep)).trans (frontierAtoms_step_subset rb hstep hr)

lemma andFrontier_subset_atoms {n : ℕ} {C : Circuit} (rb : ReadsBack n C) (root : ℕ) :
    andFrontier n C root ⊆ frontierAtoms n C root root := by
  intro j hj
  obtain ⟨hop, hr⟩ := mem_andFrontier.mp hj
  have hself : j ∈ frontierAtoms n C root (n + j.val) := by
    rw [frontierAtoms_and j.isLt hop hr]
    simp
  exact frontierAtoms_mono rb hr Relation.ReflTransGen.refl hself

lemma frontierAtoms_large_gate {n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C) (root : ℕ) {j : ℕ}
    (hj : j < C.gates.length)
    (hlarge : 2 ≤ (frontierAtoms n C root (n + j)).card) :
    OrAncestor n C (n + j) root ∧ (gateAt C j).op = GateOp.or ∧
      ∃ x y, x < n + j ∧ y < n + j ∧
        frontierAtoms n C root (n + j) =
          frontierAtoms n C root x ∪ frontierAtoms n C root y := by
  classical
  have hr : OrAncestor n C (n + j) root := by
    by_contra hnot
    rw [frontierAtoms_unreachable C root (n + j) hnot] at hlarge
    simp at hlarge
  have hop : (gateAt C j).op = GateOp.or := by
    rcases gate_op hm hj with hand | hor
    · rw [frontierAtoms_and hj hand hr] at hlarge
      simp at hlarge
    · exact hor
  refine ⟨hr, hop, ?_⟩
  have hs := frontierAtoms_or rb hj hop hr
  have hlen := (hm _ (gateAt_mem hj)).2
  cases he : (gateAt C j).inputs with
  | nil =>
    rw [he] at hs
    simp at hs
    rw [hs] at hlarge
    simp at hlarge
  | cons x tail =>
    have hx : x < n + j := rb j hj x (by simp [he])
    cases tail with
    | nil =>
      refine ⟨x, x, hx, hx, ?_⟩
      simpa [he] using hs
    | cons y tail =>
      have hy : y < n + j := rb j hj y (by simp [he])
      cases tail with
      | nil =>
        refine ⟨x, y, hx, hy, ?_⟩
        simpa [he] using hs
      | cons z rest => simp [he] at hlen

noncomputable def smallOrAncestors (n : ℕ) (C : Circuit) (root : ℕ) : Finset ℕ := by
  classical
  exact (range C.gates.length).filter fun j =>
    (gateAt C j).op = GateOp.or ∧ OrAncestor n C (n + j) root ∧
      singletonSupport n C (n + j) = ∅

lemma frontier_card_le_small_or_add_one {n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C) {root : ℕ}
    (hroot : root < n + C.gates.length) (hzero : singletonSupport n C root = ∅) :
    (andFrontier n C root).card ≤ (smallOrAncestors n C root).card + 1 := by
  classical
  let T := frontierAtoms n C root
  have hcount := union_network_one_target (n := n) (m := C.gates.length) T (T root)
    (fun w hw => by simp [T, frontierAtoms_input C root hw])
    (fun j hj hlarge => (frontierAtoms_large_gate hm rb root hj hlarge).2.2)
    ⟨root, hroot, rfl⟩
  have hsub : ((range C.gates.length).filter fun j =>
      2 ≤ (T (n + j)).card ∧ T (n + j) ⊆ T root) ⊆ smallOrAncestors n C root := by
    intro j hj
    obtain ⟨hj, hlarge, htarget⟩ := mem_filter.mp hj
    have hj' := mem_range.mp hj
    obtain ⟨hr, hop, hsplit⟩ := frontierAtoms_large_gate hm rb root hj' hlarge
    exact mem_filter.mpr ⟨hj, hop, hr, ancestor_support_empty rb hr hzero⟩
  have hle := card_le_card hsub
  have hfront := card_le_card (andFrontier_subset_atoms rb root)
  change (andFrontier n C root).card ≤ (smallOrAncestors n C root).card + 1
  dsimp only [T] at hcount hle
  omega

end OrFrontier

namespace OrFrontier

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair

lemma safe_output_support_empty {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (root : ℕ)
    (hsafe : ∀ x : Fin n → Bool, val C (List.ofFn x) root = true →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    singletonSupport n C root = ∅ := by
  ext i
  constructor
  · intro hi
    obtain ⟨u, v, huv, hu, hv⟩ := hsafe (pairInput i i) (mem_support.mp hi)
    have hui : u = i := by simpa [pairInput] using hu
    have hvi : v = i := by simpa [pairInput] using hv
    subst u
    subst v
    exact False.elim (G.irrefl huv)
  · intro hi
    simp at hi

lemma select_small_or_gates {n k : ℕ} (C : Circuit) (root : ℕ)
    (hk : k ≤ (smallOrAncestors n C root).card) :
    ∃ z : Fin k → Fin C.gates.length, Function.Injective z ∧
      ∀ i, (z i).val ∈ smallOrAncestors n C root := by
  classical
  let S := smallOrAncestors n C root
  let b : Fin k → S := fun i => S.equivFin.symm ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
  let z : Fin k → Fin C.gates.length := fun i =>
    ⟨(b i).val, mem_range.mp (mem_filter.mp (b i).property).1⟩
  refine ⟨z, ?_, ?_⟩
  · intro i j hij
    have hb : b i = b j := Subtype.ext (congrArg Fin.val hij)
    have hi := congrArg (fun u : S => (S.equivFin u).val) hb
    apply Fin.ext
    simpa [b] using hi
  · intro i
    exact (b i).property

lemma frontier_aggregation_map {n k : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C) {root : ℕ}
    (hroot : root < n + C.gates.length) (hzero : singletonSupport n C root = ∅)
    (hk : k ≤ (andFrontier n C root).card - 1) :
    ∃ z : Fin k → Fin C.gates.length, Function.Injective z ∧
      (∀ i, (gateAt C (z i).val).op = GateOp.or) ∧
      (∀ i, (singletonSupport n C (n + (z i).val)).card ≤ 1) := by
  classical
  have hc := frontier_card_le_small_or_add_one hm rb hroot hzero
  have hk' : k ≤ (smallOrAncestors n C root).card := by omega
  obtain ⟨z, hz, hmem⟩ := select_small_or_gates C root hk'
  refine ⟨z, hz, ?_, ?_⟩
  · intro i
    exact (mem_filter.mp (hmem i)).2.1
  · intro i
    rw [(mem_filter.mp (hmem i)).2.2.2]
    simp

end OrFrontier

namespace ThinBlock

open Finset PEqualNP.EdgeOwnership

lemma star_pair_iff {n : ℕ} (c u v : Fin n) (L : Finset (Fin n)) (hc : c ∉ L) :
    (pairInput u v c = true ∧ ∃ w ∈ L, pairInput u v w = true) ↔
      (u = c ∧ v ∈ L) ∨ (v = c ∧ u ∈ L) := by
  constructor
  · rintro ⟨hcu, w, hw, hwu⟩
    have hcu' : c = u ∨ c = v := by simpa [pairInput] using hcu
    have hwu' : w = u ∨ w = v := by simpa [pairInput] using hwu
    rcases hcu' with hcu' | hcu' <;> rcases hwu' with hwu' | hwu'
    · exact (hc ((hwu'.trans hcu'.symm) ▸ hw)).elim
    · exact Or.inl ⟨hcu'.symm, hwu' ▸ hw⟩
    · exact Or.inr ⟨hcu'.symm, hwu' ▸ hw⟩
    · exact (hc ((hwu'.trans hcu'.symm) ▸ hw)).elim
  · rintro (⟨rfl, hv⟩ | ⟨rfl, hu⟩)
    · exact ⟨by simp [pairInput], v, hv, by simp [pairInput]⟩
    · exact ⟨by simp [pairInput], u, hu, by simp [pairInput]⟩

lemma frontier_star_matching_pair_cover {r n t B : ℕ}
    (I : Fin r → Fin r → Prop) (F : Fin B → Finset (Finset (Bool × Fin r)))
    (hthin : ∀ b, Thin (F b)) (hsafe : ∀ b, Safe I (F b))
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin B → Fin 3 → Fin r)
    (hp : ∀ b, Function.Injective (p b)) (hl : ∀ b, Function.Injective (l b))
    (hacc : ∀ b i, Accept (F b) (p b i) (l b i))
    (e : Bool × Fin r → Fin n) (he : Function.Injective e)
    (eval : ℕ → (Fin n → Bool) → Bool) (output : ℕ) (Q : Finset ℕ)
    (hfrontier : ∀ x, eval output x = true ↔ ∃ w ∈ Q, eval w x = true)
    (hzero : ∀ u, eval output (pairInput u u) = false)
    (starOutput : Fin t → ℕ) (blockOutput : Fin B → ℕ)
    (center : Fin t → Fin n) (leaves : Fin t → Finset (Fin n))
    (hboundary : ∀ w ∈ Q, (∃ a, w = starOutput a) ∨ (∃ b, w = blockOutput b))
    (hstar : ∀ a x, eval (starOutput a) x = true ↔
      x (center a) = true ∧ ∃ v ∈ leaves a, x v = true)
    (hblock : ∀ b x, eval (blockOutput b) x = true ↔
      CnfLogic.Holds (F b) (fun z => x (e z)))
    (u v : Fin n) (huv : eval output (pairInput u v) = true) :
    (∃ a, (u = center a ∧ v ∈ leaves a) ∨ (v = center a ∧ u ∈ leaves a)) ∨
      (∃ b i, (u = e (false, p b i) ∧ v = e (true, l b i)) ∨
        (v = e (false, p b i) ∧ u = e (true, l b i))) := by
  obtain ⟨w, hwQ, hw⟩ := (hfrontier _).mp huv
  rcases hboundary w hwQ with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · have hc : center a ∉ leaves a := by
      intro hc
      have hstarone : eval (starOutput a) (pairInput (center a) (center a)) = true := by
        apply (hstar a _).mpr
        exact ⟨by simp [pairInput], center a, hc, by simp [pairInput]⟩
      have houtone := (hfrontier _).mpr ⟨starOutput a, hwQ, hstarone⟩
      rw [hzero] at houtone
      cases houtone
    exact Or.inl ⟨a, (star_pair_iff (center a) u v (leaves a) hc).mp
      ((hstar a _).mp hw)⟩
  · exact Or.inr ⟨b, (matching_three_output_pair_iff I (F b) (hthin b) (hsafe b)
      hfour (p b) (l b) (hp b) (hl b) (hacc b) e he
      (eval (blockOutput b)) (hblock b) u v).mp hw⟩

lemma frontier_star_matching_graph_cover {r n t B : ℕ}
    (I : Fin r → Fin r → Prop) (F : Fin B → Finset (Finset (Bool × Fin r)))
    (hthin : ∀ b, Thin (F b)) (hsafe : ∀ b, Safe I (F b))
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin B → Fin 3 → Fin r)
    (hp : ∀ b, Function.Injective (p b)) (hl : ∀ b, Function.Injective (l b))
    (hacc : ∀ b i, Accept (F b) (p b i) (l b i))
    (e : Bool × Fin r → Fin n) (he : Function.Injective e)
    (eval : ℕ → (Fin n → Bool) → Bool) (output : ℕ) (Q : Finset ℕ)
    (hfrontier : ∀ x, eval output x = true ↔ ∃ w ∈ Q, eval w x = true)
    (hzero : ∀ u, eval output (pairInput u u) = false)
    (starOutput : Fin t → ℕ) (blockOutput : Fin B → ℕ)
    (center : Fin t → Fin n) (leaves : Fin t → Finset (Fin n))
    (hboundary : ∀ w ∈ Q, (∃ a, w = starOutput a) ∨ (∃ b, w = blockOutput b))
    (hstar : ∀ a x, eval (starOutput a) x = true ↔
      x (center a) = true ∧ ∃ v ∈ leaves a, x v = true)
    (hblock : ∀ b x, eval (blockOutput b) x = true ↔
      CnfLogic.Holds (F b) (fun z => x (e z)))
    (G : SimpleGraph (Fin n))
    (hedge : ∀ u v, G.Adj u v → eval output (pairInput u v) = true)
    (centers : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (hplacement : ∀ a, center a ∈ centers ∧ leaves a ⊆ L (center a)) :
    ∀ u v, G.Adj u v →
      (∃ c ∈ centers, ∃ w ∈ L c, (u = c ∧ v = w) ∨ (u = w ∧ v = c)) ∨
      (∃ b i, (u = e (false, p b i) ∧ v = e (true, l b i)) ∨
        (u = e (true, l b i) ∧ v = e (false, p b i))) := by
  intro u v huv
  have hcov := frontier_star_matching_pair_cover I F hthin hsafe hfour p l hp hl
    hacc e he eval output Q hfrontier hzero starOutput blockOutput center leaves
    hboundary hstar hblock u v (hedge u v huv)
  rcases hcov with ⟨a, ha⟩ | ⟨b, i, hi⟩
  · rcases ha with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · exact Or.inl ⟨center a, (hplacement a).1, v, (hplacement a).2 hv,
        Or.inl ⟨hu, rfl⟩⟩
    · exact Or.inl ⟨center a, (hplacement a).1, u, (hplacement a).2 hu,
        Or.inr ⟨rfl, hv⟩⟩
  · refine Or.inr ⟨b, i, ?_⟩
    exact hi.elim Or.inl (fun h => Or.inr ⟨h.2, h.1⟩)

lemma edge_output_zero_and_pairs {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (f : (Fin n → Bool) → Bool)
    (hcompute : ∀ x, f x = decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) :
    (∀ u, f (pairInput u u) = false) ∧
      (∀ u v, G.Adj u v → f (pairInput u v) = true) := by
  constructor
  · intro u
    rw [hcompute]
    apply decide_eq_false_iff_not.mpr
    rintro ⟨a, b, hab, ha, hb⟩
    have hau : a = u := by simpa [pairInput] using ha
    have hbu : b = u := by simpa [pairInput] using hb
    exact G.ne_of_adj hab (hau.trans hbu.symm)
  · intro u v huv
    rw [hcompute]
    apply decide_eq_true
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

lemma circuit_frontier_graph_cover {r n t B : ℕ}
    (I : Fin r → Fin r → Prop) (F : Fin B → Finset (Finset (Bool × Fin r)))
    (hthin : ∀ b, Thin (F b)) (hsafe : ∀ b, Safe I (F b))
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin B → Fin 3 → Fin r)
    (hp : ∀ b, Function.Injective (p b)) (hl : ∀ b, Function.Injective (l b))
    (hacc : ∀ b i, Accept (F b) (p b i) (l b i))
    (e : Bool × Fin r → Fin n) (he : Function.Injective e)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (output : ℕ)
    (Q : Finset (Fin C.gates.length))
    (hfrontier : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD output false = true ↔
      ∃ j ∈ Q, (C.wires (List.ofFn x)).getD (n + j.val) false = true)
    (starOutput : Fin t → ℕ) (blockOutput : Fin B → ℕ)
    (center : Fin t → Fin n) (leaves : Fin t → Finset (Fin n))
    (hboundary : ∀ j ∈ Q,
      (∃ a, n + j.val = starOutput a) ∨ (∃ b, n + j.val = blockOutput b))
    (hstar : ∀ a x, (C.wires (List.ofFn x)).getD (starOutput a) false = true ↔
      x (center a) = true ∧ ∃ v ∈ leaves a, x v = true)
    (hblock : ∀ b x, (C.wires (List.ofFn x)).getD (blockOutput b) false = true ↔
      CnfLogic.Holds (F b) (fun z => x (e z)))
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcompute : ∀ x, (C.wires (List.ofFn x)).getD output false =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true))
    (centers : Finset (Fin n)) (L : Fin n → Finset (Fin n))
    (hplacement : ∀ a, center a ∈ centers ∧ leaves a ⊆ L (center a)) :
    ∀ u v, G.Adj u v →
      (∃ c ∈ centers, ∃ w ∈ L c, (u = c ∧ v = w) ∨ (u = w ∧ v = c)) ∨
      (∃ b i, (u = e (false, p b i) ∧ v = e (true, l b i)) ∨
        (u = e (true, l b i) ∧ v = e (false, p b i))) := by
  let eval : ℕ → (Fin n → Bool) → Bool := fun w x =>
    (C.wires (List.ofFn x)).getD w false
  let W : Finset ℕ := Q.image (fun j => n + j.val)
  have hfrontier' : ∀ x, eval output x = true ↔ ∃ w ∈ W, eval w x = true := by
    intro x
    rw [hfrontier]
    constructor
    · rintro ⟨j, hj, hx⟩
      exact ⟨n + j.val, mem_image.mpr ⟨j, hj, rfl⟩, hx⟩
    · rintro ⟨w, hw, hx⟩
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hw
      exact ⟨j, hj, hx⟩
  have hboundary' : ∀ w ∈ W,
      (∃ a, w = starOutput a) ∨ (∃ b, w = blockOutput b) := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hw
    exact hboundary j hj
  obtain ⟨hzero, hedge⟩ := edge_output_zero_and_pairs G (eval output) hcompute
  exact frontier_star_matching_graph_cover I F hthin hsafe hfour p l hp hl hacc
    e he eval output W hfrontier' hzero starOutput blockOutput center leaves
    hboundary' hstar hblock G hedge centers L hplacement

lemma circuit_frontier_indexed_graph_cover {r n t B : ℕ}
    (I : Fin r → Fin r → Prop) (F : Fin B → Finset (Finset (Bool × Fin r)))
    (hthin : ∀ b, Thin (F b)) (hsafe : ∀ b, Safe I (F b))
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin B → Fin 3 → Fin r)
    (hp : ∀ b, Function.Injective (p b)) (hl : ∀ b, Function.Injective (l b))
    (hacc : ∀ b i, Accept (F b) (p b i) (l b i))
    (e : Bool × Fin r → Fin n) (he : Function.Injective e)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (output : ℕ)
    (Q : Finset (Fin C.gates.length))
    (hfrontier : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD output false = true ↔
      ∃ j ∈ Q, (C.wires (List.ofFn x)).getD (n + j.val) false = true)
    (starOutput : Fin t → ℕ) (blockOutput : Fin B → ℕ)
    (center : Fin t → Fin n) (leaves : Fin t → Finset (Fin n))
    (hboundary : ∀ j ∈ Q,
      (∃ a, n + j.val = starOutput a) ∨ (∃ b, n + j.val = blockOutput b))
    (hstar : ∀ a x, (C.wires (List.ofFn x)).getD (starOutput a) false = true ↔
      x (center a) = true ∧ ∃ v ∈ leaves a, x v = true)
    (hblock : ∀ b x, (C.wires (List.ofFn x)).getD (blockOutput b) false = true ↔
      CnfLogic.Holds (F b) (fun z => x (e z)))
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcompute : ∀ x, (C.wires (List.ofFn x)).getD output false =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true))
    : ∀ u v, G.Adj u v →
      (∃ a, ∃ w ∈ leaves a,
        (u = center a ∧ v = w) ∨ (u = w ∧ v = center a)) ∨
      (∃ b i, (u = e (false, p b i) ∧ v = e (true, l b i)) ∨
        (u = e (true, l b i) ∧ v = e (false, p b i))) := by
  classical
  let centers : Finset (Fin n) := univ.image center
  let L : Fin n → Finset (Fin n) := fun c =>
    univ.biUnion fun a => if center a = c then leaves a else ∅
  have hplacement : ∀ a, center a ∈ centers ∧ leaves a ⊆ L (center a) := by
    intro a
    refine ⟨mem_image.mpr ⟨a, mem_univ _, rfl⟩, ?_⟩
    intro w hw
    exact mem_biUnion.mpr ⟨a, mem_univ _, by simpa using hw⟩
  have hcover := circuit_frontier_graph_cover I F hthin hsafe hfour p l hp hl hacc
    e he C output Q hfrontier starOutput blockOutput center leaves hboundary
    hstar hblock G hcompute centers L hplacement
  intro u v huv
  rcases hcover u v huv with ⟨c, _, w, hw, horient⟩ | hmatching
  · obtain ⟨a, _, hwa⟩ := mem_biUnion.mp hw
    have hca : center a = c := by
      by_contra hn
      simp [hn] at hwa
    have hwleaf : w ∈ leaves a := by simpa [hca] using hwa
    exact Or.inl ⟨a, w, hwleaf, by simpa only [hca] using horient⟩
  · exact Or.inr hmatching

end ThinBlock

namespace ThinBlock

open Finset PEqualNP.EdgeOwnership
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair

lemma automatic_and_frontier_graph_cover {r n t B : ℕ}
    (I : Fin r → Fin r → Prop) (F : Fin B → Finset (Finset (Bool × Fin r)))
    (hthin : ∀ b, Thin (F b)) (hsafe : ∀ b, Safe I (F b))
    (hfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin B → Fin 3 → Fin r)
    (hp : ∀ b, Function.Injective (p b)) (hl : ∀ b, Function.Injective (l b))
    (hacc : ∀ b i, Accept (F b) (p b i) (l b i))
    (e : Bool × Fin r → Fin n) (he : Function.Injective e)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (output : ℕ)
    (rb : ReadsBack n C) (hm : Monotone2 C)
    (houtput : output < n + C.gates.length)
    (starOutput : Fin t → ℕ) (blockOutput : Fin B → ℕ)
    (center : Fin t → Fin n) (leaves : Fin t → Finset (Fin n))
    (hboundary : ∀ j ∈ OrFrontier.andFrontier n C output,
      (∃ a, n + j.val = starOutput a) ∨ (∃ b, n + j.val = blockOutput b))
    (hstar : ∀ a x, (C.wires (List.ofFn x)).getD (starOutput a) false = true ↔
      x (center a) = true ∧ ∃ v ∈ leaves a, x v = true)
    (hblock : ∀ b x, (C.wires (List.ofFn x)).getD (blockOutput b) false = true ↔
      CnfLogic.Holds (F b) (fun z => x (e z)))
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcompute : ∀ x, (C.wires (List.ofFn x)).getD output false =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true))
    : ∀ u v, G.Adj u v →
      (∃ a, ∃ w ∈ leaves a,
        (u = center a ∧ v = w) ∨ (u = w ∧ v = center a)) ∨
      (∃ b i, (u = e (false, p b i) ∧ v = e (true, l b i)) ∨
        (u = e (true, l b i) ∧ v = e (false, p b i))) := by
  have hzero := (edge_output_zero_and_pairs G
    (fun x => val C (List.ofFn x) output) hcompute).1
  have hsupport : singletonSupport n C output = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro u hu
    have htrue := mem_support.mp hu
    rw [hzero] at htrue
    cases htrue
  exact circuit_frontier_indexed_graph_cover I F hthin hsafe hfour p l hp hl hacc
    e he C output (OrFrontier.andFrontier n C output)
    (OrFrontier.frontier_val_iff rb hm houtput hsupport)
    starOutput blockOutput center leaves hboundary hstar hblock G hcompute

end ThinBlock

namespace ThinBlock

open Finset PEqualNP.EdgeOwnership
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair

lemma mapped_cnf_safe_of_implication {r n : ℕ}
    (I : Fin r → Fin r → Prop) (F : Finset (Finset (Bool × Fin r)))
    (e : (Bool × Fin r) ≃ Fin n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcross : ∀ a b, G.Adj (e (false, a)) (e (true, b)) → I a b)
    (hpoint : ∀ a b, ¬ G.Adj (e (false, a)) (e (false, b)))
    (hline : ∀ a b, ¬ G.Adj (e (true, a)) (e (true, b)))
    (f g : (Fin n → Bool) → Bool)
    (hcnf : ∀ x, g x = true ↔ CnfLogic.Holds F (fun z => x (e z)))
    (hbelow : ∀ x, g x = true → f x = true)
    (hcompute : ∀ x, f x = decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) :
    Safe I F := by
  intro z hz
  change CnfLogic.Holds F z at hz
  let x : Fin n → Bool := fun u => z (e.symm u)
  have hg : g x = true := (hcnf x).mpr (by simpa [x] using hz)
  have hf := hbelow x hg
  rw [hcompute] at hf
  obtain ⟨u, v, huv, hu, hv⟩ := of_decide_eq_true hf
  obtain ⟨⟨sa, a⟩, rfl⟩ := e.surjective u
  obtain ⟨⟨sb, b⟩, rfl⟩ := e.surjective v
  have hza : z (sa, a) = true := by simpa [x] using hu
  have hzb : z (sb, b) = true := by simpa [x] using hv
  cases sa <;> cases sb
  · exact (hpoint a b huv).elim
  · exact ⟨a, b, hcross a b huv, hza, hzb⟩
  · exact ⟨b, a, hcross b a huv.symm, hzb, hza⟩
  · exact (hline a b huv).elim

lemma or_ancestor_cnf_safe {r n : ℕ}
    (I : Fin r → Fin r → Prop) (F : Finset (Finset (Bool × Fin r)))
    (e : (Bool × Fin r) ≃ Fin n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcross : ∀ a b, G.Adj (e (false, a)) (e (true, b)) → I a b)
    (hpoint : ∀ a b, ¬ G.Adj (e (false, a)) (e (false, b)))
    (hline : ∀ a b, ¬ G.Adj (e (true, a)) (e (true, b)))
    (C : Circuit) (rb : ReadsBack n C) (output blockOutput : ℕ)
    (hancestor : OrFrontier.OrAncestor n C blockOutput output)
    (hcnf : ∀ x : Fin n → Bool, val C (List.ofFn x) blockOutput = true ↔
      CnfLogic.Holds F (fun z => x (e z)))
    (hcompute : ∀ x : Fin n → Bool, val C (List.ofFn x) output =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) : Safe I F := by
  exact mapped_cnf_safe_of_implication I F e G hcross hpoint hline
    (fun x => val C (List.ofFn x) output) (fun x => val C (List.ofFn x) blockOutput)
    hcnf (fun x hx => OrFrontier.ancestor_val rb hancestor x hx) hcompute

lemma frontier_cnf_safe {r n : ℕ}
    (I : Fin r → Fin r → Prop) (F : Finset (Finset (Bool × Fin r)))
    (e : (Bool × Fin r) ≃ Fin n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcross : ∀ a b, G.Adj (e (false, a)) (e (true, b)) → I a b)
    (hpoint : ∀ a b, ¬ G.Adj (e (false, a)) (e (false, b)))
    (hline : ∀ a b, ¬ G.Adj (e (true, a)) (e (true, b)))
    (C : Circuit) (rb : ReadsBack n C) (output : ℕ) (j : Fin C.gates.length)
    (hj : j ∈ OrFrontier.andFrontier n C output)
    (hcnf : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + j.val) = true ↔
      CnfLogic.Holds F (fun z => x (e z)))
    (hcompute : ∀ x : Fin n → Bool, val C (List.ofFn x) output =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) : Safe I F := by
  exact or_ancestor_cnf_safe I F e G hcross hpoint hline C rb output (n + j.val)
    (OrFrontier.mem_andFrontier.mp hj).2 hcnf hcompute

end ThinBlock

namespace ConcreteStarSources

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair

lemma star_value_iff {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    {j leaf : ℕ} (center : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and)
    (hinputs : (gateAt C j).inputs = [center.val, leaf] ∨
      (gateAt C j).inputs = [leaf, center.val])
    (leaves : Finset (Fin n))
    (hcomp : ∀ x : Fin n → Bool,
      val C (List.ofFn x) leaf = decide (∃ p ∈ leaves, x p = true))
    (x : Fin n → Bool) :
    val C (List.ofFn x) (n + j) = true ↔ x center = true ∧ ∃ p ∈ leaves, x p = true := by
  have hcenter : center.val ∈ (gateAt C j).inputs := by
    rcases hinputs with h | h <;> simp [h]
  have hleaf : leaf ∈ (gateAt C j).inputs := by
    rcases hinputs with h | h <;> simp [h]
  constructor
  · intro ht
    have hc := ((val_and (by simp) hj hop).1 ht _ hcenter).2
    have hl := ((val_and (by simp) hj hop).1 ht _ hleaf).2
    rw [val_ofFn] at hc
    rw [hcomp] at hl
    exact ⟨hc, of_decide_eq_true hl⟩
  · rintro ⟨hc, hl⟩
    apply (val_and (by simp) hj hop).2
    intro w hw
    refine ⟨rb j hj w hw, ?_⟩
    have heq : w = center.val ∨ w = leaf := by
      rcases hinputs with h | h
      · simpa [h] using hw
      · have h' : w = leaf ∨ w = center.val := by simpa [h] using hw
        exact h'.symm
    rcases heq with rfl | rfl
    · simpa only [val_ofFn] using hc
    · rw [hcomp]
      exact decide_eq_true hl

lemma star_source_valid {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    {j leaf : ℕ} (center : Fin n) (hj : j < C.gates.length)
    (hinputs : (gateAt C j).inputs = [center.val, leaf] ∨
      (gateAt C j).inputs = [leaf, center.val]) : leaf < n + C.gates.length := by
  have hleaf : leaf ∈ (gateAt C j).inputs := by
    rcases hinputs with h | h <;> simp [h]
  have hlt := rb j hj leaf hleaf
  omega

lemma star_inputs_classification {C : Circuit} {j center leaf : ℕ}
    (hinputs : (gateAt C j).inputs = [center, leaf] ∨
      (gateAt C j).inputs = [leaf, center]) :
    ∀ w ∈ (gateAt C j).inputs, w = center ∨ w = leaf := by
  intro w hw
  rcases hinputs with h | h
  · simpa [h] using hw
  · have h' : w = leaf ∨ w = center := by simpa [h] using hw
    exact h'.symm

end ConcreteStarSources

namespace ThinBlock

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.AndCorePrime
open PEqualNP.Outside.L_meta_2583.OrFrontier
open PEqualNP.Outside.L_meta_2583.ConcreteStarSources

def frontierStarGate {n t B : ℕ} {C : Circuit} {output : ℕ}
    (frontier : (Fin t ⊕ Fin B) ≃ {j : Fin C.gates.length // j ∈ andFrontier n C output})
    (i : Fin t) : Fin C.gates.length := (frontier (Sum.inl i)).val

def frontierBlockGate {n t B : ℕ} {C : Circuit} {output : ℕ}
    (frontier : (Fin t ⊕ Fin B) ≃ {j : Fin C.gates.length // j ∈ andFrontier n C output})
    (b : Fin B) : Fin C.gates.length := (frontier (Sum.inr b)).val

lemma thin_five_or_frontier_cost {r n t B : ℕ}
    (I : Fin r → Fin r → Prop)
    (F : Fin B → Finset (Finset (Bool × Fin r)))
    (hthin : ∀ b, Thin (F b))
    (hIfour : ∀ a b c d, a ≠ b → c ≠ d → ¬ (I a c ∧ I a d ∧ I b c ∧ I b d))
    (p l : Fin B → Fin 3 → Fin r)
    (hp : ∀ b, Function.Injective (p b)) (hl : ∀ b, Function.Injective (l b))
    (hacc : ∀ b i, Accept (F b) (p b i) (l b i)) (hcard : ∀ b, (F b).card = 5)
    (e : (Bool × Fin r) ≃ Fin n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfour : PEqualNP.TopForm.NoFourCycle G)
    (hcross : ∀ a b, G.Adj (e (false, a)) (e (true, b)) → I a b)
    (hpoint : ∀ a b, ¬ G.Adj (e (false, a)) (e (false, b)))
    (hline : ∀ a b, ¬ G.Adj (e (true, a)) (e (true, b)))
    (C : Circuit) (hm : Monotone2 C) (rb : ReadsBack n C)
    (output : ℕ) (houtput : output < n + C.gates.length)
    (hcompute : ∀ x : Fin n → Bool, val C (List.ofFn x) output =
      decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true))
    (frontier : (Fin t ⊕ Fin B) ≃ {j : Fin C.gates.length // j ∈ andFrontier n C output})
    (core : Fin B → Finset ℕ) (hcore : ∀ b, LinearAndCore n C (core b))
    (hout : ∀ b, n + (frontierBlockGate frontier b).val ∈ core b)
    (hcnf : ∀ b, ∀ x : Fin n → Bool,
      val C (List.ofFn x) (n + (frontierBlockGate frontier b).val) = true ↔
        CnfLogic.Holds (F b) (fun u => x (e u)))
    (starCenter : Fin t → Fin n) (starLeaf : Fin t → ℕ)
    (starSet : Fin t → Finset (Fin n))
    (hinputs : ∀ i, (gateAt C (frontierStarGate frontier i).val).inputs =
        [(starCenter i).val, starLeaf i] ∨
      (gateAt C (frontierStarGate frontier i).val).inputs = [starLeaf i, (starCenter i).val])
    (hleaf : ∀ i, ∀ x : Fin n → Bool,
      val C (List.ofFn x) (starLeaf i) = decide (∃ p ∈ starSet i, x p = true)) :
    ∃ T : Finset (Fin n), Cnf.Covers G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  have hsafe : ∀ b, Safe I (F b) := by
    intro b
    exact frontier_cnf_safe I (F b) e G hcross hpoint hline C rb output
      (frontierBlockGate frontier b) (frontier (Sum.inr b)).property (hcnf b) hcompute
  let a := frontierStarGate frontier
  let blockOutput := fun b => n + (frontierBlockGate frontier b).val
  have ha : Function.Injective a := by
    intro i j hij
    have h := frontier.injective (Subtype.ext hij)
    exact Sum.inl.inj h
  have hstarfront : ∀ i, a i ∈ andFrontier n C output := fun i =>
    (frontier (Sum.inl i)).property
  have haop : ∀ i, (gateAt C (a i).val).op = GateOp.and := fun i =>
    (mem_andFrontier.1 (hstarfront i)).1
  have hfrontcard : (andFrontier n C output).card = t + B := by
    simpa only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe] using
      (Fintype.card_congr frontier).symm
  have houtsafe : ∀ x : Fin n → Bool, val C (List.ofFn x) output = true →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    intro x hx
    rw [hcompute] at hx
    exact of_decide_eq_true hx
  have hzero := safe_output_support_empty G C output houtsafe
  have hfront : ∀ x : Fin n → Bool, val C (List.ofFn x) output = true ↔
      ∃ j ∈ andFrontier n C output, val C (List.ofFn x) (n + j.val) = true :=
    frontier_val_iff rb hm houtput hzero
  have hboundary : ∀ j ∈ andFrontier n C output,
      (∃ i, n + j.val = n + (a i).val) ∨ (∃ b, n + j.val = blockOutput b) := by
    intro j hj
    obtain ⟨s, hs⟩ := frontier.surjective ⟨j, hj⟩
    cases s with
    | inl i =>
      left
      refine ⟨i, ?_⟩
      have hi : a i = j := congrArg Subtype.val hs
      exact congrArg (fun k : Fin C.gates.length => n + k.val) hi.symm
    | inr b =>
      right
      refine ⟨b, ?_⟩
      have hb : frontierBlockGate frontier b = j := congrArg Subtype.val hs
      exact congrArg (fun k : Fin C.gates.length => n + k.val) hb.symm
  have hstar : ∀ i x, val C (List.ofFn x) (n + (a i).val) = true ↔
      x (starCenter i) = true ∧ ∃ v ∈ starSet i, x v = true := by
    intro i x
    exact star_value_iff rb (starCenter i) (a i).isLt (haop i) (hinputs i) (starSet i) (hleaf i) x
  have hstarsafe : ∀ i, ∀ x : Fin n → Bool, val C (List.ofFn x) (n + (a i).val) = true →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    intro i x hx
    exact houtsafe x (ancestor_val rb (mem_andFrontier.1 (hstarfront i)).2 x hx)
  have hcover := circuit_frontier_indexed_graph_cover I F hthin hsafe hIfour p l hp hl hacc
    e e.injective C output (andFrontier n C output) hfront
    (fun i => n + (a i).val) blockOutput starCenter starSet hboundary hstar hcnf G hcompute
  by_cases hne : 1 ≤ t + B
  · obtain ⟨z, hz, hzop, hzsmall⟩ := frontier_aggregation_map hm rb houtput hzero
      (by rw [hfrontcard] : t + B - 1 ≤ (andFrontier n C output).card - 1)
    exact thin_five_concrete_stars_cost I F hthin hsafe hIfour p l hp hl hacc hcard
      e G hfour hcross hline C hm rb blockOutput core hcore hout hcnf
      a ha haop starCenter starLeaf starSet (fun i => star_inputs_classification (hinputs i))
      hleaf (fun i => star_source_valid rb (starCenter i) (a i).isLt (hinputs i))
      hstarsafe hcover z hz hzop hzsmall hne
  · have hcovempty : Cnf.Covers G ∅ := by
      intro u v huv
      rcases hcover u v huv with ⟨i, hi⟩ | ⟨b, hb⟩
      · have hlt := i.isLt
        omega
      · have hlt := b.isLt
        omega
    have he := Cnf.edges_le_cover_degrees G ∅ hcovempty
    have hedge : G.edgeFinset.card ≤ 0 := by simpa using he
    exact ⟨∅, hcovempty, by simp only [card_empty]; omega⟩

end ThinBlock

end PEqualNP.Outside.L_meta_2583

namespace PEqualNP.Outside.L_meta_2583.AndCorePrime

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.AndClauseAtoms
open PEqualNP.Outside.L_meta_2583.SemanticLinearTag

lemma clause_atoms_card_le_and_add_one {n v : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C) (tag : ℕ → Option (Fin v))
    {root : ℕ} (hroot : root < n + C.gates.length) :
    (clauseAtoms n C tag root).card ≤ (andGates C).card + 1 := by
  classical
  let T := clauseAtoms n C tag
  have hc := union_network_one_target (n := n) (m := C.gates.length) T (T root)
    (fun w hw => clauseAtoms_input C tag hw)
    (fun j hj hlarge => (clauseAtoms_large_gate hm rb tag hj hlarge).2)
    ⟨root, hroot, rfl⟩
  have hsub : ((range C.gates.length).filter fun j =>
      2 ≤ (T (n + j)).card ∧ T (n + j) ⊆ T root) ⊆ andGates C := by
    intro j hj
    obtain ⟨hj, hlarge, htarget⟩ := mem_filter.mp hj
    exact mem_filter.mpr ⟨hj, (clauseAtoms_large_gate hm rb tag (mem_range.mp hj) hlarge).1⟩
  have hcount := card_le_card hsub
  dsimp only [T] at hc hcount
  omega

lemma linear_core_cnf_and_count {n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (R : Finset ℕ) (hcore : LinearAndCore n C R)
    {root : ℕ} (hroot : root ∈ R) (F : Finset (Finset (Fin n)))
    (hcard : ∀ W ∈ F, 2 ≤ W.card) (hanti : CnfLogic.Antichain F)
    (hcnf : ∀ x : Fin n → Bool,
      val C (List.ofFn x) root = true ↔ CnfLogic.Holds F x) :
    F.card ≤ (andGates C).card + 1 := by
  classical
  let encode := supportEncoding n
  have hcover := linear_core_cnf_family rb encode R hcore hroot F hcard hanti hcnf
  have hf := card_le_card hcover
  have himage : (F.image encode).card = F.card :=
    card_image_of_injective F (supportEncoding_injective n)
  have hc := clause_atoms_card_le_and_add_one hm rb (semanticTag n C encode)
    (hcore.1 root hroot)
  rw [himage] at hf
  omega

lemma embedded_linear_core_cnf_and_count {α : Type*} {n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (R : Finset ℕ) (hcore : LinearAndCore n C R) {root : ℕ} (hroot : root ∈ R)
    (F : Finset (Finset α)) (e : α → Fin n) (he : Function.Injective e)
    (hcard : ∀ W ∈ F, 2 ≤ W.card) (hanti : CnfLogic.Antichain F)
    (hcnf : ∀ x : Fin n → Bool,
      val C (List.ofFn x) root = true ↔ CnfLogic.Holds F (fun u => x (e u))) :
    F.card ≤ (andGates C).card + 1 := by
  classical
  have hc := linear_core_cnf_and_count hm rb R hcore hroot
    (F.image (fun W => W.image e)) (CnfLogic.clause_card_image F e he 2 hcard)
    (CnfLogic.antichain_image F e he hanti) (fun x => (hcnf x).trans (CnfLogic.holds_image F e x).symm)
  simpa only [CnfLogic.family_card_image F e he] using hc

end PEqualNP.Outside.L_meta_2583.AndCorePrime

namespace PEqualNP.Outside.L_meta_2583.AndCorePrime

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.AndClauseAtoms
open PEqualNP.Outside.L_meta_2583.MatchingCertificate

lemma matching_clause_card_two {r : ℕ} (hr : 2 ≤ r)
    (W : Finset (Bool × Fin r))
    (hcover : ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W) : 2 ≤ W.card := by
  let i₀ : Fin r := ⟨0, by omega⟩
  let i₁ : Fin r := ⟨1, by omega⟩
  obtain ⟨b₀, h₀⟩ : ∃ b : Bool, (b, i₀) ∈ W := by
    rcases hcover i₀ with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  obtain ⟨b₁, h₁⟩ : ∃ b : Bool, (b, i₁) ∈ W := by
    rcases hcover i₁ with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  have hne : (b₀, i₀) ≠ (b₁, i₁) := by
    intro heq
    have hval := congrArg (fun u : Bool × Fin r => u.2.val) heq
    dsimp [i₀, i₁] at hval
    omega
  have hc : 1 < W.card := one_lt_card.mpr ⟨(b₀, i₀), h₀, (b₁, i₁), h₁, hne⟩
  omega

lemma fano_prime_core_and_lower {n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (R : Finset ℕ) (hcore : LinearAndCore n C R) {root : ℕ} (hroot : root ∈ R)
    (F : Finset (Finset (Bool × Fin 7)))
    (e : Bool × Fin 7 → Fin n) (he : Function.Injective e)
    (hanti : CnfLogic.Antichain F)
    (hcnf : ∀ x : Fin n → Bool,
      val C (List.ofFn x) root = true ↔ CnfLogic.Holds F (fun u => x (e u)))
    (hcover : ∀ W ∈ F, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W)
    (hsafe : ∀ x : Bool × Fin 7 → Bool,
      CnfLogic.Holds F x →
      ∃ i j, inc7 i j ∧ x (false, i) = true ∧ x (true, j) = true) :
    22 ≤ (andGates C).card := by
  have hsize : ∀ W ∈ F, 2 ≤ W.card := fun W hW =>
    matching_clause_card_two (by decide) W (hcover W hW)
  have hc := embedded_linear_core_cnf_and_count hm rb R hcore hroot F e he hsize hanti hcnf
  have hl := safe_matching_cnf_7_lower F hcover hsafe
  omega

lemma q3_prime_core_and_lower {n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (R : Finset ℕ) (hcore : LinearAndCore n C R) {root : ℕ} (hroot : root ∈ R)
    (F : Finset (Finset (Bool × Fin 13)))
    (e : Bool × Fin 13 → Fin n) (he : Function.Injective e)
    (hanti : CnfLogic.Antichain F)
    (hcnf : ∀ x : Fin n → Bool,
      val C (List.ofFn x) root = true ↔ CnfLogic.Holds F (fun u => x (e u)))
    (hcover : ∀ W ∈ F, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W)
    (hsafe : ∀ x : Bool × Fin 13 → Bool,
      CnfLogic.Holds F x →
      ∃ i j, inc13 i j ∧ x (false, i) = true ∧ x (true, j) = true) :
    157 ≤ (andGates C).card := by
  have hsize : ∀ W ∈ F, 2 ≤ W.card := fun W hW =>
    matching_clause_card_two (by decide) W (hcover W hW)
  have hc := embedded_linear_core_cnf_and_count hm rb R hcore hroot F e he hsize hanti hcnf
  have hl := safe_matching_cnf_13_lower F hcover hsafe
  omega

end PEqualNP.Outside.L_meta_2583.AndCorePrime

namespace PEqualNP.Outside.L_meta_2583.AndCorePrime

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.AndClauseAtoms
open PEqualNP.Outside.L_meta_2583.SemanticLinearTag

lemma linear_core_atoms_semantics {n v : ℕ} {C : Circuit}
    (rb : ReadsBack n C) (encode : Finset (Fin n) → Fin v)
    (decode : Fin v → Finset (Fin n)) (hdecode : ∀ S, decode (encode S) = S)
    (R : Finset ℕ) (hcore : LinearAndCore n C R) {root : ℕ} (hroot : root ∈ R)
    (hnounit : ∀ i : Fin n, ∃ x : Fin n → Bool,
      val C (List.ofFn x) root = true ∧ x i = false) (x : Fin n → Bool) :
    val C (List.ofFn x) root = true ↔
      ∀ a ∈ clauseAtoms n C (semanticTag n C encode) root,
        ∃ i ∈ decode a, x i = true := by
  classical
  let tag := semanticTag n C encode
  have hclosed := linearAndCore_closed encode hcore
  have aux : ∀ w, w ∈ R →
      (∀ y : Fin n → Bool, val C (List.ofFn y) root = true → val C (List.ofFn y) w = true) →
      ∀ y : Fin n → Bool, val C (List.ofFn y) w = true ↔
        ∀ a ∈ clauseAtoms n C tag w, ∃ i ∈ decode a, y i = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw himp y
      cases ht : tag w with
      | some a =>
        obtain ⟨S, ha, hlinear⟩ := semanticTag_correct encode ht
        have hdec : decode a = S := by rw [ha, hdecode]
        rw [clauseAtoms_tagged C tag ht]
        simp only [mem_singleton, forall_eq, hdec]
        rw [hlinear]
        simp
      | none =>
        by_cases hin : w < n
        · let i : Fin n := ⟨w, hin⟩
          obtain ⟨z, hz, hzi⟩ := hnounit i
          have hv := himp z hz
          change val C (List.ofFn z) i.val = true at hv
          rw [val_ofFn, hzi] at hv
          cases hv
        · have hge : n ≤ w := by omega
          have hj : w - n < C.gates.length := by have hv := hcore.1 w hw; omega
          have heq : n + (w - n) = w := Nat.add_sub_of_le hge
          obtain ⟨hop, hchildren⟩ := hclosed.2 w hw hge ht
          have hchildimp : ∀ i ∈ (gateAt C (w - n)).inputs,
              ∀ z : Fin n → Bool, val C (List.ofFn z) root = true →
                val C (List.ofFn z) i = true := by
            intro i hi z hz
            have hv := himp z hz
            rw [← heq] at hv
            exact ((val_and (by simp) hj hop).mp hv i hi).2
          have hchildsem : ∀ i ∈ (gateAt C (w - n)).inputs,
              val C (List.ofFn y) i = true ↔
                ∀ a ∈ clauseAtoms n C tag i, ∃ u ∈ decode a, y u = true := by
            intro i hi
            have hiless : i < w := by simpa only [heq] using rb (w - n) hj i hi
            exact ih i hiless (hchildren i hi) (hchildimp i hi) y
          have hatoms : clauseAtoms n C tag w =
              (gateAt C (w - n)).inputs.toFinset.biUnion (clauseAtoms n C tag) := by
            simpa only [heq] using
              clauseAtoms_and rb tag hj (by simpa only [heq] using ht) hop
          rw [hatoms]
          constructor
          · intro hv a ha
            obtain ⟨i, hi, hai⟩ := mem_biUnion.mp ha
            have hi' := List.mem_toFinset.mp hi
            have hvi : val C (List.ofFn y) i = true := by
              rw [← heq] at hv
              exact ((val_and (by simp) hj hop).mp hv i hi').2
            exact (hchildsem i hi').mp hvi a hai
          · intro hall
            rw [← heq, val_and (by simp) hj hop]
            intro i hi
            refine ⟨rb (w - n) hj i hi, (hchildsem i hi).mpr ?_⟩
            intro a ha
            exact hall a (mem_biUnion.mpr ⟨i, List.mem_toFinset.mpr hi, ha⟩)
  exact aux root hroot (fun _ hx => hx) x

lemma linear_core_extracted_cnf {n v : ℕ} {C : Circuit}
    (rb : ReadsBack n C) (encode : Finset (Fin n) → Fin v)
    (decode : Fin v → Finset (Fin n)) (hdecode : ∀ S, decode (encode S) = S)
    (R : Finset ℕ) (hcore : LinearAndCore n C R) {root : ℕ} (hroot : root ∈ R)
    (hnounit : ∀ i : Fin n, ∃ x : Fin n → Bool,
      val C (List.ofFn x) root = true ∧ x i = false) :
    ∀ x : Fin n → Bool, val C (List.ofFn x) root = true ↔
      CnfLogic.Holds ((clauseAtoms n C (semanticTag n C encode) root).image decode) x := by
  intro x
  rw [linear_core_atoms_semantics rb encode decode hdecode R hcore hroot hnounit x]
  constructor
  · intro h W hW
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hW
    exact h a ha
  · intro h a ha
    exact h (decode a) (mem_image.mpr ⟨a, ha, rfl⟩)

end PEqualNP.Outside.L_meta_2583.AndCorePrime

namespace PEqualNP.Outside.L_meta_2583.AndCorePrime

open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair
open PEqualNP.Outside.L_meta_2583.AndClauseAtoms
open PEqualNP.Outside.L_meta_2583.SemanticLinearTag
open PEqualNP.Outside.L_meta_2583.MatchingCertificate

lemma matching_acceptance_no_unit {r n : ℕ} (hr : 2 ≤ r) (C : Circuit) (root : ℕ)
    (e : Bool × Fin r → Fin n) (he : Function.Injective e)
    (hmatch : ∀ i, val C (List.ofFn (pairInput (e (false, i)) (e (true, i)))) root = true) :
    ∀ u : Fin n, ∃ x : Fin n → Bool, val C (List.ofFn x) root = true ∧ x u = false := by
  let i₀ : Fin r := ⟨0, by omega⟩
  let i₁ : Fin r := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [i₀, i₁] at hv
    omega
  intro u
  by_cases h₀ : u = e (false, i₀) ∨ u = e (true, i₀)
  · have h₁ : ¬ (u = e (false, i₁) ∨ u = e (true, i₁)) := by
      intro h
      rcases h₀ with h₀ | h₀ <;> rcases h with h | h <;>
        exact hne (congrArg Prod.snd (he (h₀.symm.trans h)))
    exact ⟨pairInput (e (false, i₁)) (e (true, i₁)), hmatch i₁, by simp [pairInput, h₁]⟩
  · exact ⟨pairInput (e (false, i₀)) (e (true, i₀)), hmatch i₀, by simp [pairInput, h₀]⟩

lemma core_matching_cnf_certificate {r n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C) (hr : 2 ≤ r)
    (R : Finset ℕ) (hcore : LinearAndCore n C R) {root : ℕ} (hroot : root ∈ R)
    (I : Fin r → Fin r → Prop) (e : (Bool × Fin r) ≃ Fin n)
    (hmatch : ∀ i, val C (List.ofFn (pairInput (e (false, i)) (e (true, i)))) root = true)
    (hsafe : ∀ x : Fin n → Bool, val C (List.ofFn x) root = true →
      ∃ i j, I i j ∧ x (e (false, i)) = true ∧ x (e (true, j)) = true) :
    ∃ F : Finset (Finset (Bool × Fin r)),
      F.card ≤ (andGates C).card + 1 ∧
      (∀ W ∈ F, ∀ i, (false, i) ∈ W ∨ (true, i) ∈ W) ∧
      (∀ x : Bool × Fin r → Bool, CnfLogic.Holds F x →
        ∃ i j, I i j ∧ x (false, i) = true ∧ x (true, j) = true) := by
  classical
  let encode := supportEncoding n
  let decode := (supportEncoding n).symm
  let A := clauseAtoms n C (semanticTag n C encode) root
  let D := A.image decode
  let F := D.image (fun W => W.image e.symm)
  have hdecode : ∀ S, decode (encode S) = S := fun S => (supportEncoding n).symm_apply_apply S
  have hnounit := matching_acceptance_no_unit hr C root e e.injective hmatch
  have hsem : ∀ x : Fin n → Bool,
      val C (List.ofFn x) root = true ↔ CnfLogic.Holds D x :=
    linear_core_extracted_cnf rb encode decode hdecode R hcore hroot hnounit
  have hcard : F.card ≤ (andGates C).card + 1 := by
    have hFD : F.card ≤ D.card := card_image_le
    have hDA : D.card ≤ A.card := card_image_le
    have hA := clause_atoms_card_le_and_add_one hm rb (semanticTag n C encode)
      (hcore.1 root hroot)
    dsimp only [A] at hDA
    omega
  refine ⟨F, hcard, ?_, ?_⟩
  · intro W hW i
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hW
    obtain ⟨u, hu, huv⟩ := (hsem (pairInput (e (false, i)) (e (true, i)))).mp (hmatch i) S hS
    have hpair : u = e (false, i) ∨ u = e (true, i) := by simpa [pairInput] using huv
    rcases hpair with rfl | rfl
    · exact Or.inl (mem_image.mpr ⟨e (false, i), hu, by simp⟩)
    · exact Or.inr (mem_image.mpr ⟨e (true, i), hu, by simp⟩)
  · intro x hx
    let y : Fin n → Bool := fun u => x (e.symm u)
    have hD : CnfLogic.Holds D y := (CnfLogic.holds_image D e.symm x).mp hx
    obtain ⟨i, j, hij, hi, hj⟩ := hsafe y ((hsem y).mpr hD)
    exact ⟨i, j, hij, by simpa [y] using hi, by simpa [y] using hj⟩

lemma fano_core_and_lower {n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (R : Finset ℕ) (hcore : LinearAndCore n C R) {root : ℕ} (hroot : root ∈ R)
    (e : (Bool × Fin 7) ≃ Fin n)
    (hmatch : ∀ i, val C (List.ofFn (pairInput (e (false, i)) (e (true, i)))) root = true)
    (hsafe : ∀ x : Fin n → Bool, val C (List.ofFn x) root = true →
      ∃ i j, inc7 i j ∧ x (e (false, i)) = true ∧ x (e (true, j)) = true) :
    22 ≤ (andGates C).card := by
  obtain ⟨F, hcount, hcover, hsafeF⟩ :=
    core_matching_cnf_certificate hm rb (by decide) R hcore hroot inc7 e hmatch hsafe
  have hlower := safe_matching_cnf_7_lower F hcover hsafeF
  omega

lemma q3_core_and_lower {n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (R : Finset ℕ) (hcore : LinearAndCore n C R) {root : ℕ} (hroot : root ∈ R)
    (e : (Bool × Fin 13) ≃ Fin n)
    (hmatch : ∀ i, val C (List.ofFn (pairInput (e (false, i)) (e (true, i)))) root = true)
    (hsafe : ∀ x : Fin n → Bool, val C (List.ofFn x) root = true →
      ∃ i j, inc13 i j ∧ x (e (false, i)) = true ∧ x (e (true, j)) = true) :
    157 ≤ (andGates C).card := by
  obtain ⟨F, hcount, hcover, hsafeF⟩ :=
    core_matching_cnf_certificate hm rb (by decide) R hcore hroot inc13 e hmatch hsafe
  have hlower := safe_matching_cnf_13_lower F hcover hsafeF
  omega

end PEqualNP.Outside.L_meta_2583.AndCorePrime

namespace PEqualNP.Outside.L_meta_2583.ThinMixedContext

lemma common_two_points_factorization : ∀ a b x y r t : Bool,
    ((a || b || r) && (x || y || t) && (b || r || x) &&
      (a || r || y) && (a || b || t)) =
    ((((b || x) && (a || y) && (a || b)) || (r && (a || b || t))) &&
      (x || y || t)) := by decide

lemma common_two_points_shared_three : ∀ a b x y r t : Bool,
    ((a || b || r) && (x || y || t) && (b || r || x) &&
      (a || r || y) && (a || b || t)) =
    ((((b || x) && (a || y) && (a || b)) || r) &&
      (((a || b) && (x || y)) || t)) := by decide

end PEqualNP.Outside.L_meta_2583.ThinMixedContext

namespace PEqualNP.Outside.L_meta_2583.TightTransferObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.TopForm PEqualNP.ReadK

def cone : Circuit :=
  { gates := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [3, 2]⟩], output := 4 }

lemma cone_ao2 : IsAO2 3 cone := by decide

lemma cone_tight :
    IsPrimeImplicant 3 cone ({0, 1} : Finset (Fin 3)) ∧
    ({0, 1} : Finset (Fin 3)).card =
      (cone.gates.filter (fun g => match g.op with | .and => true | _ => false)).length + 1 := by decide

lemma cone_one_or :
    (cone.gates.filter (fun g => match g.op with | .or => true | _ => false)).length = 1 := by decide

lemma cone_cnf : ∀ x : Fin 3 → Bool,
    circuitFun 3 cone x = ((x 0 || x 2) && (x 1 || x 2)) := by decide

lemma cone_missing_clauses :
    (¬ ∃ w : Fin 5, ∀ x : Fin 3 → Bool,
      circuitFun 3 {cone with output := w.val} x = (x 0 || x 2)) ∧
    (¬ ∃ w : Fin 5, ∀ x : Fin 3 → Bool,
      circuitFun 3 {cone with output := w.val} x = (x 1 || x 2)) := by decide

def matchingContext : Circuit :=
  { gates := [⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [4, 2]⟩,
      ⟨GateOp.and, [5, 3]⟩, ⟨GateOp.or, [4, 6]⟩], output := 7 }

lemma matching_ao2 : IsAO2 4 matchingContext := by decide

lemma matching_semantics : ∀ x : Fin 4 → Bool,
    circuitFun 4 matchingContext x = ((x 0 && x 1) || (x 2 && x 3)) := by decide

lemma matching_no_four_cycle :
    NoFourCycle (edgeGraph 4 [(0, 1), (2, 3)]) := by decide

lemma matching_all_gates_essential : ∀ j : Fin 4,
    ∃ u v : Fin 4, (edgeGraph 4 [(0, 1), (2, 3)]).Adj u v ∧
      circuitFun 4 matchingContext (pairInput u v) = true ∧
      circuitFun 4 {matchingContext with gates :=
        (matchingContext.gates.set j.val ⟨GateOp.or, []⟩)} (pairInput u v) = false := by decide

lemma matching_operand_redundant : ∀ x : Fin 4 → Bool,
    circuitFun 4 {matchingContext with gates :=
      (matchingContext.gates.set 1 ⟨GateOp.or, [2]⟩)} x =
      circuitFun 4 matchingContext x := by decide

end PEqualNP.Outside.L_meta_2583.TightTransferObstruction

namespace PEqualNP.Outside.L_meta_2583.ThinMixedContext

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2583.H8Projected.Repair

def sharedCircuit : Circuit :=
  { gates := [
    { op := .or, inputs := [0, 1] },
    { op := .or, inputs := [7, 8] },
    { op := .or, inputs := [1, 7] },
    { op := .or, inputs := [0, 8] },
    { op := .and, inputs := [16, 17] },
    { op := .and, inputs := [18, 14] },
    { op := .and, inputs := [14, 15] },
    { op := .or, inputs := [19, 2] },
    { op := .or, inputs := [20, 13] },
    { op := .and, inputs := [21, 22] },
    { op := .or, inputs := [19, 4] },
    { op := .or, inputs := [20, 11] },
    { op := .and, inputs := [24, 25] }],
    output := 26 }

lemma sharedCircuit_ao2 : PEqualNP.TopForm.IsAO2 14 sharedCircuit := by decide

lemma sharedCircuit_counts : sharedCircuit.size = 13 ∧
    (sharedCircuit.gates.filter (fun g => match g.op with | .and => true | _ => false)).length = 5 ∧
    (sharedCircuit.gates.filter (fun g => match g.op with | .or => true | _ => false)).length = 8 := by
  decide

lemma sharedCircuit_values (x : Fin 14 → Bool) :
    val sharedCircuit (List.ofFn x) 23 = (((((x 1 || x 7) && (x 0 || x 8)) && (x 0 || x 1)) || x 2) && (((x 0 || x 1) && (x 7 || x 8)) || x 13)) ∧
    val sharedCircuit (List.ofFn x) 26 = (((((x 1 || x 7) && (x 0 || x 8)) && (x 0 || x 1)) || x 4) && (((x 0 || x 1) && (x 7 || x 8)) || x 11)) := by
  have h0 : val sharedCircuit (List.ofFn x) 0 = x 0 := val_ofFn sharedCircuit x 0
  have h1 : val sharedCircuit (List.ofFn x) 1 = x 1 := val_ofFn sharedCircuit x 1
  have h2 : val sharedCircuit (List.ofFn x) 2 = x 2 := val_ofFn sharedCircuit x 2
  have h4 : val sharedCircuit (List.ofFn x) 4 = x 4 := val_ofFn sharedCircuit x 4
  have h7 : val sharedCircuit (List.ofFn x) 7 = x 7 := val_ofFn sharedCircuit x 7
  have h8 : val sharedCircuit (List.ofFn x) 8 = x 8 := val_ofFn sharedCircuit x 8
  have h11 : val sharedCircuit (List.ofFn x) 11 = x 11 := val_ofFn sharedCircuit x 11
  have h13 : val sharedCircuit (List.ofFn x) 13 = x 13 := val_ofFn sharedCircuit x 13
  have h14 : val sharedCircuit (List.ofFn x) 14 = (x 0 || x 1) := by
    have h := val_gate (n := 14) (C := sharedCircuit) (x := List.ofFn x) (j := 0) (by simp) (by decide)
    have hg : gateAt sharedCircuit 0 = { op := .or, inputs := [0, 1] } := by rfl
    rw [hg] at h
    simpa only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, ite_eq_left (by decide : 0 < 14 + 0), ite_eq_left (by decide : 1 < 14 + 0), h0, h1, Bool.or_false, Bool.and_true] using h
  have h15 : val sharedCircuit (List.ofFn x) 15 = (x 7 || x 8) := by
    have h := val_gate (n := 14) (C := sharedCircuit) (x := List.ofFn x) (j := 1) (by simp) (by decide)
    have hg : gateAt sharedCircuit 1 = { op := .or, inputs := [7, 8] } := by rfl
    rw [hg] at h
    simpa only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, ite_eq_left (by decide : 7 < 14 + 1), ite_eq_left (by decide : 8 < 14 + 1), h7, h8, Bool.or_false, Bool.and_true] using h
  have h16 : val sharedCircuit (List.ofFn x) 16 = (x 1 || x 7) := by
    have h := val_gate (n := 14) (C := sharedCircuit) (x := List.ofFn x) (j := 2) (by simp) (by decide)
    have hg : gateAt sharedCircuit 2 = { op := .or, inputs := [1, 7] } := by rfl
    rw [hg] at h
    simpa only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, ite_eq_left (by decide : 1 < 14 + 2), ite_eq_left (by decide : 7 < 14 + 2), h1, h7, Bool.or_false, Bool.and_true] using h
  have h17 : val sharedCircuit (List.ofFn x) 17 = (x 0 || x 8) := by
    have h := val_gate (n := 14) (C := sharedCircuit) (x := List.ofFn x) (j := 3) (by simp) (by decide)
    have hg : gateAt sharedCircuit 3 = { op := .or, inputs := [0, 8] } := by rfl
    rw [hg] at h
    simpa only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, ite_eq_left (by decide : 0 < 14 + 3), ite_eq_left (by decide : 8 < 14 + 3), h0, h8, Bool.or_false, Bool.and_true] using h
  have h18 : val sharedCircuit (List.ofFn x) 18 = ((x 1 || x 7) && (x 0 || x 8)) := by
    have h := val_gate (n := 14) (C := sharedCircuit) (x := List.ofFn x) (j := 4) (by simp) (by decide)
    have hg : gateAt sharedCircuit 4 = { op := .and, inputs := [16, 17] } := by rfl
    rw [hg] at h
    simpa only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, ite_eq_left (by decide : 16 < 14 + 4), ite_eq_left (by decide : 17 < 14 + 4), h16, h17, Bool.or_false, Bool.and_true] using h
  have h19 : val sharedCircuit (List.ofFn x) 19 = (((x 1 || x 7) && (x 0 || x 8)) && (x 0 || x 1)) := by
    have h := val_gate (n := 14) (C := sharedCircuit) (x := List.ofFn x) (j := 5) (by simp) (by decide)
    have hg : gateAt sharedCircuit 5 = { op := .and, inputs := [18, 14] } := by rfl
    rw [hg] at h
    simpa only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, ite_eq_left (by decide : 18 < 14 + 5), ite_eq_left (by decide : 14 < 14 + 5), h18, h14, Bool.or_false, Bool.and_true] using h
  have h20 : val sharedCircuit (List.ofFn x) 20 = ((x 0 || x 1) && (x 7 || x 8)) := by
    have h := val_gate (n := 14) (C := sharedCircuit) (x := List.ofFn x) (j := 6) (by simp) (by decide)
    have hg : gateAt sharedCircuit 6 = { op := .and, inputs := [14, 15] } := by rfl
    rw [hg] at h
    simpa only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, ite_eq_left (by decide : 14 < 14 + 6), ite_eq_left (by decide : 15 < 14 + 6), h14, h15, Bool.or_false, Bool.and_true] using h
  have h21 : val sharedCircuit (List.ofFn x) 21 = ((((x 1 || x 7) && (x 0 || x 8)) && (x 0 || x 1)) || x 2) := by
    have h := val_gate (n := 14) (C := sharedCircuit) (x := List.ofFn x) (j := 7) (by simp) (by decide)
    have hg : gateAt sharedCircuit 7 = { op := .or, inputs := [19, 2] } := by rfl
    rw [hg] at h
    simpa only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, ite_eq_left (by decide : 19 < 14 + 7), ite_eq_left (by decide : 2 < 14 + 7), h19, h2, Bool.or_false, Bool.and_true] using h
  have h22 : val sharedCircuit (List.ofFn x) 22 = (((x 0 || x 1) && (x 7 || x 8)) || x 13) := by
    have h := val_gate (n := 14) (C := sharedCircuit) (x := List.ofFn x) (j := 8) (by simp) (by decide)
    have hg : gateAt sharedCircuit 8 = { op := .or, inputs := [20, 13] } := by rfl
    rw [hg] at h
    simpa only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, ite_eq_left (by decide : 20 < 14 + 8), ite_eq_left (by decide : 13 < 14 + 8), h20, h13, Bool.or_false, Bool.and_true] using h
  have h23 : val sharedCircuit (List.ofFn x) 23 = (((((x 1 || x 7) && (x 0 || x 8)) && (x 0 || x 1)) || x 2) && (((x 0 || x 1) && (x 7 || x 8)) || x 13)) := by
    have h := val_gate (n := 14) (C := sharedCircuit) (x := List.ofFn x) (j := 9) (by simp) (by decide)
    have hg : gateAt sharedCircuit 9 = { op := .and, inputs := [21, 22] } := by rfl
    rw [hg] at h
    simpa only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, ite_eq_left (by decide : 21 < 14 + 9), ite_eq_left (by decide : 22 < 14 + 9), h21, h22, Bool.or_false, Bool.and_true] using h
  have h24 : val sharedCircuit (List.ofFn x) 24 = ((((x 1 || x 7) && (x 0 || x 8)) && (x 0 || x 1)) || x 4) := by
    have h := val_gate (n := 14) (C := sharedCircuit) (x := List.ofFn x) (j := 10) (by simp) (by decide)
    have hg : gateAt sharedCircuit 10 = { op := .or, inputs := [19, 4] } := by rfl
    rw [hg] at h
    simpa only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, ite_eq_left (by decide : 19 < 14 + 10), ite_eq_left (by decide : 4 < 14 + 10), h19, h4, Bool.or_false, Bool.and_true] using h
  have h25 : val sharedCircuit (List.ofFn x) 25 = (((x 0 || x 1) && (x 7 || x 8)) || x 11) := by
    have h := val_gate (n := 14) (C := sharedCircuit) (x := List.ofFn x) (j := 11) (by simp) (by decide)
    have hg : gateAt sharedCircuit 11 = { op := .or, inputs := [20, 11] } := by rfl
    rw [hg] at h
    simpa only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, ite_eq_left (by decide : 20 < 14 + 11), ite_eq_left (by decide : 11 < 14 + 11), h20, h11, Bool.or_false, Bool.and_true] using h
  have h26 : val sharedCircuit (List.ofFn x) 26 = (((((x 1 || x 7) && (x 0 || x 8)) && (x 0 || x 1)) || x 4) && (((x 0 || x 1) && (x 7 || x 8)) || x 11)) := by
    have h := val_gate (n := 14) (C := sharedCircuit) (x := List.ofFn x) (j := 12) (by simp) (by decide)
    have hg : gateAt sharedCircuit 12 = { op := .and, inputs := [24, 25] } := by rfl
    rw [hg] at h
    simpa only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq, ite_eq_left (by decide : 24 < 14 + 12), ite_eq_left (by decide : 25 < 14 + 12), h24, h25, Bool.or_false, Bool.and_true] using h
  exact ⟨h23, h26⟩

lemma sharedCircuit_first_cnf (x : Fin 14 → Bool) :
    val sharedCircuit (List.ofFn x) 23 =
      ((x 0 || x 1 || x 2) && (x 7 || x 8 || x 13) &&
        (x 1 || x 2 || x 7) && (x 0 || x 2 || x 8) && (x 0 || x 1 || x 13)) := by
  rw [(sharedCircuit_values x).1]
  exact (common_two_points_shared_three (x 0) (x 1) (x 7) (x 8) (x 2) (x 13)).symm

lemma sharedCircuit_second_cnf (x : Fin 14 → Bool) :
    val sharedCircuit (List.ofFn x) 26 =
      ((x 0 || x 1 || x 4) && (x 7 || x 8 || x 11) &&
        (x 1 || x 4 || x 7) && (x 0 || x 4 || x 8) && (x 0 || x 1 || x 11)) := by
  rw [(sharedCircuit_values x).2]
  exact (common_two_points_shared_three (x 0) (x 1) (x 7) (x 8) (x 4) (x 11)).symm

end PEqualNP.Outside.L_meta_2583.ThinMixedContext
