import PEqualNP.Outside.L_meta_2656

namespace PEqualNP.Outside.L_meta_650

def incidenceEdges : List (ℕ × ℕ) :=
  [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]

def incidenceRow (p : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter fun l => (p.val, 13 + l.val) ∈ incidenceEdges

lemma incidenceEdges_length : incidenceEdges.length = 52 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma incidenceRow_card : ∀ p : Fin 13, (incidenceRow p).card = 4 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma incidenceColumn_card : ∀ l : Fin 13,
    (Finset.univ.filter fun p : Fin 13 => (p.val, 13 + l.val) ∈ incidenceEdges).card = 4 := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma incidenceRows_intersection : ∀ p q : Fin 13, p ≠ q →
    (incidenceRow p ∩ incidenceRow q).card = 1 := by decide

def matchingColumn (p : Fin 13) : Fin 13 :=
  ![0, 2, 11, 6, 10, 8, 7, 9, 5, 4, 12, 3, 1] p

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma matchingColumn_injective : Function.Injective matchingColumn := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma matchingColumn_edge : ∀ p : Fin 13,
    (p.val, 13 + (matchingColumn p).val) ∈ incidenceEdges := by decide

def leftVertex (p : Fin 13) : Fin 26 := ⟨p.val, by omega⟩

def rightVertex (l : Fin 13) : Fin 26 := ⟨13 + l.val, by omega⟩

lemma matching_cover_card (T : Finset (Fin 26))
    (hT : ∀ p : Fin 13, leftVertex p ∈ T ∨ rightVertex (matchingColumn p) ∈ T) :
    13 ≤ T.card := by
  let choose : Fin 13 → Fin 26 := fun p =>
    if leftVertex p ∈ T then leftVertex p else rightVertex (matchingColumn p)
  have hc : ∀ p, choose p ∈ T := by
    intro p
    dsimp [choose]
    split_ifs with hp
    · exact hp
    · exact (hT p).resolve_left hp
  have hi : Function.Injective choose := by
    intro p q h
    dsimp [choose] at h
    split_ifs at h with hp hq hq
    · apply Fin.ext
      exact congrArg (fun v : Fin 26 => v.val) h
    · have hv := congrArg Fin.val h
      dsimp [leftVertex, rightVertex] at hv
      have := p.isLt
      omega
    · have hv := congrArg Fin.val h
      dsimp [leftVertex, rightVertex] at hv
      have := q.isLt
      omega
    · apply matchingColumn_injective
      apply Fin.ext
      have hv := congrArg Fin.val h
      dsimp [rightVertex] at hv
      omega
  have hs : Finset.univ.image choose ⊆ T := by
    intro v hv
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hv
    exact hc p
  have hb := Finset.card_le_card hs
  simpa [Finset.card_image_of_injective, hi] using hb

lemma incidence_cover_card (T : Finset (Fin 26))
    (hT : ∀ u v : Fin 26, (u.val, v.val) ∈ incidenceEdges → u ∈ T ∨ v ∈ T) :
    13 ≤ T.card := by
  apply matching_cover_card T
  intro p
  apply hT
  exact matchingColumn_edge p


-- Research partial: the imported outside theorem is not a permitted final dependency.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def incidenceGraph : SimpleGraph (Fin 26) where
  Adj u v := (u.val, v.val) ∈ incidenceEdges ∨ (v.val, u.val) ∈ incidenceEdges
  symm := by intro u v h; exact h.symm
  loopless := by
    intro u
    fin_cases u <;> decide

instance incidenceGraph_decidable : DecidableRel incidenceGraph.Adj :=
  fun u v => inferInstanceAs (Decidable
    ((u.val, v.val) ∈ incidenceEdges ∨ (v.val, u.val) ∈ incidenceEdges))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma incidenceGraph_noFour : PEqualNP.TopForm.NoFourCycle incidenceGraph := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma incidenceGraph_edges : incidenceGraph.edgeFinset.card = 52 := by decide +kernel

lemma incidenceGraph_noRectangle (a b c d : Fin 26) (hac : a ≠ c) (hbd : b ≠ d) :
    ¬ (incidenceGraph.Adj a b ∧ incidenceGraph.Adj b c ∧
      incidenceGraph.Adj c d ∧ incidenceGraph.Adj d a) := by
  rintro ⟨hab, hbc, hcd, hda⟩
  have sub : ({b, d} : Finset (Fin 26)) ⊆
      Finset.univ.filter (fun w => incidenceGraph.Adj a w ∧ incidenceGraph.Adj c w) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · simp [hab, hbc.symm]
    · simp [hda.symm, hcd]
  have card := Finset.card_le_card sub
  have upper := incidenceGraph_noFour a c hac
  have two : ({b, d} : Finset (Fin 26)).card = 2 := by simp [hbd]
  omega

lemma incidenceGraph_cover (T : Finset (Fin 26))
    (hT : ∀ u v, incidenceGraph.Adj u v → u ∈ T ∨ v ∈ T) : 13 ≤ T.card := by
  apply incidence_cover_card T
  intro u v huv
  exact hT u v (Or.inl huv)

def postedValue (x : Fin 26 → Bool) : Prop :=
  ∃ u v : Fin 26, (u.val, v.val) ∈ incidenceEdges ∧ x u = true ∧ x v = true

lemma incidenceGraph_value (x : Fin 26 → Bool) :
    (∃ u v : Fin 26, incidenceGraph.Adj u v ∧ x u = true ∧ x v = true) ↔
      postedValue x := by
  constructor
  · rintro ⟨u,v,h,hu,hv⟩
    rcases h with h | h
    · exact ⟨u,v,h,hu,hv⟩
    · exact ⟨v,u,h,hv,hu⟩
  · rintro ⟨u,v,h,hu,hv⟩
    exact ⟨u,v,Or.inl h,hu,hv⟩

def smallInput (x : Fin 26 → Bool) : Prop :=
  x = (fun _ => false) ∨
  (∃ u : Fin 26, x = fun z => decide (z = u)) ∨
  (∃ u v : Fin 26, x = fun z => decide (z = u ∨ z = v))

lemma pair_clean_lower (C : Circuit) (mono : Monotone2 C)
    (correct : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ postedValue x)
    (clean : ∀ (i : Fin C.gates.length) (x : Fin 26 → Bool), smallInput x →
      (C.gates.get i).op = GateOp.and →
      (C.wires (List.ofFn x)).getD (26 + i.val) false = true → postedValue x) :
    64 ≤ C.size := by
  obtain ⟨T,cover,bound⟩ := PEqualNP.Outside.L_meta_2656.pairCleanBound
    26 incidenceGraph incidenceGraph_noRectangle C.gates C.output mono
    (fun x => Bool.eq_iff_iff.mpr (by
      simp only [decide_eq_true_eq]
      exact (correct x).trans (incidenceGraph_value x).symm))
    (fun i x hx hop hv => (incidenceGraph_value x).mpr (clean i x hx hop hv))
  have lower := incidenceGraph_cover T cover
  rw [incidenceGraph_edges] at bound
  change 64 ≤ C.gates.length
  omega

lemma small_circuit_has_dirty_pair (C : Circuit) (mono : Monotone2 C)
    (size : C.size ≤ 63)
    (correct : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ postedValue x) :
    ∃ (i : Fin C.gates.length) (x : Fin 26 → Bool), smallInput x ∧
      (C.gates.get i).op = GateOp.and ∧
      (C.wires (List.ofFn x)).getD (26 + i.val) false = true ∧ ¬ postedValue x := by
  by_contra h
  have clean : ∀ (i : Fin C.gates.length) (x : Fin 26 → Bool), smallInput x →
      (C.gates.get i).op = GateOp.and →
      (C.wires (List.ofFn x)).getD (26 + i.val) false = true → postedValue x := by
    intro i x hx hop hv
    by_contra hf
    exact h ⟨i,x,hx,hop,hv,hf⟩
  have lower := pair_clean_lower C mono correct clean
  omega

end PEqualNP.Outside.L_meta_650
