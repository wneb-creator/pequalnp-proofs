import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.MetaComplexity.CoverPromise

theorem cut_adj {n : ℕ} (G : SimpleGraph (Fin n)) (z u v : Fin n) :
    (G.deleteEdges (G.incidenceSet z)).Adj u v ↔ G.Adj u v ∧ u ≠ z ∧ v ≠ z := by
  exact SimpleGraph.deleteIncidenceSet_adj

theorem exists_positive_cut_edge (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧
      ∃ u v : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj u v := by
  classical
  obtain ⟨e, he, f, hf, hne⟩ := Finset.one_lt_card.mp (show 1 < G.edgeFinset.card by omega)
  induction e using Sym2.inductionOn with
  | hf a b =>
    induction f using Sym2.inductionOn with
    | hf c d =>
      have hab : G.Adj a b := by simpa using he
      have hcd : G.Adj c d := by simpa using hf
      have hab' : a ≠ b := G.ne_of_adj hab
      have hout : (a ≠ c ∧ a ≠ d) ∨ (b ≠ c ∧ b ≠ d) := by
        by_cases hac : a = c <;> by_cases had : a = d <;>
          by_cases hbc : b = c <;> by_cases hbd : b = d <;>
          simp_all
      rcases hout with ⟨hac, had⟩ | ⟨hbc, hbd⟩
      · exact ⟨a, (G.degree_pos_iff_exists_adj a).mpr ⟨b, hab⟩, c, d,
          (cut_adj G a c d).mpr ⟨hcd, hac.symm, had.symm⟩⟩
      · exact ⟨b, (G.degree_pos_iff_exists_adj b).mpr ⟨a, hab.symm⟩, c, d,
          (cut_adj G b c d).mpr ⟨hcd, hbc.symm, hbd.symm⟩⟩

theorem exists_positive_cut_nonempty (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h : 2 ≤ G.edgeFinset.card) :
    ∃ z : Fin n, 0 < G.degree z ∧
      (G.deleteEdges (G.incidenceSet z)).edgeFinset.Nonempty := by
  classical
  obtain ⟨z, hz, u, v, huv⟩ := exists_positive_cut_edge n G h
  exact ⟨z, hz, s(u, v), by simpa using huv⟩

theorem cut_edge_card (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (z : Fin n) :
    (G.deleteEdges (G.incidenceSet z)).edgeFinset.card + G.degree z = G.edgeFinset.card := by
  classical
  change (G.deleteIncidenceSet z).edgeFinset.card + G.degree z = G.edgeFinset.card
  rw [SimpleGraph.card_edgeFinset_deleteIncidenceSet]
  exact Nat.sub_add_cancel (G.degree_le_card_edgeFinset z)

theorem exists_min_cover (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ S : Finset (Fin n), IsVertexCover G S ∧
      ∀ T : Finset (Fin n), IsVertexCover G T → S.card ≤ T.card := by
  classical
  have hex : ∃ k : ℕ, ∃ S : Finset (Fin n), IsVertexCover G S ∧ S.card = k :=
    ⟨Finset.univ.card, Finset.univ, by intro u v h; simp, rfl⟩
  obtain ⟨S, hS, hSk⟩ := Nat.find_spec hex
  refine ⟨S, hS, ?_⟩
  intro T hT
  have := Nat.find_min' hex (show ∃ S : Finset (Fin n), IsVertexCover G S ∧ S.card = T.card
    from ⟨T, hT, rfl⟩)
  omega

theorem cut_cover_of_cover {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (S : Finset (Fin n)) (hS : IsVertexCover G S) :
    IsVertexCover (G.deleteEdges (G.incidenceSet z)) S := by
  intro u v h
  exact hS u v ((cut_adj G z u v).mp h).1

theorem cover_insert_of_cut_cover {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (S : Finset (Fin n)) (hS : IsVertexCover (G.deleteEdges (G.incidenceSet z)) S) :
    IsVertexCover G (insert z S) := by
  intro u v h
  by_cases hu : u = z
  · exact Or.inl (by simp [hu])
  by_cases hv : v = z
  · exact Or.inr (by simp [hv])
  rcases hS u v ((cut_adj G z u v).mpr ⟨h, hu, hv⟩) with h | h
  · exact Or.inl (Finset.mem_insert_of_mem h)
  · exact Or.inr (Finset.mem_insert_of_mem h)

theorem cut_cover_erase {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (S : Finset (Fin n)) (hS : IsVertexCover (G.deleteEdges (G.incidenceSet z)) S) :
    IsVertexCover (G.deleteEdges (G.incidenceSet z)) (S.erase z) := by
  intro u v h
  have hne := (cut_adj G z u v).mp h
  rcases hS u v h with hu | hv
  · exact Or.inl (Finset.mem_erase.mpr ⟨hne.2.1, hu⟩)
  · exact Or.inr (Finset.mem_erase.mpr ⟨hne.2.2, hv⟩)

theorem min_cover_cut_bounds {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (S T : Finset (Fin n))
    (hS : IsVertexCover (G.deleteEdges (G.incidenceSet z)) S)
    (hSm : ∀ U : Finset (Fin n), IsVertexCover (G.deleteEdges (G.incidenceSet z)) U →
      S.card ≤ U.card)
    (hT : IsVertexCover G T)
    (hTm : ∀ U : Finset (Fin n), IsVertexCover G U → T.card ≤ U.card) :
    S.card ≤ T.card ∧ T.card ≤ S.card + 1 := by
  refine ⟨hSm T (cut_cover_of_cover G z T hT), ?_⟩
  exact (hTm (insert z S) (cover_insert_of_cut_cover G z S hS)).trans
    (Finset.card_insert_le z S)

theorem cut_cover_drop_iff {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (S T : Finset (Fin n))
    (hS : IsVertexCover (G.deleteEdges (G.incidenceSet z)) S)
    (hSm : ∀ U : Finset (Fin n), IsVertexCover (G.deleteEdges (G.incidenceSet z)) U →
      S.card ≤ U.card)
    (hT : IsVertexCover G T)
    (hTm : ∀ U : Finset (Fin n), IsVertexCover G U → T.card ≤ U.card) :
    (∃ U : Finset (Fin n), IsVertexCover (G.deleteEdges (G.incidenceSet z)) U ∧
      ∀ V : Finset (Fin n), IsVertexCover G V → U.card < V.card) ↔
      S.card + 1 = T.card := by
  have hb := min_cover_cut_bounds G z S T hS hSm hT hTm
  constructor
  · rintro ⟨U, hU, hUmin⟩
    have h1 := hSm U hU
    have h2 := hUmin T hT
    omega
  · intro h
    refine ⟨S, hS, ?_⟩
    intro V hV
    have := hTm V hV
    omega


def PeelStatement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v) → PEqualNP.TopForm.NoFourCycle G → 2 ≤ G.edgeFinset.card → ∃ z : Fin n, 0 < G.degree z ∧ ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ PEqualNP.MetaComplexity.circuitFun n D = (fun y : Fin n → Bool => @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a = true ∧ y b = true) (Classical.propDecidable _)) ∧ D.size + G.degree z ≤ C.size ∧ ((∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (G.deleteEdges (G.incidenceSet z)) S ∧ ∀ T : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G T → S.card < T.card) → D.size + G.degree z + 1 ≤ C.size)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem graph_singleton_false {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (i : Fin n) :
    graphFun G ∅ (fun j => decide (j = i)) = false := by
  simp [graphFun]

theorem graph_circuit_size_pos {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hne : G.edgeFinset.Nonempty) (C : Circuit)
    (hfun : circuitFun n C = graphFun G ∅) : 0 < C.size := by
  classical
  by_contra hsize
  have hnil : C.gates = [] := by
    have hh : C.size = 0 := Nat.eq_zero_of_not_pos hsize
    cases he : C.gates with
    | nil => rfl
    | cons a l => simp [Circuit.size, he] at hh
  have hval (x : Fin n → Bool) : circuitFun n C x = (List.ofFn x).getD C.output false := by
    simp [circuitFun, Circuit.eval, Circuit.wires, hnil]
  by_cases ho : C.output < n
  · let i : Fin n := ⟨C.output, ho⟩
    have hh := congrFun hfun (fun j => decide (j = i))
    rw [hval, graph_singleton_false G i] at hh
    simp [List.getD_eq_getElem?_getD, ho, i] at hh
  · obtain ⟨e, he⟩ := hne
    induction e using Sym2.inductionOn with
    | hf a b =>
      have hab : G.Adj a b := by simpa using he
      have hg : graphFun G ∅ (fun _ => true) = true := by
        simpa [graphFun] using (show ∃ u v, G.Adj u v from ⟨a, b, hab⟩)
      have hh := congrFun hfun (fun _ => true)
      rw [hval, hg] at hh
      simp [List.getD_eq_getElem?_getD, ho] at hh

theorem one_edge_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hcard : G.edgeFinset.card = 1) :
    ∃ T : Finset (Fin n), IsVertexCover G T ∧ T.card = 1 := by
  classical
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
  induction e using Sym2.inductionOn with
  | hf a b =>
    refine ⟨{a}, ?_, by simp⟩
    intro u v huv
    have hm : s(u, v) ∈ G.edgeFinset := by simpa using huv
    have heq : s(u, v) = s(a, b) := by simpa [he] using hm
    rcases Sym2.eq_iff.mp heq with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact Or.inl (by simp [hu])
    · exact Or.inr (by simp [hv])

theorem cut_bipartite {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n)
    (hb : ∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v) :
    ∃ c : Fin n → Bool, ∀ u v : Fin n,
      (G.deleteEdges (G.incidenceSet z)).Adj u v → c u ≠ c v := by
  obtain ⟨c, hc⟩ := hb
  exact ⟨c, fun u v h => hc u v ((cut_adj G z u v).mp h).1⟩

theorem cut_no_four_cycle {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (z : Fin n) (h4 : PEqualNP.TopForm.NoFourCycle G) :
    PEqualNP.TopForm.NoFourCycle (G.deleteEdges (G.incidenceSet z)) := by
  classical
  intro a b hab
  apply le_trans (Finset.card_le_card ?_) (h4 a b hab)
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  exact ⟨((cut_adj G z a w).mp hw.1).1, ((cut_adj G z b w).mp hw.2).1⟩

theorem lower_bound_of_peeling (hp : PeelStatement) (n : ℕ) :
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v) →
      PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty →
      ∀ C : Circuit, PEqualNP.TopForm.IsAO2 n C → circuitFun n C = graphFun G ∅ →
      ∃ T : Finset (Fin n), IsVertexCover G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  suffices h : ∀ m : ℕ, ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.edgeFinset.card = m →
      (∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v) →
      PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty →
      ∀ C : Circuit, PEqualNP.TopForm.IsAO2 n C → circuitFun n C = graphFun G ∅ →
      ∃ T : Finset (Fin n), IsVertexCover G T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 by
    intro G _ hb h4 hne C hC hfun
    exact h G.edgeFinset.card G rfl hb h4 hne C hC hfun
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro G _ hm hb h4 hne C hC hfun
    by_cases htwo : 2 ≤ G.edgeFinset.card
    · obtain ⟨z, hz, hpeel⟩ := hp n G hb h4 htwo
      obtain ⟨D, hD, hDfun, hsave, hbonus⟩ := hpeel C hC hfun
      let H := G.deleteEdges (G.incidenceSet z)
      have hDfun' : circuitFun n D = graphFun H ∅ := by
        funext x
        simpa [graphFun, H] using congrFun hDfun x
      have heq : H.edgeFinset.card + G.degree z = G.edgeFinset.card := cut_edge_card n G z
      by_cases hH : H.edgeFinset.Nonempty
      · have hlt : H.edgeFinset.card < m := by omega
        obtain ⟨S, hS, hScost⟩ := ih H.edgeFinset.card hlt H rfl
          (cut_bipartite G z hb) (cut_no_four_cycle G z h4) hH D hD hDfun'
        by_cases hex : ∃ T : Finset (Fin n), IsVertexCover G T ∧ T.card ≤ S.card
        · obtain ⟨T, hT, hTS⟩ := hex
          exact ⟨T, hT, by omega⟩
        · have hdrop : ∀ T : Finset (Fin n), IsVertexCover G T → S.card < T.card := by
            intro T hT
            by_contra hn
            exact hex ⟨T, hT, by omega⟩
          have hmore := hbonus ⟨S, hS, hdrop⟩
          refine ⟨insert z S, cover_insert_of_cut_cover G z S hS, ?_⟩
          have := Finset.card_insert_le z S
          omega
      · have hHe : H.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
        have hcover : IsVertexCover G {z} := by
          intro u v huv
          by_cases hu : u = z
          · exact Or.inl (by simp [hu])
          by_cases hv : v = z
          · exact Or.inr (by simp [hv])
          have hh : H.Adj u v := (cut_adj G z u v).mpr ⟨huv, hu, hv⟩
          have hm : s(u, v) ∈ H.edgeFinset := by simpa using hh
          simp [hHe] at hm
        refine ⟨{z}, hcover, ?_⟩
        have hzero : H.edgeFinset.card = 0 := by simp [hHe]
        simp only [Finset.card_singleton]
        omega
    · have hm1 : G.edgeFinset.card = 1 := by
        have := Finset.card_pos.mpr hne
        omega
      obtain ⟨T, hT, hTc⟩ := one_edge_cover G hm1
      have := graph_circuit_size_pos G hne C hfun
      exact ⟨T, hT, by omega⟩


end PEqualNP.Outside.L_meta_3566
