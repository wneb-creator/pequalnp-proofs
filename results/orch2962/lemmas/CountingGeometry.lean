import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2962_aux.CountingGeometry

/-- A pair of distinct endpoints has at most one common middle vertex. -/
theorem unique_middle {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (no_four : PEqualNP.TopForm.NoFourCycle G) (y w z z' : Fin n)
    (different : y ≠ w) (yz : G.Adj y z) (wz : G.Adj w z)
    (yz' : G.Adj y z') (wz' : G.Adj w z') : z = z' := by
  classical
  by_contra distinct
  have small := no_four y w different
  have subset : ({z, z'} : Finset (Fin n)) ⊆
      Finset.univ.filter (fun t => G.Adj y t ∧ G.Adj w t) := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, yz, wz⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, yz', wz'⟩
  have large := Finset.card_le_card subset
  rw [Finset.card_pair distinct] at large
  omega

/-- Shared endpoint-pair clauses in two path gadgets force two shared edges. -/
theorem two_path_edges_shared {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (no_four : PEqualNP.TopForm.NoFourCycle G) (y w z z' : Fin n)
    (different : y ≠ w) (yz : G.Adj y z) (wz : G.Adj w z)
    (yz' : G.Adj y z') (wz' : G.Adj w z')
    (D D' : Finset (Sym2 (Fin n)))
    (hy : s(y, z) ∈ D) (hw : s(w, z) ∈ D)
    (hy' : s(y, z') ∈ D') (hw' : s(w, z') ∈ D') :
    2 ≤ (D ∩ D').card := by
  have middle := unique_middle G no_four y w z z' different yz wz yz' wz'
  subst z'
  have edges_different : s(y, z) ≠ s(w, z) := by
    intro equal
    rcases Sym2.eq_iff.mp equal with ⟨h, _⟩ | ⟨h, h'⟩
    · exact different h
    · exact different (h.trans h')
  have subset : ({s(y, z), s(w, z)} : Finset (Sym2 (Fin n))) ⊆ D ∩ D' := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hy, hy'⟩
    · exact Finset.mem_inter.mpr ⟨hw, hw'⟩
  have bound := Finset.card_le_card subset
  simpa only [Finset.card_pair edges_different] using bound

/-- A common edge cannot be extended through the same third vertex on both ends. -/
theorem no_center_flip {n : ℕ} (G : SimpleGraph (Fin n)) (s : Fin n → Bool)
    (bipartite : ∀ u v, G.Adj u v → s u ≠ s v)
    (x y z : Fin n) (xy : G.Adj x y) (yz : G.Adj y z) (xz : G.Adj x z) : False := by
  have hxy := bipartite x y xy
  have hyz := bipartite y z yz
  have hxz := bipartite x z xz
  cases hx : s x <;> cases hy : s y <;> cases hz : s z <;> simp_all

end PEqualNP.Outside.L_meta_2962_aux.CountingGeometry
