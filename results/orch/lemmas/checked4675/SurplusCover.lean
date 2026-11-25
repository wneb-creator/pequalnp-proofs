import PetersenSurplus

namespace PEqualNP.Outside.L_meta_4675_aux.SurplusCover

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2590_aux.Surplus

lemma dag_cover {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) :
    (∀ u v, G u v → u ∈ eligSet n D ∨ v ∈ eligSet n D) ∧
      n + (eligSet n D).card ≤ D.length + 1 := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch hG h.1 hC
  have hbnd := elig_le_Bplus h.1 b hb
  have htotal := Bplus_le_total n D
  have hsize := surplus_identity h
  exact ⟨fun u v huv => sem_elig_cover hG h hC huv, by omega⟩

lemma circuit_cover {n : ℕ} (hn : 0 < n) (G : Fin n → Fin n → Prop)
    (hG : sem_Gr G) (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ sem_Edge G x) :
    ∃ S : Finset (Fin n), (∀ u v, G u v → u ∈ S ∨ v ∈ S) ∧
      n + S.card ≤ C.size + 1 := by
  have hsingle (i : Fin n) : C.eval (List.ofFn (single i)) = false := by
    cases he : C.eval (List.ofFn (single i))
    · rfl
    · exact (sem_single_no_edge hG i ((hC _).mp he)).elim
  have htwo {i a : Fin n} (hia : G i a) : C.eval (List.ofFn (sem_two i a)) = true :=
    (hC _).mpr (sem_two_edge hia)
  have hnc : ∀ b : Bool, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ b := by
    let i : Fin n := ⟨0, hn⟩
    obtain ⟨a, hia, -⟩ := hG.2.2.2 i i
    intro b
    cases b
    · exact ⟨sem_two i a, by rw [htwo hia]; decide⟩
    · exact ⟨single i, by rw [hsingle i]; decide⟩
  have hnp : ∀ i : Fin n, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ x i := by
    intro i
    exact ⟨single i, by rw [hsingle i]; simp [single]⟩
  have hess : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ C.eval (List.ofFn x) ≠ C.eval (List.ofFn y) := by
    intro i
    obtain ⟨a, hia, -⟩ := hG.2.2.2 i i
    refine ⟨single a, sem_two i a, ?_, ?_⟩
    · intro k hki
      simp [single, sem_two, hki]
    · rw [hsingle a, htwo hia]
      decide
  obtain ⟨D, hD, hlen, he⟩ := normalize_strictLive C hmono hnc hnp hess
  have hcomp : sem_Comp n G D := by
    intro x
    rw [he x]
    exact hC x
  obtain ⟨hcover, hsize⟩ := dag_cover hG hD hcomp
  exact ⟨eligSet n D, hcover, by omega⟩

lemma circuit_cover_of_edge_count {n : ℕ} (hn : 0 < n)
    (G : Fin n → Fin n → Prop) (hG : sem_Gr G) (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ sem_Edge G x)
    (m : ℕ) (hm : m ≤ n) :
    ∃ S : Finset (Fin n), (∀ u v, G u v → u ∈ S ∨ v ∈ S) ∧
      m + S.card ≤ C.size + 1 := by
  obtain ⟨S, hc, hs⟩ := circuit_cover hn G hG C hmono hC
  exact ⟨S, hc, by omega⟩

end PEqualNP.Outside.L_meta_4675_aux.SurplusCover
