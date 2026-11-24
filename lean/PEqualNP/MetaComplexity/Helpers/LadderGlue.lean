import PEqualNP.MetaComplexity.Helpers.LadderPlan
import PEqualNP.MetaComplexity.Helpers.LadderDual
import PEqualNP.MetaComplexity.Helpers.LadderFreeze
import PEqualNP.MetaComplexity.Helpers.LadderRun

/-!
# The ladder (row L-meta-1049): the glue

Unverified, a conjecture until a checker accepts a row. The five Props of the plan module
(`lp_PFreeze`, `lp_PConvex`, `lp_PDual`, `lp_PRun`, `lp_PCost`) from the pieces built in
`LadderFreeze`, `LadderDual` and `LadderRun`. The gaps are phrasing: `Circuit.eval` is the
wire list read at the output, and the wire list does not depend on the output; `Disjoint`
against an empty intersection; the run argument's break set is taken from the proof of
`lr_runs_le`.
-/

namespace PEqualNP.MetaComplexity.Ladder

open PEqualNP.CircuitLowerBounds

/-- The wire list of a circuit does not depend on its output index. -/
theorem lg_wires_output (gates : List Gate) (o o' : ℕ) (x : List Bool) :
    Circuit.wires ⟨gates, o⟩ x = Circuit.wires ⟨gates, o'⟩ x := rfl

/-- The value at wire `o` is the wire list read at `o`. -/
theorem lg_eval_getD (gates : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gates, o⟩ x = (Circuit.wires ⟨gates, 0⟩ x).getD o false := rfl

theorem lg_freeze : lp_PFreeze := by
  intro n t gates ι e hops hcov
  obtain ⟨F, hl, hF, hw⟩ := lf_freeze n t gates ι e hops hcov
  refine ⟨F, hl, hF, ?_⟩
  intro x hP o
  have hP' : ∀ j : Fin t, (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (ι j : ℕ)) false
      = e j := fun j => by rw [← lg_eval_getD]; exact hP j
  unfold Circuit.eval
  rw [hw x hP' o o]

theorem lg_convex : lp_PConvex := by
  intro n t gates ι e hops hcov a x b hax hxb hPa hPb j
  rw [lg_eval_getD]
  exact lf_convex n t gates ι e hops hcov a x b hax hxb
    (fun j => by rw [← lg_eval_getD]; exact hPa j)
    (fun j => by rw [← lg_eval_getD]; exact hPb j) j

theorem lg_dual : lp_PDual := by
  intro n g hg
  exact ⟨ld_dual n g, ld_dual_spec n g hg⟩

theorem lg_run : lp_PRun := by
  intro H t f hf
  classical
  set P : Finset ℕ := (Finset.range H).filter (fun u => 1 ≤ u ∧ f u ≠ f (u - 1)) with hP
  have hrun : ∀ u v, u ≤ v → v < H → (∀ w ∈ P, ¬ (u < w ∧ w ≤ v)) → f u = f v := by
    intro u v huv
    induction v, huv using Nat.le_induction with
    | base => intro _ _; rfl
    | succ v huv ih =>
      intro hvM hno
      have h1 : f (v + 1) = f v := by
        by_contra hne
        exact hno (v + 1)
          (Finset.mem_filter.2 ⟨Finset.mem_range.2 hvM, by omega, by simpa using hne⟩)
          ⟨by omega, le_rfl⟩
      rw [h1]
      exact ih (by omega) (fun w hw hw' => hno w hw ⟨hw'.1, by omega⟩)
  have hcard : P.card + 1 ≤ 2 ^ t := by
    have h0 : (0 : ℕ) ∉ P := by simp [hP]
    have key : ∀ u u', u' ∈ P → u < u' → f u ≠ f u' := by
      intro u u' hu' hlt heq
      obtain ⟨hu'M, _, hne⟩ := Finset.mem_filter.1 hu'
      apply hne
      have := hf u (u' - 1) u' (by omega) (by omega) (Finset.mem_range.1 hu'M) heq
      rw [this, heq]
    have hinj : Set.InjOn f (insert 0 P : Finset ℕ) := by
      intro u hu u' hu' heq
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hu hu'
      rcases lt_trichotomy u u' with h | h | h
      · exfalso
        rcases hu' with rfl | hu'
        · omega
        · exact key u u' hu' h heq
      · exact h
      · exfalso
        rcases hu with rfl | hu
        · omega
        · exact key u' u hu h heq.symm
    have := Finset.card_le_card_of_injOn f (t := (Finset.univ : Finset (Fin t → Bool)))
      (fun a _ => by simp) hinj
    rw [Finset.card_insert_of_notMem h0, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin] at this
    exact this
  exact ⟨hcard, hrun⟩

theorem lg_cost : lp_PCost := by
  intro h q n S K _ hq hn hS hSS hpts hKc hKm hKn uv h12 h2lt
  have := lr_chain_cost h q n S K hq hn hS hSS hpts hKc hKm hKn uv.1 uv.2 h12 h2lt
  unfold lr_level at this
  rw [← this]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro w _
  rw [Finset.disjoint_iff_inter_eq_empty]

end PEqualNP.MetaComplexity.Ladder
