import PEqualNP.MetaComplexity.Helpers.Deg2Count
import PEqualNP.MetaComplexity.Helpers.Deg2E0
import PEqualNP.MetaComplexity.Helpers.Deg2Alpha
import PEqualNP.MetaComplexity.Helpers.Deg2Beta
import PEqualNP.MetaComplexity.Helpers.Deg2S0Form
import PEqualNP.MetaComplexity.Helpers.Deg2S0Cover

/-!
# The degree-two count for a circuit below the incidence function

`assembly_below`: the count of L-meta-649 with "computes the incidence function" weakened to "below
it", taken on the incident pairs the circuit accepts. Conjecture until checked.
-/

namespace PEqualNP.MetaComplexity.Deg2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Deg2.Api

/-- Line-degree at most 2, below: on an incidence between N points and N lines with no two points
on two common lines, a circuit of AND and OR gates of fan-in at most two and line-degree at most 2
that is true only at inputs carrying an incident pair accepts at most 48 times its size plus 2 N
incident pairs. -/
theorem assembly_below : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.CircuitLowerBounds.HasLineDegree (N + N) (Finset.Ico N (N + N)) C 2 → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true → ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2)) = true)).card ≤ 48 * C.size + 2 * N := by
  classical
  intro N I _ C hI hmono hdeg hfun
  have hI' : NoRect I := hI
  let D : Dag N := ofCircuit N C
  have hwf : D.WF := card03b_wf C
  have hsize : D.size = C.size := by simp [D, Dag.size, ofCircuit, Circuit.size]
  have hfn : ∀ z, D.fn z = circuitFun (N + N) C z := by
    intro z
    show (ofCircuit N C).val z C.output = C.eval (List.ofFn z)
    rw [Bridge.card03c_val C hmono z C.output]
    rfl
  have hcomp : Below I D.fn := by
    intro z hz
    rw [hfn] at hz
    exact hfun z hz
  have hd : D.deg D.out ≤ 2 := le_trans (Bridge.card03d_deg C hmono C.output) hdeg
  obtain ⟨D', hwf', hs', hc', hd', hcl', hup⟩ := card04_clean_below I D hwf hcomp hd
  have hcov := card17_cover_below I D' hwf' hc' hd' hcl'
  obtain ⟨F, W, R, hsound, hmk, hF⟩ := card16_form_below I D' hwf' hc' hd'
  have h14' := card14_of card10_e0 card12_alpha card13_beta I hI' F W R hsound
  have hW : W.card ≤ N := by
    simpa using Finset.card_le_univ W
  have hp := card08_pinned I hI' D'
  have hsv := card17s_served I D'
  have h7 : (D'.fSet I D'.cone 2).card ≤ 8 * D'.X.card :=
    card07_two_line I hI' D' D'.cone (api_coneOf_down D' {D'.out})
  have hcl := api_classes_card D'
  have hao := api_andor_card D'
  have hE : Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2 ∧
      circuitFun (N + N) C
        (fun k => decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2)) = true) ⊆
      D'.pinned I ∪ D'.served I ∪ D'.fSet I D'.cone 2 ∪ F.countedEdges W R := by
    intro e he
    obtain ⟨he', hacc⟩ := (Finset.mem_filter.1 he).2
    have hacc' : D'.fn (ep e.1 e.2) = true := by
      apply hup
      rw [hfn, cv_ep_eq]
      exact hacc
    have h := hcov e.1 e.2 he' hacc'
    simp only [Finset.mem_union] at h ⊢
    rcases h with ((h | h) | h) | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr (hmk h)
  have hU := Finset.card_le_card hE
  have hU1 := Finset.card_union_le (D'.pinned I ∪ D'.served I ∪ D'.fSet I D'.cone 2)
    (F.countedEdges W R)
  have hU2 := Finset.card_union_le (D'.pinned I ∪ D'.served I) (D'.fSet I D'.cone 2)
  have hU3 := Finset.card_union_le (D'.pinned I) (D'.served I)
  omega

end PEqualNP.MetaComplexity.Deg2
