import RepairAssembly
import EdgePruning

namespace PEqualNP.Outside.L_meta_2448_aux.GraphRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2448_aux.ReaderDeletion
open PEqualNP.Outside.L_meta_2448_aux.RepairAssembly
open PEqualNP.Outside.L_meta_2448_aux.LinearCleanup
open PEqualNP.Outside.L_meta_2448_aux.TwoCenterRepair
open PEqualNP.Outside.L_meta_2448_aux.EdgePruning

theorem graph_repair_circuit (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (pre post : List Gate) (g : Gate) (a b : ℕ)
    (A B : Set (Fin n)) (c d : Fin n)
    (hC : C.gates = pre ++ g :: post) (hmono : Monotone2 C)
    (ha : a < n + pre.length) (hb : b < n + pre.length)
    (htri : ∀ u v w, G.Adj u v → G.Adj v w → ¬G.Adj w u)
    (hfour : ∀ u v w z, G.Adj u v → G.Adj v w → G.Adj w z →
      G.Adj z u → u = w ∨ v = z)
    (hc : c ∈ Centers G A B) (hd : d ∈ Centers G B A)
    (hA : ∀ x : Fin n → Bool, (wiresFrom pre (List.ofFn x)).getD a false = true ↔
      Hit A (fun v => x v = true))
    (hB : ∀ x : Fin n → Bool, (wiresFrom pre (List.ofFn x)).getD b false = true ↔
      Hit B (fun v => x v = true))
    (hexact : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x)
    (hRmono : ∀ x y : Fin n → Bool, (∀ v, x v = true → y v = true) →
      forcedEval n pre post C.output x = true → forcedEval n pre post C.output y = true)
    (hRle : ∀ x : Fin n → Bool, forcedEval n pre post C.output x = true →
      C.eval (List.ofFn x) = true)
    (hcut : ∀ x : Fin n → Bool, ¬Product A B (fun v => x v = true) →
      forcedEval n pre post C.output x = C.eval (List.ofFn x)) :
    ∃ E : Circuit, Monotone2 E ∧
      E.size + readerCount (n + pre.length) post ≤ C.size + 3 ∧
      ∀ x : Fin n → Bool, E.eval (List.ofFn x) = graphFun G ∅ x := by
  have hzero : forcedEval n pre post C.output (fun _ => false) = false := by
    cases hh : forcedEval n pre post C.output (fun _ => false) with
    | false => rfl
    | true =>
      have hh' := hRle _ hh
      rw [hexact] at hh'
      obtain ⟨u, v, _, hu, _⟩ := (graph_true_iff n G _).mp hh'
      contradiction
  have raw (v : Fin n) (x : Fin n → Bool) :
      (wiresFrom pre (List.ofFn x)).getD v.val false = x v := by
    rw [getD_wiresFrom pre _ _ (by simp)]
    simp
  have hdis := disjoint_of_centers G A B c d htri hc hd
  have hrepair (x : Fin n → Bool) : C.eval (List.ofFn x) =
      (forcedEval n pre post C.output x ||
        (((wiresFrom pre (List.ofFn x)).getD c.val false &&
          (wiresFrom pre (List.ofFn x)).getD b false) ||
         ((wiresFrom pre (List.ofFn x)).getD d.val false &&
          (wiresFrom pre (List.ofFn x)).getD a false))) := by
    apply Bool.eq_iff_iff.mpr
    rw [Bool.or_eq_true, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      raw c x, raw d x, hA x, hB x]
    change C.eval (List.ofFn x) = true ↔
      forcedEval n pre post C.output x = true ∨ Repair A B c d (fun v => x v = true)
    constructor
    · intro hx
      rw [hexact] at hx
      obtain ⟨s, t, hst, hsx, htx⟩ := (graph_true_iff n G x).mp hx
      have hp : C.eval (List.ofFn (pairInput s t)) = true := by
        rw [hexact]
        exact (graph_true_iff n G _).mpr
          ⟨s, t, hst, by simp [pairInput], by simp [pairInput]⟩
      by_cases hg : Product A B (fun v => pairInput s t v = true)
      · right
        have hpair : (fun v => pairInput s t v = true) = (fun v => v = s ∨ v = t) := by
          funext v
          simp [pairInput]
        rw [hpair] at hg
        exact repair_mono A B c d _ _ (by
          intro v hv
          rcases hv with rfl | rfl
          · exact hsx
          · exact htx)
          ((repair_preserves_edges G A B c d hdis hfour hc hd s t hst).mp hg)
      · left
        have hr : forcedEval n pre post C.output (pairInput s t) = true := by
          rw [hcut _ hg]
          exact hp
        exact hRmono _ x (pair_below n x s t hsx htx) hr
    · rintro (hr | hh)
      · exact hRle x hr
      · rw [hexact]
        exact (graph_true_iff n G x).mpr (repair_sound G A B c d hc hd _ hh)
  obtain ⟨E, hE, hs, he⟩ := repair_circuit n C pre post g a b c.val d.val hC hmono
    ha hb (by omega) (by omega) hzero hrepair
  exact ⟨E, hE, hs, fun x => (he x).trans (hexact x)⟩

end PEqualNP.Outside.L_meta_2448_aux.GraphRepair
