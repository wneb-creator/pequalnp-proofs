import ReaderRepairCount

namespace PEqualNP.Outside.L_meta_2448_aux.TracedRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2448_aux.ReaderDeletion
open PEqualNP.Outside.L_meta_2448_aux.ReaderDeletionCount
open PEqualNP.Outside.L_meta_2448_aux.RepairAssembly
open PEqualNP.Outside.L_meta_2448_aux.ReaderRepairCount

theorem deletion_traced (n : ℕ) (pre post : List Gate) (out : ℕ)
    (hpre : ∀ g ∈ pre, MonoGate g) (hpost : ∀ g ∈ post, MonoGate g)
    (hzero : forcedEval n pre post out (fun _ => false) = false) :
    ∃ D : Circuit, Monotone2 D ∧ D.gates = (lowered n pre post).2 ∧
      D.size + readerCount (n + pre.length) post + 1 ≤ pre.length + 1 + post.length ∧
      (∃ tail, D.gates = pre ++ tail) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = forcedEval n pre post out x := by
  let acc := lowered n pre post
  have hM : ∀ g ∈ acc.2, MonoGate g := elim_mono n post (seed n pre) hpost hpre
  have hlen := lowered_size n pre post hpost
  have hp : ∃ tail, acc.2 = pre ++ tail := elim_preserves_prefix n post (seed n pre)
  have hval := lowered_correct n pre post out hpost
  cases hs : acc.1.getD out (Sum.inl false) with
  | inl b =>
    have hb : b = false := by
      have h := (hval (fun _ => false)).2
      change (acc.1.getD out (Sum.inl false)).val _ = _ at h
      rw [hs] at h
      exact h.trans hzero
    subst b
    refine ⟨⟨acc.2, n + acc.2.length⟩, hM, rfl, hlen, hp, ?_⟩
    intro x
    have h := (hval x).2
    change (acc.1.getD out (Sum.inl false)).val _ = _ at h
    rw [hs] at h
    change (wiresFrom acc.2 (List.ofFn x)).getD (n + acc.2.length) false = _
    rw [List.getD_eq_default _ _ (by rw [length_wiresFrom, List.length_ofFn])]
    exact h
  | inr w =>
    refine ⟨⟨acc.2, w⟩, hM, rfl, hlen, hp, ?_⟩
    intro x
    have h := (hval x).2
    change (acc.1.getD out (Sum.inl false)).val _ = _ at h
    rw [hs] at h
    exact h

theorem repair_with_count {I : Type} (s : Finset I) (n : ℕ) (C : Circuit)
    (pre post : List Gate) (g : Gate) (a b c d : ℕ)
    (hC : C.gates = pre ++ g :: post) (hmono : Monotone2 C)
    (ha : a < n + pre.length) (hb : b < n + pre.length)
    (hc : c < n + pre.length) (hd : d < n + pre.length)
    (hzero : forcedEval n pre post C.output (fun _ => false) = false)
    (hrepair : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      (forcedEval n pre post C.output x ||
        (((wiresFrom pre (List.ofFn x)).getD c false &&
          (wiresFrom pre (List.ofFn x)).getD b false) ||
         ((wiresFrom pre (List.ofFn x)).getD d false &&
          (wiresFrom pre (List.ofFn x)).getD a false))))
    (inputs : I → Fin n → Bool)
    (hU : ∀ i ∈ s, ((wiresFrom pre (List.ofFn (inputs i))).getD c false &&
      (wiresFrom pre (List.ofFn (inputs i))).getD b false) = false)
    (hV : ∀ i ∈ s, ((wiresFrom pre (List.ofFn (inputs i))).getD d false &&
      (wiresFrom pre (List.ofFn (inputs i))).getD a false) = false)
    (j : I) (hj : j ∈ s)
    (hg : contribution g (wiresFrom pre (List.ofFn (inputs j))) = 1) :
    ∃ E : Circuit, Monotone2 E ∧
      E.size + readerCount (n + pre.length) post ≤ C.size + 3 ∧
      (∀ x : Fin n → Bool, E.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      (∑ i ∈ s, count E.gates (List.ofFn (inputs i))) <
        ∑ i ∈ s, count C.gates (List.ofFn (inputs i)) := by
  have hpre : ∀ h ∈ pre, MonoGate h := by
    intro h hh
    exact hmono h (hC ▸ List.mem_append_left _ hh)
  have hpost : ∀ h ∈ post, MonoGate h := by
    intro h hh
    exact hmono h (hC ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hh))
  obtain ⟨D, hD, htrace, hsize, ⟨tail, htail⟩, heval⟩ :=
    deletion_traced n pre post C.output hpre hpost hzero
  have hp : pre.length ≤ D.size := by simp [Circuit.size, htail]
  have hlen : C.size = pre.length + 1 + post.length := by
    simp [Circuit.size, hC]
    omega
  have hU' : ∀ i ∈ s, ((D.wires (List.ofFn (inputs i))).getD c false &&
      (D.wires (List.ofFn (inputs i))).getD b false) = false := by
    intro i hi
    rw [prefix_wire n D pre tail htail c hc (inputs i),
      prefix_wire n D pre tail htail b hb (inputs i)]
    exact hU i hi
  have hV' : ∀ i ∈ s, ((D.wires (List.ofFn (inputs i))).getD d false &&
      (D.wires (List.ofFn (inputs i))).getD a false) = false := by
    intro i hi
    rw [prefix_wire n D pre tail htail d hd (inputs i),
      prefix_wire n D pre tail htail a ha (inputs i)]
    exact hV i hi
  have hcount := weighted_repair_count_lt s n pre post g hpost D htrace
    a b c d (by omega) (by omega) inputs hU' hV' j hj hg
  rw [← hC] at hcount
  refine ⟨attach n D a b c d, attach_mono n D a b c d hD, ?_, ?_, hcount⟩
  · rw [attach_size]
    omega
  · intro x
    rw [attach_eval n D a b c d (by omega) (by omega) (by omega) (by omega), heval x]
    rw [prefix_wire n D pre tail htail c hc x, prefix_wire n D pre tail htail b hb x,
      prefix_wire n D pre tail htail d hd x, prefix_wire n D pre tail htail a ha x]
    exact (hrepair x).symm

end PEqualNP.Outside.L_meta_2448_aux.TracedRepair
