namespace PEqualNP.Outside.L_meta_2592.Signed

open PEqualNP.Outside.L_meta_5236

lemma reach_u2_list {R : Type} (assign : R → Fin 10 → Bool)
    (roots : List (Wire R))
    (inputSupply : ∀ i : Fin 10, Available true roots (fun r => assign r i))
    (gs : List U2Gate) :
    ∃ bank : List (Wire R), Reach true roots gs.length bank ∧
      ∀ i : ℕ, Available true bank (fun r => u2Val gs (assign r) i) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨roots, Reach.start, ?_⟩
    intro i
    by_cases hi : i < 10
    · simpa only [u2Val_input _ _ i hi] using inputSupply ⟨i, hi⟩
    · apply Or.inr ∘ Or.inl
      refine ⟨false, ?_⟩
      funext r
      exact List.getD_eq_default _ _ (by simp [u2Wires]; omega)
  | append_singleton gs g ih =>
    obtain ⟨bank, history, available⟩ := ih
    let a : Wire R := fun r => u2Val gs (assign r) g.a != g.pa
    let b : Wire R := fun r => u2Val gs (assign r) g.b != g.pb
    have ha : Available true bank a := by
      cases hp : g.pa
      · simpa [a, hp] using available g.a
      · change Available true bank (fun r => u2Val gs (assign r) g.a != g.pa)
        rw [hp]
        change Available true bank (PEqualNP.Outside.L_meta_5236.inv (fun r => u2Val gs (assign r) g.a))
        exact PEqualNP.Outside.L_meta_5236.avail_inv rfl (available g.a)
    have hb : Available true bank b := by
      cases hp : g.pb
      · simpa [b, hp] using available g.b
      · change Available true bank (fun r => u2Val gs (assign r) g.b != g.pb)
        rw [hp]
        change Available true bank (PEqualNP.Outside.L_meta_5236.inv (fun r => u2Val gs (assign r) g.b))
        exact PEqualNP.Outside.L_meta_5236.avail_inv rfl (available g.b)
    refine ⟨combine false a b :: bank, ?_, ?_⟩
    · simpa using Reach.two false history ha hb
    · intro i
      by_cases hi : i < 10 + gs.length
      · have eq : (fun r => u2Val (gs ++ [g]) (assign r) i) =
            (fun r => u2Val gs (assign r) i) := by
          funext r
          unfold u2Val
          rw [u2Wires_snoc]
          exact getD_snoc_lt _ _ _ i (by rw [u2Wires_length, List.length_ofFn]; exact hi)
        rw [eq]
        exact available_cons _ (available i)
      · by_cases heq : i = 10 + gs.length
        · have eq : (fun r => u2Val (gs ++ [g]) (assign r) i) = combine false a b := by
            funext r
            unfold u2Val
            rw [u2Wires_snoc]
            exact getD_snoc_eq' _ _ _ i (by rw [u2Wires_length, List.length_ofFn]; exact heq)
          rw [eq]
          exact Or.inl List.mem_cons_self
        · apply Or.inr ∘ Or.inl
          refine ⟨false, ?_⟩
          funext r
          exact List.getD_eq_default _ _ (by rw [u2Wires_length, List.length_ofFn]; simp; omega)

lemma reach_u2 {R : Type} (assign : R → Fin 10 → Bool)
    (roots : List (Wire R))
    (inputSupply : ∀ i : Fin 10, Available true roots (fun r => assign r i))
    (D : U2Circuit) :
    ∃ bank : List (Wire R), Reach true roots D.gates.length bank ∧
      Available true bank (fun r => u2Eval D (assign r)) := by
  obtain ⟨bank, history, available⟩ := reach_u2_list assign roots inputSupply D.gates
  refine ⟨bank, history, ?_⟩
  cases hout : D.out with
  | inl c =>
    exact Or.inr (Or.inl ⟨c, by simp [u2Eval, hout, refEval]⟩)
  | inr wire =>
    obtain ⟨i, flip⟩ := wire
    cases flip
    · simpa [u2Eval, hout, refEval, u2Val] using available i
    · change Available true bank (fun r => refEval (u2Wires D.gates (List.ofFn (assign r))) D.out)
      rw [hout]
      change Available true bank (PEqualNP.Outside.L_meta_5236.inv (fun r => u2Val D.gates (assign r) i))
      exact PEqualNP.Outside.L_meta_5236.avail_inv rfl (available i)

end PEqualNP.Outside.L_meta_2592.Signed
