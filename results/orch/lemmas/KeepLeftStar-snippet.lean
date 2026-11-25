
namespace PEqualNP.Outside.L_meta_2448.keep_left

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def StarAt (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (j : ℕ) : Prop :=
  (∀ u v : Fin n, G.Adj u v → ¬ Owns n C j u v) ∨
    ∃ a : Fin n, ∀ u v : Fin n, G.Adj u v → Owns n C j u v → u = a ∨ v = a

def StarPrefix (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (k : ℕ) : Prop :=
  ∀ j < k, (gateAt C j).op = GateOp.and → StarAt n G C j

lemma starAt_prefix (n : ℕ) (G : SimpleGraph (Fin n)) (pre post : List Gate)
    (output j : ℕ) (hj : j < pre.length) :
    StarAt n G ⟨pre ++ post, output⟩ j ↔ StarAt n G ⟨pre, 0⟩ j := by
  simp only [StarAt, cross.owns_prefix n pre post output j hj]

lemma starPrefix_repair (n : ℕ) (G : SimpleGraph (Fin n)) (pre post : List Gate)
    (s a b output : ℕ) (ha : a < n)
    (hpre : StarPrefix n G (oldCircuit n pre post s a b output) pre.length) :
    StarPrefix n G (newCircuit n pre post s a b output) (pre.length+3) := by
  intro j hj hop
  by_cases hjp : j < pre.length
  · have ho : StarAt n G (oldCircuit n pre post s a b output) j ↔ StarAt n G ⟨pre, 0⟩ j := by
      simpa only [oldCircuit, List.append_assoc] using
        starAt_prefix n G pre ((wide (n+pre.length) s a b).gates ++ post) output j hjp
    have hn : StarAt n G (newCircuit n pre post s a b output) j ↔ StarAt n G ⟨pre, 0⟩ j := by
      simpa only [newCircuit, List.append_assoc] using
        starAt_prefix n G pre ((kept (n+pre.length) s a b).gates ++ post) output j hjp
    have he : gateAt (oldCircuit n pre post s a b output) j =
        gateAt (newCircuit n pre post s a b output) j := by
      simpa only [oldCircuit, newCircuit, List.append_assoc] using
        (cross.gateAt_prefix pre ((wide (n+pre.length) s a b).gates ++ post) output j hjp).trans
          (cross.gateAt_prefix pre ((kept (n+pre.length) s a b).gates ++ post) output j hjp).symm
    exact hn.mpr (ho.mp (hpre j hjp (by rw [he]; exact hop)))
  · have hc : j = pre.length ∨ j = pre.length+1 ∨ j = pre.length+2 := by omega
    rcases hc with rfl | rfl | rfl
    · have hg : gateAt (newCircuit n pre post s a b output) pre.length = ⟨GateOp.or, [s,a]⟩ := by
        simp [newCircuit, kept, gateAt, List.getD_eq_getElem?_getD]
      simp [hg] at hop
    · have hg : gateAt (newCircuit n pre post s a b output) (pre.length+1) = ⟨GateOp.and, [a,b]⟩ := by
        simp [newCircuit, kept, gateAt, List.getD_eq_getElem?_getD]
      right
      refine ⟨⟨a,ha⟩, ?_⟩
      intro u v _ hov
      exact cross.owns_primary_input (newCircuit n pre post s a b output) (pre.length+1)
        ⟨a,ha⟩ (by simp [hg]) hov
    · have hg : gateAt (newCircuit n pre post s a b output) (pre.length+2) = ⟨GateOp.or, [s,n+pre.length+1]⟩ := by
        simp [newCircuit, kept, gateAt, List.getD_eq_getElem?_getD]
      simp [hg] at hop

end PEqualNP.Outside.L_meta_2448.keep_left
