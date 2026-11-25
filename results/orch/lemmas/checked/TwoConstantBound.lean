import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2592
abbrev Wire (R : Type) := R → Bool
def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum
lemma mass_cons {R} (a : Wire R) (xs : List (Wire R)) : mass (a::xs)=cost a+mass xs := by simp [mass]
lemma two_constant_bound {R Sig : Type} [DecidableEq Sig] {U : Finset Sig} {a c : Sig}
    {k : Nat} (proj : Sig → Wire R) (retained : a ∈ U)
    (fresh : c ∉ insert a U) (ac : Constant (proj a)) (cc : Constant (proj c))
    (bound : ∀ (front : List Sig), front.Nodup → front.toFinset=insert c U →
      15 + mass (front.map proj) ≤ k) : 17 ≤ k := by
  classical
  have hne : c ≠ a := fun h => fresh (by simp [h])
  have hn : c ∉ U := fun h => fresh (Finset.mem_insert_of_mem h)
  let front := c :: a :: (U.erase a).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, Finset.nodup_toList _⟩⟩
    · intro hc
      rcases List.mem_cons.mp hc with he | hc
      · exact hne he
      · exact hn (Finset.mem_erase.mp (Finset.mem_toList.mp hc)).2
    · simp
  have eqS : front.toFinset = insert c U := by
    simp only [front, List.toFinset_cons, Finset.toList_toFinset, Finset.insert_erase retained]
  have need := bound front nd eqS
  have charge : 2 ≤ mass (front.map proj) := by
    simp only [front, List.map_cons, mass_cons, cost, if_pos ac, if_pos cc]
    omega
  omega
end PEqualNP.Outside.L_meta_2592
