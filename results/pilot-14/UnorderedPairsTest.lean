import TightFormulaTest

namespace PEqualNP.Outside.L_meta_670_aux.UnorderedPairs

open LiveCheck TightFormula

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: xs => (singles xs).map (fun (b,r) => (a,b,r)) ++
      (pairs xs).map (fun (b,c,r) => (b,c,a :: r))

lemma pair_mem {α : Type} {v r : List α} {a b : α}
    (hp : v.Perm (a :: b :: r)) :
    ∃ s, ((a,b,s) ∈ pairs v ∨ (b,a,s) ∈ pairs v) ∧ s.Perm r := by
  classical
  induction v generalizing r with
  | nil => have h := hp.length_eq; simp at h
  | cons x xs ih =>
      by_cases hxa : x = a
      · subst x
        have hx : xs.Perm (b :: r) := List.Perm.cons_inv hp
        obtain ⟨s,hm,hs⟩ := pick_one (hx.mem_iff.mpr (by simp : b ∈ b :: r))
        refine ⟨s,Or.inl ?_,List.Perm.cons_inv (hs.symm.trans hx)⟩
        exact List.mem_append_left _ (List.mem_map.mpr ⟨(b,s),hm,rfl⟩)
      · by_cases hxb : x = b
        · subst x
          have hx : xs.Perm (a :: r) :=
            List.Perm.cons_inv (hp.trans (List.Perm.swap b a r))
          obtain ⟨s,hm,hs⟩ := pick_one (hx.mem_iff.mpr (by simp : a ∈ a :: r))
          refine ⟨s,Or.inr ?_,List.Perm.cons_inv (hs.symm.trans hx)⟩
          exact List.mem_append_left _ (List.mem_map.mpr ⟨(a,s),hm,rfl⟩)
        · have hxr : x ∈ r := by
            have hx := hp.mem_iff.mp (List.mem_cons_self : x ∈ x :: xs)
            simpa only [List.mem_cons,hxa,hxb,false_or] using hx
          obtain ⟨r₀,_,hr⟩ := pick_one hxr
          have hx : xs.Perm (a :: b :: r₀) := by
            apply List.Perm.cons_inv
            exact (hp.trans ((hr.cons b).cons a)).trans
              (((List.Perm.swap x b r₀).cons a).trans (List.Perm.swap x a (b :: r₀)))
          obtain ⟨s,hm,hs⟩ := ih hx
          refine ⟨x :: s,?_,(hs.cons x).trans hr.symm⟩
          rcases hm with hm | hm
          · exact Or.inl (List.mem_append_right _
              (List.mem_map.mpr ⟨(a,b,s),hm,rfl⟩))
          · exact Or.inr (List.mem_append_right _
              (List.mem_map.mpr ⟨(b,a,s),hm,rfl⟩))

lemma and_comm (a b : Sig) : bin false a b = bin false b a := by
  simp [bin,BitVec.and_comm]

lemma ops_swap_mem {a b z : Sig} (h : z ∈ ops a b) : z ∈ ops b a := by
  simp only [ops,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
  rcases h with h | h | h | h
  · exact Or.inl (h.trans (congrArg phase (and_comm a b)))
  · exact Or.inr (Or.inr (Or.inl (h.trans (congrArg phase (and_comm a (neg b))))))
  · exact Or.inr (Or.inl (h.trans (congrArg phase (and_comm (neg a) b))))
  · exact Or.inr (Or.inr (Or.inr (h.trans (congrArg phase (and_comm (neg a) (neg b))))))

def steps (v : List Sig) : List (List Sig) :=
  (pairs v).flatMap fun (a,b,r) => (ops a b).map fun z => z :: r

lemma step_mem {v r : List Sig} {a b z : Sig}
    (hp : v.Perm (a :: b :: r)) (hz : z ∈ ops a b) :
    ∃ w ∈ steps v, w.Perm (z :: r) := by
  obtain ⟨s,hm,hs⟩ := pair_mem hp
  refine ⟨z :: s,?_,hs.cons z⟩
  rcases hm with hm | hm
  · exact List.mem_flatMap.mpr ⟨(a,b,s),hm,List.mem_map.mpr ⟨z,hz,rfl⟩⟩
  · exact List.mem_flatMap.mpr ⟨(b,a,s),hm,List.mem_map.mpr ⟨z,ops_swap_mem hz,rfl⟩⟩

def keepSteps (v : List Sig) : List (List Sig) :=
  (pairs v).flatMap fun (a,b,r) => (ops a b).flatMap fun z =>
    [z :: a :: r,z :: b :: r]

lemma keep_step_mem {v r : List Sig} {a b z : Sig}
    (hp : v.Perm (a :: b :: r)) (hz : z ∈ ops a b) (keep : Bool) :
    ∃ w ∈ keepSteps v, w.Perm (z :: (if keep then a else b) :: r) := by
  obtain ⟨s,hm,hs⟩ := pair_mem hp
  refine ⟨z :: (if keep then a else b) :: s,?_,(hs.cons _).cons z⟩
  rcases hm with hm | hm
  · exact List.mem_flatMap.mpr ⟨(a,b,s),hm,List.mem_flatMap.mpr
      ⟨z,hz,by cases keep <;> simp⟩⟩
  · exact List.mem_flatMap.mpr ⟨(b,a,s),hm,List.mem_flatMap.mpr
      ⟨z,ops_swap_mem hz,by cases keep <;> simp⟩⟩

end PEqualNP.Outside.L_meta_670_aux.UnorderedPairs

namespace PEqualNP.Outside.L_meta_670_aux.UnorderedPairs
open LiveCheck
example : (pairs ([1,1,2] : List Nat)).length = 3 := by decide +kernel
example : (steps [raw0,raw1,raw2]).length = 12 := by decide +kernel
example : (keepSteps [raw0,raw1,raw2]).length = 24 := by decide +kernel
#print axioms pair_mem
#print axioms step_mem
#print axioms keep_step_mem
end PEqualNP.Outside.L_meta_670_aux.UnorderedPairs
