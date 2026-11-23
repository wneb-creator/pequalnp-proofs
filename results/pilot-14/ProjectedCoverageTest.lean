import DynamicFastBase
namespace PEqualNP.Outside.L_meta_670_aux.Base1007
lemma sep_unary (t : Nat) (a : Sig) (i : Nat)
    (h : (sep (decide (0<t)) (neg a)).getLsbD i = true) :
    (sep true a).getLsbD i = true := by
  by_cases hi : i < 252
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 252 ≤ i)] at h

lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 252
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 252 ≤ i)] at h

lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 252)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).getLsbD i = true ↔ ∃ a ∈ v, (sep d a).getLsbD i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih => simp only [unionSep,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp] <;> aesop


end PEqualNP.Outside.L_meta_670_aux.Base1007
namespace PEqualNP.Outside.L_meta_670_aux.ProjectedCoverage

variable {p : LiveCheck.Sig → Base1007.Sig}
variable (pt : p LiveCheck.target = Base1007.target)
variable (pn : ∀ a, p (LiveCheck.neg a) = Base1007.neg (p a))
variable (pb : ∀ d a b, p (LiveCheck.bin d a b) = Base1007.bin d (p a) (p b))

include pt pn pb

lemma projected_sep {k t : Nat} {S : Finset LiveCheck.Sig}
    (h : LiveCheck.Live k t S) (i : Nat) (hi : i < 252) :
    ∃ a ∈ S, (Base1007.sep (decide (0 < t)) (p a)).getLsbD i = true := by
  induction h with
  | stop =>
    refine ⟨LiveCheck.target,by simp,?_⟩
    rw [pt]
    change (BitVec.allOnes 252 &&& ~~~(0 : Base1007.B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 252)] <;>
      simp [hi]
  | @unary k t U a ha hf tail ih =>
    obtain ⟨x,hx,hs⟩ := ih
    simp only [Nat.zero_lt_succ,decide_true]
    rcases Finset.mem_insert.mp hx with hx | hx
    · subst x
      refine ⟨a,Finset.mem_insert_self _ _,?_⟩
      apply Base1007.sep_unary t (p a) i
      simpa only [pn] using hs
    · exact ⟨x,Finset.mem_insert_of_mem hx,Base1007.sep_weaken t (p x) i hi hs⟩
  | @binary k t U a b d ha hb hab hf tail ih =>
    obtain ⟨x,hx,hs⟩ := ih
    rcases Finset.mem_insert.mp hx with hx | hx
    · subst x
      have hs' : (Base1007.sep (decide (0 < t)) (Base1007.bin d (p a) (p b))).getLsbD i = true := by
        simpa only [pb] using hs
      rcases Base1007.sep_binary (decide (0 < t)) d (p a) (p b) i hs' with h | h
      · exact ⟨a,Finset.mem_insert_self _ _,h⟩
      · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx),hs⟩

lemma projected_cover {k t : Nat} {S : Finset LiveCheck.Sig} {v : List LiveCheck.Sig}
    (h : LiveCheck.Live k t S) (he : v.toFinset = S) :
    Base1007.unionSep (decide (0 < t)) (v.map p) = Base1007.top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,ha,hs⟩ := projected_sep pt pn pb h i hi
  have hm : p a ∈ v.map p := List.mem_map.mpr ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),rfl⟩
  simpa only [Base1007.top,BitVec.getLsbD_allOnes,hi,decide_true] using
    (Base1007.mem_unionSep _ _ _).2 ⟨p a,hm,hs⟩

lemma projected_xor_cover {k t : Nat} {S : Finset LiveCheck.Sig} {v : List LiveCheck.Sig}
    (h : LiveCheck.Live k t S) (he : v.toFinset = S) :
    Base1007.unionSep true (v.map p) = Base1007.top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,ha,hs⟩ := projected_sep pt pn pb h i hi
  have hm : p a ∈ v.map p := List.mem_map.mpr ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),rfl⟩
  simpa only [Base1007.top,BitVec.getLsbD_allOnes,hi,decide_true] using
    (Base1007.mem_unionSep _ _ _).2 ⟨p a,hm,Base1007.sep_weaken t (p a) i hi hs⟩

lemma directed_failure {k t : Nat} {v : List LiveCheck.Sig} {ps : List Base1007.Sig}
    (hp : ps = v.map p) (hf : Base1007.unionSep (decide (0 < t)) ps ≠ Base1007.top) :
    LiveCheck.Impossible k t v := by
  intro m hm h
  apply hf
  rw [hp]
  exact projected_cover pt pn pb h rfl

lemma xor_failure {k t : Nat} {v : List LiveCheck.Sig} {ps : List Base1007.Sig}
    (hp : ps = v.map p) (hf : Base1007.unionSep true ps ≠ Base1007.top) :
    LiveCheck.Impossible k t v := by
  intro m hm h
  apply hf
  rw [hp]
  exact projected_xor_cover pt pn pb h rfl

end PEqualNP.Outside.L_meta_670_aux.ProjectedCoverage
