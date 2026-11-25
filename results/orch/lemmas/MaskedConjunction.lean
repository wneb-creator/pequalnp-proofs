import NegOrReassociate

namespace PEqualNP.Outside.L_meta_2592.FewNot.Extended

def negative_fold (p : Sig) : List Sig → Sig
  | [] => p
  | a :: as => bin 2 (negative_fold p as) a

lemma negative_fold_bit (r : Row) (p : Sig) (as : List Sig) :
    bit r (negative_fold p as) = (bit r p && !(as.any (bit r))) := by
  induction as with
  | nil => simp [negative_fold]
  | cons a as ih =>
    rw [negative_fold,bit_bin,ih]
    simp only [List.any_cons]
    cases bit r p <;> cases bit r a <;> cases as.any (bit r) <;> decide

lemma negative_fold_zero_bit (p : Sig) (as : List Sig) (hp : bit 0 p = false) :
    bit 0 (negative_fold p as) = false := by
  rw [negative_fold_bit,hp]
  rfl

lemma negative_fold_zero (as : List Sig) : negative_fold zero as = zero := by
  apply bit_ext
  intro r
  rw [negative_fold_bit,bit_zero]
  rfl

lemma pull_negative_fold (roots : List Sig) (p : Sig) (hp : p ∈ roots)
    (plain : ∀ v ∈ roots, bit 0 v = false) (as : List Sig)
    (available : ∀ v ∈ as, v ∈ roots)
    {k : Nat} {S : Finset Sig} (run : Live true target k S)
    (raw : ∀ v ∈ S, v ∈ roots ∨ v = negative_fold p as) :
    ∃ n T, n ≤ k + as.length ∧ Live true target n T ∧ ∀ v ∈ T, v ∈ roots := by
  induction as generalizing k S with
  | nil =>
    refine ⟨k,S,by simp,run,?_⟩
    intro v hv
    rcases raw v hv with h | h
    · exact h
    · simpa [negative_fold] using h ▸ hp
  | cons a as ih =>
    let q := negative_fold p as
    let extended := roots ++ [q]
    have hq0 : bit 0 q = false := negative_fold_zero_bit p as (plain p hp)
    have ha0 : bit 0 a = false := plain a (available a (by simp))
    have hq1 : q ≠ one := by intro h; rw [h,bit_one] at hq0; cases hq0
    have ha1 : a ≠ one := by intro h; rw [h,bit_one] at ha0; cases ha0
    have rep := bin_rep (u := true) (w := extended) 2 (Or.inr ⟨rfl,by decide⟩)
      (Or.inl (show q ∈ extended by simp [extended]))
      (Or.inl (show a ∈ extended by simp [extended,available a (by simp)]))
      (fun _ => ⟨hq1,ha1⟩)
    obtain ⟨m,U,hm,tail,hU⟩ := pull_gate (c := 1) run
      (rep.imp id (fun h => ⟨rfl,h⟩)) (by
        intro v hv
        rcases raw v hv with hv | hv
        · simp [extended,hv]
        · simp only [negative_fold] at hv
          simp [hv,q])
    obtain ⟨n,T,hn,done,hT⟩ := ih
      (fun v hv => available v (by simp [hv])) tail (by
        intro v hv
        simpa [extended,q] using hU v hv)
    exact ⟨n,T,by simp only [List.length_cons]; omega,done,hT⟩

lemma negative_fold_seed_bound {a c : Sig} (as : List Sig)
    (ha : a ∈ pins) (hc : c ∈ pins) (available : ∀ v ∈ as, v ∈ pins)
    {k : Nat} {S : Finset Sig} (run : Live true target k S)
    (raw : ∀ v ∈ S, v ∈ pins ∨ v = negative_fold (bin 2 c a) as) :
    18 ≤ k + (a :: as).length := by
  by_cases same : c = a
  · have hz : bin 2 c a = zero := by
      apply bit_ext
      intro r
      simp only [same,bit_bin,bit_zero]
      cases bit r a <;> decide
    have floor := PEqualNP.Outside.L_meta_2592.FewNot.pins_seventeen run (by
      intro v hv
      rcases raw v hv with hp | he
      · exact hp
      · exact False.elim ((live_proper run v hv).1
          (he.trans (by rw [hz,negative_fold_zero]))))
    simp only [List.length_cons]
    omega
  · let p := bin 2 c a
    let roots := pins ++ [p]
    have hp0 : bit 0 p = false := by simp [p,bit_bin,pin_zero_bit hc,pin_zero_bit ha]
    obtain ⟨n,T,hn,tail,hT⟩ := pull_negative_fold roots p (by simp [roots]) (by
      intro v hv
      simp only [roots,List.mem_append,List.mem_singleton] at hv
      rcases hv with hp | rfl
      · exact pin_zero_bit hp
      · exact hp0) as (by
        intro v hv
        simp [roots,available v hv]) run (by
          intro v hv
          rcases raw v hv with hp | he
          · exact Or.inl (by simp [roots,hp])
          · exact Or.inr he)
    have floor := PEqualNP.Outside.L_meta_2592.FewNot.pair_seventeen
      (Or.inr ⟨rfl,by decide⟩ : allowed true 2) (by decide : (2 : Nat) ≠ 1)
      hc ha same tail (by intro v hv; simpa [roots,p] using hT v hv)
    simp only [List.length_cons]
    omega

end PEqualNP.Outside.L_meta_2592.FewNot.Extended
