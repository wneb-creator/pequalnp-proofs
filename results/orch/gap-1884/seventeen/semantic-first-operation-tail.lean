namespace PEqualNP.Outside.L_meta_6581

lemma left_absorbing_eighteen1884 {k : Nat} {U : Finset Extended.Sig}
    {a b : Extended.Sig} {d : Nat}
    (hfloor : Lower true inputs graph 15)
    (ha : a∈Extended.initial)
    (hU : ∀ v∈U,v∈Extended.initial)
    (hretain : a∈U)
    (hfresh : Extended.bin d a b∉U)
    (hd : d=0 ∨ d=2)
    (hrun : Extended.Live true Extended.target k (insert (Extended.bin d a b) U)) :
    18≤k+1 := by
  have hidx : a∈List.ofFn (fun i : Fin 10 => Extended.pins.getD i.val Extended.zero) := by
    rwa [pin_initial1884]
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hidx
  have heq : restrictRows (pinEmbed1884 i) (Extended.observe Extended.target)=observe graph := by
    rw [pin_observe1884,pin_target1884]
  have hzero : restrictRows (pinEmbed1884 i) (Extended.observe a)=fun _ => false := by
    rw [pin_observe1884,←hi,pin_self1884]
    funext r
    simp [observe,bit,zero]
  have hz : Constant (restrictRows (pinEmbed1884 i) (Extended.observe (Extended.bin d a b))) := by
    refine ⟨false,?_⟩
    rw [Extended.obs_bin,restrict_comb]
    rcases hd with rfl | rfl <;> funext r <;> simp [comb,combine,inv,hzero]
  exact retained_absorbing_restriction1884 hrun hretain hfresh (pinEmbed1884 i)
    heq hzero hz (fun v hv => pin_available1884 i v (hU v hv)) hfloor

lemma first_non_or_eighteen1884 {k : Nat} {U : Finset Extended.Sig}
    {a b : Extended.Sig} {d : Nat}
    (hfloor : Lower true inputs graph 15)
    (ha : a∈Extended.initial) (hb : b∈Extended.initial) (hab : a≠b)
    (hd : Extended.allowed true d) (hnot : d≠1)
    (hU : ∀ v∈U,v∈Extended.initial)
    (hfresh : Extended.bin d a b∉U)
    (hrun : Extended.Live true Extended.target k (insert (Extended.bin d a b) U)) :
    18≤k+1 := by
  have hretain := Extended.retain_first_both1884 ha hb hab hd hU hrun
  rcases Extended.allowed_four hd with h0 | h1 | ⟨_,h2⟩ | ⟨_,h3⟩
  · exact left_absorbing_eighteen1884 hfloor ha hU hretain.1 hfresh (Or.inl h0) hrun
  · exact (hnot h1).elim
  · exact left_absorbing_eighteen1884 hfloor ha hU hretain.1 hfresh (Or.inr h2) hrun
  · subst d
    have he : Extended.bin 3 a b=Extended.bin 2 b a := by
      simp [Extended.bin,BitVec.and_comm]
    rw [he] at hfresh hrun
    exact left_absorbing_eighteen1884 hfloor hb hU hretain.2 hfresh (Or.inr rfl) hrun

lemma first_or_of_seventeen1884 {k : Nat} {U : Finset Extended.Sig}
    {a b : Extended.Sig} {d : Nat}
    (hfloor : Lower true inputs graph 15)
    (ha : a∈Extended.initial) (hb : b∈Extended.initial) (hab : a≠b)
    (hd : Extended.allowed true d)
    (hU : ∀ v∈U,v∈Extended.initial)
    (hfresh : Extended.bin d a b∉U)
    (hrun : Extended.Live true Extended.target k (insert (Extended.bin d a b) U))
    (hsmall : k+1≤17) : d=1 := by
  by_contra hn
  have hh := first_non_or_eighteen1884 hfloor ha hb hab hd hn hU hfresh hrun
  omega

end PEqualNP.Outside.L_meta_6581
