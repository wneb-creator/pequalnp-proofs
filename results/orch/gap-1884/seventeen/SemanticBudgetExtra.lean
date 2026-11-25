import SemanticBudgetCore


namespace PEqualNP.Outside.L_meta_6581.Extended

def rawPin1884 (i : Fin 10) : Sig := initial.getD i.val zero

def probeStart1884 (i j : Fin 10) (d : Fin 4) : Row :=
  Fin.ofNat 1024 (([0,0,0,0,16,128,128,16,16,48,48,16,16,272,272,16,16,64,64,16,64,16,16,64,16,20,20,16,16,65,65,16,16,72,72,16,16,18,18,16,4,512,512,4,0,0,0,0,4,32,32,4,4,260,260,4,4,68,68,4,4,20,20,4,32,4,4,32,4,5,5,4,4,40,40,4,4,34,34,4,1,513,513,1,1,128,128,1,0,0,0,0,1,256,256,1,1,65,65,1,1,144,144,1,1,5,5,1,128,1,1,128,1,9,9,1,1,130,130,1,8,520,520,8,8,136,136,8,8,32,32,8,0,0,0,0,8,64,64,8,8,48,48,8,8,36,36,8,8,9,9,8,32,8,8,32,8,10,10,8,2,512,512,2,2,130,130,2,2,34,34,2,2,256,256,2,0,0,0,0,2,18,18,2,2,260,260,2,2,257,257,2,2,10,10,2,256,2,2,256,1,512,512,1,1,129,129,1,1,40,40,1,1,257,257,1,1,65,65,1,0,0,0,0,1,5,5,1,8,1,1,8,1,8,8,1,1,10,10,1,2,514,514,2,2,128,128,2,2,34,34,2,2,258,258,2,2,72,72,2,2,18,18,2,0,0,0,0,2,9,9,2,2,8,8,2,8,2,2,8,2,514,514,2,2,130,130,2,2,32,32,2,2,258,258,2,2,80,80,2,2,16,16,2,2,20,20,2,0,0,0,0,2,10,10,2,16,2,2,16,4,516,516,4,4,144,144,4,4,36,36,4,4,256,256,4,4,68,68,4,4,16,16,4,16,4,4,16,4,5,5,4,0,0,0,0,4,18,18,4,1,513,513,1,1,129,129,1,1,36,36,1,1,257,257,1,1,64,64,1,1,20,20,1,1,4,4,1,4,1,1,4,1,9,9,1,0,0,0,0] : List Nat).getD ((i.val * 10 + j.val) * 4 + d.val) 0)

def probeEnd1884 (i j : Fin 10) (d : Fin 4) : Row :=
  Fin.ofNat 1024 ((probeStart1884 i j d).val ^^^ ([512,128,32,256,64,16,4,1,8,2] : List Nat).getD i.val 0)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma probeSpec1884 : ∀ (i j : Fin 10) (d : Fin 4), i ≠ j →
    bit (probeStart1884 i j d) target ≠ bit (probeEnd1884 i j d) target ∧
    bit (probeStart1884 i j d) (bin d.val (rawPin1884 i) (rawPin1884 j)) =
      bit (probeEnd1884 i j d) (bin d.val (rawPin1884 i) (rawPin1884 j)) ∧
    ∀ q : Fin 10, q ≠ i →
      bit (probeStart1884 i j d) (rawPin1884 q) = bit (probeEnd1884 i j d) (rawPin1884 q) := by
  decide +kernel

lemma rawPin1884_mem {a : Sig} (ha : a ∈ initial) : ∃ i : Fin 10, rawPin1884 i = a := by
  have he : initial = List.ofFn rawPin1884 := by decide +kernel
  rw [he] at ha
  exact List.mem_ofFn.mp ha

lemma retain_first_left1884 {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat}
    (ha : a ∈ initial) (hb : b ∈ initial) (hab : a ≠ b) (hd : allowed true d)
    (raw : ∀ c ∈ U, c ∈ initial)
    (run : Live true target k (insert (bin d a b) U)) : a ∈ U := by
  classical
  by_contra hmiss
  obtain ⟨i,rfl⟩ := rawPin1884_mem ha
  obtain ⟨j,rfl⟩ := rawPin1884_mem hb
  have hij : i ≠ j := fun h => hab (congrArg rawPin1884 h)
  have hlt : d < 4 := by
    rcases hd with h | ⟨_,h⟩ <;> omega
  obtain ⟨hp,hbin,hstable⟩ := probeSpec1884 i j ⟨d,hlt⟩ hij
  obtain ⟨c,hc,hdiff⟩ := live_row_difference run hp
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact hdiff hbin
  · obtain ⟨q,rfl⟩ := rawPin1884_mem (raw c hc)
    have hqi : q ≠ i := by
      intro he
      subst q
      exact hmiss hc
    exact hdiff (hstable q hqi)

lemma retain_first_both1884 {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat}
    (ha : a ∈ initial) (hb : b ∈ initial) (hab : a ≠ b) (hd : allowed true d)
    (raw : ∀ c ∈ U, c ∈ initial)
    (run : Live true target k (insert (bin d a b) U)) : a ∈ U ∧ b ∈ U := by
  refine ⟨retain_first_left1884 ha hb hab hd raw run, ?_⟩
  apply retain_first_left1884 hb ha hab.symm (flip_flip hd).1 raw
  simpa only [← bin_flip hd a b] using run

end PEqualNP.Outside.L_meta_6581.Extended
namespace PEqualNP.Outside.L_meta_6581

lemma comb_available_zero1884 {R : Type} {bank : List (Wire R)} {a b : Wire R}
    (d : Nat) (hd : allowed true d) (ha : a=fun _ => false)
    (hb : Available true bank b) : Available true bank (comb d a b) := by
  rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
  · exact Or.inr (Or.inl ⟨false,by funext r;simp [comb,combine,ha]⟩)
  · simpa [comb,combine,ha] using hb
  · exact Or.inr (Or.inl ⟨false,by funext r;simp [comb,combine,ha]⟩)
  · simpa [comb,combine,inv,ha] using hb

lemma retained_restriction1884 {k : Nat} {U : Finset Extended.Sig}
    {a b : Extended.Sig} {d : Nat}
    (hd : Extended.allowed true d)
    (hrun : Extended.Live true Extended.target k (insert (Extended.bin d a b) U))
    (hretain : a∈U)
    (rows : Row → Extended.Row)
    (heq : restrictRows rows (Extended.observe Extended.target)=observe graph)
    (hzero : restrictRows rows (Extended.observe a)=fun _ => false)
    (hb : Available true (inputs.map observe) (restrictRows rows (Extended.observe b)))
    (hU : ∀ v∈U,Available true (inputs.map observe) (restrictRows rows (Extended.observe v)))
    (hfloor : Lower true inputs graph 15) :
    17 ≤ k+1 := by
  classical
  let S := insert (Extended.bin d a b) U
  let front := a :: (S.erase a).toList
  have ha : a∈S := Finset.mem_insert_of_mem hretain
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    exact ⟨by simp,Finset.nodup_toList _⟩
  have eqS : front.toFinset=S := by
    ext v
    by_cases hv : v=a <;> simp [front,hv,ha]
  have run := Extended.list_run hrun front nd eqS
  have supplyRoots : supply true (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows rows)) := by
    intro v hv
    obtain ⟨_,hin,rfl⟩ := List.mem_map.mp hv
    obtain ⟨v,hm,rfl⟩ := List.mem_map.mp hin
    have hmem : v∈S := eqS ▸ List.mem_toFinset.mpr hm
    rcases Finset.mem_insert.mp hmem with rfl | h
    · rw [Extended.obs_bin,restrict_comb]
      exact comb_available_zero1884 d hd hzero hb
    · exact hU v h
  have bound := projected_bound rows run (heq ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L:=15) (heq ▸ hfloor)
  have charge : 1≤mass ((front.map Extended.observe).map (restrictRows rows)) := by
    have ac : Constant (restrictRows rows (Extended.observe a)) := ⟨false,hzero⟩
    simp [front,mass_cons,cost,ac]
  omega

end PEqualNP.Outside.L_meta_6581
namespace PEqualNP.Outside.L_meta_6581

def moveNine1884 (i j : Fin 10) : Fin 10 :=
  (([[2,3,8,6,1,7,4,5,9,0],
    [4,3,8,5,0,9,2,6,7,1],
    [0,4,9,6,1,5,3,7,8,2],
    [1,0,5,7,2,6,4,8,9,3],
    [1,2,7,5,0,6,3,9,8,4],
    [1,2,3,4,0,6,7,8,9,5],
    [0,4,3,2,1,5,9,8,7,6],
    [1,0,4,3,2,6,5,9,8,7],
    [2,1,0,4,3,7,6,5,9,8],
    [0,1,2,3,4,5,6,7,8,9]] : List (List (Fin 10))).getD i.val []).getD j.val 0


def pinEmbed1884 (i : Fin 10) (r : Row) : Extended.Row :=
  Fin.ofNat 1024 ((List.finRange 9).foldl (fun m k =>
    if r.val.testBit k.val then
      m ||| ([512,128,32,256,64,16,4,1,8,2] : List Nat).getD (moveNine1884 i k.castSucc).val 0
    else m) 0)

def pinProj1884 (i : Fin 10) (a : Extended.Sig) : Sig :=
  table (restrictRows (pinEmbed1884 i) (Extended.observe a))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pin_target1884 : ∀ i : Fin 10,pinProj1884 i Extended.target=graph := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pin_self1884 : ∀ i : Fin 10,
    pinProj1884 i (Extended.pins.getD i.val Extended.zero)=zero := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pin_raw1884 : ∀ i j : Fin 10,
    ((pinProj1884 i (Extended.pins.getD j.val Extended.zero)==zero) ||
    inputs.contains (pinProj1884 i (Extended.pins.getD j.val Extended.zero))) = true := by
  decide +kernel

lemma pin_initial1884 :
    List.ofFn (fun i : Fin 10 => Extended.pins.getD i.val Extended.zero)=Extended.initial := by
  decide +kernel

lemma pin_observe1884 (i : Fin 10) (a : Extended.Sig) :
    restrictRows (pinEmbed1884 i) (Extended.observe a)=observe (pinProj1884 i a) :=
  (observe_table _).symm

lemma pin_available1884 (i : Fin 10) (a : Extended.Sig) (ha : a∈Extended.initial) :
    Available true (inputs.map observe) (restrictRows (pinEmbed1884 i) (Extended.observe a)) := by
  rw [←pin_initial1884] at ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
  rw [pin_observe1884]
  have hc := pin_raw1884 i j
  simp only [Bool.or_eq_true,beq_iff_eq] at hc
  rcases hc with hz | hm
  · exact Or.inr (Or.inl ⟨false,by rw [hz];funext r;simp [observe,bit,zero]⟩)
  · exact Or.inl (List.mem_map.mpr ⟨_,by simpa using hm,rfl⟩)

end PEqualNP.Outside.L_meta_6581
namespace PEqualNP.Outside.L_meta_6581

lemma atLeastSeventeen1884 {k : Nat} {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a∈S,a∈Extended.initial)
    (hfloor : Lower true inputs graph 15)
    (retained : ∀ {U : Finset Extended.Sig} {a b : Extended.Sig} {d k : Nat},
      a∈Extended.initial → b∈Extended.initial → a≠b → Extended.allowed true d →
      (∀ v∈U,v∈Extended.initial) →
      Extended.Live true Extended.target k (insert (Extended.bin d a b) U) → a∈U ∧ b∈U) :
    17≤k := by
  classical
  cases k with
  | zero =>
    obtain ⟨rfl,hp⟩ := run
    have hh := raw Extended.target (by simp)
    have hn : Extended.target∉Extended.initial := by decide +kernel
    exact (hn hh).elim
  | succ k =>
    obtain ⟨U,a,b,d,hd,hS,ha,hb,hab,hfresh,htail⟩ := run
    have haraw : a∈Extended.initial := raw a (by rw [hS];simp)
    have hbraw : b∈Extended.initial := raw b (by rw [hS];simp)
    have hU : ∀ v∈U,v∈Extended.initial := by
      intro v hv
      exact raw v (by rw [hS];simp [hv])
    have hretain := (retained haraw hbraw hab hd hU htail).1
    have hidx : a∈List.ofFn (fun i : Fin 10 => Extended.pins.getD i.val Extended.zero) := by
      rwa [pin_initial1884]
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hidx
    have heq : restrictRows (pinEmbed1884 i) (Extended.observe Extended.target)=observe graph := by
      rw [pin_observe1884,pin_target1884]
    have hzero : restrictRows (pinEmbed1884 i) (Extended.observe a)=fun _ => false := by
      rw [pin_observe1884,←hi,pin_self1884]
      funext r
      simp [observe,bit,zero]
    exact retained_restriction1884 hd htail hretain (pinEmbed1884 i) heq hzero
      (pin_available1884 i b hbraw) (fun v hv => pin_available1884 i v (hU v hv)) hfloor

end PEqualNP.Outside.L_meta_6581
namespace PEqualNP.Outside.L_meta_6581

lemma retained_absorbing_restriction1884 {k : Nat} {U : Finset Extended.Sig}
    {a z : Extended.Sig}
    (hrun : Extended.Live true Extended.target k (insert z U))
    (hretain : a∈U) (hfresh : z∉U)
    (rows : Row → Extended.Row)
    (heq : restrictRows rows (Extended.observe Extended.target)=observe graph)
    (hzero : restrictRows rows (Extended.observe a)=fun _ => false)
    (hz : Constant (restrictRows rows (Extended.observe z)))
    (hU : ∀ v∈U,Available true (inputs.map observe) (restrictRows rows (Extended.observe v)))
    (hfloor : Lower true inputs graph 15) :
    18 ≤ k+1 := by
  classical
  let front := z :: a :: (U.erase a).toList
  have hza : z≠a := fun h => hfresh (h ▸ hretain)
  have nd : front.Nodup := by
    simp [front,hza,hfresh]
    exact Finset.nodup_toList _
  have eqS : front.toFinset=insert z U := by
    ext v
    by_cases hv : v=a <;> simp [front,hv,hretain]
  have run := Extended.list_run hrun front nd eqS
  have supplyRoots : supply true (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows rows)) := by
    intro v hv
    obtain ⟨_,hin,rfl⟩ := List.mem_map.mp hv
    obtain ⟨v,hm,rfl⟩ := List.mem_map.mp hin
    have hmem : v∈insert z U := eqS ▸ List.mem_toFinset.mpr hm
    rcases Finset.mem_insert.mp hmem with rfl | h
    · exact Or.inr (Or.inl hz)
    · exact hU v h
  have bound := projected_bound rows run (heq ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L:=15) (heq ▸ hfloor)
  have charge : 2≤mass ((front.map Extended.observe).map (restrictRows rows)) := by
    have ac : Constant (restrictRows rows (Extended.observe a)) := ⟨false,hzero⟩
    simp [front,mass_cons,cost,ac,hz]
    omega
  omega

end PEqualNP.Outside.L_meta_6581

namespace PEqualNP.Outside.L_meta_6581
lemma signed_plan_seventeen1884 {k : Nat} {S : Finset Extended.Sig}
    (hfloor : Lower true inputs graph 15)
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a∈S,a∈Extended.initial) : 17≤k := by
  exact atLeastSeventeen1884 run raw hfloor
    (fun ha hb hab hd hU ht => Extended.retain_first_both1884 ha hb hab hd hU ht)

lemma circuit_nonNot_seventeen1884 (hfloor : Lower true inputs graph 15)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hcompute : ∀ x : Fin 10 → Bool,C.eval (List.ofFn x)=Extended.f10 x) :
    17≤C.gates.countP (fun g => !Extended.isNot g) := by
  obtain ⟨k,S,hk,hr,hs⟩ := Extended.realize C hfan hcompute
  exact (signed_plan_seventeen1884 hfloor hr hs).trans hk
end PEqualNP.Outside.L_meta_6581
