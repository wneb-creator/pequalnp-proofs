import PEqualNP.Outside.L_meta_2592

namespace PEqualNP.Outside.L_meta_2592.Floor17

def oneDropRows : List (ℕ × ℕ) := [(0,0),(0,0),(0,0),(0,0),(32,160),(512,640),(32,160),(512,640),(128,160),(768,800),(128,160),(768,800),(32,288),(544,800),(32,288),(544,800),(256,320),(512,576),(256,320),(512,576),(1,17),(512,528),(1,17),(512,528),(128,132),(520,524),(128,132),(520,524),(32,33),(544,545),(32,33),(544,545),(256,264),(768,776),(256,264),(768,776),(64,66),(516,518),(64,66),(516,518),(64,576),(128,640),(64,576),(128,640),(0,0),(0,0),(0,0),(0,0),(256,288),(128,160),(256,288),(128,160),(32,288),(192,448),(32,288),(192,448),(512,576),(384,448),(512,576),(384,448),(512,528),(129,145),(512,528),(129,145),(8,12),(128,132),(8,12),(128,132),(32,33),(144,145),(32,33),(144,145),(256,264),(384,392),(256,264),(384,392),(64,66),(192,194),(64,66),(192,194),(128,640),(96,608),(128,640),(96,608),(512,640),(32,160),(512,640),(32,160),(0,0),(0,0),(0,0),(0,0),(64,320),(32,288),(64,320),(32,288),(512,576),(544,608),(512,576),(544,608),(512,528),(544,560),(512,528),(544,560),(128,132),(40,44),(128,132),(40,44),(16,17),(32,33),(16,17),(32,33),(256,264),(48,56),(256,264),(48,56),(64,66),(96,98),(64,66),(96,98),(128,640),(384,896),(128,640),(384,896),(512,640),(768,896),(512,640),(768,896),(128,160),(256,288),(128,160),(256,288),(0,0),(0,0),(0,0),(0,0),(512,576),(256,320),(512,576),(256,320),(512,528),(768,784),(512,528),(768,784),(128,132),(384,388),(128,132),(384,388),(32,33),(272,273),(32,33),(272,273),(16,24),(256,264),(16,24),(256,264),(64,66),(260,262),(64,66),(260,262),(128,640),(64,576),(128,640),(64,576),(512,640),(96,224),(512,640),(96,224),(128,160),(192,224),(128,160),(192,224),(32,288),(64,320),(32,288),(64,320),(0,0),(0,0),(0,0),(0,0),(512,528),(65,81),(512,528),(65,81),(128,132),(192,196),(128,132),(192,196),(32,33),(96,97),(32,33),(96,97),(256,264),(80,88),(256,264),(80,88),(4,6),(64,66),(4,6),(64,66),(128,640),(16,528),(128,640),(16,528),(512,640),(48,176),(512,640),(48,176),(128,160),(144,176),(128,160),(144,176),(32,288),(48,304),(32,288),(48,304),(512,576),(272,336),(512,576),(272,336),(0,0),(0,0),(0,0),(0,0),(128,132),(144,148),(128,132),(144,148),(32,33),(16,17),(32,33),(16,17),(256,264),(16,24),(256,264),(16,24),(64,66),(80,82),(64,66),(80,82),(128,640),(68,580),(128,640),(68,580),(512,640),(4,132),(512,640),(4,132),(128,160),(260,292),(128,160),(260,292),(32,288),(36,292),(32,288),(36,292),(512,576),(516,580),(512,576),(516,580),(512,528),(516,532),(512,528),(516,532),(0,0),(0,0),(0,0),(0,0),(32,33),(36,37),(32,33),(36,37),(256,264),(4,12),(256,264),(4,12),(64,66),(4,6),(64,66),(4,6),(128,640),(129,641),(128,640),(129,641),(512,640),(513,641),(512,640),(513,641),(128,160),(1,33),(128,160),(1,33),(32,288),(65,321),(32,288),(65,321),(512,576),(513,577),(512,576),(513,577),(512,528),(1,17),(512,528),(1,17),(128,132),(129,133),(128,132),(129,133),(0,0),(0,0),(0,0),(0,0),(256,264),(257,265),(256,264),(257,265),(64,66),(1,3),(64,66),(1,3),(128,640),(136,648),(128,640),(136,648),(512,640),(520,648),(512,640),(520,648),(128,160),(136,168),(128,160),(136,168),(32,288),(8,264),(32,288),(8,264),(512,576),(520,584),(512,576),(520,584),(512,528),(8,24),(512,528),(8,24),(128,132),(8,12),(128,132),(8,12),(32,33),(40,41),(32,33),(40,41),(0,0),(0,0),(0,0),(0,0),(64,66),(72,74),(64,66),(72,74),(128,640),(130,642),(128,640),(130,642),(512,640),(514,642),(512,640),(514,642),(128,160),(130,162),(128,160),(130,162),(32,288),(34,290),(32,288),(34,290),(512,576),(2,66),(512,576),(2,66),(512,528),(514,530),(512,528),(514,530),(128,132),(2,6),(128,132),(2,6),(32,33),(2,3),(32,33),(2,3),(256,264),(258,266),(256,264),(258,266),(0,0),(0,0),(0,0),(0,0)]

def oneDropWitnessRows (i j : Fin 10) (d : Fin 4) : Extended.Row × Extended.Row :=
  let w := oneDropRows.getD ((i.val * 10 + j.val) * 4 + d.val) (0,0)
  (Fin.ofNat 1024 w.1, Fin.ofNat 1024 w.2)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma oneDropWitness : ∀ (i j : Fin 10) (d : Fin 4), i ≠ j →
    let r := (oneDropWitnessRows i j d).1
    let s := (oneDropWitnessRows i j d).2
    Extended.bit r Extended.target ≠ Extended.bit s Extended.target ∧
    Extended.bit r (Extended.bin d.val (pin i) (pin j)) =
      Extended.bit s (Extended.bin d.val (pin i) (pin j)) ∧
    ∀ q : Fin 10, q ≠ j → Extended.bit r (pin q) = Extended.bit s (pin q) := by
  decide +kernel

lemma keep_second {k : ℕ} {U : Finset Extended.Sig} {a b : Extended.Sig} {d : ℕ}
    (ha : a ∈ Extended.pins) (hb : b ∈ Extended.pins)
    (hu : ∀ c ∈ U, c ∈ Extended.pins) (hd : Extended.allowed true d) (hab : a ≠ b)
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d a b) U)) : b ∈ U := by
  classical
  by_contra nb
  obtain ⟨i,rfl⟩ := pinComplete a ha
  obtain ⟨j,rfl⟩ := pinComplete b hb
  have hij : i ≠ j := by intro h; subst j; exact hab rfl
  have hd4 : d < 4 := by rcases hd with h|⟨_,h⟩ <;> omega
  have witness := oneDropWitness i j ⟨d,hd4⟩ hij
  obtain ⟨c,hc,different⟩ := Extended.live_row_difference tail witness.1
  rcases Finset.mem_insert.mp hc with rfl|hc
  · exact different witness.2.1
  · obtain ⟨q,rfl⟩ := pinComplete c (hu c hc)
    have hqj : q ≠ j := by intro h; subst q; exact nb hc
    exact different (witness.2.2 q hqj)

lemma keep_both {k : ℕ} {U : Finset Extended.Sig} {a b : Extended.Sig} {d : ℕ}
    (ha : a ∈ Extended.pins) (hb : b ∈ Extended.pins)
    (hu : ∀ c ∈ U, c ∈ Extended.pins) (hd : Extended.allowed true d) (hab : a ≠ b)
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d a b) U)) : a ∈ U ∧ b ∈ U := by
  refine ⟨?_,keep_second ha hb hu hd hab tail⟩
  have flip := Extended.bin_flip hd a b
  rw [flip] at tail
  exact keep_second hb ha hu (Extended.flip_flip hd).1 (Ne.symm hab) tail

lemma keep_left_constant {k : ℕ} {U : Finset Extended.Sig} {d : ℕ} {b : Extended.Sig}
    (i : Fin 10) (hb : b ∈ Extended.pins) (hu : ∀ a ∈ U, a ∈ Extended.pins)
    (keep : pin i ∈ U) (fresh : Extended.bin d (pin i) b ∉ U)
    (kind : d = 0 ∨ d = 2)
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d (pin i) b) U)) :
    17 ≤ k := by
  classical
  let ws := Extended.bin d (pin i) b :: U.toList
  have nd : ws.Nodup := by
    exact List.nodup_cons.mpr ⟨by simpa using fresh,Finset.nodup_toList U⟩
  have eqS : ws.toFinset = insert (Extended.bin d (pin i) b) U := by simp [ws]
  have hrun := Extended.list_run tail ws nd eqS
  have same : restrictRows (projection i) (Extended.observe Extended.target) = observe graph := by
    rw [observe_projected,projectionGoal]
  have supplyRoots : supply true (inputs.map observe)
      ((ws.map Extended.observe).map (restrictRows (projection i))) := by
    intro v hv
    obtain ⟨_,hmem,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hmem
    change a ∈ Extended.bin d (pin i) b :: U.toList at ha
    rcases List.mem_cons.mp ha with rfl|ha
    · exact projected_bin_available i b hb d
    · exact projected_available i a (hu a (by simpa using ha))
  have need := projected_bound (projection i) hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L:=15) (same ▸ nineFloor)
  have pinProjectedMem : restrictRows (projection i) (Extended.observe (pin i)) ∈
      ((U.toList.map Extended.observe).map (restrictRows (projection i))) :=
    List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨_,by simpa using keep,rfl⟩,rfl⟩
  have charge := mass_one pinProjectedMem (show Constant
      (restrictRows (projection i) (Extended.observe (pin i))) from ⟨false,pin_zero_wire i⟩)
  have dead : Constant (restrictRows (projection i) (Extended.observe (Extended.bin d (pin i) b))) := by
    refine ⟨false,?_⟩
    rw [Extended.obs_bin]
    funext r
    have hz := congrFun (pin_zero_wire i) r
    change Extended.observe (pin i) (projection i r) = false at hz
    rcases kind with rfl|rfl <;> simp [restrictRows,comb,combine,hz]
  have fullcharge : 2 ≤ mass ((ws.map Extended.observe).map (restrictRows (projection i))) := by
    simp only [ws,List.map_cons,mass_cons]
    have one : cost (restrictRows (projection i)
        (Extended.observe (Extended.bin d (pin i) b))) = 1 := by simp [cost,dead]
    rw [one]
    omega
  omega

lemma first_nonor_floor {k : ℕ} {U : Finset Extended.Sig} {a b : Extended.Sig} {d : ℕ}
    (ha : a ∈ Extended.pins) (hb : b ∈ Extended.pins)
    (hu : ∀ c ∈ U, c ∈ Extended.pins) (hd : Extended.allowed true d) (hab : a ≠ b)
    (fresh : Extended.bin d a b ∉ U) (kind : d ≠ 1)
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d a b) U)) : 18 ≤ k + 1 := by
  obtain ⟨ka,kb⟩ := keep_both ha hb hu hd hab tail
  rcases Extended.allowed_four hd with h0|h1|⟨_,h2⟩|⟨_,h3⟩
  · subst d
    obtain ⟨i,rfl⟩ := pinComplete a ha
    have lower := keep_left_constant i hb hu ka fresh (Or.inl rfl) tail
    omega
  · exact False.elim (kind h1)
  · subst d
    obtain ⟨i,rfl⟩ := pinComplete a ha
    have lower := keep_left_constant i hb hu ka fresh (Or.inr rfl) tail
    omega
  · subst d
    obtain ⟨i,rfl⟩ := pinComplete b hb
    have eq : Extended.bin 3 a (pin i) = Extended.bin 2 (pin i) a := by
      simpa [Extended.flipOp] using Extended.bin_flip hd a (pin i)
    rw [eq] at tail fresh
    have lower := keep_left_constant i ha hu kb fresh (Or.inr rfl) tail
    omega

end PEqualNP.Outside.L_meta_2592.Floor17
