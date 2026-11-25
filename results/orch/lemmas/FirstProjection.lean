namespace PEqualNP.Outside.L_meta_2592_aux

def primaryWire (i : Fin 10) : Extended.Sig := Extended.initial.getD i.val Extended.zero

lemma primaryWire_list : List.ofFn primaryWire = Extended.initial := rfl

lemma initial_mem_index (a : Extended.Sig) : a ∈ Extended.initial ↔ ∃ i : Fin 10, primaryWire i = a := by
  rw [← primaryWire_list, List.mem_ofFn]

lemma primaryWire_mem (i : Fin 10) : primaryWire i ∈ Extended.initial :=
  (initial_mem_index _).mpr ⟨i, rfl⟩

def projectionMasks (i : Fin 10) : List Nat :=
  ([[1,2,4,8,16,32,64,128,256],
    [8,16,1,2,4,256,512,32,64],
    [2,4,8,16,1,64,128,256,512],
    [16,1,2,4,8,512,32,64,128],
    [4,8,16,1,2,128,256,512,32],
    [64,256,32,128,512,2,8,1,4],
    [512,64,256,32,128,16,2,8,1],
    [128,512,64,256,32,4,16,2,8],
    [32,128,512,64,256,1,4,16,2],
    [256,32,128,512,64,8,1,4,16]] : List (List Nat)).getD i.val []

def projectionRows (i : Fin 10) (r : Row) : Extended.Row :=
  ⟨((List.range 9).foldl (fun z b =>
    if r.val.testBit b then z ||| (projectionMasks i).getD b 0 else z) 0) % 1024,
    Nat.mod_lt _ (by decide)⟩

def projectedAt (i : Fin 10) (a : Extended.Sig) : Sig :=
  table fun r => Extended.bit (projectionRows i r) a

lemma observe_projectedAt (i : Fin 10) (a : Extended.Sig) :
    restrictRows (projectionRows i) (Extended.observe a) = observe (projectedAt i a) := by
  funext r
  exact (bit_table _ _).symm

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma projectedAt_target : ∀ i : Fin 10, projectedAt i Extended.target = graph := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma projectedAt_primary : ∀ i : Fin 10, projectedAt i (primaryWire i) = zero := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma projectedAt_permitted : ∀ i : Fin 10,
    Extended.initial.all (fun a => (projectedAt i a == zero) || inputs.contains (projectedAt i a)) = true := by
  decide +kernel

lemma projection_bit_bin (r : Row) (d : Nat) (a b : Sig) : bit r (bin d a b) =
    (if d = 0 then bit r a && bit r b else if d = 1 then bit r a || bit r b else
      if d = 2 then bit r a && !(bit r b) else !(bit r a) && bit r b) := by
  unfold bin
  split_ifs <;> simp [bit]

lemma projection_extended_bit_bin (r : Extended.Row) (d : Nat) (a b : Extended.Sig) :
    Extended.bit r (Extended.bin d a b) =
      (if d = 0 then Extended.bit r a && Extended.bit r b else
        if d = 1 then Extended.bit r a || Extended.bit r b else
          if d = 2 then Extended.bit r a && !(Extended.bit r b) else
            !(Extended.bit r a) && Extended.bit r b) := by
  unfold Extended.bin
  split_ifs <;> simp [Extended.bit]

lemma projectedAt_bin (i : Fin 10) (d : Nat) (a b : Extended.Sig) :
    projectedAt i (Extended.bin d a b) = bin d (projectedAt i a) (projectedAt i b) := by
  apply bit_ext
  intro r
  change bit r (table _) = _
  rw [bit_table, projection_extended_bit_bin, projection_bit_bin]
  simp only [projectedAt, bit_table]

lemma projectedAt_primary_cases (i : Fin 10) {a : Extended.Sig} (ha : a ∈ Extended.initial) :
    projectedAt i a = zero ∨ projectedAt i a ∈ inputs := by
  have h := List.all_eq_true.mp (projectedAt_permitted i) a ha
  simpa using h

lemma projectedAt_available (i : Fin 10) {a : Extended.Sig}
    (ha : projectedAt i a = zero ∨ projectedAt i a ∈ inputs) :
    Available true (inputs.map observe) (restrictRows (projectionRows i) (Extended.observe a)) := by
  rw [observe_projectedAt]
  rcases ha with hz | hm
  · right
    left
    refine ⟨false, ?_⟩
    rw [hz]
    funext r
    simp [observe, bit, zero]
  · left
    exact List.mem_map.mpr ⟨_, hm, rfl⟩

lemma projectedAt_gate_cases (i : Fin 10) (b : Extended.Sig)
    (hb : b ∈ Extended.initial) (d : Nat) (hd : Extended.allowed true d) :
    projectedAt i (Extended.bin d (primaryWire i) b) = zero ∨
      projectedAt i (Extended.bin d (primaryWire i) b) ∈ inputs := by
  rw [projectedAt_bin, projectedAt_primary]
  have h := projectedAt_primary_cases i hb
  rcases Extended.allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact Or.inl (by simp [bin, zero])
  · simpa [bin, zero] using h
  · exact Or.inl (by simp [bin, zero])
  · simpa [bin, zero] using h

lemma projectedAt_gate_zero (i : Fin 10) (b : Extended.Sig) (d : Nat)
    (hd : d = 0 ∨ d = 2) :
    projectedAt i (Extended.bin d (primaryWire i) b) = zero := by
  rw [projectedAt_bin, projectedAt_primary]
  rcases hd with rfl | rfl <;> simp [bin, zero]

lemma projection_constants_bound {k : Nat} {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S) (i : Fin 10)
    (singles : Finset Extended.Sig) (subS : singles ⊆ S)
    (constant : ∀ a ∈ singles, projectedAt i a = zero)
    (covered : ∀ a ∈ S, projectedAt i a = zero ∨ projectedAt i a ∈ inputs) :
    15 + singles.card ≤ k := by
  classical
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by
    ext a
    simp [front, Finset.union_sdiff_of_subset subS]
  have hrun := Extended.list_run run front nd fe
  have same : restrictRows (projectionRows i) (Extended.observe Extended.target) = observe graph := by
    rw [observe_projectedAt, projectedAt_target]
  have supp : supply true (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows (projectionRows i))) := by
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hm
    exact projectedAt_available i (covered a (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound (projectionRows i) hrun
    (same ▸ observe_proper graph_proper) Reach.start supp (L := 15) (same ▸ nineFloor)
  have massLo : singles.card ≤
      mass ((front.map Extended.observe).map (restrictRows (projectionRows i))) := by
    simp only [front, List.map_append, mass_append]
    let xs := (singles.toList.map Extended.observe).map (restrictRows (projectionRows i))
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hm
      rw [observe_projectedAt, constant a (Finset.mem_toList.mp hmem)]
      refine ⟨false, ?_⟩
      funext r
      simp [observe, bit, zero]
    have sz := mass_constants xs only
    simp only [xs, List.length_map, Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega

lemma first_binary_floor_seventeen {k : Nat} {U : Finset Extended.Sig}
    {a b : Extended.Sig} {d : Nat}
    (ha : a ∈ Extended.initial) (hb : b ∈ Extended.initial) (hne : a ≠ b)
    (hd : Extended.allowed true d) (raw : ∀ c ∈ U, c ∈ Extended.initial)
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d a b) U)) :
    17 ≤ k + 1 := by
  classical
  obtain ⟨i, hi⟩ := (initial_mem_index a).mp ha
  obtain ⟨keep, _⟩ := Extended.first_operands_retained ha hb hne hd raw tail
  have covered : ∀ c ∈ insert (Extended.bin d a b) U,
      projectedAt i c = zero ∨ projectedAt i c ∈ inputs := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · rw [← hi]
      exact projectedAt_gate_cases i b hb d hd
    · exact projectedAt_primary_cases i (raw c hc)
  have bound := projection_constants_bound tail i {a}
    (by simpa using Finset.mem_insert_of_mem keep)
    (by intro c hc; have hc' : c = a := by simpa using hc; subst c; rw [← hi]; exact projectedAt_primary i)
    covered
  simp only [Finset.card_singleton] at bound
  omega

lemma first_binary_floor_eighteen_left {k : Nat} {U : Finset Extended.Sig}
    {a b : Extended.Sig} {d : Nat}
    (ha : a ∈ Extended.initial) (hb : b ∈ Extended.initial) (hne : a ≠ b)
    (hd : Extended.allowed true d) (raw : ∀ c ∈ U, c ∈ Extended.initial)
    (fresh : Extended.bin d a b ∉ Extended.initial)
    (shape : d = 0 ∨ d = 2)
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d a b) U)) :
    18 ≤ k + 1 := by
  classical
  obtain ⟨i, hi⟩ := (initial_mem_index a).mp ha
  obtain ⟨keep, _⟩ := Extended.first_operands_retained ha hb hne hd raw tail
  have gateZero : projectedAt i (Extended.bin d a b) = zero := by
    rw [← hi]
    exact projectedAt_gate_zero i b d shape
  have covered : ∀ c ∈ insert (Extended.bin d a b) U,
      projectedAt i c = zero ∨ projectedAt i c ∈ inputs := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact Or.inl gateZero
    · exact projectedAt_primary_cases i (raw c hc)
  have distinct : a ≠ Extended.bin d a b := by
    intro h
    exact fresh (h ▸ ha)
  have sub : ({a, Extended.bin d a b} : Finset Extended.Sig) ⊆
      insert (Extended.bin d a b) U := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact Finset.mem_insert_of_mem keep
    · exact Finset.mem_insert_self _ _
  have constant : ∀ c ∈ ({a, Extended.bin d a b} : Finset Extended.Sig), projectedAt i c = zero := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · rw [← hi]
      exact projectedAt_primary i
    · exact gateZero
  have bound := projection_constants_bound tail i {a, Extended.bin d a b} sub constant covered
  simp only [Finset.card_pair distinct] at bound
  omega

lemma first_binary_floor_eighteen {k : Nat} {U : Finset Extended.Sig}
    {a b : Extended.Sig} {d : Nat}
    (ha : a ∈ Extended.initial) (hb : b ∈ Extended.initial) (hne : a ≠ b)
    (hd : Extended.allowed true d) (raw : ∀ c ∈ U, c ∈ Extended.initial)
    (fresh : Extended.bin d a b ∉ Extended.initial) (shape : d ≠ 1)
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d a b) U)) :
    18 ≤ k + 1 := by
  rcases Extended.allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact first_binary_floor_eighteen_left ha hb hne hd raw fresh (Or.inl rfl) tail
  · exact False.elim (shape rfl)
  · exact first_binary_floor_eighteen_left ha hb hne hd raw fresh (Or.inr rfl) tail
  · have eq : Extended.bin 3 a b = Extended.bin 2 b a := by
      simp [Extended.bin, BitVec.and_comm]
    apply first_binary_floor_eighteen_left hb ha hne.symm (by simp [Extended.allowed]) raw
      (eq ▸ fresh) (Or.inr rfl)
    exact eq ▸ tail

lemma atLeastSeventeen {k : Nat} {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) : 17 ≤ k := by
  have previous := atLeastSixteen run raw
  cases k with
  | zero => omega
  | succ k =>
    obtain ⟨U, a, b, d, hd, eqS, _, _, hne, _, tail⟩ := run
    have ha : a ∈ Extended.initial := raw a (eqS.symm ▸ Finset.mem_insert_self _ _)
    have hb : b ∈ Extended.initial := raw b (eqS.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hraw : ∀ c ∈ U, c ∈ Extended.initial := by
      intro c hc
      exact raw c (eqS.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc))
    exact first_binary_floor_seventeen ha hb hne hd hraw tail

end PEqualNP.Outside.L_meta_2592_aux
