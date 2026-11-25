namespace PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended.OrFirstNonOr

open Extended

def seed : Extended.Sig := bin 1 (pins.getD 0 zero) (pins.getD 1 zero)
def initial : List Extended.Sig := pins ++ [seed]
def bank (v : Extended.Sig) := pins ++ [seed,v]

lemma initial_lower {k S} (run : Live true target k S)
    (raw : ∀ a ∈ S, a ∈ initial) : 16 ≤ k :=
  CanonicalBank.lower 1 0 run raw

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma endpoint_extra : ∀ q : Bool, ∀ p : Fin 10, p = 0 ∨ p = 1 →
    SeedConjunction.extra q p = if q then pins.getD p.val zero else
      bin 2 (pins.getD (if p = 0 then 1 else 0) zero) (pins.getD p.val zero) := by
  decide +kernel

lemma positive_seed_lower (q : Bool) (p : Fin 10) {k S}
    (run : Live true target k S)
    (used : SeedConjunction.extra q p ∈ S)
    (raw : ∀ a ∈ S, a ∈ SeedConjunction.bank q p) : 16 ≤ k := by
  by_cases hp : p = 0 ∨ p = 1
  · have eq := endpoint_extra q p hp
    cases q with
    | true =>
      apply initial_lower run
      intro a ha
      have hr := raw a ha
      simp only [SeedConjunction.bank,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
      simp only [initial,List.mem_append,List.mem_singleton]
      rcases hr with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · have pin : pins.getD p.val zero ∈ pins := by
          have all : ∀ i : Fin 10, pins.getD i.val zero ∈ pins := by decide +kernel
          exact all p
        exact Or.inl (h.symm ▸ (eq.symm ▸ pin))
    | false =>
      let a : Fin 10 := if p = 0 then 1 else 0
      have hab : a ≠ p := by rcases hp with rfl | rfl <;> decide
      have he : SeedConjunction.extra false p = bin 2 (pins.getD a.val zero) (pins.getD p.val zero) := by
        by_cases hp0 : p = 0 <;> simpa [a,hp0] using eq
      apply second_rt_nonOr_lower 2 (by decide) a p hab run (he ▸ used)
      change ∀ v ∈ S, v ∈ pins ++ [seed,bin 2 (pins.getD a.val zero) (pins.getD p.val zero)]
      simpa only [SeedConjunction.bank,SeedConjunction.seed,he,seed] using raw
  · exact SeedConjunction.lower q p (fun h => hp (Or.inl h)) (fun h => hp (Or.inr h)) run raw used

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma negative_swap : ∀ p : Fin 10,
    bin 3 seed (pins.getD p.val zero) = NegativeSeedTransport.originalExtra p := by
  decide +kernel

lemma seed_pair_lower (d : Fin 4) (notOr : d.val ≠ 1) (p : Fin 10) {k S}
    (run : Live true target k S)
    (used : bin d.val seed (pins.getD p.val zero) ∈ S)
    (raw : ∀ a ∈ S, a ∈ bank (bin d.val seed (pins.getD p.val zero))) : 16 ≤ k := by
  fin_cases d
  · exact positive_seed_lower true p run used raw
  · exact (notOr rfl).elim
  · exact positive_seed_lower false p run used raw
  · have he := negative_swap p
    exact NegativeSeedTransport.lower p run
      (by
        change ∀ a ∈ S, a ∈ pins ++ [seed,NegativeSeedTransport.originalExtra p]
        simpa only [bank,he] using raw)
      (he ▸ used)

lemma nonOr_lower (d : Fin 4) (notOr : d.val ≠ 1) (a b : Extended.Sig)
    (ha : a ∈ initial) (hb : b ∈ initial) (hab : a ≠ b) {k S}
    (run : Live true target k S) (used : bin d.val a b ∈ S)
    (raw : ∀ v ∈ S, v ∈ bank (bin d.val a b)) : 16 ≤ k := by
  simp only [initial,List.mem_append,List.mem_singleton] at ha hb
  rcases ha with ha | rfl
  · have hlist : List.ofFn (fun i : Fin 10 => pins.getD i.val zero) = pins := rfl
    rw [←hlist] at ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    rcases hb with hb | rfl
    · rw [←hlist] at hb
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
      have hij : i ≠ j := fun h => hab (congrArg (fun t : Fin 10 => pins.getD t.val zero) h)
      exact second_rt_nonOr_lower d notOr i j hij run used raw
    · have hd : allowed true d.val := Or.inr ⟨rfl,d.isLt⟩
      have he := bin_flip hd (pins.getD i.val zero) seed
      have hf := (flip_flip hd).1
      have fb : flipOp d.val < 4 := by rcases hf with h | ⟨_,h⟩ <;> omega
      have fn : flipOp d.val ≠ 1 := by fin_cases d <;> simp_all [flipOp]
      exact seed_pair_lower ⟨flipOp d.val,fb⟩ fn i run (he ▸ used) (by simpa only [he] using raw)
  · rcases hb with hb | rfl
    · have hlist : List.ofFn (fun i : Fin 10 => pins.getD i.val zero) = pins := rfl
      rw [←hlist] at hb
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
      exact seed_pair_lower d notOr i run used raw
    · exact (hab rfl).elim


lemma first_or_of_sixteen {k S} (run : Live true target k S)
    (raw : ∀ a ∈ S, a ∈ initial) (budget : k ≤ 16) :
    k = 16 ∧ ∃ (a b : Extended.Sig) (T : Finset Extended.Sig),
      a ∈ initial ∧ b ∈ initial ∧ a ≠ b ∧
      bin 1 a b ≠ a ∧ bin 1 a b ≠ b ∧
      Live true target 15 T ∧ bin 1 a b ∈ T ∧
      ∀ v ∈ T, v ∈ bank (bin 1 a b) := by
  have bound := initial_lower run raw
  have hk : k = 16 := by omega
  refine ⟨hk,?_⟩
  subst k
  obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
  have ha : a ∈ initial := raw a (by simp)
  have hb : b ∈ initial := raw b (by simp)
  have used : bin d a b ∈ insert (bin d a b) U := by simp
  have tailRaw : ∀ v ∈ insert (bin d a b) U, v ∈ bank (bin d a b) := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simp [bank]
    · have h := raw v (by simp [hv])
      simp only [initial,bank,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      exact h.elim Or.inl (Or.inr ∘ Or.inl)
  have dlt : d < 4 := by rcases hd with h | ⟨_,h⟩ <;> omega
  have hone : d = 1 := by
    by_contra hn
    have impossible := nonOr_lower ⟨d,dlt⟩ hn a b ha hb hab tail used tailRaw
    exact (by decide : ¬ ((16 : Nat) ≤ 15)) impossible
  subst d
  refine ⟨a,b,insert (bin 1 a b) U,ha,hb,hab,?_,?_,tail,used,tailRaw⟩
  · intro eq
    apply hfresh
    simp [eq]
  · intro eq
    apply hfresh
    simp [eq]

end PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended.OrFirstNonOr
