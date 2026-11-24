theorem run_tight_bits {m y s ws} (h : NatRun m y s ws) (i j : Nat) :
    ws.length = s+1 →
    (∀ w ∈ ws, w.testBit i = true → w.testBit j = true) →
    y.testBit i = true → y.testBit j = true := by
  induction h using Run.fold with
  | done => intro hl hw; exact hw _ (by simp)
  | perm hp h ih =>
    intro hl hw
    exact ih (by rwa [hp.length_eq]) (fun w hm => hw w (hp.mem_iff.1 hm))
  | one save h ih =>
    intro hl hw
    have hlength := run_len h
    cases save <;> simp [kept] at hlength hl <;> omega
  | two conj ka kb h ih =>
    intro hl hw
    have hlength := run_len h
    have hk : ka = false ∧ kb = false := by
      cases ka <;> cases kb <;> simp [kept] at hlength hl ⊢ <;> omega
    rcases hk with ⟨rfl,rfl⟩
    apply ih
    · simp [kept] at hl ⊢
      omega
    · have ha := hw _ List.mem_cons_self
      have hbitB := hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
      intro w hm
      simp only [kept,Bool.false_eq_true,ite_false,List.mem_cons] at hm
      rcases hm with rfl | hm
      · cases conj <;> simp only [Bool.false_eq_true,ite_false,ite_true,
          Nat.testBit_and,Nat.testBit_or]
        · simp only [Bool.or_eq_true]
          intro ht
          rcases ht with ht | ht
          · exact Or.inl (ha ht)
          · exact Or.inr (hbitB ht)
        · simp only [Bool.and_eq_true]
          intro ht
          exact ⟨ha ht.1,hbitB ht.2⟩
      · exact hw _ (by simp [hm])

def tightPairCover (pairs : List (Nat × Nat)) (s : Nat) (ws : List Nat) : Bool :=
  if ws.length = s+1 then
    pairs.all fun p => ws.any fun w => !w.testBit p.1 && w.testBit p.2
  else pairCover pairs ws

theorem tightPairCover_ok {m y s ws} (h : NatRun m y s ws)
    (pairs : List (Nat × Nat))
    (hpairs : ∀ p ∈ pairs, m.testBit p.1 = m.testBit p.2 ∧
      y.testBit p.1 = false ∧ y.testBit p.2 = true) :
    tightPairCover pairs s ws = true := by
  unfold tightPairCover
  split_ifs with ht
  · apply List.all_eq_true.2
    intro p hp
    apply List.any_eq_true.2
    have hex : ∃ w ∈ ws, w.testBit p.1 = false ∧ w.testBit p.2 = true := by
      by_contra! hn
      have hb := run_tight_bits h p.2 p.1 ht
      have hy := hb (by
        intro w hw hwi
        have := hn w hw
        cases hv : w.testBit p.1
        · exact False.elim (this hv hwi)
        · rfl) (hpairs p hp).2.2
      rw [(hpairs p hp).2.1] at hy
      contradiction
    obtain ⟨w,hw,h0,h1⟩ := hex
    exact ⟨w,hw,by simp [h0,h1]⟩
  · apply pairCover_ok h pairs
    intro p hp
    exact ⟨(hpairs p hp).1,by simp [(hpairs p hp).2.1,(hpairs p hp).2.2]⟩
