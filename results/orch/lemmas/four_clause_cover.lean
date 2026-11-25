import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602_aux.RectangleCNF

def edge (E : Fin 512) (p q : Fin 3) : Prop := E.val.testBit (3*p.val+q.val) = true

def diagonal (E : Fin 512) : Prop := ∀ i : Fin 3, edge E i i

def noFour (E : Fin 512) : Prop :=
  ∀ p q l m : Fin 3, p ≠ q → l ≠ m → ¬ (edge E p l ∧ edge E p m ∧ edge E q l ∧ edge E q m)

def independent (E : Fin 512) (S : Fin 64) : Prop :=
  ∀ p q : Fin 3, edge E p q → ¬ (S.val.testBit p.val = true ∧ S.val.testBit (3+q.val) = true)

def conflict (S T : Fin 64) : Prop :=
  ∃ i : Fin 3, (S.val.testBit i.val || T.val.testBit i.val) = true ∧
    (S.val.testBit (3+i.val) || T.val.testBit (3+i.val)) = true

def cert (E : Fin 512) : Fin 5 → Fin 64 :=
  if E.val &&& 279 = E.val then ![1,14,28,42,56] else
  if E.val &&& 309 = E.val then ![3,10,17,28,56] else
  if E.val &&& 313 = E.val then ![2,21,28,49,56] else
  if E.val &&& 345 = E.val then ![6,20,34,49,56] else
  if E.val &&& 371 = E.val then ![7,10,20,33,56] else
  if E.val &&& 403 = E.val then ![5,12,33,42,56] else
  if E.val &&& 413 = E.val then ![7,12,17,34,56] else
  ![4,35,42,49,56]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
lemma cert_correct : ∀ E : Fin 512, diagonal E → noFour E →
    (∀ i : Fin 5, independent E (cert E i)) ∧
      (∀ i j : Fin 5, i ≠ j → conflict (cert E i) (cert E j)) := by
  unfold diagonal noFour independent conflict edge
  decide


def accepts (A : Finset (Fin 6)) (S : Fin 64) : Prop :=
  ∃ v ∈ A, S.val.testBit v.val = true

lemma no_four_clauses (E : Fin 512) (hd : diagonal E) (h4 : noFour E)
    (A : Fin 4 → Finset (Fin 6))
    (hits : ∀ c : Fin 4, ∀ i : Fin 3,
      Fin.castAdd 3 i ∈ A c ∨ Fin.natAdd 3 i ∈ A c)
    (clean : ∀ S : Fin 64, (∀ c : Fin 4, accepts (A c) S) →
      ∃ p q : Fin 3, edge E p q ∧ S.val.testBit p.val = true ∧
        S.val.testBit (3+q.val) = true) : False := by
  classical
  obtain ⟨ind,conf⟩ := cert_correct E hd h4
  have miss : ∀ i : Fin 5, ∃ c : Fin 4, ¬ accepts (A c) (cert E i) := by
    intro i
    by_contra h
    push Not at h
    obtain ⟨p,q,hpq,hp,hq⟩ := clean (cert E i) h
    exact ind i p q hpq ⟨hp,hq⟩
  choose f hf using miss
  have inj : Function.Injective f := by
    intro i j heq
    by_contra hne
    obtain ⟨k,hp,hq⟩ := conf i j hne
    simp only [Bool.or_eq_true] at hp hq
    rcases hits (f i) k with h | h
    · rcases hp with hbit | hbit
      · exact hf i ⟨Fin.castAdd 3 k,h,hbit⟩
      · exact hf j ⟨Fin.castAdd 3 k,heq ▸ h,hbit⟩
    · rcases hq with hbit | hbit
      · exact hf i ⟨Fin.natAdd 3 k,h,hbit⟩
      · exact hf j ⟨Fin.natAdd 3 k,heq ▸ h,hbit⟩
  have card := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_fin] at card
  omega


def bits (R : Fin 3 → Fin 3 → Bool) : BitVec 9 :=
  BitVec.ofBool (R 2 2) ++ BitVec.ofBool (R 2 1) ++ BitVec.ofBool (R 2 0) ++
  BitVec.ofBool (R 1 2) ++ BitVec.ofBool (R 1 1) ++ BitVec.ofBool (R 1 0) ++
  BitVec.ofBool (R 0 2) ++ BitVec.ofBool (R 0 1) ++ BitVec.ofBool (R 0 0)

def encode (R : Fin 3 → Fin 3 → Bool) : Fin 512 := (bits R).toFin

lemma edge_encode (R : Fin 3 → Fin 3 → Bool) (p q : Fin 3) :
    edge (encode R) p q ↔ R p q = true := by
  change (bits R).toNat.testBit (3*p.val+q.val) = true ↔ R p q = true
  rw [BitVec.testBit_toNat]
  fin_cases p <;> fin_cases q <;>
    norm_num only [bits,BitVec.getLsbD_append,BitVec.getLsbD_ofBool] <;> simp

lemma no_matching_three {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (noRect : ∀ p q l m, p ≠ q → l ≠ m → R p l → R p m → R q l → ¬ R q m)
    (P : Fin 3 → α) (Q : Fin 3 → β) (hP : Function.Injective P) (hQ : Function.Injective Q)
    (matching : ∀ i : Fin 3, R (P i) (Q i))
    (C : Fin 4 → Finset (α ⊕ β))
    (hits : ∀ c : Fin 4, ∀ i : Fin 3, Sum.inl (P i) ∈ C c ∨ Sum.inr (Q i) ∈ C c)
    (clean : ∀ (f : α → Bool) (g : β → Bool),
      (∀ c : Fin 4, ∃ v ∈ C c, Sum.elim f g v = true) →
      ∃ p q, R p q ∧ f p = true ∧ g q = true) : False := by
  classical
  let E := encode (fun i j => decide (R (P i) (Q j)))
  have he : ∀ i j : Fin 3, edge E i j ↔ R (P i) (Q j) := by
    intro i j
    simpa [E] using edge_encode (fun i j => decide (R (P i) (Q j))) i j
  have hd : diagonal E := fun i => (he i i).mpr (matching i)
  have h4 : noFour E := by
    intro i j k l hij hkl ⟨h1,h2,h3,h4⟩
    exact noRect (P i) (P j) (Q k) (Q l) (fun h => hij (hP h))
      (fun h => hkl (hQ h)) ((he i k).mp h1) ((he i l).mp h2)
      ((he j k).mp h3) ((he j l).mp h4)
  let vertex : Fin 6 → α ⊕ β := fun v => Fin.addCases (motive := fun _ => α ⊕ β)
    (fun i => Sum.inl (P i)) (fun j => Sum.inr (Q j)) v
  let A : Fin 4 → Finset (Fin 6) := fun c => Finset.univ.filter (fun v => vertex v ∈ C c)
  have ha : ∀ c : Fin 4, ∀ i : Fin 3, Fin.castAdd 3 i ∈ A c ∨ Fin.natAdd 3 i ∈ A c := by
    intro c i
    simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and,vertex,
      Fin.addCases_left,Fin.addCases_right] using hits c i
  apply no_four_clauses E hd h4 A ha
  intro S hs
  let f : α → Bool := fun p => decide (∃ i : Fin 3, P i = p ∧ S.val.testBit i.val = true)
  let g : β → Bool := fun q => decide (∃ i : Fin 3, Q i = q ∧ S.val.testBit (3+i.val) = true)
  have split (v : Fin 6) : (∃ i : Fin 3, v = Fin.castAdd 3 i) ∨
      (∃ j : Fin 3, v = Fin.natAdd 3 j) := by
    by_cases h : v.val < 3
    · exact Or.inl ⟨⟨v.val,h⟩,rfl⟩
    · refine Or.inr ⟨⟨v.val-3,by omega⟩,?_⟩
      apply Fin.ext
      dsimp
      omega
  have pass : ∀ c : Fin 4, ∃ v ∈ C c, Sum.elim f g v = true := by
    intro c
    obtain ⟨v,hv,hbit⟩ := hs c
    have hv' := (Finset.mem_filter.mp hv).2
    rcases split v with ⟨i,rfl⟩ | ⟨j,rfl⟩
    · refine ⟨Sum.inl (P i),by simpa only [vertex,Fin.addCases_left,Fin.addCases_right] using hv',?_⟩
      change decide (∃ j : Fin 3, P j = P i ∧ S.val.testBit j.val = true) = true
      exact decide_eq_true ⟨i,rfl,hbit⟩
    · refine ⟨Sum.inr (Q j),by simpa only [vertex,Fin.addCases_left,Fin.addCases_right] using hv',?_⟩
      change decide (∃ i : Fin 3, Q i = Q j ∧ S.val.testBit (3+i.val) = true) = true
      exact decide_eq_true ⟨j,rfl,hbit⟩
  obtain ⟨p,q,hpq,hp,hq⟩ := clean f g pass
  have hp' : ∃ i : Fin 3, P i = p ∧ S.val.testBit i.val = true := of_decide_eq_true hp
  have hq' : ∃ i : Fin 3, Q i = q ∧ S.val.testBit (3+i.val) = true := of_decide_eq_true hq
  obtain ⟨i,rfl,hi⟩ := hp'
  obtain ⟨j,rfl,hj⟩ := hq'
  exact ⟨i,j,(he i j).mpr hpq,hi,hj⟩

end PEqualNP.Outside.L_meta_2602_aux.RectangleCNF


namespace PEqualNP.Outside.L_meta_2602_aux.MatchingCover

lemma injective_three {α : Type*} (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

lemma cover_two_branch {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop)
    (noThree : ∀ a b c : α, ∀ u v w : β,
      a ≠ b → a ≠ c → b ≠ c → u ≠ v → u ≠ w → v ≠ w →
      R a u → R b v → R c w → False)
    (a b c : α) (u v : β)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (huv : u ≠ v)
    (hau : R a u) (hbv : R b v) (hcu : R c u) :
    ∃ P : Finset α, ∃ Q : Finset β, P.card + Q.card ≤ 2 ∧
      ∀ p q, R p q → p ∈ P ∨ q ∈ Q := by
  classical
  have alternate (d : α) : ∃ x, R x u ∧ x ≠ b ∧ x ≠ d := by
    by_cases hda : d = a
    · exact ⟨c, hcu, (Ne.symm hbc), by simpa [hda] using (Ne.symm hac)⟩
    · exact ⟨a, hau, hab, (Ne.symm hda)⟩
  by_cases cols : ∀ p q, R p q → q = u ∨ q = v
  · refine ⟨∅, {u, v}, by simp [huv], ?_⟩
    intro p q hpq
    exact Or.inr (by simpa using cols p q hpq)
  · push Not at cols
    obtain ⟨d, z, hdz, hzu, hzv⟩ := cols
    have hdb : d = b := by
      by_contra hdb
      obtain ⟨x, hxu, hxb, hxd⟩ := alternate d
      exact noThree x b d u v z hxb hxd (Ne.symm hdb) huv (Ne.symm hzu) (Ne.symm hzv)
        hxu hbv hdz
    subst d
    refine ⟨{b}, {u}, by simp, ?_⟩
    intro p q hpq
    by_cases hpb : p = b
    · exact Or.inl (by simp [hpb])
    by_cases hqu : q = u
    · exact Or.inr (by simp [hqu])
    obtain ⟨x, hxu, hxb, hxp⟩ := alternate p
    by_cases hqv : q = v
    · exact False.elim (noThree x b p u z v hxb hxp (Ne.symm hpb) (Ne.symm hzu) huv hzv
        hxu hdz (hqv ▸ hpq))
    · exact False.elim (noThree x b p u v q hxb hxp (Ne.symm hpb) huv (Ne.symm hqu) (Ne.symm hqv)
        hxu hbv hpq)

lemma cover_two_of_no_three {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop)
    (noThree : ∀ a b c : α, ∀ u v w : β,
      a ≠ b → a ≠ c → b ≠ c → u ≠ v → u ≠ w → v ≠ w →
      R a u → R b v → R c w → False) :
    ∃ P : Finset α, ∃ Q : Finset β, P.card + Q.card ≤ 2 ∧
      ∀ p q, R p q → p ∈ P ∨ q ∈ Q := by
  classical
  by_cases two : ∃ a b : α, ∃ u v : β, a ≠ b ∧ u ≠ v ∧ R a u ∧ R b v
  · obtain ⟨a, b, u, v, hab, huv, hau, hbv⟩ := two
    by_cases rows : ∀ p q, R p q → p = a ∨ p = b
    · refine ⟨{a, b}, ∅, by simp [hab], ?_⟩
      intro p q hpq
      exact Or.inl (by simpa using rows p q hpq)
    · push Not at rows
      obtain ⟨c, w, hcw, hca, hcb⟩ := rows
      have hwu : w = u ∨ w = v := by
        by_contra h
        push Not at h
        exact noThree a b c u v w hab (Ne.symm hca) (Ne.symm hcb) huv (Ne.symm h.1) (Ne.symm h.2)
          hau hbv hcw
      rcases hwu with hwu | hwv
      · exact cover_two_branch R noThree a b c u v hab (Ne.symm hca) (Ne.symm hcb) huv
          hau hbv (hwu ▸ hcw)
      · exact cover_two_branch R noThree b a c v u (Ne.symm hab) (Ne.symm hcb) (Ne.symm hca)
          (Ne.symm huv) hbv hau (hwv ▸ hcw)
  · by_cases edge : ∃ a u, R a u
    · obtain ⟨a, u, hau⟩ := edge
      refine ⟨{a}, {u}, by simp, ?_⟩
      intro p q hpq
      by_cases hpa : p = a
      · exact Or.inl (by simp [hpa])
      by_cases hqu : q = u
      · exact Or.inr (by simp [hqu])
      exact False.elim (two ⟨a, p, u, q, (Ne.symm hpa), (Ne.symm hqu), hau, hpq⟩)
    · refine ⟨∅, ∅, by simp, ?_⟩
      intro p q hpq
      exact False.elim (edge ⟨p, q, hpq⟩)

lemma cover_two_of_no_matching_three {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop)
    (noMatching : ¬∃ (P : Fin 3 → α) (Q : Fin 3 → β),
      Function.Injective P ∧ Function.Injective Q ∧ ∀ i, R (P i) (Q i)) :
    ∃ P : Finset α, ∃ Q : Finset β, P.card + Q.card ≤ 2 ∧
      ∀ p q, R p q → p ∈ P ∨ q ∈ Q := by
  apply cover_two_of_no_three R
  intro a b c u v w hab hac hbc huv huw hvw hau hbv hcw
  apply noMatching
  refine ⟨![a, b, c], ![u, v, w], injective_three a b c hab hac hbc,
    injective_three u v w huv huw hvw, ?_⟩
  intro i
  fin_cases i <;> simp_all

end PEqualNP.Outside.L_meta_2602_aux.MatchingCover

namespace PEqualNP.Outside.L_meta_2602_aux.RectangleCNF

lemma four_clause_shadow_cover_two {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (noRect : ∀ p q l m, p ≠ q → l ≠ m → R p l → R p m → R q l → ¬ R q m)
    (C : Fin 4 → Finset (α ⊕ β))
    (clean : ∀ (f : α → Bool) (g : β → Bool),
      (∀ c : Fin 4, ∃ v ∈ C c, Sum.elim f g v = true) →
      ∃ p q, R p q ∧ f p = true ∧ g q = true) :
    ∃ P : Finset α, ∃ Q : Finset β, P.card + Q.card ≤ 2 ∧
      ∀ p q, (∀ c : Fin 4, Sum.inl p ∈ C c ∨ Sum.inr q ∈ C c) → p ∈ P ∨ q ∈ Q := by
  classical
  let H : α → β → Prop := fun p q => ∀ c : Fin 4, Sum.inl p ∈ C c ∨ Sum.inr q ∈ C c
  have edge_of_shadow (p : α) (q : β) (h : H p q) : R p q := by
    obtain ⟨a,b,hab,ha,hb⟩ := clean (fun a => decide (a = p)) (fun b => decide (b = q))
      (fun c => by
        rcases h c with hp | hq
        · exact ⟨Sum.inl p,hp,by simp⟩
        · exact ⟨Sum.inr q,hq,by simp⟩)
    simp only [decide_eq_true_eq] at ha hb
    subst a b
    exact hab
  apply PEqualNP.Outside.L_meta_2602_aux.MatchingCover.cover_two_of_no_matching_three H
  rintro ⟨P,Q,hP,hQ,hmatch⟩
  exact no_matching_three R noRect P Q hP hQ
    (fun i => edge_of_shadow (P i) (Q i) (hmatch i)) C (fun c i => hmatch i c) clean

end PEqualNP.Outside.L_meta_2602_aux.RectangleCNF
