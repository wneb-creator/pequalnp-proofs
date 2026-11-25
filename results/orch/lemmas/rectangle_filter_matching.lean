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


lemma no_two_filtered_edges_away_from_pair {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (noRect : ∀ p q l m, p ≠ q → l ≠ m → R p l → R p m → R q l → ¬ R q m)
    (P : Fin 3 → α) (Q : Fin 3 → β) (hP : Function.Injective P) (hQ : Function.Injective Q)
    (matching : ∀ i : Fin 3, R (P i) (Q i))
    (S T : Finset (α ⊕ β))
    (hitS : ∀ i : Fin 3, Sum.inl (P i) ∈ S ∨ Sum.inr (Q i) ∈ S)
    (hitT : ∀ i : Fin 3, Sum.inl (P i) ∈ T ∨ Sum.inr (Q i) ∈ T)
    (w₁ w₂ : α ⊕ β)
    (hw₁ : w₁ = Sum.inl (P 1) ∨ w₁ = Sum.inr (Q 1))
    (hw₂ : w₂ = Sum.inl (P 2) ∨ w₂ = Sum.inr (Q 2))
    (clean : ∀ (f : α → Bool) (g : β → Bool),
      (∃ v ∈ S, Sum.elim f g v = true) → (∃ v ∈ T, Sum.elim f g v = true) →
      (Sum.elim f g w₁ = true ∨ Sum.elim f g w₂ = true) →
      ∃ p q, R p q ∧ f p = true ∧ g q = true) : False := by
  classical
  let C : Fin 4 → Finset (α ⊕ β) :=
    ![S,T,{Sum.inl (P 0),w₁,w₂},{Sum.inr (Q 0),w₁,w₂}]
  have hits : ∀ c : Fin 4, ∀ i : Fin 3,
      Sum.inl (P i) ∈ C c ∨ Sum.inr (Q i) ∈ C c := by
    intro c i
    fin_cases c
    · exact hitS i
    · exact hitT i
    · fin_cases i
      · exact Or.inl (by simp [C])
      · rcases hw₁ with h | h
        · exact Or.inl (by simp [C,h])
        · exact Or.inr (by simp [C,h])
      · rcases hw₂ with h | h
        · exact Or.inl (by simp [C,h])
        · exact Or.inr (by simp [C,h])
    · fin_cases i
      · exact Or.inr (by simp [C])
      · rcases hw₁ with h | h
        · exact Or.inl (by simp [C,h])
        · exact Or.inr (by simp [C,h])
      · rcases hw₂ with h | h
        · exact Or.inl (by simp [C,h])
        · exact Or.inr (by simp [C,h])
  apply no_matching_three R noRect P Q hP hQ matching C hits
  intro f g pass
  have hs : ∃ v ∈ S, Sum.elim f g v = true := pass 0
  have ht : ∃ v ∈ T, Sum.elim f g v = true := pass 1
  have triple (a b c : α ⊕ β)
      (h : ∃ v ∈ ({a,b,c} : Finset (α ⊕ β)), Sum.elim f g v = true) :
      Sum.elim f g a = true ∨ Sum.elim f g b = true ∨ Sum.elim f g c = true := by
    obtain ⟨v,hv,hbit⟩ := h
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact Or.inl hbit
    · exact Or.inr (Or.inl hbit)
    · exact Or.inr (Or.inr hbit)
  have hp := triple (Sum.inl (P 0)) w₁ w₂ (pass 2)
  have hq := triple (Sum.inr (Q 0)) w₁ w₂ (pass 3)
  rcases hp with hp | h₁ | h₂
  · rcases hq with hq | h₁ | h₂
    · exact ⟨P 0,Q 0,matching 0,hp,hq⟩
    · exact clean f g hs ht (Or.inl h₁)
    · exact clean f g hs ht (Or.inr h₂)
  · exact clean f g hs ht (Or.inl h₁)
  · exact clean f g hs ht (Or.inr h₂)

end PEqualNP.Outside.L_meta_2602_aux.RectangleCNF
