import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17365

variable {α β : Type} [DecidableEq α] [DecidableEq β]

private def Bic (A : α → β → Bool) (R : Finset α) (C : Finset β) : Prop :=
  ∀ a ∈ R, ∀ b ∈ R, ∀ c ∈ C, ∀ d ∈ C,
    A a c = true → A b c = true → A a d = true → A b d = true

private def Twins (A : α → β → Bool) (R X : Finset α) (C Y : Finset β) : Prop :=
  (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ C, A a c = A b c) ∧
  (∀ a ∈ Y, ∀ b ∈ Y, ∀ r ∈ R, A r a = A r b)

-- One round can delete a class of equal rows and a class of equal columns.
private def Rank (A : α → β → Bool) : ℕ → Finset α → Finset β → Prop
  | 0, R, C => Bic A R C
  | n + 1, R, C => ∃ X ⊆ R, ∃ Y ⊆ C, Twins A R X C Y ∧ Rank A n (R \ X) (C \ Y)

private theorem rank_extend {A : α → β → Bool} {k : ℕ} {R S : Finset α} {C D : Finset β}
    (hS : S ⊆ R) (hD : D ⊆ C) (h : Rank A k S D)
    (hsub : Bic A (R \ S) (C \ D))
    (h1 : ∀ a ∈ S, ∀ b ∈ C \ D, A a b = false)
    (h2 : ∀ a ∈ R \ S, ∀ b ∈ D, A a b = false) : Rank A k R C := by
  induction k generalizing R S C D with
  | zero =>
    intro a ha b hb c hc d hd hac hbc had
    have key : ∀ x ∈ R, ∀ y ∈ C, A x y = true → (x ∈ S ↔ y ∈ D) := by
      intro x hx y hy hxy
      constructor
      · intro hxS
        by_contra hn
        rw [h1 x hxS y (Finset.mem_sdiff.2 ⟨hy, hn⟩)] at hxy
        contradiction
      · intro hyD
        by_contra hn
        rw [h2 x (Finset.mem_sdiff.2 ⟨hx, hn⟩) y hyD] at hxy
        contradiction
    have e1 := key a ha c hc hac
    have e2 := key b hb c hc hbc
    have e3 := key a ha d hd had
    by_cases hs : a ∈ S
    · exact h a hs b (e2.mpr (e1.mp hs)) c (e1.mp hs) d (e3.mp hs) hac hbc had
    · exact hsub a (Finset.mem_sdiff.2 ⟨ha, hs⟩)
        b (Finset.mem_sdiff.2 ⟨hb, hs ∘ e1.mpr ∘ e2.mp⟩)
        c (Finset.mem_sdiff.2 ⟨hc, hs ∘ e1.mpr⟩)
        d (Finset.mem_sdiff.2 ⟨hd, hs ∘ e3.mpr⟩) hac hbc had
  | succ k ih =>
    obtain ⟨X, hX, Y, hY, hT, h⟩ := h
    refine ⟨X, hX.trans hS, Y, hY.trans hD, ⟨?_, ?_⟩, ?_⟩
    · intro a ha b hb c hc
      by_cases hd : c ∈ D
      · exact hT.1 a ha b hb c hd
      · rw [h1 a (hX ha) c (Finset.mem_sdiff.2 ⟨hc, hd⟩), h1 b (hX hb) c (Finset.mem_sdiff.2 ⟨hc, hd⟩)]
    · intro a ha b hb r hr
      by_cases hs : r ∈ S
      · exact hT.2 a ha b hb r hs
      · rw [h2 r (Finset.mem_sdiff.2 ⟨hr, hs⟩) a (hY ha), h2 r (Finset.mem_sdiff.2 ⟨hr, hs⟩) b (hY hb)]
    · have eR : (R \ X) \ (S \ X) = R \ S := by
        ext a
        simp only [Finset.mem_sdiff]
        have := @hX a
        tauto
      have eC : (C \ Y) \ (D \ Y) = C \ D := by
        ext a
        simp only [Finset.mem_sdiff]
        have := @hY a
        tauto
      have Incl {T U V : Finset α} (h : T ⊆ U) : T \ V ⊆ U \ V :=
        fun _ hmem => Finset.mem_sdiff.2 ⟨h (Finset.mem_sdiff.1 hmem).1, (Finset.mem_sdiff.1 hmem).2⟩
      have Incl' {T U V : Finset β} (h : T ⊆ U) : T \ V ⊆ U \ V :=
        fun _ hmem => Finset.mem_sdiff.2 ⟨h (Finset.mem_sdiff.1 hmem).1, (Finset.mem_sdiff.1 hmem).2⟩
      apply ih (Incl hS) (Incl' hD) h
      · simpa only [eR, eC] using hsub
      · intro a ha b hb
        exact h1 a (Finset.mem_sdiff.1 ha).1 b (eC ▸ hb)
      · intro a ha b hb
        exact h2 a (eR ▸ ha) b (Finset.mem_sdiff.1 hb).1

private def Pairing (F : Finset ℕ → Bool) (A : α → β → Bool) (l : α → ℕ) (r : β → ℕ)
    (N : Finset ℕ) (R : Finset α) (C : Finset β) : Prop :=
  (∀ a ∈ R, l a ∈ N ∧ F {l a} = false) ∧
  (∀ b ∈ C, r b ∈ N ∧ F {r b} = false) ∧
  (∀ a ∈ R, ∀ b ∈ C, A a b = F {l a, r b})

private def Depends (F : Finset ℕ → Bool) (N : Finset ℕ) : Prop :=
  ∀ P Q : Finset ℕ, (∀ i ∈ N, i ∈ P ↔ i ∈ Q) → F P = F Q

private def Budgets (F : Finset ℕ → Bool) (N : Finset ℕ) (k : ℕ) : Prop :=
  ∀ {α β : Type} [DecidableEq α] [DecidableEq β] (A : α → β → Bool)
    (l : α → ℕ) (r : β → ℕ) (R : Finset α) (C : Finset β),
    Pairing F A l r N R C → Rank A k R C

private def avoid {γ : Type} (S : Finset γ) (w : γ → ℕ) (J : Finset ℕ) : Finset γ :=
  S.filter fun a => w a ∉ J

private theorem charge {F : Finset ℕ → Bool} {A : α → β → Bool} {l : α → ℕ} {r : β → ℕ}
    {N R C} (h : Pairing F A l r N R C) (J : Finset ℕ) {k : ℕ}
    (hk : Rank A k (avoid R l J) (avoid C r J)) : Rank A (k + J.card) R C := by
  induction J using Finset.induction_on generalizing R C with
  | empty => simpa [avoid] using hk
  | @insert j J hj ih =>
    let X := R.filter fun a => l a = j
    let Y := C.filter fun b => r b = j
    rw [Finset.card_insert_of_notMem hj, ← Nat.add_assoc]
    refine ⟨X, Finset.filter_subset _ _, Y, Finset.filter_subset _ _, ⟨?_, ?_⟩, ?_⟩
    · intro a ha b hb c hc
      obtain ⟨ha, e₁⟩ := Finset.mem_filter.1 ha
      obtain ⟨hb, e₂⟩ := Finset.mem_filter.1 hb
      rw [h.2.2 a ha c hc, h.2.2 b hb c hc, e₁, e₂]
    · intro a ha b hb c hc
      obtain ⟨ha, e₁⟩ := Finset.mem_filter.1 ha
      obtain ⟨hb, e₂⟩ := Finset.mem_filter.1 hb
      rw [h.2.2 c hc a ha, h.2.2 c hc b hb, e₁, e₂]
    · apply ih
      · exact ⟨fun a ha => h.1 a (Finset.mem_sdiff.1 ha).1,
          fun b hb => h.2.1 b (Finset.mem_sdiff.1 hb).1,
          fun a ha b hb => h.2.2 a (Finset.mem_sdiff.1 ha).1 b (Finset.mem_sdiff.1 hb).1⟩
      · have eR : avoid (R \ X) l J = avoid R l (insert j J) := by
          ext a
          simp only [avoid, X, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert]
          tauto
        have eC : avoid (C \ Y) r J = avoid C r (insert j J) := by
          ext a
          simp only [avoid, Y, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert]
          tauto
        rw [eR, eC]
        exact hk

private def put (t : ℕ) (b : Bool) (P : Finset ℕ) : Finset ℕ :=
  if b then insert t P else P.erase t

private def trigger (S : Finset ℕ) (isAnd : Bool) (P : Finset ℕ) : Bool :=
  if isAnd then decide (S ⊆ P) else decide (∃ i ∈ S, i ∈ P)

private theorem trigger_congr (S : Finset ℕ) (a : Bool) (P Q : Finset ℕ)
    (h : ∀ i ∈ S, i ∈ P ↔ i ∈ Q) : trigger S a P = trigger S a Q := by
  cases a
  · simp only [trigger, Bool.false_eq_true, ite_false, decide_eq_decide]
    exact exists_congr fun i => and_congr_right (h i)
  · simp only [trigger, ite_true, decide_eq_decide]
    exact forall_congr' fun i => imp_congr_right (h i)

private theorem trigger_zero (S : Finset ℕ) (a : Bool)
    (ha : a = true → S.card = 2) : trigger S a ∅ = false := by
  cases a
  · simp [trigger]
  · have h : S ≠ ∅ := fun e => by simpa [e] using ha rfl
    simp [trigger, h]

private theorem put_mem_self (t : ℕ) (b : Bool) (P : Finset ℕ) :
    t ∈ put t b P ↔ b = true := by cases b <;> simp [put]

private theorem put_mem_other {i t : ℕ} (h : i ≠ t) (b : Bool) (P : Finset ℕ) :
    i ∈ put t b P ↔ i ∈ P := by cases b <;> simp [put, h]

private theorem replace_depends {F : Finset ℕ → Bool} {N S : Finset ℕ} {t : ℕ} {a : Bool}
    (hd : Depends F N) : Depends (fun P => F (put t (trigger S a P) P)) (N.erase t ∪ S) := by
  intro P Q hPQ
  apply hd
  intro i hi
  by_cases h : i = t
  · subst i
    rw [put_mem_self, put_mem_self, trigger_congr S a P Q (fun i hi => hPQ i (Finset.mem_union_right _ hi))]
  · rw [put_mem_other h, put_mem_other h]
    exact hPQ i (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨h, hi⟩))

private theorem ignored_update {F : Finset ℕ → Bool} {N : Finset ℕ} {t : ℕ}
    (hd : Depends F N) (ht : t ∉ N) (P : Finset ℕ) (b : Bool) : F (put t b P) = F P := by
  apply hd
  intro i hi
  have hn : i ≠ t := fun e => ht (e ▸ hi)
  exact put_mem_other hn b P

private theorem or_pair {F : Finset ℕ → Bool} {N S : Finset ℕ} {t u v : ℕ}
    (hd : Depends F N) (ht : t ∈ N)
    (hu : u ∈ N.erase t ∪ S) (hv : v ∈ N.erase t ∪ S)
    (hu' : u ∉ N.erase t ∩ S) (hv' : v ∉ N.erase t ∩ S) :
    let m (w : ℕ) := if w ∈ S then t else w
    m u ∈ N ∧ m v ∈ N ∧ F (put t (trigger S false {u,v}) {u,v}) = F {m u,m v} := by
  dsimp
  have hm : ∀ w ∈ N.erase t ∪ S, (if w ∈ S then t else w) ∈ N := by
    intro w hw
    split_ifs with hh
    · exact ht
    · exact (Finset.mem_erase.1 ((Finset.mem_union.1 hw).resolve_right hh)).2
  refine ⟨hm u hu, hm v hv, ?_⟩
  apply hd
  intro i hi
  have mt : ∀ w ∈ N.erase t ∪ S, (if w ∈ S then t else w) = t ↔ w ∈ S := by
    intro w hw
    by_cases hh : w ∈ S
    · simp [hh]
    · have hne := (Finset.mem_erase.1 ((Finset.mem_union.1 hw).resolve_right hh)).1
      simp [hh, hne]
  have mo : ∀ w, w ∉ N.erase t ∩ S → i ≠ t →
      (i = (if w ∈ S then t else w) ↔ i = w) := by
    intro w hw hn
    by_cases hS : w ∈ S
    · have hw' : i ≠ w := fun e => hw (Finset.mem_inter.2 ⟨Finset.mem_erase.2 ⟨e ▸ hn, e ▸ hi⟩, hS⟩)
      simp [hS, hn, hw']
    · simp [hS]
  by_cases he : i = t
  · subst i
    rw [put_mem_self]
    simp only [trigger, Bool.false_eq_true, ite_false, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
    rw [eq_comm (a := t) (b := if u ∈ S then t else u),
      eq_comm (a := t) (b := if v ∈ S then t else v), mt u hu, mt v hv]
    constructor
    · rintro ⟨j, hj, (rfl | rfl)⟩
      · exact Or.inl hj
      · exact Or.inr hj
    · rintro (h | h)
      · exact ⟨u, h, Or.inl rfl⟩
      · exact ⟨v, h, Or.inr rfl⟩
  · rw [put_mem_other he]
    simp only [Finset.mem_insert, Finset.mem_singleton, mo u hu' he, mo v hv' he]

private theorem and_pair {F : Finset ℕ → Bool} {N S : Finset ℕ} {t u v : ℕ}
    (hd : Depends F N) (hS : S.card = 2) (htS : t ∉ S)
    (hu : u ∈ N.erase t ∪ S) (hv : v ∈ N.erase t ∪ S)
    (hu' : u ∉ N.erase t ∩ S) (hv' : v ∉ N.erase t ∩ S) :
    F (put t (trigger S true {u,v}) {u,v}) =
      if u ∈ S then
        if v ∈ S then (if S ⊆ {u,v} then F {t} else F ∅) else F {v}
      else if v ∈ S then F {u} else F {u,v} := by
  have ht : t ≠ u ∧ t ≠ v := by
    constructor
    · rintro rfl
      exact (Finset.mem_union.1 hu).elim (by simp) htS
    · rintro rfl
      exact (Finset.mem_union.1 hv).elim (by simp) htS
  have hnot : ∀ w : ℕ, ¬ S ⊆ {w} := by
    intro w hn
    have := Finset.card_le_card hn
    simp [hS] at this
  have htno : ∀ i ∈ N, i ≠ t → i ≠ u ∨ u ∉ S := by
    intro i hi hit
    by_cases d : i = u
    · subst i
      exact Or.inr (fun h => hu' (Finset.mem_inter.2 ⟨Finset.mem_erase.2 ⟨hit, hi⟩, h⟩))
    · exact Or.inl d
  have htno' : ∀ i ∈ N, i ≠ t → i ≠ v ∨ v ∉ S := by
    intro i hi hit
    by_cases d : i = v
    · subst i
      exact Or.inr (fun h => hv' (Finset.mem_inter.2 ⟨Finset.mem_erase.2 ⟨hit, hi⟩, h⟩))
    · exact Or.inl d
  have off : u ∉ S ∨ v ∉ S → ¬ S ⊆ ({u,v} : Finset ℕ) := by
    rintro (h | h) hs
    · apply hnot v
      intro x hx
      have := hs hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      exact this.resolve_left (fun e => h (e ▸ hx))
    · apply hnot u
      intro x hx
      have := hs hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      exact this.resolve_right (fun e => h (e ▸ hx))
  by_cases huS : u ∈ S <;> by_cases hvS : v ∈ S
  · simp only [huS, hvS, ite_true]
    split_ifs with e
    · apply hd
      intro i hi
      by_cases ht' : i = t
      · subst i
        simp [put_mem_self, trigger, e]
      · rw [put_mem_other ht']
        have h₁ := (htno i hi ht').resolve_right (not_not_intro huS)
        have h₂ := (htno' i hi ht').resolve_right (not_not_intro hvS)
        simp [h₁, h₂, ht']
    · apply hd
      intro i hi
      by_cases ht' : i = t
      · subst i
        simp [put_mem_self, trigger, e]
      · rw [put_mem_other ht']
        have h₁ := (htno i hi ht').resolve_right (not_not_intro huS)
        have h₂ := (htno' i hi ht').resolve_right (not_not_intro hvS)
        simp [h₁, h₂]
  · simp only [huS, hvS, ite_true, ite_false]
    apply hd
    intro i hi
    by_cases ht' : i = t
    · subst i
      simp [put_mem_self, trigger, off (Or.inr hvS), ht.2]
    · rw [put_mem_other ht']
      have h₁ := (htno i hi ht').resolve_right (not_not_intro huS)
      simp [h₁]
  · simp only [huS, hvS, ite_true, ite_false]
    apply hd
    intro i hi
    by_cases ht' : i = t
    · subst i
      simp [put_mem_self, trigger, off (Or.inl huS), ht.1]
    · rw [put_mem_other ht']
      have h₂ := (htno' i hi ht').resolve_right (not_not_intro hvS)
      simp [h₂]
  · simp only [huS, hvS, ite_false]
    apply hd
    intro i hi
    by_cases ht' : i = t
    · subst i
      simp [put_mem_self, trigger, off (Or.inl huS), ht.1, ht.2]
    · exact put_mem_other ht' _ _

-- Shared operands spend deletion rounds. Fresh OR operands merge into the old
-- label, and the fresh AND operands contribute only isolated rectangles.
private theorem replace_budget {F : Finset ℕ → Bool} {N S : Finset ℕ} {t k : ℕ} {a : Bool}
    (hd : Depends F N) (h0 : F ∅ = false) (hB : Budgets F N k)
    (ht : t ∈ N) (htS : t ∉ S) (ha : a = true → S.card = 2) :
    Budgets (fun P => F (put t (trigger S a P) P)) (N.erase t ∪ S) (k + (N.erase t ∩ S).card) := by
  intro α β _ _ A l r R C h
  let J := N.erase t ∩ S
  apply charge h J
  let R' := avoid R l J
  let C' := avoid C r J
  have hL : ∀ i ∈ R', l i ∈ N.erase t ∪ S ∧ l i ∉ J := fun i hi =>
    ⟨(h.1 i (Finset.mem_filter.1 hi).1).1, (Finset.mem_filter.1 hi).2⟩
  have hR : ∀ j ∈ C', r j ∈ N.erase t ∪ S ∧ r j ∉ J := fun j hj =>
    ⟨(h.2.1 j (Finset.mem_filter.1 hj).1).1, (Finset.mem_filter.1 hj).2⟩
  have hLS : ∀ i ∈ R', F (put t (trigger S a {l i}) {l i}) = false := fun i hi =>
    (h.1 i (Finset.mem_filter.1 hi).1).2
  have hRS : ∀ j ∈ C', F (put t (trigger S a {r j}) {r j}) = false := fun j hj =>
    (h.2.1 j (Finset.mem_filter.1 hj).1).2
  have hP : ∀ i ∈ R', ∀ j ∈ C', A i j = F (put t (trigger S a {l i,r j}) {l i,r j}) := fun i hi j hj =>
    h.2.2 i (Finset.mem_filter.1 hi).1 j (Finset.mem_filter.1 hj).1
  cases a
  · let m (w : ℕ) := if w ∈ S then t else w
    apply hB A (m ∘ l) (m ∘ r) R' C'
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have e := or_pair hd ht (hL i hi).1 (hL i hi).1 (hL i hi).2 (hL i hi).2
      have q : F (put t (trigger S false {l i}) {l i}) = F {m (l i)} := by
        simpa [m] using e.2.2
      exact ⟨e.1, q.symm.trans (hLS i hi)⟩
    · intro j hj
      have e := or_pair hd ht (hR j hj).1 (hR j hj).1 (hR j hj).2 (hR j hj).2
      have q : F (put t (trigger S false {r j}) {r j}) = F {m (r j)} := by
        simpa [m] using e.2.2
      exact ⟨e.1, q.symm.trans (hRS j hj)⟩
    · intro i hi j hj
      exact (hP i hi j hj).trans (or_pair hd ht (hL i hi).1 (hR j hj).1 (hL i hi).2 (hR j hj).2).2.2
  · have hS := ha rfl
    let X := avoid R' l S
    let Y := avoid C' r S
    let e u v hu hv hu' hv' := and_pair (u := u) (v := v) hd hS htS hu hv hu' hv'
    have lzero : ∀ i ∈ X, F {l i} = false := by
      intro i hi
      obtain ⟨hr, hs⟩ := Finset.mem_filter.1 hi
      have q := e (l i) (l i) (hL i hr).1 (hL i hr).1 (hL i hr).2 (hL i hr).2
      have q' : F (put t (trigger S true {l i}) {l i}) = F {l i} := by simpa [hs] using q
      exact q'.symm.trans (hLS i hr)
    have rzero : ∀ j ∈ Y, F {r j} = false := by
      intro j hj
      obtain ⟨hr, hs⟩ := Finset.mem_filter.1 hj
      have q := e (r j) (r j) (hR j hr).1 (hR j hr).1 (hR j hr).2 (hR j hr).2
      have q' : F (put t (trigger S true {r j}) {r j}) = F {r j} := by simpa [hs] using q
      exact q'.symm.trans (hRS j hr)
    have hX : X ⊆ R' := Finset.filter_subset _ _
    have hY : Y ⊆ C' := Finset.filter_subset _ _
    have hx : ∀ i ∈ R' \ X, l i ∈ S := by
      intro i hi
      by_contra hn
      exact (Finset.mem_sdiff.1 hi).2 (Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 hi).1, hn⟩)
    have hy : ∀ j ∈ C' \ Y, r j ∈ S := by
      intro j hj
      by_contra hn
      exact (Finset.mem_sdiff.1 hj).2 (Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 hj).1, hn⟩)
    have evalP : ∀ i ∈ R', ∀ j ∈ C', A i j =
        if l i ∈ S then if r j ∈ S then (if S ⊆ {l i,r j} then F {t} else F ∅) else F {r j}
        else if r j ∈ S then F {l i} else F {l i,r j} := by
      intro i hi j hj
      exact (hP i hi j hj).trans (e _ _ (hL i hi).1 (hR j hj).1 (hL i hi).2 (hR j hj).2)
    apply rank_extend hX hY (hB A l r X Y ?_)
    · intro a ha b hb c hc d hd' hac hbc had
      have E : ∀ i ∈ R' \ X, ∀ j ∈ C' \ Y, A i j = (if S ⊆ {l i,r j} then F {t} else false) := by
        intro i hi j hj
        simpa [hx i hi, hy j hj, h0] using evalP i (Finset.mem_sdiff.1 hi).1 j (Finset.mem_sdiff.1 hj).1
      rw [E a ha c hc] at hac
      rw [E a ha d hd'] at had
      rw [E b hb c hc] at hbc
      rw [E b hb d hd']
      have h₁ : S ⊆ ({l a,r c} : Finset ℕ) := by
        by_contra e
        simp [e] at hac
      have h₂ : S ⊆ ({l a,r d} : Finset ℕ) := by
        by_contra e
        simp [e] at had
      have same : ({l a,r c} : Finset ℕ) = {l a,r d} := by
        have eq : ∀ x y : ℕ, S ⊆ {x,y} → S = {x,y} := by
          intro x y hxy
          apply Finset.eq_of_subset_of_card_le hxy
          rw [hS]
          exact le_trans (Finset.card_insert_le _ _) (by simp)
        exact (eq _ _ h₁).symm.trans (eq _ _ h₂)
      have neq : r d ≠ l a := by
        intro he
        have := Finset.card_le_card h₂
        simp [he, hS] at this
      have hr' : r d = r c := by
        have hm : r d ∈ ({l a,r c} : Finset ℕ) := by rw [same]; simp
        exact (Finset.mem_insert.1 hm).resolve_left neq |> Finset.mem_singleton.1
      simpa only [hr'] using hbc
    · intro i hi j hj
      simpa [(Finset.mem_filter.1 hi).2, hy j hj, lzero i hi] using
        evalP i (hX hi) j (Finset.mem_sdiff.1 hj).1
    · intro i hi j hj
      simpa [hx i hi, (Finset.mem_filter.1 hj).2, rzero j hj] using
        evalP i (Finset.mem_sdiff.1 hi).1 j (hY hj)
    · refine ⟨?_, ?_, ?_⟩
      · intro i hi
        have nue := (Finset.mem_filter.1 hi).2
        exact ⟨(Finset.mem_erase.1 ((Finset.mem_union.1 (hL i (hX hi)).1).resolve_right nue)).2, lzero i hi⟩
      · intro j hj
        have nue := (Finset.mem_filter.1 hj).2
        exact ⟨(Finset.mem_erase.1 ((Finset.mem_union.1 (hR j (hY hj)).1).resolve_right nue)).2, rzero j hj⟩
      · intro i hi j hj
        simpa [(Finset.mem_filter.1 hi).2, (Finset.mem_filter.1 hj).2] using evalP i (hX hi) j (hY hj)


-- For distinct equal rows, at most one common column needs deletion to
-- disconnect the class from every other row.

-- The general gate-budget argument above and its circuit simulation below follow
-- L-meta-10055. The zero-edge estimate specializes that budget to sparse complements.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def wiresFrom (gs : List Gate) (x : List Bool) : List Bool :=
  (⟨gs, 0⟩ : Circuit).wires x

private theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst i; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private def run : List Gate → ℕ → (ℕ → Bool) → ℕ → Bool
  | [], _, x => x
  | g :: gs, t, x => run gs (t + 1) (Function.update x t (g.op.eval (g.inputs.map x)))

private theorem run_eq (gs : List Gate) : ∀ w : List Bool, ∀ i,
    (wiresFrom gs w).getD i false = run gs w.length (fun j => w.getD j false) i := by
  induction gs with
  | nil => intro w i; rfl
  | cons g gs ih =>
    intro w i
    have e : wiresFrom (g :: gs) w =
        wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [e, ih, List.length_append, List.length_singleton, run]
    congr 2
    funext j
    rw [getD_snoc, Function.update_apply]

private theorem op_mono (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (S T : ℕ → Bool) (h : ∀ i, S i = true → T i = true)
    (he : g.op.eval (g.inputs.map S) = true) : g.op.eval (g.inputs.map T) = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop <;> rw [hop] at he ⊢
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at he ⊢
    exact fun i hi => h i (he i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at he ⊢
    obtain ⟨i, hi, hv⟩ := he
    exact ⟨i, hi, h i hv⟩

private theorem run_mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    ∀ t (x y : ℕ → Bool), (∀ i, x i = true → y i = true) →
      ∀ o, run gs t x o = true → run gs t y o = true := by
  induction gs with
  | nil => exact fun _ x y h o => h o
  | cons g gs ih =>
    intro t x y h o
    simp only [run]
    apply ih (fun g' h' => hg g' (List.mem_cons_of_mem _ h')) _ _ _ _ o
    intro i
    by_cases hi : i = t
    · subst i
      simpa using op_mono g (hg g (by simp)) x y h
    · simpa only [Function.update_of_ne hi] using h i

-- The cut records changes from the all-zero evaluation of the earlier gates.
private def readCut (b : List Bool) (P : Finset ℕ) (i : ℕ) : Bool :=
  b.getD i false || decide (i < b.length ∧ i ∈ P)

private def cut (gs : List Gate) (b : List Bool) (o : ℕ) (P : Finset ℕ) : Bool :=
  run gs b.length (readCut b P) o

private theorem cut_mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (b : List Bool) (o : ℕ) {P Q : Finset ℕ} (h : P ⊆ Q) : cut gs b o P = true → cut gs b o Q = true := by
  apply run_mono gs hg
  intro i
  simp only [readCut, Bool.or_eq_true, decide_eq_true_eq]
  rintro (hi | ⟨hlt, hp⟩)
  · exact Or.inl hi
  · exact Or.inr ⟨hlt, h hp⟩

private theorem readCut_snoc (b : List Bool) (v : Bool) (P : Finset ℕ) (e : Bool) :
    readCut (b ++ [v]) (put b.length e P) = Function.update (readCut b P) b.length (v || e) := by
  funext i
  unfold readCut
  rw [getD_snoc, Function.update_apply]
  split_ifs with hi
  · subst i
    simp [put_mem_self]
  · have hh : i < b.length + 1 ↔ i < b.length := by omega
    simp [hh, put_mem_other hi]

private abbrev Atom := ℕ ⊕ Bool

private def readAtom (b : List Bool) (i : ℕ) : Atom :=
  if b.getD i false then .inr true else if i < b.length then .inl i else .inr false

private def val (P : Finset ℕ) : Atom → Bool
  | .inl i => decide (i ∈ P)
  | .inr b => b

private theorem val_atom (b : List Bool) (i : ℕ) (P : Finset ℕ) :
    val P (readAtom b i) = readCut b P i := by
  unfold readAtom readCut
  by_cases h : b.getD i false = true
  · simp only [h, ite_true, val, Bool.true_or]
  · have h' : b.getD i false = false := by
      cases e : b.getD i false
      · rfl
      · exact (h e).elim
    rw [h']
    by_cases e : i < b.length
    · simp only [Bool.false_eq_true, ite_false, e, ite_true, val, Bool.false_or, true_and]
    · simp only [Bool.false_eq_true, ite_false, e, val, Bool.false_or, false_and, decide_false]

private theorem atom_lt (b : List Bool) (i x : ℕ) (h : readAtom b i = .inl x) : x < b.length := by
  unfold readAtom at h
  split_ifs at h with h₁ h₂; simp_all

private def Normal (t : ℕ) (f : Finset ℕ → Bool) : Prop :=
  ∃ v : Bool, ∃ S : Finset ℕ, ∃ a : Bool,
    (∀ i ∈ S, i < t) ∧ S.card ≤ 2 ∧ (a = true → S.card = 2) ∧
    ∀ P, f P = (v || trigger S a P)

private theorem norm_const (t : ℕ) (v : Bool) : Normal t (fun _ => v) := by
  refine ⟨v, ∅, false, ?_, by simp, by simp, ?_⟩
  · simp
  · intro P; simp [trigger]

private theorem norm_atom (t : ℕ) (x : Atom) (hx : ∀ i, x = .inl i → i < t) :
    Normal t (fun P => val P x) := by
  cases x with
  | inr b => exact norm_const t b
  | inl i =>
    refine ⟨false, {i}, false, ?_, by simp, by simp, ?_⟩
    · intro j hj
      have e := Finset.mem_singleton.1 hj
      exact hx j (congrArg Sum.inl e.symm)
    · intro P; simp [trigger, val]

private def combine (a : Bool) (p q : Bool) : Bool := if a then p && q else p || q

private theorem norm_two (t : ℕ) (a : Bool) (x y : Atom)
    (hx : ∀ i, x = .inl i → i < t) (hy : ∀ i, y = .inl i → i < t) :
    Normal t (fun P => combine a (val P x) (val P y)) := by
  cases x with
  | inr b =>
    cases a <;> cases b
    · simpa [combine, val] using norm_atom t y hy
    · simpa [combine, val] using norm_const t true
    · simpa [combine, val] using norm_const t false
    · simpa [combine, val] using norm_atom t y hy
  | inl p =>
    cases y with
    | inr b =>
      cases a <;> cases b
      · simpa [combine, val] using norm_atom t (.inl p) hx
      · simpa [combine, val] using norm_const t true
      · simpa [combine, val] using norm_const t false
      · simpa [combine, val] using norm_atom t (.inl p) hx
    | inl q =>
      by_cases e : p = q
      · subst q
        cases a <;> simpa [combine] using norm_atom t (.inl p) hx
      · refine ⟨false, {p,q}, a, ?_, by simp [e], fun _ => by simp [e], ?_⟩
        · intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl
          · exact hx _ rfl
          · exact hy _ rfl
        · intro P
          cases a <;> simp [combine, val, trigger, Finset.insert_subset_iff, Finset.singleton_subset_iff]

private theorem norm_gate (b : List Bool) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    Normal b.length (fun P => g.op.eval (g.inputs.map (readCut b P))) := by
  rcases g with ⟨op, l⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with ⟨hop, hl⟩
  rcases l with _ | ⟨p, _ | ⟨q, l⟩⟩
  · rcases hop with rfl | rfl
    · exact norm_const _ true
    · exact norm_const _ false
  · rcases hop with rfl | rfl <;>
      simpa [GateOp.eval, val_atom] using norm_atom b.length (readAtom b p) (atom_lt b p)
  · have e : l = [] := by
      cases l with
      | nil => rfl
      | cons u l =>
        simp only [List.length_cons] at hl
        omega
    subst l
    rcases hop with rfl | rfl
    · simpa [GateOp.eval, combine, val_atom] using
        norm_two b.length true (readAtom b p) (readAtom b q) (atom_lt b p) (atom_lt b q)
    · simpa [GateOp.eval, combine, val_atom] using
        norm_two b.length false (readAtom b p) (readAtom b q) (atom_lt b p) (atom_lt b q)

private theorem cut_normal (gs : List Gate) (b : List Bool) (o : ℕ) (g : Gate)
    (v : Bool) (S : Finset ℕ) (a : Bool)
    (he : ∀ P, g.op.eval (g.inputs.map (readCut b P)) = (v || trigger S a P)) :
    cut (g :: gs) b o = fun P => cut gs (b ++ [v]) o (put b.length (trigger S a P) P) := by
  funext P
  simp only [cut, run, List.length_append, List.length_singleton, readCut_snoc, he]

-- Each gate increases the dependency count plus deletion budget by at most one.
private theorem cut_budget (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ b o, cut gs b o ∅ = false → ∃ N : Finset ℕ, ∃ k : ℕ,
    Depends (cut gs b o) N ∧ Budgets (cut gs b o) N k ∧ N.card + k ≤ gs.length + 1 := by
  induction gs with
  | nil =>
    intro b o h0
    refine ⟨{o}, 0, ?_, ?_, by simp⟩
    · intro P Q he
      have e := he o (Finset.mem_singleton_self _)
      unfold cut run readCut
      have hh : (o < b.length ∧ o ∈ P) ↔ (o < b.length ∧ o ∈ Q) := by rw [e]
      rw [decide_eq_decide.2 hh]
    · intro α β _ _ A l r R C h i hi j hj c hc d hd e₁ e₂ e₃
      have ho := (h.2.2 i hi c hc).symm.trans e₁
      have hli : l i = o := Finset.mem_singleton.1 (h.1 i hi).1
      have hrc : r c = o := Finset.mem_singleton.1 (h.2.1 c hc).1
      have hf := (h.1 i hi).2
      rw [hli] at hf
      have ht : cut [] b o {o} = true := by simpa [hli, hrc] using ho
      exact Bool.false_ne_true (hf.symm.trans ht) |>.elim
  | cons g gs ih =>
    intro b o h0
    obtain ⟨v, S, a, hS, hS2, ha, he⟩ := norm_gate b g (hg g (by simp))
    have eq := cut_normal gs b o g v S a he
    rw [eq] at h0 ⊢
    have h0' : cut gs (b ++ [v]) o ∅ = false := by
      simpa [trigger_zero S a ha, put] using h0
    obtain ⟨N, k, hd, hb, hsz⟩ := ih (fun h hh => hg h (List.mem_cons_of_mem _ hh)) _ _ h0'
    by_cases ht : b.length ∈ N
    · have htS : b.length ∉ S := fun h => (Nat.lt_irrefl _ (hS _ h))
      refine ⟨N.erase b.length ∪ S, k + (N.erase b.length ∩ S).card,
        replace_depends hd, replace_budget hd h0' hb ht htS ha, ?_⟩
      have h₁ := Finset.card_union_add_card_inter (N.erase b.length) S
      have h₂ := Finset.card_erase_of_mem ht
      have h₃ : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
      simp only [List.length_cons]
      omega
    · have e : (fun P => cut gs (b ++ [v]) o (put b.length (trigger S a P) P)) = cut gs (b ++ [v]) o := by
        funext P
        exact ignored_update hd ht P _
      rw [e]
      exact ⟨N, k, hd, hb, by simp only [List.length_cons]; omega⟩

private def inp (N : ℕ) (P : Finset ℕ) : List Bool := List.ofFn fun i : Fin N => decide ((i : ℕ) ∈ P)

private theorem inp_getD (N : ℕ) (P : Finset ℕ) (i : ℕ) :
    (inp N P).getD i false = decide (i < N ∧ i ∈ P) := by
  unfold inp
  by_cases h : i < N <;> simp [List.getD_eq_getElem?_getD, h]

private theorem oneEach_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    oneEach u v = inp (n + m) {(u : ℕ), n + (v : ℕ)} := by
  have hu := u.2
  have hv := v.2
  apply List.ext_getElem
  · simp [oneEach, inp]
  · intro i h1 h2
    simp only [oneEach, inp, List.length_append, List.length_ofFn] at h1 h2 ⊢
    by_cases hi : i < n
    · rw [List.getElem_append_left (by simpa using hi)]
      simp only [List.getElem_ofFn, Fin.ext_iff, Finset.mem_insert, Finset.mem_singleton,
        decide_eq_decide]
      omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff, Finset.mem_insert, Finset.mem_singleton,
        decide_eq_decide]
      omega

private theorem see_pair (C : Circuit) {n m : ℕ} (i : Fin n) (j : Fin m) : C.eval (oneEach i j) =
    cut C.gates (List.replicate (n + m) false) C.output {i.val, n + j.val} := by
  rw [oneEach_eq]
  change (wiresFrom C.gates (inp (n + m) _)).getD C.output false = _
  rw [run_eq]
  unfold cut
  have hlen : (inp (n + m) {i.val,n + j.val}).length = (n + m) := by simp [inp]
  rw [hlen, List.length_replicate]
  congr 2
  funext k
  rw [inp_getD]
  have hoff : ∀ n w, (List.replicate n false).getD w false = false := by
    intro n
    induction n with
    | zero => intro w; simp [List.getD_eq_getElem?_getD]
    | succ n ih =>
      intro w
      cases w with
      | zero => simp [List.replicate_succ, List.getD_eq_getElem?_getD]
      | succ w => simp [List.replicate_succ, List.getD_eq_getElem?_getD]
  simp only [readCut, hoff, List.length_replicate, Bool.false_or]


private theorem full_matrix_rank {n m s : ℕ} (hn : 0 < n) (A : Fin n → Fin m → Bool)
    (rows_vary : ∀ a, (∃ b, A a b = true) ∧ (∃ b, A a b = false))
    (cols_vary : ∀ b, (∃ a, A a b = true) ∧ (∃ a, A a b = false))
    (h : RepSizeAtMost A s) : ∃ t, Rank A t Finset.univ Finset.univ ∧ n + m + t ≤ s + 1 := by
  revert h
  rintro ⟨C, hg, hs, hrep⟩
  let F := cut C.gates (List.replicate (n + m) false) C.output
  have hm : ∀ {P Q}, P ⊆ Q → F P = true → F Q = true :=
    fun h => cut_mono C.gates (fun g hg' => (hg g hg').1) _ _ h
  have hv : ∀ (a : Fin n) (b : Fin m), F {a.val, n + b.val} = A a b := by
    intro a b
    change cut C.gates (List.replicate (n + m) false) C.output {a.val, n + b.val} = A a b
    rw [← see_pair]
    exact hrep a b
  have hS₁ : ∀ a : Fin n, F {a.val} = false := by
    intro a
    obtain ⟨b, hb⟩ := (rows_vary a).2
    rw [← Bool.not_eq_true]
    intro h
    have h' := hm (Q := {a.val, n + b.val}) (by simp) h
    rw [hv, hb] at h'
    contradiction
  have hS₂ : ∀ b : Fin m, F {n + b.val} = false := by
    intro b
    obtain ⟨a, ha⟩ := (cols_vary b).2
    rw [← Bool.not_eq_true]
    intro h
    have h' := hm (Q := {a.val, n + b.val}) (by simp) h
    rw [hv, ha] at h'
    contradiction
  have h0 : F ∅ = false := by
    rw [← Bool.not_eq_true]
    intro h
    have h' := hm (Q := {0}) (by simp) h
    have e := hS₁ ⟨0, hn⟩
    exact Bool.false_ne_true (e.symm.trans h')
  obtain ⟨N, t, hd, hb, hsN⟩ := cut_budget C.gates hg _ _ h0
  have hN₁ : ∀ a : Fin n, a.val ∈ N := by
    intro a
    obtain ⟨b, hb⟩ := (rows_vary a).1
    by_contra h
    have e : F {a.val, n + b.val} = F {n + b.val} := by
      apply hd
      intro i hi
      have hne : i ≠ a.val := fun e => h (e ▸ hi)
      simp [hne]
    rw [hv, hb, hS₂] at e
    contradiction
  have hN₂ : ∀ b : Fin m, n + b.val ∈ N := by
    intro b
    obtain ⟨a, ha⟩ := (cols_vary b).1
    by_contra h
    have e : F {a.val, n + b.val} = F {a.val} := by
      apply hd
      intro i hi
      have hne : i ≠ n + b.val := fun e => h (e ▸ hi)
      simp [hne]
    rw [hv, ha, hS₁] at e
    contradiction
  have hN : Finset.range (n + m) ⊆ N := by
    intro i hi
    have hh := Finset.mem_range.1 hi
    by_cases h : i < n
    · exact hN₁ ⟨i, h⟩
    · have hey := hN₂ ⟨i - n, by omega⟩
      simpa [Nat.add_sub_of_le (by omega : n ≤ i)] using hey
  have hc := Finset.card_le_card hN
  rw [Finset.card_range] at hc
  have hsz : C.gates.length ≤ s := hs
  have hR := hb A Fin.val (fun b => n + b.val) Finset.univ Finset.univ
    ⟨fun a _ => ⟨hN₁ a, hS₁ a⟩, fun b _ => ⟨hN₂ b, hS₂ b⟩, fun a _ b _ => (hv a b).symm⟩
  exact ⟨t,hR,by omega⟩

section Sparse
variable [Fintype α] [Fintype β]

private def zeros (A : α → β → Bool) (R : Finset α) (C : Finset β) :=
  (R ×ˢ C).filter fun p => A p.1 p.2 = false

-- A zero rectangle in a C₄-free graph of maximum degree two has at most two edges.
private theorem rectangle_bound (A : α → β → Bool)
    (hrow : ∀ r, (Finset.univ.filter fun c => A r c = false).card ≤ 2)
    (hcol : ∀ c, (Finset.univ.filter fun r => A r c = false).card ≤ 2)
    (hsq : ∀ r s c d, A r c = false → A r d = false → A s c = false →
      A s d = false → r = s ∨ c = d)
    {R : Finset α} {C : Finset β} (h : ∀ r ∈ R, ∀ c ∈ C, A r c = false) :
    (R ×ˢ C).card ≤ 2 := by
  rcases R.eq_empty_or_nonempty with hr | ⟨r, hr⟩
  · simp [hr]
  rcases C.eq_empty_or_nonempty with hc | ⟨c, hc⟩
  · simp [hc]
  have hR : R.card ≤ 2 := (Finset.card_le_card (show R ⊆ _ from
    fun s hs => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h s hs c hc⟩)).trans (hcol c)
  have hC : C.card ≤ 2 := (Finset.card_le_card (show C ⊆ _ from
    fun d hd => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h r hr d hd⟩)).trans (hrow r)
  rw [Finset.card_product]
  by_cases h₁ : R.card ≤ 1
  · exact (Nat.mul_le_mul h₁ hC).trans (by decide)
  obtain ⟨r₁, hr₁, r₂, hr₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < R.card)
  have hs : C ⊆ {c} := by
    intro d hd
    exact Finset.mem_singleton.mpr ((hsq r₁ r₂ d c (h _ hr₁ _ hd) (h _ hr₁ _ hc)
      (h _ hr₂ _ hd) (h _ hr₂ _ hc)).resolve_left hne)
  have hC' : C.card ≤ 1 := by simpa using Finset.card_le_card hs
  exact (Nat.mul_le_mul hR hC').trans (by decide)

private theorem twin_rows_bound (A : α → β → Bool) {X : Finset α} {C : Finset β}
    (ht : ∀ r ∈ X, ∀ s ∈ X, ∀ c ∈ C, A r c = A s c)
    (hr : ∀ (S : Finset α) (T : Finset β), (∀ r ∈ S, ∀ c ∈ T, A r c = false) →
      (S ×ˢ T).card ≤ 2) : (zeros A X C).card ≤ 2 := by
  rcases X.eq_empty_or_nonempty with hx | ⟨x, hx⟩
  · simp [zeros, hx]
  let T := C.filter fun c => A x c = false
  have he : zeros A X C ⊆ X ×ˢ T := by
    rintro ⟨r,c⟩ hp
    obtain ⟨⟨h₁,h₂⟩, h₃⟩ := (show (r ∈ X ∧ c ∈ C) ∧ A r c = false by simpa [zeros] using hp)
    exact Finset.mem_product.mpr ⟨h₁, Finset.mem_filter.mpr ⟨h₂,(ht x hx r h₁ c h₂).trans h₃⟩⟩
  apply (Finset.card_le_card he).trans (hr X T ?_)
  intro r h₁ c hc
  obtain ⟨h₂, h₃⟩ := Finset.mem_filter.mp hc
  exact (ht r h₁ x hx c h₂).trans h₃

private theorem twin_cols_bound (A : α → β → Bool) {R : Finset α} {Y : Finset β}
    (ht : ∀ c ∈ Y, ∀ d ∈ Y, ∀ r ∈ R, A r c = A r d)
    (hr : ∀ (S : Finset α) (T : Finset β), (∀ r ∈ S, ∀ c ∈ T, A r c = false) →
      (S ×ˢ T).card ≤ 2) : (zeros A R Y).card ≤ 2 := by
  rcases Y.eq_empty_or_nonempty with hy | ⟨y, hy⟩
  · simp [zeros, hy]
  let S := R.filter fun r => A r y = false
  have he : zeros A R Y ⊆ S ×ˢ Y := by
    rintro ⟨r,c⟩ hp
    obtain ⟨⟨h₁,h₂⟩, h₃⟩ := (show (r ∈ R ∧ c ∈ Y) ∧ A r c = false by simpa [zeros] using hp)
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨h₁,(ht y hy c h₂ r h₁).trans h₃⟩,h₂⟩
  apply (Finset.card_le_card he).trans (hr S Y ?_)
  intro r hs c hc
  obtain ⟨h₁, h₂⟩ := Finset.mem_filter.mp hs
  exact (ht c hc y hy r h₁).trans h₂

private theorem sparse_rank_bound (A : α → β → Bool)
    (hrow : ∀ r, (Finset.univ.filter fun c => A r c = false).card ≤ 2)
    (hcol : ∀ c, (Finset.univ.filter fun r => A r c = false).card ≤ 2)
    (hsq : ∀ r s c d, A r c = false → A r d = false → A s c = false →
      A s d = false → r = s ∨ c = d)
    {t : ℕ} {R : Finset α} {C : Finset β} (h : Rank A t R C) :
    (zeros A R C).card ≤ 4 * t + 8 := by
  have rect := fun S T => @rectangle_bound _ _ _ _ _ _ A hrow hcol hsq S T
  induction t generalizing R C with
  | zero =>
    by_cases small : R.card ≤ 4
    · let fibers := fun r : α => ({r} : Finset α) ×ˢ (Finset.univ.filter fun c => A r c = false)
      have incl : zeros A R C ⊆ R.biUnion fibers := by
        rintro ⟨r,c⟩ hp
        obtain ⟨⟨hr,hc⟩, hz⟩ := (show (r ∈ R ∧ c ∈ C) ∧ A r c = false by simpa [zeros] using hp)
        exact Finset.mem_biUnion.mpr ⟨r,hr,by simp [fibers,hz]⟩
      calc
        _ ≤ _ := Finset.card_le_card incl
        _ ≤ _ := Finset.card_biUnion_le
        _ ≤ ∑ _r ∈ R, 2 := Finset.sum_le_sum fun r _ => by simpa [fibers] using hrow r
        _ ≤ _ := by simp; omega
    · have common (c d : β) : ∃ r ∈ R, A r c = true ∧ A r d = true := by
        by_contra! bad
        have incl : R ⊆ (Finset.univ.filter fun r => A r c = false) ∪
            (Finset.univ.filter fun r => A r d = false) := by
          intro r hr
          cases he : A r c <;> simp [he, bad r hr] at *
        have h₁ := Finset.card_le_card incl
        have h₂ := Finset.card_union_le (Finset.univ.filter fun r => A r c = false)
          (Finset.univ.filter fun r => A r d = false)
        have := hcol c
        have := hcol d
        omega
      have twins : ∀ c ∈ C, ∀ d ∈ C, ∀ r ∈ R, A r c = A r d := by
        intro c hc d hd r hr
        obtain ⟨x,hx,hxc,hxd⟩ := common c d
        apply Bool.eq_iff_iff.mpr
        exact ⟨fun hrc => h x hx r hr c hc d hd hxc hrc hxd,
          fun hrd => h x hx r hr d hd c hc hxd hrd hxc⟩
      exact (twin_cols_bound A twins rect).trans (by decide)
  | succ t ih =>
    obtain ⟨X, _, Y, _, tw, tail⟩ := h
    have incl : zeros A R C ⊆ (zeros A X C ∪ zeros A R Y) ∪ zeros A (R \ X) (C \ Y) := by
      rintro ⟨r,c⟩ hp
      simp only [zeros, Finset.mem_filter, Finset.mem_product, Finset.mem_union, Finset.mem_sdiff] at *
      tauto
    have h₁ := Finset.card_le_card incl
    have h₂ := Finset.card_union_le (zeros A X C ∪ zeros A R Y) (zeros A (R \ X) (C \ Y))
    have h₃ := Finset.card_union_le (zeros A X C) (zeros A R Y)
    have h₄ := twin_rows_bound A tw.1 rect
    have h₅ := twin_cols_bound A tw.2 rect
    have h₆ := ih tail
    omega

end Sparse


def A (k : ℕ) (u v : Fin (2*k)) : Bool :=
  decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % (2*k))

def next {n : ℕ} (u : Fin n) : Fin n :=
  if h : u.val + 1 < n then ⟨u.val + 1, h⟩ else ⟨0, by omega⟩

def prev {n : ℕ} (u : Fin n) : Fin n :=
  if u.val = 0 then ⟨n-1, by have := u.isLt; omega⟩ else ⟨u.val-1, by omega⟩

theorem next_val {n : ℕ} (u : Fin n) : (next u).val = (u.val+1) % n := by
  unfold next
  split
  · exact (Nat.mod_eq_of_lt (by assumption)).symm
  · have h : u.val + 1 = n := by omega
    simp [h]

theorem next_ne {n : ℕ} (hn : 2 ≤ n) (u : Fin n) : next u ≠ u := by
  intro h
  have e := congrArg Fin.val h
  unfold next at e
  split at e <;> simp only at e <;> omega

theorem next_next_ne {n : ℕ} (hn : 3 ≤ n) (u : Fin n) : next (next u) ≠ u := by
  intro h
  have e := congrArg Fin.val h
  unfold next at e
  split at e <;> simp only at e <;> split at e <;> simp only at e <;> omega

theorem prev_next {n : ℕ} (u : Fin n) : prev (next u) = u := by
  apply Fin.ext
  unfold prev next
  split <;> simp only <;> split <;> simp_all
  omega

theorem next_prev {n : ℕ} (u : Fin n) : next (prev u) = u := by
  apply Fin.ext
  unfold next prev
  split <;> simp only <;> split <;> simp_all <;> omega

theorem zero_iff {k : ℕ} (u v : Fin (2*k)) :
    A k u v = false ↔ v = u ∨ v = next u := by
  simp only [A, decide_eq_false_iff_not, Fin.ext_iff, next_val]
  tauto

theorem row_card {k : ℕ} (hk : 2 ≤ k) (u : Fin (2*k)) :
    (Finset.univ.filter fun v => A k u v = false).card = 2 := by
  have eq : (Finset.univ.filter fun v => A k u v = false) = {u, next u} := by
    ext v
    simp [zero_iff]
  rw [eq]
  simp [(next_ne (by omega) u).symm]

theorem col_card {k : ℕ} (hk : 2 ≤ k) (v : Fin (2*k)) :
    (Finset.univ.filter fun u => A k u v = false).card = 2 := by
  have hp (u : Fin (2*k)) : v = next u ↔ u = prev v := by
    constructor
    · rintro rfl
      exact (prev_next u).symm
    · rintro rfl
      exact (next_prev v).symm
  have eq : (Finset.univ.filter fun u => A k u v = false) = {v, prev v} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, zero_iff, hp, Finset.mem_insert,
      Finset.mem_singleton]
    exact or_congr eq_comm Iff.rfl
  have ne : v ≠ prev v := by
    intro h
    have he := congrArg next h
    rw [next_prev] at he
    exact next_ne (by omega) v he
  rw [eq]
  simp [ne]

theorem no_rectangle {k : ℕ} (hk : 2 ≤ k) (u u' v v' : Fin (2*k))
    (hrow : u ≠ u') (hcol : v ≠ v') :
    ¬ (A k u v = false ∧ A k u v' = false ∧ A k u' v = false ∧ A k u' v' = false) := by
  simp only [zero_iff]
  have hinj : Function.Injective (@next (2*k)) := fun a b h =>
    (prev_next a).symm.trans ((congrArg prev h).trans (prev_next b))
  have hu := next_next_ne (by omega) u
  have hu' := next_next_ne (by omega) u'
  rintro ⟨h1,h2,h3,h4⟩
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4 <;> grind

theorem zeros_card {k : ℕ} (hk : 2 ≤ k) :
    ((Finset.univ ×ˢ Finset.univ).filter fun e : Fin (2*k) × Fin (2*k) =>
      A k e.1 e.2 = false).card = 4*k := by
  rw [Finset.card_filter, Finset.sum_product]
  simp_rw [← Finset.card_filter, row_card hk]
  simp
  omega


private theorem both_values {n : ℕ} (hn : 2 < n) (p : Fin n → Bool)
    (h : (Finset.univ.filter fun x => p x = false).card = 2) :
    (∃ x, p x = true) ∧ (∃ x, p x = false) := by
  constructor
  · by_contra! hn'
    have he : (Finset.univ.filter fun x => p x = false) = Finset.univ := by
      ext x
      simp [Bool.eq_false_iff.mpr (hn' x)]
    rw [he, Finset.card_univ, Fintype.card_fin] at h
    omega
  · obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter fun x => p x = false).card)
    exact ⟨x,(Finset.mem_filter.mp hx).2⟩

-- A size bound for any rectangular matrix whose zero graph has maximum degree
-- two and contains no four-cycle. The assumptions on each row and column
-- ensure that every input wire contributes to the gate budget.
theorem sparse_complement_gate_bound {n m s : ℕ} (hn : 0 < n) (A : Fin n → Fin m → Bool)
    (rows_vary : ∀ r, (∃ c, A r c = true) ∧ (∃ c, A r c = false))
    (cols_vary : ∀ c, (∃ r, A r c = true) ∧ (∃ r, A r c = false))
    (hrow : ∀ r, (Finset.univ.filter fun c => A r c = false).card ≤ 2)
    (hcol : ∀ c, (Finset.univ.filter fun r => A r c = false).card ≤ 2)
    (hsq : ∀ r s c d, A r c = false → A r d = false → A s c = false →
      A s d = false → r = s ∨ c = d)
    (h : RepSizeAtMost A s) :
    4 * (n + m) + ((Finset.univ ×ˢ Finset.univ).filter
      fun e : Fin n × Fin m => A e.1 e.2 = false).card ≤ 4 * s + 12 := by
  obtain ⟨t, rank, budget⟩ := full_matrix_rank hn A rows_vary cols_vary h
  have bound := sparse_rank_bound A hrow hcol hsq rank
  unfold zeros at bound
  omega

private theorem double_crown_bound {k s : ℕ} (hk : 2 ≤ k) (h : RepSizeAtMost (A k) s) :
    5*k - 3 ≤ s := by
  have bound := sparse_complement_gate_bound (by omega) (A k)
    (fun r => both_values (by omega) _ (row_card hk r))
    (fun c => both_values (by omega) _ (col_card hk c))
    (fun r => (row_card hk r).le) (fun c => (col_card hk c).le)
    (fun r s c d h₁ h₂ h₃ h₄ => by
      by_contra! ne
      exact no_rectangle hk r s c d ne.1 ne.2 ⟨h₁,h₂,h₃,h₄⟩) h
  rw [zeros_card hk] at bound
  omega

end PEqualNP.Outside.L_meta_17365

theorem PEqualNP.Outside.L_meta_17365 :
    ∀ k s : ℕ, 2 ≤ k → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin (2 * k) => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % (2 * k))) s → 5 * k - 3 ≤ s := by
  intro k s hk h
  exact L_meta_17365.double_crown_bound hk h
