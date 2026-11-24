import PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity

def mfWire {n : ℕ} (C : Circuit) (w : ℕ) (z : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn z)).getD w false

def mfSafeProduct (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (u v : ℕ) : Prop :=
  ∀ z : Fin (N + N) → Bool, mfWire C u z = true → mfWire C v z = true →
    ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true

lemma mfCrossPoint (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hmono : Monotone2 C) (u v : ℕ) (hsafe : mfSafeProduct N I C u v)
    (p q r : Fin N) (hu : mfWire C u (lcSingleton (Fin.castAdd N p)) = true)
    (hv : mfWire C v (lcPair N q r) = true) (hbad : ¬ I q r) : I p r := by
  let z : Fin (N + N) → Bool := fun k => lcPair N p r k || lcPair N q r k
  have huz : mfWire C u z = true := by
    apply decWireMono (N + N) C hmono (lcSingleton (Fin.castAdd N p)) z ?_ u hu
    intro k hk
    have he : k = Fin.castAdd N p := of_decide_eq_true hk
    subst k
    simp [z, lcPair]
  have hvz : mfWire C v z = true := by
    apply decWireMono (N + N) C hmono (lcPair N q r) z ?_ v hv
    intro k hk
    simp [z, hk]
  obtain ⟨a, b, hab, ha, hb⟩ := hsafe z huz hvz
  simp only [z, Bool.or_eq_true] at ha hb
  have hb' : b = r := by
    rcases hb with hb | hb
    · exact (lcPairLine N p r b).mp hb
    · exact (lcPairLine N q r b).mp hb
  subst b
  have ha' : a = p ∨ a = q := by
    rcases ha with ha | ha
    · exact Or.inl ((lcPairPoint N p r a).mp ha)
    · exact Or.inr ((lcPairPoint N q r a).mp ha)
  rcases ha' with rfl | rfl
  · exact hab
  · exact (hbad hab).elim

lemma mfCrossLine (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hmono : Monotone2 C) (u v : ℕ) (hsafe : mfSafeProduct N I C u v)
    (l q r : Fin N) (hu : mfWire C u (lcSingleton (Fin.natAdd N l)) = true)
    (hv : mfWire C v (lcPair N q r) = true) (hbad : ¬ I q r) : I q l := by
  let z : Fin (N + N) → Bool := fun k => lcPair N q l k || lcPair N q r k
  have huz : mfWire C u z = true := by
    apply decWireMono (N + N) C hmono (lcSingleton (Fin.natAdd N l)) z ?_ u hu
    intro k hk
    have he : k = Fin.natAdd N l := of_decide_eq_true hk
    subst k
    simp [z, lcPair]
  have hvz : mfWire C v z = true := by
    apply decWireMono (N + N) C hmono (lcPair N q r) z ?_ v hv
    intro k hk
    simp [z, hk]
  obtain ⟨a, b, hab, ha, hb⟩ := hsafe z huz hvz
  simp only [z, Bool.or_eq_true] at ha hb
  have ha' : a = q := by
    rcases ha with ha | ha
    · exact (lcPairPoint N q l a).mp ha
    · exact (lcPairPoint N q r a).mp ha
  subst a
  have hb' : b = l ∨ b = r := by
    rcases hb with hb | hb
    · exact Or.inl ((lcPairLine N q l b).mp hb)
    · exact Or.inr ((lcPairLine N q r b).mp hb)
  rcases hb' with rfl | rfl
  · exact hab
  · exact (hbad hab).elim

lemma mfJunkRectangle (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hmono : Monotone2 C) (u v : ℕ) (hsafe : mfSafeProduct N I C u v)
    (q r : Fin N) (hbad : ¬ I q r) (hv : mfWire C v (lcPair N q r) = true) :
    (∀ p : Fin N, mfWire C u (lcSingleton (Fin.castAdd N p)) = true → I p r) ∧
    (∀ l : Fin N, mfWire C u (lcSingleton (Fin.natAdd N l)) = true → I q l) := by
  exact ⟨fun p hp => mfCrossPoint N I C hmono u v hsafe p q r hp hv hbad,
    fun l hl => mfCrossLine N I C hmono u v hsafe l q r hl hv hbad⟩

lemma mfTwoPointsForceLine (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hmono : Monotone2 C) (u v v' : ℕ) (hsafe : mfSafeProduct N I C u v)
    (hsafe' : mfSafeProduct N I C u v')
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (p p' : Fin N) (hpp : p ≠ p')
    (hp : mfWire C u (lcSingleton (Fin.castAdd N p)) = true)
    (hp' : mfWire C u (lcSingleton (Fin.castAdd N p')) = true)
    (q r q' r' : Fin N) (hbad : ¬ I q r) (hbad' : ¬ I q' r')
    (hv : mfWire C v (lcPair N q r) = true)
    (hv' : mfWire C v' (lcPair N q' r') = true) : r = r' := by
  by_contra hrr
  exact hfour p p' r r' hpp hrr
    ⟨mfCrossPoint N I C hmono u v hsafe p q r hp hv hbad,
      mfCrossPoint N I C hmono u v' hsafe' p q' r' hp hv' hbad',
      mfCrossPoint N I C hmono u v hsafe p' q r hp' hv hbad,
      mfCrossPoint N I C hmono u v' hsafe' p' q' r' hp' hv' hbad'⟩

lemma mfTwoLinesForcePoint (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hmono : Monotone2 C) (u v v' : ℕ) (hsafe : mfSafeProduct N I C u v)
    (hsafe' : mfSafeProduct N I C u v')
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (l l' : Fin N) (hll : l ≠ l')
    (hl : mfWire C u (lcSingleton (Fin.natAdd N l)) = true)
    (hl' : mfWire C u (lcSingleton (Fin.natAdd N l')) = true)
    (q r q' r' : Fin N) (hbad : ¬ I q r) (hbad' : ¬ I q' r')
    (hv : mfWire C v (lcPair N q r) = true)
    (hv' : mfWire C v' (lcPair N q' r') = true) : q = q' := by
  by_contra hqq
  exact hfour q q' l l' hqq hll
    ⟨mfCrossLine N I C hmono u v hsafe l q r hl hv hbad,
      mfCrossLine N I C hmono u v hsafe l' q r hl' hv hbad,
      mfCrossLine N I C hmono u v' hsafe' l q' r' hl hv' hbad',
      mfCrossLine N I C hmono u v' hsafe' l' q' r' hl' hv' hbad'⟩

lemma mfTwoEachForcePair (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hmono : Monotone2 C) (u v v' : ℕ) (hsafe : mfSafeProduct N I C u v)
    (hsafe' : mfSafeProduct N I C u v')
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (p p' l l' : Fin N) (hpp : p ≠ p') (hll : l ≠ l')
    (hp : mfWire C u (lcSingleton (Fin.castAdd N p)) = true)
    (hp' : mfWire C u (lcSingleton (Fin.castAdd N p')) = true)
    (hl : mfWire C u (lcSingleton (Fin.natAdd N l)) = true)
    (hl' : mfWire C u (lcSingleton (Fin.natAdd N l')) = true)
    (q r q' r' : Fin N) (hbad : ¬ I q r) (hbad' : ¬ I q' r')
    (hv : mfWire C v (lcPair N q r) = true)
    (hv' : mfWire C v' (lcPair N q' r') = true) : q = q' ∧ r = r' := by
  exact ⟨mfTwoLinesForcePoint N I C hmono u v v' hsafe hsafe' hfour l l' hll hl hl'
      q r q' r' hbad hbad' hv hv',
    mfTwoPointsForceLine N I C hmono u v v' hsafe hsafe' hfour p p' hpp hp hp'
      q r q' r' hbad hbad' hv hv'⟩

lemma mfRectangleRows (N : ℕ) (I : Fin N → Fin N → Prop)
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (P L : Finset (Fin N)) (q r l l' : Fin N)
    (hl : l ∈ L) (hl' : l' ∈ L) (hll : l ≠ l')
    (hmiss : ∀ p ∈ P, ∀ k ∈ L, ¬ I p k → p = q ∧ k = r) : P.card ≤ 2 := by
  classical
  by_cases hs : P ⊆ {q}
  · have h := Finset.card_le_card hs
    simp only [Finset.card_singleton] at h
    omega
  · obtain ⟨p, hp, hpq⟩ := Finset.not_subset.mp hs
    simp only [Finset.mem_singleton] at hpq
    have hrow (a : Fin N) (ha : a ∈ P) (haq : a ≠ q) (k : Fin N) (hk : k ∈ L) :
        I a k := by
      by_contra h
      exact haq (hmiss a ha k hk h).1
    have hsub : P ⊆ {q, p} := by
      intro a ha
      by_cases haq : a = q
      · simp [haq]
      · have hap : a = p := by
          by_contra h
          exact hfour a p l l' h hll
            ⟨hrow a ha haq l hl, hrow a ha haq l' hl',
              hrow p hp hpq l hl, hrow p hp hpq l' hl'⟩
        simp [hap]
    exact (Finset.card_le_card hsub).trans
      (by simpa using Finset.card_insert_le q ({p} : Finset (Fin N)))

lemma mfRectangleColumns (N : ℕ) (I : Fin N → Fin N → Prop)
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (P L : Finset (Fin N)) (q r p p' : Fin N)
    (hp : p ∈ P) (hp' : p' ∈ P) (hpp : p ≠ p')
    (hmiss : ∀ a ∈ P, ∀ l ∈ L, ¬ I a l → a = q ∧ l = r) : L.card ≤ 2 := by
  refine mfRectangleRows N (fun l p => I p l) ?_ L P r q p p' hp hp' hpp ?_
  · intro l l' p p' hll hpp h
    exact hfour p p' l l' hpp hll ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩
  · intro l hl a ha hbad
    exact (hmiss a ha l hl hbad).symm

lemma mfRectangleStarOrSquare (N : ℕ) (I : Fin N → Fin N → Prop)
    (hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (P L : Finset (Fin N)) (q r : Fin N)
    (hmiss : ∀ a ∈ P, ∀ l ∈ L, ¬ I a l → a = q ∧ l = r) :
    P.card ≤ 1 ∨ L.card ≤ 1 ∨ P.card ≤ 2 ∧ L.card ≤ 2 := by
  by_cases hp : P.card ≤ 1
  · exact Or.inl hp
  by_cases hl : L.card ≤ 1
  · exact Or.inr (Or.inl hl)
  obtain ⟨p, hp, p', hp', hpp⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
  obtain ⟨l, hl, l', hl', hll⟩ := Finset.one_lt_card.mp (by omega : 1 < L.card)
  exact Or.inr (Or.inr
    ⟨mfRectangleRows N I hfour P L q r l l' hl hl' hll hmiss,
      mfRectangleColumns N I hfour P L q r p p' hp hp' hpp hmiss⟩)

end PEqualNP.Outside.L_meta_3451
