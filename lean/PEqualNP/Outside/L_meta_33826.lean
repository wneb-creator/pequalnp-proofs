import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33826
def bigNat_0 : Nat := 0x3ffffefffffbefffff7df7ffffddf7ffffdefffffbdffffefbeefffff7beefbdefffeb6d5aaffedffd6d55ffd7ff7ff555adab557ff56ffedffdb55affeb6bffbffadaabffaffeffedb7ff0000000000000000
def bigNat_1 : Nat := 0x1492a55001200292aa002800800aaa5254aa800a900120024aa50014940040052554005001001248000000000000000000
def bigNat_2 : Nat := 0x4000010000041000008208000022080000210000042000010411000008411042100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def bigNat_3 : Nat := 0x3ffffe00000000000000000000000007ffff81f07c0f0000000040042008400220888220230000200808412308461080000082414210218004421108408624843000000000000000001082601209820441304143d44c0102014c204049840808e08222516703e0f81e0826000180000000001440010007ff0100c030100046000c0000100000868003ff80288002000ffedb7ff8dadadfe4a5a5433
def bigNat_4 : Nat := 0xfffff01f07ffffbc007de00000000000006000c82280188070060000000220052800c201c002100a484038031045003100e00c6180a00000000000000000211480245204088a4082040690420422904084920854d5403e0295aa7800fbc0114800040000000010c500017ff00004020084400050000dffc0442000b0bff800218a0002ffe000c3000d6f76f5b6b5840a5
def bigNat_5 : Nat := 0x3ffffe00000000fffff7c007ffffbdf700000000000001026004c902a05c0160160004000280152902e0058082c04a5b0130131205413804c04c6c02a000000000000000004221004884081110810408182084495b200108241065464f800319327bee0000221000100200000016055ffc00000010180205000056ffe00003058000b60000002c0abff8000000d800039cee7185296b7bd
def bigNat_6 : Nat := 0x7ffffc0000000000000000000000007ffffc0fffff7df70000000000000000000200420c6428b68043010c10c00000402a10e002180430402521c0008608616d008a02282284911c0000000000000000080482d7120800224120800610508008c048433388046646fbee0220300200802048200c008000c0016d000000000004040180557ff000000001805affe000000002da00000000000db7fff83e9b0745d1745d
def bigNat_7 : Nat := 0x7ffff80f8000000f80000007ffffde00000000000000000000000000410010088213000001200480482a800d500088001100220d28011000044044049004c013013000090000000000000000010401c1800710a3c0e01f1080381f10103806223f3c8007810404003c08421044401c860020000dffc000000000000055001ab00000000000001b500000000000002daabffaffeffe00000367267c68e5cecc4
def bigNat_8 : Nat := 0x7ffffbe00000000fbffffef0000000000000000000000000000000004800110b0014000001400500502aad400000900012002409a881601205805800000500140140000a000000000000000002080e06003820c3c707c02101c01f611fc1e803c001007802084803c01080208880e0b0002affe00000000000000000555ac0000000000000001b55affeb6bffbff80000000000000000005b5b4a6b6b794969
def bigNat_9 : Nat := 0x1fffff00000007ffffbefbffffee000000000000000000000000000000000000000005b4ac04c0098000009802602602aa969580ae0025c04b8000005800016016000001600580580002c000000000000000003f0700801c00083f807df41fe01c001e000003c000007800410803c00210441000700b6d58000000000000000000000555adab557ff56ffedffc0000000000000000000000000000000000639c738c739e718e
def bigNat_10 : Nat := 0x1fffff7ffffdf00000000000000000000000000000000000000000000000000000000126a847004e002480e00380380000000000300006000c00000060000180180000018006006000030000000000000000003ff800ffe003efc0004107e0000107e00010fc00021f80008200fc00042088210f800b6d5aaffedffd6d55ffd7ff7ff0000000000000000000000000000000000000000000000000000000d6b5295ad6b52b5a
def bigNat_11 : Nat := 0x3ffffefffffbefffff7df7ffffddf7ffffdefffffbdffffefbeefffff7beefbdefffeb6d5aaffedffd6d55ffd7ff7ff555adab557ff56ffedffdb55affeb6bffbffadaabffaffeffedb7ffffffffffffffffff
variable {R : ℕ → ℕ}
def op (d : Bool) (a b : ℕ) : ℕ := bif d then a ||| b else a &&& b
lemma op_comm (d : Bool) (a b : ℕ) : op d a b = op d b a := by
  cases d <;> simp [op, Nat.and_comm, Nat.or_comm]
lemma op_bit (d : Bool) (a b i : ℕ) : (op d a b).testBit i =
    bif d then a.testBit i || b.testBit i else a.testBit i && b.testBit i := by
  cases d <;> simp [op]
lemma op_self (d : Bool) (a : ℕ) : op d a a = a := by cases d <;> simp [op]
def Al (R : ℕ → ℕ) (d : Bool) (a b : ℕ) : Prop := (R a &&& R b) ≤ (bif d then 1 else 0)
lemma Al.symm {d : Bool} {a b : ℕ} (h : Al R d a b) : Al R d b a := by unfold Al at *; rwa [Nat.and_comm]
def Z0 : ℕ → ℕ := fun _ => 0
lemma al0 (d : Bool) (a b : ℕ) : Al Z0 d a b := by simp [Al, Z0]
inductive Sol (R : ℕ → ℕ) (m T : ℕ) : ℕ → Set ℕ → Prop
  | done {q : ℕ} {S : Set ℕ} : T ∈ S → Sol R m T q S
  | un {q : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S → Sol R m T q (insert (a ^^^ m) S) → Sol R m T (q + 1) S
  | bi {q : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S → Al R d a b →
      Sol R m T q (insert (op d a b) S) → Sol R m T (q + 1) S
lemma Sol.mono {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∀ {q' : ℕ} {S' : Set ℕ}, q ≤ q' → S ⊆ S' → Sol R m T q' S' := by
  induction h with
  | done h => intro q' S' _ hs; exact .done (hs h)
  | un h _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .un (hs h) (ih (by omega) (Set.insert_subset_insert hs))
  | bi h1 h2 ha _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .bi (hs h1) (hs h2) ha (ih (by omega) (Set.insert_subset_insert hs))
lemma Sol.rel {R' : ℕ → ℕ} {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Sol R' m T q S := by
  induction h with
  | done h => exact .done h
  | un h _ ih => exact .un h ih
  | bi h1 h2 ha _ ih => exact .bi h1 h2 (hR _ _ _ ha) ih
lemma Sol.to0 {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) : Sol Z0 m T q S := h.rel fun d a b _ => al0 d a b
inductive Live (R : ℕ → ℕ) (m T : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | stop : Live R m T 0 0 {T}
  | un {k t : ℕ} {a : ℕ} {U : Finset ℕ} : Live R m T k t (insert (a ^^^ m) U) →
      Live R m T (k + 1) (t + 1) (insert a U)
  | bi {k t : ℕ} {d : Bool} {a b : ℕ} {U : Finset ℕ} : a ≠ b → Al R d a b → Live R m T k t (insert (op d a b) U) →
      Live R m T (k + 1) t (insert a (insert b U))
lemma Live.sol {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : Sol Z0 m T k (S : Set ℕ) := by
  induction h with
  | stop => exact .done (by simp)
  | @un k t a U _ ih =>
    refine .un (a := a) (by simp) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
  | @bi k t d a b U _ _ _ ih =>
    refine .bi (d := d) (a := a) (b := b) (by simp) (by simp) (al0 _ _ _) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
lemma Sol.live {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∃ k ≤ q, ∃ t, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live R m T k t S0 := by
  induction h with
  | @done q S h => exact ⟨0, by omega, 0, {T}, by simpa using h, .stop⟩
  | @un q S a ha _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : a ^^^ m ∈ S1
    · refine ⟨k + 1, by omega, t + 1, insert a (S1.erase (a ^^^ m)), ?_, .un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1, h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
  | @bi q S d a b ha hb hal _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : op d a b ∈ S1
    · by_cases hab : a = b
      · subst hab; rw [op_self] at hs
        exact ⟨k, by omega, t, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
      refine ⟨k + 1, by omega, t, insert a (insert b (S1.erase (op d a b))), ?_, .bi hab hal (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1, h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
def C (m : ℕ) (S : Set ℕ) : Set ℕ := S ∪ {0, m}
lemma C_mono {m : ℕ} {S S' : Set ℕ} (h : S ⊆ S') : C m S ⊆ C m S' := Set.union_subset_union_left _ h
lemma sub_C (m : ℕ) (S : Set ℕ) : S ⊆ C m S := Set.subset_union_left
def Un (m a : ℕ) (S S' : Finset ℕ) : Prop := ∃ U, S = insert a U ∧ S' = insert (a ^^^ m) U
def Bi (R : ℕ → ℕ) (d : Bool) (a b : ℕ) (S S' : Finset ℕ) : Prop :=
  a ≠ b ∧ ∃ U, S = insert a (insert b U) ∧ S' = insert (op d a b) U ∧ Al R d a b
lemma Un.live {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) (t + 1) S := by obtain ⟨U, rfl, rfl⟩ := h; exact .un hl
lemma Bi.live {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) t S := by obtain ⟨hab, U, rfl, rfl, hal⟩ := h; exact .bi hab hal hl
lemma Bi.symm {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') : Bi R d b a S S' := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  exact ⟨hab.symm, U, Finset.insert_comm _ _ _, by rw [op_comm], hal.symm⟩
lemma Un.sub {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') : a ∈ S ∧ S' ⊆ insert (a ^^^ m) S := by
  obtain ⟨U, rfl, rfl⟩ := h
  exact ⟨by simp, Finset.insert_subset_insert _ (Finset.subset_insert _ _)⟩
lemma Bi.sub {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') :
    a ∈ S ∧ b ∈ S ∧ S' ⊆ insert (op d a b) S := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  refine ⟨by simp, by simp, Finset.insert_subset_insert _ ?_⟩
  intro x hx; simp [hx]
def Min (R : ℕ → ℕ) (m T k t : ℕ) (S : Finset ℕ) : Prop := Live R m T k t S ∧ ∀ q < k, ¬ Sol Z0 m T q (C m S)
lemma Un.sol {m T a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (a := a) (sub_C _ _ (by simpa using ha)) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Bi.sol {m T a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (a := a) (b := b) (sub_C _ _ (by simpa using ha)) (sub_C _ _ (by simpa using hb)) (al0 _ _ _) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Un.min {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Bi.min {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Un.fresh {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : a ^^^ m ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Bi.fresh {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : op d a b ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Min.size {m T : ℕ} : ∀ {k t : ℕ} {S : Finset ℕ}, Min R m T k t S → S.card + t ≤ k + 1 ∧ t ≤ k := by
  intro k t S ⟨hl, hm⟩
  induction hl with
  | stop => simp
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have ih := ih (hu.min hl hm).2
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have ih := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
def phi (a n : ℕ) (X : Finset ℕ) : Finset ℕ := insert a (X.erase n)
lemma phi_un {m a n c : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (h1 : c ≠ n) (h2 : c ^^^ m ≠ n) :
    Un m c (phi a n X) (phi a n X') := by
  obtain ⟨U, rfl, rfl⟩ := h
  refine ⟨insert a (U.erase n), ?_, ?_⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_bi {a n b c : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (h1 : b ≠ n) (h2 : c ≠ n)
    (h3 : op d b c ≠ n) : Bi R d b c (phi a n X) (phi a n X') := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  refine ⟨hab, insert a (U.erase n), ?_, ?_, hal⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_back {m a : ℕ} {X : Finset ℕ} (h : a ^^^ m ∈ X) : Un m a (phi a (a ^^^ m) X) X :=
  ⟨X.erase (a ^^^ m), rfl, by rw [Finset.insert_erase h]⟩
lemma phi_start {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hn : a ^^^ m ∉ S) : phi a (a ^^^ m) S' = S := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn
  simp [phi, hn.2]
lemma un_keep {m c n : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (hn : n ∈ X) (h1 : c ≠ n) : n ∈ X' := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn ⊢; exact Or.inr (hn.resolve_left (Ne.symm h1))
lemma bi_keep {b c n : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (hn : n ∈ X) (h1 : b ≠ n)
    (h2 : c ≠ n) : n ∈ X' := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  simp at hn ⊢; rcases hn with h | h | h
  · exact absurd h.symm h1
  · exact absurd h.symm h2
  · exact Or.inr h
lemma first_move {m T : ℕ} : ∀ (k t : ℕ) (S : Finset ℕ), Min R m T k t S → 2 ≤ S.card →
    (∃ k0 d a b S1, k = k0 + 1 ∧ Bi R d a b S S1 ∧ Live R m T k0 t S1) ∨
    (∃ k0 t0 a d c S1 S2, k = k0 + 2 ∧ t = t0 + 1 ∧ Un m a S S1 ∧ Bi R d (a ^^^ m) c S1 S2 ∧ Live R m T k0 t0 S2) ∨
    (∃ k0 t0 a a' d S1 S2 S3, k = k0 + 3 ∧ t = t0 + 2 ∧ Un m a S S1 ∧ a' ≠ a ^^^ m ∧ Un m a' S1 S2 ∧
      Bi R d (a ^^^ m) (a' ^^^ m) S2 S3 ∧ Live R m T k0 t0 S3) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro t S hS hc
  obtain ⟨hl, hm⟩ := hS
  cases hl with
  | stop => simp at hc
  | @bi k t d a b U hab hal hl => exact Or.inl ⟨k, d, a, b, _, rfl, ⟨hab, U, rfl, rfl, hal⟩, hl⟩
  | @un k t a U hl =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf := hu.fresh hl hm
    have hn : a ^^^ m ∉ insert a U := fun h => hf (sub_C _ _ (by simpa using h))
    have hmin := hu.min hl hm
    have hxx : ∀ c : ℕ, c ^^^ m ^^^ m = c := fun c => by simp
    have hc' : 2 ≤ (insert (a ^^^ m) U).card := by
      have h1 := Finset.card_insert_le a U
      rw [Finset.card_insert_of_notMem (fun h => hn (by simp [h]))]; omega
    generalize hS1 : insert (a ^^^ m) U = S1 at *
    have hnS1 : a ^^^ m ∈ S1 := by rw [← hS1]; simp
    have hst := phi_start hu hn
    have dbl : ∀ {c k2 t2 S2}, Un m c S1 S2 → Live R m T k2 t2 S2 → k = k2 + 1 → c ≠ a ^^^ m ∧ c ^^^ m ≠ a ^^^ m := by
      intro c k2 t2 S2 h2 hl2 hk
      constructor
      · rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        apply hm (k2 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (hl2.sol.mono le_rfl fun x hx => ?_)
        have h3 := hsub hx
        have h4 : x ∈ insert a (insert (a ^^^ m) U) := by rw [hS1]; exact h3
        simp at h4
        rcases h4 with rfl | rfl | h4
        · exact Or.inr (sub_C _ _ (by simp))
        · exact Or.inl rfl
        · exact Or.inr (sub_C _ _ (by simp [h4]))
      · intro e
        exact h2.fresh hl2 (by rw [← hk]; exact hmin.2) (sub_C _ _ (by rw [e]; simpa using hnS1))
    rcases ih k (by omega) t S1 hmin hc' with
      ⟨k0, d, x, y, S2, rfl, hb, hl2⟩ | ⟨k0, t0, c, d, y, S2, S3, rfl, rfl, h1, hb, hl2⟩ |
      ⟨k0, t0, c, c', d, S2, S3, S4, rfl, rfl, h1, hne, h2, hb, hl2⟩
    · by_cases hx : x = a ^^^ m
      · subst hx; exact Or.inr (Or.inl ⟨k0, t, a, d, y, S1, S2, rfl, rfl, hu, hb, hl2⟩)
      by_cases hy : y = a ^^^ m
      · subst hy; exact Or.inr (Or.inl ⟨k0, t, a, d, x, S1, S2, rfl, rfl, hu, hb.symm, hl2⟩)
      have hg : op d x y ≠ a ^^^ m := fun e => hb.fresh hl2 hmin.2 (sub_C _ _ (by rw [e]; simpa using hnS1))
      refine Or.inl ⟨k0 + 1, d, x, y, phi a (a ^^^ m) S2, rfl, ?_, ?_⟩
      · rw [← hst]; exact phi_bi hb hx hy hg
      · exact (phi_back (bi_keep hb hnS1 hx hy)).live hl2
    · have hb1 := hb.live hl2
      obtain ⟨n1, n2⟩ := dbl h1 hb1 rfl
      have hm2 := h1.min hb1 hmin.2
      by_cases hy : y = a ^^^ m
      · subst hy
        exact Or.inr (Or.inr ⟨k0, t0, a, c, d, S1, S2, S3, rfl, rfl, hu, n1, h1, hb.symm, hl2⟩)
      have hk2 := un_keep h1 hnS1 n1
      have hg : op d (c ^^^ m) y ≠ a ^^^ m := fun e => hb.fresh hl2 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      refine Or.inr (Or.inl ⟨k0 + 1, t0 + 1, c, d, y, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, rfl, rfl, ?_, phi_bi hb n2 hy hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk2 n2 hy)).live hl2
    · have hb1 := hb.live hl2
      have hb2 := h2.live hb1
      obtain ⟨n1, n2⟩ := dbl h1 hb2 rfl
      have hm2 := h1.min hb2 hmin.2
      have hk2 := un_keep h1 hnS1 n1
      have hm3 := h2.min hb1 hm2.2
      have n3 : c' ≠ a ^^^ m := by
        rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        obtain ⟨hcS, hsub1⟩ := h1.sub
        have hcS' : c ∈ insert a U := by
          have : c ∈ insert (a ^^^ m) U := by rw [hS1]; exact hcS
          simp at this ⊢; exact Or.inr (this.resolve_left n1)
        apply hm (k0 + 1 + 1 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (.un (a := c) (Or.inr (sub_C _ _ (by simpa using hcS'))) (hb1.sol.mono le_rfl fun x hx => ?_))
        have h3 : x = a ∨ x = c ^^^ m ∨ x ∈ S1 := by
          have := hsub hx; simp at this
          rcases this with h | h
          · exact Or.inl h
          · have := hsub1 h; simp at this; exact Or.inr this
        rcases h3 with rfl | rfl | h3
        · exact Or.inr (Or.inr (sub_C _ _ (by simp)))
        · exact Or.inl rfl
        · rw [← hS1] at h3; simp at h3
          rcases h3 with rfl | h3
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (sub_C _ _ (by simp [h3])))
      have n4 : c' ^^^ m ≠ a ^^^ m := fun e => h2.fresh hb1 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      have hk3 := un_keep h2 hk2 n3
      have hg : op d (c ^^^ m) (c' ^^^ m) ≠ a ^^^ m := fun e => hb.fresh hl2 hm3.2 (sub_C _ _ (by rw [e]; simpa using hk3))
      refine Or.inr (Or.inr ⟨k0 + 1, t0 + 1, c, c', d, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, phi a (a ^^^ m) S4, rfl, rfl, ?_, hne,
        phi_un h2 n3 n4, phi_bi hb n2 n4 hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk3 n2 n4)).live hl2
lemma and_op (d : Bool) (a b n : ℕ) : op d a b &&& n = op d (a &&& n) (b &&& n) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases d <;> simp [op_bit] <;> grind
lemma and_neg {m n : ℕ} (hn : n &&& m = n) (a : ℕ) : (a ^^^ m) &&& n = (a &&& n) ^^^ n := by
  apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (fun x => x.testBit i) hn
  simp at this ⊢
  grind
abbrev Cst (n x : ℕ) : Prop := x &&& n = 0 ∨ x &&& n = n
def Im (n : ℕ) (S : Finset ℕ) : Set ℕ := (fun x => x &&& n) '' (S : Set ℕ)
lemma Im_mem {n x : ℕ} {S : Finset ℕ} (h : x ∈ S) : x &&& n ∈ C n (Im n S) := Or.inl ⟨x, by simpa using h, rfl⟩
lemma Cst_mem {n x : ℕ} {S : Set ℕ} (h : Cst n x) : x &&& n ∈ C n S := by
  rcases h with h | h <;> simp [C, h]
lemma Cst_neg {m n a : ℕ} (hn : n &&& m = n) : Cst n (a ^^^ m) ↔ Cst n a := by
  unfold Cst; rw [and_neg hn]
  constructor
  · rintro (h | h)
    · right; have := congrArg (· ^^^ n) h; simpa using this
    · left; have := congrArg (· ^^^ n) h; simpa using this
  · rintro (h | h) <;> simp [h]
lemma op_cst {n a b : ℕ} (d : Bool) (ha : Cst n a) :
    op d a b &&& n = 0 ∨ op d a b &&& n = n ∨ op d a b &&& n = b &&& n := by
  rw [and_op]
  rcases ha with h | h <;> rw [h] <;> cases d
  · left; simp [op]
  · right; right; simp [op]
  · right; right; apply Nat.eq_of_testBit_eq; intro i; simp [op]
  · right; left; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_cst2 {n a b : ℕ} (d : Bool) (ha : Cst n a) (hb : Cst n b) : Cst n (op d a b) := by
  rcases op_cst (b := b) d ha with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · unfold Cst at hb ⊢; rw [h]; exact hb
lemma op_cst_mem {n a b : ℕ} {S : Finset ℕ} (d : Bool) (h : Cst n a ∨ Cst n b) (ha : a ∈ S) (hb : b ∈ S) :
    op d a b &&& n ∈ C n (Im n S) := by
  rcases h with h | h
  · rcases op_cst (b := b) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem hb
  · rw [op_comm]
    rcases op_cst (b := a) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem ha
lemma C_Im_sub {n g : ℕ} {S S' : Finset ℕ} {Q : Set ℕ} (h : S' ⊆ insert g S) (hg : g &&& n ∈ Q)
    (hQ : C n (Im n S) ⊆ Q) : C n (Im n S') ⊆ Q := by
  rintro x (⟨y, hy, rfl⟩ | hx)
  · have := h hy; simp at this
    rcases this with rfl | h'
    · exact hg
    · exact hQ (Im_mem h')
  · exact hQ (Or.inr hx)
section proj
variable {m T n : ℕ} (hn : n &&& m = n)
include hn
lemma Un.im {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (Im_mem ha) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_neg hn]; exact Or.inl rfl
omit hn in
lemma Bi.im {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (Im_mem ha) (Im_mem hb) (al0 _ _ _) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
lemma Un.kill {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hc : Cst n a) (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2 (Cst_mem ((Cst_neg hn).2 hc)) subset_rfl)
omit hn in
lemma Bi.kill {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hc : Cst n a ∨ Cst n b)
    (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) : Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)
lemma Min.const (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n) {k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) :
    ∃ q, q + (S.filter (Cst n)).card ≤ k ∧ Sol Z0 n (T &&& n) q (C n (Im n S)) := by
  obtain ⟨hl, hm⟩ := h
  induction hl with
  | stop =>
    refine ⟨0, ?_, .done (Im_mem (by simp))⟩
    rw [Finset.filter_eq_empty_iff.2]; · simp
    intro x hx; simp at hx; subst hx
    rintro (h | h); exacts [hT0 h, hT1 h]
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have h1 : (U.filter (Cst n)).card ≤ ((insert (a ^^^ m) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    by_cases hc : Cst n a
    · refine ⟨q, ?_, hu.kill hn hc hs⟩
      rw [Finset.filter_insert, ite_eq_left hc]
      have := Finset.card_insert_le a (U.filter (Cst n)); omega
    · refine ⟨q + 1, ?_, hu.im hn hs⟩
      rw [Finset.filter_insert, ite_eq_right hc]; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (op d a b) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have ca := Finset.card_insert_le a (U.filter (Cst n))
    have cb := Finset.card_insert_le b (U.filter (Cst n))
    by_cases hca : Cst n a
    · refine ⟨q, ?_, hu.kill (Or.inl hca) hs⟩
      rw [Finset.filter_insert, ite_eq_left hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert, ite_eq_left (op_cst2 d hca hcb), Finset.card_insert_of_notMem (by simp [hf])] at hq
        have := Finset.card_insert_le a (insert b (U.filter (Cst n))); omega
      · rw [ite_eq_right hcb]; omega
    · rw [Finset.filter_insert, ite_eq_right hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · refine ⟨q, ?_, hu.kill (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]; omega
      · refine ⟨q + 1, ?_, hu.im hs⟩
        rw [ite_eq_right hcb]; omega
end proj
lemma Min.proper {m T k t : ℕ} (hT : T &&& m = T) (hT0 : T ≠ 0) (hT1 : T ≠ m) {S : Finset ℕ} (hS : ∀ x ∈ S, x &&& m = x)
    (h : Min R m T k t S) : 0 ∉ S ∧ m ∉ S := by
  obtain ⟨q, hq, hs⟩ := h.const (n := m) (by simp) (by rwa [hT]) (by rwa [hT])
  have hi : Im m S = (S : Set ℕ) := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; have := hS y hy; simp only; rw [this]; exact hy
    · intro hx; exact ⟨x, hx, hS x hx⟩
  rw [hi, hT] at hs
  have key : ∀ x ∈ S, ¬ Cst m x := by
    intro x hx hc
    have : 0 < (S.filter (Cst m)).card := Finset.card_pos.2 ⟨x, by simp [hx, hc]⟩
    exact h.2 q (by omega) hs
  exact ⟨fun h0 => key 0 h0 (Or.inl (by simp)), fun h1 => key m h1 (Or.inr (by simp))⟩
def sepb (N : ℕ) (d : Bool) (w i : ℕ) : Bool :=
  bif d then xor (w.testBit i) (w.testBit (N + i)) else w.testBit i && !w.testBit (N + i)
def pos' (t : ℕ) : Bool := decide (0 < t)
section cov
variable {N m T i : ℕ} (m1 : m.testBit i = true) (m2 : m.testBit (N + i) = true)
  (t1 : T.testBit i = true) (t2 : T.testBit (N + i) = false)
include t1 t2 m1 m2
lemma Live.cov {k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : ∃ w ∈ S, sepb N (pos' t) w i = true := by
  induction h with
  | stop => exact ⟨T, by simp, by simp [sepb, pos', t1, t2]⟩
  | @un k t a U _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    have weak : sepb N true w i = true := by
      revert hs; cases pos' t <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨a, by simp, ?_⟩
      revert weak; simp [sepb, pos', m1, m2]
    · exact ⟨w, by simp [hw], by simpa [pos'] using weak⟩
  | @bi k t d a b U _ _ _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    simp at hw
    rcases hw with rfl | hw
    · by_cases ha : sepb N (pos' t) a i = true
      · exact ⟨a, by simp, ha⟩
      · refine ⟨b, by simp, ?_⟩
        revert hs ha
        unfold sepb; simp only [op_bit]
        cases pos' t <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact ⟨w, by simp [hw], hs⟩
end cov
def Uq (N : ℕ) (e : Bool) (S : Finset ℕ) (a i : ℕ) : Prop :=
  sepb N e a i = true ∧ ∀ c ∈ S, c ≠ a → sepb N e c i = false
lemma sepb_weak {N w i : ℕ} (e : Bool) (h : sepb N e w i = true) : sepb N true w i = true := by
  revert h; cases e <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
section rect
variable {N m T : ℕ}
def Lg (N m T i : ℕ) : Prop := m.testBit i = true ∧ m.testBit (N + i) = true ∧ T.testBit i = true ∧ T.testBit (N + i) = false
lemma bi_uq {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (hi : Lg N m T i)
    (hc : c ∈ insert a (insert b U)) (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl
      rcases hcc with rfl | rfl; exacts [ha hx, hb hx]
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma un_uq {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (ha : a ∉ U)
    (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
  by_cases hcc : c = a
  · rw [ite_eq_left hcc]; subst hcc
    refine ⟨by rw [hn]; exact h.1, fun x hx hne => ?_⟩
    simp at hx
    exact h.2 x (by simp [hx.resolve_left hne]) (fun e => ha (e ▸ hx.resolve_left hne))
  · rw [ite_eq_right hcc]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hcc)
    · exact h.2 x (by simp [hx]) hne
lemma phi_mem {x y g c : ℕ} {U : Finset ℕ} (hc : c ∈ insert x (insert y U)) :
    (if c = x ∨ c = y then g else c) ∈ insert g U := by
  split_ifs with h
  · simp
  · simp only [Finset.mem_insert] at hc ⊢; tauto
lemma phi_ne {x y g a b : ℕ} {U : Finset ℕ} (hg : g ∉ U) (ha : a ∈ insert x (insert y U)) (hb : b ∈ insert x (insert y U))
    (hab : a ≠ b) (h : ¬ ((a = x ∨ a = y) ∧ (b = x ∨ b = y))) :
    (if a = x ∨ a = y then g else a) ≠ (if b = x ∨ b = y then g else b) := by
  simp only [Finset.mem_insert] at ha hb
  split_ifs with p q q
  · exact absurd ⟨p, q⟩ h
  · rintro rfl; tauto
  · rintro rfl; tauto
  · exact hab
lemma bi_tight {a b k t : ℕ} {d : Bool} {U : Finset ℕ} (hab : a ≠ b) (hal : Al R d a b) (hl : Live R m T k t (insert (op d a b) U))
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m ((insert a (insert b U) : Finset ℕ) : Set ℕ)))
    (hc : (insert a (insert b U)).card + t = k + 2) :
    a ∉ U ∧ b ∉ U ∧ op d a b ∉ U ∧ (insert (op d a b) U).card + t = k + 1 ∧ Min R m T k t (insert (op d a b) U) := by
  have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
  have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a (insert b U)
  have h2 := Finset.card_insert_le b U
  have ha : a ∉ insert b U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  have hb : b ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc h1; omega
  exact ⟨fun h => ha (by simp [h]), hb, hf, by omega, hmin⟩
lemma un_tight {a k t : ℕ} {U : Finset ℕ} (hl : Live R m T k t (insert (a ^^^ m) U))
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m ((insert a U : Finset ℕ) : Set ℕ)))
    (hc : (insert a U).card + (t + 1) = k + 2) :
    a ∉ U ∧ a ^^^ m ∉ U ∧ (insert (a ^^^ m) U).card + t = k + 1 ∧ Min R m T k t (insert (a ^^^ m) U) := by
  have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
  have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a U
  have ha : a ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  exact ⟨ha, hf, by omega, hmin⟩
lemma rect0 {k : ℕ} {S : Finset ℕ} (hl : Live R m T k 0 S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N false S a i1 → Uq N false S b i2 → Uq N false S a j1 → Uq N false S b j2 → False := by
  generalize ht : 0 = t at hl
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | un => omega
  | @bi k t d x y U hxy hal hl ih =>
    subst ht
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by simpa using hc)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N false (insert x (insert y U)) c i →
        Uq N false (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inr (by simp [pos'])) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4
      have e1 := r1 b hb; have e2 := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have s1 := v1.1; have s3 := v3.1; have s2 := u2.1; have s4 := u4.1
      revert e1 e2 n1 n3 s1 s3 s2 s4
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 (by simpa using hc') rfl ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
lemma polar {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i j : ℕ} (h1 : Lg N m T i) (h2 : Lg N m T j) :
    ∀ {a : ℕ}, a ∈ S → Uq N true S a i → Uq N true S a j → a.testBit i = a.testBit j := by
  induction hl with
  | stop => intro a ha _ _; simp at ha; subst ha; rw [h1.2.2.1, h2.2.2.1]
  | @un k t x U hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    have := ih hmin.2 hc' (a := if a = x then x ^^^ m else a) (by split_ifs with h <;> simp at ha ⊢; tauto)
      (un_uq h1 hx ha u1) (un_uq h2 hx ha u2)
    split_ifs at this with h
    · subst h; simpa [h1.1, h2.1] using this
    · exact this
  | @bi k t d x y U hxy hal hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have v1 := bi_uq (Or.inl rfl) hl hx hy h1 ha u1
    have v2 := bi_uq (Or.inl rfl) hl hx hy h2 ha u2
    have := ih hmin.2 hc' (phi_mem ha) v1 v2
    split_ifs at this v1 v2 with h
    · obtain ⟨b, hb, hab, hop⟩ : ∃ b ∈ insert x (insert y U), b ≠ a ∧ op d x y = op d a b := by
        rcases h with rfl | rfl
        · exact ⟨y, by simp, Ne.symm hxy, rfl⟩
        · exact ⟨x, by simp, hxy, op_comm _ _ _⟩
      rw [hop] at this v1 v2
      have n1 := u1.2 b hb hab; have n2 := u2.2 b hb hab
      have s1 := v1.1; have s2 := v2.1; have p1 := u1.1; have p2 := u2.1
      revert this n1 n2 s1 s2 p1 p2
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · exact this
lemma rect1 {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N true S a i1 → Uq N true S b i2 → Uq N true S a j1 → Uq N true S b j2 → False := by
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t x U hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (un_uq h1 hx ha u1) (un_uq h2 hx hb u2) (un_uq h3 hx ha u3) (un_uq h4 hx hb u4)
    · split_ifs with h <;> simp at ha ⊢; tauto
    · split_ifs with h <;> simp at hb ⊢; tauto
    · split_ifs with p q q
      · exact absurd (p.trans q.symm) hab
      · intro e; simp at hb; rw [← e] at hb; rcases hb with h | h
        · exact q (by rw [← e, h])
        · exact hg h
      · intro e; simp at ha; rw [e] at ha; rcases ha with h | h
        · exact p (by rw [e, h])
        · exact hg h
      · exact hab
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r1 x (by simp), h1.1, h2.1]
      · exact r1 w (by simp [hw])
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r2 x (by simp), h3.2.1, h4.2.1]
      · exact r2 w (by simp [hw])
  | @bi k t d x y U hxy hal hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N true (insert x (insert y U)) c i →
        Uq N true (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inl rfl) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hpol := polar hl hmin.2 hc' h1 h3 (by simp) v1 v3
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4 hpol
      have e1 := r1 a ha; have e2 := r2 a ha; have e1b := r1 b hb; have e2b := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have n2 := u2.2 a ha hab; have n4 := u4.2 a ha hab
      have s1 := v1.1; have s3 := v3.1; have s2 := v2.1; have s4 := v4.1
      have p1 := u1.1; have p2 := u2.1; have p3 := u3.1; have p4 := u4.1
      revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 p1 p2 p3 p4 hpol
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
end rect
section chrom
variable {N m T : ℕ}
def Ht (N m T : ℕ) (e : Bool) (S : Finset ℕ) (a b : ℕ) : Prop := ∃ i1 i2 j1 j2, Lg N m T i1 ∧ Lg N m T i2 ∧ Lg N m T j1 ∧ Lg N m T j2 ∧
  (∀ w ∈ S, w.testBit i1 = w.testBit i2) ∧ (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) ∧
  Uq N e S a i1 ∧ Uq N e S b i2 ∧ Uq N e S a j1 ∧ Uq N e S b j2 ∧ a.testBit i1 = a.testBit j1 ∧ b.testBit i2 = b.testBit j2
lemma Ht.symm {e : Bool} {S : Finset ℕ} {a b : ℕ} (h : Ht N m T e S a b) : Ht N m T e S b a := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  exact ⟨i2, i1, j2, j1, l2, l1, l4, l3, fun w hw => (r1 w hw).symm, fun w hw => (r2 w hw).symm, u2, u1, u4, u3, p2, p1⟩
lemma bi_uq2 {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hi : Lg N m T i) (hc : c ∈ insert a (insert b U)) (h1 : c = a → a ∉ U) (h2 : c = b → b ∉ U)
    (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hcU : c ∉ U := by
      rcases hcc with rfl | rfl; exacts [h1 rfl, h2 rfl]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl; exact hcU hx
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma pol_op {a b i : ℕ} {d e : Bool} (ha : sepb N e a i = true) (hb : sepb N e b i = false) (ho : sepb N e (op d a b) i = true) :
    (op d a b).testBit i = a.testBit i := by
  revert ha hb ho; unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
    cases b.testBit (N + i) <;> simp
lemma pol_phi {a b c i : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (h : Uq N e (insert a (insert b U)) c i)
    (hu : Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i) :
    (if c = a ∨ c = b then op d a b else c).testBit i = c.testBit i := by
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc] at hu ⊢
    rcases hcc with rfl | rfl
    · exact pol_op h.1 (h.2 b (by simp) (Ne.symm hab)) hu.1
    · rw [op_comm] at hu ⊢
      exact pol_op h.1 (h.2 a (by simp) hab) hu.1
  · rw [ite_eq_right hcc]
lemma ht_bi {a b k t c1 c2 : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hc1 : c1 ∈ insert a (insert b U)) (hc2 : c2 ∈ insert a (insert b U))
    (h1 : c1 = a → a ∉ U) (h1' : c1 = b → b ∉ U) (h2 : c2 = a → a ∉ U) (h2' : c2 = b → b ∉ U)
    (h : Ht N m T e (insert a (insert b U)) c1 c2) :
    Ht N m T e (insert (op d a b) U) (if c1 = a ∨ c1 = b then op d a b else c1) (if c2 = a ∨ c2 = b then op d a b else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := bi_uq2 he hl l1 hc1 h1 h1' u1
  have v2 := bi_uq2 he hl l2 hc2 h2 h2' u2
  have v3 := bi_uq2 he hl l3 hc1 h1 h1' u3
  have v4 := bi_uq2 he hl l4 hc2 h2 h2' u4
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, v1, v2, v3, v4, ?_, ?_⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r1 a (by simp), r1 b (by simp)]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r2 a (by simp), r2 b (by simp)]
    · exact r2 w (by simp [hw])
  · rw [pol_phi hab u1 v1, pol_phi hab u3 v3, p1]
  · rw [pol_phi hab u2 v2, pol_phi hab u4 v4, p2]
lemma ht_merge {a b k t : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (h : Ht N m T e (insert a (insert b U)) a b) : False := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := (bi_uq2 he hl l1 (by simp) (fun _ => ha) (fun _ => hb) u1).1
  have v2 := (bi_uq2 he hl l2 (by simp) (fun _ => ha) (fun _ => hb) u2).1
  have v3 := (bi_uq2 he hl l3 (by simp) (fun _ => ha) (fun _ => hb) u3).1
  have v4 := (bi_uq2 he hl l4 (by simp) (fun _ => ha) (fun _ => hb) u4).1
  simp only [true_or, or_true, if_true] at v1 v2 v3 v4
  have e1 := r1 a (by simp); have e2 := r2 a (by simp); have e1b := r1 b (by simp); have e2b := r2 b (by simp)
  have n1 := u1.2 b (by simp) (Ne.symm hab); have n3 := u3.2 b (by simp) (Ne.symm hab)
  have n2 := u2.2 a (by simp) hab; have n4 := u4.2 a (by simp) hab
  have s1 := u1.1; have s2 := u2.1; have s3 := u3.1; have s4 := u4.1
  revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 v1 v2 v3 v4 p1 p2
  unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> simp <;> grind
lemma un_uq2 {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (h1 : c = a → a ∉ U) (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  by_cases hca : c = a
  · exact un_uq hi (h1 hca) hc h
  · rw [ite_eq_right hca]
    have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
    · exact h.2 x (by simp [hx]) hne
lemma ht_un {a c1 c2 : ℕ} {U : Finset ℕ} (hc1 : c1 ∈ insert a U) (hc2 : c2 ∈ insert a U) (h1 : c1 = a → a ∉ U) (h2 : c2 = a → a ∉ U)
    (h : Ht N m T true (insert a U) c1 c2) :
    Ht N m T true (insert (a ^^^ m) U) (if c1 = a then a ^^^ m else c1) (if c2 = a then a ^^^ m else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have pp : ∀ {c i j : ℕ}, m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
      (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j := by
    intro c i j m1 m2 p
    split_ifs with h
    · subst h; simp [m1, m2, p]
    · exact p
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, un_uq2 l1 h1 hc1 u1, un_uq2 l2 h2 hc2 u2, un_uq2 l3 h1 hc1 u3, un_uq2 l4 h2 hc2 u4,
    pp l1.1 l3.1 p1, pp l2.1 l4.1 p2⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r1 a (by simp), l1.1, l2.1]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r2 a (by simp), l3.2.1, l4.2.1]
    · exact r2 w (by simp [hw])
lemma chrom {e : Bool} {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (he : e = true ∨ t = 0) :
    ∃ (x : ℕ) (f : ℕ → ℕ), S.card + t + x = k + 1 ∧ (∀ a ∈ S, f a ≤ x) ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Ht N m T e S a b → f a ≠ f b := by
  induction hl with
  | stop =>
    refine ⟨0, fun _ => 0, by simp, by simp, ?_⟩
    intro a ha b hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t a U hl ih =>
    have he1 : e = true := he.resolve_right (by omega)
    subst he1
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have hmin := hu.min hl hm
    obtain ⟨x, f, hx, hfx, hc⟩ := ih hmin.2 (Or.inl rfl)
    rw [Finset.card_insert_of_notMem hf] at hx
    have sm : ∀ {i1 i2 : ℕ}, m.testBit i1 = true → m.testBit i2 = true → (∀ w ∈ insert a U, w.testBit i1 = w.testBit i2) →
        ∀ w ∈ insert (a ^^^ m) U, w.testBit i1 = w.testBit i2 := by
      intro i1 i2 m1 m2 r w hw
      simp at hw
      rcases hw with rfl | hw
      · simp [r a (by simp), m1, m2]
      · exact r w (by simp [hw])
    by_cases ha : a ∈ U
    · have eS : insert a U = U := Finset.insert_eq_of_mem ha
      refine ⟨x + 1, fun c => if c = a then x + 1 else f c, by rw [eS]; omega, ?_, ?_⟩
      · intro c hcS
        rw [eS] at hcS
        by_cases hca : c = a
        · simp [hca]
        · simp only [hca, if_false]
          have := hfx c (by simp [hcS]); omega
      · intro c1 h1 c2 h2 h12 hh
        rw [eS] at h1 h2
        by_cases q1 : c1 = a
        · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
          have := hfx c2 (by simp [h2])
          simp only [q1, q2, if_true, if_false]; omega
        · by_cases q2 : c2 = a
          · have := hfx c1 (by simp [h1])
            simp only [q1, q2, if_true, if_false]; omega
          · simp only [q1, q2, if_false]
            refine hc c1 (by simp [h1]) c2 (by simp [h2]) h12 ?_
            obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := hh
            have tr : ∀ {c i : ℕ}, c ≠ a → Lg N m T i → Uq N true (insert a U) c i → Uq N true (insert (a ^^^ m) U) c i := by
              intro c i hca hi h
              refine ⟨h.1, fun y hy hne => ?_⟩
              simp at hy
              rcases hy with rfl | hy
              · have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
                rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
              · exact h.2 y (by simp [hy]) hne
            exact ⟨i1, i2, j1, j2, l1, l2, l3, l4, sm l1.1 l2.1 r1, sm l3.2.1 l4.2.1 r2, tr q1 l1 u1, tr q2 l2 u2, tr q1 l3 u3, tr q2 l4 u4, p1, p2⟩
    · rw [Finset.card_insert_of_notMem ha]
      have mem : ∀ {c : ℕ}, c ∈ insert a U → (if c = a then a ^^^ m else c) ∈ insert (a ^^^ m) U := by
        intro c hcS; split_ifs with h <;> simp at hcS ⊢; tauto
      refine ⟨x, fun c => f (if c = a then a ^^^ m else c), by omega, fun c hcS => hfx _ (mem hcS), ?_⟩
      intro c1 h1 c2 h2 h12 hh
      refine hc _ (mem h1) _ (mem h2) ?_ ?_
      · split_ifs with p q q
        · exact absurd (p.trans q.symm) h12
        · intro e; simp at h2; rw [← e] at h2; rcases h2 with h | h
          · exact q (by rw [← e, h])
          · exact hf h
        · intro e; simp at h1; rw [e] at h1; rcases h1 with h | h
          · exact p (by rw [e, h])
          · exact hf h
        · exact h12
      · obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := hh
        have pp : ∀ {c i j : ℕ}, m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
            (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j := by
          intro c i j m1 m2 p
          split_ifs with h
          · subst h; simp [m1, m2, p]
          · exact p
        exact ⟨i1, i2, j1, j2, l1, l2, l3, l4, sm l1.1 l2.1 r1, sm l3.2.1 l4.2.1 r2, un_uq l1 ha h1 u1, un_uq l2 ha h2 u2, un_uq l3 ha h1 u3, un_uq l4 ha h2 u4,
          pp l1.1 l3.1 p1, pp l2.1 l4.1 p2⟩
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have hfS : op d a b ∉ insert a (insert b U) := fun h => hu.fresh hl hm (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by simp [h])
    have hmin := hu.min hl hm
    have he2 : e = true ∨ e = pos' t := by
      rcases he with h | h
      · exact Or.inl h
      · subst h; cases e <;> simp [pos']
    obtain ⟨x, f, hx, hfx, hc⟩ := ih hmin.2 he
    rw [Finset.card_insert_of_notMem hf] at hx
    have mem : ∀ {c : ℕ}, c ∈ insert a (insert b U) → (if c = a ∨ c = b then op d a b else c) ∈ insert (op d a b) U := fun h => phi_mem h
    by_cases ha : a ∈ U
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = U := by rw [Finset.insert_eq_of_mem hb, Finset.insert_eq_of_mem ha]
        refine ⟨x + 2, fun c => if c = a then x + 2 else if c = b then x + 1 else f c, by rw [eS]; omega, ?_, ?_⟩
        · intro c hcS
          rw [eS] at hcS
          have := hfx c (by simp [hcS])
          dsimp only; split_ifs <;> omega
        · intro c1 h1 c2 h2 h12 hh
          have k1 := h1; have k2 := h2
          rw [eS] at h1 h2
          have f1 := hfx c1 (by simp [h1]); have f2 := hfx c2 (by simp [h2])
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
            · by_cases q3 : c1 = b
              · have q4 : c2 ≠ b := fun e => h12 (q3.trans e.symm)
                simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
              · by_cases q4 : c2 = b
                · simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
                · simp only [q1, q2, q3, q4, if_false]
                  have := ht_bi hab he2 hl k1 k2 (fun e => absurd e q1) (fun e => absurd e q3) (fun e => absurd e q2) (fun e => absurd e q4) hh
                  simp only [q1, q2, q3, q4, or_self, if_false] at this
                  exact hc c1 (by simp [h1]) c2 (by simp [h2]) h12 this
      · have eS : insert a (insert b U) = insert b U := Finset.insert_eq_of_mem (by simp [ha])
        refine ⟨x + 1, fun c => if c = a then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem hb]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = a
          · simp [hca]
          · simp only [hca, if_false, false_or] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, false_or] at f2 ⊢; omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false, false_or] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun e => absurd e q1) (fun _ => hb) (fun e => absurd e q2) (fun _ => hb) hh
              simp only [q1, q2, if_false, false_or] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = b ∨ c1 ∈ U := by simp at h1; tauto
              have h2' : c2 = b ∨ c2 ∈ U := by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = insert a U := by rw [Finset.insert_eq_of_mem hb]
        refine ⟨x + 1, fun c => if c = b then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem ha]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = b
          · simp [hca]
          · simp only [hca, if_false, or_false] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = b
          · have q2 : c2 ≠ b := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, or_false] at f2 ⊢; omega
          · by_cases q2 : c2 = b
            · simp only [q1, q2, if_true, if_false, or_false] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun e => absurd e q1) (fun _ => ha) (fun e => absurd e q2) hh
              simp only [q1, q2, if_false, or_false] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = a ∨ c1 ∈ U := by simp at h1; tauto
              have h2' : c2 = a ∨ c2 ∈ U := by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
      · refine ⟨x, fun c => f (if c = a ∨ c = b then op d a b else c), ?_, fun c hcS => hfx _ (mem hcS), ?_⟩
        · rw [Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hb]; omega
        · intro c1 h1 c2 h2 h12 hh
          by_cases hab' : (c1 = a ∨ c1 = b) ∧ (c2 = a ∨ c2 = b)
          · exfalso
            have : Ht N m T e (insert a (insert b U)) a b := by
              rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
              · exact absurd rfl h12
              · exact hh
              · exact hh.symm
              · exact absurd rfl h12
            exact ht_merge hab he2 hl ha hb this
          · exact hc _ (mem h1) _ (mem h2) (phi_ne hf h1 h2 h12 hab')
              (ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun _ => hb) (fun _ => ha) (fun _ => hb) hh)
end chrom
structure W where
  s : Nat
  a : Nat
  b : Nat
  c : Nat
  r : Nat
structure X where
  w : W
  s : Nat
  q : Nat
  u : Nat
structure Cm where
  a : List Nat
  b : List Nat
def NN : Nat := 663
def AA : Nat := bigNat_0
def HX : Nat := bigNat_1
def HY : Nat := bigNat_2
noncomputable section core
def st (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f m) (Nat.succ n)
def sp (d : Bool) (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) (Bool.rec (motive := fun _ => Nat) (Nat.land s l) l d)
def cov (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor (sp d l w.s) ih) v
def twice (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (sp d l w.s) (cov d l t)) ih) v
def hit (f e : Nat) : Bool := (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (true) (false) (Nat.beq (Nat.land (Nat.land f e) HY) 0))) (false) (Nat.beq (Nat.land (Nat.land f e) HX) 0))
def hits (f : Nat) (m : List Nat) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun e _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (hit f e))) (m))
def flag (d : Bool) (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (sp d l w.s) o) AA
def rect (d : Bool) (l o : Nat) (v : List W) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => (Bool.rec (motive := fun _ => Bool) (ih (flag d l o w :: m)) (true) (hits (flag d l o w) m))) v
def app (x y : List Nat) : List Nat := List.rec (motive := fun _ => List Nat) y (fun e _ ih => e :: ih) x
def join (k : List Cm → Bool) (f : Nat) (cs : List Cm) : List Nat → List Nat → List Cm → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → List Cm → Bool) (fun S O R => k (⟨S, O⟩ :: R))
    (fun c _ ih S O R => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih S O (c :: R)) (ih (app c.a S) (app c.b O) R) (hits f c.b))
      (Bool.rec (motive := fun _ => Bool) (ih (app c.b S) (app c.a O) R) true (hits f c.b)) (hits f c.a)) cs
def bip (l o : Nat) (v : List W) : List Cm → Bool :=
  List.rec (motive := fun _ => List Cm → Bool) (fun _ => false)
    (fun w _ ih cs => (fun f => join ih f cs [f] [] []) (flag false l o w)) v
def anyE (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) false (fun f t ih => Bool.rec (motive := fun _ => Bool) ih true (hits f t)) m
def rmF (f : Nat) (m : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun e t ih => Bool.rec (motive := fun _ => List Nat) (e :: ih) t (hit f e)) m
def star (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) true (fun f t ih => Bool.rec (motive := fun _ => Bool) ih
  (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false (anyE (rmF f t))) false (hits f (rmF f t))) (anyE t)) (hits f t)) m
def flk (l o : Nat) (v : List W) : (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k []) (fun w _ ih k => (fun f => ih (fun r => k (f :: r))) (flag false l o w)) v
def mkX (d : Bool) (l o : Nat) (v : List W) : List X :=
  List.rec (motive := fun _ => List X) [] (fun w _ ih => ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩ :: ih) v
def rm (x y : Nat) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (ih h) (Nat.beq w.s y)) (ih h) (Nat.beq w.s x)) v
def ins (o : W) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [o]) (fun w t ih h => Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive := fun _ => Bool) (h (o :: w :: t)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def child (f : Nat → List W → Bool) (g : Nat) (mk : (List W → Bool) → Bool) (z : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (st z (fun z => mk (f z))) (Nat.beq (Nat.land z g) g)
def put (m s x y : Nat) (v : List W) (h : List W → Bool) : Bool :=
  (st (s) (fun s => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((st (x) (fun x1 => (st (y) (fun y1 => (st (Nat.lor x y) (fun w => ins ⟨s, x1, y1, w, 0⟩ v h))))))) (false) (Nat.beq s m))) (false) (Nat.beq s 0))))
def kids (c : ((List W → Bool) → Bool) → Nat → Bool) (e n z x y a c' : Nat) (oa oc : Bool) (mk : (List W → Bool) → Bool) : Bool :=
  (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c mk (Nat.sub (Nat.sub z x) y)) (Nat.ble (Nat.succ (Nat.succ n)) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm a a r h)) (Nat.sub z y)) (oa))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm c' c' r h)) (Nat.sub z x)) (oc))))) (Nat.ble (Nat.succ n) e))))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm a c' r h)) z) (oc))) (oa))))
def mid (f : Nat → List W → Bool) (m g e n z : Nat) (v : List W) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) ((st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) (fun z => kids (child f g) e n z a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v)))) (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g))
def f0 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.lor da dc) 0))
def f1 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.mul da dc) 0))
def f2 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool := h a c da dc s x y
def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : X) : Bool :=
  X.rec (motive := fun _ => Bool) (fun a s q u => X.rec (motive := fun _ => Bool) (fun c s' q' u' => (Bool.rec (motive := fun _ => Bool) (h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)) (true) (h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b)))) c) a
def scan (p : X → Bool) (xs : List X) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun c _ jh => (Bool.rec (motive := fun _ => Bool) (jh) (true) (p c))) (xs))
def pairs (h : X → X → Bool) (xs : List X) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a r ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (scan (h a) r))) (xs))
def pairsP (q : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (h a c) (false) (Nat.beq c.s q))) xs) (Nat.beq a.s q))) xs
def pairsQ (q q' : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (false) (h a c) (Nat.beq c.s q'))) xs) (Nat.beq a.s q))) xs
def fr (xs : List X) : List X := List.rec (motive := fun _ => List X) [] (fun a _ ih => Bool.rec (motive := fun _ => List X) ih (a :: ih) (Nat.beq a.w.r 0)) xs
def fs (xs : List X) : List X := List.rec (motive := fun _ => List X) [] (fun a _ ih => Bool.rec (motive := fun _ => List X) (a :: ih) ih (Nat.beq a.w.r 0)) xs
def pairsN (h : X → X → Bool) (xs : List X) : Bool :=
  Bool.rec (motive := fun _ => Bool) (scan (fun a => scan (h a) (fs xs)) (fr xs)) true (pairs h (fr xs))
def pairsS (h : X → X → Bool) (xs : List X) : Bool := pairs h (fs xs)
def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) ((Bool.rec (motive := fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st (Nat.sub z a.c) (fun z => ins ⟨s, a.b, a.a, a.c, 0⟩ v (fun v => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))
def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t
def wst (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twice d l v)
def node (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (X → X → Bool) → List X → Bool) : Bool :=
  (fun h => (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive := fun _ => Bool) (go (pair (f1 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkX d l (wst d l v) v))
  (mid f m g e (Nat.pred n) z v)
def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t
def cv (d : Bool) (l : Nat) (v : List W) (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false b (Nat.beq (cov d l v) l)) b d
def tst (d : Bool) (l e : Nat) (v : List W) (F : Nat → Bool) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flk l (wst d l v) v star)) false (bip l (wst d l v) v []))
      (Nat.beq (Nat.succ n) e))
    (Bool.rec (motive := fun _ => Bool) (F 0) false (rect d l (wst d l v) v [])) (Nat.beq n e)) v.length
def mv (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          node (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (node (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v v)) true
    (node (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length
def look (l m g : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mv ih l m g k t z v y)) true (Nat.ble v.length 1)) fuel
def look1 (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) fuel
end core
lemma bR (c e t : Bool) : (Bool.rec (motive := fun _ => Bool) e t c : Bool) = bif c then t else e := by cases c <;> rfl
lemma st_eq (n : ℕ) (f : ℕ → Bool) : st n f = f n := by cases n <;> rfl
lemma nl (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma no (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nx (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nsr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma sp_bit (d : Bool) (l s i : ℕ) : (sp d l s).testBit i = (l.testBit i && sepb NN d s i) := by
  cases d <;> simp [sp, sepb, nl, nx, nsr, Nat.testBit_shiftRight] <;>
    cases l.testBit i <;> cases s.testBit i <;> cases s.testBit (NN + i) <;> rfl
lemma cov_bit (d : Bool) (l i : ℕ) (v : List W) : (cov d l v).testBit i = true ↔ ∃ w ∈ v, (sp d l w.s).testBit i = true := by
  induction v with
  | nil => simp [cov]
  | cons w v ih =>
    change (Nat.lor (sp d l w.s) (cov d l v)).testBit i = true ↔ _
    simp [no, ih]
lemma twice_bit (d : Bool) (l i : ℕ) (v : List W) (h : (twice d l v).testBit i = false) :
    v.Pairwise (fun w w' => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) := by
  induction v with
  | nil => simp
  | cons w v ih =>
    change (Nat.lor (Nat.land (sp d l w.s) (cov d l v)) (twice d l v)).testBit i = false at h
    simp only [no, nl, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff] at h
    refine List.pairwise_cons.2 ⟨fun w' hw' ⟨h1, h2⟩ => ?_, ih h.2⟩
    have := (cov_bit d l i v).2 ⟨w', hw', h2⟩
    simp [h1, this] at h
def Rep (v : List W) (S : Finset ℕ) : Prop := (v.map W.s).Nodup ∧ (v.map W.s).toFinset = S
lemma Rep.mem {v : List W} {S : Finset ℕ} (h : Rep v S) {x : ℕ} : x ∈ S ↔ ∃ w ∈ v, w.s = x := by
  rw [← h.2]; simp
lemma Rep.inj {v : List W} {S : Finset ℕ} (h : Rep v S) {w w' : W} (hw : w ∈ v) (hw' : w' ∈ v) (e : w.s = w'.s) : w = w' :=
  List.inj_on_of_nodup_map h.1 hw hw' e
lemma Rep.card {v : List W} {S : Finset ℕ} (h : Rep v S) : S.card = v.length := by
  rw [← h.2, List.toFinset_card_of_nodup h.1, List.length_map]
lemma uq_of {d : Bool} {l i : ℕ} {v : List W} {S : Finset ℕ} (h : Rep v S) {w : W} (hw : w ∈ v)
    (hu : (Nat.land (sp d l w.s) (wst d l v)).testBit i = true) : l.testBit i = true ∧ Uq NN d S w.s i := by
  simp only [nl, wst, nx, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true, sp_bit] at hu
  obtain ⟨⟨hl, hs⟩, ht⟩ := hu
  have ht : (twice d l v).testBit i = false := by simpa [hl] using ht
  refine ⟨hl, hs, fun c hc hne => ?_⟩
  obtain ⟨w', hw', rfl⟩ := h.mem.1 hc
  have hp := twice_bit d l i v ht
  haveI : Std.Symm (fun w w' : W => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) :=
    ⟨fun a b h h' => h h'.symm⟩
  have := hp.forall hw hw' (fun e => hne (by rw [e]))
  simp only [sp_bit, hl, hs, Bool.true_and, true_and] at this
  simpa using this
def segsX : List (ℕ × ℕ) := [(63, 75), (75, 78), (78, 81), (81, 84), (84, 96), (96, 108), (108, 110), (110, 122), (122, 124), (124, 126), (126, 128), (128, 130), (130, 133), (133, 136), (136, 138), (138, 150), (150, 162), (162, 164), (164, 167), (167, 170), (170, 172), (172, 184), (184, 186), (186, 189), (189, 191), (191, 193), (193, 195), (195, 198), (198, 201), (201, 213), (213, 216), (216, 228), (228, 231), (231, 233), (233, 235), (235, 247), (247, 249), (249, 251), (251, 253), (253, 255), (255, 258), (258, 260), (260, 262), (262, 265), (265, 268), (268, 270), (270, 273), (273, 275), (275, 277), (277, 279), (279, 281), (281, 283), (283, 295), (295, 307), (307, 309), (309, 321), (321, 323), (323, 325), (325, 327), (327, 329), (329, 332), (332, 335), (335, 337), (337, 349), (349, 352), (352, 364), (364, 366), (366, 368), (368, 370), (370, 373), (373, 375), (375, 377), (377, 380), (380, 383), (383, 386), (386, 388)]
def segsY : List (ℕ × ℕ) := [(388, 404), (404, 409), (409, 414), (414, 420), (420, 424), (424, 430), (430, 435), (435, 456), (456, 460), (460, 466), (466, 472), (472, 493), (493, 498), (498, 520), (520, 525), (525, 547), (547, 553), (553, 557), (557, 579), (579, 585), (585, 591), (591, 612), (612, 618), (618, 640), (640, 662)]
def segOk (s : ℕ × ℕ) : Bool := decide (s.1 < s.2) && decide (AA % 2 ^ s.2 + 2 ^ (s.1 + 1) = 2 ^ s.2 + AA % 2 ^ s.1) &&
  !AA.testBit s.1 && !AA.testBit s.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segX_ok : segsX.all segOk = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segY_ok : segsY.all segOk = true := by decide +kernel
def bitsOf (L : List (ℕ × ℕ)) : ℕ := L.foldr (fun s x => 2 ^ s.2 ||| x) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HX_eq : HX = bitsOf segsX := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HY_eq : HY = bitsOf segsY := by decide +kernel
lemma bitsOf_bit {L : List (ℕ × ℕ)} {h : ℕ} (hh : (bitsOf L).testBit h = true) : ∃ s ∈ L, s.2 = h := by
  induction L with
  | nil => simp [bitsOf] at hh
  | cons s L ih =>
    change (2 ^ s.2 ||| bitsOf L).testBit h = true at hh
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact ⟨s, by simp, by simpa using hh⟩
    · obtain ⟨s', hs', e⟩ := ih hh; exact ⟨s', by simp [hs'], e⟩
lemma carry {u A p h : ℕ} (hp : p < h) (hA : A % 2 ^ h + 2 ^ (p + 1) = 2 ^ h + A % 2 ^ p) (hAh : A.testBit h = false)
    (huh : u.testBit h = false) (hup : u.testBit p = false) (hs : (u + A).testBit h = true) :
    ∃ i, p < i ∧ i < h ∧ u.testBit i = true := by
  by_contra hno
  push Not at hno
  have e1 : u % 2 ^ h = u % 2 ^ p := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_mod_two_pow]
    by_cases h1 : i < p
    · simp [h1, show i < h by omega]
    · by_cases h2 : i < h
      · rcases Nat.lt_or_ge p i with h3 | h3
        · simp [h1, hno i h3 h2]
        · obtain rfl : i = p := by omega
          simp [hup]
      · simp [h1, h2]
  have l1 := Nat.mod_lt u (Nat.two_pow_pos p)
  have l2 := Nat.mod_lt A (Nat.two_pow_pos p)
  have hlt : u % 2 ^ h + A % 2 ^ h < 2 ^ h := by rw [e1]; have := Nat.pow_succ 2 p; omega
  have e2 : (u + A).testBit h = (u / 2 ^ h + A / 2 ^ h).testBit 0 := by
    have : u + A = 2 ^ h * (u / 2 ^ h + A / 2 ^ h) + (u % 2 ^ h + A % 2 ^ h) := by
      have a1 := Nat.div_add_mod u (2 ^ h); have a2 := Nat.div_add_mod A (2 ^ h)
      rw [Nat.mul_add]; omega
    rw [this, Nat.testBit_two_pow_mul_add _ hlt]; simp
  have b1 : (u / 2 ^ h).testBit 0 = false := by rw [← huh, Nat.testBit_div_two_pow]; simp
  have b2 : (A / 2 ^ h).testBit 0 = false := by rw [← hAh, Nat.testBit_div_two_pow]; simp
  rw [e2] at hs
  simp [Nat.testBit_zero] at hs b1 b2
  omega
def Same (L : List (ℕ × ℕ)) (i j : ℕ) : Prop := ∃ s ∈ L, s.1 < i ∧ i < s.2 ∧ s.1 < j ∧ j < s.2
def Good (l s : ℕ) : Prop := (∀ i j, Same segsX i j → l.testBit i = true → l.testBit j = true → s.testBit i = s.testBit j) ∧
  (∀ i j, Same segsY i j → l.testBit i = true → l.testBit j = true → s.testBit (NN + i) = s.testBit (NN + j))
lemma flag_seg {L : List (ℕ × ℕ)} (hL : L.all segOk = true) {u : ℕ} (hu : ∀ i, u.testBit i = true → AA.testBit i = true)
    {s : ℕ × ℕ} (hs : s ∈ L) (hb : (u + AA).testBit s.2 = true) : ∃ i, s.1 < i ∧ i < s.2 ∧ u.testBit i = true := by
  have h := List.all_eq_true.1 hL s hs
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  refine carry h.1.1.1 h.1.1.2 h.2 ?_ ?_ hb
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.2] at this; simp at this
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.1.2] at this; simp at this
lemma hit_spec {f e : ℕ} (h : hit f e = true) :
    (∃ s ∈ segsX, f.testBit s.2 = true ∧ e.testBit s.2 = true) ∧ (∃ s ∈ segsY, f.testBit s.2 = true ∧ e.testBit s.2 = true) := by
  have aux : ∀ H, Nat.beq (Nat.land (Nat.land f e) H) 0 = false → ∃ i, f.testBit i = true ∧ e.testBit i = true ∧ H.testBit i = true := by
    intro H hH
    have hne : (f &&& e &&& H) ≠ 0 := fun h0 => by rw [nl, nl, h0] at hH; simp at hH
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
    simp at hi; exact ⟨i, hi.1.1, hi.1.2, hi.2⟩
  simp only [hit, bR] at h
  cases h1 : Nat.beq (Nat.land (Nat.land f e) HX) 0 with
  | true => rw [h1] at h; simp only [cond_true, Bool.false_eq_true] at h
  | false =>
    cases h2 : Nat.beq (Nat.land (Nat.land f e) HY) 0 with
    | true => rw [h1, h2] at h; simp only [cond_true, cond_false, Bool.false_eq_true] at h
    | false =>
      obtain ⟨i, a1, a2, a3⟩ := aux _ h1
      obtain ⟨j, b1, b2, b3⟩ := aux _ h2
      rw [HX_eq] at a3; rw [HY_eq] at b3
      obtain ⟨s, hs, rfl⟩ := bitsOf_bit a3
      obtain ⟨s', hs', rfl⟩ := bitsOf_bit b3
      exact ⟨⟨s, hs, a1, a2⟩, ⟨s', hs', b1, b2⟩⟩
lemma hits_false {f : ℕ} {m : List ℕ} (h : ∀ e ∈ m, hit f e = false) : hits f m = false := by
  induction m with
  | nil => rfl
  | cons e m ih =>
    change (Bool.rec (motive := fun _ => Bool) (hits f m) true (hit f e) : Bool) = false
    rw [bR, h e (by simp), ih (fun x hx => h x (by simp [hx]))]; rfl
lemma rect_false {d : Bool} {l o : ℕ} {v : List W} : ∀ {m : List ℕ}, v.Pairwise (fun a b => hit (flag d l o b) (flag d l o a) = false) →
    (∀ w ∈ v, ∀ e ∈ m, hit (flag d l o w) e = false) → rect d l o v m = false := by
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro m hp hm
    change (Bool.rec (motive := fun _ => Bool) (rect d l o v (flag d l o w :: m)) true (hits (flag d l o w) m) : Bool) = false
    rw [List.pairwise_cons] at hp
    rw [bR, hits_false (hm w (by simp)), ih hp.2]; · rfl
    intro w' hw' e he
    simp at he
    rcases he with rfl | he
    · exact hp.1 w' hw'
    · exact hm w' (by simp [hw']) e he
lemma Live.pos {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : 0 < S.card := by
  cases h with
  | stop => simp
  | un => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
  | bi => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
def pk (n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range n, f j * 2 ^ (5 * j)
lemma pk_succ (n : ℕ) (f : ℕ → ℕ) : pk (n + 1) f = 2 ^ (5 * n) * f n + pk n f := by
  rw [pk, Finset.sum_range_succ, ← pk]; ring
lemma pk_lt {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j < 32) : pk n f < 2 ^ (5 * n) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    rw [pk_succ, show 5 * (n + 1) = 5 * n + 5 by ring, pow_add]
    have : 2 ^ (5 * n) * f n ≤ 2 ^ (5 * n) * 31 := Nat.mul_le_mul_left _ (by omega)
    omega
lemma pk_add (n : ℕ) (f g : ℕ → ℕ) : pk n f + pk n g = pk n (fun j => f j + g j) := by
  simp [pk, ← Finset.sum_add_distrib, add_mul]
lemma pk_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) : pk n f = pk n g :=
  Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]
lemma pk_sub {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, g j ≤ f j) : pk n f - pk n g = pk n (fun j => f j - g j) := by
  have : pk n (fun j => f j - g j) + pk n g = pk n f := by
    rw [pk_add]; exact pk_congr fun j hj => Nat.sub_add_cancel (h j hj)
  omega
lemma pk_guard {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, 16 ≤ f j ∧ f j < 32) :
    pk n f &&& pk n (fun _ => 16) = pk n (fun _ => 16) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have ih := ih (fun j hj => h j (by omega))
    have h1 : pk n f < 2 ^ (5 * n) := pk_lt fun j hj => (h j (by omega)).2
    have h2 : pk n (fun _ => 16) < 2 ^ (5 * n) := pk_lt fun _ _ => by omega
    have h3 : f n &&& 16 = 16 := by
      obtain ⟨a, b⟩ := h n (by omega)
      generalize f n = x at *
      interval_cases x <;> rfl
    rw [pk_succ, pk_succ]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2]
    split_ifs with hi
    · rw [← Nat.testBit_and, ih]
    · rw [← Nat.testBit_and, h3]
def isPk (n x : ℕ) : Prop := ∀ i, x.testBit i = true → i % 5 = 0 ∧ i / 5 < n
lemma pk_of {n : ℕ} : ∀ {x : ℕ}, isPk n x → x = pk n (fun j => (x.testBit (5 * j)).toNat) := by
  induction n with
  | zero =>
    intro x h
    simp only [pk, Finset.range_zero, Finset.sum_empty]
    apply Nat.eq_of_testBit_eq; intro i
    by_contra hc
    have := h i (by simpa using hc); omega
  | succ n ih =>
    intro x h
    have hm : isPk n (x % 2 ^ (5 * n)) := by
      intro i hi
      simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hi
      exact ⟨(h i hi.2).1, by omega⟩
    have e := ih hm
    have hd : x / 2 ^ (5 * n) = (x.testBit (5 * n)).toNat := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_div_two_pow]
      cases i with
      | zero => cases hb : x.testBit (5 * n) <;> simp [hb]
      | succ i =>
        have e1 : x.testBit (i + 1 + 5 * n) = false := by
          by_contra hc
          have := h _ (by simpa using hc); omega
        rw [e1]
        cases x.testBit (5 * n) <;> simp [Nat.testBit_succ]
    rw [pk_succ, ← hd]
    have e2 : pk n (fun j => (x.testBit (5 * j)).toNat) = x % 2 ^ (5 * n) := by
      conv_rhs => rw [e]
      refine pk_congr fun j hj => ?_
      rw [Nat.testBit_mod_two_pow]; simp [show 5 * j < 5 * n by omega]
    rw [e2]; exact (Nat.div_add_mod x _).symm
lemma isPk_and {n x y : ℕ} (hx : isPk n x) : isPk n (x &&& y) := fun i hi => hx i (by simp at hi; exact hi.1)
lemma isPk_or {n x y : ℕ} (hx : isPk n x) (hy : isPk n y) : isPk n (x ||| y) := fun i hi => by
  simp at hi; exact hi.elim (hx i) (hy i)
def fl (w : W) (j : ℕ) : ℕ := (w.c.testBit (5 * j)).toNat
lemma fl_le (w : W) (j : ℕ) : fl w j ≤ 1 := by unfold fl; cases w.c.testBit (5 * j) <;> simp
def cnt (v : List W) (j : ℕ) : ℕ := (v.map (fun w => fl w j)).sum
lemma cnt_cons (w : W) (v : List W) (j : ℕ) : cnt (w :: v) j = fl w j + cnt v j := by simp [cnt]
lemma cnt_perm {v v' : List W} (h : v.Perm v') (j : ℕ) : cnt v j = cnt v' j := (h.map _).sum_eq
structure WOk (P : List ℕ) (w : W) : Prop where
  pa : isPk P.length w.a
  pb : isPk P.length w.b
  ec : w.c = w.a ||| w.b
  ca : ∀ j < P.length, w.a.testBit (5 * j) = true → w.s &&& P.getD j 0 = 0
  cb : ∀ j < P.length, w.b.testBit (5 * j) = true → w.s &&& P.getD j 0 = P.getD j 0
lemma WOk.pc {P : List ℕ} {w : W} (h : WOk P w) : isPk P.length w.c := by rw [h.ec]; exact isPk_or h.pa h.pb
lemma WOk.cst {P : List ℕ} {w : W} (h : WOk P w) {j : ℕ} (hj : j < P.length) (hf : w.c.testBit (5 * j) = true) :
    Cst (P.getD j 0) w.s := by
  rw [h.ec, Nat.testBit_or, Bool.or_eq_true] at hf
  exact hf.elim (fun h1 => Or.inl (h.ca j hj h1)) (fun h1 => Or.inr (h.cb j hj h1))
def Cl (P : List ℕ) (T k : ℕ) (b : ℕ → ℕ) (S : Finset ℕ) : Prop := ∀ j < P.length, ∀ q, q + b j < k →
  ¬ Sol Z0 (P.getD j 0) (T &&& P.getD j 0) q (C (P.getD j 0) (Im (P.getD j 0) S))
structure StOk (P : List ℕ) (T l k z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  bud : ∃ b : ℕ → ℕ, (∀ j < P.length, b j ≤ 15) ∧ Cl P T k b S ∧ z = pk P.length (fun j => 16 + b j - cnt v j)
structure Ctx (P : List ℕ) (l m g T : ℕ) : Prop where
  lg : ∀ i, l.testBit i = true → Lg NN m T i ∧ AA.testBit i = true
  hP : ∀ j < P.length, P.getD j 0 &&& m = P.getD j 0 ∧ T &&& P.getD j 0 ≠ 0 ∧ T &&& P.getD j 0 ≠ P.getD j 0
  hg : g = pk P.length (fun _ => 16)
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma cnt_le {k k' t : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ} (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w)
    (hc : Cl P T k b S) (hm : Min R m T k' t S) (hk : k' ≤ k) : ∀ j < P.length, cnt v j ≤ b j := by
  intro j hj
  obtain ⟨p1, p2, p3⟩ := X.hP j hj
  obtain ⟨q, hq, hs⟩ := hm.const p1 p2 p3
  have hqb : ¬ q + b j < k := fun h => hc j hj q h hs
  have : cnt v j ≤ (S.filter (Cst (P.getD j 0))).card := by
    have e : cnt v j = (v.filter (fun w => w.c.testBit (5 * j))).length := by
      clear hr hw
      induction v with
      | nil => rfl
      | cons w v ih =>
        rw [cnt_cons, ih, List.filter_cons, fl]
        cases w.c.testBit (5 * j) <;> simp; omega
    rw [e, ← List.length_map W.s, ← List.toFinset_card_of_nodup (hr.1.sublist (List.filter_sublist.map _))]
    apply Finset.card_le_card
    intro x hx
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hx
    obtain ⟨w, ⟨h1, h2⟩, rfl⟩ := hx
    rw [Finset.mem_filter]
    exact ⟨hr.mem.2 ⟨w, h1, rfl⟩, (hw w h1).cst hj h2⟩
  omega
lemma guard_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hr : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    Nat.beq (Nat.land z g) g = true := by
  obtain ⟨b, hb, hc, hz⟩ := hr.bud
  have hle := cnt_le X hr.rep hr.wok hc hm hk
  rw [nl, hz, X.hg, pk_guard]; · simp
  intro j hj
  have := hb j hj; have := hle j hj; omega
lemma child_sound {f : ℕ → List W → Bool} {z t k k' : ℕ} {r : List W} {S : Finset ℕ}
    {mk : (List W → Bool) → Bool} (hmk : ∀ h, mk h = h r)
    (hr : StOk P T l k z r S) (hm : Min R m T k' t S) (hk : k' ≤ k) (h : child f g mk z = false) : f z r = false := by
  simp only [child, bR, st_eq, guard_ok X hr hm hk, cond_true, hmk] at h
  exact h
end sound
lemma rm_eq (x y : ℕ) (v : List W) : ∀ h, rm x y v h = h (v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y))) := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (rm x y v (fun r => h (w :: r)))
      (rm x y v h) (Nat.beq w.s y)) (rm x y v h) (Nat.beq w.s x) : Bool) = _
    rw [bR, bR, ih, ih, List.filter_cons]
    cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> simp
lemma ins_spec (o : W) (v : List W) (hv : ∀ w ∈ v, w.s ≠ o.s) : ∃ r : List W, r.Perm (o :: v) ∧ ∀ h, ins o v h = h r := by
  induction v with
  | nil => exact ⟨[o], List.Perm.refl _, fun h => rfl⟩
  | cons w v ih =>
    obtain ⟨r, hp, hr⟩ := ih fun w' hw' => hv w' (by simp [hw'])
    have e : ∀ h, ins o (w :: v) h = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then false else h (o :: w :: v)) else ins o v (fun r => h (w :: r)) := by
      intro h
      change (Bool.rec (motive := fun _ => Bool) (ins o v (fun r => h (w :: r)))
        (Bool.rec (motive := fun _ => Bool) (h (o :: w :: v)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s) : Bool) = _
      rw [bR, bR]
    cases hb : Nat.ble w.s o.s with
    | true =>
      refine ⟨o :: w :: v, List.Perm.refl _, fun h => ?_⟩
      have : Nat.beq o.s w.s = false := Bool.eq_false_iff.2 fun h => hv w (by simp) (Nat.eq_of_beq_eq_true h).symm
      rw [e, hb, this]; rfl
    | false =>
      refine ⟨w :: r, (List.Perm.cons w hp).trans (List.Perm.swap _ _ _), fun h => ?_⟩
      rw [e, hb, hr]; rfl
lemma filter_perm {v : List W} (hv : (v.map W.s).Nodup) {a : W} (ha : a ∈ v) :
    (a :: v.filter (fun w => !Nat.beq w.s a.s)).Perm v := by
  induction v with
  | nil => simp at ha
  | cons w v ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hv
    have hne : ∀ x y : ℕ, x ≠ y → Nat.beq x y = false := fun x y h => Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · have : v.filter (fun w => !Nat.beq w.s a.s) = v := by
        rw [List.filter_eq_self]
        intro w' hw'
        rw [hne _ _ (hv.1 w' hw')]; rfl
      rw [List.filter_cons, this]; simp
    · rw [List.filter_cons, hne w.s a.s (fun e => hv.1 a ha e.symm)]
      simp only [Bool.not_false, if_true]
      exact (List.Perm.swap _ _ _).trans ((ih hv.2 ha).cons w)
lemma filter2 {v : List W} {x y : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y)) =
    (v.filter (fun w => !Nat.beq w.s x)).filter (fun w => !Nat.beq w.s y) := by
  rw [List.filter_filter]; congr 1; funext w; cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> rfl
lemma filter1 {v : List W} {x : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s x)) = v.filter (fun w => !Nat.beq w.s x) := by
  congr 1; funext w; cases Nat.beq w.s x <;> rfl
inductive Shape (o a c : W) (v : List W) : Bool → Bool → List W → Prop
  | ff {r} : (a :: c :: r).Perm (o :: v) → Shape o a c v false false r
  | tf {r} : (c :: r).Perm (o :: v) → Shape o a c v true false r
  | ft {r} : (a :: r).Perm (o :: v) → Shape o a c v false true r
  | tt {r} : r.Perm (o :: v) → Shape o a c v true true r
lemma Shape.cnt {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) (j : ℕ) :
    cnt r j + (bif ka then 0 else fl a j) + (bif kc then 0 else fl c j) = fl o j + cnt v j := by
  cases h with
  | ff h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tf h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | ft h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tt h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
lemma Shape.mem {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {w : W} (hw : w ∈ r) : w = o ∨ w ∈ v := by
  have : w ∈ o :: v := by
    cases h with
    | ff h => exact h.subset (by simp [hw])
    | tf h => exact h.subset (by simp [hw])
    | ft h => exact h.subset (by simp [hw])
    | tt h => exact h.subset (by simp [hw])
  simpa using this
lemma Shape.len {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) :
    r.length + (bif ka then 0 else 1) + (bif kc then 0 else 1) = v.length + 1 := by
  cases h with
  | ff h => have := h.length_eq; simp at this ⊢; omega
  | tf h => have := h.length_eq; simp at this ⊢; omega
  | ft h => have := h.length_eq; simp at this ⊢; omega
  | tt h => have := h.length_eq; simp at this ⊢; omega
lemma Shape.rep {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {S S' : Finset ℕ} (hr : Rep v S)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) (ho : o.s ∉ S)
    (hS : ∀ x, x ∈ S' ↔ x = o.s ∨ (x ∈ S ∧ (x = a.s → ka = true) ∧ (x = c.s → kc = true))) : Rep r S' := by
  have hov : ((o :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ho ?_, hr.1⟩
    rw [← hr.2]; simpa using hm
  have hvS : ∀ x, x ∈ v.map W.s ↔ x ∈ S := fun x => by rw [← hr.2]; simp
  have hm : ∀ x, x ∈ (o :: v).map W.s ↔ x = o.s ∨ x ∈ S := fun x => by simp only [List.map_cons, List.mem_cons, hvS]
  have haS := (hvS a.s).1 (List.mem_map_of_mem ha)
  have hcS := (hvS c.s).1 (List.mem_map_of_mem hc)
  have hao : a.s ≠ o.s := fun e => ho (e ▸ haS)
  have hco : c.s ≠ o.s := fun e => ho (e ▸ hcS)
  cases h with
  | ff h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hn
    refine ⟨hn.2.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n1 : x ≠ a.s := fun e => hn.1.2 (e ▸ h1)
      have n2 : x ≠ c.s := fun e => hn.2.1 (e ▸ h1)
      rcases hx.1 (Or.inr (Or.inr h1)) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n1, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · rcases hx.2 (Or.inl e) with e' | e' | e'
        · exact absurd (e'.symm.trans e) hao
        · exact absurd (e'.symm.trans e) hco
        · exact e'
      · rcases hx.2 (Or.inr e) with e' | e' | e'
        · exact absurd (f1 e') (by simp)
        · exact absurd (f2 e') (by simp)
        · exact e'
  | tf h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ c.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun _ => rfl, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hco (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f2 e'
  | ft h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ a.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n2, fun _ => rfl⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hao (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  | tt h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    refine ⟨hn, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx
    rw [List.mem_toFinset, hS, hx]; simp
lemma shape_all {o a c : W} {v r : List W} (ho : ∀ w ∈ v, w.s ≠ o.s) (hp : r.Perm (o :: v)) (hv : (v.map W.s).Nodup)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) :
    Shape o a c v false false (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s c.s))) ∧
    Shape o a c v true false (r.filter (fun w => !(Nat.beq w.s c.s || Nat.beq w.s c.s))) ∧
    Shape o a c v false true (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))) ∧ Shape o a c v true true r := by
  have hnd : (r.map W.s).Nodup := by
    refine (hp.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => ho w hw, hv⟩
  have har : a ∈ r := hp.symm.subset (by simp [ha])
  have hcr : c ∈ r := hp.symm.subset (by simp [hc])
  refine ⟨.ff ?_, .tf ?_, .ft ?_, .tt hp⟩
  · rw [filter2]
    have h1 := filter_perm hnd har
    have h2 : c ∈ r.filter (fun w => !Nat.beq w.s a.s) := by
      rw [List.mem_filter]; refine ⟨hcr, ?_⟩
      rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
    exact ((filter_perm (hnd.sublist (List.filter_sublist.map _)) h2).cons a).trans (h1.trans hp)
  · rw [filter1]; exact (filter_perm hnd hcr).trans hp
  · rw [filter1]; exact (filter_perm hnd har).trans hp
lemma cnt_two {v : List W} {a c : W} (ha : a ∈ v) (hc : c ∈ v) (hv : (v.map W.s).Nodup) (hac : a.s ≠ c.s) (j : ℕ) :
    fl a j + fl c j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  have h2 : c ∈ v.filter (fun w => !Nat.beq w.s a.s) := by
    rw [List.mem_filter]; refine ⟨hc, ?_⟩
    rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
  have h3 := cnt_perm (filter_perm (hv.sublist (List.filter_sublist.map _)) h2) j
  simp only [cnt_cons] at h1 h3; omega
lemma cnt_one {v : List W} {a : W} (ha : a ∈ v) (hv : (v.map W.s).Nodup) (j : ℕ) : fl a j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  simp only [cnt_cons] at h1; omega
def opW (d : Bool) (a c : W) : W := bif d then ⟨a.s ||| c.s, a.a &&& c.a, a.b ||| c.b, (a.a &&& c.a) ||| (a.b ||| c.b), 0⟩
  else ⟨a.s &&& c.s, a.a ||| c.a, a.b &&& c.b, (a.a ||| c.a) ||| (a.b &&& c.b), 0⟩
lemma opW_s (d : Bool) (a c : W) : (opW d a c).s = op d a.s c.s := by cases d <;> rfl
lemma opW_ok {P : List ℕ} {a c : W} (d : Bool) (ha : WOk P a) (hc : WOk P c) : WOk P (opW d a c) := by
  cases d
  · refine ⟨isPk_or ha.pa hc.pa, isPk_and ha.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a ||| c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.ca j hj h]; simp [op]
      · rw [hc.ca j hj h]; simp [op]
    · have h : (a.b &&& c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.cb j hj h.1, hc.cb j hj h.2, op_self]
  · refine ⟨isPk_and ha.pa, isPk_or ha.pb hc.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a &&& c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.ca j hj h.1, hc.ca j hj h.2, op_self]
    · have h : (a.b ||| c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
      · rw [hc.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_good {l x y : ℕ} (d : Bool) (hx : Good l x) (hy : Good l y) : Good l (op d x y) := by
  refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
  · rw [op_bit, op_bit, hx.1 i j h h1 h2, hy.1 i j h h1 h2]
  · rw [op_bit, op_bit, hx.2 i j h h1 h2, hy.2 i j h h1 h2]
lemma fl_and {P : List ℕ} {a c : W} (ha : WOk P a) : a.c &&& c.c = pk P.length (fun j => fl a j * fl c j) := by
  rw [pk_of (isPk_and (y := c.c) ha.pc)]
  refine pk_congr fun j _ => ?_
  rw [Nat.testBit_and]; unfold fl; cases a.c.testBit (5 * j) <;> cases c.c.testBit (5 * j) <;> rfl
lemma fl_pk {P : List ℕ} {a : W} (ha : WOk P a) : a.c = pk P.length (fl a) := pk_of ha.pc
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma bi_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {ka kc : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hb : Bi R d' a.s c.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v) (hka : ka = decide (a.s ∈ S')) (hkc : kc = decide (c.s ∈ S'))
    (hsh : Shape (opW d' a c) a c v ka kc r) :
    StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
    Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hab : a.s ≠ c.s := hb.1
  have hfr := hb.fresh hl hm.2
  have hfS : (opW d' a c).s ∉ S := by rw [opW_s]; exact fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha; have wc := hs.wok c hc
  have wo := opW_ok d' wa wc
  have hrep : Rep r S' := by
    refine hsh.rep hs.rep ha hc hab hfS fun x => ?_
    obtain ⟨_, U, e1, e2, _⟩ := hb
    rw [opW_s] at hfS ⊢
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_, ?_⟩
        · rintro rfl; rw [hka, e2]; simp [h]
        · rintro rfl; rw [hkc, e2]; simp [h]
    · rintro (h | ⟨h, f1, f2⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · have := f2 h; rw [hkc, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hsh.mem hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hsh.mem hw with rfl | h
    · rw [opW_s]; exact op_good _ (hs.good a ha) (hs.good c hc)
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - max (fl a j) (fl c j)
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_two ha hc hs.rep.1 hab j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true ∨ c.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (hkill.imp (wa.cst hj) (wc.cst hj)) hsol)
      have : 1 ≤ max (fl a j) (fl c j) := by
        rcases hkill with h | h <;> simp [fl, h]
      have := fl_le a j; have := fl_le c j; omega
    · push Not at hkill
      refine hcl j hj (q + 1) ?_ (hb.im hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill.1]
      have e2 : fl c j = 0 := by simp [fl, hkill.2]
      rw [e1, e2] at hq; simp at hq; omega
  have hmin := hb.min hl hm.2
  have hle' := cnt_le X hrep hwok hcl' hmin hk
  have num : ∀ j < P.length, 1 ≤ 16 + b j - cnt v j + fl a j * fl c j ∧ fl (opW d' a c) j ≤ 1 ∧
      16 ≤ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j ∧ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j < 32 ∧
      16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j - (bif ka then fl a j else 0) - (bif kc then fl c j else 0) = 16 + b' j - cnt r j := by
    intro j hj
    have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_two ha hc hs.rep.1 hab j; have q4 := hb15 j hj
    have q5 := hsh.cnt j; have q6 := fl_le a j; have q7 := fl_le c j; have q8 := fl_le (opW d' a c) j
    simp only [b'] at q2 ⊢
    generalize fl a j = fa at *; generalize fl c j = fc at *; generalize fl (opW d' a c) j = fo at *
    interval_cases fa <;> interval_cases fc <;> cases ka <;> cases kc <;> simp at q2 q3 q5 ⊢ <;> omega
  have e1 : z + (a.c &&& c.c) - (opW d' a c).c = pk P.length (fun j => 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j) := by
    rw [hz, fl_and wa, fl_pk wo, pk_add, pk_sub]
    intro j hj; have := num j hj; omega
  refine ⟨⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩, ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · rw [e1]
    have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have ec : (bif kc then c.c else 0) = pk P.length (fun j => bif kc then fl c j else 0) := by
      cases kc
      · simp [pk]
      · exact fl_pk wc
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    have le2 : ∀ j, (bif kc then fl c j else 0) ≤ 1 := fun j => by cases kc <;> simp [fl_le]
    rw [ea, ec, pk_sub, pk_sub]
    · exact pk_congr fun j hj => (num j hj).2.2.2.2
    · intro j hj; have := num j hj; have := le1 j; have := le2 j; omega
    · intro j hj; have := num j hj; have := le1 j; omega
  · rw [e1, nl, X.hg, pk_guard]; · simp
    intro j hj; have := num j hj; omega
lemma drop_ok {k' t : ℕ} {v : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {i : ℕ} (hr : Rep v S)
    (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S')
    (ha : a ∈ v) (hk : a.s ∉ S')
    (hu : (Nat.land (sp (pos' t) l a.s) (wst (pos' t) l v)).testBit i = true) :
    bif d' then c.s.testBit (NN + i) = false else c.s.testBit i = true := by
  obtain ⟨hli, u1, u2⟩ := uq_of hr ha hu
  obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
  obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
  have hac : c.s ≠ a.s := hb.1.symm
  have hsub := hb.sub.2.2 hw
  rw [Finset.mem_insert] at hsub
  have hg : sepb NN (pos' t) (op d' a.s c.s) i = true := by
    rcases hsub with rfl | h
    · exact hs
    · have := u2 w h (fun e => hk (e ▸ hw))
      rw [this] at hs; simp at hs
  have hcn := u2 c.s hb.sub.2.1 hac
  revert hg hcn u1
  unfold sepb; simp only [op_bit]
  cases pos' t <;> cases d' <;> cases a.s.testBit i <;> cases a.s.testBit (NN + i) <;> cases c.s.testBit i <;>
    cases c.s.testBit (NN + i) <;> simp
end sound
def mkx (d : Bool) (l o : ℕ) (w : W) : X := ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩
lemma mkX_eq (d : Bool) (l o : ℕ) (v : List W) : mkX d l o v = v.map (mkx d l o) := by
  induction v with
  | nil => rfl
  | cons w v ih => change _ :: mkX d l o v = _; rw [ih]; rfl
def modeF (n e : ℕ) : (W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ n) e then f2 else f1) else f0
lemma node_eq (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ) (v : List W) (go : (X → X → Bool) → List X → Bool) :
    node f d l m g e n z v go = go (pair (modeF n e (mid f m g e (Nat.pred n) z v))) (v.map (mkx d l (wst d l v))) := by
  rw [← mkX_eq]; unfold node modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl
lemma modeF_false {n e : ℕ} {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {a c : W} {da dc : ℕ} {s x y : ℕ}
    (hf : modeF n e h a c da dc s x y = false) (h0 : ¬ n ≤ e → da = 0 ∧ dc = 0) (h1 : ¬ n + 1 ≤ e → da = 0 ∨ dc = 0) :
    h a c da dc s x y = false := by
  unfold modeF at hf
  cases b1 : Nat.ble n e with
  | false =>
    have := h0 (fun h => by rw [Nat.ble_eq_true_of_le h] at b1; simp at b1)
    rw [b1, this.1, this.2] at hf; rw [this.1, this.2]; exact hf
  | true =>
    cases b2 : Nat.ble (Nat.succ n) e with
    | false =>
      have := h1 (fun h => by rw [Nat.ble_eq_true_of_le h] at b2; simp at b2)
      have h3 : Nat.beq (Nat.mul da dc) 0 = true := by
        change Nat.beq (da * dc) 0 = true
        rcases this with h | h <;> simp [h]
      rw [b1, b2] at hf
      simp only [Bool.cond_true, Bool.cond_false, f1, h3] at hf
      exact hf
    | true => rw [b1, b2] at hf; exact hf
def dfc (d d' : Bool) (l o : ℕ) (a c : W) : ℕ := bif d' then Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s NN)
  else Nat.xor (Nat.land (Nat.land (sp d l a.s) o) c.s) (Nat.land (sp d l a.s) o)
lemma pair_false {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {d : Bool} {l o : ℕ} {a c : W}
    (hp : pair h (mkx d l o a) (mkx d l o c) = false) (d' : Bool) :
    h a c (dfc d d' l o a c) (dfc d d' l o c a) (opW d' a c).s (opW d' a c).a (opW d' a c).b = false := by
  simp only [pair, mkx, bR] at hp
  rw [Bool.cond_eq_ite] at hp
  split_ifs at hp with h1
  · cases d'
    · rw [Bool.not_eq_true] at h1; exact h1
    · exact hp
lemma put_eq {m : ℕ} {o : W} {v : List W} (ho : Nat.lor o.a o.b = o.c) (hr : o.r = 0) (h0 : o.s ≠ 0) (h1 : o.s ≠ m) (h : List W → Bool) :
    put m o.s o.a o.b v h = ins o v h := by
  have hb0 : Nat.beq o.s 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
  have hb1 : Nat.beq o.s m = false := Bool.eq_false_iff.2 fun h => h1 (Nat.eq_of_beq_eq_true h)
  simp only [put, st_eq, hb0, hb1, ho]
  rw [← hr]
lemma mid_false {f : ℕ → List W → Bool} {m g e n z : ℕ} {v : List W} {a c : W} {da dc : ℕ} {d' : Bool}
    (h : mid f m g e n z v a c da dc (opW d' a c).s (opW d' a c).a (opW d' a c).b = false)
    (hg : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true) :
    kids (child f g) e n (z + (a.c &&& c.c) - (opW d' a c).c) a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0)
      (put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v) = false := by
  have ec : Nat.lor (opW d' a c).a (opW d' a c).b = (opW d' a c).c := by cases d' <;> rfl
  simp only [mid, st_eq, ec] at h
  have hg' : Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (opW d' a c).c) g) g = true := hg
  rw [hg'] at h
  exact h
lemma kids_false {ch : ((List W → Bool) → Bool) → ℕ → Bool} {e n z x y a c : ℕ} {oa oc : Bool} {mk : (List W → Bool) → Bool}
    (h : kids ch e n z x y a c oa oc mk = false) :
    (oa = true → oc = true → ch (fun h => mk (fun r => rm a c r h)) z = false) ∧
    (oc = true → n + 1 ≤ e → ch (fun h => mk (fun r => rm c c r h)) (z - x) = false) ∧
    (oa = true → n + 1 ≤ e → ch (fun h => mk (fun r => rm a a r h)) (z - y) = false) ∧
    (n + 2 ≤ e → ch mk (z - x - y) = false) := by
  simp only [kids, bR] at h
  have b1 : n + 1 ≤ e → Nat.ble (Nat.succ n) e = true := fun h => Nat.ble_eq_true_of_le h
  have b2 : n + 2 ≤ e → Nat.ble (Nat.succ (Nat.succ n)) e = true := fun h => Nat.ble_eq_true_of_le h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2; subst h1 h2
    revert h; simp only [Bool.cond_true]; cases ch (fun h => mk (fun r => rm a c r h)) z <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) = false
    cases ch (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) = false
    cases ch (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) <;> simp
  · intro h2; rw [b2 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch mk (Nat.sub (Nat.sub z x) y) = false
    cases ch mk (Nat.sub (Nat.sub z x) y) <;> simp
lemma Live.rel {R' : ℕ → ℕ} {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Live R' m T k t S := by
  induction h with
  | stop => exact .stop
  | un _ ih => exact .un ih
  | bi hab hal _ ih => exact .bi hab (hR _ _ _ hal) ih
lemma Bi.rel {R' : ℕ → ℕ} {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hR : ∀ d a b, Al R d a b → Al R' d a b) : Bi R' d a b S S' := by
  obtain ⟨hab, U, e1, e2, hal⟩ := h; exact ⟨hab, U, e1, e2, hR _ _ _ hal⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma rect_ok {t k k' z : ℕ} {r : List W} {S : Finset ℕ} (hr : StOk P T l k z r S) (hm : Min R m T k' t S) (hk : k' ≤ k)
    (hn : r.length + t = k + 1) : rect (pos' t) l (wst (pos' t) l r) r [] = false := by
  cases hrect : rect (pos' t) l (wst (pos' t) l r) r [] with
  | false => rfl
  | true =>
      exfalso
      have hs := hm.size
      have hcard := hr.rep.card
      have hpos : 0 < S.card := hm.1.pos
      have htight : S.card + t = k' + 1 := by omega
      rw [rect_false (o := wst (pos' t) l r)] at hrect; · simp at hrect
      · have hnd : r.Pairwise (fun a b => a.s ≠ b.s) := List.pairwise_map.1 hr.rep.1
        refine hnd.imp_of_mem fun {a b} ha hb' hab => ?_
        by_contra hhit
        rw [Bool.not_eq_false] at hhit
        obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec hhit
        have hu : ∀ w, ∀ i, (Nat.land (sp (pos' t) l w) (wst (pos' t) l r)).testBit i = true → AA.testBit i = true := by
          intro w i hi
          simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
          exact (X.lg i hi.1.1).2
        obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x1
        obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x2
        obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.s) hs2 y1
        obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.s) hs2 y2
        obtain ⟨l1, u1⟩ := uq_of hr.rep ha a3
        obtain ⟨l2, u2⟩ := uq_of hr.rep hb' b3
        obtain ⟨l3, u3⟩ := uq_of hr.rep ha c3
        obtain ⟨l4, u4⟩ := uq_of hr.rep hb' d3
        have g1 : ∀ w ∈ S, w.testBit i1 = w.testBit i2 := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
        have g2 : ∀ w ∈ S, w.testBit (NN + j1) = w.testBit (NN + j2) := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
        have ma := hr.rep.mem.2 ⟨a, ha, rfl⟩
        have mb := hr.rep.mem.2 ⟨b, hb', rfl⟩
        rcases Nat.eq_zero_or_pos t with rfl | htp
        · have hd' : pos' 0 = false := by simp [pos']
          rw [hd'] at u1 u2 u3 u4
          exact rect0 hm.1 hm.2 (by simpa using htight) (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
        · have hd' : pos' t = true := by simp [pos', htp]
          rw [hd'] at u1 u2 u3 u4
          exact rect1 hm.1 hm.2 htight (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
      · simp
lemma hit_ht {k z : ℕ} {r : List W} {S : Finset ℕ} {d : Bool} (hr : StOk P T l k z r S) {a b : W} (ha : a ∈ r) (hb : b ∈ r)
    (h : hit (flag false l (wst d l r) a) (flag false l (wst d l r) b) = true) : Ht NN m T d S a.s b.s := by
  obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec h
  have hu : ∀ w, ∀ i, (Nat.land (sp false l w) (wst d l r)).testBit i = true → AA.testBit i = true := by
    intro w i hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
    exact (X.lg i hi.1.1).2
  have uq : ∀ {w : W} {i : ℕ}, w ∈ r → (Nat.land (sp false l w.s) (wst d l r)).testBit i = true →
      l.testBit i = true ∧ Uq NN d S w.s i ∧ w.s.testBit i = true := by
    intro w i hw hi
    have hi2 := hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi2
    obtain ⟨⟨hl, hs⟩, ho⟩ := hi2
    have hsd : sepb NN d w.s i = true := by
      cases d
      · exact hs
      · exact sepb_weak _ hs
    obtain ⟨q1, q2⟩ := uq_of hr.rep hw (d := d) (l := l) (i := i) (by
      simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true]; exact ⟨⟨hl, hsd⟩, ho⟩)
    refine ⟨q1, q2, ?_⟩
    revert hs; simp only [sepb, cond_false]; cases w.s.testBit i <;> simp
  obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x1
  obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x2
  obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.s) hs2 y1
  obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.s) hs2 y2
  obtain ⟨l1, u1, p1⟩ := uq ha a3
  obtain ⟨l2, u2, p2⟩ := uq hb b3
  obtain ⟨l3, u3, p3⟩ := uq ha c3
  obtain ⟨l4, u4, p4⟩ := uq hb d3
  refine ⟨i1, i2, j1, j2, (X.lg _ l1).1, (X.lg _ l2).1, (X.lg _ l3).1, (X.lg _ l4).1, ?_, ?_, u1, u2, u3, u4, by rw [p1, p3], by rw [p2, p4]⟩
  · intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
    exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
  · intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
    exact (hr.good w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
end sound
lemma hits_true {f : ℕ} {m : List ℕ} (h : hits f m = true) : ∃ e ∈ m, hit f e = true := by
  by_contra hc
  push Not at hc
  rw [hits_false fun e he => by simpa using hc e he] at h; simp at h
lemma app_mem {x y : List ℕ} {e : ℕ} : e ∈ app x y ↔ e ∈ x ∨ e ∈ y := by
  induction x with
  | nil => simp [app]
  | cons a x ih =>
    change e ∈ a :: app x y ↔ _
    simp only [List.mem_cons, ih, or_assoc]
def CmOk (F : W → ℕ) (r : List W) (col : ℕ → ℕ) (c : Cm) : Prop := ∃ κ ≤ 1, (∀ e ∈ c.a, ∃ w ∈ r, F w = e ∧ col w.s = κ) ∧
  ∀ e ∈ c.b, ∃ w ∈ r, F w = e ∧ col w.s = 1 - κ
lemma join_false {F : W → ℕ} {r : List W} {col : ℕ → ℕ} {k : List Cm → Bool} {w : W} (hw1 : col w.s ≤ 1)
    (hh : ∀ w' ∈ r, hit (F w) (F w') = true → col w.s ≠ col w'.s)
    (hk : ∀ cs, (∀ c ∈ cs, CmOk F (w :: r) col c) → k cs = false) : ∀ (cs : List Cm) (S O : List ℕ) (Q : List Cm),
    (∀ c ∈ cs, CmOk F r col c) → (∀ c ∈ Q, CmOk F (w :: r) col c) → (∀ e ∈ S, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = col w.s) →
    (∀ e ∈ O, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = 1 - col w.s) → join k (F w) cs S O Q = false := by
  intro cs
  induction cs with
  | nil =>
    intro S O Q _ hQ hS hO
    refine hk _ fun c hc => ?_
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨col w.s, hw1, hS, hO⟩
    · exact hQ c hc
  | cons c cs ih =>
    intro S O Q hcs hQ hS hO
    have hc := hcs c (by simp)
    have hcs' : ∀ c ∈ cs, CmOk F r col c := fun c' h => hcs c' (by simp [h])
    obtain ⟨κ, hκ, ha, hb⟩ := hc
    have e : join k (F w) (c :: cs) S O Q = bif hits (F w) c.a then (bif hits (F w) c.b then true else join k (F w) cs (app c.b S) (app c.a O) Q)
        else (bif hits (F w) c.b then join k (F w) cs (app c.a S) (app c.b O) Q else join k (F w) cs S O (c :: Q)) := by
      change (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) (join k (F w) cs S O (c :: Q)) (join k (F w) cs (app c.a S) (app c.b O) Q) (hits (F w) c.b))
        (Bool.rec (motive := fun _ => Bool) (join k (F w) cs (app c.b S) (app c.a O) Q) true (hits (F w) c.b)) (hits (F w) c.a) : Bool) = _
      rw [bR, bR, bR]
    rw [e]
    have hA : hits (F w) c.a = true → κ = 1 - col w.s := by
      intro h
      obtain ⟨x, hx, hhx⟩ := hits_true h
      obtain ⟨w', hw', e1, e2⟩ := ha x hx
      have := hh w' hw' (by rw [e1]; exact hhx)
      omega
    have hB : hits (F w) c.b = true → κ = col w.s := by
      intro h
      obtain ⟨x, hx, hhx⟩ := hits_true h
      obtain ⟨w', hw', e1, e2⟩ := hb x hx
      have := hh w' hw' (by rw [e1]; exact hhx)
      omega
    have up : ∀ {κ' : ℕ} {L : List ℕ}, (∀ e ∈ L, ∃ w' ∈ r, F w' = e ∧ col w'.s = κ') → ∀ e ∈ L, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = κ' := by
      intro κ' L h e he
      obtain ⟨w', h1, h2⟩ := h e he
      exact ⟨w', by simp [h1], h2⟩
    cases h1 : hits (F w) c.a with
    | true =>
      have k1 := hA h1
      cases h2 : hits (F w) c.b with
      | true => have k2 := hB h2; omega
      | false =>
        simp only [cond_true, cond_false]
        refine ih _ _ _ hcs' hQ ?_ ?_
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up hb e h; exact ⟨w', q1, q2, by omega⟩
          · exact hS e h
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up ha e h; exact ⟨w', q1, q2, by omega⟩
          · exact hO e h
    | false =>
      cases h2 : hits (F w) c.b with
      | true =>
        have k2 := hB h2
        simp only [cond_true, cond_false]
        refine ih _ _ _ hcs' hQ ?_ ?_
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up ha e h; exact ⟨w', q1, q2, by omega⟩
          · exact hS e h
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up hb e h; exact ⟨w', q1, q2, by omega⟩
          · exact hO e h
      | false =>
        simp only [cond_false]
        refine ih _ _ _ hcs' ?_ hS hO
        intro c' hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact ⟨κ, hκ, up ha, up hb⟩
        · exact hQ c' hc'
lemma bip_aux {l o : ℕ} {col : ℕ → ℕ} : ∀ (v r : List W) (cs : List Cm), (∀ w ∈ v, col w.s ≤ 1) → (∀ c ∈ cs, CmOk (flag false l o) r col c) →
    (∀ w ∈ v, ∀ w' ∈ r, hit (flag false l o w) (flag false l o w') = true → col w.s ≠ col w'.s) →
    v.Pairwise (fun a b => hit (flag false l o b) (flag false l o a) = true → col b.s ≠ col a.s) → bip l o v cs = false := by
  intro v
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro r cs h1 h2 h3 h4
    rw [List.pairwise_cons] at h4
    change join (bip l o v) (flag false l o w) cs [flag false l o w] [] [] = false
    refine join_false (F := flag false l o) (h1 w (by simp)) (h3 w (by simp)) ?_ cs _ _ _ h2 (by simp) ?_ (by simp)
    · intro cs' hcs'
      refine ih (w :: r) cs' (fun x hx => h1 x (by simp [hx])) hcs' ?_ h4.2
      intro x hx w' hw'
      simp only [List.mem_cons] at hw'
      rcases hw' with rfl | hw'
      · exact h4.1 x hx
      · exact h3 x (by simp [hx]) w' hw'
    · intro e he
      simp only [List.mem_singleton] at he
      exact ⟨w, by simp, he.symm, rfl⟩
lemma anyE_false : ∀ {m : List ℕ}, m.Pairwise (fun p q => hit p q = false) → anyE m = false := by
  intro m
  induction m with
  | nil => intro _; rfl
  | cons f t ih =>
    intro h
    rw [List.pairwise_cons] at h
    change (Bool.rec (motive := fun _ => Bool) (anyE t) true (hits f t) : Bool) = false
    rw [bR, hits_false h.1, ih h.2]; rfl
lemma rmF_eq (F : W → ℕ) (f : ℕ) (t : List W) : rmF f (t.map F) = (t.eraseP (fun q => hit f (F q))).map F := by
  induction t with
  | nil => rfl
  | cons x t ih =>
    change (Bool.rec (motive := fun _ => List ℕ) (F x :: rmF f (t.map F)) (t.map F) (hit f (F x)) : List ℕ) = _
    rw [List.eraseP_cons]
    cases h : hit f (F x)
    · simp [ih]
    · simp
lemma eraseP_not {α : Type} {p : α → Bool} {a : α} : ∀ {t : List α}, t.Nodup → a ∈ t → p a = true → (∀ x ∈ t, p x = true → x = a) → a ∉ t.eraseP p := by
  intro t
  induction t with
  | nil => intro _ h; simp at h
  | cons x t ih =>
    intro hn ha hp hx
    rw [List.nodup_cons] at hn
    rw [List.eraseP_cons]
    cases h : p x
    · have hax : a ≠ x := fun e => by rw [← e, hp] at h; simp at h
      simp only [Bool.false_eq_true, if_false, List.mem_cons, not_or]
      simp only [List.mem_cons] at ha
      exact ⟨hax, ih hn.2 (ha.resolve_left hax) hp fun y hy => hx y (by simp [hy])⟩
    · have := hx x (by simp) h
      subst this
      simpa using hn.1
lemma star_false {F : W → ℕ} {a : W} : ∀ {v : List W}, v.Nodup → star (v.map F) = false →
    ∃ p q : W, [p, q].Sublist v ∧ hit (F p) (F q) = true ∧ p ≠ a ∧ q ≠ a := by
  intro v hn hst
  by_contra hno
  push Not at hno
  have bad : ∀ p q : W, [p, q].Sublist v → hit (F p) (F q) = true → p = a ∨ q = a := by
    intro p q h1 h2
    by_cases h : p = a
    · exact Or.inl h
    · exact Or.inr (hno p q h1 h2 h)
  clear hno
  have key : star (v.map F) = true := by
    clear hst
    induction v with
    | nil => rfl
    | cons w t ih =>
      rw [List.nodup_cons] at hn
      have bt : ∀ p q : W, [p, q].Sublist t → hit (F p) (F q) = true → p = a ∨ q = a := fun p q h => bad p q (h.cons w)
      have e : star ((w :: t).map F) = bif hits (F w) (t.map F) then (bif anyE (t.map F) then (bif hits (F w) (rmF (F w) (t.map F)) then false else
          (bif anyE (rmF (F w) (t.map F)) then false else true)) else true) else star (t.map F) := by
        change (Bool.rec (motive := fun _ => Bool) (star (t.map F)) (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool) true false (anyE (rmF (F w) (t.map F)))) false (hits (F w) (rmF (F w) (t.map F)))) (anyE (t.map F))) (hits (F w) (t.map F)) : Bool) = _
        rw [bR, bR, bR, bR]
      rw [e]
      have edge : ∀ u : List W, u.Sublist t → a ∉ u → anyE (u.map F) = false := by
        intro u hu ha
        refine anyE_false ?_
        rw [List.pairwise_map, List.pairwise_iff_forall_sublist]
        intro p q hpq
        by_contra hc
        rw [Bool.not_eq_false] at hc
        have hm : ∀ x ∈ [p, q], x ∈ u := fun x hx => hpq.subset hx
        rcases bt p q (hpq.trans hu) hc with rfl | rfl
        · exact ha (hm p (by simp))
        · exact ha (hm q (by simp))
      cases h1 : hits (F w) (t.map F) with
      | false => rw [cond_false]; exact ih hn.2 bt
      | true =>
        rw [cond_true]
        have part : ∀ q ∈ t, hit (F w) (F q) = true → w = a ∨ q = a := fun q hq h => bad w q ((List.singleton_sublist.2 hq).cons_cons w) h
        by_cases hwa : w = a
        · subst hwa
          rw [edge t (List.Sublist.refl t) hn.1]; rfl
        · have pa : ∀ q ∈ t, hit (F w) (F q) = true → q = a := fun q hq h => (part q hq h).resolve_left hwa
          obtain ⟨x, hx, hhx⟩ := hits_true h1
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
          have hqa := pa q hq hhx
          subst hqa
          have hna : q ∉ t.eraseP (fun q => hit (F w) (F q)) := eraseP_not hn.2 hq hhx pa
          rw [rmF_eq, edge _ List.eraseP_sublist hna]
          have : hits (F w) ((t.eraseP (fun q => hit (F w) (F q))).map F) = false := by
            refine hits_false fun e he => ?_
            obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he
            by_contra hc
            rw [Bool.not_eq_false] at hc
            have hyt : y ∈ t := List.eraseP_sublist.subset hy
            exact hna (pa y hyt hc ▸ hy)
          rw [this]
          cases anyE (t.map F) <;> rfl
  rw [key] at hst; simp at hst
lemma flk_eq (l o : ℕ) (v : List W) : ∀ k, flk l o v k = k (v.map (flag false l o)) := by
  induction v with
  | nil => intro k; rfl
  | cons w v ih =>
    intro k
    change flk l o v (fun r => k (flag false l o w :: r)) = _
    rw [ih]; rfl
def NK (R : ℕ → ℕ) (m T k' t : ℕ) (S : Finset ℕ) : Prop :=
  (∀ d a b S1 k0, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → S1.card < S.card) ∧
  ∀ a S1 k0 t0, k' = k0 + 1 → t = t0 + 1 → Un m a S S1 → Live R m T k0 t0 S1 → S1.card ≤ S.card
lemma Rep.nodup {v : List W} {S : Finset ℕ} (h : Rep v S) : v.Nodup := List.Nodup.of_map _ h.1
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nk_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S)
    (hx : k' ≤ S.card + t) (hst : flk l (wst (pos' t) l v) v star = false) : NK R m T k' t S := by
  rw [flk_eq] at hst
  have hsz := hm.size
  have av : ∀ a : ℕ, a ∈ S → ∃ p q : ℕ, p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ p ≠ a ∧ q ≠ a ∧ Ht NN m T (pos' t) S p q := by
    intro a ha
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 ha
    obtain ⟨p, q, hpq, hh, h1, h2⟩ := star_false (F := flag false l (wst (pos' t) l v)) (a := wa) hs.rep.nodup hst
    have hp : p ∈ v := hpq.subset (by simp)
    have hq : q ∈ v := hpq.subset (by simp)
    have hne : p ≠ q := by
      have := hs.rep.nodup.sublist hpq
      simpa using this
    refine ⟨p.s, q.s, hs.rep.mem.2 ⟨p, hp, rfl⟩, hs.rep.mem.2 ⟨q, hq, rfl⟩, fun e => hne (hs.rep.inj hp hq e), fun e => h1 (hs.rep.inj hp hwa e),
      fun e => h2 (hs.rep.inj hq hwa e), hit_ht X hs hp hq hh⟩
  have he : ∀ t', pos' t = true ∨ t = t' → pos' t = true ∨ t' = 0 := by
    intro t' h
    rcases h with h | h
    · exact Or.inl h
    · subst h
      rcases Nat.eq_zero_or_pos t with h | h
      · exact Or.inr h
      · exact Or.inl (by simp [pos', h])
  have kb : ∀ d a b S1 k0, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → ∀ U, S = insert a (insert b U) → S1 = insert (op d a b) U → a ∈ U → b ∉ U → False := by
    rintro d a b S1 k0 rfl hb hl U rfl rfl ha hbU
    have hab := hb.1
    have hfS : op d a b ∉ insert a (insert b U) := fun h => hb.fresh hl hm.2 (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by simp [h])
    have eS : insert a (insert b U) = insert b U := Finset.insert_eq_of_mem (by simp [ha])
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := pos' t) hl (hb.min hl hm.2).2 (he t (Or.inr rfl))
    rw [Finset.card_insert_of_notMem hf] at h1
    rw [eS, Finset.card_insert_of_notMem hbU] at hx
    obtain ⟨p, q, hp, hq, hpq, hpa, hqa, hh⟩ := av a (by simp)
    have := ht_bi hab (Or.inr rfl) hl hp hq (fun e => absurd e hpa) (fun _ => hbU) (fun e => absurd e hqa) (fun _ => hbU) hh
    have m1 := phi_mem (g := op d a b) hp
    have m2 := phi_mem (g := op d a b) hq
    have hne : (if p = a ∨ p = b then op d a b else p) ≠ (if q = a ∨ q = b then op d a b else q) := by
      simp only [hpa, hqa, false_or]
      have h1' : p = b ∨ p ∈ U := by simp at hp; tauto
      have h2' : q = b ∨ q ∈ U := by simp at hq; tauto
      split_ifs with r s s
      · exact absurd (r.trans s.symm) hpq
      · intro e; exact hf (e ▸ h2'.resolve_left s)
      · intro e; exact hf (e ▸ h1'.resolve_left r)
      · exact hpq
    have k1 := h3 _ m1 _ m2 hne this
    have c1 := h2 _ m1; have c2 := h2 _ m2
    omega
  constructor
  · intro d a b S1 k0 hk' hb hl
    by_contra hc
    obtain ⟨hab, U, e1, e2, hal⟩ := id hb
    have hfS : op d a b ∉ S := fun h => hb.fresh hl (by rw [← hk']; exact hm.2) (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by rw [e1]; simp [h])
    have hs1 := (hb.min hl (by rw [← hk']; exact hm.2)).size.1
    have hcS1 : S1.card = U.card + 1 := by rw [e2, Finset.card_insert_of_notMem hf]
    by_cases ha : a ∈ U
    · by_cases hbU : b ∈ U
      · have : S = U := by rw [e1, Finset.insert_eq_of_mem hbU, Finset.insert_eq_of_mem ha]
        rw [this] at hx; omega
      · exact kb d a b S1 k0 hk' hb hl U e1 e2 ha hbU
    · by_cases hbU : b ∈ U
      · exact kb d b a S1 k0 hk' hb.symm hl U (by rw [e1, Finset.insert_comm]) (by rw [e2, op_comm]) hbU ha
      · have : S.card = U.card + 2 := by
          rw [e1, Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hbU]
        omega
  · rintro a S1 k0 t0 rfl rfl hu hl
    by_contra hc
    obtain ⟨U, rfl, rfl⟩ := id hu
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm.2 (sub_C _ _ (by simp [h]))
    have ha : a ∈ U := by
      by_contra ha
      rw [Finset.card_insert_of_notMem hf, Finset.card_insert_of_notMem ha] at hc; omega
    have eS : insert a U = U := Finset.insert_eq_of_mem ha
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := true) hl (hu.min hl hm.2).2 (Or.inl rfl)
    rw [Finset.card_insert_of_notMem hf] at h1
    rw [eS] at hx
    obtain ⟨p, q, hp, hq, hpq, hpa, hqa, hh⟩ := av a (by simp)
    have hpos : pos' (t0 + 1) = true := by simp [pos']
    rw [hpos] at hh
    have := ht_un hp hq (fun e => absurd e hpa) (fun e => absurd e hqa) hh
    simp only [hpa, hqa, if_false] at this
    have m1 : p ∈ insert (a ^^^ m) U := by rw [eS] at hp; simp [hp]
    have m2 : q ∈ insert (a ^^^ m) U := by rw [eS] at hq; simp [hq]
    have k1 := h3 _ m1 _ m2 hpq this
    have c1 := h2 _ m1; have c2 := h2 _ m2
    omega
lemma tst_sound {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    ∃ y, (∀ F : ℕ → Bool, tst (pos' t) l (k + 1 - t) v F = F y) ∧ (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK R m T k' t S)) := by
  have hsz := hm.size
  have hcard := hs.rep.card
  have e : ∀ F : ℕ → Bool, tst (pos' t) l (k + 1 - t) v F = bif Nat.beq v.length (k + 1 - t) then (bif rect (pos' t) l (wst (pos' t) l v) v [] then false else F 0) else
      (bif Nat.beq (v.length + 1) (k + 1 - t) then (bif bip l (wst (pos' t) l v) v [] then false else
        (bif flk l (wst (pos' t) l v) v star then F 0 else F 1)) else F 0) := by
    intro F
    change (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flk l (wst (pos' t) l v) v star)) false
        (bip l (wst (pos' t) l v) v [])) (Nat.beq (v.length + 1) (k + 1 - t)))
      (Bool.rec (motive := fun _ => Bool) (F 0) false (rect (pos' t) l (wst (pos' t) l v) v [])) (Nat.beq v.length (k + 1 - t)) : Bool) = _
    rw [bR, bR, bR, bR, bR]
  cases h1 : Nat.beq v.length (k + 1 - t) with
  | true =>
    have h1' := Nat.eq_of_beq_eq_true h1
    have hr := rect_ok X hs hm hk (by omega)
    exact ⟨0, fun F => by rw [e, h1, hr]; rfl, Or.inl rfl⟩
  | false =>
    cases h2 : Nat.beq (v.length + 1) (k + 1 - t) with
    | false => exact ⟨0, fun F => by rw [e, h1, h2]; rfl, Or.inl rfl⟩
    | true =>
      have h2' := Nat.eq_of_beq_eq_true h2
      have hbip : bip l (wst (pos' t) l v) v [] = false := by
        obtain ⟨x, f, q1, q2, q3⟩ := chrom (N := NN) (e := pos' t) hm.1 hm.2 (by
          rcases Nat.eq_zero_or_pos t with h | h
          · exact Or.inr h
          · exact Or.inl (by simp [pos', h]))
        refine bip_aux (col := f) v [] [] ?_ (by simp) (by simp) ?_
        · intro w hw
          have := q2 w.s (hs.rep.mem.2 ⟨w, hw, rfl⟩); omega
        · have hnd : v.Pairwise (fun a b => a.s ≠ b.s) := List.pairwise_map.1 hs.rep.1
          refine hnd.imp_of_mem fun {a b} ha hb hab hh => ?_
          exact q3 b.s (hs.rep.mem.2 ⟨b, hb, rfl⟩) a.s (hs.rep.mem.2 ⟨a, ha, rfl⟩) (Ne.symm hab) (hit_ht X hs hb ha hh)
      cases h3 : flk l (wst (pos' t) l v) v star with
      | true => exact ⟨0, fun F => by rw [e, h1, h2, hbip, h3]; rfl, Or.inl rfl⟩
      | false => exact ⟨1, fun F => by rw [e, h1, h2, hbip, h3]; rfl, Or.inr ⟨rfl, by omega, nk_ok X hs hm (by omega) h3⟩⟩
lemma cv_ok {t k k' z : ℕ} {v : List W} {S : Finset ℕ} {b : Bool} (hs : StOk P T l k z v S) (hl : Live R m T k' t S)
    (h : cv (pos' t) l v b = false) : b = false := by
  have hcov : Nat.beq (cov (pos' t) l v) l = true := by
    rw [Nat.beq_eq]
    apply Nat.eq_of_testBit_eq; intro i
    cases hli : l.testBit i with
    | false =>
      by_contra hc
      obtain ⟨w, _, hw⟩ := (cov_bit _ _ _ _).1 (by simpa using hc)
      rw [sp_bit, hli] at hw; simp at hw
    | true =>
      rw [cov_bit]
      obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
      obtain ⟨w, hw, hs1⟩ := hl.cov m1 m2 t1 t2
      obtain ⟨w', hw', rfl⟩ := hs.rep.mem.1 hw
      exact ⟨w', hw', by rw [sp_bit, hli, hs1]; rfl⟩
  simp only [cv, bR, hcov, cond_true] at h
  cases hp : pos' t <;> rw [hp] at h <;> simpa using h
end sound
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma gate_sound {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hp : pair (modeF n e (mid f m g e (Nat.pred n) z v)) (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
  subst hd hn
  have hmin := hb.min hl hm.2
  have hpos := hl.pos
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (opW d' a c).s := fun w hw e => hfr (by
    rw [← opW_s, ← e]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  have ho0 : (opW d' a c).s ≠ 0 := fun e => hfr (by rw [← opW_s, e]; simp [C])
  have ho1 : (opW d' a c).s ≠ m := fun e => hfr (by rw [← opW_s, e]; simp [C])
  obtain ⟨r0, hr0, hins⟩ := ins_spec (opW d' a c) v hosS
  obtain ⟨s1, s2, s3, s4⟩ := shape_all hosS hr0 hs.rep.1 ha hc hb.1
  have hp := pair_false hp d'
  generalize hoa : dfc (pos' t) d' l (wst (pos' t) l v) a c = da at hp
  generalize hoc : dfc (pos' t) d' l (wst (pos' t) l v) c a = dc at hp
  have filt : ∀ {x y : W}, (∀ i, (Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (NN + i) = false else y.s.testBit i = true) →
      dfc (pos' t) d' l (wst (pos' t) l v) x y = 0 := by
    intro x y hu
    unfold dfc
    generalize Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v) = u at *
    cases d'
    · simp only [Bool.cond_false, nl, nx] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_xor, Nat.testBit_and]; cases h1 : u.testBit i <;> simp_all
    · simp only [Bool.cond_true, nl, nsr] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_and, Nat.testBit_shiftRight]; cases h1 : u.testBit i <;> simp_all
  have fa : a.s ∉ S' → da = 0 := fun h => by
    rw [← hoa]; exact filt fun i hi => drop_ok X hs.rep hb hl ha h hi
  have fc : c.s ∉ S' → dc = 0 := fun h => by
    rw [← hoc]; exact filt fun i hi => drop_ok X hs.rep hb.symm hl hc h hi
  have b0 : ∀ {q : ℕ}, q = 0 → Nat.beq q 0 = true := fun h => by rw [h]; rfl
  have hput : ∀ h, put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v h = h r0 := fun h => by
    rw [put_eq (by cases d' <;> rfl) (by cases d' <;> rfl) ho0 ho1, hins]
  have hv2 : 2 ≤ v.length := by
    rw [← hs.rep.card]
    have : ({a.s, c.s} : Finset ℕ) ⊆ S := by
      intro x hx; simp at hx; rcases hx with rfl | rfl; exacts [hb.sub.1, hb.sub.2.1]
    have h2 := Finset.card_le_card this
    rwa [Finset.card_pair hb.1] at h2
  have hpr : Nat.pred v.length + 1 = v.length := by simp [Nat.pred_eq_sub_one]; omega
  have main : ∀ {ka kc : Bool} {r : List W}, ka = decide (a.s ∈ S') → kc = decide (c.s ∈ S') → Shape (opW d' a c) a c v ka kc r →
      r.length = S'.card ∧ StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
      ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
    intro ka kc r h1 h2 h3
    have := (bi_st X hs hm hk hb hl ha hc h1 h2 h3).1
    exact ⟨this.rep.card.symm, this, fun w hw => h3.mem hw⟩
  have hguard : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
    by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s4).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s2).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s3).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s1).2
  have fin : ∀ {z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l k z' r S' → (∀ w ∈ r, w = opW d' a c ∨ w ∈ v) →
      child f g mk z' = false → ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v :=
    fun {z' r mk} h1 h2 h3 h4 => ⟨z', r, child_sound X h1 h2 hmin hk h4, h2, h3⟩
  by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s4
    have hlen := s4.len; simp at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => by omega)) hguard
    exact fin hput c3 c4 ((kids_false hmid).2.2.2 (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s2
    have hlen := s2.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inr (fc q2))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).2.1 (b0 (fc q2)) (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s3
    have hlen := s3.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).2.2.1 (b0 (fa q1)) (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s1
    have hlen := s1.len; simp only [Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => ⟨fa q1, fc q2⟩) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).1 (b0 (fa q1)) (b0 (fc q2)))
end sound
def notW (m : ℕ) (a : W) : W := ⟨a.s ^^^ m, a.b, a.a, a.c, 0⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma un_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {a : W} {ka : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hb : Un m a.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hka : ka = decide (a.s ∈ S'))
    (hsh : bif ka then r.Perm (notW m a :: v) else (a :: r).Perm (notW m a :: v)) :
    StOk P T l k (z - a.c - (bif ka then a.c else 0)) r S' := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hfr := hb.fresh hl hm.2
  have hfS : a.s ^^^ m ∉ S := fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha
  have haS : a.s ∈ S := hb.sub.1
  have wo : WOk P (notW m a) := by
    refine ⟨wa.pb, wa.pa, by rw [Nat.or_comm]; exact wa.ec, fun j hj h => ?_, fun j hj h => ?_⟩
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.cb j hj h]; simp
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.ca j hj h]; simp
  have hov : ((notW m a :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => hfS ?_, hs.rep.1⟩
    rw [← hs.rep.2]; simpa [notW] using hm
  have hov2 : ∀ x, x ∈ (notW m a :: v).map W.s ↔ x = a.s ^^^ m ∨ x ∈ S := fun x => by
    rw [← hs.rep.2]; simp [notW]
  have hS' : ∀ x, x ∈ S' ↔ x = a.s ^^^ m ∨ (x ∈ S ∧ (x = a.s → ka = true)) := by
    intro x
    obtain ⟨U, e1, e2⟩ := hb
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_⟩
        rintro rfl; rw [hka, e2]; simp [h]
    · rintro (h | ⟨h, f1⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hne : a.s ≠ a.s ^^^ m := fun e => hfS (e ▸ haS)
  have hrep : Rep r S' := by
    cases hkk : ka with
    | true =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      refine ⟨hn, Finset.ext fun x => ?_⟩
      rw [List.mem_toFinset, (hsh.map W.s).mem_iff, hov2, hS']; simp
    | false =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      simp only [List.map_cons, List.nodup_cons] at hn
      refine ⟨hn.2, Finset.ext fun x => ?_⟩
      have hx := (hsh.map W.s).mem_iff (a := x)
      rw [hov2] at hx; simp only [List.map_cons, List.mem_cons] at hx
      rw [List.mem_toFinset, hS']
      constructor
      · intro h1
        rcases hx.1 (Or.inr h1) with e | e
        · exact Or.inl e
        · exact Or.inr ⟨e, fun e => absurd (e ▸ h1) hn.1⟩
      · rintro (e | ⟨e, f1⟩)
        · exact (hx.2 (Or.inl e)).resolve_left fun e' => hne (e'.symm.trans e)
        · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  have hmem : ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
    intro w hw
    have : w ∈ notW m a :: v := by
      cases hkk : ka <;> rw [hkk] at hsh
      · exact List.Perm.subset hsh (by simp [hw])
      · exact List.Perm.subset hsh hw
    simpa using this
  have hcnt : ∀ j, cnt r j + (bif ka then 0 else fl a j) = fl a j + cnt v j := by
    intro j
    have ef : fl (notW m a) j = fl a j := rfl
    cases hkk : ka <;> rw [hkk] at hsh
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hmem w hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hmem w hw with rfl | h
    · have hg := hs.good a ha
      refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
      · change (a.s ^^^ m).testBit i = (a.s ^^^ m).testBit j
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.1 i j h h1 h2, (X.lg i h1).1.1, (X.lg j h2).1.1]
      · change (a.s ^^^ m).testBit (NN + i) = (a.s ^^^ m).testBit (NN + j)
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.2 i j h h1 h2, (X.lg i h1).1.2.1, (X.lg j h2).1.2.1]
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - fl a j
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_one ha hs.rep.1 j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (X.hP j hj).1 (wa.cst hj hkill) hsol)
      have : fl a j = 1 := by simp [fl, hkill]
      omega
    · refine hcl j hj (q + 1) ?_ (hb.im (X.hP j hj).1 hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill]
      omega
  have hle' := cnt_le X hrep hwok hcl' (hb.min hl hm.2) hk
  refine ⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    rw [ea, hz]
    conv_lhs => rw [fl_pk wa]
    rw [pk_sub, pk_sub]
    · refine pk_congr fun j hj => ?_
      have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_one ha hs.rep.1 j; have q4 := hb15 j hj
      have q5 := hcnt j; have q6 := fl_le a j
      simp only [b'] at q2 ⊢
      cases ka <;> simp at q5 ⊢ <;> omega
    · intro j hj; have := hle j hj; have := le1 j; have := fl_le a j; omega
    · intro j hj; have := hle j hj; have := fl_le a j; omega
end sound
lemma nots_false {f : ℕ → ℕ → List W → Bool} {m g e n z q : ℕ} {v r : List W} (h : nots f m g e n z q v r = false)
    {a : W} (ha : a ∈ r) (hq : a.s + 1 ≠ q) : ins (notW m a) v (fun v =>
      (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
      (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) = false := by
  induction r with
  | nil => simp at ha
  | cons w r ih =>
    change (Bool.rec (motive := fun _ => Bool) (nots f m g e n z q v r) true (Bool.rec (motive := fun _ => Bool)
      (st (Nat.xor w.s m) (fun s => st (Nat.sub z w.c) (fun z => ins ⟨s, w.b, w.a, w.c, 0⟩ v (fun v =>
        Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
          (child (f s) g (fun h => h v) (Nat.sub z w.c)) (Nat.ble (Nat.succ n) e)) true
          (Bool.rec (motive := fun _ => Bool) false (child (f s) g (rm w.s w.s v) z) (Nat.ble n e)))))) false (Nat.beq (Nat.succ w.s) q)) : Bool) = false at h
    rw [bR, bR] at h
    simp only [st_eq, bR] at h
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [Bool.eq_false_iff.2 fun h => hq (Nat.eq_of_beq_eq_true h), Bool.cond_false] at h
      cases hh : ins (notW m a) v (fun v =>
        (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
        (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) with
      | false => rfl
      | true =>
        have h : (bif ins (notW m a) v (fun v =>
          (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
          (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) then true
          else nots f m g e n z q v r) = false := h
        rw [hh] at h; simp at h
    · refine ih ?_ ha
      revert h
      cases nots f m g e n z q v r <;> simp
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nots_sound {f : ℕ → ℕ → List W → Bool} {e n z q t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Un m a.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hq : a.s + 1 ≠ q) {rr : List W} (har' : a ∈ rr)
    (hp : nots f m g e n z q v rr = false) : ∃ z' r, f (a.s ^^^ m) z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
  subst hn
  have hmin := hb.min hl hm.2
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (notW m a).s := fun w hw e => hfr (by
    change a.s ^^^ m ∈ _
    have : w.s = a.s ^^^ m := e
    rw [← this]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  obtain ⟨r0, hr0, hins⟩ := ins_spec (notW m a) v hosS
  have h := nots_false hp har' hq
  rw [hins] at h
  have hl0 : r0.length = v.length + 1 := by rw [hr0.length_eq]; simp
  have hnd : (r0.map W.s).Nodup := by
    refine (hr0.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => hosS w hw, hs.rep.1⟩
  have har : a ∈ r0 := hr0.symm.subset (by simp [ha])
  have hmem : ∀ w ∈ r0, w = notW m a ∨ w ∈ v := fun w hw => by simpa using hr0.subset hw
  by_cases q1 : a.s ∈ S'
  · have hst := un_st X hs hm hk hb hl ha (ka := true) (by simp [q1]) hr0
    have hc := hst.rep.card
    have hb1 : Nat.ble (v.length + 1) e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c - a.c) <;> simp
    exact ⟨_, _, child_sound X (fun h => rfl) hst hmin hk h, hst, hmem⟩
  · have hperm : (a :: r0.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))).Perm (notW m a :: v) := by
      rw [filter1]; exact (filter_perm hnd har).trans hr0
    have hst := un_st X hs hm hk hb hl ha (ka := false) (by simp [q1]) hperm
    simp only [Bool.cond_false, Nat.sub_zero] at hst
    have hc := hst.rep.card
    have hlen := hperm.length_eq
    simp only [List.length_cons] at hlen
    have hb1 : Nat.ble v.length e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) g (rm a.s a.s r0) (z - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (rm a.s a.s r0) (z - a.c) <;> simp
    exact ⟨_, _, child_sound X (rm_eq _ _ _) hst hmin hk h, hst, fun w hw => hmem w (List.mem_of_mem_filter hw)⟩
end sound
lemma scan_false {p : X → Bool} {xs : List X} (h : scan p xs = false) : ∀ c ∈ xs, p c = false := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (scan p r) true (p a) : Bool) = false at h
    rw [bR] at h
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · revert h; cases p c <;> simp
    · refine ih ?_ c hc
      revert h; cases scan p r <;> simp
lemma pairs_false {h : X → X → Bool} {xs : List X} (hp : pairs h xs = false) : xs.Pairwise (fun a c => h a c = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairs h r) true (scan (h a) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · apply scan_false; revert hp; cases scan (h a) r <;> simp
    · apply ih; revert hp; cases pairs h r <;> simp
lemma beq_f {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
lemma pairsP_false {h : X → X → Bool} {xs : List X} {q : ℕ} {a c : X} (hp : pairsP q h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s ≠ q) : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [beq_f hcq, Bool.cond_false] at h2
lemma pairsQ_false {h : X → X → Bool} {xs : List X} {q q' : ℕ} {a c : X} (hp : pairsQ q q' h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s = q') : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [hcq, Nat.beq_refl, Bool.cond_true] at h2
lemma pos_eq (t : ℕ) : pos t = pos' t := by cases t <;> simp [pos, pos']
lemma fr_mem {xs : List X} {a : X} (ha : a ∈ xs) (h : a.w.r = 0) : a ∈ fr xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List X) (fr xs) (x :: fr xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [h]; simp
    · cases Nat.beq x.w.r 0
      · exact ih ha
      · exact List.mem_cons_of_mem _ (ih ha)
lemma fs_mem {xs : List X} {a : X} (ha : a ∈ xs) (h : a.w.r ≠ 0) : a ∈ fs xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List X) (x :: fs xs) (fs xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [beq_f h]; simp
    · cases Nat.beq x.w.r 0
      · exact List.mem_cons_of_mem _ (ih ha)
      · exact ih ha
lemma pairs_any {h : X → X → Bool} {xs : List X} (hp : pairs h xs = false) {a c : X} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c) :
    h a c = false ∨ h c a = false := by
  have hpw := pairs_false hp
  have : Std.Symm (fun a c : L_meta_33826.X => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
  exact (hpw.imp (S := fun a c => h a c = false ∨ h c a = false) fun h => Or.inl h).forall ha hc hne
lemma pairsN_false {h : X → X → Bool} {xs : List X} (hp : pairsN h xs = false) {a c : X} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c)
    (hr : a.w.r = 0 ∨ c.w.r = 0) : h a c = false ∨ h c a = false := by
  simp only [pairsN, bR] at hp
  cases h1 : pairs h (fr xs) with
  | true => rw [h1] at hp; simp at hp
  | false =>
    rw [h1, cond_false] at hp
    by_cases hra : a.w.r = 0
    · by_cases hrc : c.w.r = 0
      · exact pairs_any h1 (fr_mem ha hra) (fr_mem hc hrc) hne
      · exact Or.inl (scan_false (scan_false hp a (fr_mem ha hra)) c (fs_mem hc hrc))
    · have hrc := hr.resolve_left hra
      exact Or.inr (scan_false (scan_false hp c (fr_mem hc hrc)) a (fs_mem ha hra))
def Cod (R : ℕ → ℕ) (v : List W) : Prop := ∀ w ∈ v, w.r = 0 ∨ w.r = R w.s
def RR (R : ℕ → ℕ) : Prop := ∀ d a b, R a ≠ 0 → R b ≠ 0 → ¬ Al R d a b
lemma opW_r (d : Bool) (a c : W) : (opW d a c).r = 0 := by cases d <;> rfl
lemma mv_false (F : ℕ → ℕ → ℕ → List W → Bool) (l m g k t z : ℕ) (v : List W) (y : ℕ) (h : mv F l m g k t z v y = false) :
    node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN = false ∧
    ∀ s, t = s + 1 → nots (fun q z v => cv (pos' s) l v (tst (pos' s) l (k - s) v (fun y =>
      bif node (F (k - 2) s) (pos' s) l m g (k - 1 - s - y) v.length z v (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => cv (pos' s) l v (tst (pos' s) l (k - 1 - s) v (fun y =>
        node (F (k - 3) s) (pos' s) l m g (k - 2 - s - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s - y) v.length z (q + 1) v v)))) m g (k - s - y) v.length z 0 v v = false := by
  change (Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (k - s) v (fun y =>
      (Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (k - 1 - s) v (fun y =>
        node (F (k - 3) s) (pos s) l m g (k - 2 - s - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s - y) v.length z (q + 1) v v)) true
        (node (F (k - 2) s) (pos s) l m g (k - 1 - s - y) v.length z v (pairsP q)) : Bool)))) m g (k - s - y) v.length z 0 v v)) true
      (node (F (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsN) : Bool) = false at h
  simp only [bR, pos_eq] at h
  cases h1 : node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN with
  | true => rw [h1] at h; simp at h
  | false =>
    rw [h1, Bool.cond_false] at h
    refine ⟨rfl, ?_⟩
    rintro s rfl
    exact h
lemma NK.sizeB {m T k k' t : ℕ} {S S1 : Finset ℕ} {d : Bool} {a b n y : ℕ} (hn : S.card = n) (hm : Min R m T (k' + 1) t S) (hk : k' + 1 ≤ k)
    (hb : Bi R d a b S S1) (hl : Live R m T k' t S1) (hy : y = 0 ∨ (y = 1 ∧ n + t = k ∧ NK R m T (k' + 1) t S)) : S1.card ≤ k - t - y := by
  have hs := (hb.min hl hm.2).size.1
  rcases hy with rfl | ⟨rfl, h1, h2⟩
  · omega
  · have := h2.1 d a b S1 k' rfl hb hl; omega
lemma NK.sizeU {m T k k' t : ℕ} {S S1 : Finset ℕ} {a n y : ℕ} (hn : S.card = n) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' + 1 ≤ k)
    (hb : Un m a S S1) (hl : Live R m T k' t S1) (hy : y = 0 ∨ (y = 1 ∧ n + (t + 1) = k ∧ NK R m T (k' + 1) (t + 1) S)) : S1.card ≤ k - t - y := by
  have hs := (hb.min hl hm.2).size.1
  rcases hy with rfl | ⟨rfl, h1, h2⟩
  · omega
  · have := h2.2 a S1 k' t rfl rfl hb hl; omega
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma node_bi {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : (L_meta_33826.X → L_meta_33826.X → Bool) → List L_meta_33826.X → Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' x y S S') (hl : Live R m T k' t S')
    (hgo : ∀ h xs, go h xs = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → xs = v.map (mkx d l (wst d l v)) →
      h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false ∨ h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false)
    (hp : node f d l m g e n z v go = false) : ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ w ∈ v := by
  rw [node_eq] at hp
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb hl ha hc h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s], by rw [e, opW_r]⟩) id⟩
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb.symm hl hc ha h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s, op_comm], by rw [e, opW_r]⟩) id⟩
lemma mv_sound (hR : RR R) {F : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), F k t z v = false → StOk P T l k z v S → Cod R v → ∀ k' ≤ k, ¬ Min R m T k' t S)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hcod : Cod R v) (hlen : 2 ≤ v.length)
    (h : mv F l m g k t z v y = false) : ∀ k' ≤ k, Min R m T k' t S → (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK R m T k' t S)) → False := by
  intro k' hk hm hy
  obtain ⟨hA, hN⟩ := mv_false F l m g k t z v y h
  have hcard := hs.rep.card
  have codB : ∀ {v r : List W} {o : ℕ}, Cod R v → (∀ w ∈ r, (w.s = o ∧ w.r = 0) ∨ w ∈ v) → Cod R r := by
    intro v r o hv hr w hw
    rcases hr w hw with ⟨_, h⟩ | h
    · exact Or.inl h
    · exact hv w h
  have codU : ∀ {v r : List W} {a : W}, Cod R v → (∀ w ∈ r, w = notW m a ∨ w ∈ v) → Cod R r := by
    intro v r o hv hr w hw
    rcases hr w hw with h | h
    · exact Or.inl (by rw [h]; rfl)
    · exact hv w h
  rcases first_move k' t S hm (by omega) with
    ⟨k0, d, a, b, S1, rfl, hb, hl⟩ | ⟨k0, t0, a, d, c, S1, S2, rfl, rfl, hu, hb, hl⟩ |
    ⟨k0, t0, a, a', d, S1, S2, S3, rfl, rfl, hu, hne, hu', hb, hl⟩
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hs hm (by omega) rfl rfl (NK.sizeB hcard hm hk hb hl hy) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      refine pairsN_false hp (List.mem_map_of_mem ha) (List.mem_map_of_mem hc) ?_ ?_
      · intro e
        have : a.s = c.s := congrArg L_meta_33826.X.s e
        exact hb.1 (by rw [← hax, ← hcy, this])
      · by_contra hc'
        push Not at hc'
        obtain ⟨_, U, _, _, hal⟩ := hb
        have h1 : a.r = R a.s := (hcod a ha).resolve_left hc'.1
        have h2 : c.r = R c.s := (hcod c hc).resolve_left hc'.2
        have g1 : a.r ≠ 0 := hc'.1
        have g2 : c.r ≠ 0 := hc'.2
        rw [← hax, ← hcy] at hal
        exact hR _ _ _ (by rw [← h1]; exact g1) (by rw [← h2]; exact g2) hal) hA
    exact hF _ _ _ _ _ hf hst (codB hcod hmem) k0 (by simpa using hk) (hb.min hl hm.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hl1 := hb.live hl
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN t0 rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 1) hs hm (by omega) rfl (NK.sizeU hcard hm hk hu hl1 hy) hu hl1 hwa (by omega) hwa h2
    have hm1 := hu.min hl1 hm.2
    have hf1 := cv_ok X hst1 hl1 hf1
    obtain ⟨y1, hF1, hy1⟩ := tst_sound X hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    rw [Bool.not_eq_true] at hf2
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst1 hm1 (by omega) rfl rfl (NK.sizeB hst1.rep.card hm1 (by omega) hb hl hy1) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsP_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) (fun e => hb.1 (by rw [← hcy, ← e]; rfl)))) hf2
    exact hF _ _ _ _ _ hf hst (codB (codU hcod hmem1) hmem) k0 (by simpa using hk) (hb.min hl hm1.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hl1 := hb.live hl
    have hl2 := hu'.live hl1
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN (t0 + 1) rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 2) hs hm (by omega) rfl (NK.sizeU hcard hm hk hu hl2 hy) hu hl2 hwa (by omega) hwa h2
    have hm1 := hu.min hl2 hm.2
    have hf1 := cv_ok X hst1 hl2 hf1
    obtain ⟨y1, hF1, hy1⟩ := tst_sound X hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    obtain ⟨wa', hwa', rfl⟩ := hst1.rep.mem.1 hu'.sub.1
    obtain ⟨z2, r2, hf3, hst2, hmem2⟩ := nots_sound X (k := k + 1) hst1 hm1 (by omega) rfl (NK.sizeU hst1.rep.card hm1 (by omega) hu' hl1 hy1) hu' hl1 hwa' (by omega) hwa' hf1
    have hm2 := hu'.min hl1 hm1.2
    have hf3 := cv_ok X hst2 hl1 hf3
    obtain ⟨y2, hF3, hy2⟩ := tst_sound X hst2 hm2 (by omega)
    have hf3 := (hF3 _).symm.trans hf3
    beta_reduce at hf3
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst2 hm2 (by omega) rfl rfl (NK.sizeB hst2.rep.card hm2 (by omega) hb hl hy2) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsQ_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) hcy)) hf3
    exact hF _ _ _ _ _ hf hst (codB (codU (codU hcod hmem1) hmem2) hmem) k0 (by simpa using hk) (hb.min hl hm2.2)
lemma look_sound (hR : RR R) : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g fuel k t z v = false → StOk P T l k z v S → Cod R v →
    ∀ k' ≤ k, ¬ Min R m T k' t S := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hm
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => mv (look l m g fuel) l m g k t z v y)) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hm hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      exact mv_sound X hR ih hs hcod hlen hy k' hk hm hyk
end sound
lemma Live.W {m T k t : ℕ} {S : Finset ℕ} {Q : Set ℕ} (hl : Live R m T k t S) (hQ : (S : Set ℕ) ⊆ Q) : Sol Z0 m T k Q := hl.sol.mono le_rfl hQ
lemma front {m T : ℕ} (hR : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {k t : ℕ} {S : Finset ℕ} (hl : Live Z0 m T k t S)
    (hm : ∀ q < k, ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) :
    Live R m T k t S ∨ ∃ k0 d a b S1, k = k0 + 1 ∧ R a ≠ 0 ∧ R b ≠ 0 ∧ Bi Z0 d a b S S1 ∧ Live Z0 m T k0 t S1 := by
  induction hl with
  | stop => exact Or.inl .stop
  | @un k t a U hl ih =>
    set Q : Set ℕ := {x | R x ≠ 0} with hQ
    have hfr : a ^^^ m ∉ C m (Q ∪ ((insert a U : Finset ℕ) : Set ℕ)) := by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU : a ^^^ m ∉ U := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR : R (a ^^^ m) = 0 := by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm' : ∀ q < k, ¬ Sol Z0 m T q (C m (Q ∪ ((insert (a ^^^ m) U : Finset ℕ) : Set ℕ))) := by
      intro q hq hs
      refine hm (q + 1) (by omega) (.un (a := a) (Or.inl (Or.inr (by simp))) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0, d, x, y, S1, rfl, hx, hy, ⟨hxy, V, e1, rfl, hal⟩, hl1⟩
    · exact Or.inl (.un h)
    · have nx : x ≠ a ^^^ m := fun e => hx (e ▸ hfR)
      have ny : y ≠ a ^^^ m := fun e => hy (e ▸ hfR)
      have hmV : a ^^^ m ∈ V := by
        have : a ^^^ m ∈ insert x (insert y V) := by rw [← e1]; simp
        simp at this
        rcases this with h | h | h
        · exact absurd h.symm nx
        · exact absurd h.symm ny
        · exact h
      have eU : U = insert x (insert y (V.erase (a ^^^ m))) := by
        ext z
        by_cases hz : z = a ^^^ m
        · subst hz
          simp [hfU, Ne.symm nx, Ne.symm ny]
        · have : z ∈ insert (a ^^^ m) U ↔ z ∈ insert x (insert y V) := by rw [e1]
          simp only [Finset.mem_insert, hz, false_or, Finset.mem_erase, ne_eq, not_false_eq_true, true_and] at this ⊢
          exact this
      refine Or.inr ⟨k0 + 1, d, x, y, insert a (insert (op d x y) (V.erase (a ^^^ m))), rfl, hx, hy,
        ⟨hxy, insert a (V.erase (a ^^^ m)), ?_, ?_, hal⟩, ?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]; tauto
      · ext z; simp only [Finset.mem_insert]; tauto
      · refine .un ?_
        have : insert (a ^^^ m) (insert (op d x y) (V.erase (a ^^^ m))) = insert (op d x y) V := by
          rw [Finset.insert_comm, Finset.insert_erase hmV]
        rw [this]; exact hl1
  | @bi k t d0 a b U hab hal0 hl ih =>
    set Q : Set ℕ := {x | R x ≠ 0} with hQ
    have hb0 : Bi Z0 d0 a b (insert a (insert b U)) (insert (op d0 a b) U) := ⟨hab, U, rfl, rfl, hal0⟩
    by_cases hW : R a ≠ 0 ∧ R b ≠ 0
    · exact Or.inr ⟨k, d0, a, b, _, rfl, hW.1, hW.2, hb0, hl⟩
    have hal : Al R d0 a b := hR _ _ _ (by
      by_contra hc; push Not at hc; exact hW hc)
    have hfr : op d0 a b ∉ C m (Q ∪ ((insert a (insert b U) : Finset ℕ) : Set ℕ)) := by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU : op d0 a b ∉ U := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfa : op d0 a b ≠ a := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfb : op d0 a b ≠ b := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR : R (op d0 a b) = 0 := by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm' : ∀ q < k, ¬ Sol Z0 m T q (C m (Q ∪ ((insert (op d0 a b) U : Finset ℕ) : Set ℕ))) := by
      intro q hq hs
      refine hm (q + 1) (by omega) (.bi (d := d0) (a := a) (b := b) (Or.inl (Or.inr (by simp))) (Or.inl (Or.inr (by simp))) (al0 _ _ _) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0, d, x, y, S1, rfl, hx, hy, ⟨hxy, V, e1, rfl, hal'⟩, hl1⟩
    · exact Or.inl (.bi hab hal h)
    · set o := op d0 a b with ho
      have nx : x ≠ o := fun e => hx (e ▸ hfR)
      have ny : y ≠ o := fun e => hy (e ▸ hfR)
      have hmV : o ∈ V := by
        have : o ∈ insert x (insert y V) := by rw [← e1]; simp
        simp at this
        rcases this with h | h | h
        · exact absurd h.symm nx
        · exact absurd h.symm ny
        · exact h
      have eU : U = insert x (insert y (V.erase o)) := by
        ext z
        by_cases hz : z = o
        · subst hz
          simp [hfU, Ne.symm nx, Ne.symm ny]
        · have : z ∈ insert o U ↔ z ∈ insert x (insert y V) := by rw [e1]
          simp only [Finset.mem_insert, hz, false_or, Finset.mem_erase, ne_eq, not_false_eq_true, true_and] at this ⊢
          exact this
      refine Or.inr ⟨k0 + 1, d, x, y, insert a (insert b (insert (op d x y) (V.erase o))), rfl, hx, hy,
        ⟨hxy, insert a (insert b (V.erase o)), ?_, ?_, hal'⟩, ?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h | h) <;> simp only [h, true_or, or_true])
      · ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h) <;> simp only [h, true_or, or_true])
      · refine .bi hab hal0 ?_
        have : insert (op d0 a b) (insert (op d x y) (V.erase o)) = insert (op d x y) V := by
          rw [Finset.insert_comm, ← ho, Finset.insert_erase hmV]
        rw [this]; exact hl1
lemma Min.Z {m T k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) : Min Z0 m T k t S := ⟨h.1.rel fun d a b _ => al0 d a b, h.2⟩
lemma NK.toR {m T k t : ℕ} {S : Finset ℕ} (h : NK Z0 m T k t S) : NK R m T k t S :=
  ⟨fun d a b S1 k0 e hb hl => h.1 d a b S1 k0 e (hb.rel fun d a b _ => al0 d a b) (hl.rel fun d a b _ => al0 d a b),
    fun a S1 k0 t0 e e' hu hl => h.2 a S1 k0 t0 e e' hu (hl.rel fun d a b _ => al0 d a b)⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma one_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} {f : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), f k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hlen : 2 ≤ v.length)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ))))
    (hy : y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK Z0 m T k' t S))
    (h2 : mv (look l m g K) l m g k t z v y = false)
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (L_meta_33826.X → L_meta_33826.X → Bool) → List L_meta_33826.X → Bool,
      node (f (k - 1) t) (pos' t) l m g (k - t - y) v.length z v go = false ∧
      ∀ h, go h (v.map (mkx (pos' t) l (wst (pos' t) l v))) = false →
        h (mkx (pos' t) l (wst (pos' t) l v) a) (mkx (pos' t) l (wst (pos' t) l v) c) = false ∨
        h (mkx (pos' t) l (wst (pos' t) l v) c) (mkx (pos' t) l (wst (pos' t) l v) a) = false) : False := by
  have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  have hcard := hs.rep.card
  rcases front hR2 hl hmW with hlR | ⟨k0, d, a, b, S1, rfl, ha, hb', hb, hl1⟩
  · exact mv_sound X hR (look_sound X hR K) hs (fun w hw => Or.inr (hcod w hw)) hlen h2 k' hk ⟨hlR, hmin.2⟩ (hy.imp id fun ⟨q1, q2, q3⟩ => ⟨q1, q2, q3.toR⟩)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hb.sub.1
    obtain ⟨wb, hwb, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
    obtain ⟨go, hg1, hg2⟩ := h1 wa hwa wb hwb hb.1 (by rw [hcod wa hwa]; exact ha) (by rw [hcod wb hwb]; exact hb')
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hs hmin (by omega) rfl rfl (NK.sizeB hcard hmin hk hb hl1 hy) hb hl1 (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      rw [hs.rep.inj ha hwa hax, hs.rep.inj hc hwb hcy]
      exact hg2 h hp) hg1
    have hfr : R (op d wa.s wb.s) = 0 := by
      by_contra hne
      refine hmW k0 (by omega) (hl1.sol.mono le_rfl fun x hx => ?_)
      have hx' := hb.sub.2.2 hx
      simp only [Finset.mem_insert] at hx'
      rcases hx' with rfl | hx'
      · exact Or.inl (Or.inl hne)
      · exact Or.inl (Or.inr hx')
    refine hF _ _ _ _ _ hf hst ?_ k0 (by simpa using hk) hl1 ?_
    · intro w hw
      rcases hmem w hw with ⟨e1, e2⟩ | h
      · rw [e1, e2, hfr]
      · exact hcod w h
    · intro q hq hs'
      refine hmW (q + 1) (by omega) (.bi (d := d) (a := wa.s) (b := wb.s) (Or.inl (Or.inr hb.sub.1)) (Or.inl (Or.inr hb.sub.2.1)) (al0 _ _ _) (hs'.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · have hx' := hb.sub.2.2 hx
        simp only [Finset.mem_insert] at hx'
        rcases hx' with rfl | hx'
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr hx'))
      · exact Or.inr (Or.inr hx)
lemma or_false' {a b : Bool} (h : (Bool.rec (motive := fun _ => Bool) b true a : Bool) = false) : a = false ∧ b = false := by
  clear X
  cases a <;> simp_all
lemma look1_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ),
    look1 l m g K fuel k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look1] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hl hmW
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (look1 l m g K fuel (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsS))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
      obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hmin hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      obtain ⟨hy1, hy2⟩ := or_false' X hy
      refine one_sound X hR hR2 ih hs hcod hlen hk hl hmW hyk hy2 fun a ha c hc hne har hcr => ⟨pairsS, hy1, fun h hp => ?_⟩
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_33826.X.s e))
end sound
def rawP : List ℕ := [bigNat_3, bigNat_4, bigNat_5, bigNat_6, bigNat_7, bigNat_8, bigNat_9, bigNat_10]
def xw (e : ℕ × ℕ) : ℕ := rawP.getD e.1 0 ||| rawP.getD e.2 0
def rawL (E : List (ℕ × ℕ)) : List ℕ := rawP ++ E.map xw
def six : List (ℕ × ℕ) := []
def rawG : List ℕ := rawL six
def FPM : ℕ := 2 ^ 64 - 1
def FULL : ℕ := 2 ^ NN - 1
def TG : ℕ := bigNat_11
def kz (Z : ℕ) : ℕ := (List.range 8).foldr (fun i x => bif Nat.testBit Z i then Nat.lor x (Nat.land (Nat.lor (rawP.getD i 0) (Nat.shiftRight (rawP.getD i 0) NN)) FULL) else x) 0
def lz (Z : ℕ) : ℕ := Nat.land AA (Nat.xor (kz Z) FULL)
def fz (Z : ℕ) : ℕ := Nat.land FPM (Nat.xor (kz Z) FULL)
def mz (Z : ℕ) : ℕ := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) NN)
def tz (Z : ℕ) : ℕ := Nat.land TG (mz Z)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_TG : AA &&& TG = AA := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_lt : TG < 2 ^ NN := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_lt : AA < 2 ^ NN := by decide +kernel
lemma lz_lg (Z i : ℕ) (h : (lz Z).testBit i = true) : Lg NN (mz Z) (tz Z) i ∧ AA.testBit i = true := by
  have hA : AA.testBit i = true := by
    simp only [lz, nl, Nat.testBit_and, Bool.and_eq_true] at h; exact h.1
  have hT : TG.testBit i = true := by
    have := congrArg (fun x => x.testBit i) AA_TG
    simp [hA] at this; exact this
  have m1 : (mz Z).testBit i = true := by simp [mz, no, h]
  have m2 : (mz Z).testBit (NN + i) = true := by
    simp only [mz, no, Nat.testBit_or, Nat.shiftLeft_eq, Bool.or_eq_true]
    right
    change (lz Z <<< NN).testBit (NN + i) = true
    rw [Nat.testBit_shiftLeft]; simp [h]
  refine ⟨⟨m1, m2, ?_, ?_⟩, hA⟩
  · simp only [tz, nl, Nat.testBit_and, hT, m1]; rfl
  · simp only [tz, nl, Nat.testBit_and]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le TG_lt (Nat.pow_le_pow_right (by omega) (by omega)))]; rfl
def segGood (w o : ℕ) (s : ℕ × ℕ) : Bool :=
  Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) 0 || Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) (2 ^ (s.2 - s.1 - 1) - 1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raw_good : rawG.all (fun w => segsX.all (segGood w 0) && segsY.all (segGood w NN)) = true := by decide +kernel
lemma segGood_eq {w o : ℕ} {s : ℕ × ℕ} (h : segGood w o s = true) {i j : ℕ} (h1 : s.1 < i) (h2 : i < s.2) (h3 : s.1 < j) (h4 : j < s.2) :
    w.testBit (o + i) = w.testBit (o + j) := by
  have key : ∀ i, s.1 < i → i < s.2 → w.testBit (o + i) = ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)).testBit (i - s.1 - 1) := by
    intro i h1 h2
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, show o + s.1 + 1 + (i - s.1 - 1) = o + i by omega]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega]
  rw [key i h1 h2, key j h3 h4]
  simp only [segGood, Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with h | h <;> rw [h]
  · simp
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega, show j - s.1 - 1 < s.2 - s.1 - 1 by omega]
lemma wire_good {w : ℕ} (hw : w ∈ rawG) (Z : ℕ) : Good (lz Z) (w &&& mz Z) := by
  have h := List.all_eq_true.1 raw_good w hw
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun i j hij h1 h2 => ?_, fun i j hij h1 h2 => ?_⟩ <;> obtain ⟨s, hs, a1, a2, a3, a4⟩ := hij
  · have := segGood_eq (h.1 s hs) a1 a2 a3 a4
    simp only [Nat.zero_add] at this
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.1, (lz_lg Z j h2).1.1]
  · have := segGood_eq (h.2 s hs) a1 a2 a3 a4
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.2.1, (lz_lg Z j h2).1.2.1]
noncomputable section packingList
def pL (L : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih 5) d) L
end packingList
lemma pL_cons (d : ℕ) (L : List ℕ) : pL (d :: L) = 2 ^ 5 * pL L + d := by
  change (pL L <<< 5) + d = _; rw [Nat.shiftLeft_eq]; ring
lemma pL_pk (L : List ℕ) : pL L = pk L.length (fun j => L.getD j 0) := by
  induction L with
  | nil => simp [pL, pk]
  | cons d L ih =>
    rw [pL_cons, ih, pk, pk, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.mul_zero, pow_zero, mul_one, List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 5 * (j + 1) = 5 * j + 5 by ring, pow_add]; ring
lemma pL_bit {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : ∀ i, (pL L).testBit i = true ↔ (i % 5 = 0 ∧ i / 5 < L.length ∧ L.getD (i / 5) 0 = 1) := by
  induction L with
  | nil => intro i; simp [pL]
  | cons d L ih =>
    intro i
    have hd := h d (by simp)
    have ih := ih fun x hx => h x (by simp [hx])
    rw [pL_cons, Nat.testBit_two_pow_mul_add _ (by omega)]
    split_ifs with hi
    · have : i / 5 = 0 := by omega
      rw [this]
      rcases Nat.eq_zero_or_pos i with rfl | hp
      · interval_cases d <;> simp
      · constructor
        · intro hb
          have : d.testBit i = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hd (Nat.one_lt_two_pow (by omega)))
          rw [this] at hb; simp at hb
        · intro hb; omega
    · rw [ih, show i / 5 = (i - 5) / 5 + 1 by omega]
      simp only [List.length_cons, List.getD_cons_succ]
      constructor
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
lemma pL_isPk {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : isPk L.length (pL L) := fun i hi => by
  have := (pL_bit h i).1 hi; exact ⟨this.1, this.2.1⟩
def bit01 (b : Bool) : ℕ := bif b then 1 else 0
def mkW (P : List ℕ) (s : ℕ) : W := ⟨s, pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0)), pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)),
  Nat.lor (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0))) (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n))), 3⟩
lemma mkW_ok (P : List ℕ) (s : ℕ) : WOk P (mkW P s) := by
  have h01 : ∀ f : ℕ → Bool, ∀ d ∈ P.map (fun n => bit01 (f n)), d ≤ 1 := by
    intro f d hd; simp only [List.mem_map] at hd
    obtain ⟨n, _, rfl⟩ := hd; cases f n <;> simp [bit01]
  have bt : ∀ f : ℕ → Bool, ∀ j < P.length, (pL (P.map fun n => bit01 (f n))).testBit (5 * j) = true → f (P.getD j 0) = true := by
    intro f j hj h
    have h := ((pL_bit (h01 f) _).1 h).2.2
    rw [show 5 * j / 5 = j by omega, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp at h ⊢
    cases hf : f P[j] <;> simp [bit01, hf] at h ⊢
  refine ⟨?_, ?_, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) 0); rwa [List.length_map] at this
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) n); rwa [List.length_map] at this
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) 0) j hj h)
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) n) j hj h)
noncomputable section compiledSearch
def addS (o : W) (v : List W) : List W := List.rec (motive := fun _ => List W) [o]
  (fun w t ih => Bool.rec (motive := fun _ => List W) (w :: ih) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def avl (P : List ℕ) (m : ℕ) (L : List ℕ) : List W := List.rec (motive := fun _ => List W) []
  (fun w _ ih => Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land w m)) ih) ih (Nat.beq (Nat.land w m) m)) ih (Nat.beq (Nat.land w m) 0)) L
def frc (v : List W) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => st w.s fun s => st w.a fun a => st w.b fun b => st w.c fun c => ih fun r => h (⟨s, a, b, c, w.r⟩ :: r)) v
def anySub (d : Bool) (l : ℕ) (v : List W) : ℕ → (List W → Bool) → Bool := List.rec (motive := fun _ => ℕ → (List W → Bool) → Bool) (fun _ h => h [])
  (fun w t ih c h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (ih c h) (Nat.beq (Nat.lor c (cov d l t)) l)) true
    (st (Nat.lor c (sp d l w.s)) fun c => ih c fun r => h (w :: r))) v
def sumc (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add w.c ih) v
def MM : ℕ := 214
def hb (H x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1
def pairsC (H : ℕ) (h : X → X → Bool) (xs : List X) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a r ih => Bool.rec (motive := fun _ => Bool) ih true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r)) xs
def topC (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (node (look1 l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
def hasP (p : ℕ) (v : List W) : Bool := Bool.rec (motive := fun _ => Bool)
  (List.rec (motive := fun _ => Bool) false (fun w _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w.s p)) v) true (Nat.beq p 0)
def startv (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topC l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
end compiledSearch
lemma frc_eq (v : List W) : ∀ h, frc v h = h v := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change st w.s (fun s => st w.a fun a => st w.b fun b => st w.c fun c => frc v fun r => h (⟨s, a, b, c, w.r⟩ :: r)) = _
    simp only [st_eq]; rw [ih]
lemma anySub_false {d : Bool} {l : ℕ} {v : List W} : ∀ {c : ℕ} {h : List W → Bool}, (∀ i, c.testBit i = true → l.testBit i = true) → anySub d l v c h = false →
    ∀ r, r.Sublist v → (∀ i, l.testBit i = true → c.testBit i = true ∨ (cov d l r).testBit i = true) → h r = false := by
  induction v with
  | nil => intro c h _ hh r hr _; rw [List.sublist_nil.1 hr]; exact hh
  | cons w v ih =>
    intro c h hcl hh r hr hcov
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (anySub d l v c h) (Nat.beq (Nat.lor c (cov d l v)) l)) true
      (st (Nat.lor c (sp d l w.s)) fun c => anySub d l v c fun r => h (w :: r)) : Bool) = false at hh
    rw [bR, bR, st_eq] at hh
    cases h1 : anySub d l v (Nat.lor c (sp d l w.s)) (fun r => h (w :: r)) with
    | true => rw [h1] at hh; simp at hh
    | false =>
      rw [h1, Bool.cond_false] at hh
      have hc2 : ∀ i, (cov d l v).testBit i = true → l.testBit i = true := by
        intro i hi
        obtain ⟨w', _, hw'⟩ := (cov_bit _ _ _ _).1 hi
        rw [sp_bit, Bool.and_eq_true] at hw'; exact hw'.1
      cases hr with
      | cons _ hr =>
        have : Nat.beq (Nat.lor c (cov d l v)) l = true := by
          rw [Nat.beq_eq]
          apply Nat.eq_of_testBit_eq; intro i
          rw [no, Nat.testBit_or]
          cases hli : l.testBit i with
          | false =>
            by_contra hc
            rw [Bool.not_eq_false, Bool.or_eq_true] at hc
            rcases hc with h | h
            · rw [hcl i h] at hli; simp at hli
            · rw [hc2 i h] at hli; simp at hli
          | true =>
            rcases hcov i hli with h | h
            · rw [h]; rfl
            · obtain ⟨w', hw', h2⟩ := (cov_bit _ _ _ _).1 h
              rw [(cov_bit d l i v).2 ⟨w', hr.subset hw', h2⟩]; simp
        rw [this, Bool.cond_true] at hh
        exact ih hcl hh r hr hcov
      | cons_cons _ hr =>
        rename_i r'
        refine ih (c := Nat.lor c (sp d l w.s)) ?_ h1 r' hr ?_
        · intro i hi
          rw [no, Nat.testBit_or, Bool.or_eq_true] at hi
          rcases hi with h | h
          · exact hcl i h
          · rw [sp_bit, Bool.and_eq_true] at h; exact h.1
        · intro i hi
          rw [no, Nat.testBit_or, Bool.or_eq_true]
          rcases hcov i hi with h | h
          · exact Or.inl (Or.inl h)
          · change (Nat.lor (sp d l w.s) (cov d l r')).testBit i = true at h
            rw [no, Nat.testBit_or, Bool.or_eq_true] at h
            rcases h with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
lemma addS_cons (o w : W) (t : List W) : addS o (w :: t) = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then w :: t else o :: w :: t) else w :: addS o t := by
  change Bool.rec (motive := fun _ => List W) (w :: addS o t) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s) = _
  cases Nat.ble w.s o.s <;> cases Nat.beq o.s w.s <;> rfl
def Srt (v : List W) : Prop := v.Pairwise (fun a b => b.s < a.s)
lemma addS_spec {o : W} {v : List W} (hv : Srt v) : Srt (addS o v) ∧ (∀ w ∈ addS o v, w = o ∨ w ∈ v) ∧
    (∃ w ∈ addS o v, w.s = o.s) ∧ ∀ w ∈ v, w ∈ addS o v := by
  induction v with
  | nil => exact ⟨List.pairwise_singleton _ _, by simp [addS], ⟨o, by simp [addS], rfl⟩, by simp⟩
  | cons x t ih =>
    have hp := List.pairwise_cons.1 hv
    obtain ⟨i1, i2, i3, i4⟩ := ih hp.2
    rw [addS_cons]
    cases h1 : Nat.ble x.s o.s with
    | true =>
      have hle := Nat.le_of_ble_eq_true h1
      cases h2 : Nat.beq o.s x.s with
      | true => exact ⟨hv, fun w hw => Or.inr hw, ⟨x, by simp, (Nat.eq_of_beq_eq_true h2).symm⟩, fun w hw => hw⟩
      | false =>
        have hne : o.s ≠ x.s := fun e => by rw [e, Nat.beq_refl] at h2; simp at h2
        refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, hv⟩, fun w hw => by simpa using hw, ⟨o, by simp, rfl⟩, fun w hw => by simp at hw ⊢; tauto⟩
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · omega
        · have := hp.1 w hw; omega
    | false =>
      have hlt : o.s < x.s := by
        by_contra hc; rw [Nat.ble_eq_true_of_le (by omega)] at h1; simp at h1
      refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, i1⟩, fun w hw => ?_, ?_, fun w hw => ?_⟩
      · rcases i2 w hw with rfl | h
        · exact hlt
        · exact hp.1 w h
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · rcases i2 w hw with h | h <;> simp [h]
      · obtain ⟨w, hw, e⟩ := i3; exact ⟨w, by simp [hw], e⟩
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · exact Or.inr (i4 w hw)
lemma avl_spec (P : List ℕ) (m : ℕ) (L : List ℕ) : Srt (avl P m L) ∧ (∀ w ∈ avl P m L, ∃ x ∈ L, w = mkW P (x &&& m)) ∧
    ∀ x ∈ L, x &&& m ≠ 0 → x &&& m ≠ m → ∃ w ∈ avl P m L, w.s = x &&& m := by
  induction L with
  | nil => exact ⟨List.Pairwise.nil, by simp [avl], by simp⟩
  | cons y L ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    have e : avl P m (y :: L) = bif Nat.beq (Nat.land y m) 0 then avl P m L else bif Nat.beq (Nat.land y m) m then avl P m L else addS (mkW P (Nat.land y m)) (avl P m L) := by
      change Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land y m)) (avl P m L)) (avl P m L) (Nat.beq (Nat.land y m) m)) (avl P m L) (Nat.beq (Nat.land y m) 0) = _
      cases Nat.beq (Nat.land y m) 0 <;> cases Nat.beq (Nat.land y m) m <;> rfl
    have old : ∀ w ∈ avl P m L, ∃ x ∈ y :: L, w = mkW P (x &&& m) := fun w hw => by
      obtain ⟨x, hx, e⟩ := i2 w hw; exact ⟨x, by simp [hx], e⟩
    rw [e]
    cases h1 : Nat.beq (Nat.land y m) 0 with
    | true =>
      refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact absurd (Nat.eq_of_beq_eq_true h1) h2
      · exact i3 x hx h2 h3
    | false =>
      cases h1' : Nat.beq (Nat.land y m) m with
      | true =>
        refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd (Nat.eq_of_beq_eq_true h1') h3
        · exact i3 x hx h2 h3
      | false =>
        obtain ⟨j1, j2, j3, j4⟩ := addS_spec (o := mkW P (Nat.land y m)) i1
        refine ⟨j1, fun w hw => ?_, fun x hx h2 h3 => ?_⟩
        · rcases j2 w hw with rfl | h
          · exact ⟨y, by simp, rfl⟩
          · exact old w h
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact j3
          · obtain ⟨w, hw, e⟩ := i3 x hx h2 h3; exact ⟨w, j4 w hw, e⟩
lemma pairsC_false {H : ℕ} {h : X → X → Bool} {xs : List X} (hp : pairsC H h xs = false) :
    xs.Pairwise (fun a b => hb H (a.s + b.s) = true → h a b = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairsC H h r) true
      (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · intro b hbm hi
      have h1 : scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r = false := by
        revert hp
        cases scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r <;> simp
      have h2 := scan_false h1 b hbm
      beta_reduce at h2
      rw [bR] at h2
      have h3 : hb H (Nat.add a.s b.s) = true := hi
      rwa [h3, Bool.cond_true] at h2
    · apply ih; revert hp; cases pairsC H h r <;> simp
def mFull (M : List (ℕ × ℕ)) : Bool := (List.range MM).all (fun r => M.any (fun p => hb p.1 r)) && M.any (fun p => Nat.beq p.2 1)
lemma hb_mod (H x : ℕ) : hb H x = hb H (x % MM) := by
  unfold hb
  change Nat.beq ((H >>> (x % MM)) &&& 1) 1 = Nat.beq ((H >>> (x % MM % MM)) &&& 1) 1
  rw [Nat.mod_mod]
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma topC_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)}
    (hM : mFull M = true) (h : ∀ p ∈ M, topC l m g K p.1 p.2 k t z v = false) (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) : False := by
  simp only [mFull, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_eq_true] at hM
  obtain ⟨hM1, p0, hp0, hp1⟩ := hM
  have un : ∀ p ∈ M, 2 ≤ v.length ∧ tst (pos' t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq p.2 1)) true
      (node (look1 l m g K K (k - 1) t) (pos' t) l m g (k - t - y) v.length z v (fun h xs => pairsC p.1 h (fs xs)))) = false := by
    intro p hp
    have h := h p hp
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq p.2 1)) true
      (node (look1 l m g K K (k - 1) t) (pos t) l m g (k - t - y) v.length z v (fun h xs => pairsC p.1 h (fs xs))))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      refine ⟨?_, h⟩
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
  have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hmin hk
  have un2 := fun p hp => (hFy _).symm.trans (un p hp).2
  refine one_sound X hR hR2 (K := K) (f := look1 l m g K K) (look1_sound X hR hR2 (K := K) K) hs hcod (un p0 hp0).1 hk hl hmW hyk ?_ ?_
  · have := (or_false' X (un2 p0 hp0)).2
    rw [bR, hp1, cond_true] at this; exact this
  · intro a ha c hc hne har hcr
    obtain ⟨p, hpM, hpb⟩ := hM1 ((a.s + c.s) % MM) (Nat.mod_lt _ (by decide))
    rw [← hb_mod] at hpb
    refine ⟨_, (or_false' X (un2 p hpM)).1, fun h hp => ?_⟩
    have hpw := pairsC_false hp
    have : Std.Symm (fun a b : L_meta_33826.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_33826.X.s e)) hpb
end sound
def WZ (E : List (ℕ × ℕ)) (Z : ℕ) : Set ℕ := {x | ∃ w ∈ rawL E, x = w &&& mz Z}
def Imp (E : List (ℕ × ℕ)) (Z L : ℕ) : Prop := ∀ q < L, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z))
def PZ (Q : List (ℕ × ℕ)) : List ℕ := Q.map (fun e => mz e.1)
def pOk (Z : ℕ) (Q : List (ℕ × ℕ)) : Bool := !Nat.beq (tz Z) 0 && !Nat.beq (tz Z) (mz Z) && Q.all (fun e => Nat.beq (Nat.land (mz e.1) (mz Z)) (mz e.1) &&
  !Nat.beq (tz e.1) 0 && !Nat.beq (tz e.1) (mz e.1))
def pwr (E : List (ℕ × ℕ)) (Z : ℕ) : ℕ := (E.map fun e => Nat.land (xw e) (mz Z)).headD 0
noncomputable def chk (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startv l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
lemma tz_sub {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') : tz Z &&& mz Z' = tz Z' := by
  simp only [tz, nl, Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]
lemma Im_WZ {E : List (ℕ × ℕ)} {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ WZ E Z) : Im (mz Z') S ⊆ WZ E Z' := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hS hy
  exact ⟨w, hw, by simp only [Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]⟩
lemma sumc_eq {P : List ℕ} {v : List W} (hw : ∀ w ∈ v, WOk P w) : sumc v = pk P.length (cnt v) := by
  induction v with
  | nil => simp [sumc, pk, cnt]
  | cons w v ih =>
    change w.c + sumc v = _
    rw [ih fun x hx => hw x (by simp [hx]), fl_pk (hw w (by simp)), pk_add]
    exact pk_congr fun j _ => by rw [cnt_cons]
lemma pk16 (Q : List (ℕ × ℕ)) (K : ℕ) : pL (Q.map fun e => 16 + (K - e.2)) = pk (PZ Q).length (fun j => 16 + (K - (Q.getD j (0, K)).2)) := by
  rw [pL_pk, PZ, List.length_map, List.length_map]
  refine pk_congr fun j hj => ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
open Classical in
noncomputable def RZ (E : List (ℕ × ℕ)) (Z : ℕ) : ℕ → ℕ := fun s => if s ∈ WZ E Z then 3 else 0
lemma RZ_set (E : List (ℕ × ℕ)) (Z : ℕ) : {x | RZ E Z x ≠ 0} = WZ E Z := by
  ext x; simp only [RZ, Set.mem_setOf_eq]; split_ifs with h <;> simp [h]
lemma RZ_R (E : List (ℕ × ℕ)) (Z : ℕ) : RR (RZ E Z) := by
  intro d a b ha hb h
  have h3 : ∀ x, RZ E Z x ≠ 0 → RZ E Z x = 3 := by
    intro x hx; unfold RZ at hx ⊢; split_ifs at hx ⊢ with h
    · rfl
    · simp at hx
  unfold Al at h
  rw [h3 a ha, h3 b hb] at h
  cases d <;> simp at h
lemma RZ_R2 (E : List (ℕ × ℕ)) (Z : ℕ) : ∀ d a b, (RZ E Z a = 0 ∨ RZ E Z b = 0) → Al (RZ E Z) d a b := by
  intro d a b h
  unfold Al
  rcases h with h | h <;> rw [h] <;> simp
lemma hasP_ok {p : ℕ} {v : List W} (h : p = 0 ∨ ∃ w ∈ v, w.s = p) : hasP p v = true := by
  unfold hasP
  rw [bR]
  rcases h with rfl | ⟨w, hw, rfl⟩
  · rfl
  · have : (List.rec (motive := fun _ => Bool) false (fun w' _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w'.s w.s)) v : Bool) = true := by
      induction v with
      | nil => simp at hw
      | cons x v ih =>
        change (Bool.rec (motive := fun _ => Bool) (List.rec (motive := fun _ => Bool) false (fun w' _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w'.s w.s)) v : Bool) true (Nat.beq x.s w.s) : Bool) = true
        rw [bR]
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · rw [Nat.beq_refl]; rfl
        · rw [ih hw]; cases Nat.beq x.s w.s <;> rfl
    rw [this]; cases Nat.beq w.s 0 <;> rfl
lemma rawL_sub {E : List (ℕ × ℕ)} (hE : ∀ e ∈ E, e ∈ six) {w : ℕ} (hw : w ∈ rawL E) : w ∈ rawG := by
  simp only [rawG, rawL, List.mem_append, List.mem_map] at hw ⊢
  rcases hw with h | ⟨e, he, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, hE e he, rfl⟩
lemma imp_of_live {E Q : List (ℕ × ℕ)} {Z L k t : ℕ} {S : Finset ℕ}
    (hE : E = [] ∨ ∃ e ∈ six, E = [e] ∧ Imp [] Z L) (hp : pOk Z Q = true) (hL : L ≤ 15)
    (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hk : k < L) (hS : (S : Set ℕ) ⊆ C (mz Z) (WZ E Z)) (hl : Live Z0 (mz Z) (tz Z) k t S)
    (hmin : ∀ q < k, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)))
    (hb : (∃ e ∈ Q, L ≤ e.2) ∨ ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q Z (L - 1) t p.1 p.2 = false) : False := by
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE6 : ∀ e ∈ E, e ∈ six := by
    rcases hE with rfl | ⟨e, he, rfl, _⟩
    · simp
    · intro e' he'; simp only [List.mem_singleton] at he'; rw [he']; exact he
  classical
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => hmin q' hq' (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno e he q' (by omega) hs'
  have hpw : pwr E Z = 0 ∨ pwr E Z ∈ S := by
    rcases hE with rfl | ⟨e, he, rfl, hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k (by omega) (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      simp only [rawL, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
      · have hx : xw e &&& mz Z ∈ S := by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨M, hMf, hchk⟩ := hb
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Q) (mz Z) (rawL E)
  set v := (avl (PZ Q) (mz Z) (rawL E)).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Q) (mz Z) (rawL E)) := List.filter_sublist
  have hnd : (v.map W.s).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hv, List.mem_filter] at hw; simpa using hw.2
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
      exact ⟨w', by rw [hv, List.mem_filter]; exact ⟨hw', by simpa [e] using hx⟩, e⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _
  have hcod : ∀ w ∈ v, w.r = RZ E Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw)
    have : x &&& mz Z ∈ WZ E Z := ⟨x, hx, rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ, if_pos this]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good (rawL_sub hE6 hx) Z
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, L - 1)).1 ∧ Q.getD j (0, L - 1) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hcl : Cl (PZ Q) (tz Z) (L - 1) (fun j => L - 1 - (Q.getD j (0, L - 1)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    have hq' : q + (L - 1 - (Q.getD j (0, L - 1)).2) < L - 1 := hq
    rw [e1]; exact hno _ e2 q (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
    refine ⟨hrep, hwok, hgood, _, fun j _ => by omega, hcl, ?_⟩
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, pos_eq, hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true := Nat.ble_eq_true_of_le (by
    change v.length ≤ L - 1 + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topC_sound X (RZ_R E Z) (RZ_R2 E Z) hMf all hst hcod (by omega) hl ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine hmin q hq (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx
lemma imp_of {E Q : List (ℕ × ℕ)} {Z L : ℕ} (hE : E = [] ∨ ∃ e ∈ six, E = [e] ∧ Imp [] Z L) (hp : pOk Z Q = true) (hL : L ≤ 15) (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hb : (∃ e ∈ Q, L ≤ e.2) ∨ ∀ t < L, ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q Z (L - 1) t p.1 p.2 = false) : Imp E Z L := by
  intro q hq hsol
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE6 : ∀ e ∈ E, e ∈ six := by
    rcases hE with rfl | ⟨e, he, rfl, _⟩
    · simp
    · intro e' he'; simp only [List.mem_singleton] at he'; rw [he']; exact he
  classical
  have hex : ∃ q, Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)) := ⟨q, hsol⟩
  have hqL : Nat.find hex < L := lt_of_le_of_lt (Nat.find_min' hex hsol) hq
  obtain ⟨k, hk, t, S, hS, hl⟩ := (Nat.find_spec hex).live
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hkeq : k = Nat.find hex := le_antisymm hk (Nat.find_min' hex (hl.sol.mono le_rfl hS))
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => Nat.find_min hex (by omega) (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno e he q' (by omega) hs'
  have hpw : pwr E Z = 0 ∨ pwr E Z ∈ S := by
    rcases hE with rfl | ⟨e, he, rfl, hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k (by omega) (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      simp only [rawL, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
      · have hx : xw e &&& mz Z ∈ S := by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨M, hMf, hchk⟩ := hb t (by omega)
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Q) (mz Z) (rawL E)
  set v := (avl (PZ Q) (mz Z) (rawL E)).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Q) (mz Z) (rawL E)) := List.filter_sublist
  have hnd : (v.map W.s).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hv, List.mem_filter] at hw; simpa using hw.2
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
      exact ⟨w', by rw [hv, List.mem_filter]; exact ⟨hw', by simpa [e] using hx⟩, e⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _
  have hcod : ∀ w ∈ v, w.r = RZ E Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw)
    have : x &&& mz Z ∈ WZ E Z := ⟨x, hx, rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ, if_pos this]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good (rawL_sub hE6 hx) Z
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, L - 1)).1 ∧ Q.getD j (0, L - 1) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hcl : Cl (PZ Q) (tz Z) (L - 1) (fun j => L - 1 - (Q.getD j (0, L - 1)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    have hq' : q + (L - 1 - (Q.getD j (0, L - 1)).2) < L - 1 := hq
    rw [e1]; exact hno _ e2 q (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
    refine ⟨hrep, hwok, hgood, _, fun j _ => by omega, hcl, ?_⟩
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, pos_eq, hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true := Nat.ble_eq_true_of_le (by
    change v.length ≤ L - 1 + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topC_sound X (RZ_R E Z) (RZ_R2 E Z) hMf all hst hcod (by omega) hl ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine Nat.find_min hex (show q < Nat.find hex by omega) (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx
def FF : ℕ := 2 ^ MM - 1
lemma ffull : mFull [(FF, 1)] = true := by decide +kernel
noncomputable def okT (E Q : List (ℕ × ℕ)) (Z L : ℕ) (ts : List ℕ) : Bool := ts.all (fun t => !chk E Q Z (L - 1) t FF 1)
noncomputable def okE (E Q : List (ℕ × ℕ)) (e : ℕ × ℕ) : Bool := pOk e.1 Q && Nat.ble e.2 15 && (Q.any (fun x => Nat.ble e.2 x.2) || okT E Q e.1 e.2 (List.range e.2))
lemma okE_of_checks {E Q : List (ℕ × ℕ)} {Z L : ℕ}
    (hp : pOk Z Q = true) (hL : Nat.ble L 15 = true)
    (hc : ∀ t < L, chk E Q Z (L - 1) t FF 1 = false) :
    okE E Q (Z, L) = true := by
  simp only [okE, Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨⟨hp, hL⟩, Or.inr ?_⟩
  simp only [okT, List.all_eq_true, List.mem_range, Bool.not_eq_true']
  exact hc
lemma imp_okE {E Q : List (ℕ × ℕ)} {e : ℕ × ℕ} (hE : E = [] ∨ ∃ e' ∈ six, E = [e'] ∧ Imp [] e.1 e.2) (h : okE E Q e = true) (hI : ∀ e' ∈ Q, Imp E e'.1 e'.2) : Imp E e.1 e.2 := by
  simp only [okE, okT, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  refine imp_of hE h.1.1 (Nat.le_of_ble_eq_true h.1.2) hI (h.2.imp (fun ⟨x, hx, hx2⟩ => ⟨x, hx, Nat.le_of_ble_eq_true hx2⟩) fun h t ht =>
    ⟨[(FF, 1)], ffull, fun p hp => ?_⟩)
  simp only [List.mem_singleton] at hp; subst hp; exact h t ht
def rt3 : List (ℕ × ℕ) := [(7, 5), (11, 6), (13, 6), (14, 5), (19, 7), (21, 6), (22, 7), (25, 6), (26, 7), (28, 7), (35, 7), (37, 7), (38, 7), (41, 6), (42, 7), (44, 7), (49, 5), (50, 7), (52, 7), (56, 5), (67, 7), (69, 7), (70, 7), (73, 7), (74, 7), (76, 6), (81, 6), (82, 7), (84, 7), (88, 6), (97, 5), (98, 7), (100, 7), (104, 6), (112, 5), (131, 5), (133, 5), (134, 6), (137, 5), (138, 5), (140, 5), (145, 5), (146, 7), (148, 6), (152, 5), (161, 5), (162, 7), (164, 7), (168, 5), (176, 5), (193, 5), (194, 7), (196, 6), (200, 5), (208, 5), (224, 5)]
def rt2 : List (ℕ × ℕ) := [(3, 9), (5, 9), (6, 9), (9, 8), (10, 9), (12, 8), (17, 9), (18, 10), (20, 10), (24, 9), (33, 8), (34, 10), (36, 10), (40, 8), (48, 8), (65, 9), (66, 10), (68, 9), (72, 8), (80, 9), (96, 8), (129, 7), (130, 9), (132, 9), (136, 7), (144, 8), (160, 8), (192, 8)]
def rt1 : List (ℕ × ℕ) := [(1, 11), (2, 13), (4, 12), (8, 11), (16, 12), (32, 11), (64, 11), (128, 11)]
def pr (T : List (ℕ × ℕ)) (Z : ℕ) : List (ℕ × ℕ) := T.filter (fun e => Nat.beq (Nat.land Z e.1) Z && !Nat.beq Z e.1)
def rt : List (ℕ × ℕ) := rt1 ++ rt2 ++ rt3
lemma okAll {T U : List (ℕ × ℕ)} (h : U.all (fun e => okE [] (pr T e.1) e) = true)
    (hT : ∀ e ∈ T, Imp [] e.1 e.2) : ∀ e ∈ U, Imp [] e.1 e.2 := fun e he => imp_okE
  (Or.inl rfl) (List.all_eq_true.1 h e he) (fun e' h' => hT e' (List.mem_of_mem_filter h'))
lemma apI {E A B : List (ℕ × ℕ)} (ha : ∀ e ∈ A, Imp E e.1 e.2) (hb : ∀ e ∈ B, Imp E e.1 e.2) : ∀ e ∈ A ++ B, Imp E e.1 e.2 := fun e he =>
  (List.mem_append.1 he).elim (ha e) (hb e)
lemma imp_ts {E Q : List (ℕ × ℕ)} {L : ℕ} (hE : E = [] ∨ ∃ p ∈ six, E = [p] ∧ Imp [] 0 L) (hp : pOk 0 Q = true) (hL : L ≤ 15) (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (h : ∀ t < L, ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q 0 (L - 1) t p.1 p.2 = false) : Imp E 0 L :=
  imp_of hE hp hL hI (Or.inr h)
lemma one {E Q : List (ℕ × ℕ)} {K t : ℕ} (h : chk E Q 0 K t FF 1 = false) : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q 0 K t p.1 p.2 = false :=
  ⟨[(FF, 1)], ffull, fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact h⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_7 : okE [] (pr [] 7) (7, 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_11 : okE [] (pr [] 11) (11, 6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_13 : okE [] (pr [] 13) (13, 6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_14 : okE [] (pr [] 14) (14, 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_19 : okE [] (pr [] 19) (19, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_21 : okE [] (pr [] 21) (21, 6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_22 : okE [] (pr [] 22) (22, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_25 : okE [] (pr [] 25) (25, 6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_26 : okE [] (pr [] 26) (26, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_28 : okE [] (pr [] 28) (28, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_35 : okE [] (pr [] 35) (35, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_37 : okE [] (pr [] 37) (37, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_38 : okE [] (pr [] 38) (38, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_41 : okE [] (pr [] 41) (41, 6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_42 : okE [] (pr [] 42) (42, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_44 : okE [] (pr [] 44) (44, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_49 : okE [] (pr [] 49) (49, 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_50 : okE [] (pr [] 50) (50, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_52 : okE [] (pr [] 52) (52, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_56 : okE [] (pr [] 56) (56, 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_67 : okE [] (pr [] 67) (67, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_69 : okE [] (pr [] 69) (69, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_70 : okE [] (pr [] 70) (70, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_73 : okE [] (pr [] 73) (73, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_74 : okE [] (pr [] 74) (74, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_76 : okE [] (pr [] 76) (76, 6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_81 : okE [] (pr [] 81) (81, 6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_82 : okE [] (pr [] 82) (82, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_84 : okE [] (pr [] 84) (84, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_88 : okE [] (pr [] 88) (88, 6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_97 : okE [] (pr [] 97) (97, 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_98 : okE [] (pr [] 98) (98, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_100 : okE [] (pr [] 100) (100, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_104 : okE [] (pr [] 104) (104, 6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_112 : okE [] (pr [] 112) (112, 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_131 : okE [] (pr [] 131) (131, 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_133 : okE [] (pr [] 133) (133, 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_134 : okE [] (pr [] 134) (134, 6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_137 : okE [] (pr [] 137) (137, 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_138 : okE [] (pr [] 138) (138, 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_140 : okE [] (pr [] 140) (140, 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_145 : okE [] (pr [] 145) (145, 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_146 : okE [] (pr [] 146) (146, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_148 : okE [] (pr [] 148) (148, 6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_152 : okE [] (pr [] 152) (152, 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_161 : okE [] (pr [] 161) (161, 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_162 : okE [] (pr [] 162) (162, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_164 : okE [] (pr [] 164) (164, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_168 : okE [] (pr [] 168) (168, 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_176 : okE [] (pr [] 176) (176, 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_193 : okE [] (pr [] 193) (193, 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_194 : okE [] (pr [] 194) (194, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_196 : okE [] (pr [] 196) (196, 6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_200 : okE [] (pr [] 200) (200, 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_208 : okE [] (pr [] 208) (208, 5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r3_224 : okE [] (pr [] 224) (224, 5) = true := by decide +kernel
lemma r3 : rt3.all (fun e => okE [] (pr [] e.1) e) = true := by
  apply List.all_eq_true.mpr
  intro e he
  simp only [rt3, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r3_7
  · exact r3_11
  · exact r3_13
  · exact r3_14
  · exact r3_19
  · exact r3_21
  · exact r3_22
  · exact r3_25
  · exact r3_26
  · exact r3_28
  · exact r3_35
  · exact r3_37
  · exact r3_38
  · exact r3_41
  · exact r3_42
  · exact r3_44
  · exact r3_49
  · exact r3_50
  · exact r3_52
  · exact r3_56
  · exact r3_67
  · exact r3_69
  · exact r3_70
  · exact r3_73
  · exact r3_74
  · exact r3_76
  · exact r3_81
  · exact r3_82
  · exact r3_84
  · exact r3_88
  · exact r3_97
  · exact r3_98
  · exact r3_100
  · exact r3_104
  · exact r3_112
  · exact r3_131
  · exact r3_133
  · exact r3_134
  · exact r3_137
  · exact r3_138
  · exact r3_140
  · exact r3_145
  · exact r3_146
  · exact r3_148
  · exact r3_152
  · exact r3_161
  · exact r3_162
  · exact r3_164
  · exact r3_168
  · exact r3_176
  · exact r3_193
  · exact r3_194
  · exact r3_196
  · exact r3_200
  · exact r3_208
  · exact r3_224
lemma i3 : ∀ e ∈ rt3, Imp [] e.1 e.2 := okAll (T := []) r3 (by simp)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_3 : okE [] (pr rt3 3) (3, 9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_5 : okE [] (pr rt3 5) (5, 9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_6 : okE [] (pr rt3 6) (6, 9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_9 : okE [] (pr rt3 9) (9, 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_10 : okE [] (pr rt3 10) (10, 9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_12 : okE [] (pr rt3 12) (12, 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_17 : okE [] (pr rt3 17) (17, 9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_18 : okE [] (pr rt3 18) (18, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_20 : okE [] (pr rt3 20) (20, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_24 : okE [] (pr rt3 24) (24, 9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_33 : okE [] (pr rt3 33) (33, 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_34 : okE [] (pr rt3 34) (34, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_36 : okE [] (pr rt3 36) (36, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_40 : okE [] (pr rt3 40) (40, 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_48 : okE [] (pr rt3 48) (48, 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_65 : okE [] (pr rt3 65) (65, 9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_66 : okE [] (pr rt3 66) (66, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_68 : okE [] (pr rt3 68) (68, 9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_72 : okE [] (pr rt3 72) (72, 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_80 : okE [] (pr rt3 80) (80, 9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_96 : okE [] (pr rt3 96) (96, 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_129 : okE [] (pr rt3 129) (129, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_130 : okE [] (pr rt3 130) (130, 9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_132 : okE [] (pr rt3 132) (132, 9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_136 : okE [] (pr rt3 136) (136, 7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_144 : okE [] (pr rt3 144) (144, 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_160 : okE [] (pr rt3 160) (160, 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r2_192 : okE [] (pr rt3 192) (192, 8) = true := by decide +kernel
lemma r2 : rt2.all (fun e => okE [] (pr rt3 e.1) e) = true := by
  apply List.all_eq_true.mpr
  intro e he
  simp only [rt2, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r2_3
  · exact r2_5
  · exact r2_6
  · exact r2_9
  · exact r2_10
  · exact r2_12
  · exact r2_17
  · exact r2_18
  · exact r2_20
  · exact r2_24
  · exact r2_33
  · exact r2_34
  · exact r2_36
  · exact r2_40
  · exact r2_48
  · exact r2_65
  · exact r2_66
  · exact r2_68
  · exact r2_72
  · exact r2_80
  · exact r2_96
  · exact r2_129
  · exact r2_130
  · exact r2_132
  · exact r2_136
  · exact r2_144
  · exact r2_160
  · exact r2_192
lemma i2 : ∀ e ∈ rt2, Imp [] e.1 e.2 := okAll r2 i3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_1_t0 : chk [] (pr (rt2 ++ rt3) 1) 1 10 0 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_1_t1 : chk [] (pr (rt2 ++ rt3) 1) 1 10 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_1_t2 : chk [] (pr (rt2 ++ rt3) 1) 1 10 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_1_t3 : chk [] (pr (rt2 ++ rt3) 1) 1 10 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_1_t4 : chk [] (pr (rt2 ++ rt3) 1) 1 10 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_1_t5 : chk [] (pr (rt2 ++ rt3) 1) 1 10 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_1_t6 : chk [] (pr (rt2 ++ rt3) 1) 1 10 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_1_t7 : chk [] (pr (rt2 ++ rt3) 1) 1 10 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_1_t8 : chk [] (pr (rt2 ++ rt3) 1) 1 10 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_1_t9 : chk [] (pr (rt2 ++ rt3) 1) 1 10 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_1_t10 : chk [] (pr (rt2 ++ rt3) 1) 1 10 10 FF 1 = false := by decide +kernel
lemma r1_1 : okE [] (pr (rt2 ++ rt3) 1) (1, 11) = true := by
  refine okE_of_checks (E := []) (Q := pr (rt2 ++ rt3) 1)
    (Z := 1) (L := 11) (by decide +kernel) (by decide +kernel) ?_
  intro t ht
  interval_cases t
  · exact r1_1_t0
  · exact r1_1_t1
  · exact r1_1_t2
  · exact r1_1_t3
  · exact r1_1_t4
  · exact r1_1_t5
  · exact r1_1_t6
  · exact r1_1_t7
  · exact r1_1_t8
  · exact r1_1_t9
  · exact r1_1_t10
lemma oneZ {E Q : List (ℕ × ℕ)} {Z K t : ℕ}
    (h : chk E Q Z K t FF 1 = false) :
    ∃ M : List (ℕ × ℕ), mFull M = true ∧
      ∀ p ∈ M, chk E Q Z K t p.1 p.2 = false := by
  refine ⟨[(FF, 1)], ffull, ?_⟩
  intro p hp
  have hp' : p = (FF, 1) := List.mem_singleton.mp hp
  subst p
  exact h
def r1Z2Parts : List (ℕ × ℕ) := [(0, 1), (64, 0), (1024, 0), (4194304, 0), (67108864, 0), (0x10000000000, 0), (0x40000000000, 0), (0x400000000000000000, 0), (0x4000000000000000000000, 0), (0x4000000000000000000000000, 0), (0x400000000000000000000000000, 0), (0x400000000000000000000000000000, 0), (0x100000000000000000000000000000000, 0), (0x400000000000000000000000000000000000, 0), (0x1000000000000000000000000000000000000, 0), (0x4000000000000000000000000000000000000000, 0), (0x100000000000000000000000000000000000000000, 0), (0x100000000000000000000000000000000000000000000, 0), (0x400000000000000000000000000000000000000000000, 0), (0x100000000000000000000000000000000000000000000000, 0), (0x400000000000000000000000000000000000000000000000, 0), (0x10000000000000000000000000000000000000000000000000000, 0), (0x3effffaffaffefbffebffeffbffbfbffbfffbffffffafffbbffbbf, 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2Parts_full : mFull r1Z2Parts = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_p : pOk 2 (pr (rt2 ++ rt3) 2) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_phase1 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r6 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 64 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r10 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 1024 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r22 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 4194304 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r26 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 67108864 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r40 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 0x10000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r42 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 0x40000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r70 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 0x400000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r86 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 0x4000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r98 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 0x4000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r106 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 0x400000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r118 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 0x400000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r128 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 0x100000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r142 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 0x400000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r144 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 0x1000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r158 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 0x4000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r164 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 0x100000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r176 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 0x100000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r178 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 0x400000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r188 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 0x100000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r190 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 0x400000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_r208 : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 0x10000000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t0_rest : chk [] (pr (rt2 ++ rt3) 2) 2 12 0 0x3effffaffaffefbffebffeffbffbfbffbfffbffffffafffbbffbbf 0 = false := by decide +kernel
lemma r1Z2_t0_parts : ∀ p ∈ r1Z2Parts, chk [] (pr (rt2 ++ rt3) 2) 2 12 0 p.1 p.2 = false := by
  intro p hp
  simp only [r1Z2Parts, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r1Z2_t0_phase1
  · exact r1Z2_t0_r6
  · exact r1Z2_t0_r10
  · exact r1Z2_t0_r22
  · exact r1Z2_t0_r26
  · exact r1Z2_t0_r40
  · exact r1Z2_t0_r42
  · exact r1Z2_t0_r70
  · exact r1Z2_t0_r86
  · exact r1Z2_t0_r98
  · exact r1Z2_t0_r106
  · exact r1Z2_t0_r118
  · exact r1Z2_t0_r128
  · exact r1Z2_t0_r142
  · exact r1Z2_t0_r144
  · exact r1Z2_t0_r158
  · exact r1Z2_t0_r164
  · exact r1Z2_t0_r176
  · exact r1Z2_t0_r178
  · exact r1Z2_t0_r188
  · exact r1Z2_t0_r190
  · exact r1Z2_t0_r208
  · exact r1Z2_t0_rest
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_phase1 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r6 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 64 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r10 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 1024 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r22 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 4194304 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r26 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 67108864 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r40 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 0x10000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r42 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 0x40000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r70 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 0x400000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r86 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 0x4000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r98 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 0x4000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r106 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 0x400000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r118 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 0x400000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r128 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 0x100000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r142 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 0x400000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r144 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 0x1000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r158 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 0x4000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r164 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 0x100000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r176 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 0x100000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r178 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 0x400000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r188 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 0x100000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r190 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 0x400000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_r208 : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 0x10000000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t1_rest : chk [] (pr (rt2 ++ rt3) 2) 2 12 1 0x3effffaffaffefbffebffeffbffbfbffbfffbffffffafffbbffbbf 0 = false := by decide +kernel
lemma r1Z2_t1_parts : ∀ p ∈ r1Z2Parts, chk [] (pr (rt2 ++ rt3) 2) 2 12 1 p.1 p.2 = false := by
  intro p hp
  simp only [r1Z2Parts, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r1Z2_t1_phase1
  · exact r1Z2_t1_r6
  · exact r1Z2_t1_r10
  · exact r1Z2_t1_r22
  · exact r1Z2_t1_r26
  · exact r1Z2_t1_r40
  · exact r1Z2_t1_r42
  · exact r1Z2_t1_r70
  · exact r1Z2_t1_r86
  · exact r1Z2_t1_r98
  · exact r1Z2_t1_r106
  · exact r1Z2_t1_r118
  · exact r1Z2_t1_r128
  · exact r1Z2_t1_r142
  · exact r1Z2_t1_r144
  · exact r1Z2_t1_r158
  · exact r1Z2_t1_r164
  · exact r1Z2_t1_r176
  · exact r1Z2_t1_r178
  · exact r1Z2_t1_r188
  · exact r1Z2_t1_r190
  · exact r1Z2_t1_r208
  · exact r1Z2_t1_rest
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_phase1 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r6 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 64 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r10 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 1024 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r22 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 4194304 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r26 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 67108864 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r40 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 0x10000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r42 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 0x40000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r70 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 0x400000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r86 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 0x4000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r98 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 0x4000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r106 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 0x400000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r118 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 0x400000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r128 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 0x100000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r142 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 0x400000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r144 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 0x1000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r158 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 0x4000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r164 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 0x100000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r176 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 0x100000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r178 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 0x400000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r188 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 0x100000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r190 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 0x400000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_r208 : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 0x10000000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t2_rest : chk [] (pr (rt2 ++ rt3) 2) 2 12 2 0x3effffaffaffefbffebffeffbffbfbffbfffbffffffafffbbffbbf 0 = false := by decide +kernel
lemma r1Z2_t2_parts : ∀ p ∈ r1Z2Parts, chk [] (pr (rt2 ++ rt3) 2) 2 12 2 p.1 p.2 = false := by
  intro p hp
  simp only [r1Z2Parts, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r1Z2_t2_phase1
  · exact r1Z2_t2_r6
  · exact r1Z2_t2_r10
  · exact r1Z2_t2_r22
  · exact r1Z2_t2_r26
  · exact r1Z2_t2_r40
  · exact r1Z2_t2_r42
  · exact r1Z2_t2_r70
  · exact r1Z2_t2_r86
  · exact r1Z2_t2_r98
  · exact r1Z2_t2_r106
  · exact r1Z2_t2_r118
  · exact r1Z2_t2_r128
  · exact r1Z2_t2_r142
  · exact r1Z2_t2_r144
  · exact r1Z2_t2_r158
  · exact r1Z2_t2_r164
  · exact r1Z2_t2_r176
  · exact r1Z2_t2_r178
  · exact r1Z2_t2_r188
  · exact r1Z2_t2_r190
  · exact r1Z2_t2_r208
  · exact r1Z2_t2_rest
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_phase1 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r6 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 64 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r10 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 1024 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r22 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 4194304 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r26 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 67108864 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r40 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 0x10000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r42 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 0x40000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r70 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 0x400000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r86 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 0x4000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r98 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 0x4000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r106 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 0x400000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r118 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 0x400000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r128 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 0x100000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r142 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 0x400000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r144 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 0x1000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r158 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 0x4000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r164 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 0x100000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r176 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 0x100000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r178 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 0x400000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r188 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 0x100000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r190 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 0x400000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_r208 : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 0x10000000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1Z2_t3_rest : chk [] (pr (rt2 ++ rt3) 2) 2 12 3 0x3effffaffaffefbffebffeffbffbfbffbfffbffffffafffbbffbbf 0 = false := by decide +kernel
lemma r1Z2_t3_parts : ∀ p ∈ r1Z2Parts, chk [] (pr (rt2 ++ rt3) 2) 2 12 3 p.1 p.2 = false := by
  intro p hp
  simp only [r1Z2Parts, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r1Z2_t3_phase1
  · exact r1Z2_t3_r6
  · exact r1Z2_t3_r10
  · exact r1Z2_t3_r22
  · exact r1Z2_t3_r26
  · exact r1Z2_t3_r40
  · exact r1Z2_t3_r42
  · exact r1Z2_t3_r70
  · exact r1Z2_t3_r86
  · exact r1Z2_t3_r98
  · exact r1Z2_t3_r106
  · exact r1Z2_t3_r118
  · exact r1Z2_t3_r128
  · exact r1Z2_t3_r142
  · exact r1Z2_t3_r144
  · exact r1Z2_t3_r158
  · exact r1Z2_t3_r164
  · exact r1Z2_t3_r176
  · exact r1Z2_t3_r178
  · exact r1Z2_t3_r188
  · exact r1Z2_t3_r190
  · exact r1Z2_t3_r208
  · exact r1Z2_t3_rest
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_2_t4 : chk [] (pr (rt2 ++ rt3) 2) 2 12 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_2_t5 : chk [] (pr (rt2 ++ rt3) 2) 2 12 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_2_t6 : chk [] (pr (rt2 ++ rt3) 2) 2 12 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_2_t7 : chk [] (pr (rt2 ++ rt3) 2) 2 12 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_2_t8 : chk [] (pr (rt2 ++ rt3) 2) 2 12 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_2_t9 : chk [] (pr (rt2 ++ rt3) 2) 2 12 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_2_t10 : chk [] (pr (rt2 ++ rt3) 2) 2 12 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_2_t11 : chk [] (pr (rt2 ++ rt3) 2) 2 12 11 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_2_t12 : chk [] (pr (rt2 ++ rt3) 2) 2 12 12 FF 1 = false := by decide +kernel
lemma i1_two : Imp [] 2 13 := by
  have hI : ∀ e ∈ pr (rt2 ++ rt3) 2, Imp [] e.1 e.2 := by
    intro e he
    unfold pr at he
    exact (apI i2 i3) e (List.mem_of_mem_filter he)
  refine imp_of (E := []) (Q := pr (rt2 ++ rt3) 2) (Z := 2) (L := 13)
    (Or.inl rfl) r1Z2_p (by norm_num) hI (Or.inr ?_)
  intro t ht
  interval_cases t
  · exact ⟨r1Z2Parts, r1Z2Parts_full, r1Z2_t0_parts⟩
  · exact ⟨r1Z2Parts, r1Z2Parts_full, r1Z2_t1_parts⟩
  · exact ⟨r1Z2Parts, r1Z2Parts_full, r1Z2_t2_parts⟩
  · exact ⟨r1Z2Parts, r1Z2Parts_full, r1Z2_t3_parts⟩
  · exact oneZ r1_2_t4
  · exact oneZ r1_2_t5
  · exact oneZ r1_2_t6
  · exact oneZ r1_2_t7
  · exact oneZ r1_2_t8
  · exact oneZ r1_2_t9
  · exact oneZ r1_2_t10
  · exact oneZ r1_2_t11
  · exact oneZ r1_2_t12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_4_t0 : chk [] (pr (rt2 ++ rt3) 4) 4 11 0 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_4_t1 : chk [] (pr (rt2 ++ rt3) 4) 4 11 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_4_t2 : chk [] (pr (rt2 ++ rt3) 4) 4 11 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_4_t3 : chk [] (pr (rt2 ++ rt3) 4) 4 11 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_4_t4 : chk [] (pr (rt2 ++ rt3) 4) 4 11 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_4_t5 : chk [] (pr (rt2 ++ rt3) 4) 4 11 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_4_t6 : chk [] (pr (rt2 ++ rt3) 4) 4 11 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_4_t7 : chk [] (pr (rt2 ++ rt3) 4) 4 11 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_4_t8 : chk [] (pr (rt2 ++ rt3) 4) 4 11 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_4_t9 : chk [] (pr (rt2 ++ rt3) 4) 4 11 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_4_t10 : chk [] (pr (rt2 ++ rt3) 4) 4 11 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_4_t11 : chk [] (pr (rt2 ++ rt3) 4) 4 11 11 FF 1 = false := by decide +kernel
lemma r1_4 : okE [] (pr (rt2 ++ rt3) 4) (4, 12) = true := by
  refine okE_of_checks (E := []) (Q := pr (rt2 ++ rt3) 4)
    (Z := 4) (L := 12) (by decide +kernel) (by decide +kernel) ?_
  intro t ht
  interval_cases t
  · exact r1_4_t0
  · exact r1_4_t1
  · exact r1_4_t2
  · exact r1_4_t3
  · exact r1_4_t4
  · exact r1_4_t5
  · exact r1_4_t6
  · exact r1_4_t7
  · exact r1_4_t8
  · exact r1_4_t9
  · exact r1_4_t10
  · exact r1_4_t11
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_8_t0 : chk [] (pr (rt2 ++ rt3) 8) 8 10 0 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_8_t1 : chk [] (pr (rt2 ++ rt3) 8) 8 10 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_8_t2 : chk [] (pr (rt2 ++ rt3) 8) 8 10 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_8_t3 : chk [] (pr (rt2 ++ rt3) 8) 8 10 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_8_t4 : chk [] (pr (rt2 ++ rt3) 8) 8 10 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_8_t5 : chk [] (pr (rt2 ++ rt3) 8) 8 10 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_8_t6 : chk [] (pr (rt2 ++ rt3) 8) 8 10 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_8_t7 : chk [] (pr (rt2 ++ rt3) 8) 8 10 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_8_t8 : chk [] (pr (rt2 ++ rt3) 8) 8 10 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_8_t9 : chk [] (pr (rt2 ++ rt3) 8) 8 10 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_8_t10 : chk [] (pr (rt2 ++ rt3) 8) 8 10 10 FF 1 = false := by decide +kernel
lemma r1_8 : okE [] (pr (rt2 ++ rt3) 8) (8, 11) = true := by
  refine okE_of_checks (E := []) (Q := pr (rt2 ++ rt3) 8)
    (Z := 8) (L := 11) (by decide +kernel) (by decide +kernel) ?_
  intro t ht
  interval_cases t
  · exact r1_8_t0
  · exact r1_8_t1
  · exact r1_8_t2
  · exact r1_8_t3
  · exact r1_8_t4
  · exact r1_8_t5
  · exact r1_8_t6
  · exact r1_8_t7
  · exact r1_8_t8
  · exact r1_8_t9
  · exact r1_8_t10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_16_t0 : chk [] (pr (rt2 ++ rt3) 16) 16 11 0 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_16_t1 : chk [] (pr (rt2 ++ rt3) 16) 16 11 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_16_t2 : chk [] (pr (rt2 ++ rt3) 16) 16 11 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_16_t3 : chk [] (pr (rt2 ++ rt3) 16) 16 11 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_16_t4 : chk [] (pr (rt2 ++ rt3) 16) 16 11 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_16_t5 : chk [] (pr (rt2 ++ rt3) 16) 16 11 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_16_t6 : chk [] (pr (rt2 ++ rt3) 16) 16 11 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_16_t7 : chk [] (pr (rt2 ++ rt3) 16) 16 11 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_16_t8 : chk [] (pr (rt2 ++ rt3) 16) 16 11 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_16_t9 : chk [] (pr (rt2 ++ rt3) 16) 16 11 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_16_t10 : chk [] (pr (rt2 ++ rt3) 16) 16 11 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_16_t11 : chk [] (pr (rt2 ++ rt3) 16) 16 11 11 FF 1 = false := by decide +kernel
lemma r1_16 : okE [] (pr (rt2 ++ rt3) 16) (16, 12) = true := by
  refine okE_of_checks (E := []) (Q := pr (rt2 ++ rt3) 16)
    (Z := 16) (L := 12) (by decide +kernel) (by decide +kernel) ?_
  intro t ht
  interval_cases t
  · exact r1_16_t0
  · exact r1_16_t1
  · exact r1_16_t2
  · exact r1_16_t3
  · exact r1_16_t4
  · exact r1_16_t5
  · exact r1_16_t6
  · exact r1_16_t7
  · exact r1_16_t8
  · exact r1_16_t9
  · exact r1_16_t10
  · exact r1_16_t11
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_32_t0 : chk [] (pr (rt2 ++ rt3) 32) 32 10 0 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_32_t1 : chk [] (pr (rt2 ++ rt3) 32) 32 10 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_32_t2 : chk [] (pr (rt2 ++ rt3) 32) 32 10 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_32_t3 : chk [] (pr (rt2 ++ rt3) 32) 32 10 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_32_t4 : chk [] (pr (rt2 ++ rt3) 32) 32 10 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_32_t5 : chk [] (pr (rt2 ++ rt3) 32) 32 10 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_32_t6 : chk [] (pr (rt2 ++ rt3) 32) 32 10 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_32_t7 : chk [] (pr (rt2 ++ rt3) 32) 32 10 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_32_t8 : chk [] (pr (rt2 ++ rt3) 32) 32 10 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_32_t9 : chk [] (pr (rt2 ++ rt3) 32) 32 10 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_32_t10 : chk [] (pr (rt2 ++ rt3) 32) 32 10 10 FF 1 = false := by decide +kernel
lemma r1_32 : okE [] (pr (rt2 ++ rt3) 32) (32, 11) = true := by
  refine okE_of_checks (E := []) (Q := pr (rt2 ++ rt3) 32)
    (Z := 32) (L := 11) (by decide +kernel) (by decide +kernel) ?_
  intro t ht
  interval_cases t
  · exact r1_32_t0
  · exact r1_32_t1
  · exact r1_32_t2
  · exact r1_32_t3
  · exact r1_32_t4
  · exact r1_32_t5
  · exact r1_32_t6
  · exact r1_32_t7
  · exact r1_32_t8
  · exact r1_32_t9
  · exact r1_32_t10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_64_t0 : chk [] (pr (rt2 ++ rt3) 64) 64 10 0 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_64_t1 : chk [] (pr (rt2 ++ rt3) 64) 64 10 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_64_t2 : chk [] (pr (rt2 ++ rt3) 64) 64 10 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_64_t3 : chk [] (pr (rt2 ++ rt3) 64) 64 10 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_64_t4 : chk [] (pr (rt2 ++ rt3) 64) 64 10 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_64_t5 : chk [] (pr (rt2 ++ rt3) 64) 64 10 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_64_t6 : chk [] (pr (rt2 ++ rt3) 64) 64 10 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_64_t7 : chk [] (pr (rt2 ++ rt3) 64) 64 10 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_64_t8 : chk [] (pr (rt2 ++ rt3) 64) 64 10 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_64_t9 : chk [] (pr (rt2 ++ rt3) 64) 64 10 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_64_t10 : chk [] (pr (rt2 ++ rt3) 64) 64 10 10 FF 1 = false := by decide +kernel
lemma r1_64 : okE [] (pr (rt2 ++ rt3) 64) (64, 11) = true := by
  refine okE_of_checks (E := []) (Q := pr (rt2 ++ rt3) 64)
    (Z := 64) (L := 11) (by decide +kernel) (by decide +kernel) ?_
  intro t ht
  interval_cases t
  · exact r1_64_t0
  · exact r1_64_t1
  · exact r1_64_t2
  · exact r1_64_t3
  · exact r1_64_t4
  · exact r1_64_t5
  · exact r1_64_t6
  · exact r1_64_t7
  · exact r1_64_t8
  · exact r1_64_t9
  · exact r1_64_t10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_128_t0 : chk [] (pr (rt2 ++ rt3) 128) 128 10 0 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_128_t1 : chk [] (pr (rt2 ++ rt3) 128) 128 10 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_128_t2 : chk [] (pr (rt2 ++ rt3) 128) 128 10 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_128_t3 : chk [] (pr (rt2 ++ rt3) 128) 128 10 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_128_t4 : chk [] (pr (rt2 ++ rt3) 128) 128 10 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_128_t5 : chk [] (pr (rt2 ++ rt3) 128) 128 10 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_128_t6 : chk [] (pr (rt2 ++ rt3) 128) 128 10 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_128_t7 : chk [] (pr (rt2 ++ rt3) 128) 128 10 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_128_t8 : chk [] (pr (rt2 ++ rt3) 128) 128 10 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_128_t9 : chk [] (pr (rt2 ++ rt3) 128) 128 10 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def r1_128_t10 : chk [] (pr (rt2 ++ rt3) 128) 128 10 10 FF 1 = false := by decide +kernel
lemma r1_128 : okE [] (pr (rt2 ++ rt3) 128) (128, 11) = true := by
  refine okE_of_checks (E := []) (Q := pr (rt2 ++ rt3) 128)
    (Z := 128) (L := 11) (by decide +kernel) (by decide +kernel) ?_
  intro t ht
  interval_cases t
  · exact r1_128_t0
  · exact r1_128_t1
  · exact r1_128_t2
  · exact r1_128_t3
  · exact r1_128_t4
  · exact r1_128_t5
  · exact r1_128_t6
  · exact r1_128_t7
  · exact r1_128_t8
  · exact r1_128_t9
  · exact r1_128_t10
lemma i1 : ∀ e ∈ rt1, Imp [] e.1 e.2 := by
  have hI : ∀ (Z : ℕ) (e : ℕ × ℕ), e ∈ pr (rt2 ++ rt3) Z → Imp [] e.1 e.2 := by
    intro Z e he
    unfold pr at he
    exact (apI i2 i3) e (List.mem_of_mem_filter he)
  intro e he
  simp only [rt1, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact imp_okE (Or.inl rfl) r1_1 (hI 1)
  · exact i1_two
  · exact imp_okE (Or.inl rfl) r1_4 (hI 4)
  · exact imp_okE (Or.inl rfl) r1_8 (hI 8)
  · exact imp_okE (Or.inl rfl) r1_16 (hI 16)
  · exact imp_okE (Or.inl rfl) r1_32 (hI 32)
  · exact imp_okE (Or.inl rfl) r1_64 (hI 64)
  · exact imp_okE (Or.inl rfl) r1_128 (hI 128)
lemma ir : ∀ e ∈ rt, Imp [] e.1 e.2 := apI (apI i1 i2) i3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma root_p : pOk 0 rt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_0 : chk [] rt 0 13 0 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_1 : chk [] rt 0 13 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_2 : chk [] rt 0 13 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_3 : chk [] rt 0 13 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_4 : chk [] rt 0 13 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_5 : chk [] rt 0 13 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_6 : chk [] rt 0 13 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_7 : chk [] rt 0 13 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_8 : chk [] rt 0 13 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_9 : chk [] rt 0 13 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_10 : chk [] rt 0 13 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_11 : chk [] rt 0 13 11 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_12 : chk [] rt 0 13 12 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_13 : chk [] rt 0 13 13 FF 1 = false := by decide +kernel
lemma iroot : Imp [] 0 14 := imp_ts (Or.inl rfl) root_p (by norm_num) ir (fun t ht => by
  interval_cases t
  · exact one root_0
  · exact one root_1
  · exact one root_2
  · exact one root_3
  · exact one root_4
  · exact one root_5
  · exact one root_6
  · exact one root_7
  · exact one root_8
  · exact one root_9
  · exact one root_10
  · exact one root_11
  · exact one root_12
  · exact one root_13
)
noncomputable section hash29Memo
def topF (F : Nat → List W → Bool) (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (node F (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
def startF (F : Nat → List W → Bool) (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topF F l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
def chkF (F : Nat → List W → Bool) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startF F l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
lemma st_apply (n : Nat) (f : Nat → Bool) : st n f = f n := by
  rfl
lemma frc_apply (v : List W) : ∀ h, frc v h = h v := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change st w.s (fun s => st w.a fun a => st w.b fun b => st w.c fun c =>
      frc v fun r => h (⟨s,a,b,c,w.r⟩::r)) = _
    simp only [st_apply, ih]
lemma topC_expand (l m g K H ph k t z : Nat) (v : List W) :
    topC l m g K H ph k t z v =
      topF (look1 l m g K K (k-1) t) l m g K H ph k t z v := by
  rfl
lemma startv_expand (l m g B K t p H ph : Nat) (v : List W) :
    startv l m g B K t p H ph v =
      startF (look1 l m g K K (K-1) t) l m g B K t p H ph v := by
  simp only [startv, startF, child, st_apply, topC_expand]
lemma chk_expand (E Q : List (Nat × Nat)) (Z K t H ph : Nat) :
    chk E Q Z K t H ph =
      chkF (look1 (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K K (K-1) t)
        E Q Z K t H ph := by
  simp only [chk, chkF, frc_apply, st_apply, startv_expand]
def z0 : Nat := 0xa52939529494a949ca94a5274a5ab4a52b4a4eb495252b5294a527494a949d272b4e7494a538c6749d2728d29294a729469394e3184a5194610
def v0 : List W := [⟨0x1fffff7ffffdf00000000000000000000000000000000000000000000000000000000126a847004e002480e00380380000000000300006000c00000060000180180000018006006000030000000000000000003ff800ffe003efc0004107e0000107e00010fc00021f80008200fc00042088210f800b6d5aaffedffd6d55ffd7ff7ff0000000000000000000000000000000000000000000000000000000d6b5295ad6b52b5a, 0x842108421084210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 0x0, 0x842108421084210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 0x3⟩, ⟨0x1fffff00000007ffffbefbffffee000000000000000000000000000000000000000005b4ac04c0098000009802602602aa969580ae0025c04b8000005800016016000001600580580002c000000000000000003f0700801c00083f807df41fe01c001e000003c000007800410803c00210441000700b6d58000000000000000000000555adab557ff56ffedffc0000000000000000000000000000000000639c738c739e718e, 0x842108400000000000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x0, 0x842108400000000000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x3⟩, ⟨0x7ffffc0000000000000000000000007ffffc0fffff7df70000000000000000000200420c6428b68043010c10c00000402a10e002180430402521c0008608616d008a02282284911c0000000000000000080482d7120800224120800610508008c048433388046646fbee0220300200802048200c008000c0016d000000000004040180557ff000000001805affe000000002da00000000000db7fff83e9b0745d1745d, 0x2000001000010000108400000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x0, 0x2000001000010000108400000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x3⟩, ⟨0x7ffffbe00000000fbffffef0000000000000000000000000000000004800110b0014000001400500502aad400000900012002409a881601205805800000500140140000a000000000000000002080e06003820c3c707c02101c01f611fc1e803c001007802084803c01080208880e0b0002affe00000000000000000555ac0000000000000001b55affeb6bffbff80000000000000000005b5b4a6b6b794969, 0x800000021084200000000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 0x0, 0x800000021084200000000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 0x3⟩, ⟨0x7ffff80f8000000f80000007ffffde00000000000000000000000000410010088213000001200480482a800d500088001100220d28011000044044049004c013013000090000000000000000010401c1800710a3c0e01f1080381f10103806223f3c8007810404003c08421044401c860020000dffc000000000000055001ab00000000000001b500000000000002daabffaffeffe00000367267c68e5cecc4, 0x40000020000010842000000004000002108400000000842100000000210842100000000200000008000004000002108400000000000100000, 0x0, 0x40000020000010842000000004000002108400000000842100000000210842100000000200000008000004000002108400000000000100000, 0x3⟩, ⟨0x3ffffe00000000000000000000000007ffff81f07c0f0000000040042008400220888220230000200808412308461080000082414210218004421108408624843000000000000000001082601209820441304143d44c0102014c204049840808e08222516703e0f81e0826000180000000001440010007ff0100c030100046000c0000100000868003ff80288002000ffedb7ff8dadadfe4a5a5433, 0x400000200002000401080000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 0x0, 0x400000200002000401080000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 0x3⟩, ⟨0x3ffffe00000000fffff7c007ffffbdf700000000000001026004c902a05c0160160004000280152902e0058082c04a5b0130131205413804c04c6c02a000000000000000004221004884081110810408182084495b200108241065464f800319327bee0000221000100200000016055ffc00000010180205000056ffe00003058000b60000002c0abff8000000d800039cee7185296b7bd, 0x100000080000800100021000010000100020004200040008001080200042008401000000800000020000010000100020004200000000400, 0x0, 0x100000080000800100021000010000100020004200040008001080200042008401000000800000020000010000100020004200000000400, 0x3⟩, ⟨0xfffff01f07ffffbc007de00000000000006000c82280188070060000000220052800c201c002100a484038031045003100e00c6180a00000000000000000211480245204088a4082040690420422904084920854d5403e0295aa7800fbc0114800040000000010c500017ff00004020084400050000dffc0442000b0bff800218a0002ffe000c3000d6f76f5b6b5840a5, 0x8000004000040008020080000800008001004010002000401004010040108021000000040000001000000800008001004010000000020, 0x0, 0x8000004000040008020080000800008001004010002000401004010040108021000000040000001000000800008001004010000000020, 0x3⟩, ⟨0x10800012000204000000420000000200000040000008000000024000020080100800000180000000001440010007ff000000000000000000000000000000000000000000000000000000084a5295a42100012, 0x842108421084210842108421080000040000400080210000100020084000802100421084210842000000080000040000400080210800000001, 0x0, 0x842108421084210842108421080000040000400080210000100020084000802100421084210842000000080000040000400080210800000001, 0x0⟩]
def z1 : Nat := 0xad6b49d2b59ce95a4e95ad294a5ab4a56b4a52b49d273b5295a52949ce94a5293b52959ce7494a749d2729529294e7294a939ce528ca5194611
def v1 : List W := [⟨0x1fffff7ffffdf000000003ffffe00000000000000000000000007ffff81f07c0f0000126ac47424e8424a2e88ba23a3000020080b41236846d080000682415a11a180045a1168468624b4300000000000000003ff826ffe09befc4134517fd44c117e014d2fc049a5f808e8a22fd16743e8fa1ef826b6d5aaffedffd6d55ffd7ff7ff0100c030100046000c0000100000868003ff80288002000ffedb7ffdfbdadfedeff7f7b, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x0, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x0⟩, ⟨0x1fffff7ffffdf00000000000000000000000000000000000000000000000000000000126a847004e002480e00380380000000000300006000c00000060000180180000018006006000030000000000000000003ff800ffe003efc0004107e0000107e00010fc00021f80008200fc00042088210f800b6d5aaffedffd6d55ffd7ff7ff0000000000000000000000000000000000000000000000000000000d6b5295ad6b52b5a, 0x842108421084210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 0x0, 0x842108421084210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 0x3⟩, ⟨0x1fffff00000007ffffbefbffffee000000000000000000000000000000000000000005b4ac04c0098000009802602602aa969580ae0025c04b8000005800016016000001600580580002c000000000000000003f0700801c00083f807df41fe01c001e000003c000007800410803c00210441000700b6d58000000000000000000000555adab557ff56ffedffc0000000000000000000000000000000000639c738c739e718e, 0x842108400000000000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x0, 0x842108400000000000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x3⟩, ⟨0x7ffffc0000000000000000000000007ffffc0fffff7df70000000000000000000200420c6428b68043010c10c00000402a10e002180430402521c0008608616d008a02282284911c0000000000000000080482d7120800224120800610508008c048433388046646fbee0220300200802048200c008000c0016d000000000004040180557ff000000001805affe000000002da00000000000db7fff83e9b0745d1745d, 0x2000001000010000108400000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x0, 0x2000001000010000108400000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x3⟩, ⟨0x7ffffbe00000000fbffffef0000000000000000000000000000000004800110b0014000001400500502aad400000900012002409a881601205805800000500140140000a000000000000000002080e06003820c3c707c02101c01f611fc1e803c001007802084803c01080208880e0b0002affe00000000000000000555ac0000000000000001b55affeb6bffbff80000000000000000005b5b4a6b6b794969, 0x800000021084200000000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 0x0, 0x800000021084200000000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 0x3⟩, ⟨0x7ffff80f8000000f80000007ffffde00000000000000000000000000410010088213000001200480482a800d500088001100220d28011000044044049004c013013000090000000000000000010401c1800710a3c0e01f1080381f10103806223f3c8007810404003c08421044401c860020000dffc000000000000055001ab00000000000001b500000000000002daabffaffeffe00000367267c68e5cecc4, 0x40000020000010842000000004000002108400000000842100000000210842100000000200000008000004000002108400000000000100000, 0x0, 0x40000020000010842000000004000002108400000000842100000000210842100000000200000008000004000002108400000000000100000, 0x3⟩, ⟨0x3ffffe00000000000000000000000007ffff81f07c0f0000000040042008400220888220230000200808412308461080000082414210218004421108408624843000000000000000001082601209820441304143d44c0102014c204049840808e08222516703e0f81e0826000180000000001440010007ff0100c030100046000c0000100000868003ff80288002000ffedb7ff8dadadfe4a5a5433, 0x400000200002000401080000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 0x0, 0x400000200002000401080000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 0x3⟩, ⟨0x3ffffe00000000fffff7c007ffffbdf700000000000001026004c902a05c0160160004000280152902e0058082c04a5b0130131205413804c04c6c02a000000000000000004221004884081110810408182084495b200108241065464f800319327bee0000221000100200000016055ffc00000010180205000056ffe00003058000b60000002c0abff8000000d800039cee7185296b7bd, 0x100000080000800100021000010000100020004200040008001080200042008401000000800000020000010000100020004200000000400, 0x0, 0x100000080000800100021000010000100020004200040008001080200042008401000000800000020000010000100020004200000000400, 0x3⟩, ⟨0xfffff01f07ffffbc007de00000000000006000c82280188070060000000220052800c201c002100a484038031045003100e00c6180a00000000000000000211480245204088a4082040690420422904084920854d5403e0295aa7800fbc0114800040000000010c500017ff00004020084400050000dffc0442000b0bff800218a0002ffe000c3000d6f76f5b6b5840a5, 0x8000004000040008020080000800008001004010002000401004010040108021000000040000001000000800008001004010000000020, 0x0, 0x8000004000040008020080000800008001004010002000401004010040108021000000040000001000000800008001004010000000020, 0x3⟩]
def encW (w : W) : Nat × Nat × Nat × Nat × Nat := (w.s,w.a,w.b,w.c,w.r)
def enc (v : List W) : List (Nat × Nat × Nat × Nat × Nat) := v.map encW
lemma encW_inj : Function.Injective encW := by
  intro w w' h
  cases w with
  | mk s a b c r =>
    cases w' with
    | mk s' a' b' c' r' =>
      simp only [encW, Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl,rfl,rfl,rfl⟩
      rfl
lemma enc_inj : Function.Injective enc := by
  intro v v' h
  induction v generalizing v' with
  | nil => cases v' <;> simp_all [enc]
  | cons w v ih =>
    cases v' with
    | nil => simp [enc] at h
    | cons w' v' =>
      have hh : encW w = encW w' ∧ enc v = enc v' := by
        simpa only [enc, List.map_cons, List.cons.injEq] using h
      have hw := encW_inj hh.1
      have hv := ih hh.2
      cases hw
      cases hv
      rfl
def memo (F : Nat → List W → Bool) (z0 : Nat) (v0 : List W)
    (z : Nat) (v : List W) : Bool :=
  if z = z0 ∧ enc v = enc v0 then false else F z v
lemma memo_eq (F : Nat → List W → Bool) (z0 : Nat) (v0 : List W)
    (h : F z0 v0 = false) : memo F z0 v0 = F := by
  funext z v
  by_cases he : z = z0 ∧ enc v = enc v0
  · have hz := he.1
    have hv := enc_inj he.2
    cases hz
    cases hv
    simp only [memo, and_self, if_true, h]
  · simp only [memo, he, if_false]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma memo_outer (F : Nat → List W → Bool) :
    chkF (memo (memo F z0 v0) z1 v1) [] rt 0 14 1 536870912 0 = false := by
  rfl
lemma assemble (F : Nat → List W → Bool)
    (h0 : F z0 v0 = false) (h1 : F z1 v1 = false) :
    chkF F [] rt 0 14 1 536870912 0 = false := by
  have hm0 := memo_eq F z0 v0 h0
  have hm1 := memo_eq F z1 v1 h1
  have hout := memo_outer F
  simpa only [hm0, hm1] using hout
def h8L : Nat := 0x3ffffefffffbefffff7df7ffffddf7ffffdefffffbdffffefbeefffff7beefbdefffeb6d5aaffedffd6d55ffd7ff7ff555adab557ff56ffedffdb55affeb6bffbffadaabffaffeffedb7ff0000000000000000
def h8M : Nat := 0x1fffff7ffffdf7ffffbefbffffeefbffffef7ffffdefffff7df77ffffbdf77def7fff5b6ad57ff6ffeb6aaffebffbffaaad6d5aabffab7ff6ffedaad7ff5b5ffdffd6d55ffd7ff7ff6dbff80000000000000003ffffefffffbefffff7df7ffffddf7ffffdefffffbdffffefbeefffff7beefbdefffeb6d5aaffedffd6d55ffd7ff7ff555adab557ff56ffedffdb55affeb6bffbffadaabffaffeffedb7ffffffffffffffffff
def h8G : Nat := 0x8421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210
def h8w0 : W := ⟨0x1fffff7ffffdf7ffffbefbffffee000000000000000000000000000000000000000005b6ac47c04f802480f803e03e02aa969580be0027c04f800000780001e01e000001e00780780003c000000000000000003fff00fffc03efff807df7ffe01d07fe0010ffc0021ff800c308ffc00630cc310ff00b6d5aaffedffd6d55ffd7ff7ff555adab557ff56ffedffc0000000000000000000000000000000000f7bd7bdef7bf7bde, 0x842108400000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000, 0x0, 0x842108400000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000, 0x0⟩
def h8w1 : W := ⟨0x1fffff7ffffdf000000003ffffe00000000000000000000000007ffff81f07c0f0000126ac47424e8424a2e88ba23a3000020080b41236846d080000682415a11a180045a1168468624b4300000000000000003ff826ffe09befc4134517fd44c117e014d2fc049a5f808e8a22fd16743e8fa1ef826b6d5aaffedffd6d55ffd7ff7ff0100c030100046000c0000100000868003ff80288002000ffedb7ffdfbdadfedeff7f7b, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x0, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x0⟩
def h8w2 : W := ⟨0x1fffff7ffffdf00000000000000000000000000000000000000000000000000000000126a847004e002480e00380380000000000300006000c00000060000180180000018006006000030000000000000000003ff800ffe003efc0004107e0000107e00010fc00021f80008200fc00042088210f800b6d5aaffedffd6d55ffd7ff7ff0000000000000000000000000000000000000000000000000000000d6b5295ad6b52b5a, 0x842108421084210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 0x0, 0x842108421084210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 0x3⟩
def h8w3 : W := ⟨0x1fffff00000007ffffbefbffffee000000000000000000000000000000000000000005b4ac04c0098000009802602602aa969580ae0025c04b8000005800016016000001600580580002c000000000000000003f0700801c00083f807df41fe01c001e000003c000007800410803c00210441000700b6d58000000000000000000000555adab557ff56ffedffc0000000000000000000000000000000000639c738c739e718e, 0x842108400000000000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x0, 0x842108400000000000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x3⟩
def h8w4 : W := ⟨0x7ffffc0000000000000000000000007ffffc0fffff7df70000000000000000000200420c6428b68043010c10c00000402a10e002180430402521c0008608616d008a02282284911c0000000000000000080482d7120800224120800610508008c048433388046646fbee0220300200802048200c008000c0016d000000000004040180557ff000000001805affe000000002da00000000000db7fff83e9b0745d1745d, 0x2000001000010000108400000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x0, 0x2000001000010000108400000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x3⟩
def h8w5 : W := ⟨0x7ffffbe00000000fbffffef0000000000000000000000000000000004800110b0014000001400500502aad400000900012002409a881601205805800000500140140000a000000000000000002080e06003820c3c707c02101c01f611fc1e803c001007802084803c01080208880e0b0002affe00000000000000000555ac0000000000000001b55affeb6bffbff80000000000000000005b5b4a6b6b794969, 0x800000021084200000000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 0x0, 0x800000021084200000000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 0x3⟩
def h8w6 : W := ⟨0x7ffff80f8000000f80000007ffffde00000000000000000000000000410010088213000001200480482a800d500088001100220d28011000044044049004c013013000090000000000000000010401c1800710a3c0e01f1080381f10103806223f3c8007810404003c08421044401c860020000dffc000000000000055001ab00000000000001b500000000000002daabffaffeffe00000367267c68e5cecc4, 0x40000020000010842000000004000002108400000000842100000000210842100000000200000008000004000002108400000000000100000, 0x0, 0x40000020000010842000000004000002108400000000842100000000210842100000000200000008000004000002108400000000000100000, 0x3⟩
def h8w7 : W := ⟨0x3ffffe00000000000000000000000007ffff81f07c0f0000000040042008400220888220230000200808412308461080000082414210218004421108408624843000000000000000001082601209820441304143d44c0102014c204049840808e08222516703e0f81e0826000180000000001440010007ff0100c030100046000c0000100000868003ff80288002000ffedb7ff8dadadfe4a5a5433, 0x400000200002000401080000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 0x0, 0x400000200002000401080000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 0x3⟩
def h8w8 : W := ⟨0x3ffffe00000000fffff7c007ffffbdf700000000000001026004c902a05c0160160004000280152902e0058082c04a5b0130131205413804c04c6c02a000000000000000004221004884081110810408182084495b200108241065464f800319327bee0000221000100200000016055ffc00000010180205000056ffe00003058000b60000002c0abff8000000d800039cee7185296b7bd, 0x100000080000800100021000010000100020004200040008001080200042008401000000800000020000010000100020004200000000400, 0x0, 0x100000080000800100021000010000100020004200040008001080200042008401000000800000020000010000100020004200000000400, 0x3⟩
def h8w9 : W := ⟨0xfffff01f07ffffbc007de00000000000006000c82280188070060000000220052800c201c002100a484038031045003100e00c6180a00000000000000000211480245204088a4082040690420422904084920854d5403e0295aa7800fbc0114800040000000010c500017ff00004020084400050000dffc0442000b0bff800218a0002ffe000c3000d6f76f5b6b5840a5, 0x8000004000040008020080000800008001004010002000401004010040108021000000040000001000000800008001004010000000020, 0x0, 0x8000004000040008020080000800008001004010002000401004010040108021000000040000001000000800008001004010000000020, 0x3⟩
def h8w10 : W := ⟨0x1fffff7ffffdf000000000000000000000007ffffc0fffff7df700000000000000000126a8470c6e28b680e3038c38c00000402a30e006180c30402561c0018618616d018a06286284931c00000000000000003ffc82fff20befe2416187e6105187e8c058ff338a1fe646fbeefe20342288a12fc82b6d5aaffedffd6d55ffd7ff7ff4040180557ff000000001805affe000000002da00000000000db7fffebfbb5fd7f57f5f, 0x2000001000010000108400000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000, 0x0, 0x2000001000010000108400000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000, 0x0⟩
def h8w11 : W := ⟨0x1fffff7ffffdf7ffffbe00000000fbffffef0000000000000000000000000000000005a6a957b04f402480f403d03d02aad40000390007200e409a88760121d81d800001d00740740003a000000000000000003ff8e0ffe383effc707d07f01c01f7f1fc1efc3c021f8780a284fc3c05288a298f8e0b6d5aaffedffd6d55ffd7ff7ff555ac0000000000000001b55affeb6bffbff8000000000000000000dfff6b7bfffd6b7b, 0x800000021084200000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000, 0x0, 0x800000021084200000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000, 0x0⟩
def h8w12 : W := ⟨0x1fffff7ffffdf7ffff80f8000000f80000007ffffde00000000000000000000000000536a947886f302480f203c83c82a800d500388007100e20d280710001c41c404901cc07307300039000000000000000003ff81cffe073effc0e41f7e80381f7e10390fe23f3df80789240fc03c4a4a9254f81cb6d5aaffedffd6d55ffd7ff7ff55001ab00000000000001b500000000000002daabffaffeffe00000f6f76fdedefdefde, 0x40000020000010842000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000, 0x0, 0x40000020000010842000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000, 0x0⟩
def h8w13 : W := ⟨0x10800012000204000000420000000200000040000008000000024000020080100800000180000000001440010007ff000000000000000000000000000000000000000000000000000000084a5295a42100012, 0x842108421084210842108421080000040000400080210000100020084000802100421084210842000000080000040000400080210800000001, 0x0, 0x842108421084210842108421080000040000400080210000100020084000802100421084210842000000080000040000400080210800000001, 0x0⟩
def h8w14 : W := ⟨0x1fffff7ffffdf00000000000000003ffffe00000000fffff7c007ffffbdf700000000126a857264e4cb4aae5c3963960004000283152962e0c58082c64a5b1931931205593864c64c6c32a00000000000000003ffa10ffe843efd1085147e1820947f5b210fc82431fd464fa00fd9327bee8210fa10b6d5aaffedffd6d55ffd7ff7ff10180205000056ffe00003058000b60000002c0abff8000000d8000ffffef5ad6b7bfff, 0x100000080000800100021000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000, 0x0, 0x100000080000800100021000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000, 0x0⟩
def h8w15 : W := ⟨0x8040080100000220020800600100008000003000000600041080200000000000040000c000000000000000000000004040180557ff0000000000000000000000000000000000000000000601c13044190700c, 0x842108401000010000108400004210842108421084210800008420000210800008420080010000108421080200002000021080000040008000, 0x0, 0x842108401000010000108400004210842108421084210800008420000210800008420080010000108421080200002000021080000040008000, 0x0⟩
def h8w16 : W := ⟨0x1fffff7ffffc07ffffbefbffffee000000007ffffc0fffff7df7000000000000000005b6ac46cc6da8b680db036c36c2aa96d5aabee027d84fb0402579c001e61e616d01ea07a87a8493dc00000000000000003f0782d71e08083fc17df41ff05c801ec04843f388047e46fbee03e03212449020782b6d588000c0016d00000000000555adab557ff56ffedffd805affe000000002da00000000000db7fffbbefb8f77df75df, 0x2000000000000000000000000200002000021080000000000000000000000000000000000000000400000000000000000000000000000000, 0x0, 0x2000000000000000000000000200002000021080000000000000000000000000000000000000000400000000000000000000000000000000, 0x0⟩
def h8w17 : W := ⟨0x7ffffbe0000000000000000000000000000000000000000000000000480000080010000001000400402aa94000008000100020000001000004004000000400100100000800000000000000000200000000000083c007c0010000000100000000000000000000000000000000000000b0000000000000000000000000555ac000000000000000000000000000000000000000000000000004318420863184108, 0x842108421084200000000000004210842108421084210842108421084000000000000084000000108421084210840000000000000042000000, 0x0, 0x842108421084200000000000004210842108421084210842108421084000000000000084000000108421084210840000000000000042000000, 0x0⟩
def h8w18 : W := ⟨0x1fffff00000007ffffbefbffffeefbffffef0000000000000000000000000000000005b4ad14f009c000009c02702702aad69580af0025e04bc09a885e012178178000017005c05c0002e000000000000000003f87e0e01f820c3ff07df61ffc1df61ffc1e83fc00107f80618c83fc03184618887e0b6d5aaffe00000000000000000555adab557ff56ffedffdb55affeb6bffbff80000000000000000007bdf7bef7bff79ef, 0x800000000000000000000000004210840000000000000000000000000000000000000000000000100000000000000000000000000000000000, 0x0, 0x800000000000000000000000004210840000000000000000000000000000000000000000000000100000000000000000000000000000000000, 0x0⟩
def h8w19 : W := ⟨0x1fffff00000007ffffbefbffffeef80000007ffffde000000000000000000000000005b4ad04c829b000009a02682682aa96d580ae8025d04ba0d28059000164164049016c05b05b0002d000000000000000003f471c981c710a3f8e7df51fe39df11f038063e3f3c87878514843c3c29465144471cb6d5a0000dffc0000000000000555adab557ff56ffedffdb500000000000002daabffaffeffe0000077fe77ceffdefdce, 0x40000000000000000000000004000002108400000000000000000000000000000000000000000008000000000000000000000000000000000, 0x0, 0x40000000000000000000000004000002108400000000000000000000000000000000000000000008000000000000000000000000000000000, 0x0⟩
def h8w20 : W := ⟨0x1fffff00000007ffffbefbffffee0000000000000000000000007ffff81f07c0f00005b4ac04c209840022988a622632aa969580ae1235c46b880000582415611618004561158458624ac300000000000000003f0f26813c98287f937df43fe4dc103e14c207c49840f88e492a27d6723e4f91e0f26b6d580000000001440010007ff555adab557ff56ffedffc0100000868003ff80288002000ffedb7ffefbdfffe7bde75bf, 0x400000000000000000000000040000400080210000000000000000000000000000000000000000080000000000000000000000000000, 0x0, 0x400000000000000000000000040000400080210000000000000000000000000000000000000000080000000000000000000000000000, 0x0⟩
def h8w21 : W := ⟨0x1fffff00000007ffffbefbffffee03ffffe00000000fffff7c007ffffbdf7000000005b4ac14e609cc902a9dc2762762aad695a8af52b5ee4bd8082c5ca5b173173120557385cc5cc6c2ea00000000000000003f2710849c40893f887df49fe21c449fb20013c241067c64f90833d327bee41002710b6d58200000016055ffc000000555adab557ff56ffedffc3058000b60000002c0abff8000000d80007bdef79c739ef7bf, 0x100000000000000000000000010000100020004200000000000000000000000000000000000000020000000000000000000000000000000, 0x0, 0x100000000000000000000000010000100020004200000000000000000000000000000000000000020000000000000000000000000000000, 0x0⟩
def h8w22 : W := ⟨0x8040020000204020000010008000c00800300000060020840020000000000008000000800000000000000000000404000000000000000001805affe000000000000000000000000000581a0a0341514049, 0x802000021084210000108400004210842000021080000842108421084210800008420004010000100400004210842000021080000002008000, 0x0, 0x802000021084210000108400004210842000021080000842108421084210800008420004010000100400004210842000021080000002008000, 0x0⟩
def h8w23 : W := ⟨0x7ffffc07ffffbe00000000fbffffef7ffffc0fffff7df7000000000000000004820152bc6568b68057015c15c2aad4402a19e003380670daad37c120de0de16d00da0368368491bc00000000000000002884e2f7138a0c3e717c82161c51f619fc5ec33f881467c6fbee823c310a0288a84e2b0c02affec0016d00000000000555ad80557ff000000001b55affeb6bffbffada00000000000db7fffb7fdb6f6ff97d7d, 0x1000000000000000000200000000000000000800008420000000000000000000000000000000000200000000000000000000000000, 0x0, 0x1000000000000000000200000000000000000800008420000000000000000000000000000000000200000000000000000000000000, 0x0⟩
def h8w24 : W := ⟨0x7ffffc07ffff80f8000000f80000007ffffdefffff7df70000000000000000041201428c6538b68053014c14c2a800d52a18e003180630d2a531c000c60c616d00ce03383384919c000000000000000018449edf12790a3e4f21f10e13d1f109c3c86333fbcc667efbee4223f08621846449e86c028000dffd6d0000000000055401ab557ff000000001b55affe000000002daabffaffeffedb7fffe7effc7cfddfcdd, 0x10000000000000000002000000000000800000000000210800000000000000000000000000000002000000000000000000000, 0x0, 0x10000000000000000002000000000000800000000000210800000000000000000000000000000002000000000000000000000, 0x0⟩
def h8w25 : W := ⟨0x7ffffc0000000003ffffe0000000007ffffc0fffff7df77ffff81f07c0f000000204424e64acb6a24b892e12f0000240aa94f2329c6538402529e414a70a796d44ab12ac2ae6d95f0000000000000000090ca6d7329820665324943f54d09028d4ca47379844e6cefbee2736703e0f81e0ca600c188000c0016d440010007ff4140d83557ff46000c001815affe868003ffada88002000ffedb7fffdbfbfff4fdb747f, 0x400000000000000000080000000000020000000800000420000000000000000000000000000000080000000000000, 0x0, 0x400000000000000000080000000000020000000800000420000000000000000000000000000000080000000000000, 0x0⟩
def h8w26 : W := ⟨0x7ffffc000000000000000003ffffe07ffffc0fffff7df77ffffbdf70000000000200522e646cb6aa47c11e11e00040402a11f2923e0478482d25e5b09709716d549b826c26c6d13e00000000000000000c2692d79a4881334930c0879258c49df24853b3c9067666fbee33b337bee0802269200d00a000c0016d55ffc00000050581a0557ff56ffe0001b05affeb60000002daabff8000000db7fff9feff1f57d7f7fd, 0x100000000000000000020000000000008000000200000008400000000000000000000000000000020000000000000000, 0x0, 0x100000000000000000020000000000008000000200000008400000000000000000000000000000020000000000000000, 0x0⟩
def h8w27 : W := ⟨0x7ffffbef8000000fbffffef7ffffde000000000000000000000000004900110b8217000001600580582aad4d500098001300260da881701205c05c049005c0170170000b0000000000000000030c0fc7803f30e3c7e7df3181f81f711ff9ee23ff3d807f830c4c03fc18c230ccc0fcb6002affedffc0000000000000555adab00000000000001b55affeb6bffbffadaabffaffeffe000007f7b6fefef7deded, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x0, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x0⟩
def h8w28 : W := ⟨0x7ffffbe03ffffe0fbffffef00000000000000007ffff81f07c0f00004800510f201c400221c88720732aad600808d1231a463489a881e253479079800447111c41c6248e300000000000000002188e661239a2c7c737c163d5cc1f631fcde843c9850878e28a6a53e713e0f89e88e6b001aaffe000001440010007ff555ac030100046000c001b55affeb6bffbff80288002000ffedb7ffdfffefff6b7b5d7b, 0x200000000000000000040000000000000000100020084000000000000000000000000000000000040000000000000000000000, 0x0, 0x200000000000000000040000000000000000100020084000000000000000000000000000000000040000000000000000000000, 0x0⟩
def h8w29 : W := ⟨0x7ffffbe00000000fbffffef0000000fffff7c007ffffbdf7000000004800110b6014c902a15c0560562aad400280952912e02589aac16a5b05b05b1205453814c14c6c0aa000000000000000024a2f0648bc28d3d787c42919e09f695fe1e90be411657e4f884b1bf27bee2088a2f0b0102affe00016055ffc000000555ac205000056ffe0001b55affeb6bffbffac0abff8000000d80007bdfef7b7bfffffd, 0x80000000000000000010000000000000000040008001080000000000000000000000000000000010000000000000000000000000, 0x0, 0x80000000000000000010000000000000000040008001080000000000000000000000000000000010000000000000000000000000, 0x0⟩
def h8w30 : W := ⟨0x7ffff80fbffffe0f80000007ffffde0000000007ffff81f07c0f00004100500ca21b400221a886a06b2a802d5808c9231946328d28019241465065849446d11b41b6248d3000000000000000011483e1920f92a7c1f05f53d47c1f12117c26627fbc880fe18626517f0be2f85e483e8601a0000dffc01440010007ff5500dab0100046000c001b500000868003ffadaabffaffeffedb7ffbfffeffece5efcf7, 0x2000000000000000000400000000000100000000000802100000000000000000000000000000000400000000000000000, 0x0, 0x2000000000000000000400000000000100000000000802100000000000000000000000000000000400000000000000000, 0x0⟩
def h8w31 : W := ⟨0x7ffff80f8000000fbffffe07ffffdefffff7c007ffffbdf7000000004100110ae217c902a17c05e05e2a840d52809d2913e0278daac15a5b057057169545f817c17c6c0ba000000000000000014621c1c88718b3d0e11f1898389f595b38072a3f3ce547cf8407193e7bee1044621c861022000dffd6055ffc00000055181ab5000056ffe0001b558000b60000002daabffaffeffed80003ffee7dededefffd, 0x800000000000000000100000000000040000000000200042000000000000000000000000000000100000000000000000000, 0x0, 0x800000000000000000100000000000040000000000200042000000000000000000000000000000100000000000000000000, 0x0⟩
def h8w32 : W := ⟨0x3ffffe003ffffe00000000fffff7c007ffffbdf77c0f000000004106600cc902a0dc8360370004200a88552b0ae6158082c0ca5b433033920543390cc0ce6c86b0000000000000000052a3605a8d8a1551b1454bdc6c854b5b6c21486d946d4eef822359777beef81e2a3600118200000016155ffd0007ff1118c235100056ffec0003158000b68003ffac2abffa000ffedb7ffbdefeffe5adef7bf, 0x1000000000000000000200000000000080000002000401000000000000000000000000000000000200000000000, 0x0, 0x1000000000000000000200000000000080000002000401000000000000000000000000000000000200000000000, 0x0⟩
def h8w33 : W := ⟨0x1fffff0000000000000003ffffe000000000000000000000000000000000000000000124ac044008800000880220220000020080a40024804900000048000120120000012004804800024000000000000000003f000080000008040045141d400000000000000000000000000001000010040000000b6d580000000000000000000000100c030100046000c0000000000000000000000000000000000000439c218c529e710a, 0x842108400000200002000401084210842108421084210000000000000000000000000080000002108421080000000000000000000040000000, 0x0, 0x842108400000200002000401084210842108421084210000000000000000000000000080000002108421080000000000000000000040000000, 0x0⟩
def h8w34 : W := ⟨0x1fffff7ffffdf7ffffbefbffffee0000000000000000000000007ffff81f07c0f00005b6ac47c24f8424a2f88be23e32aa969580be1237c46f880000782415e11e180045e1178478624bc300000000000000003fff26fffc9befff937df7ffe4dd17fe14d2ffc49a5ff88ecb2affd6763ecfb1eff26b6d5aaffedffd6d55ffd7ff7ff555adab557ff56ffedffc0100000868003ff80288002000ffedb7ffffbdfffeffff7fff, 0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0⟩
def h8w35 : W := ⟨0x7ffffc0000000000000000000000000000000000000000000000000000000000020042004400248040010010000000000010000200040000002000008008000000800200200001000000000000000000080002d700080000010000040040000000404000880400068a220000300200802000200c008000c0016d0000000000000000000100000000000000000000000000000200000000000db7ffd83c890644d17459, 0x2000401000210002108401080200002000021080000800008420000210800008420000010002000400000200002000021080000000008000, 0x0, 0x2000401000210002108401080200002000021080000800008420000210800008420000010002000400000200002000021080000000008000, 0x0⟩
def h8w36 : W := ⟨0x1fffff7ffffdf000000003ffffe0000000007ffffc0fffff7df77ffff81f07c0f0000126ac474e6eacb6a2eb8bae3af0000240aab4f2369c6d38402569e415a71a796d45ab16ac6ae6db5f00000000000000003ffca6fff29befe6536597ff54d197e8d4daff379a5fe6cefbeeff36743e8fa1efca6b6d5aaffedffd6d55ffd7ff7ff4140d83557ff46000c001815affe868003ffada88002000ffedb7ffffbfbfffdfff7f7f, 0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0⟩
def h8w37 : W := ⟨0x2080206000820c0410440210040116001412800400100080000080140008020088020b0002affe000000000000000000100c00000000000000000100000868003ff80000000000000000005b19086a4a794969, 0x800000421084200002000401084210840000000000000842108421084000000000000004000002100000004210840000000000000002000000, 0x0, 0x800000421084200002000401084210840000000000000842108421084000000000000004000002100000004210840000000000000002000000, 0x0⟩
def h8w38 : W := ⟨0x1fffff7ffffdf7ffffbe03ffffe0fbffffef00000000000000007ffff81f07c0f00005a6ad57f24fc424a2fc8bf23f32aad60080bd1237a46f489a887e2535f91f980045f117c47c624be300000000000000003ff8e6ffe39beffc737d17fd5cc1f7f1fcdefc3c9a5f878eaaa6fd3e753e8fa9ef8e6b6d5aaffedffd6d55ffd7ff7ff555ac030100046000c001b55affeb6bffbff80288002000ffedb7ffdfffefffffff7f7b, 0x200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 0x200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0⟩
def h8w39 : W := ⟨0x1fffff7ffffdf7ffff80fbffffe0f80000007ffffde0000000007ffff81f07c0f0000536ad47ca6fb424a2fa8bea3eb2a802d580bc9237946f28d280792415e51e584945ed17b47b624bd300000000000000003ff83effe0fbeffc1f45f7fd47c1f7e117d2fe27fbdf80fe9a62fd17f4beafa5ef83eb6d5aaffedffd6d55ffd7ff7ff5500dab0100046000c001b500000868003ffadaabffaffeffedb7ffffffeffedeffffff, 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0⟩
def h8w40 : W := ⟨0x1fffff7ffffdf000000003ffffe003ffffe00000000fffff7c007ffffbdf77c0f0000126ac57664eccb4aaedcbb63b70004200a8b552b6ae6d58082c6ca5b5b31b392055b396cc6ce6cb6b00000000000000003ffa36ffe8dbefd51b5557fdc6c957f5b6d2fc86db5fd4eefa22fd9777beefa1efa36b6d5aaffedffd6d55ffd7ff7ff1118c235100056ffec0003158000b68003ffac2abffa000ffedb7ffffffeffedeffffff, 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0⟩
def h8w41 : W := ⟨0x1fffff7ffffdf7ffffbef800000efbffffef7ffffdefffff7df7000003c0701e07fff5b6a957bd6f7ab688f763ddbdcaaad4d52a3be8877b0ef6daad77d1a1dedde56d11dec77b779493bc80000000000000003fffd8ffff63effbec79e7e2bb1de7ffeb1cfffb639fff70f3ccfee987a0e83d0ffd8b6d5aaffedffd6d55ffd7ff7ff545a1a8547ff10ffe1ffdb45affe303ff8002d823ff8ffe00000000f6f77b5bf7b5abde, 0x0, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x0⟩
def h8w42 : W := ⟨0x7ffffbef800000efbffffef7ffffdefffff7df7000003c0701e07fff4900110bd217a920817605d85caaad4d52a0be8817b02f6daad17d1a05ec5e56d105ec17b179490bc80000000000000000007d8001f60003bec38e002bb1ce01feb0c03fb61807f7071cc02e98380601c007d800000000000000000000000000545a1a8547ff10ffe1ffdb45affe303ff8002d823ff8ffe000000002042520121008084, 0x0, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x0⟩
def h8w43 : W := ⟨0x7ffffbef800000e00000000000000000000000000000000000000000490000080010000001000400402aa9495000a000140028000001000004004000000400100100000800000000000000000000700001c00003b8038e002a01c001e000003c000007800410802c0020040100070000000000000000000000000000545a1a8547ff10ffe1ffc00000000000000000000000000000000002000520021000084, 0x842108400000000000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x0, 0x842108400000000000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x0⟩
def h8w44 : W := ⟨0x1fffff00000007ffffbefbffffeefbffffef7ffffdefffff7df7000003c0701e07fff5b4ad14fd29fa92089f627da7caaad6d5aaafe8a5fb4bf6daad5fd1a17ed7e56d117ec5fb5f9492fc80000000000000003f07d8801f60083fec7df41ffb1ce01feb0c03fb61807f7071cc03e98390641c007d8b6d58000000000000000000000555adab557ff56ffedffdb45affe303ff8002d823ff8ffe0000000063de738d739ef18e, 0x0, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x0⟩
def h8w45 : W := ⟨0x7ffffc0fffff7df70000000000000000000000000c2028920003000c00c00000402a00e000180030402501c0000600616d000a00280284901c000000000000000000048000120000224020800210108008c00803330000664071cc02200000000000480000000000000000000000000004040180547ff000000001805affe000000002d800000000000000002002120101000004, 0x2000001000010000108400000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x0, 0x2000001000010000108400000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x0⟩
def h8w46 : W := ⟨0x7ffffc07ffffbef800000efbffffef7ffffdefffff7df7000003c0701e07fff4920152bd657ab68857615d95caaad4d52a1be8837b06f6daad37d1a0decde56d10dec37b379491bc80000000000000000807dad71f68003bed38e006bb5ce01feb4c43fbe9847f76fbee02e9b382609c207da00c008000c0016d00000000000545a1a8557ff10ffe1ffdb45affe303ff8002da23ff8ffe000db7fff87edb0765d1f4dd, 0x0, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x0⟩
def h8w47 : W := ⟨0x7ffffbe00000000fbffffef0000000000000000000000000000000004800110b0014000001400500502aad400000900012002409a881601205805800000500140140000a000000000000000000000c00003000038603800001800e011e80c0038000007002084002801000008000c000000000000000000000000000545a00000000000000001b45affe303ff80000000000000000000000042420121000000, 0x800000021084200000000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 0x0, 0x800000021084200000000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 0x0⟩
def h8w48 : W := ⟨0x7ffffbef800000efbffffef7ffffdefffff7df7000003c0701e07fff4900110bd217a920817605d85caaad4d52a0be8817b02f6daad17d1a05ec5e56d105ec17b179490bc80000000000000002087f8601fe20c3ffc7ce212bf1df61fff1e83ff61907ff071cc82fd8388621c887f8b0002affe00000000000000000555ada8547ff10ffe1ffdb55affeb6bffbffad823ff8ffe000000007b5b5a6b6b79c9ed, 0x0, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x0⟩
def h8w49 : W := ⟨0x7ffffbef800000efbffffef7ffffdefffff7df7000003c0701e07fff4900110bd217a920817605d85caaad4d52a0be8817b02f6daad17d1a05ec5e56d105ec17b179490bc80000000000000001047dc181f710a3fee39f10abb9df11feb8c63fbf3c87f7871cc42ebc384611c447dc860020000dffc0000000000000555a1ab547ff10ffe1ffdb55affe303ff8002daabffaffeffe00000367277c7af5cecc4, 0x0, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x0⟩
def h8w50 : W := ⟨0x7ffffbefbffffeefbffffef7ffffdefffff7df77ffffbdf77def7fff4900510ff21fe922a1fe87f87faaad6d5aa8ffab1ff63fedaad1ff5b47fc7fd6d547fd1ff1ff6d8ff8000000000000000010ffe013ff8207fff3cf43fffdcf03fffce07fff9c0fffe79ee27fff3be6f9de0ffe000180000000001440010007ff555adab557ff56ffedffdb55affeb6bffbffadaabffaffeffedb7ffadefffff6b5ad4b7, 0x0, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x0⟩
def h8w51 : W := ⟨0x7ffffbef800000efbffffef7ffffdefffff7df77ffffbdf701e07fff4900110bf217e922a17e05f85eaaad4d52a0bfa917f02fedaad17f5b05fc5f56d545fc17f17d6d0be80000000000000000427d8049f60813bec38e083bb1ce49ffb0c13fb61867f74f9cc33fba7bee01c027d800100200000016055ffc000000545a1a8547ff56ffe1ffdb45affeb63ff8002d8abff8ffe000d800039cef7197396b7bd, 0x0, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x0⟩
def h8w52 : W := ⟨0x7ffffdf0000000000000000000000000000000000000007ffff81f07c0f0000002004302460424a26089821830000000001012120424080000202414810818004481120420624903000000000000000000f8267fe09be7c0130003e004c117e014d2fc049a5f808e8a22fc16742e8ba1ef82600002affedffd6d55ffd7ff7ff0000000000000000000000100000868003ff80288002000ffedb7ff9c218c728c610e71, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x0, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x0⟩
def h8w53 : W := ⟨0x7ffffc0000000000000000000000007ffffc0fffff7df70000000000000000000200420c6428b68043010c10c00000402a10e002180430402521c0008608616d008a02282284911c000000000000000000008257020800004100000010408000c048403388040646bae600203002008020082000008000c0016d00000000000000000000000000000001805affe000000002da00000000000db7ff9822880304410451, 0x2000001000010000108400000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x0, 0x2000001000010000108400000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x0⟩
def h8w54 : W := ⟨0xfbffffef000000000000000000000000000000000000011030004000000400100100004000000100002000409a8806012018018000001000400400002000000000000000000080e06003820400700002001c01f601fc1e803c001007802084803c01080208880e000002affe00000000000000000000000000000000000001b55affeb6bffbff80000000000000000001843086308610861, 0x800000021084200000000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 0x0, 0x800000021084200000000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 0x0⟩
def h8w55 : W := ⟨0x1fffff000001f000000003ffffe00000000000000000000000007ffff81f07c0f0000124ac05420a840022a88aa22a3000020080a412348469080000482415211218004521148448624a43000000000000000037f82428e093efc4124517f9448117e01492bc04125b80880000fd16443c8f21cf824b615a2ffe1ffc0055ffd7ff7ff0100c030000046000c0000100000868003ff80088002000ffe00000078124f89a2e0b22, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x0, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x0⟩
def h8w56 : W := ⟨0x1fffff000001f00000000000000000000000000000000000000000000000000000000124a805000a000000a002802800000000002000040008000000400001001000000100040040000200000000000000000037f80028e003efc0004107e0000107e00010bc00021b80000000fc00042088210f800b615a2ffe1ffc0055ffd7ff7ff00000000000000000000000000000000000000000000000000000000681205892240b02, 0x842108421084210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 0x0, 0x842108421084210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 0x0⟩
def h8w57 : W := ⟨0x1fffff00000007ffffbefbffffee000000000000000000000000000000000000000005b4ac04c0098000009802602602aa969580ae0025c04b8000005800016016000001600580580002c00000000000000000370300000c00081d805d7419e00c0016000000c000001800000001c00210441000300b6158000000000000000000000151ac2b0000056ffedffc000000000000000000000000000000000003806088320e0182, 0x842108400000000000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x0, 0x842108400000000000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x0⟩
def h8w58 : W := ⟨0x7ffffbe00000000fbffffef0000000000000000000000000000000004800110b0014000001400500502aad400000900012002409a881601205805800000500140140000a000000000000000002080602001820c1c305c02100c0176113c16800c001001800000801c0108020888060b00022ffe00000000000000000151ac00000000000000003500000b6bffbff8000000000000000000034140682a280920, 0x800000021084200000000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 0x0, 0x800000021084200000000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 0x0⟩
def h8w59 : W := ⟨0x1fffff7ffffdf000000003ffffe00000000000000000000000007ffff81f07c0f0000126ac47424e8424a2e88ba23a3000020080b41236846d080000682415a11a180045a1168468624b4300000000000000001f78069fe019e3c0030115ed40c001e000c07c009a4f800e8a227d0274368da16780606d580000dffd6d55ffd7ff7ff00000030100046000c00000000000000000000288002000ffedb7ff84a4a59494863612, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x0, 0x400000200002000401080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000, 0x0⟩
def h8w60 : W := ⟨0x1fffff7ffffdf00000000000000000000000000000000000000000000000000000000126a847004e002480e00380380000000000300006000c00000060000180180000018006006000030000000000000000001f78009fe001e3c0000105e0000001e000007c00020f800082007c00042088210780006d580000dffd6d55ffd7ff7ff000000000000000000000000000000000000000000000000000000084a4211094842212, 0x842108421084210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 0x0, 0x842108421084210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 0x0⟩
def h8w61 : W := ⟨0x1fffff00000000000000fbffffee00000000000000000000000000000000000000000134ac044008800000880220220000029580a60024c04980000048000120120000012004804800024000000000000000001f0700801c0000038001f40fe01c000e000003c000007800410803c0021044100070006d5800000000000000000000000001ab557ff56ffedffc00000000000000000000000000000000002084318410863086, 0x842108400000000000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x0, 0x842108400000000000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x0⟩
def h8w62 : W := ⟨0x7ffffc0000000000000000000000007ffffc0fffff7df70000000000000000000200420c6428b68043010c10c00000402a10e002180430402521c0008608616d008a02282284911c0000000000000000080402971008000201008006005000080040430388046046db6a0200300200802040200c000000c0016d000000000000000180557ff0000000000000000000000002da00000000000db7ffa024910404803414, 0x2000001000010000108400000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x0, 0x2000001000010000108400000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x0⟩
def h8w63 : W := ⟨0x3ffffe00000000000000000000000007ffff81f07c0f0000000040042008400220888220230000200808412308461080000082414210218004421108408624843000000000000000001080601201820400300142d40c0002000c004009840800e0822250270360d8160806000180000000001440010007ff00000030100046000c00000000000000000000288002000ffedb7ff84a4a59400021412, 0x400000200002000401080000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 0x0, 0x400000200002000401080000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 0x0⟩
def h8z0 : Nat := 0x9ce728ca9494a749ca74a4e739d6939d2939ce9394e52b5295a52949ce94a5293b52958ca538c65394e518d29294e7294a939ce528465194611
def h8z1 : Nat := 0xad6949d2b49ce94a4e94a4e94a5a94a5694a529395273ad2959ce749ce739d293ace759ce7394a749ce729527294e5294a7294e528ca518c611
def h8z2 : Nat := 0xa527394e9394a739ca739ca739da94a5694a529395273ad2959ce749ce739d293ace7594a528c6549ce729527294e5294a7294e5284a518c611
def h8z3 : Nat := 0xa56b49d29494a75a4e95ad294a56939d2b4a52b49d273ace749ce7394a94a5293b52959ca7494a739d27294e718ca7294a939ce528ca3194611
def h8z4 : Nat := 0x9d29394e738c6549ca74a4e739d6939d2b4a52b49d273ace749ce7394a94a5293b5295946538c6539d27294e718ca7294a939ce5284a3194611
def h8z5 : Nat := 0xad2b49d2959ce949ca75ad294a56b4a56939ceb49d273ace74a52949ce739ce72b52959ce5494a749527294e9294e518c6939ce528ca5094611
def h8z6 : Nat := 0xa4e9394e7494a7394654a4e739d6b4a56939ceb49d273ace74a52949ce739ce72b529594a338c6549527294e9294e518c6939ce5284a5094611
def h8z7 : Nat := 0xa52939529494a949ca94a5274a5ab4a52b4a4eb495252b5294a527494a949d272b4e7494a538c6749d2728d29294a729469394e3184a5194610
def h8z8 : Nat := 0xa529294e948ca7494a73a4e529dab3a56b3a52949ce53b4e959d29394e74a4e73ace9494a53846549d2529529194e7194a739ca3284a5194211
def h8z9 : Nat := 0x9ce728cab39ce93a4e939ca94a527294e7294a728ca31a529594a549ce5295293a4a558ce7294a728ca308525294e3294a518ce528c25184611
def h8z10 : Nat := 0xa527394eb49ce94a4e94a4e94a56739d2739ce728ce52ad2959ce749ce739d293ace7594e7394a7394a518d27294e5294a7294e528c6518c611
def h8z11 : Nat := 0x9ce728ca738c655a4e95ad294a527294e7294a728ca31a4a5394a528c694a5293b52958c67494a728ca3084a508467294a939ce528c21194611
def h8z12 : Nat := 0x9d29394e9494a75a4e95ad294a527294e939ce9394e52ace749ce7394a94a5293b529594a7494a7294e518ce718ca7294a939ce528c63194611
def h8z13 : Nat := 0xa4e9394e959ce949ca75ad294a52939d27294a9394e52ace74a52949ce739ce72b529594e5494a738ce518ce9294e518c6939ce528c65094611
def h8z14 : Nat := 0xa529394ab59ce75a4e75ace939d6939ce939ca938ce31b5294a527494a949d272b4e7494e7494a5394e518529294a729469394e318c65194610
def h8z15 : Nat := 0xa529294eb594e959ce94ad273a56929d2929ce7394a32b4e959d29394e74a4e73ace9494e748ca7394e318d29194e7194a739ca328c65194211
def h8z16 : Nat := 0x9d6749d2738c653a4e939ca94a527294e74a52728d273a4a5394a528c65295293a4a559c67294a729ca7294a508463294a518ce528ca1184611
def h8z17 : Nat := 0xa56949d29394a74a4e94a4e94a56739d294a529395273a4e7494a5394a739d293ace759ca7394a739ce7294e518ca5294a7294e528ca318c611
def h8z18 : Nat := 0xad2949d2949ce939ca74a4e94a5694a56739ce9395273a4e749ce749ce5294e72ace759ce5394a7494e7294e7294e318c67294e528ca508c611
def h8z19 : Nat := 0xad6949ceb49ce74a4e74a4a939da94a5294a4e938d252ad2949ce5494a7395272aca549ce7394a549ce728d27294a52946728ce318ca518c610
def h8z20 : Nat := 0xad6939d2b494e949ce93a4e73a5a93a5693a527394e53ace9594e7394e539ce73a4a749ce738ca749ce529527194e5194a5294a328ca518c211
def h8z21 : Nat := 0xa52b49d27494a749ca75ad294a52939d2939ceb49d273a4a539ce7394a739ce72b52959ca5494a739527294a718ca518c6939ce528ca3094611
def h8z22 : Nat := 0xa56b49ce9494a55a4e75ace939d6939ceb4a4eb495252ace739ce538c6949d272b4e749ca7494a539d2728ce718c6729469394e318ca3194610
def h8z23 : Nat := 0xa56b39d2948ca759ce94ad273a56929d2b3a52949ce53aca7494e728ca74a4e73ace949ca748ca739d25294e708ca7194a739ca328ca3194211
def h8z24 : Nat := 0xad2b49ce959ce749ca55ace939d6b4a52939cab495252ace73a527494a7394e51b4e749ce5494a54952728ce9294a518c29394e318ca5094610
def h8z25 : Nat := 0xad2b39d29594e9494a74ad273a56b3a56929ce949ce53aca749d29394e539ca52ace949ce548ca749525294e9194e508c6739ca328ca5094211
def h8z26 : Nat := 0xad6b39d2b594e959ce94ad273a5ab3a56b3a52949ce53b4e959d29394e74a4e73ace949ce748ca749d2529529194e7194a739ca328ca5194211
def h8z27 : Nat := 0xad6b39ceb594e759ce74ace729dab3a52b3a4e9494e32b4e949d2738ca749ce52aca739ce748ca549d2528d29194a719467394a118ca5194210
def h8z28 : Nat := 0x9ce728ceb59ce75a4e75ace939d27294e7294a728ca31b5295a52949ce94a5293b52958ce7494a528ca308529294e7294a939ce528c25194611
def h8z29 : Nat := 0x9ce728cab59ce55a4e55aca929527294e7294a728ca31b5295a52949ce94a5293b52958ce7494a328ca308529294e7294a939ce528c25194611
def h8z30 : Nat := 0xa529394eb59ce95a4e95ad294a56939d2939ce9394e52b5295a52949ce94a5293b529594e7494a7394e518d29294e7294a939ce528c65194611
def h8z31 : Nat := 0xa529394ab59ce75a4e75ace939d6939d2939ce9394e52b5295a52949ce94a5293b529594e7494a5394e518d29294e7294a939ce528c65194611
def h8z32 : Nat := 0xad6749ceb39ce73a4e739ce939da74a5674a52728d273a529594a549ce5295293a4a559ce7294a549ca729525294e3294a518ce528ca5184611
def h8z33 : Nat := 0xad6749cab39ce53a4e539ca9295a74a5674a52728d273a529594a549ce5295293a4a559ce7294a349ca729525294e3294a518ce528ca5184611
def h8z34 : Nat := 0xad6949ceb49ce74a4e74a4a939da94a5694a529395273ad2959ce749ce739d293ace759ce7394a549ce729527294e5294a7294e528ca518c611
def h8z35 : Nat := 0x9d6b49ce738c675a4e75ace939d27294eb4a52b49d273a4a5394a528c694a5293b52959c67494a529d27294a508467294a939ce528ca1194611
def h8z36 : Nat := 0x9d6b49ca738c655a4e55aca929527294eb4a52b49d273a4a5394a528c694a5293b52959c67494a329d27294a508467294a939ce528ca1194611
def h8z37 : Nat := 0xa56b49ce9494a55a4e75ace939d6939d2b4a52b49d273ace749ce7394a94a5293b52959ca7494a539d27294e718ca7294a939ce528ca3194611
def h8z38 : Nat := 0xad2b49ce959ce749ca55ace939d6b4a56939ceb49d273ace74a52949ce739ce72b52959ce5494a549527294e9294e518c6939ce528ca5094611
def h8z39 : Nat := 0xad6b39ceb594e759ce74ace729dab3a56b3a52949ce53b4e959d29394e74a4e73ace949ce748ca549d2529529194e7194a739ca328ca5194211
def h8z40 : Nat := 0xa529394a9494a549ca54a4a7295ab4a56b4a52b49d273b5295a52949ce94a5293b529594a538c6349d2729529294e7294a939ce5284a5194611
def h8z41 : Nat := 0xa52939469494a349ca34a46718dab4a56b4a52b49d273b5295a52949ce94a5293b529594a538c6149d2729529294e7294a939ce5284a5194611
def h8z42 : Nat := 0x9ce728cab59ce75a4e75ace939d27294e7294a728ca31b5295a52949ce94a5293b52958ce7494a528ca308529294e7294a939ce528c25194611
def h8z43 : Nat := 0x9ce728c6b59ce55a4e55aca929527294e7294a728ca31b5295a52949ce94a5293b52958ce7494a328ca308529294e7294a939ce528c25194611
def h8z44 : Nat := 0xa529394ab59ce55a4e55aca92956939d2939ce9394e52b5295a52949ce94a5293b529594e7494a3394e518d29294e7294a939ce528c65194611
def h8z45 : Nat := 0xa5293946b59ce35a4e35ac6918d6939d2939ce9394e52b5295a52949ce94a5293b529594e7494a1394e518d29294e7294a939ce528c65194611
def h8z46 : Nat := 0xad6749ceb39ce73a4e739ca939da74a5674a52728d273a529594a549ce5295293a4a559ce7294a549ca729525294e3294a518ce528ca5184611
def h8z47 : Nat := 0xad6749cab39ce53a4e539c69295a74a5674a52728d273a529594a549ce5295293a4a559ce7294a349ca729525294e3294a518ce528ca5184611
def h8z48 : Nat := 0xad6949cab49ce54a4e54a4a9295a94a5694a529395273ad2959ce749ce739d293ace759ce7394a349ce729527294e5294a7294e528ca518c611
def h8z49 : Nat := 0xad6949c6b49ce34a4e34a46918da94a5694a529395273ad2959ce749ce739d293ace759ce7394a149ce729527294e5294a7294e528ca518c611
def h8z50 : Nat := 0x9d6b49ce738c655a4e75ace939d27294eb4a52b49d273a4a5394a528c694a5293b52959c67494a529d27294a508467294a939ce528ca1194611
def h8z51 : Nat := 0x9d6b49ca738c635a4e55aca929527294eb4a52b49d273a4a5394a528c694a5293b52959c67494a329d27294a508467294a939ce528ca1194611
def h8z52 : Nat := 0xa56b49ca9494a55a4e55aca92956939d2b4a52b49d273ace749ce7394a94a5293b52959ca7494a339d27294e718ca7294a939ce528ca3194611
def h8z53 : Nat := 0xa56b49c69494a35a4e35ac6918d6939d2b4a52b49d273ace749ce7394a94a5293b52959ca7494a139d27294e718ca7294a939ce528ca3194611
def h8z54 : Nat := 0xad2b49ca959ce549ca55aca92956b4a56939ceb49d273ace74a52949ce739ce72b52959ce5494a349527294e9294e518c6939ce528ca5094611
def h8z55 : Nat := 0xad2b49c6959ce349ca35ac6918d6b4a56939ceb49d273ace74a52949ce739ce72b52959ce5494a149527294e9294e518c6939ce528ca5094611
def h8z56 : Nat := 0xad6b49cab59ce55a4e55aca9295ab4a52b4a4eb495252b5294a527494a949d272b4e749ce7494a349d2728d29294a729469394e318ca5194610
def h8z57 : Nat := 0xad6b49c6b59ce35a4e35ac6918dab4a52b4a4eb495252b5294a527494a949d272b4e749ce7494a149d2728d29294a729469394e318ca5194610
def h8z58 : Nat := 0xad6b39cab594e559ce54aca7295ab3a56b3a52949ce53b4e959d29394e74a4e73ace949ce748ca349d2529529194e7194a739ca328ca5194211
def h8z59 : Nat := 0xad6b39c6b594e359ce34ac6718dab3a56b3a52949ce53b4e959d29394e74a4e73ace949ce748ca149d2529529194e7194a739ca328ca5194211
def h8z60 : Nat := 0xad6b49cab59ce55a4e55aca9295ab4a56b4a52b49d273b5295a52949ce94a5293b52959ce7494a349d2729529294e7294a939ce528ca5194611
def h8z61 : Nat := 0xad6b49c6b59ce35a4e35ac6918dab4a56b4a52b49d273b5295a52949ce94a5293b52959ce7494a149d2729529294e7294a939ce528ca5194611
def h8z62 : Nat := 0x9ce728c2b59ce35a4e35ac6918d27294e7294a728ca31b5295a52949ce94a5293b52958ce7494a128ca308529294e7294a939ce528c25194611
def h8z63 : Nat := 0xad6749c6b39ce33a4e339c2918da74a5674a52728d273a529594a549ce5295293a4a559ce7294a149ca729525294e3294a518ce528ca5184611
def h8z64 : Nat := 0x9d6b49c6738c615a4e35ac6918d27294eb4a52b49d273a4a5394a528c694a5293b52959c67494a129d27294a508467294a939ce528ca1194611
def h8z65 : Nat := 0x9ce528cab39ce93a4e939ca94a525294e5294a5184a31a529594a549ce5295293a4a558ce7294a728c6308525294e3294a518ce528c25184611
def h8z66 : Nat := 0x94e728ca738c655a4e95ad294a4e518ca7294a728ca31a4a5394a528c694a5293b52958c67494a718ca3084a508467294a939ce528c21194611
def h8z67 : Nat := 0xa527394e9394a739ca739ca739da74a5674a52728d273a529594a549ce5295293a4a5594a528c6549ca729525294e3294a518ce5284a5184611
def h8z68 : Nat := 0x9d6749d2728c653a4e939ca94a525294e74a52728d2739ca538c6328c65295293a4a559c67294a729ca7294a308463294a518ce528ca1184611
def h8z69 : Nat := 0x9d29394e738c6549ca74a4e739d27294eb4a52b49d273a4a5394a528c694a5293b5295946538c6529d27294a508467294a939ce5284a1194611
def h8z70 : Nat := 0x9d6b49ce738c655a4e75ace939d27294eb4a4eb495252a4a5394a528c6949d272b4e749c67494a529d2728ca50846729469394e318ca1194610
def h8z71 : Nat := 0xad6b49d2b59ce95a4e95ad294a5ab4a56b4a52b49d273b5295a52949ce94a5293b52959ce7494a749d2729529294e7294a939ce528ca5194611

def memo4 (F : Nat → Nat → Nat → List W → Bool)
    (k0 t0 z0 : Nat) (v0 : List W) (k t z : Nat) (v : List W) : Bool :=
  if k = k0 ∧ t = t0 ∧ z = z0 ∧ enc v = enc v0 then false else F k t z v
lemma memo4_eq (F : Nat → Nat → Nat → List W → Bool)
    (k0 t0 z0 : Nat) (v0 : List W) (h : F k0 t0 z0 v0 = false) :
    memo4 F k0 t0 z0 v0 = F := by
  funext k t z v
  by_cases he : k = k0 ∧ t = t0 ∧ z = z0 ∧ enc v = enc v0
  · rcases he with ⟨rfl,rfl,rfl,hv⟩
    obtain rfl := enc_inj hv
    simp only [memo4, and_self, if_true, h]
  · simp only [memo4, he, if_false]
def look1F (A B : Nat → Nat → Nat → List W → Bool)
    (l m g k t z : Nat) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mv B l m g k t z v y) true
        (node (A (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y)
          v.length z v pairsS))) true (Nat.ble v.length 1)
lemma look1_succ (l m g K fuel k t z : Nat) (v : List W) :
    look1 l m g K (fuel + 1) k t z v =
      look1F (look1 l m g K fuel) (look l m g K) l m g k t z v := by
  rfl
def cacheA (A : Nat → Nat → Nat → List W → Bool) := memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (A) 12 1 h8z0 [h8w0, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z1 [h8w1, h8w10, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z2 [h8w1, h8w10, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z3 [h8w11, h8w1, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z4 [h8w11, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z5 [h8w12, h8w1, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z6 [h8w12, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z7 [h8w1, h8w3, h8w4, h8w5, h8w6, h8w8, h8w9, h8w13]) 12 1 h8z8 [h8w1, h8w14, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z9 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w15]) 12 1 h8z10 [h8w1, h8w2, h8w16, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z11 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w17, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z12 [h8w1, h8w2, h8w18, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z13 [h8w1, h8w2, h8w19, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z14 [h8w1, h8w2, h8w20, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z15 [h8w1, h8w2, h8w21, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z16 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w22]) 12 1 h8z17 [h8w1, h8w2, h8w3, h8w23, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z18 [h8w1, h8w2, h8w3, h8w24, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z19 [h8w1, h8w2, h8w3, h8w25, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z20 [h8w1, h8w2, h8w3, h8w26, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z21 [h8w1, h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z3 [h8w1, h8w2, h8w3, h8w4, h8w28, h8w5, h8w6, h8w8, h8w9]) 12 1 h8z22 [h8w1, h8w2, h8w3, h8w4, h8w28, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z23 [h8w1, h8w2, h8w3, h8w4, h8w29, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z5 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w30, h8w6, h8w8, h8w9]) 12 1 h8z24 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w30, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z25 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w31, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z26 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w32, h8w8, h8w9]) 12 1 h8z27 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w32, h8w7, h8w8, h8w9]
lemma cacheA_eq (A : Nat → Nat → Nat → List W → Bool)
    (h0 : A 12 1 h8z0 [h8w0, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h1 : A 12 1 h8z1 [h8w1, h8w10, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h2 : A 12 1 h8z2 [h8w1, h8w10, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h3 : A 12 1 h8z3 [h8w11, h8w1, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h4 : A 12 1 h8z4 [h8w11, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h5 : A 12 1 h8z5 [h8w12, h8w1, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h6 : A 12 1 h8z6 [h8w12, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h7 : A 12 1 h8z7 [h8w1, h8w3, h8w4, h8w5, h8w6, h8w8, h8w9, h8w13] = false)
    (h8 : A 12 1 h8z8 [h8w1, h8w14, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h9 : A 12 1 h8z9 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w15] = false)
    (h10 : A 12 1 h8z10 [h8w1, h8w2, h8w16, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h11 : A 12 1 h8z11 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w17, h8w6, h8w7, h8w8, h8w9] = false)
    (h12 : A 12 1 h8z12 [h8w1, h8w2, h8w18, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h13 : A 12 1 h8z13 [h8w1, h8w2, h8w19, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h14 : A 12 1 h8z14 [h8w1, h8w2, h8w20, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h15 : A 12 1 h8z15 [h8w1, h8w2, h8w21, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h16 : A 12 1 h8z16 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w22] = false)
    (h17 : A 12 1 h8z17 [h8w1, h8w2, h8w3, h8w23, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h18 : A 12 1 h8z18 [h8w1, h8w2, h8w3, h8w24, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h19 : A 12 1 h8z19 [h8w1, h8w2, h8w3, h8w25, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h20 : A 12 1 h8z20 [h8w1, h8w2, h8w3, h8w26, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h21 : A 12 1 h8z21 [h8w1, h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h22 : A 12 1 h8z3 [h8w1, h8w2, h8w3, h8w4, h8w28, h8w5, h8w6, h8w8, h8w9] = false)
    (h23 : A 12 1 h8z22 [h8w1, h8w2, h8w3, h8w4, h8w28, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h24 : A 12 1 h8z23 [h8w1, h8w2, h8w3, h8w4, h8w29, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h25 : A 12 1 h8z5 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w30, h8w6, h8w8, h8w9] = false)
    (h26 : A 12 1 h8z24 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w30, h8w6, h8w7, h8w8, h8w9] = false)
    (h27 : A 12 1 h8z25 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w31, h8w6, h8w7, h8w8, h8w9] = false)
    (h28 : A 12 1 h8z26 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w32, h8w8, h8w9] = false)
    (h29 : A 12 1 h8z27 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w32, h8w7, h8w8, h8w9] = false)
    : cacheA A = A := by
  simp only [cacheA, memo4_eq A 12 1 h8z0 [h8w0, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h0, memo4_eq A 12 1 h8z1 [h8w1, h8w10, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h1, memo4_eq A 12 1 h8z2 [h8w1, h8w10, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h2, memo4_eq A 12 1 h8z3 [h8w11, h8w1, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h3, memo4_eq A 12 1 h8z4 [h8w11, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h4, memo4_eq A 12 1 h8z5 [h8w12, h8w1, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h5, memo4_eq A 12 1 h8z6 [h8w12, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h6, memo4_eq A 12 1 h8z7 [h8w1, h8w3, h8w4, h8w5, h8w6, h8w8, h8w9, h8w13] h7, memo4_eq A 12 1 h8z8 [h8w1, h8w14, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h8, memo4_eq A 12 1 h8z9 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w15] h9, memo4_eq A 12 1 h8z10 [h8w1, h8w2, h8w16, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h10, memo4_eq A 12 1 h8z11 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w17, h8w6, h8w7, h8w8, h8w9] h11, memo4_eq A 12 1 h8z12 [h8w1, h8w2, h8w18, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h12, memo4_eq A 12 1 h8z13 [h8w1, h8w2, h8w19, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h13, memo4_eq A 12 1 h8z14 [h8w1, h8w2, h8w20, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h14, memo4_eq A 12 1 h8z15 [h8w1, h8w2, h8w21, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h15, memo4_eq A 12 1 h8z16 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w22] h16, memo4_eq A 12 1 h8z17 [h8w1, h8w2, h8w3, h8w23, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h17, memo4_eq A 12 1 h8z18 [h8w1, h8w2, h8w3, h8w24, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h18, memo4_eq A 12 1 h8z19 [h8w1, h8w2, h8w3, h8w25, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h19, memo4_eq A 12 1 h8z20 [h8w1, h8w2, h8w3, h8w26, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h20, memo4_eq A 12 1 h8z21 [h8w1, h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9] h21, memo4_eq A 12 1 h8z3 [h8w1, h8w2, h8w3, h8w4, h8w28, h8w5, h8w6, h8w8, h8w9] h22, memo4_eq A 12 1 h8z22 [h8w1, h8w2, h8w3, h8w4, h8w28, h8w5, h8w6, h8w7, h8w8, h8w9] h23, memo4_eq A 12 1 h8z23 [h8w1, h8w2, h8w3, h8w4, h8w29, h8w5, h8w6, h8w7, h8w8, h8w9] h24, memo4_eq A 12 1 h8z5 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w30, h8w6, h8w8, h8w9] h25, memo4_eq A 12 1 h8z24 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w30, h8w6, h8w7, h8w8, h8w9] h26, memo4_eq A 12 1 h8z25 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w31, h8w6, h8w7, h8w8, h8w9] h27, memo4_eq A 12 1 h8z26 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w32, h8w8, h8w9] h28, memo4_eq A 12 1 h8z27 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w32, h8w7, h8w8, h8w9] h29]
def cacheB (B : Nat → Nat → Nat → List W → Bool) := memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (B) 12 1 h8z28 [h8w2, h8w3, h8w33, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z29 [h8w1, h8w2, h8w3, h8w33, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z30 [h8w34, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z31 [h8w34, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z32 [h8w2, h8w3, h8w4, h8w35, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z33 [h8w1, h8w2, h8w3, h8w4, h8w35, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z1 [h8w36, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z34 [h8w36, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z35 [h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w37]) 12 1 h8z36 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w37]) 12 1 h8z3 [h8w38, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z37 [h8w38, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z5 [h8w39, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z38 [h8w39, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z26 [h8w40, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 12 1 h8z39 [h8w40, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z40 [h8w41, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z41 [h8w41, h8w2, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z42 [h8w2, h8w3, h8w4, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z43 [h8w2, h8w3, h8w4, h8w42, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z44 [h8w2, h8w44, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z45 [h8w2, h8w44, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z46 [h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9]) 11 0 h8z47 [h8w2, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9]) 11 0 h8z48 [h8w2, h8w3, h8w46, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z49 [h8w2, h8w3, h8w46, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z50 [h8w2, h8w3, h8w4, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z51 [h8w2, h8w3, h8w4, h8w42, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z52 [h8w2, h8w3, h8w4, h8w48, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z53 [h8w2, h8w3, h8w4, h8w48, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z54 [h8w2, h8w3, h8w4, h8w49, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z55 [h8w2, h8w3, h8w4, h8w49, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z56 [h8w2, h8w3, h8w4, h8w50, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z57 [h8w2, h8w3, h8w4, h8w50, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z58 [h8w2, h8w3, h8w4, h8w51, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z59 [h8w2, h8w3, h8w4, h8w51, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z60 [h8w41, h8w1, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z61 [h8w41, h8w1, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z41 [h8w41, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z43 [h8w1, h8w2, h8w3, h8w4, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z62 [h8w1, h8w2, h8w3, h8w4, h8w42, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z45 [h8w1, h8w2, h8w44, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z47 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9]) 11 0 h8z63 [h8w1, h8w2, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9]) 11 0 h8z49 [h8w1, h8w2, h8w3, h8w46, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z51 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z64 [h8w1, h8w2, h8w3, h8w4, h8w42, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z53 [h8w1, h8w2, h8w3, h8w4, h8w48, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z55 [h8w1, h8w2, h8w3, h8w4, h8w49, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z60 [h8w1, h8w2, h8w3, h8w4, h8w50, h8w5, h8w6, h8w8, h8w9]) 11 0 h8z61 [h8w1, h8w2, h8w3, h8w4, h8w50, h8w42, h8w5, h8w6, h8w8, h8w9]) 11 0 h8z57 [h8w1, h8w2, h8w3, h8w4, h8w50, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z59 [h8w1, h8w2, h8w3, h8w4, h8w51, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z42 [h8w2, h8w3, h8w52, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z43 [h8w1, h8w2, h8w3, h8w52, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z65 [h8w1, h8w2, h8w3, h8w4, h8w53, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z66 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w54, h8w8, h8w9]) 11 0 h8z46 [h8w2, h8w55, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z47 [h8w1, h8w2, h8w55, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z67 [h8w1, h8w56, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z65 [h8w1, h8w2, h8w3, h8w57, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z68 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w58, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z50 [h8w59, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z51 [h8w1, h8w59, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z69 [h8w1, h8w60, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z66 [h8w1, h8w2, h8w3, h8w61, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z68 [h8w1, h8w2, h8w3, h8w4, h8w62, h8w5, h8w6, h8w7, h8w8, h8w9]) 11 0 h8z70 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w63, h8w8, h8w9]
lemma cacheB_eq (B : Nat → Nat → Nat → List W → Bool)
    (h30 : B 12 1 h8z28 [h8w2, h8w3, h8w33, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h31 : B 12 1 h8z29 [h8w1, h8w2, h8w3, h8w33, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h32 : B 12 1 h8z30 [h8w34, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h33 : B 12 1 h8z31 [h8w34, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h34 : B 12 1 h8z32 [h8w2, h8w3, h8w4, h8w35, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h35 : B 12 1 h8z33 [h8w1, h8w2, h8w3, h8w4, h8w35, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h36 : B 12 1 h8z1 [h8w36, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h37 : B 12 1 h8z34 [h8w36, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h38 : B 12 1 h8z35 [h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w37] = false)
    (h39 : B 12 1 h8z36 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w37] = false)
    (h40 : B 12 1 h8z3 [h8w38, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h41 : B 12 1 h8z37 [h8w38, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h42 : B 12 1 h8z5 [h8w39, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h43 : B 12 1 h8z38 [h8w39, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h44 : B 12 1 h8z26 [h8w40, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h45 : B 12 1 h8z39 [h8w40, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h46 : B 11 0 h8z40 [h8w41, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h47 : B 11 0 h8z41 [h8w41, h8w2, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h48 : B 11 0 h8z42 [h8w2, h8w3, h8w4, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h49 : B 11 0 h8z43 [h8w2, h8w3, h8w4, h8w42, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h50 : B 11 0 h8z44 [h8w2, h8w44, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h51 : B 11 0 h8z45 [h8w2, h8w44, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h52 : B 11 0 h8z46 [h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9] = false)
    (h53 : B 11 0 h8z47 [h8w2, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9] = false)
    (h54 : B 11 0 h8z48 [h8w2, h8w3, h8w46, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h55 : B 11 0 h8z49 [h8w2, h8w3, h8w46, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h56 : B 11 0 h8z50 [h8w2, h8w3, h8w4, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9] = false)
    (h57 : B 11 0 h8z51 [h8w2, h8w3, h8w4, h8w42, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9] = false)
    (h58 : B 11 0 h8z52 [h8w2, h8w3, h8w4, h8w48, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h59 : B 11 0 h8z53 [h8w2, h8w3, h8w4, h8w48, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h60 : B 11 0 h8z54 [h8w2, h8w3, h8w4, h8w49, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h61 : B 11 0 h8z55 [h8w2, h8w3, h8w4, h8w49, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h62 : B 11 0 h8z56 [h8w2, h8w3, h8w4, h8w50, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h63 : B 11 0 h8z57 [h8w2, h8w3, h8w4, h8w50, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h64 : B 11 0 h8z58 [h8w2, h8w3, h8w4, h8w51, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h65 : B 11 0 h8z59 [h8w2, h8w3, h8w4, h8w51, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h66 : B 11 0 h8z60 [h8w41, h8w1, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h67 : B 11 0 h8z61 [h8w41, h8w1, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h68 : B 11 0 h8z41 [h8w41, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h69 : B 11 0 h8z43 [h8w1, h8w2, h8w3, h8w4, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h70 : B 11 0 h8z62 [h8w1, h8w2, h8w3, h8w4, h8w42, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h71 : B 11 0 h8z45 [h8w1, h8w2, h8w44, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h72 : B 11 0 h8z47 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9] = false)
    (h73 : B 11 0 h8z63 [h8w1, h8w2, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9] = false)
    (h74 : B 11 0 h8z49 [h8w1, h8w2, h8w3, h8w46, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h75 : B 11 0 h8z51 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9] = false)
    (h76 : B 11 0 h8z64 [h8w1, h8w2, h8w3, h8w4, h8w42, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9] = false)
    (h77 : B 11 0 h8z53 [h8w1, h8w2, h8w3, h8w4, h8w48, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h78 : B 11 0 h8z55 [h8w1, h8w2, h8w3, h8w4, h8w49, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h79 : B 11 0 h8z60 [h8w1, h8w2, h8w3, h8w4, h8w50, h8w5, h8w6, h8w8, h8w9] = false)
    (h80 : B 11 0 h8z61 [h8w1, h8w2, h8w3, h8w4, h8w50, h8w42, h8w5, h8w6, h8w8, h8w9] = false)
    (h81 : B 11 0 h8z57 [h8w1, h8w2, h8w3, h8w4, h8w50, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h82 : B 11 0 h8z59 [h8w1, h8w2, h8w3, h8w4, h8w51, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h83 : B 11 0 h8z42 [h8w2, h8w3, h8w52, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h84 : B 11 0 h8z43 [h8w1, h8w2, h8w3, h8w52, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h85 : B 11 0 h8z65 [h8w1, h8w2, h8w3, h8w4, h8w53, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h86 : B 11 0 h8z66 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w54, h8w8, h8w9] = false)
    (h87 : B 11 0 h8z46 [h8w2, h8w55, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h88 : B 11 0 h8z47 [h8w1, h8w2, h8w55, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h89 : B 11 0 h8z67 [h8w1, h8w56, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h90 : B 11 0 h8z65 [h8w1, h8w2, h8w3, h8w57, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h91 : B 11 0 h8z68 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w58, h8w6, h8w7, h8w8, h8w9] = false)
    (h92 : B 11 0 h8z50 [h8w59, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h93 : B 11 0 h8z51 [h8w1, h8w59, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h94 : B 11 0 h8z69 [h8w1, h8w60, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h95 : B 11 0 h8z66 [h8w1, h8w2, h8w3, h8w61, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h96 : B 11 0 h8z68 [h8w1, h8w2, h8w3, h8w4, h8w62, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h97 : B 11 0 h8z70 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w63, h8w8, h8w9] = false)
    : cacheB B = B := by
  simp only [cacheB, memo4_eq B 12 1 h8z28 [h8w2, h8w3, h8w33, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h30, memo4_eq B 12 1 h8z29 [h8w1, h8w2, h8w3, h8w33, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h31, memo4_eq B 12 1 h8z30 [h8w34, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h32, memo4_eq B 12 1 h8z31 [h8w34, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h33, memo4_eq B 12 1 h8z32 [h8w2, h8w3, h8w4, h8w35, h8w5, h8w6, h8w7, h8w8, h8w9] h34, memo4_eq B 12 1 h8z33 [h8w1, h8w2, h8w3, h8w4, h8w35, h8w5, h8w6, h8w7, h8w8, h8w9] h35, memo4_eq B 12 1 h8z1 [h8w36, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h36, memo4_eq B 12 1 h8z34 [h8w36, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h37, memo4_eq B 12 1 h8z35 [h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w37] h38, memo4_eq B 12 1 h8z36 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w37] h39, memo4_eq B 12 1 h8z3 [h8w38, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h40, memo4_eq B 12 1 h8z37 [h8w38, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h41, memo4_eq B 12 1 h8z5 [h8w39, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h42, memo4_eq B 12 1 h8z38 [h8w39, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h43, memo4_eq B 12 1 h8z26 [h8w40, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h44, memo4_eq B 12 1 h8z39 [h8w40, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h45, memo4_eq B 11 0 h8z40 [h8w41, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h46, memo4_eq B 11 0 h8z41 [h8w41, h8w2, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] h47, memo4_eq B 11 0 h8z42 [h8w2, h8w3, h8w4, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9] h48, memo4_eq B 11 0 h8z43 [h8w2, h8w3, h8w4, h8w42, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9] h49, memo4_eq B 11 0 h8z44 [h8w2, h8w44, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h50, memo4_eq B 11 0 h8z45 [h8w2, h8w44, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] h51, memo4_eq B 11 0 h8z46 [h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9] h52, memo4_eq B 11 0 h8z47 [h8w2, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9] h53, memo4_eq B 11 0 h8z48 [h8w2, h8w3, h8w46, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h54, memo4_eq B 11 0 h8z49 [h8w2, h8w3, h8w46, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] h55, memo4_eq B 11 0 h8z50 [h8w2, h8w3, h8w4, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9] h56, memo4_eq B 11 0 h8z51 [h8w2, h8w3, h8w4, h8w42, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9] h57, memo4_eq B 11 0 h8z52 [h8w2, h8w3, h8w4, h8w48, h8w5, h8w6, h8w7, h8w8, h8w9] h58, memo4_eq B 11 0 h8z53 [h8w2, h8w3, h8w4, h8w48, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] h59, memo4_eq B 11 0 h8z54 [h8w2, h8w3, h8w4, h8w49, h8w5, h8w6, h8w7, h8w8, h8w9] h60, memo4_eq B 11 0 h8z55 [h8w2, h8w3, h8w4, h8w49, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] h61, memo4_eq B 11 0 h8z56 [h8w2, h8w3, h8w4, h8w50, h8w5, h8w6, h8w7, h8w8, h8w9] h62, memo4_eq B 11 0 h8z57 [h8w2, h8w3, h8w4, h8w50, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] h63, memo4_eq B 11 0 h8z58 [h8w2, h8w3, h8w4, h8w51, h8w5, h8w6, h8w7, h8w8, h8w9] h64, memo4_eq B 11 0 h8z59 [h8w2, h8w3, h8w4, h8w51, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] h65, memo4_eq B 11 0 h8z60 [h8w41, h8w1, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h66, memo4_eq B 11 0 h8z61 [h8w41, h8w1, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] h67, memo4_eq B 11 0 h8z41 [h8w41, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h68, memo4_eq B 11 0 h8z43 [h8w1, h8w2, h8w3, h8w4, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9] h69, memo4_eq B 11 0 h8z62 [h8w1, h8w2, h8w3, h8w4, h8w42, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9] h70, memo4_eq B 11 0 h8z45 [h8w1, h8w2, h8w44, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h71, memo4_eq B 11 0 h8z47 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9] h72, memo4_eq B 11 0 h8z63 [h8w1, h8w2, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9] h73, memo4_eq B 11 0 h8z49 [h8w1, h8w2, h8w3, h8w46, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h74, memo4_eq B 11 0 h8z51 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9] h75, memo4_eq B 11 0 h8z64 [h8w1, h8w2, h8w3, h8w4, h8w42, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9] h76, memo4_eq B 11 0 h8z53 [h8w1, h8w2, h8w3, h8w4, h8w48, h8w5, h8w6, h8w7, h8w8, h8w9] h77, memo4_eq B 11 0 h8z55 [h8w1, h8w2, h8w3, h8w4, h8w49, h8w5, h8w6, h8w7, h8w8, h8w9] h78, memo4_eq B 11 0 h8z60 [h8w1, h8w2, h8w3, h8w4, h8w50, h8w5, h8w6, h8w8, h8w9] h79, memo4_eq B 11 0 h8z61 [h8w1, h8w2, h8w3, h8w4, h8w50, h8w42, h8w5, h8w6, h8w8, h8w9] h80, memo4_eq B 11 0 h8z57 [h8w1, h8w2, h8w3, h8w4, h8w50, h8w5, h8w6, h8w7, h8w8, h8w9] h81, memo4_eq B 11 0 h8z59 [h8w1, h8w2, h8w3, h8w4, h8w51, h8w5, h8w6, h8w7, h8w8, h8w9] h82, memo4_eq B 11 0 h8z42 [h8w2, h8w3, h8w52, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h83, memo4_eq B 11 0 h8z43 [h8w1, h8w2, h8w3, h8w52, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h84, memo4_eq B 11 0 h8z65 [h8w1, h8w2, h8w3, h8w4, h8w53, h8w5, h8w6, h8w7, h8w8, h8w9] h85, memo4_eq B 11 0 h8z66 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w54, h8w8, h8w9] h86, memo4_eq B 11 0 h8z46 [h8w2, h8w55, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h87, memo4_eq B 11 0 h8z47 [h8w1, h8w2, h8w55, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h88, memo4_eq B 11 0 h8z67 [h8w1, h8w56, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h89, memo4_eq B 11 0 h8z65 [h8w1, h8w2, h8w3, h8w57, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h90, memo4_eq B 11 0 h8z68 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w58, h8w6, h8w7, h8w8, h8w9] h91, memo4_eq B 11 0 h8z50 [h8w59, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h92, memo4_eq B 11 0 h8z51 [h8w1, h8w59, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h93, memo4_eq B 11 0 h8z69 [h8w1, h8w60, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h94, memo4_eq B 11 0 h8z66 [h8w1, h8w2, h8w3, h8w61, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] h95, memo4_eq B 11 0 h8z68 [h8w1, h8w2, h8w3, h8w4, h8w62, h8w5, h8w6, h8w7, h8w8, h8w9] h96, memo4_eq B 11 0 h8z70 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w63, h8w8, h8w9] h97]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma grandchildren_outer (A B : Nat → Nat → Nat → List W → Bool) :
    look1F (cacheA A) (cacheB B) h8L h8M h8G 13 1 h8z71 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by
  rfl
lemma or_assemble
    (h0 : look1 h8L h8M h8G 14 13 12 1 h8z0 [h8w0, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h1 : look1 h8L h8M h8G 14 13 12 1 h8z1 [h8w1, h8w10, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h2 : look1 h8L h8M h8G 14 13 12 1 h8z2 [h8w1, h8w10, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h3 : look1 h8L h8M h8G 14 13 12 1 h8z3 [h8w11, h8w1, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h4 : look1 h8L h8M h8G 14 13 12 1 h8z4 [h8w11, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h5 : look1 h8L h8M h8G 14 13 12 1 h8z5 [h8w12, h8w1, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h6 : look1 h8L h8M h8G 14 13 12 1 h8z6 [h8w12, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h7 : look1 h8L h8M h8G 14 13 12 1 h8z7 [h8w1, h8w3, h8w4, h8w5, h8w6, h8w8, h8w9, h8w13] = false)
    (h8 : look1 h8L h8M h8G 14 13 12 1 h8z8 [h8w1, h8w14, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h9 : look1 h8L h8M h8G 14 13 12 1 h8z9 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w15] = false)
    (h10 : look1 h8L h8M h8G 14 13 12 1 h8z10 [h8w1, h8w2, h8w16, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h11 : look1 h8L h8M h8G 14 13 12 1 h8z11 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w17, h8w6, h8w7, h8w8, h8w9] = false)
    (h12 : look1 h8L h8M h8G 14 13 12 1 h8z12 [h8w1, h8w2, h8w18, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h13 : look1 h8L h8M h8G 14 13 12 1 h8z13 [h8w1, h8w2, h8w19, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h14 : look1 h8L h8M h8G 14 13 12 1 h8z14 [h8w1, h8w2, h8w20, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h15 : look1 h8L h8M h8G 14 13 12 1 h8z15 [h8w1, h8w2, h8w21, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h16 : look1 h8L h8M h8G 14 13 12 1 h8z16 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w22] = false)
    (h17 : look1 h8L h8M h8G 14 13 12 1 h8z17 [h8w1, h8w2, h8w3, h8w23, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h18 : look1 h8L h8M h8G 14 13 12 1 h8z18 [h8w1, h8w2, h8w3, h8w24, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h19 : look1 h8L h8M h8G 14 13 12 1 h8z19 [h8w1, h8w2, h8w3, h8w25, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h20 : look1 h8L h8M h8G 14 13 12 1 h8z20 [h8w1, h8w2, h8w3, h8w26, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h21 : look1 h8L h8M h8G 14 13 12 1 h8z21 [h8w1, h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h22 : look1 h8L h8M h8G 14 13 12 1 h8z3 [h8w1, h8w2, h8w3, h8w4, h8w28, h8w5, h8w6, h8w8, h8w9] = false)
    (h23 : look1 h8L h8M h8G 14 13 12 1 h8z22 [h8w1, h8w2, h8w3, h8w4, h8w28, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h24 : look1 h8L h8M h8G 14 13 12 1 h8z23 [h8w1, h8w2, h8w3, h8w4, h8w29, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h25 : look1 h8L h8M h8G 14 13 12 1 h8z5 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w30, h8w6, h8w8, h8w9] = false)
    (h26 : look1 h8L h8M h8G 14 13 12 1 h8z24 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w30, h8w6, h8w7, h8w8, h8w9] = false)
    (h27 : look1 h8L h8M h8G 14 13 12 1 h8z25 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w31, h8w6, h8w7, h8w8, h8w9] = false)
    (h28 : look1 h8L h8M h8G 14 13 12 1 h8z26 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w32, h8w8, h8w9] = false)
    (h29 : look1 h8L h8M h8G 14 13 12 1 h8z27 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w32, h8w7, h8w8, h8w9] = false)
    (h30 : look h8L h8M h8G 14 12 1 h8z28 [h8w2, h8w3, h8w33, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h31 : look h8L h8M h8G 14 12 1 h8z29 [h8w1, h8w2, h8w3, h8w33, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h32 : look h8L h8M h8G 14 12 1 h8z30 [h8w34, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h33 : look h8L h8M h8G 14 12 1 h8z31 [h8w34, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h34 : look h8L h8M h8G 14 12 1 h8z32 [h8w2, h8w3, h8w4, h8w35, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h35 : look h8L h8M h8G 14 12 1 h8z33 [h8w1, h8w2, h8w3, h8w4, h8w35, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h36 : look h8L h8M h8G 14 12 1 h8z1 [h8w36, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h37 : look h8L h8M h8G 14 12 1 h8z34 [h8w36, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h38 : look h8L h8M h8G 14 12 1 h8z35 [h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w37] = false)
    (h39 : look h8L h8M h8G 14 12 1 h8z36 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w37] = false)
    (h40 : look h8L h8M h8G 14 12 1 h8z3 [h8w38, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h41 : look h8L h8M h8G 14 12 1 h8z37 [h8w38, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h42 : look h8L h8M h8G 14 12 1 h8z5 [h8w39, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h43 : look h8L h8M h8G 14 12 1 h8z38 [h8w39, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h44 : look h8L h8M h8G 14 12 1 h8z26 [h8w40, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h45 : look h8L h8M h8G 14 12 1 h8z39 [h8w40, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h46 : look h8L h8M h8G 14 11 0 h8z40 [h8w41, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h47 : look h8L h8M h8G 14 11 0 h8z41 [h8w41, h8w2, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h48 : look h8L h8M h8G 14 11 0 h8z42 [h8w2, h8w3, h8w4, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h49 : look h8L h8M h8G 14 11 0 h8z43 [h8w2, h8w3, h8w4, h8w42, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h50 : look h8L h8M h8G 14 11 0 h8z44 [h8w2, h8w44, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h51 : look h8L h8M h8G 14 11 0 h8z45 [h8w2, h8w44, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h52 : look h8L h8M h8G 14 11 0 h8z46 [h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9] = false)
    (h53 : look h8L h8M h8G 14 11 0 h8z47 [h8w2, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9] = false)
    (h54 : look h8L h8M h8G 14 11 0 h8z48 [h8w2, h8w3, h8w46, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h55 : look h8L h8M h8G 14 11 0 h8z49 [h8w2, h8w3, h8w46, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h56 : look h8L h8M h8G 14 11 0 h8z50 [h8w2, h8w3, h8w4, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9] = false)
    (h57 : look h8L h8M h8G 14 11 0 h8z51 [h8w2, h8w3, h8w4, h8w42, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9] = false)
    (h58 : look h8L h8M h8G 14 11 0 h8z52 [h8w2, h8w3, h8w4, h8w48, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h59 : look h8L h8M h8G 14 11 0 h8z53 [h8w2, h8w3, h8w4, h8w48, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h60 : look h8L h8M h8G 14 11 0 h8z54 [h8w2, h8w3, h8w4, h8w49, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h61 : look h8L h8M h8G 14 11 0 h8z55 [h8w2, h8w3, h8w4, h8w49, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h62 : look h8L h8M h8G 14 11 0 h8z56 [h8w2, h8w3, h8w4, h8w50, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h63 : look h8L h8M h8G 14 11 0 h8z57 [h8w2, h8w3, h8w4, h8w50, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h64 : look h8L h8M h8G 14 11 0 h8z58 [h8w2, h8w3, h8w4, h8w51, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h65 : look h8L h8M h8G 14 11 0 h8z59 [h8w2, h8w3, h8w4, h8w51, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h66 : look h8L h8M h8G 14 11 0 h8z60 [h8w41, h8w1, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h67 : look h8L h8M h8G 14 11 0 h8z61 [h8w41, h8w1, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h68 : look h8L h8M h8G 14 11 0 h8z41 [h8w41, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h69 : look h8L h8M h8G 14 11 0 h8z43 [h8w1, h8w2, h8w3, h8w4, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h70 : look h8L h8M h8G 14 11 0 h8z62 [h8w1, h8w2, h8w3, h8w4, h8w42, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h71 : look h8L h8M h8G 14 11 0 h8z45 [h8w1, h8w2, h8w44, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h72 : look h8L h8M h8G 14 11 0 h8z47 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9] = false)
    (h73 : look h8L h8M h8G 14 11 0 h8z63 [h8w1, h8w2, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9] = false)
    (h74 : look h8L h8M h8G 14 11 0 h8z49 [h8w1, h8w2, h8w3, h8w46, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h75 : look h8L h8M h8G 14 11 0 h8z51 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9] = false)
    (h76 : look h8L h8M h8G 14 11 0 h8z64 [h8w1, h8w2, h8w3, h8w4, h8w42, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9] = false)
    (h77 : look h8L h8M h8G 14 11 0 h8z53 [h8w1, h8w2, h8w3, h8w4, h8w48, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h78 : look h8L h8M h8G 14 11 0 h8z55 [h8w1, h8w2, h8w3, h8w4, h8w49, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h79 : look h8L h8M h8G 14 11 0 h8z60 [h8w1, h8w2, h8w3, h8w4, h8w50, h8w5, h8w6, h8w8, h8w9] = false)
    (h80 : look h8L h8M h8G 14 11 0 h8z61 [h8w1, h8w2, h8w3, h8w4, h8w50, h8w42, h8w5, h8w6, h8w8, h8w9] = false)
    (h81 : look h8L h8M h8G 14 11 0 h8z57 [h8w1, h8w2, h8w3, h8w4, h8w50, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h82 : look h8L h8M h8G 14 11 0 h8z59 [h8w1, h8w2, h8w3, h8w4, h8w51, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h83 : look h8L h8M h8G 14 11 0 h8z42 [h8w2, h8w3, h8w52, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h84 : look h8L h8M h8G 14 11 0 h8z43 [h8w1, h8w2, h8w3, h8w52, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h85 : look h8L h8M h8G 14 11 0 h8z65 [h8w1, h8w2, h8w3, h8w4, h8w53, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h86 : look h8L h8M h8G 14 11 0 h8z66 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w54, h8w8, h8w9] = false)
    (h87 : look h8L h8M h8G 14 11 0 h8z46 [h8w2, h8w55, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h88 : look h8L h8M h8G 14 11 0 h8z47 [h8w1, h8w2, h8w55, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h89 : look h8L h8M h8G 14 11 0 h8z67 [h8w1, h8w56, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h90 : look h8L h8M h8G 14 11 0 h8z65 [h8w1, h8w2, h8w3, h8w57, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h91 : look h8L h8M h8G 14 11 0 h8z68 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w58, h8w6, h8w7, h8w8, h8w9] = false)
    (h92 : look h8L h8M h8G 14 11 0 h8z50 [h8w59, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h93 : look h8L h8M h8G 14 11 0 h8z51 [h8w1, h8w59, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h94 : look h8L h8M h8G 14 11 0 h8z69 [h8w1, h8w60, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h95 : look h8L h8M h8G 14 11 0 h8z66 [h8w1, h8w2, h8w3, h8w61, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h96 : look h8L h8M h8G 14 11 0 h8z68 [h8w1, h8w2, h8w3, h8w4, h8w62, h8w5, h8w6, h8w7, h8w8, h8w9] = false)
    (h97 : look h8L h8M h8G 14 11 0 h8z70 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w63, h8w8, h8w9] = false)
    : look1 h8L h8M h8G 14 14 13 1 h8z71 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by
  rw [show (14 : Nat) = 13 + 1 from rfl, look1_succ]
  have hout := grandchildren_outer (look1 h8L h8M h8G 14 13) (look h8L h8M h8G 14)
  have ha := cacheA_eq (look1 h8L h8M h8G 14 13) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29
  have hb := cacheB_eq (look h8L h8M h8G 14) h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 h45 h46 h47 h48 h49 h50 h51 h52 h53 h54 h55 h56 h57 h58 h59 h60 h61 h62 h63 h64 h65 h66 h67 h68 h69 h70 h71 h72 h73 h74 h75 h76 h77 h78 h79 h80 h81 h82 h83 h84 h85 h86 h87 h88 h89 h90 h91 h92 h93 h94 h95 h96 h97
  simpa only [ha,hb] using hout
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf0 : look1 h8L h8M h8G 14 13 12 1 h8z0 [h8w0, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf1 : look1 h8L h8M h8G 14 13 12 1 h8z1 [h8w1, h8w10, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf2 : look1 h8L h8M h8G 14 13 12 1 h8z2 [h8w1, h8w10, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf3 : look1 h8L h8M h8G 14 13 12 1 h8z3 [h8w11, h8w1, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf4 : look1 h8L h8M h8G 14 13 12 1 h8z4 [h8w11, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf5 : look1 h8L h8M h8G 14 13 12 1 h8z5 [h8w12, h8w1, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf6 : look1 h8L h8M h8G 14 13 12 1 h8z6 [h8w12, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf7 : look1 h8L h8M h8G 14 13 12 1 h8z7 [h8w1, h8w3, h8w4, h8w5, h8w6, h8w8, h8w9, h8w13] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf8 : look1 h8L h8M h8G 14 13 12 1 h8z8 [h8w1, h8w14, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf9 : look1 h8L h8M h8G 14 13 12 1 h8z9 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w15] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf10 : look1 h8L h8M h8G 14 13 12 1 h8z10 [h8w1, h8w2, h8w16, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf11 : look1 h8L h8M h8G 14 13 12 1 h8z11 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w17, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf12 : look1 h8L h8M h8G 14 13 12 1 h8z12 [h8w1, h8w2, h8w18, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf13 : look1 h8L h8M h8G 14 13 12 1 h8z13 [h8w1, h8w2, h8w19, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf14 : look1 h8L h8M h8G 14 13 12 1 h8z14 [h8w1, h8w2, h8w20, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf15 : look1 h8L h8M h8G 14 13 12 1 h8z15 [h8w1, h8w2, h8w21, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf16 : look1 h8L h8M h8G 14 13 12 1 h8z16 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w22] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf17 : look1 h8L h8M h8G 14 13 12 1 h8z17 [h8w1, h8w2, h8w3, h8w23, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf18 : look1 h8L h8M h8G 14 13 12 1 h8z18 [h8w1, h8w2, h8w3, h8w24, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf19 : look1 h8L h8M h8G 14 13 12 1 h8z19 [h8w1, h8w2, h8w3, h8w25, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf20 : look1 h8L h8M h8G 14 13 12 1 h8z20 [h8w1, h8w2, h8w3, h8w26, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf21 : look1 h8L h8M h8G 14 13 12 1 h8z21 [h8w1, h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf22 : look1 h8L h8M h8G 14 13 12 1 h8z3 [h8w1, h8w2, h8w3, h8w4, h8w28, h8w5, h8w6, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf23 : look1 h8L h8M h8G 14 13 12 1 h8z22 [h8w1, h8w2, h8w3, h8w4, h8w28, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf24 : look1 h8L h8M h8G 14 13 12 1 h8z23 [h8w1, h8w2, h8w3, h8w4, h8w29, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf25 : look1 h8L h8M h8G 14 13 12 1 h8z5 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w30, h8w6, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf26 : look1 h8L h8M h8G 14 13 12 1 h8z24 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w30, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf27 : look1 h8L h8M h8G 14 13 12 1 h8z25 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w31, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf28 : look1 h8L h8M h8G 14 13 12 1 h8z26 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w32, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf29 : look1 h8L h8M h8G 14 13 12 1 h8z27 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w32, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf30 : look h8L h8M h8G 14 12 1 h8z28 [h8w2, h8w3, h8w33, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf31 : look h8L h8M h8G 14 12 1 h8z29 [h8w1, h8w2, h8w3, h8w33, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf32 : look h8L h8M h8G 14 12 1 h8z30 [h8w34, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf33 : look h8L h8M h8G 14 12 1 h8z31 [h8w34, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf34 : look h8L h8M h8G 14 12 1 h8z32 [h8w2, h8w3, h8w4, h8w35, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf35 : look h8L h8M h8G 14 12 1 h8z33 [h8w1, h8w2, h8w3, h8w4, h8w35, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf36 : look h8L h8M h8G 14 12 1 h8z1 [h8w36, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf37 : look h8L h8M h8G 14 12 1 h8z34 [h8w36, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf38 : look h8L h8M h8G 14 12 1 h8z35 [h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w37] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf39 : look h8L h8M h8G 14 12 1 h8z36 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w37] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf40 : look h8L h8M h8G 14 12 1 h8z3 [h8w38, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf41 : look h8L h8M h8G 14 12 1 h8z37 [h8w38, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf42 : look h8L h8M h8G 14 12 1 h8z5 [h8w39, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf43 : look h8L h8M h8G 14 12 1 h8z38 [h8w39, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf44 : look h8L h8M h8G 14 12 1 h8z26 [h8w40, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf45 : look h8L h8M h8G 14 12 1 h8z39 [h8w40, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf46 : look h8L h8M h8G 14 11 0 h8z40 [h8w41, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf47 : look h8L h8M h8G 14 11 0 h8z41 [h8w41, h8w2, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf48 : look h8L h8M h8G 14 11 0 h8z42 [h8w2, h8w3, h8w4, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf49 : look h8L h8M h8G 14 11 0 h8z43 [h8w2, h8w3, h8w4, h8w42, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf50 : look h8L h8M h8G 14 11 0 h8z44 [h8w2, h8w44, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf51 : look h8L h8M h8G 14 11 0 h8z45 [h8w2, h8w44, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf52 : look h8L h8M h8G 14 11 0 h8z46 [h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf53 : look h8L h8M h8G 14 11 0 h8z47 [h8w2, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf54 : look h8L h8M h8G 14 11 0 h8z48 [h8w2, h8w3, h8w46, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf55 : look h8L h8M h8G 14 11 0 h8z49 [h8w2, h8w3, h8w46, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf56 : look h8L h8M h8G 14 11 0 h8z50 [h8w2, h8w3, h8w4, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf57 : look h8L h8M h8G 14 11 0 h8z51 [h8w2, h8w3, h8w4, h8w42, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf58 : look h8L h8M h8G 14 11 0 h8z52 [h8w2, h8w3, h8w4, h8w48, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf59 : look h8L h8M h8G 14 11 0 h8z53 [h8w2, h8w3, h8w4, h8w48, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf60 : look h8L h8M h8G 14 11 0 h8z54 [h8w2, h8w3, h8w4, h8w49, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf61 : look h8L h8M h8G 14 11 0 h8z55 [h8w2, h8w3, h8w4, h8w49, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf62 : look h8L h8M h8G 14 11 0 h8z56 [h8w2, h8w3, h8w4, h8w50, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf63 : look h8L h8M h8G 14 11 0 h8z57 [h8w2, h8w3, h8w4, h8w50, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf64 : look h8L h8M h8G 14 11 0 h8z58 [h8w2, h8w3, h8w4, h8w51, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf65 : look h8L h8M h8G 14 11 0 h8z59 [h8w2, h8w3, h8w4, h8w51, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf66 : look h8L h8M h8G 14 11 0 h8z60 [h8w41, h8w1, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf67 : look h8L h8M h8G 14 11 0 h8z61 [h8w41, h8w1, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf68 : look h8L h8M h8G 14 11 0 h8z41 [h8w41, h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf69 : look h8L h8M h8G 14 11 0 h8z43 [h8w1, h8w2, h8w3, h8w4, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf70 : look h8L h8M h8G 14 11 0 h8z62 [h8w1, h8w2, h8w3, h8w4, h8w42, h8w43, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf71 : look h8L h8M h8G 14 11 0 h8z45 [h8w1, h8w2, h8w44, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf72 : look h8L h8M h8G 14 11 0 h8z47 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf73 : look h8L h8M h8G 14 11 0 h8z63 [h8w1, h8w2, h8w3, h8w4, h8w42, h8w5, h8w6, h8w7, h8w8, h8w45, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf74 : look h8L h8M h8G 14 11 0 h8z49 [h8w1, h8w2, h8w3, h8w46, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf75 : look h8L h8M h8G 14 11 0 h8z51 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf76 : look h8L h8M h8G 14 11 0 h8z64 [h8w1, h8w2, h8w3, h8w4, h8w42, h8w5, h8w47, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf77 : look h8L h8M h8G 14 11 0 h8z53 [h8w1, h8w2, h8w3, h8w4, h8w48, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf78 : look h8L h8M h8G 14 11 0 h8z55 [h8w1, h8w2, h8w3, h8w4, h8w49, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf79 : look h8L h8M h8G 14 11 0 h8z60 [h8w1, h8w2, h8w3, h8w4, h8w50, h8w5, h8w6, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf80 : look h8L h8M h8G 14 11 0 h8z61 [h8w1, h8w2, h8w3, h8w4, h8w50, h8w42, h8w5, h8w6, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf81 : look h8L h8M h8G 14 11 0 h8z57 [h8w1, h8w2, h8w3, h8w4, h8w50, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf82 : look h8L h8M h8G 14 11 0 h8z59 [h8w1, h8w2, h8w3, h8w4, h8w51, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf83 : look h8L h8M h8G 14 11 0 h8z42 [h8w2, h8w3, h8w52, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf84 : look h8L h8M h8G 14 11 0 h8z43 [h8w1, h8w2, h8w3, h8w52, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf85 : look h8L h8M h8G 14 11 0 h8z65 [h8w1, h8w2, h8w3, h8w4, h8w53, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf86 : look h8L h8M h8G 14 11 0 h8z66 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w54, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf87 : look h8L h8M h8G 14 11 0 h8z46 [h8w2, h8w55, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf88 : look h8L h8M h8G 14 11 0 h8z47 [h8w1, h8w2, h8w55, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf89 : look h8L h8M h8G 14 11 0 h8z67 [h8w1, h8w56, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf90 : look h8L h8M h8G 14 11 0 h8z65 [h8w1, h8w2, h8w3, h8w57, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf91 : look h8L h8M h8G 14 11 0 h8z68 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w58, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf92 : look h8L h8M h8G 14 11 0 h8z50 [h8w59, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf93 : look h8L h8M h8G 14 11 0 h8z51 [h8w1, h8w59, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf94 : look h8L h8M h8G 14 11 0 h8z69 [h8w1, h8w60, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf95 : look h8L h8M h8G 14 11 0 h8z66 [h8w1, h8w2, h8w3, h8w61, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf96 : look h8L h8M h8G 14 11 0 h8z68 [h8w1, h8w2, h8w3, h8w4, h8w62, h8w5, h8w6, h8w7, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8leaf97 : look h8L h8M h8G 14 11 0 h8z70 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w63, h8w8, h8w9] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h8and_complete : look1 h8L h8M h8G 14 14 13 1 h8z7 [h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h8w13] = false := by decide +kernel
def h8or_complete : look1 h8L h8M h8G 14 14 13 1 h8z71 [h8w1, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9] = false :=
  or_assemble h8leaf0 h8leaf1 h8leaf2 h8leaf3 h8leaf4 h8leaf5 h8leaf6 h8leaf7 h8leaf8 h8leaf9 h8leaf10 h8leaf11 h8leaf12 h8leaf13 h8leaf14 h8leaf15 h8leaf16 h8leaf17 h8leaf18 h8leaf19 h8leaf20 h8leaf21 h8leaf22 h8leaf23 h8leaf24 h8leaf25 h8leaf26 h8leaf27 h8leaf28 h8leaf29 h8leaf30 h8leaf31 h8leaf32 h8leaf33 h8leaf34 h8leaf35 h8leaf36 h8leaf37 h8leaf38 h8leaf39 h8leaf40 h8leaf41 h8leaf42 h8leaf43 h8leaf44 h8leaf45 h8leaf46 h8leaf47 h8leaf48 h8leaf49 h8leaf50 h8leaf51 h8leaf52 h8leaf53 h8leaf54 h8leaf55 h8leaf56 h8leaf57 h8leaf58 h8leaf59 h8leaf60 h8leaf61 h8leaf62 h8leaf63 h8leaf64 h8leaf65 h8leaf66 h8leaf67 h8leaf68 h8leaf69 h8leaf70 h8leaf71 h8leaf72 h8leaf73 h8leaf74 h8leaf75 h8leaf76 h8leaf77 h8leaf78 h8leaf79 h8leaf80 h8leaf81 h8leaf82 h8leaf83 h8leaf84 h8leaf85 h8leaf86 h8leaf87 h8leaf88 h8leaf89 h8leaf90 h8leaf91 h8leaf92 h8leaf93 h8leaf94 h8leaf95 h8leaf96 h8leaf97
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def hash29_complete : chk [] rt 0 14 1 536870912 0 = false := by
  rw [chk_expand]
  exact assemble _ h8and_complete h8or_complete

end hash29Memo
noncomputable section hash95Memo
def h95w0 : W := ⟨0x1fffff000000000000000000000000000000000000000000000000000000000000000124a8040008000000800200200000000000200004000800000040000100100000010004004000020000000000000000003f0000800000080000410400000000000000000000000000000000000000000000000b6d580000000000000000000000000000000000000000000000000000000000000000000000000000429421085294210a, 0x842108421084210842108421084210842108421084210000000000000000000000000084210842108421080000000000000000000840000000, 0x0, 0x842108421084210842108421084210842108421084210000000000000000000000000084210842108421080000000000000000000840000000, 0x0⟩

def h95w1 : W := ⟨0x7ffffc0000000000000000000000000000000000000000000000000000000000020042004400248040010010000000000010000200040000002000008008000000800200200001000000000000000000080000d7000000000000000000000000000040000004000082000000000000000000000c008000c0016d000000000000000000000000000000000000000000000000000000000000000000d034090244912058, 0x842108421084210842108421080200002000021080000800008420000210800008420084210842000400000200002000021080000800008000, 0x0, 0x842108421084210842108421080200002000021080000800008420000210800008420084210842000400000200002000021080000800008000, 0x0⟩

def h95w2 : W := ⟨0x3ffffe000000000000000000000000000000000000000000000040040008000000800200200000200808400208041000000080000200200000020008008000040000000000000000001000000000000040004141d400000000000000000000000000001000010040000000000180000000000000000000000100c030100046000c0000000000000000000000000000000000000018c218c421a5002, 0x842108400000200002000401084210842108421084210000100020084000802100421080000002108421080000040000400080210040000001, 0x0, 0x842108400000200002000401084210842108421084210000100020084000802100421080000002108421080000040000400080210040000001, 0x0⟩

def h95w3 : W := ⟨0x20100080000010000040040000000400000880000060822000030020080200020000000000000010000000000000000000100000000000000000000000000000200000000000db7ff882c890640505411, 0x2000401000210002108401080200042000421080210800108420084210802108421000010002000400080200042000421080210000008001, 0x0, 0x2000401000210002108401080200042000421080210800108420084210802108421000010002000400080200042000421080210000008001, 0x0⟩

def h95w4 : W := ⟨0x30c0007800030e0000410300000107000010e000021800000000c000000000000c000b6002affedffc000000000000000000000000000000000000000000000000000000000000000000005631294ac6352948, 0x842108421084210842108421084000000000000000000842100000000000000000000084210842000000004000000000000000000800000000, 0x0, 0x842108421084210842108421084000000000000000000842100000000000000000000084210842000000004000000000000000000800000000, 0x0⟩

def h95w5 : W := ⟨0x1fffff7ffffdf7ffffbef8000000fbffffef7ffffde000000000000000000000000005b6a957b86f702480f603d83d82aad4d500398007300e60da88770121dc1dc04901dc0770770003b000000000000000003ff8fcffe3f3effc7e7df7f81f81f7f1ff9efe3ff3df87f8b2c4fc3fc5acab2dcf8fcb6d5aaffedffd6d55ffd7ff7ff555adab00000000000001b55affeb6bffbffadaabffaffeffe00000ffff6ffffffdefff, 0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0⟩

def h95w6 : W := ⟨0x7ffffbef800000000000000000000000000000000000000000000000490000080010000001000400402aa94950008000100020000001000004004000000400100100000800000000000000000300000000000083c007df018000000100000020000000000000000000000000000000b6000000000000000000000000555adab0000000000000000000000000000000000000000000000006318638c631c618c, 0x842108420000000000000000004210842108421084210842100000000000000000000080000000108421084000000000000000000040000000, 0x0, 0x842108420000000000000000004210842108421084210842100000000000000000000080000000108421084000000000000000000040000000, 0x0⟩

def h95w7 : W := ⟨0x1fffff00000007ffffbefbffffeefbffffef7ffffde000000000000000000000000005b4ad14f829f000009e02782782aad6d580af8025f04be0da885f01217c17c049017c05f05f0002f000000000000000003fc7fcf81ff30e3ffe7df71fff9df71fff9ee3fff3d87ff871ccc3ffc39c671ccc7fcb6d5aaffedffc0000000000000555adab557ff56ffedffdb55affeb6bffbffadaabffaffeffe000007fff7feffffffdef, 0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0, 0x4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x0⟩

def h95w8 : W := ⟨0x7ffffc000000000000000000000000000000000008202000000200080080000040000080001000204000010000040040490008002002000010000000000000000000008050020000204020800010008000c00842338000064030c400200000000000080000008000c0000000000000000404018000000000000001805affe000000002da0000000000000000783a0b074551644d, 0x2000021000010000108400004200002000021080000842108420000210800008420000010000000400004200002000021080000000008000, 0x0, 0x2000021000010000108400004200002000021080000842108420000210800008420000010000000400004200002000021080000000008000, 0x0⟩

def h95w9 : W := ⟨0x7ffffc07ffffbef8000000fbffffef7ffffdefffff7df7000000000000000004920152bc6578b68057015c15c2aad4d52a19e003380670daad37c120de0de16d00de0378378491bc000000000000000038c4feff13fb0e3e7f7df31e1fd1f719ffdee33ffbdc67fefbeec23ff18e238cec4feb6c02affedffd6d00000000000555adab557ff000000001b55affeb6bffbffadaabffaffeffedb7ffff7fffefeffdfdfd, 0x800000000000000000000000000000000000000000000000000000000000000000000, 0x0, 0x800000000000000000000000000000000000000000000000000000000000000000000, 0x0⟩

def h95w10 : W := ⟨0x2400009000041204101804801000148200049040008800000016400c0300c0024000000000000000000000000000100c03000000000000000100000868003ff80288002000ffe000000d292dee4a584421, 0x420000200002000401084000040000400080210842100020084000802100421000000002000000084000040000400080210000000001, 0x0, 0x420000200002000401084000040000400080210842100020084000802100421000000002000000084000040000400080210000000001, 0x0⟩

def h95w11 : W := ⟨0x7ffffbefbffffe0fbffffef7ffffde0000000007ffff81f07c0f00004900510fa21f400221e887a07b2aad6d5808d9231b46368da881f25347d07d849447d11f41f6248f3000000000000000031c8fe7923fb2e7c7f7df73d5fc1f731ffdee63ffbd887fe38e6e53ff1be2f8dec8feb601aaffedffc01440010007ff555adab0100046000c001b55affeb6bffbffadaabffaffeffedb7ffffffefffef7ffdff, 0x100000000000000000000000000000000000000000000000000000000000000000, 0x0, 0x100000000000000000000000000000000000000000000000000000000000000000, 0x0⟩

def h95w12 : W := ⟨0x7ffffbef8000000fbffffef7ffffdefffff7c007ffffbdf7000000004900110be217c902a17c05e05e2aad4d52809d2913e0278daac17a5b05f05f169545f817c17c6c0ba000000000000000034e2fc7c8bf38f3d7e7df3999f89f795ff9ef2bff3de57fcf8c4f1bfe7bee30cce2fcb6102affedffd6055ffc000000555adab5000056ffe0001b55affeb6bffbffadaabffaffeffed80007fffeffffffffffd, 0x40000000000000000000000000000000000000000000000000000000000000000000, 0x0, 0x40000000000000000000000000000000000000000000000000000000000000000000, 0x0⟩

def h95w13 : W := ⟨0x7ffffbefbffffee000000000000000000000000000000000000000004900400c0018000001800600602aa9695808e0021c0438000001800006006000000600180180000c00000000000000000000700001c00003f803cf01fe01c001e000003c000007800410803c0021044100070000000000000000000000000000555adab557ff56ffedffc000000000000000000000000000000000021085284210a5084, 0x842108400000000000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x0, 0x842108400000000000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x0⟩

def h95w14 : W := ⟨0x7ffffc0fffff7df70000000000000000000000000c2028920003000c00c00000402a00e000180030402501c0000600616d000a00280284901c000000000000000000048200120800224120800610508008c04803338800664679ee02203002008020482000000000000000000000000004040180557ff000000001805affe000000002da00000000000db7ff280a920501405405, 0x2000001000010000108400000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x0, 0x2000001000010000108400000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x0⟩

def h95w15 : W := ⟨0x7ffffbef8000000fbffffef7ffffde000000000000000000000000004900110b8217000001600580582aad4d500098001300260da881701205c05c049005c0170170000b000000000000000000000fc0003f0003c7e3cf0181f80f011ff8e023ff1c007f830c4003fc18c230cc00fc00000000000000000000000000555adab00000000000001b55affeb6bffbffadaabffaffeffe00000294a46a52948c4a5, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x0, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x0⟩

def h95w16 : W := ⟨0x7ffffbe00000000fbffffef0000000000000000000000000000000004800110b0014000001400500502aad400000900012002409a881601205805800000500140140000a000000000000000000000e0000380003c703c00101c00f011fc0e003c000007802084003c01080208800e000000000000000000000000000555ac0000000000000001b55affeb6bffbff8000000000000000000094a422129484021, 0x800000021084200000000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 0x0, 0x800000021084200000000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 0x0⟩

def h95w17 : W := ⟨0x3ffffe00000000000000000000000007ffff81f07c0f0000000040042008400220888220230000200808412308461080000082414210218004421108408624843000000000000000000002600009800041304101d44c0100014c200049840008e08220116701e0780e0026000000000000000000000000000100c030100046000c0000100000868003ff80288002000ffedb7ff090884a4084a5421, 0x400000200002000401080000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 0x0, 0x400000200002000401080000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 0x0⟩

def h95w18 : W := ⟨0x7ffffdf00000000000000000000000000000000000000000000000000000000002004300460024806001801800000000001000020004000000200000800800000080020020000100000000000000000000f8007fe003e7c0000003e0000107e00010fc00021f80008200fc00042088210f80000002affedffd6d55ffd7ff7ff00000000000000000000000000000000000000000000000000000009421085284210a50, 0x842108421084210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 0x0, 0x842108421084210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 0x0⟩

def h95w19 : W := ⟨0xfbffffef7ffffde0000000000000000000000000000001103820700000060018018000404000018000300060da880701201c01c049001c007007000030000000000000000000c0fc7803f306007e0003001f81f701ff9ee03ff3d807f830c4c03fc18c230ccc0fc00002affedffc0000000000000000000000000000000001b55affeb6bffbffadaabffaffeffe000001c630c638c618c61, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x0, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x0⟩

def h95w20 : W := ⟨0x7ffff81f07c0f0000000000002000400220088020030000000000012100420080000002414010018004401100400624803000000000000000000082601209820401300002004c0102014c204049840808e08222416702e0b81e0826000000000000001440010007ff0000000000000000000000100000868003ff80288002000ffedb7ff8c218c7208400431, 0x400000200002000401080000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 0x0, 0x400000200002000401080000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 0x0⟩

def h95w21 : W := ⟨0x7ffffbef8000000fbffffef000001e000000000000000000000000004900110b0015000001400500502aad495000900012002409a881601205805800000540150150000a0000000000000000030c07c2801f30e1c3e5d73180f8177113f96a00c73d801b80000c01fc18c230ccc07cb60022ffe1ffc0000000000000151ac2b000000000000003500000b6bffbff800abffaffeffe00000074164e8aa2c89a0, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x0, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x0⟩

def h95w22 : W := ⟨0x3ffffe00000000000000000000000007ffff81f07c0f0000000040042008400220888220230000200808412308461080000082414210218004421108408624843000000000000000001082400209020441204143944801020148204041040808800002516403c0f01c0824000180000000000440010007ff0100c030000046000c0000100000868003ff80088002000ffe00000058124f80a0a0022, 0x400000200002000401080000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 0x0, 0x400000200002000401080000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 0x0⟩

def h95w23 : W := ⟨0x1fffff7ffffdf00000000000000000000000000000000000000000000000000000000126a847004e002480e00380380000000000300006000c00000060000180180000018006006000030000000000000000000f380087e000e1c0000004e0000000e000001c000007800082003c00042088210380000d58000000016d55ffd7ff7ff00000000000000000000000000000000000000000000000000000008084001010800212, 0x842108421084210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 0x0, 0x842108421084210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 0x0⟩

def h95w24 : W := ⟨0x1fffff7ffffdf000000003ffffee000000000000000fffff7df77ffffbdf77def7fff126ac47474e8eb6aae9eba7ba78000200aab67ab6cf6d9e002568f495a3da3d2455a3d68f68f6db4f80000000000000000f3f0287fc08e1c3810004e7e05c00ee00401dc00807f806cb2a3fc03632ccb123f0200d58000000016d55ffd7ff7ff0000000557ff56ffedffc00000000000000000000000000000db7ff8084901010821212, 0x0, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x0⟩

def h95w25 : W := ⟨0x1fffff7ffffdf000000003ffffee000000000000000fffff7df77ffffbdf77def7fff126ac47474e8eb6aae9eba7ba78000200aab67ab6cf6d9e002568f495a3da3d2455a3d68f68f6db4f80000000000000003fff02fffc0befc3814107e7e05d07ee0050fdc00a1ff806cb2affc03632ccb12ff02b6d5aaffedffd6d55ffd7ff7ff0000000557ff56ffedffc00000000000000000000000000000db7ffd6b5b95ad6b73b5a, 0x0, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x0⟩

def h95w26 : W := ⟨0x1fffff0000000000000003ffffee00000000000000000000000000000000000000000124ac044008800000880220220000020080a60024c04980000048000120120000012004804800024000000000000000000f0700801c00000380000407e01c000e000001c000007800410803c0021044100070000d580000000000000000000000000000557ff56ffedffc00000000000000000000000000000000000084100010821002, 0x842108400000000000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x0, 0x842108400000000000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x0⟩

def h95w27 : W := ⟨0x1fffff7ffffdf7ffffbefbffffee000000000000000fffff7df77ffffbdf77def7fff5b6ac47c74f8eb6aaf9ebe7be7aaa9695aabe7ab7cf6f9e002578f495e3de3d2455e3d78f78f6dbcf80000000000000003f3f0287fc08e9ff817df4ffe05c00fe00401fc00807f806cb2a3fc03632ccb123f02b6d58000000016d55ffd7ff7ff555adab557ff56ffedffc00000000000000000000000000000db7ffe39cf39c739e739e, 0x0, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x0⟩

def h95w28 : W := ⟨0x7ffffc0000000000000000000000000000000fffff7df7000000000000000000020042044408b68041010410400000002a106002080410002520c00082082124008202082084910c0000000000000000080402871008000201000006005000080040010008046006cb2a0200300200802040200c00000000016d000000000000000000557ff00000000000000000000000000000000000000db7ff8004900000801010, 0x2000001000010000108400000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x0, 0x2000001000010000108400000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x0⟩

def h95w29 : W := ⟨0x1fffff7ffffdf000000003ffffee000000007ffffc0fffff7df77ffffbdf77def7fff126ac474f6eaeb6aaebebafbaf8000240aab6fab6df6dbe402569f495a7da7d6d55abd6af6af6db5f80000000000000000f3f82d7fe08e1e3c12084e7f05c80eec0485ff38807fe46fbee3fe03632ccb123f8200d588000c0016d55ffd7ff7ff4040180557ff56ffedffd805affe000000002da00000000000db7fff8be9b1755d3765f, 0x0, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x0⟩

def h95w30 : W := ⟨0x1fffff7ffffdf7ffffbe03ffffeefbffffef0000000fffff7df77ffffbdf77def7fff5a6ad57f74fceb6aafdebf7bf7aaad600aabf7ab7ef6fde9aad7ef5b5fbdfbd2455f3d7cf7cf6dbef80000000000000002fbfe2e7ff8aedfff17c06f7fc5df6fffc5e9dfc0817ff86ebaebffc373aceb9abfe2b0d5aaffe00016d55ffd7ff7ff555ac00557ff56ffedffdb55affeb6bffbff80000000000000db7ffdbdfda7b7bfb5b7b, 0x0, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x0⟩

def h95w31 : W := ⟨0x3ffffe00000000000000000000000007ffff81f07c0f000000004004200840022088822023000020080841230846108000008241421021800442110840862484300000000000000000108020120082040010004254040002000400400080080060822250030320c8120802000180000000001440010007ff00000000100046000c00000000000000000000000000000000db7ff8084801000021012, 0x400000200002000401080000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 0x0, 0x400000200002000401080000040000400080210000100020084000802100421000000002000000080000040000400080210000000001, 0x0⟩

def h95w32 : W := ⟨0x1fffff7ffffdf000000003ffffee000000000000000fffff7df77ffffbdf77def7fff126ac47474e8eb6aae9eba7ba78000200aab67ab6cf6d9e002568f495a3da3d2455a3d68f68f6db4f80000000000000000f3f2687fc98e1c7930414ffe4dc10ee14c21dc49847f88ecb2a3fd6763ecfb1e3f2600d58000000016d55ffd7ff7ff0100c03557ff56ffedffc0100000868003ff80288002000ffedb7ff8dadbdfe5ada5633, 0x0, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x0⟩

def h95w33 : W := ⟨0x1fffff7ffffdf000000003ffffee03ffffe00000000fffff7df77ffffbdf77def7fff126ac57674eceb6aaedebb7bb78004200aab77ab6ef6dde082d6cf5b5b3db3d2455b3d6cf6cf6db6f80000000000000000f3f1287fc48e1d3891044e7e25c44ffb2401dc24907fc66fb2a3fd337beecb123f1200d58200000016d55ffd7ff7ff1018020557ff56ffedffc3058000b60000002c0abff8000000db7ffb9cef7185296b7bf, 0x0, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x0⟩

def h95w34 : W := ⟨0x1fffff7ffffdf7ffff80fbffffeef80000007ffffdefffff7df77ffffbdf77def7fff536ad47cf6fbeb6aafbebefbefaa802d5aabefab7df6fbed2a579f495e7de7d6d55efd7bf7bf6dbdf80000000000000001f7f1e9ffc79ebff8f01f5efe3ddf1ef03c07fe3fbcff87edb6a7fc3f6b6edb567f1e86d5a0000dffd6d55ffd7ff7ff55001ab557ff56ffedffdb500000000000002daabffaffeffedb7ffb6f6f7d69edefed6, 0x0, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x0⟩

def h95w35 : W := ⟨0x1fffff7ffffdf00000000000000000000000000000000000000000000000000000000126a847004e002480e00380380000000000300006000c00000060000180180000018006006000030000000000000000003ef000fec003cf80004103c0000107c00010f800021f00008200d800040080200f000b6d42affedffd6c11ffc7ff00000000000000000000000000000000000000000000000000000000005210000094a52b48, 0x842108421084210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 0x0, 0x842108421084210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 0x0⟩

def h95w36 : W := ⟨0x1fffff00000007ffffbef800000e000000000000000000000000000000000000000005b4a80480090000009002402402aa9495002a0005400a80000050000140140000014005005000028000000000000000003e0700801c00083b8079e002a01c001e000003c000007800410802c00200401000700b6d40000000000000000000000545a1a8547ff10ffe1ffc0000000000000000000000000000000000621052003184218c, 0x842108400000000000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x0, 0x842108400000000000000000004210842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x0⟩

def h95w37 : W := ⟨0x7ffffc0000000000000000000000007ffffc0fffff7df70000000000000000000200420c6428b68043010c10c00000402a10e002180430402521c0008608616d008a02282284911c0000000000000000080480d6120000224020800210108008c008433300046640f3cc0220000000000048000c008000c0016c000000000004040180547ff000000001805affe000000002d80000000000000000701212010581204c, 0x2000001000010000108400000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x0, 0x2000001000010000108400000200002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x0⟩

def h95w38 : W := ⟨0x7ffffbef8000000fbffffef7ffffde000000000000000000000000004900110b8217000001600580582aad4d500098001300260da881701205c05c049005c0170170000b0000000000000000030c0d87803630e386c79e3001b01e711eb1ce23b6398077030c4c0298180200c0c0d8b6002affedffc0000000000000545a1a800000000000001b45affe303ff8002d823ff8ffe0000000072524201a525a9cc, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x0, 0x20000000000000000004000000000000000000842100000000000000000000000000000000000004000000000000000000000000000, 0x0⟩

def h95w39 : W := ⟨0x7ffffbe00000000fbffffef0000000000000000000000000000000004800110b0014000001400500502aad400000900012002409a881601205805800000500140140000a000000000000000002080c06003020c38607802001801e611e81c8038001007002084802801000008080c0b0002affe00000000000000000545a00000000000000001b45affe303ff80000000000000000000005252420121210948, 0x800000021084200000000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 0x0, 0x800000021084200000000000004210840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 0x0⟩

def h95z0 : Nat := 0x9ce93952538c67394674a5274a4a518ce518ca7294a52a4a549ce939ce73a4e93b56b6946338c67184a308ca718ce518ca93a4e738423094612

def h95z1 : Nat := 0x9ce939527494a949ca95ad695ace729527294e939ce73a4a549ce939ce73a4e93b56b694a5494a928ce5194a718ce518ca93a4e738c63094612

def h95z2 : Nat := 0x9ce93952538c67394674a5274a52539d6539d2729529494a548c6539ce3194e93a4e76946338c67394a729ca318ce118ca5194e7384a3084612

def h95z3 : Nat := 0xa52949d67394a939ca94a5295ad2739d6739d2939d2949ca5494a739ce529ce93ad2969ca5394a9394e729ca518ce318ca729ce738ca308c612

def h95z4 : Nat := 0xa52b49d67494a949ca95ad695ad2939d6939d2b4a5294a4a549ce939ce73a4e93b56b69ca5494a93952729ca718ce518ca93a4e738ca3094612

def h95z5 : Nat := 0x9d2b49d6538c6749ca95ad695ace72952939d2b4a52949c63394a7294a73a4e93b56b69c65494a92952729c65084a518ca93a4e738ca1094612

def h95z6 : Nat := 0x9ce93952538c67394674a5274a52939ce939cab495252a4a529ce538c67394e51b4e74946338c673952728ca718c6518c29394e3184a3094610

def h95z7 : Nat := 0xa52b39d6748ca9494a94ad674ad2929d6929d294a4e74a465494e9294e53a4a73ad2b59ca548ca93952529ca708ce508ca73a4a538ca3094212

def h95z8 : Nat := 0x9ce93952939ceb3a4eb4a52b6b4a518ce518ca7294a5294a548c6539ce3194e93a4e7694e739ceb184a308ca318ce118ca5194e739423084612

def h95z9 : Nat := 0xa52949d6949ceb4a4eb5ad6b6b4e529525294e7294e739ca5494a739ce529ce93ad2969ce749ceb28ca5194a518ce318ca729ce73946308c612

def h95z10 : Nat := 0xa52b49d6959ceb5a4eb6b5ab6b4e729527294e939ce73a4a549ce939ce73a4e93b56b69ce759ceb28ce5194a718ce518ca93a4e739463094612

def h95z11 : Nat := 0x9d2b49d67494a95a4eb6b5ab6b4a518ce7294e939ce739c63394a7294a73a4e93b56b69ca759ceb18ce519465084a518ca93a4e739461094612

def h95z12 : Nat := 0x9ce93952959ce75a4e76b52b4a4a518ce518ca7294a52a4a529ce538c67394e51b4e7494e759ce7184a308ca718c6518c29394e319423094610

def h95z13 : Nat := 0xa52b49d2959ce95a4e96b56b5ace7294e7294a9394e52a4a539ce7394a739ce72b52959ce759ce928ce518ca718ca518c6939ce529463094611

def h95z14 : Nat := 0xa52b39d69594eb59ceb5b5a95b4e719527194e739ca53a465494e9294e53a4a73ad2b59ce7594eb28ce3194a708ce508ca73a4a539463094212

def h95z15 : Nat := 0xa5695a5a7494a93a4eb4a52b6b4e72952539d272952949c63394a7294a3194e93a4e76a4a739ceb294a729c65084a118ca5194e7394a1084612

def h95z16 : Nat := 0xa56b5a5a7394a94a4eb5ad6b6b4e52952739d2939d294946338c65294a529ce93ad296a4a749ceb294e729c63084a318ca729ce7394a108c612

def h95z17 : Nat := 0xad6b5a5a949ceb4a4eb5ad6b6b52739d6739d2939d2949ca5494a739ce529ce93ad296a4e749ceb394e729ca518ce318ca729ce7394a308c612

def h95z18 : Nat := 0xad695a52939ce73a4e74a52b4a52539ce539ca729525294a528c6538c63194e51a4e74a4e739ce7394a728ca318c6118c25194e3194a3084610

def h95z19 : Nat := 0xad6b5a56949ce94a4e95ad2b5ad2739d2739ce93952739ca5394a5394a5294e72ace75a4e749ce9394e7294a518ca318c67294e5294a308c611

def h95z20 : Nat := 0xad6b4a5a9494eb49ceb4ad695b52729d6729d2739ce749c6548ca7294e329ca73a4e95a4e7494eb394e529ca508ce308ca529ca5394a308c212

def h95z21 : Nat := 0xad6d5a56959ce95a4e96b56b5ad2939d2939ceb49d273a4a539ce7394a739ce72b5295a4e759ce939527294a718ca518c6939ce5294a3094611

def h95z22 : Nat := 0xa56d5a567494a75a4e96b56b5ace7294e939ceb49d2739c63294a528c6739ce72b5295a4a759ce929527294650846518c6939ce5294a1094611

def h95z23 : Nat := 0xad6d4a5a9594eb59ceb5b5a95b52929d6929d294a4e74a465494e9294e53a4a73ad2b5a4e7594eb3952529ca708ce508ca73a4a5394a3094212

def h95z24 : Nat := 0xad6d4a569594e959ce95b5694ad2929d2929ce949ce53a465394e728ca539ca52ace94a4e7594e939525294a708ca508c6739ca3294a3094211

def h95z25 : Nat := 0x9ce93952738c67394674a5274a4e939d6939d2b4a52949c6339ce939ce73a4e93b56b6946338c673952729c6718ce518ca93a4e7384a3094612

def h95z26 : Nat := 0x9ce93952538c67394674a5274a4a939d6939d2b4a5294942129ce939ce73a4e93b56b6946338c673952729c2718ce518ca93a4e7384a3094612

def h95z27 : Nat := 0xa52b49d65494a949ca95ad695ace939d6939d2b4a52949c6339ce939ce73a4e93b56b69ca5494a93952729c6718ce518ca93a4e738ca3094612

def h95z28 : Nat := 0x9ce93952759ceb5a4eb6b5ab6b4e518ce518ca7294a529c6339ce939ce73a4e93b56b694e759ceb184a308c6718ce518ca93a4e739423094612

def h95z29 : Nat := 0x9ce93952559ceb5a4eb6b5ab6b4a518ce518ca7294a52942129ce939ce73a4e93b56b694e759ceb184a308c2718ce518ca93a4e739423094612

def h95z30 : Nat := 0xa52b49d6759ceb5a4eb6b5ab6b4a729527294e939ce739c6339ce939ce73a4e93b56b69ce759ceb28ce51946718ce518ca93a4e739463094612

def h95z31 : Nat := 0xad695a5a739ceb3a4eb4a52b6b4e539d6539d272952949c6338c6539ce3194e93a4e76a4e739ceb394a729c6318ce118ca5194e7394a3084612

def h95z32 : Nat := 0xad695a5a539ceb3a4eb4a52b6b4a539d6539d27295294942128c6539ce3194e93a4e76a4e739ceb394a729c2318ce118ca5194e7394a3084612

def h95z33 : Nat := 0xad6b5a5a749ceb4a4eb5ad6b6b4e739d6739d2939d2949463394a739ce529ce93ad296a4e749ceb394e729c6518ce318ca729ce7394a308c612

def h95z34 : Nat := 0xad6d5a52759ce75a4e76b52b4a4e939ce939cab4952529c6339ce538c67394e51b4e74a4e759ce73952728c6718c6518c29394e3194a3094610

def h95z35 : Nat := 0xad6d5a52559ce75a4e76b52b4a4a939ce939cab495252942129ce538c67394e51b4e74a4e759ce73952728c2718c6518c29394e3194a3094610

def h95z36 : Nat := 0xad6d5a56759ce95a4e96b56b5ace939d2939ceb49d2739c6329ce7394a739ce72b5295a4e759ce9395272946718ca518c6939ce5294a3094611

def h95z37 : Nat := 0xad6d4a5a7594eb59ceb5b5a95b4e929d6929d294a4e749c23394e9294e53a4a73ad2b5a4e7594eb3952529c6708ce508ca73a4a5394a3094212

def h95z38 : Nat := 0x94a728ce538c67394674a5274a4a518ce518ca7294a52a4a549ce939ce73a4e93b56b68c6338c67184a308ca718ce518ca93a4e738423094612

def h95z39 : Nat := 0x9ce73952528c672946739ce74a52539d6539d2729529494a548c6539ce3194e93a4e76946328c67394a729ca318ce118ca5194e7384a3084612

def h95z40 : Nat := 0x9ce93952538c67394674a5274a4e939d6939d2b4a52949c6339ce939ce73a4e93b56b6946338c673952729c6718ce518ca93a4e7384a3094612

def h95z41 : Nat := 0x9ce93952338c67394674a5274a4a939d6939d2b4a5294942129ce939ce73a4e93b56b6946338c673952729c2718ce518ca93a4e7384a3094612

def h95z42 : Nat := 0x9ce93952538c67394674a5274a4e72952939d2b4a52949c63394a7294a73a4e93b56b6946338c672952729c65084a518ca93a4e7384a1094612

def h95z43 : Nat := 0x9ce9394e538c65394654a4e739d2939ce939cab495252a4a529ce538c67394e51b4e74946338c653952728ca718c6518c29394e3184a3094610

def h95z44 : Nat := 0x9ce73952939ceb3a4eb4a52b6b4a318ce318ca518ca5294a548c6539ce3194e93a4e7694e739ceb1846308ca318ce118ca5194e739423084612

def h95z45 : Nat := 0x9ce93952759ceb5a4eb6b5ab6b4a518ce518ca7294a529c6339ce939ce73a4e93b56b694e759ceb184a308c6718ce518ca93a4e739423094612

def h95z46 : Nat := 0x9ce93952559ceb5a4eb6b5ab6b46518ce518ca7294a52942129ce939ce73a4e93b56b694e759ceb184a308c2718ce518ca93a4e739423094612

def h95z47 : Nat := 0x9ce939527494a95a4eb6b5ab6b4a518ce518ca7294a529c63394a7294a73a4e93b56b694a759ceb184a308c65084a518ca93a4e739421094612

def h95z48 : Nat := 0x9ce9394e959ce75a4e76b52b4a4a518ca518c6728ca31a4a529ce538c67394e51b4e7494e759ce7184a3084a718c6518c29394e319423094610

def h95z49 : Nat := 0xad695a5a739ceb3a4eb4a52b6b4e539d6539d27295294946338c6539ce3194e93a4e76a4e739ceb394a729c6318ce118ca5194e7394a3084612

def h95z50 : Nat := 0xad695a5a539ceb3a4eb4a52b6b4a539d6539d272952948c2128c6539ce3194e93a4e76a4e739ceb394a729c2318ce118ca5194e7394a3084612

def h95z51 : Nat := 0xad695a52939ce73a4e74a4eb4a52539ce539ca728d25294a528c6338c6318ce51a4a54a4e739ce7394a728ca318c6118c2518ce3194a3084610

def h95z52 : Nat := 0xa52b49d65494a949ca95ad695aca939d6939d2b4a5294942129ce939ce73a4e93b56b69ca5494a93952729c2718ce518ca93a4e738ca3094612

def h95z53 : Nat := 0xa52b49d6559ceb5a4eb6b5ab6b4a729527294e939ce73942129ce939ce73a4e93b56b69ce759ceb28ce51942718ce518ca93a4e739463094612

def h95z54 : Nat := 0xad6b5a5a549ceb4a4eb5ad6b6b4a739d6739d2939d2949421294a739ce529ce93ad296a4e749ceb394e729c2518ce318ca729ce7394a308c612

def h95z55 : Nat := 0xa56d5a5a5494a95a4eb6b5ab6b4a72952939d2b4a52949421294a7294a73a4e93b56b6a4a759ceb2952729c25084a518ca93a4e7394a1094612

def h95z56 : Nat := 0xad6d5a52759ce75a4e76b52b4a4e939ce939cab4952529c6329ce538c67394e51b4e74a4e759ce73952728c6718c6518c29394e3194a3094610

def h95z57 : Nat := 0xad6d5a52559ce75a4e76b52b4a4a939ce939cab495252942119ce538c67394e51b4e74a4e759ce73952728c2718c6518c29394e3194a3094610

def h95z58 : Nat := 0xad6d5a56559ce95a4e96b56b5aca939d2939ceb49d273942129ce7394a739ce72b5295a4e759ce9395272942718ca518c6939ce5294a3094611

def h95z59 : Nat := 0xad6d4a5a5594eb59ceb5b5a95b4a929d6929d294a4e749421294e9294e53a4a73ad2b5a4e7594eb3952529c2708ce508ca73a4a5394a3094212

def h95z60 : Nat := 0xad6d5a5a559ceb5a4eb6b5ab6b4a939d6939d2b4a5294942129ce939ce73a4e93b56b6a4e759ceb3952729c2718ce518ca93a4e7394a3094612

def h95z61 : Nat := 0xa56d5a527494a75a4e76b52b4a4e7294e939cab4952529c63294a528c67394e51b4e74a4a759ce72952728c650846518c29394e3194a1094610

def h95z62 : Nat := 0xad6d5a5a959ceb5a4eb6b5ab6b52939d6939d2b4a5294a4a549ce939ce73a4e93b56b6a4e759ceb3952729ca718ce518ca93a4e7394a3094612

def h95v0 : List W := [h8w2, h8w3, h95w0, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v1 : List W := [h8w0, h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v2 : List W := [h8w2, h8w3, h8w4, h95w1, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v3 : List W := [h8w10, h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v4 : List W := [h8w11, h8w2, h8w3, h8w4, h8w27, h8w6, h8w7, h8w8, h8w9]

def h95v5 : List W := [h8w11, h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v6 : List W := [h8w12, h8w2, h8w3, h8w4, h8w27, h8w5, h8w7, h8w8, h8w9]

def h95v7 : List W := [h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9, h8w13]

def h95v8 : List W := [h8w1, h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v9 : List W := [h8w14, h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v10 : List W := [h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9, h8w15]

def h95v11 : List W := [h8w2, h8w16, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v12 : List W := [h8w2, h8w18, h8w3, h8w4, h8w27, h8w6, h8w7, h8w8, h8w9]

def h95v13 : List W := [h8w2, h8w18, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v14 : List W := [h8w2, h8w19, h8w3, h8w4, h8w27, h8w5, h8w7, h8w8, h8w9]

def h95v15 : List W := [h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h95w2, h8w8, h8w9]

def h95v16 : List W := [h8w2, h8w20, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v17 : List W := [h8w2, h8w21, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v18 : List W := [h8w2, h8w3, h8w4, h8w27, h8w6, h8w7, h8w8, h8w9, h8w22]

def h95v19 : List W := [h8w2, h8w3, h8w23, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v20 : List W := [h8w2, h8w3, h8w24, h8w4, h8w27, h8w5, h8w7, h8w8, h8w9]

def h95v21 : List W := [h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9, h95w3]

def h95v22 : List W := [h8w2, h8w3, h8w25, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v23 : List W := [h8w2, h8w3, h8w26, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v24 : List W := [h8w2, h8w3, h8w4, h8w27, h8w28, h8w6, h8w7, h8w8, h8w9]

def h95v25 : List W := [h8w2, h8w3, h8w4, h8w27, h8w28, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v26 : List W := [h8w2, h8w3, h8w4, h8w27, h8w29, h8w6, h8w7, h8w8, h8w9]

def h95v27 : List W := [h8w2, h8w3, h8w4, h8w27, h8w5, h8w30, h8w7, h8w8, h8w9]

def h95v28 : List W := [h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w32, h8w7, h8w8, h8w9]

def h95v29 : List W := [h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h95w4]

def h95v30 : List W := [h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9, h95w4]

def h95v31 : List W := [h95w5, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v32 : List W := [h95w5, h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v33 : List W := [h8w2, h8w3, h8w4, h95w6, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v34 : List W := [h8w2, h8w3, h8w4, h8w27, h95w6, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v35 : List W := [h8w2, h95w7, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v36 : List W := [h8w2, h95w7, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v37 : List W := [h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h95w8, h8w9]

def h95v38 : List W := [h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h95w8, h8w9]

def h95v39 : List W := [h8w2, h8w3, h95w9, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v40 : List W := [h8w2, h8w3, h95w9, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v41 : List W := [h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9, h95w10]

def h95v42 : List W := [h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9, h95w10]

def h95v43 : List W := [h8w2, h8w3, h8w4, h95w11, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v44 : List W := [h8w2, h8w3, h8w4, h95w11, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v45 : List W := [h8w2, h8w3, h8w4, h95w12, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v46 : List W := [h8w2, h8w3, h8w4, h95w12, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v47 : List W := [h8w2, h8w3, h8w4, h95w13, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v48 : List W := [h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h95w14, h8w9]

def h95v49 : List W := [h8w2, h8w3, h8w4, h95w15, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v50 : List W := [h8w2, h8w3, h8w4, h8w27, h95w15, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v51 : List W := [h8w2, h8w3, h8w4, h8w27, h95w16, h8w6, h8w7, h8w8, h8w9]

def h95v52 : List W := [h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h95w17, h8w8, h8w9]

def h95v53 : List W := [h8w2, h8w3, h95w18, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v54 : List W := [h8w2, h8w3, h8w4, h8w53, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v55 : List W := [h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h95w19, h8w8, h8w9]

def h95v56 : List W := [h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h95w19, h8w8, h8w9]

def h95v57 : List W := [h8w2, h8w3, h8w4, h8w27, h8w6, h8w7, h8w54, h8w8, h8w9]

def h95v58 : List W := [h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9, h95w20]

def h95v59 : List W := [h8w2, h8w56, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v60 : List W := [h8w2, h8w3, h8w57, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v61 : List W := [h8w2, h8w3, h8w4, h95w21, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v62 : List W := [h8w2, h8w3, h8w4, h8w27, h95w21, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v63 : List W := [h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h95w22, h8w8, h8w9]

def h95v64 : List W := [h8w2, h95w23, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v65 : List W := [h95w24, h8w2, h95w23, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v66 : List W := [h95w25, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v67 : List W := [h8w2, h8w3, h95w26, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v68 : List W := [h95w24, h8w2, h8w3, h95w26, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v69 : List W := [h95w27, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v70 : List W := [h8w2, h8w3, h8w4, h95w28, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v71 : List W := [h95w24, h8w2, h8w3, h8w4, h95w28, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v72 : List W := [h95w29, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v73 : List W := [h95w30, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v74 : List W := [h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h95w31, h8w8, h8w9]

def h95v75 : List W := [h95w24, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h95w31, h8w8, h8w9]

def h95v76 : List W := [h95w32, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v77 : List W := [h95w33, h8w2, h8w3, h8w4, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v78 : List W := [h8w2, h95w23, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v79 : List W := [h8w2, h8w3, h95w26, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v80 : List W := [h8w2, h8w3, h8w4, h95w28, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v81 : List W := [h95w30, h8w2, h8w3, h8w4, h8w27, h8w6, h8w7, h8w8, h8w9]

def h95v82 : List W := [h95w34, h8w2, h8w3, h8w4, h8w27, h8w5, h8w7, h8w8, h8w9]

def h95v83 : List W := [h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h95w31, h8w8, h8w9]

def h95v84 : List W := [h8w2, h95w35, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v85 : List W := [h8w2, h8w3, h95w36, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v86 : List W := [h8w2, h8w3, h8w4, h95w37, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v87 : List W := [h8w2, h8w3, h8w4, h95w38, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v88 : List W := [h8w2, h8w3, h8w4, h8w27, h95w38, h8w5, h8w6, h8w7, h8w8, h8w9]

def h95v89 : List W := [h8w2, h8w3, h8w4, h8w27, h95w39, h8w6, h8w7, h8w8, h8w9]

def h95v90 : List W := [h8w2, h8w3, h8w4, h8w27, h8w5, h8w6, h8w7, h8w8, h8w9]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf0 : look1 h8L h8M h8G 14 13 12 1 h95z0 h95v0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf1 : look1 h8L h8M h8G 14 13 12 1 h95z1 h95v1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf2 : look1 h8L h8M h8G 14 13 12 1 h95z2 h95v2 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf3 : look1 h8L h8M h8G 14 13 12 1 h95z3 h95v3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf4 : look1 h8L h8M h8G 14 13 12 1 h95z4 h95v4 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf5 : look1 h8L h8M h8G 14 13 12 1 h95z5 h95v5 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf6 : look1 h8L h8M h8G 14 13 12 1 h95z4 h95v6 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf7 : look1 h8L h8M h8G 14 13 12 1 h95z6 h95v7 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf8 : look1 h8L h8M h8G 14 13 12 1 h8z21 h95v8 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf9 : look1 h8L h8M h8G 14 13 12 1 h95z7 h95v9 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf10 : look1 h8L h8M h8G 14 13 12 1 h95z8 h95v10 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf11 : look1 h8L h8M h8G 14 13 12 1 h95z9 h95v11 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf12 : look1 h8L h8M h8G 14 13 12 1 h95z10 h95v12 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf13 : look1 h8L h8M h8G 14 13 12 1 h95z11 h95v13 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf14 : look1 h8L h8M h8G 14 13 12 1 h95z10 h95v14 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf15 : look1 h8L h8M h8G 14 13 12 1 h95z12 h95v15 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf16 : look1 h8L h8M h8G 14 13 12 1 h95z13 h95v16 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf17 : look1 h8L h8M h8G 14 13 12 1 h95z14 h95v17 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf18 : look1 h8L h8M h8G 14 13 12 1 h95z15 h95v18 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf19 : look1 h8L h8M h8G 14 13 12 1 h95z16 h95v19 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf20 : look1 h8L h8M h8G 14 13 12 1 h95z17 h95v20 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf21 : look1 h8L h8M h8G 14 13 12 1 h95z18 h95v21 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf22 : look1 h8L h8M h8G 14 13 12 1 h95z19 h95v22 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf23 : look1 h8L h8M h8G 14 13 12 1 h95z20 h95v23 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf24 : look1 h8L h8M h8G 14 13 12 1 h95z21 h95v24 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf25 : look1 h8L h8M h8G 14 13 12 1 h95z22 h95v25 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf26 : look1 h8L h8M h8G 14 13 12 1 h95z23 h95v26 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf27 : look1 h8L h8M h8G 14 13 12 1 h95z21 h95v27 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf28 : look1 h8L h8M h8G 14 13 12 1 h95z24 h95v28 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf29 : look h8L h8M h8G 14 12 1 h95z25 h95v29 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf30 : look h8L h8M h8G 14 12 1 h95z26 h95v30 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf31 : look h8L h8M h8G 14 12 1 h95z4 h95v31 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf32 : look h8L h8M h8G 14 12 1 h95z27 h95v32 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf33 : look h8L h8M h8G 14 12 1 h95z28 h95v33 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf34 : look h8L h8M h8G 14 12 1 h95z29 h95v34 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf35 : look h8L h8M h8G 14 12 1 h95z10 h95v35 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf36 : look h8L h8M h8G 14 12 1 h95z30 h95v36 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf37 : look h8L h8M h8G 14 12 1 h95z31 h95v37 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf38 : look h8L h8M h8G 14 12 1 h95z32 h95v38 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf39 : look h8L h8M h8G 14 12 1 h95z17 h95v39 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf40 : look h8L h8M h8G 14 12 1 h95z33 h95v40 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf41 : look h8L h8M h8G 14 12 1 h95z34 h95v41 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf42 : look h8L h8M h8G 14 12 1 h95z35 h95v42 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf43 : look h8L h8M h8G 14 12 1 h95z21 h95v43 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf44 : look h8L h8M h8G 14 12 1 h95z36 h95v44 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf45 : look h8L h8M h8G 14 12 1 h95z23 h95v45 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf46 : look h8L h8M h8G 14 12 1 h95z37 h95v46 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf47 : look h8L h8M h8G 14 11 0 h95z38 h95v47 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf48 : look h8L h8M h8G 14 11 0 h95z39 h95v48 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf49 : look h8L h8M h8G 14 11 0 h95z40 h95v49 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf50 : look h8L h8M h8G 14 11 0 h95z41 h95v50 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf51 : look h8L h8M h8G 14 11 0 h95z42 h95v51 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf52 : look h8L h8M h8G 14 11 0 h95z43 h95v52 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf53 : look h8L h8M h8G 14 11 0 h95z38 h95v53 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf54 : look h8L h8M h8G 14 11 0 h95z44 h95v54 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf55 : look h8L h8M h8G 14 11 0 h95z45 h95v55 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf56 : look h8L h8M h8G 14 11 0 h95z46 h95v56 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf57 : look h8L h8M h8G 14 11 0 h95z47 h95v57 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf58 : look h8L h8M h8G 14 11 0 h95z48 h95v58 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf59 : look h8L h8M h8G 14 11 0 h95z39 h95v59 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf60 : look h8L h8M h8G 14 11 0 h95z44 h95v60 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf61 : look h8L h8M h8G 14 11 0 h95z49 h95v61 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf62 : look h8L h8M h8G 14 11 0 h95z50 h95v62 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf63 : look h8L h8M h8G 14 11 0 h95z51 h95v63 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf64 : look h8L h8M h8G 14 11 0 h95z40 h95v64 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf65 : look h8L h8M h8G 14 11 0 h95z41 h95v65 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf66 : look h8L h8M h8G 14 11 0 h95z52 h95v66 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf67 : look h8L h8M h8G 14 11 0 h95z45 h95v67 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf68 : look h8L h8M h8G 14 11 0 h95z46 h95v68 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf69 : look h8L h8M h8G 14 11 0 h95z53 h95v69 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf70 : look h8L h8M h8G 14 11 0 h95z49 h95v70 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf71 : look h8L h8M h8G 14 11 0 h95z50 h95v71 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf72 : look h8L h8M h8G 14 11 0 h95z54 h95v72 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf73 : look h8L h8M h8G 14 11 0 h95z55 h95v73 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf74 : look h8L h8M h8G 14 11 0 h95z56 h95v74 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf75 : look h8L h8M h8G 14 11 0 h95z57 h95v75 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf76 : look h8L h8M h8G 14 11 0 h95z58 h95v76 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf77 : look h8L h8M h8G 14 11 0 h95z59 h95v77 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf78 : look h8L h8M h8G 14 11 0 h95z41 h95v78 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf79 : look h8L h8M h8G 14 11 0 h95z46 h95v79 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf80 : look h8L h8M h8G 14 11 0 h95z50 h95v80 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf81 : look h8L h8M h8G 14 11 0 h95z60 h95v81 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf82 : look h8L h8M h8G 14 11 0 h95z60 h95v82 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf83 : look h8L h8M h8G 14 11 0 h95z57 h95v83 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf84 : look h8L h8M h8G 14 11 0 h95z43 h95v84 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf85 : look h8L h8M h8G 14 11 0 h95z48 h95v85 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf86 : look h8L h8M h8G 14 11 0 h95z51 h95v86 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf87 : look h8L h8M h8G 14 11 0 h95z56 h95v87 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf88 : look h8L h8M h8G 14 11 0 h95z57 h95v88 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95leaf89 : look h8L h8M h8G 14 11 0 h95z61 h95v89 = false := by decide +kernel

def h95cacheA (A : Nat → Nat → Nat → List W → Bool) := memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (A) 12 1 h95z0 h95v0) 12 1 h95z1 h95v1) 12 1 h95z2 h95v2) 12 1 h95z3 h95v3) 12 1 h95z4 h95v4) 12 1 h95z5 h95v5) 12 1 h95z4 h95v6) 12 1 h95z6 h95v7) 12 1 h8z21 h95v8) 12 1 h95z7 h95v9) 12 1 h95z8 h95v10) 12 1 h95z9 h95v11) 12 1 h95z10 h95v12) 12 1 h95z11 h95v13) 12 1 h95z10 h95v14) 12 1 h95z12 h95v15) 12 1 h95z13 h95v16) 12 1 h95z14 h95v17) 12 1 h95z15 h95v18) 12 1 h95z16 h95v19) 12 1 h95z17 h95v20) 12 1 h95z18 h95v21) 12 1 h95z19 h95v22) 12 1 h95z20 h95v23) 12 1 h95z21 h95v24) 12 1 h95z22 h95v25) 12 1 h95z23 h95v26) 12 1 h95z21 h95v27) 12 1 h95z24 h95v28

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95cacheA_eq : h95cacheA (look1 h8L h8M h8G 14 13) = look1 h8L h8M h8G 14 13 := by
  simp only [h95cacheA, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z0 h95v0 h95leaf0, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z1 h95v1 h95leaf1, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z2 h95v2 h95leaf2, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z3 h95v3 h95leaf3, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z4 h95v4 h95leaf4, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z5 h95v5 h95leaf5, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z4 h95v6 h95leaf6, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z6 h95v7 h95leaf7, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h8z21 h95v8 h95leaf8, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z7 h95v9 h95leaf9, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z8 h95v10 h95leaf10, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z9 h95v11 h95leaf11, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z10 h95v12 h95leaf12, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z11 h95v13 h95leaf13, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z10 h95v14 h95leaf14, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z12 h95v15 h95leaf15, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z13 h95v16 h95leaf16, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z14 h95v17 h95leaf17, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z15 h95v18 h95leaf18, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z16 h95v19 h95leaf19, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z17 h95v20 h95leaf20, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z18 h95v21 h95leaf21, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z19 h95v22 h95leaf22, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z20 h95v23 h95leaf23, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z21 h95v24 h95leaf24, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z22 h95v25 h95leaf25, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z23 h95v26 h95leaf26, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z21 h95v27 h95leaf27, memo4_eq (look1 h8L h8M h8G 14 13) 12 1 h95z24 h95v28 h95leaf28]

def h95cacheB (B : Nat → Nat → Nat → List W → Bool) := memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (memo4 (B) 12 1 h95z25 h95v29) 12 1 h95z26 h95v30) 12 1 h95z4 h95v31) 12 1 h95z27 h95v32) 12 1 h95z28 h95v33) 12 1 h95z29 h95v34) 12 1 h95z10 h95v35) 12 1 h95z30 h95v36) 12 1 h95z31 h95v37) 12 1 h95z32 h95v38) 12 1 h95z17 h95v39) 12 1 h95z33 h95v40) 12 1 h95z34 h95v41) 12 1 h95z35 h95v42) 12 1 h95z21 h95v43) 12 1 h95z36 h95v44) 12 1 h95z23 h95v45) 12 1 h95z37 h95v46) 11 0 h95z38 h95v47) 11 0 h95z39 h95v48) 11 0 h95z40 h95v49) 11 0 h95z41 h95v50) 11 0 h95z42 h95v51) 11 0 h95z43 h95v52) 11 0 h95z38 h95v53) 11 0 h95z44 h95v54) 11 0 h95z45 h95v55) 11 0 h95z46 h95v56) 11 0 h95z47 h95v57) 11 0 h95z48 h95v58) 11 0 h95z39 h95v59) 11 0 h95z44 h95v60) 11 0 h95z49 h95v61) 11 0 h95z50 h95v62) 11 0 h95z51 h95v63) 11 0 h95z40 h95v64) 11 0 h95z41 h95v65) 11 0 h95z52 h95v66) 11 0 h95z45 h95v67) 11 0 h95z46 h95v68) 11 0 h95z53 h95v69) 11 0 h95z49 h95v70) 11 0 h95z50 h95v71) 11 0 h95z54 h95v72) 11 0 h95z55 h95v73) 11 0 h95z56 h95v74) 11 0 h95z57 h95v75) 11 0 h95z58 h95v76) 11 0 h95z59 h95v77) 11 0 h95z41 h95v78) 11 0 h95z46 h95v79) 11 0 h95z50 h95v80) 11 0 h95z60 h95v81) 11 0 h95z60 h95v82) 11 0 h95z57 h95v83) 11 0 h95z43 h95v84) 11 0 h95z48 h95v85) 11 0 h95z51 h95v86) 11 0 h95z56 h95v87) 11 0 h95z57 h95v88) 11 0 h95z61 h95v89

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95cacheB_eq : h95cacheB (look h8L h8M h8G 14) = look h8L h8M h8G 14 := by
  simp only [h95cacheB, memo4_eq (look h8L h8M h8G 14) 12 1 h95z25 h95v29 h95leaf29, memo4_eq (look h8L h8M h8G 14) 12 1 h95z26 h95v30 h95leaf30, memo4_eq (look h8L h8M h8G 14) 12 1 h95z4 h95v31 h95leaf31, memo4_eq (look h8L h8M h8G 14) 12 1 h95z27 h95v32 h95leaf32, memo4_eq (look h8L h8M h8G 14) 12 1 h95z28 h95v33 h95leaf33, memo4_eq (look h8L h8M h8G 14) 12 1 h95z29 h95v34 h95leaf34, memo4_eq (look h8L h8M h8G 14) 12 1 h95z10 h95v35 h95leaf35, memo4_eq (look h8L h8M h8G 14) 12 1 h95z30 h95v36 h95leaf36, memo4_eq (look h8L h8M h8G 14) 12 1 h95z31 h95v37 h95leaf37, memo4_eq (look h8L h8M h8G 14) 12 1 h95z32 h95v38 h95leaf38, memo4_eq (look h8L h8M h8G 14) 12 1 h95z17 h95v39 h95leaf39, memo4_eq (look h8L h8M h8G 14) 12 1 h95z33 h95v40 h95leaf40, memo4_eq (look h8L h8M h8G 14) 12 1 h95z34 h95v41 h95leaf41, memo4_eq (look h8L h8M h8G 14) 12 1 h95z35 h95v42 h95leaf42, memo4_eq (look h8L h8M h8G 14) 12 1 h95z21 h95v43 h95leaf43, memo4_eq (look h8L h8M h8G 14) 12 1 h95z36 h95v44 h95leaf44, memo4_eq (look h8L h8M h8G 14) 12 1 h95z23 h95v45 h95leaf45, memo4_eq (look h8L h8M h8G 14) 12 1 h95z37 h95v46 h95leaf46, memo4_eq (look h8L h8M h8G 14) 11 0 h95z38 h95v47 h95leaf47, memo4_eq (look h8L h8M h8G 14) 11 0 h95z39 h95v48 h95leaf48, memo4_eq (look h8L h8M h8G 14) 11 0 h95z40 h95v49 h95leaf49, memo4_eq (look h8L h8M h8G 14) 11 0 h95z41 h95v50 h95leaf50, memo4_eq (look h8L h8M h8G 14) 11 0 h95z42 h95v51 h95leaf51, memo4_eq (look h8L h8M h8G 14) 11 0 h95z43 h95v52 h95leaf52, memo4_eq (look h8L h8M h8G 14) 11 0 h95z38 h95v53 h95leaf53, memo4_eq (look h8L h8M h8G 14) 11 0 h95z44 h95v54 h95leaf54, memo4_eq (look h8L h8M h8G 14) 11 0 h95z45 h95v55 h95leaf55, memo4_eq (look h8L h8M h8G 14) 11 0 h95z46 h95v56 h95leaf56, memo4_eq (look h8L h8M h8G 14) 11 0 h95z47 h95v57 h95leaf57, memo4_eq (look h8L h8M h8G 14) 11 0 h95z48 h95v58 h95leaf58, memo4_eq (look h8L h8M h8G 14) 11 0 h95z39 h95v59 h95leaf59, memo4_eq (look h8L h8M h8G 14) 11 0 h95z44 h95v60 h95leaf60, memo4_eq (look h8L h8M h8G 14) 11 0 h95z49 h95v61 h95leaf61, memo4_eq (look h8L h8M h8G 14) 11 0 h95z50 h95v62 h95leaf62, memo4_eq (look h8L h8M h8G 14) 11 0 h95z51 h95v63 h95leaf63, memo4_eq (look h8L h8M h8G 14) 11 0 h95z40 h95v64 h95leaf64, memo4_eq (look h8L h8M h8G 14) 11 0 h95z41 h95v65 h95leaf65, memo4_eq (look h8L h8M h8G 14) 11 0 h95z52 h95v66 h95leaf66, memo4_eq (look h8L h8M h8G 14) 11 0 h95z45 h95v67 h95leaf67, memo4_eq (look h8L h8M h8G 14) 11 0 h95z46 h95v68 h95leaf68, memo4_eq (look h8L h8M h8G 14) 11 0 h95z53 h95v69 h95leaf69, memo4_eq (look h8L h8M h8G 14) 11 0 h95z49 h95v70 h95leaf70, memo4_eq (look h8L h8M h8G 14) 11 0 h95z50 h95v71 h95leaf71, memo4_eq (look h8L h8M h8G 14) 11 0 h95z54 h95v72 h95leaf72, memo4_eq (look h8L h8M h8G 14) 11 0 h95z55 h95v73 h95leaf73, memo4_eq (look h8L h8M h8G 14) 11 0 h95z56 h95v74 h95leaf74, memo4_eq (look h8L h8M h8G 14) 11 0 h95z57 h95v75 h95leaf75, memo4_eq (look h8L h8M h8G 14) 11 0 h95z58 h95v76 h95leaf76, memo4_eq (look h8L h8M h8G 14) 11 0 h95z59 h95v77 h95leaf77, memo4_eq (look h8L h8M h8G 14) 11 0 h95z41 h95v78 h95leaf78, memo4_eq (look h8L h8M h8G 14) 11 0 h95z46 h95v79 h95leaf79, memo4_eq (look h8L h8M h8G 14) 11 0 h95z50 h95v80 h95leaf80, memo4_eq (look h8L h8M h8G 14) 11 0 h95z60 h95v81 h95leaf81, memo4_eq (look h8L h8M h8G 14) 11 0 h95z60 h95v82 h95leaf82, memo4_eq (look h8L h8M h8G 14) 11 0 h95z57 h95v83 h95leaf83, memo4_eq (look h8L h8M h8G 14) 11 0 h95z43 h95v84 h95leaf84, memo4_eq (look h8L h8M h8G 14) 11 0 h95z48 h95v85 h95leaf85, memo4_eq (look h8L h8M h8G 14) 11 0 h95z51 h95v86 h95leaf86, memo4_eq (look h8L h8M h8G 14) 11 0 h95z56 h95v87 h95leaf87, memo4_eq (look h8L h8M h8G 14) 11 0 h95z57 h95v88 h95leaf88, memo4_eq (look h8L h8M h8G 14) 11 0 h95z61 h95v89 h95leaf89]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma h95grandchildren_outer (A B : Nat → Nat → Nat → List W → Bool) :
    look1F (h95cacheA A) (h95cacheB B) h8L h8M h8G 13 1 h95z62 h95v90 = false := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h95or_complete : look1 h8L h8M h8G 14 14 13 1 h95z62 h95v90 = false := by
  rw [show (14 : Nat) = 13 + 1 from rfl, look1_succ]
  have hout := h95grandchildren_outer (look1 h8L h8M h8G 14 13) (look h8L h8M h8G 14)
  simpa only [h95cacheA_eq, h95cacheB_eq] using hout

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma h95root_outer (F : Nat → List W → Bool) :
    chkF (memo F h95z62 h95v90) [] rt 0 14 1 39614081257132168796771975168 0 = false := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def hash95_complete : chk [] rt 0 14 1 39614081257132168796771975168 0 = false := by
  rw [chk_expand]
  change chkF (look1 h8L h8M h8G 14 14 13 1) [] rt 0 14 1 39614081257132168796771975168 0 = false
  have hm := memo_eq (look1 h8L h8M h8G 14 14 13 1) h95z62 h95v90 h95or_complete
  simpa only [hm] using h95root_outer (look1 h8L h8M h8G 14 14 13 1)

end hash95Memo
def prootParts : List (ℕ × ℕ) := [(0, 1), (8, 0), (536870912, 0), (0x400000000000, 0), (0x20000000000000, 0), (0x800000000000000000, 0), (0x40000000000000000000, 0), (0x2000000000000000000000, 0), (0x10000000000000000000000, 0), (0x20000000000000000000000, 0), (0x800000000000000000000000, 0), (0x40000000000000000000000000000, 0), (0x80000000000000000000000000000000000, 0), (0x100000000000000000000000000000000000000000, 0), (0x1000000000000000000000000000000000000000000, 0), (0x2000000000000000000000000000000000000000000000, 0), (0x100000000000000000000000000000000000000000000000, 0), (0x200000000000000000000000000000000000000000000000, 0), (0x2000000000000000000000000000000000000000000000000, 0), (0x4000000000000000000000000000000000000000000000000000, 0), (0x40000000000000000000000000000000000000000000000000000, 0), (0x200000000000000000000000000000000000000000000000000000, 0), (0x1bbffdcfdffeeffffff7fffffbffff7cdfbf7fffdfbfffdffffff7, 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def prootParts_full : mFull prootParts = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_phase1 : chk [] rt 0 14 1 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r3 : chk [] rt 0 14 1 8 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r29 : chk [] rt 0 14 1 536870912 0 = false := hash29_complete
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r46 : chk [] rt 0 14 1 0x400000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r53 : chk [] rt 0 14 1 0x20000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r71 : chk [] rt 0 14 1 0x800000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r78 : chk [] rt 0 14 1 0x40000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r85 : chk [] rt 0 14 1 0x2000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r88 : chk [] rt 0 14 1 0x10000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r89 : chk [] rt 0 14 1 0x20000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r95 : chk [] rt 0 14 1 0x800000000000000000000000 0 = false := hash95_complete
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r114 : chk [] rt 0 14 1 0x40000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r139 : chk [] rt 0 14 1 0x80000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r164 : chk [] rt 0 14 1 0x100000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r168 : chk [] rt 0 14 1 0x1000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r181 : chk [] rt 0 14 1 0x2000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r188 : chk [] rt 0 14 1 0x100000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r189 : chk [] rt 0 14 1 0x200000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r193 : chk [] rt 0 14 1 0x2000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r206 : chk [] rt 0 14 1 0x4000000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r210 : chk [] rt 0 14 1 0x40000000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_r213 : chk [] rt 0 14 1 0x200000000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot1_rest : chk [] rt 0 14 1 0x1bbffdcfdffeeffffff7fffffbffff7cdfbf7fffdfbfffdffffff7 0 = false := by decide +kernel
lemma proot1_parts : ∀ p ∈ prootParts, chk [] rt 0 14 1 p.1 p.2 = false := by
  intro p hp
  simp only [prootParts, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact proot1_phase1
  · exact proot1_r3
  · exact proot1_r29
  · exact proot1_r46
  · exact proot1_r53
  · exact proot1_r71
  · exact proot1_r78
  · exact proot1_r85
  · exact proot1_r88
  · exact proot1_r89
  · exact proot1_r95
  · exact proot1_r114
  · exact proot1_r139
  · exact proot1_r164
  · exact proot1_r168
  · exact proot1_r181
  · exact proot1_r188
  · exact proot1_r189
  · exact proot1_r193
  · exact proot1_r206
  · exact proot1_r210
  · exact proot1_r213
  · exact proot1_rest
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_phase1 : chk [] rt 0 14 2 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r3 : chk [] rt 0 14 2 8 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r29 : chk [] rt 0 14 2 536870912 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r46 : chk [] rt 0 14 2 0x400000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r53 : chk [] rt 0 14 2 0x20000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r71 : chk [] rt 0 14 2 0x800000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r78 : chk [] rt 0 14 2 0x40000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r85 : chk [] rt 0 14 2 0x2000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r88 : chk [] rt 0 14 2 0x10000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r89 : chk [] rt 0 14 2 0x20000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r95 : chk [] rt 0 14 2 0x800000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r114 : chk [] rt 0 14 2 0x40000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r139 : chk [] rt 0 14 2 0x80000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r164 : chk [] rt 0 14 2 0x100000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r168 : chk [] rt 0 14 2 0x1000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r181 : chk [] rt 0 14 2 0x2000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r188 : chk [] rt 0 14 2 0x100000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r189 : chk [] rt 0 14 2 0x200000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r193 : chk [] rt 0 14 2 0x2000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r206 : chk [] rt 0 14 2 0x4000000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r210 : chk [] rt 0 14 2 0x40000000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_r213 : chk [] rt 0 14 2 0x200000000000000000000000000000000000000000000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot2_rest : chk [] rt 0 14 2 0x1bbffdcfdffeeffffff7fffffbffff7cdfbf7fffdfbfffdffffff7 0 = false := by decide +kernel
lemma proot2_parts : ∀ p ∈ prootParts, chk [] rt 0 14 2 p.1 p.2 = false := by
  intro p hp
  simp only [prootParts, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact proot2_phase1
  · exact proot2_r3
  · exact proot2_r29
  · exact proot2_r46
  · exact proot2_r53
  · exact proot2_r71
  · exact proot2_r78
  · exact proot2_r85
  · exact proot2_r88
  · exact proot2_r89
  · exact proot2_r95
  · exact proot2_r114
  · exact proot2_r139
  · exact proot2_r164
  · exact proot2_r168
  · exact proot2_r181
  · exact proot2_r188
  · exact proot2_r189
  · exact proot2_r193
  · exact proot2_r206
  · exact proot2_r210
  · exact proot2_r213
  · exact proot2_rest
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_3 : chk [] rt 0 14 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_4 : chk [] rt 0 14 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_5 : chk [] rt 0 14 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_6 : chk [] rt 0 14 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_7 : chk [] rt 0 14 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_8 : chk [] rt 0 14 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_9 : chk [] rt 0 14 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_10 : chk [] rt 0 14 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_11 : chk [] rt 0 14 11 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_12 : chk [] rt 0 14 12 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_13 : chk [] rt 0 14 13 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_14 : chk [] rt 0 14 14 FF 1 = false := by decide +kernel
lemma iroot_pos {t : ℕ} {S : Finset ℕ} (ht1 : 1 ≤ t) (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0))
    (hl : Live Z0 (mz 0) (tz 0) 14 t S) : False := by
  have hmin : ∀ q < 14, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [] 0)) := fun q hq => iroot q hq
  have hm0 : Min Z0 (mz 0) (tz 0) 14 t S := ⟨hl, fun q hq hs => hmin q hq (hs.mono le_rfl (by rintro x (hx | hx); exact hS hx; exact Or.inr hx))⟩
  have htk : t < 15 := by have := hm0.size.2; omega
  have hM : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rt 0 14 t p.1 p.2 = false := by
    interval_cases t
    · exact ⟨prootParts, prootParts_full, proot1_parts⟩
    · exact ⟨prootParts, prootParts_full, proot2_parts⟩
    · exact one proot_3
    · exact one proot_4
    · exact one proot_5
    · exact one proot_6
    · exact one proot_7
    · exact one proot_8
    · exact one proot_9
    · exact one proot_10
    · exact one proot_11
    · exact one proot_12
    · exact one proot_13
    · exact one proot_14
  exact imp_of_live (L := 15) (Or.inl rfl) root_p (by norm_num) ir (by omega) hS hl hmin (Or.inr hM)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
section circuit
variable (m : ℕ)
def gv (w : List ℕ) (g : Gate) : ℕ := match g.op, g.inputs with
  | .and, [] => m
  | .and, [i] => w.getD i 0
  | .and, i :: j :: _ => w.getD i 0 &&& w.getD j 0
  | .or, [] => 0
  | .or, [i] => w.getD i 0
  | .or, i :: j :: _ => w.getD i 0 ||| w.getD j 0
  | .not, [] => m
  | .not, i :: _ => w.getD i 0 ^^^ m
  | _, _ => 0
def ex (gs : List Gate) (w : List ℕ) : List ℕ := gs.foldl (fun w g => w ++ [gv m w g]) w
lemma getD_mem {S : Set ℕ} {w : List ℕ} (hw : ∀ x ∈ w, x ∈ S) (h0 : 0 ∈ S) (i : ℕ) : w.getD i 0 ∈ S := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · rw [List.getElem?_eq_getElem h]; exact hw _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none (by omega)]; exact h0
lemma ex_sol {T : ℕ} (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ), (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) → Sol Z0 m T gs.length S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact .done (getD_mem hw h0 i)
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → Sol Z0 m T (g :: gs).length S := fun h =>
      (ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT).mono (by simp) subset_rfl
    have go : Sol Z0 m T gs.length (insert (gv m w g) S) := ih (w ++ [gv m w g]) _ (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := false) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := true) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay hm
      | i :: _ => exact .un (rd i) go
lemma gv_sub {w : List ℕ} (hw : ∀ x ∈ w, x &&& m = x) (g : Gate) : gv m w g &&& m = gv m w g := by
  have rd : ∀ i, w.getD i 0 &&& m = w.getD i 0 := fun i => getD_mem (S := {x | x &&& m = x}) hw (by simp) i
  unfold gv
  split
  · simp
  · exact rd _
  · rw [Nat.and_assoc, rd]
  · simp
  · exact rd _
  · rw [Nat.and_or_distrib_right, rd, rd]
  · simp
  · rw [and_neg (Nat.and_self m), rd]
  · simp
lemma ex_sub {gs : List Gate} : ∀ {w : List ℕ}, (∀ x ∈ w, x &&& m = x) → ∀ x ∈ ex m gs w, x &&& m = x := by
  induction gs with
  | nil => intro w hw; exact hw
  | cons g gs ih =>
    intro w hw
    refine ih (w := w ++ [gv m w g]) fun x hx => ?_
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hw x hx
    · exact gv_sub m hw g
lemma getD_map (w : List ℕ) (b i : ℕ) : (w.map (fun x => x.testBit b)).getD i false = (w.getD i 0).testBit b := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp
lemma gv_bit {b : ℕ} (hb : m.testBit b = true) (w : List ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (gv m w g).testBit b = g.op.eval (g.inputs.map fun i => (w.map (fun x => x.testBit b)).getD i false) := by
  have e1 : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
  have e2 : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
  have e3 : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  obtain ⟨o, l⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_map]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  rcases hop with rfl | rfl | rfl
  · match l, hlen with
    | [], _ => simp [gv, e1, hb]
    | [i], _ => simp [gv, e1]
    | [i, j], _ => simp [gv, e1]
  · match l, hlen with
    | [], _ => simp [gv, e2]
    | [i], _ => simp [gv, e2]
    | [i, j], _ => simp [gv, e2]
  · match l, hlen with
    | [], _ => simp [gv, e3, hb]
    | [i], _ => simp [gv, e3, hb]
    | [i, j], _ => simp [gv, e3, hb]
lemma ex_bit {b : ℕ} (hb : m.testBit b = true) (gs : List Gate) : ∀ (w : List ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (ex m gs w).map (fun x => x.testBit b) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.map (fun x => x.testBit b)) := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hg
    rw [List.foldl_cons, ← gv_bit m hb w g (hg g List.mem_cons_self)]
    have := ih (w ++ [gv m w g]) (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    rw [List.map_append] at this
    exact this
end circuit
def f (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7)
def EF : ℕ := (rawP.getD 0 0 &&& rawP.getD 3 0) ||| (rawP.getD 0 0 &&& rawP.getD 4 0) ||| (rawP.getD 1 0 &&& rawP.getD 4 0) ||| (rawP.getD 2 0 &&& rawP.getD 4 0) ||| (rawP.getD 0 0 &&& rawP.getD 5 0) ||| (rawP.getD 1 0 &&& rawP.getD 5 0) ||| (rawP.getD 3 0 &&& rawP.getD 5 0) ||| (rawP.getD 1 0 &&& rawP.getD 6 0) ||| (rawP.getD 2 0 &&& rawP.getD 6 0) ||| (rawP.getD 3 0 &&& rawP.getD 6 0) ||| (rawP.getD 0 0 &&& rawP.getD 7 0) ||| (rawP.getD 1 0 &&& rawP.getD 7 0) ||| (rawP.getD 2 0 &&& rawP.getD 7 0) ||| (rawP.getD 4 0 &&& rawP.getD 7 0) ||| (rawP.getD 5 0 &&& rawP.getD 7 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len : rawP.length = 8 := rfl
lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 8 => (rawP.getD v.val 0).testBit b) = rawP.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len]
  · intro i h1 h2
    have : i < rawP.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl
lemma f_bit (k : ℕ) : EF.testBit k = f (fun v : Fin 8 => (rawP.getD v.val 0).testBit k) := by
  simp only [f, EF, Nat.testBit_or, Nat.testBit_and]
  rfl
lemma bridge (D : PEqualNP.CircuitLowerBounds.Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D)
    (hf : ∀ y : Fin 8 → Bool, D.eval (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) D.size (C (mz 0) (WZ [] 0)) := by
  obtain ⟨gates, out⟩ := D
  let row : ℕ → Fin 8 → Bool := fun k v => (rawP.getD v.val 0).testBit k
  let init : List ℕ := rawP.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, _, rfl⟩ := hx
    rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ [] 0) := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
  have hinit_bits : ∀ k, (mz 0).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by
    intro k hk
    simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]
    rw [row_list]
  have hout : (ex (mz 0) gates init).getD out 0 = tz 0 := by
    rw [← EF_ok]
    have hsub : ∀ x ∈ ex (mz 0) gates init, x &&& mz 0 = x := ex_sub (mz 0) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 0 = x}) hsub (by simp) out
    apply Nat.eq_of_testBit_eq; intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1
    rw [← e1, Nat.testBit_and]
    cases hk : (mz 0).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]
      rw [← getD_map, ex_bit (mz 0) hk gates init hD, hinit_bits k hk]
      have h := hf (row k)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn (row k))).getD out false = f (row k) at h
      rw [h]
      exact (f_bit k).symm
  exact ex_sol (mz 0) gates init (C (mz 0) (WZ [] 0))
    hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl))
    hD ⟨out, hout⟩
lemma fanInTwo_of {gates : List Gate} {o : ℕ}
    (h : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    FanInTwo ⟨gates, o⟩ := by
  intro g hg; obtain ⟨ho, hl⟩ := h g hg
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ho, hl⟩

lemma ex_sol_not {T : ℕ} (m : ℕ) (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ),
    (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ g ∈ gs, g.op = GateOp.not) →
    (∃ i, (ex m gs w).getD i 0 = T) →
    Sol Z0 m T (gs.length - 1) S ∨ ∃ t, 1 ≤ t ∧ ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T gs.length t S0 := by
  induction gs with
  | nil => intro _ _ _ _ _ _ hnot; simp at hnot
  | cons g gs ih =>
    intro w S hw h0 hm hg hnot hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have hwm_stay : gv m w g ∈ S → ∀ x ∈ w ++ [gv m w g], x ∈ S := fun h x hx => by
      simp only [List.mem_append, List.mem_singleton] at hx; rcases hx with hx | rfl; exact hw x hx; exact h
    have hwm_ins : ∀ x ∈ w ++ [gv m w g], x ∈ insert (gv m w g) S := fun x hx => by
      simp only [List.mem_append, List.mem_singleton] at hx; rcases hx with hx | rfl; exact Or.inr (hw x hx); exact Or.inl rfl
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · have hnot' : ∃ g' ∈ gs, g'.op = GateOp.not := by
        rcases hnot with ⟨g', hg', ho⟩; simp only [List.mem_cons] at hg'; rcases hg' with rfl | hg'; simp at ho; exact ⟨g', hg', ho⟩
      match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.and, []⟩]) S (hwm_stay hm) h0 hm hgs hT)
      | [i] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.and, [i]⟩]) S (hwm_stay (rd i)) h0 hm hgs hT)
      | i :: j :: _ =>
        rcases ih (w ++ [gv m w ⟨.and, i :: j :: _⟩]) (insert (op false (w.getD i 0) (w.getD j 0)) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs hnot' hT with hs | ⟨t, ht, S1, hS1, hl1⟩
        · exact Or.inl ((Sol.bi (d := false) (rd i) (rd j) (al0 _ _ _) hs).mono (by cases gs <;> simp at hnot' ⊢) subset_rfl)
        · by_cases hz : op false (w.getD i 0) (w.getD j 0) ∈ S1
          · by_cases hab : w.getD i 0 = w.getD j 0
            · have hsub : (S1 : Set ℕ) ⊆ S := fun x hx => (hS1 hx).elim (fun e => by subst e; rw [hab, op_self]; exact rd j) id
              exact Or.inl (hl1.sol.mono le_rfl hsub)
            · refine Or.inr ⟨t, ht, insert (w.getD i 0) (insert (w.getD j 0) (S1.erase (op false (w.getD i 0) (w.getD j 0)))), ?_, Live.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hz])⟩
              intro x hx; simp at hx; rcases hx with rfl | rfl | ⟨h1, h2⟩; exact rd i; exact rd j; exact (hS1 h1).resolve_left h2
          · exact Or.inl (hl1.sol.mono le_rfl (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))
    · have hnot' : ∃ g' ∈ gs, g'.op = GateOp.not := by
        rcases hnot with ⟨g', hg', ho⟩; simp only [List.mem_cons] at hg'; rcases hg' with rfl | hg'; simp at ho; exact ⟨g', hg', ho⟩
      match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.or, []⟩]) S (hwm_stay h0) h0 hm hgs hT)
      | [i] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.or, [i]⟩]) S (hwm_stay (rd i)) h0 hm hgs hT)
      | i :: j :: _ =>
        rcases ih (w ++ [gv m w ⟨.or, i :: j :: _⟩]) (insert (op true (w.getD i 0) (w.getD j 0)) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs hnot' hT with hs | ⟨t, ht, S1, hS1, hl1⟩
        · exact Or.inl ((Sol.bi (d := true) (rd i) (rd j) (al0 _ _ _) hs).mono (by cases gs <;> simp at hnot' ⊢) subset_rfl)
        · by_cases hz : op true (w.getD i 0) (w.getD j 0) ∈ S1
          · by_cases hab : w.getD i 0 = w.getD j 0
            · have hsub : (S1 : Set ℕ) ⊆ S := fun x hx => (hS1 hx).elim (fun e => by subst e; rw [hab, op_self]; exact rd j) id
              exact Or.inl (hl1.sol.mono le_rfl hsub)
            · refine Or.inr ⟨t, ht, insert (w.getD i 0) (insert (w.getD j 0) (S1.erase (op true (w.getD i 0) (w.getD j 0)))), ?_, Live.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hz])⟩
              intro x hx; simp at hx; rcases hx with rfl | rfl | ⟨h1, h2⟩; exact rd i; exact rd j; exact (hS1 h1).resolve_left h2
          · exact Or.inl (hl1.sol.mono le_rfl (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))
    · match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.not, []⟩]) S (hwm_stay hm) h0 hm hgs hT)
      | i :: _ =>
        have go := ex_sol m gs (w ++ [gv m w ⟨.not, i :: _⟩]) (insert (w.getD i 0 ^^^ m) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs hT
        obtain ⟨k, hk, t, S1, hS1, hl1⟩ := go.live
        by_cases hz : w.getD i 0 ^^^ m ∈ S1
        · have hsub : ((insert (w.getD i 0) (S1.erase (w.getD i 0 ^^^ m)) : Finset ℕ) : Set ℕ) ⊆ S := by
            intro x hx; simp at hx; rcases hx with rfl | ⟨h1, h2⟩; exact rd i; exact (hS1 h1).resolve_left h2
          have hlu : Live Z0 m T (k + 1) (t + 1) (insert (w.getD i 0) (S1.erase (w.getD i 0 ^^^ m))) := Live.un (by rwa [Finset.insert_erase hz])
          by_cases hkeq : k = gs.length
          · subst hkeq; exact Or.inr ⟨t + 1, by omega, _, hsub, hlu⟩
          · exact Or.inl (hlu.sol.mono (by simp; omega) hsub)
        · exact Or.inl (hl1.sol.mono (by simp; omega) (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))

lemma bridge_not (gates : List Gate) (o : ℕ) (hD : FanInTwo ⟨gates, o⟩) (hnot : ∃ g ∈ gates, g.op = GateOp.not)
    (hf : ∀ y : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) (gates.length - 1) (C (mz 0) (WZ [] 0)) ∨
    ∃ t, 1 ≤ t ∧ ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ C (mz 0) (WZ [] 0) ∧ Live Z0 (mz 0) (tz 0) gates.length t S0 := by
  let row : ℕ → Fin 8 → Bool := fun k v => (rawP.getD v.val 0).testBit k
  let init : List ℕ := rawP.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, _, rfl⟩ := hx; rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ [] 0) := by intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, hw, rfl⟩ := hx; exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
  have hinit_bits : ∀ k, (mz 0).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by intro k hk; simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]; rw [row_list]
  have hout : (ex (mz 0) gates init).getD o 0 = tz 0 := by
    rw [← EF_ok]
    have hsub : ∀ x ∈ ex (mz 0) gates init, x &&& mz 0 = x := ex_sub (mz 0) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 0 = x}) hsub (by simp) o
    apply Nat.eq_of_testBit_eq; intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1; rw [← e1, Nat.testBit_and]
    cases hk : (mz 0).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]; rw [← getD_map, ex_bit (mz 0) hk gates init hD, hinit_bits k hk]
      have h := hf (row k)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (row k))).getD o false = f (row k) at h
      rw [h]; exact (f_bit k).symm
  exact ex_sol_not (mz 0) gates init (C (mz 0) (WZ [] 0)) hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl)) hD hnot ⟨o, hout⟩

section onenot
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def onWit : List Gate := [⟨.or, [4, 5]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [13, 7]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [0, 16]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 18]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [20, 21]⟩]

lemma onWitBasis : ∀ g ∈ onWit,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [onWit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma onWitCorrect : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨onWit, 22⟩ (List.ofFn x) = f x := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma onGraphCorrect : ∀ x : Fin 8 → Bool, f x = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

lemma onFinal :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfit _hone hev
  have hf : ∀ y : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y := fun y => (hev y).trans (onGraphCorrect y).symm
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have hge : 15 ≤ gates.length := by
      by_contra hlt
      by_cases hlt2 : gates.length < 14
      · exact iroot gates.length hlt2 (bridge ⟨gates, o⟩ (fanInTwo_of hfit) hf)
      · have heq : gates.length = 14 := by omega
        rcases bridge_not gates o (fanInTwo_of hfit) hnot hf with hsol | ⟨t, ht1, S0, hS0, hl0⟩
        · exact iroot (gates.length - 1) (by omega) hsol
        · rw [heq] at hl0; exact iroot_pos ht1 hS0 hl0
    have hw : onWit.length = 15 := rfl
    exact ⟨onWit, 22, onWitBasis, by omega, fun x => (onWitCorrect x).trans (onGraphCorrect x)⟩
  · refine ⟨gates, o, ?_, le_rfl, hev⟩
    intro g hg; obtain ⟨ho, hl⟩ := hfit g hg; refine ⟨?_, hl⟩
    rcases ho with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hnot ⟨g, hg, h⟩).elim

end onenot
end PEqualNP.Outside.L_meta_33826

theorem PEqualNP.Outside.L_meta_33826 :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  PEqualNP.Outside.L_meta_33826.onFinal
