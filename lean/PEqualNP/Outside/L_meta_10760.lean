import PEqualNP.Defs

-- The search engine is adapted from PEqualNP.Outside.L_meta_1673 by Trey Kind (pull request 6929,Apache License 2.0).
-- This file declares its own data types (records for the search state and inductive predicates).

namespace PEqualNP.Outside.L_meta_10760
variable {R:ℕ → ℕ}
def op (d:Bool) (a b:ℕ):ℕ:=bif d then a ||| b else a &&& b
lemma op_comm (d:Bool) (a b:ℕ):op d a b = op d b a:=by
  cases d <;> simp [op,Nat.and_comm,Nat.or_comm]
lemma op_bit (d:Bool) (a b i:ℕ):(op d a b).testBit i =
    bif d then a.testBit i || b.testBit i else a.testBit i && b.testBit i:=by
  cases d <;> simp [op]
lemma op_self (d:Bool) (a:ℕ):op d a a = a:=by cases d <;> simp [op]
def Al (R:ℕ → ℕ) (d:Bool) (a b:ℕ):Prop:=(R a &&& R b) ≤ (bif d then 1 else 0)
lemma Al.symm {d:Bool} {a b:ℕ} (h:Al R d a b):Al R d b a:=by unfold Al at *; rwa [Nat.and_comm]
def Z0:ℕ → ℕ:=fun _ => 0
lemma al0 (d:Bool) (a b:ℕ):Al Z0 d a b:=by simp [Al,Z0]
inductive Sol (R:ℕ → ℕ) (m T:ℕ):ℕ → Set ℕ → Prop
  | done {q:ℕ} {S:Set ℕ}:T ∈ S → Sol R m T q S
  | un {q:ℕ} {S:Set ℕ} {a:ℕ}:a ∈ S → Sol R m T q (insert (a ^^^ m) S) → Sol R m T (q + 1) S
  | bi {q:ℕ} {S:Set ℕ} {d:Bool} {a b:ℕ}:a ∈ S → b ∈ S → Al R d a b →
      Sol R m T q (insert (op d a b) S) → Sol R m T (q + 1) S
lemma Sol.mono {m T q:ℕ} {S:Set ℕ} (h:Sol R m T q S) :
    ∀ {q':ℕ} {S':Set ℕ},q ≤ q' → S ⊆ S' → Sol R m T q' S':=by
  induction h with
  | done h => intro q' S' _ hs; exact .done (hs h)
  | un h _ ih =>
    intro q' S' hq hs
    obtain ⟨r,rfl⟩:∃ r,q' = r + 1:=⟨q' - 1,by omega⟩
    exact .un (hs h) (ih (by omega) (Set.insert_subset_insert hs))
  | bi h1 h2 ha _ ih =>
    intro q' S' hq hs
    obtain ⟨r,rfl⟩:∃ r,q' = r + 1:=⟨q' - 1,by omega⟩
    exact .bi (hs h1) (hs h2) ha (ih (by omega) (Set.insert_subset_insert hs))
lemma Sol.rel {R':ℕ → ℕ} {m T q:ℕ} {S:Set ℕ} (h:Sol R m T q S) (hR:∀ d a b,Al R d a b → Al R' d a b):Sol R' m T q S:=by
  induction h with
  | done h => exact .done h
  | un h _ ih => exact .un h ih
  | bi h1 h2 ha _ ih => exact .bi h1 h2 (hR _ _ _ ha) ih
lemma Sol.to0 {m T q:ℕ} {S:Set ℕ} (h:Sol R m T q S):Sol Z0 m T q S:=h.rel fun d a b _ => al0 d a b
inductive Live (R:ℕ → ℕ) (m T:ℕ):ℕ → ℕ → Finset ℕ → Prop
  | stop:Live R m T 0 0 {T}
  | un {k t:ℕ} {a:ℕ} {U:Finset ℕ}:Live R m T k t (insert (a ^^^ m) U) →
      Live R m T (k + 1) (t + 1) (insert a U)
  | bi {k t:ℕ} {d:Bool} {a b:ℕ} {U:Finset ℕ}:a ≠ b → Al R d a b → Live R m T k t (insert (op d a b) U) →
      Live R m T (k + 1) t (insert a (insert b U))
lemma Live.sol {m T k t:ℕ} {S:Finset ℕ} (h:Live R m T k t S):Sol Z0 m T k (S:Set ℕ):=by
  induction h with
  | stop => exact .done (by simp)
  | @un k t a U _ ih =>
    refine .un (a:=a) (by simp) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
  | @bi k t d a b U _ _ _ ih =>
    refine .bi (d:=d) (a:=a) (b:=b) (by simp) (by simp) (al0 _ _ _) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
lemma Sol.live {m T q:ℕ} {S:Set ℕ} (h:Sol R m T q S) :
    ∃ k ≤ q,∃ t,∃ S0:Finset ℕ,(S0:Set ℕ) ⊆ S ∧ Live R m T k t S0:=by
  induction h with
  | @done q S h => exact ⟨0,by omega,0,{T},by simpa using h,.stop⟩
  | @un q S a ha _ ih =>
    obtain ⟨k,hk,t,S1,hs,hl⟩:=ih
    by_cases hg:a ^^^ m ∈ S1
    · refine ⟨k + 1,by omega,t + 1,insert a (S1.erase (a ^^^ m)),?_,.un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1,h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k,by omega,t,S1,fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)),hl⟩
  | @bi q S d a b ha hb hal _ ih =>
    obtain ⟨k,hk,t,S1,hs,hl⟩:=ih
    by_cases hg:op d a b ∈ S1
    · by_cases hab:a = b
      · subst hab; rw [op_self] at hs
        exact ⟨k,by omega,t,S1,fun x hx => (hs hx).elim (fun e => e ▸ ha) id,hl⟩
      refine ⟨k + 1,by omega,t,insert a (insert b (S1.erase (op d a b))),?_,.bi hab hal (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1,h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
    · exact ⟨k,by omega,t,S1,fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)),hl⟩
def C (m:ℕ) (S:Set ℕ):Set ℕ:=S ∪ {0,m}
lemma C_mono {m:ℕ} {S S':Set ℕ} (h:S ⊆ S'):C m S ⊆ C m S':=Set.union_subset_union_left _ h
lemma sub_C (m:ℕ) (S:Set ℕ):S ⊆ C m S:=Set.subset_union_left
def Un (m a:ℕ) (S S':Finset ℕ):Prop:=∃ U,S = insert a U ∧ S' = insert (a ^^^ m) U
def Bi (R:ℕ → ℕ) (d:Bool) (a b:ℕ) (S S':Finset ℕ):Prop :=
  a ≠ b ∧ ∃ U,S = insert a (insert b U) ∧ S' = insert (op d a b) U ∧ Al R d a b
lemma Un.live {m T a k t:ℕ} {S S':Finset ℕ} (h:Un m a S S') (hl:Live R m T k t S') :
    Live R m T (k + 1) (t + 1) S:=by obtain ⟨U,rfl,rfl⟩:=h; exact .un hl
lemma Bi.live {m T a b k t:ℕ} {d:Bool} {S S':Finset ℕ} (h:Bi R d a b S S') (hl:Live R m T k t S') :
    Live R m T (k + 1) t S:=by obtain ⟨hab,U,rfl,rfl,hal⟩:=h; exact .bi hab hal hl
lemma Bi.symm {a b:ℕ} {d:Bool} {S S':Finset ℕ} (h:Bi R d a b S S'):Bi R d b a S S':=by
  obtain ⟨hab,U,rfl,rfl,hal⟩:=h
  exact ⟨hab.symm,U,Finset.insert_comm _ _ _,by rw [op_comm],hal.symm⟩
lemma Un.sub {m a:ℕ} {S S':Finset ℕ} (h:Un m a S S'):a ∈ S ∧ S' ⊆ insert (a ^^^ m) S:=by
  obtain ⟨U,rfl,rfl⟩:=h
  exact ⟨by simp,Finset.insert_subset_insert _ (Finset.subset_insert _ _)⟩
lemma Bi.sub {a b:ℕ} {d:Bool} {S S':Finset ℕ} (h:Bi R d a b S S') :
    a ∈ S ∧ b ∈ S ∧ S' ⊆ insert (op d a b) S:=by
  obtain ⟨_,U,rfl,rfl,_⟩:=h
  refine ⟨by simp,by simp,Finset.insert_subset_insert _ ?_⟩
  intro x hx; simp [hx]
def Min (R:ℕ → ℕ) (m T k t:ℕ) (S:Finset ℕ):Prop:=Live R m T k t S ∧ ∀ q < k,¬ Sol Z0 m T q (C m S)
lemma Un.sol {m T a q:ℕ} {S S':Finset ℕ} (h:Un m a S S') (hs:Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S):=by
  obtain ⟨ha,hsub⟩:=h.sub
  refine .un (a:=a) (sub_C _ _ (by simpa using ha)) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have:=hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Bi.sol {m T a b q:ℕ} {d:Bool} {S S':Finset ℕ} (h:Bi R d a b S S') (hs:Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S):=by
  obtain ⟨ha,hb,hsub⟩:=h.sub
  refine .bi (d:=d) (a:=a) (b:=b) (sub_C _ _ (by simpa using ha)) (sub_C _ _ (by simpa using hb)) (al0 _ _ _) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have:=hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Un.min {m T a k t:ℕ} {S S':Finset ℕ} (h:Un m a S S') (hl:Live R m T k t S')
    (hm:∀ q < k + 1,¬ Sol Z0 m T q (C m S)):Min R m T k t S' :=
  ⟨hl,fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Bi.min {m T a b k t:ℕ} {d:Bool} {S S':Finset ℕ} (h:Bi R d a b S S') (hl:Live R m T k t S')
    (hm:∀ q < k + 1,¬ Sol Z0 m T q (C m S)):Min R m T k t S' :=
  ⟨hl,fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Un.fresh {m T a k t:ℕ} {S S':Finset ℕ} (h:Un m a S S') (hl:Live R m T k t S')
    (hm:∀ q < k + 1,¬ Sol Z0 m T q (C m S)):a ^^^ m ∉ C m S:=by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have:=h.sub.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Bi.fresh {m T a b k t:ℕ} {d:Bool} {S S':Finset ℕ} (h:Bi R d a b S S') (hl:Live R m T k t S')
    (hm:∀ q < k + 1,¬ Sol Z0 m T q (C m S)):op d a b ∉ C m S:=by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have:=h.sub.2.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Min.size {m T:ℕ}:∀ {k t:ℕ} {S:Finset ℕ},Min R m T k t S → S.card + t ≤ k + 1 ∧ t ≤ k:=by
  intro k t S ⟨hl,hm⟩
  induction hl with
  | stop => simp
  | @un k t a U hl ih =>
    have hu:Un m a (insert a U) (insert (a ^^^ m) U):=⟨U,rfl,rfl⟩
    have ih:=ih (hu.min hl hm).2
    have hf:a ^^^ m ∉ U:=fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1:=Finset.card_insert_le a U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu:Bi R d a b (insert a (insert b U)) (insert (op d a b) U):=⟨hab,U,rfl,rfl,hal⟩
    have ih:=ih (hu.min hl hm).2
    have hf:op d a b ∉ U:=fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1:=Finset.card_insert_le a (insert b U)
    have h2:=Finset.card_insert_le b U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
def phi (a n:ℕ) (X:Finset ℕ):Finset ℕ:=insert a (X.erase n)
lemma phi_un {m a n c:ℕ} {X X':Finset ℕ} (h:Un m c X X') (h1:c ≠ n) (h2:c ^^^ m ≠ n) :
    Un m c (phi a n X) (phi a n X'):=by
  obtain ⟨U,rfl,rfl⟩:=h
  refine ⟨insert a (U.erase n),?_,?_⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_bi {a n b c:ℕ} {d:Bool} {X X':Finset ℕ} (h:Bi R d b c X X') (h1:b ≠ n) (h2:c ≠ n)
    (h3:op d b c ≠ n):Bi R d b c (phi a n X) (phi a n X'):=by
  obtain ⟨hab,U,rfl,rfl,hal⟩:=h
  refine ⟨hab,insert a (U.erase n),?_,?_,hal⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_back {m a:ℕ} {X:Finset ℕ} (h:a ^^^ m ∈ X):Un m a (phi a (a ^^^ m) X) X :=
  ⟨X.erase (a ^^^ m),rfl,by rw [Finset.insert_erase h]⟩
lemma phi_start {m a:ℕ} {S S':Finset ℕ} (h:Un m a S S') (hn:a ^^^ m ∉ S):phi a (a ^^^ m) S' = S:=by
  obtain ⟨U,rfl,rfl⟩:=h
  simp at hn
  simp [phi,hn.2]
lemma un_keep {m c n:ℕ} {X X':Finset ℕ} (h:Un m c X X') (hn:n ∈ X) (h1:c ≠ n):n ∈ X':=by
  obtain ⟨U,rfl,rfl⟩:=h
  simp at hn ⊢; exact Or.inr (hn.resolve_left (Ne.symm h1))
lemma bi_keep {b c n:ℕ} {d:Bool} {X X':Finset ℕ} (h:Bi R d b c X X') (hn:n ∈ X) (h1:b ≠ n)
    (h2:c ≠ n):n ∈ X':=by
  obtain ⟨_,U,rfl,rfl,_⟩:=h
  simp at hn ⊢; rcases hn with h | h | h
  · exact absurd h.symm h1
  · exact absurd h.symm h2
  · exact Or.inr h
lemma first_move {m T:ℕ}:∀ (k t:ℕ) (S:Finset ℕ),Min R m T k t S → 2 ≤ S.card →
    (∃ k0 d a b S1,k = k0 + 1 ∧ Bi R d a b S S1 ∧ Live R m T k0 t S1) ∨
    (∃ k0 t0 a d c S1 S2,k = k0 + 2 ∧ t = t0 + 1 ∧ Un m a S S1 ∧ Bi R d (a ^^^ m) c S1 S2 ∧ Live R m T k0 t0 S2) ∨
    (∃ k0 t0 a a' d S1 S2 S3,k = k0 + 3 ∧ t = t0 + 2 ∧ Un m a S S1 ∧ a' ≠ a ^^^ m ∧ Un m a' S1 S2 ∧
      Bi R d (a ^^^ m) (a' ^^^ m) S2 S3 ∧ Live R m T k0 t0 S3):=by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro t S hS hc
  obtain ⟨hl,hm⟩:=hS
  cases hl with
  | stop => simp at hc
  | @bi k t d a b U hab hal hl => exact Or.inl ⟨k,d,a,b,_,rfl,⟨hab,U,rfl,rfl,hal⟩,hl⟩
  | @un k t a U hl =>
    have hu:Un m a (insert a U) (insert (a ^^^ m) U):=⟨U,rfl,rfl⟩
    have hf:=hu.fresh hl hm
    have hn:a ^^^ m ∉ insert a U:=fun h => hf (sub_C _ _ (by simpa using h))
    have hmin:=hu.min hl hm
    have hxx:∀ c:ℕ,c ^^^ m ^^^ m = c:=fun c => by simp
    have hc':2 ≤ (insert (a ^^^ m) U).card:=by
      have h1:=Finset.card_insert_le a U
      rw [Finset.card_insert_of_notMem (fun h => hn (by simp [h]))]; omega
    generalize hS1:insert (a ^^^ m) U = S1 at *
    have hnS1:a ^^^ m ∈ S1:=by rw [← hS1]; simp
    have hst:=phi_start hu hn
    have dbl:∀ {c k2 t2 S2},Un m c S1 S2 → Live R m T k2 t2 S2 → k = k2 + 1 → c ≠ a ^^^ m ∧ c ^^^ m ≠ a ^^^ m:=by
      intro c k2 t2 S2 h2 hl2 hk
      constructor
      · rintro rfl
        have hsub:=h2.sub.2
        rw [hxx] at hsub
        apply hm (k2 + 1) (by omega)
        refine .un (a:=a) (sub_C _ _ (by simp)) (hl2.sol.mono le_rfl fun x hx => ?_)
        have h3:=hsub hx
        have h4:x ∈ insert a (insert (a ^^^ m) U):=by rw [hS1]; exact h3
        simp at h4
        rcases h4 with rfl | rfl | h4
        · exact Or.inr (sub_C _ _ (by simp))
        · exact Or.inl rfl
        · exact Or.inr (sub_C _ _ (by simp [h4]))
      · intro e
        exact h2.fresh hl2 (by rw [← hk]; exact hmin.2) (sub_C _ _ (by rw [e]; simpa using hnS1))
    rcases ih k (by omega) t S1 hmin hc' with
      ⟨k0,d,x,y,S2,rfl,hb,hl2⟩ | ⟨k0,t0,c,d,y,S2,S3,rfl,rfl,h1,hb,hl2⟩ |
      ⟨k0,t0,c,c',d,S2,S3,S4,rfl,rfl,h1,hne,h2,hb,hl2⟩
    · by_cases hx:x = a ^^^ m
      · subst hx; exact Or.inr (Or.inl ⟨k0,t,a,d,y,S1,S2,rfl,rfl,hu,hb,hl2⟩)
      by_cases hy:y = a ^^^ m
      · subst hy; exact Or.inr (Or.inl ⟨k0,t,a,d,x,S1,S2,rfl,rfl,hu,hb.symm,hl2⟩)
      have hg:op d x y ≠ a ^^^ m:=fun e => hb.fresh hl2 hmin.2 (sub_C _ _ (by rw [e]; simpa using hnS1))
      refine Or.inl ⟨k0 + 1,d,x,y,phi a (a ^^^ m) S2,rfl,?_,?_⟩
      · rw [← hst]; exact phi_bi hb hx hy hg
      · exact (phi_back (bi_keep hb hnS1 hx hy)).live hl2
    · have hb1:=hb.live hl2
      obtain ⟨n1,n2⟩:=dbl h1 hb1 rfl
      have hm2:=h1.min hb1 hmin.2
      by_cases hy:y = a ^^^ m
      · subst hy
        exact Or.inr (Or.inr ⟨k0,t0,a,c,d,S1,S2,S3,rfl,rfl,hu,n1,h1,hb.symm,hl2⟩)
      have hk2:=un_keep h1 hnS1 n1
      have hg:op d (c ^^^ m) y ≠ a ^^^ m:=fun e => hb.fresh hl2 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      refine Or.inr (Or.inl ⟨k0 + 1,t0 + 1,c,d,y,phi a (a ^^^ m) S2,phi a (a ^^^ m) S3,rfl,rfl,?_,phi_bi hb n2 hy hg,?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk2 n2 hy)).live hl2
    · have hb1:=hb.live hl2
      have hb2:=h2.live hb1
      obtain ⟨n1,n2⟩:=dbl h1 hb2 rfl
      have hm2:=h1.min hb2 hmin.2
      have hk2:=un_keep h1 hnS1 n1
      have hm3:=h2.min hb1 hm2.2
      have n3:c' ≠ a ^^^ m:=by
        rintro rfl
        have hsub:=h2.sub.2
        rw [hxx] at hsub
        obtain ⟨hcS,hsub1⟩:=h1.sub
        have hcS':c ∈ insert a U:=by
          have:c ∈ insert (a ^^^ m) U:=by rw [hS1]; exact hcS
          simp at this ⊢; exact Or.inr (this.resolve_left n1)
        apply hm (k0 + 1 + 1 + 1) (by omega)
        refine .un (a:=a) (sub_C _ _ (by simp)) (.un (a:=c) (Or.inr (sub_C _ _ (by simpa using hcS'))) (hb1.sol.mono le_rfl fun x hx => ?_))
        have h3:x = a ∨ x = c ^^^ m ∨ x ∈ S1:=by
          have:=hsub hx; simp at this
          rcases this with h | h
          · exact Or.inl h
          · have:=hsub1 h; simp at this; exact Or.inr this
        rcases h3 with rfl | rfl | h3
        · exact Or.inr (Or.inr (sub_C _ _ (by simp)))
        · exact Or.inl rfl
        · rw [← hS1] at h3; simp at h3
          rcases h3 with rfl | h3
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (sub_C _ _ (by simp [h3])))
      have n4:c' ^^^ m ≠ a ^^^ m:=fun e => h2.fresh hb1 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      have hk3:=un_keep h2 hk2 n3
      have hg:op d (c ^^^ m) (c' ^^^ m) ≠ a ^^^ m:=fun e => hb.fresh hl2 hm3.2 (sub_C _ _ (by rw [e]; simpa using hk3))
      refine Or.inr (Or.inr ⟨k0 + 1,t0 + 1,c,c',d,phi a (a ^^^ m) S2,phi a (a ^^^ m) S3,phi a (a ^^^ m) S4,rfl,rfl,?_,hne,
        phi_un h2 n3 n4,phi_bi hb n2 n4 hg,?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk3 n2 n4)).live hl2
lemma and_op (d:Bool) (a b n:ℕ):op d a b &&& n = op d (a &&& n) (b &&& n):=by
  apply Nat.eq_of_testBit_eq; intro i
  cases d <;> simp [op_bit] <;> grind
lemma and_neg {m n:ℕ} (hn:n &&& m = n) (a:ℕ):(a ^^^ m) &&& n = (a &&& n) ^^^ n:=by
  apply Nat.eq_of_testBit_eq; intro i
  have:=congrArg (fun x => x.testBit i) hn
  simp at this ⊢
  grind
abbrev Cst (n x:ℕ):Prop:=x &&& n = 0 ∨ x &&& n = n
def Im (n:ℕ) (S:Finset ℕ):Set ℕ:=(fun x => x &&& n) '' (S:Set ℕ)
lemma Im_mem {n x:ℕ} {S:Finset ℕ} (h:x ∈ S):x &&& n ∈ C n (Im n S):=Or.inl ⟨x,by simpa using h,rfl⟩
lemma Cst_mem {n x:ℕ} {S:Set ℕ} (h:Cst n x):x &&& n ∈ C n S:=by
  rcases h with h | h <;> simp [C,h]
lemma Cst_neg {m n a:ℕ} (hn:n &&& m = n):Cst n (a ^^^ m) ↔ Cst n a:=by
  unfold Cst; rw [and_neg hn]
  constructor
  · rintro (h | h)
    · right; have:=congrArg (· ^^^ n) h; simpa using this
    · left; have:=congrArg (· ^^^ n) h; simpa using this
  · rintro (h | h) <;> simp [h]
lemma op_cst {n a b:ℕ} (d:Bool) (ha:Cst n a) :
    op d a b &&& n = 0 ∨ op d a b &&& n = n ∨ op d a b &&& n = b &&& n:=by
  rw [and_op]
  rcases ha with h | h <;> rw [h] <;> cases d
  · left; simp [op]
  · right; right; simp [op]
  · right; right; apply Nat.eq_of_testBit_eq; intro i; simp [op]
  · right; left; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_cst2 {n a b:ℕ} (d:Bool) (ha:Cst n a) (hb:Cst n b):Cst n (op d a b):=by
  rcases op_cst (b:=b) d ha with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · unfold Cst at hb ⊢; rw [h]; exact hb
lemma op_cst_mem {n a b:ℕ} {S:Finset ℕ} (d:Bool) (h:Cst n a ∨ Cst n b) (ha:a ∈ S) (hb:b ∈ S) :
    op d a b &&& n ∈ C n (Im n S):=by
  rcases h with h | h
  · rcases op_cst (b:=b) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem hb
  · rw [op_comm]
    rcases op_cst (b:=a) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem ha
lemma C_Im_sub {n g:ℕ} {S S':Finset ℕ} {Q:Set ℕ} (h:S' ⊆ insert g S) (hg:g &&& n ∈ Q)
    (hQ:C n (Im n S) ⊆ Q):C n (Im n S') ⊆ Q:=by
  rintro x (⟨y,hy,rfl⟩ | hx)
  · have:=h hy; simp at this
    rcases this with rfl | h'
    · exact hg
    · exact hQ (Im_mem h')
  · exact hQ (Or.inr hx)
section proj
variable {m T n:ℕ} (hn:n &&& m = n)
include hn
lemma Un.im {a q:ℕ} {S S':Finset ℕ} (h:Un m a S S') (hs:Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)):=by
  obtain ⟨ha,hsub⟩:=h.sub
  refine .un (Im_mem ha) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_neg hn]; exact Or.inl rfl
omit hn in
lemma Bi.im {a b q:ℕ} {d:Bool} {S S':Finset ℕ} (h:Bi R d a b S S') (hs:Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)):=by
  obtain ⟨ha,hb,hsub⟩:=h.sub
  refine .bi (d:=d) (Im_mem ha) (Im_mem hb) (al0 _ _ _) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
lemma Un.kill {a q:ℕ} {S S':Finset ℕ} (h:Un m a S S') (hc:Cst n a) (hs:Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2 (Cst_mem ((Cst_neg hn).2 hc)) subset_rfl)
omit hn in
lemma Bi.kill {a b q:ℕ} {d:Bool} {S S':Finset ℕ} (h:Bi R d a b S S') (hc:Cst n a ∨ Cst n b)
    (hs:Sol Z0 n (T &&& n) q (C n (Im n S'))):Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)
lemma Min.const (hT0:T &&& n ≠ 0) (hT1:T &&& n ≠ n) {k t:ℕ} {S:Finset ℕ} (h:Min R m T k t S) :
    ∃ q,q + (S.filter (Cst n)).card ≤ k ∧ Sol Z0 n (T &&& n) q (C n (Im n S)):=by
  obtain ⟨hl,hm⟩:=h
  induction hl with
  | stop =>
    refine ⟨0,?_,.done (Im_mem (by simp))⟩
    rw [Finset.filter_eq_empty_iff.2]; · simp
    intro x hx; simp at hx; subst hx
    rintro (h | h); exacts [hT0 h,hT1 h]
  | @un k t a U hl ih =>
    have hu:Un m a (insert a U) (insert (a ^^^ m) U):=⟨U,rfl,rfl⟩
    obtain ⟨q,hq,hs⟩:=ih (hu.min hl hm).2
    have h1:(U.filter (Cst n)).card ≤ ((insert (a ^^^ m) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    by_cases hc:Cst n a
    · refine ⟨q,?_,hu.kill hn hc hs⟩
      rw [Finset.filter_insert,ite_eq_left hc]
      have:=Finset.card_insert_le a (U.filter (Cst n)); omega
    · refine ⟨q + 1,?_,hu.im hn hs⟩
      rw [Finset.filter_insert,ite_eq_right hc]; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu:Bi R d a b (insert a (insert b U)) (insert (op d a b) U):=⟨hab,U,rfl,rfl,hal⟩
    obtain ⟨q,hq,hs⟩:=ih (hu.min hl hm).2
    have hf:op d a b ∉ U:=fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1:(U.filter (Cst n)).card ≤ ((insert (op d a b) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have ca:=Finset.card_insert_le a (U.filter (Cst n))
    have cb:=Finset.card_insert_le b (U.filter (Cst n))
    by_cases hca:Cst n a
    · refine ⟨q,?_,hu.kill (Or.inl hca) hs⟩
      rw [Finset.filter_insert,ite_eq_left hca,Finset.filter_insert]
      by_cases hcb:Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert,ite_eq_left (op_cst2 d hca hcb),Finset.card_insert_of_notMem (by simp [hf])] at hq
        have:=Finset.card_insert_le a (insert b (U.filter (Cst n))); omega
      · rw [ite_eq_right hcb]; omega
    · rw [Finset.filter_insert,ite_eq_right hca,Finset.filter_insert]
      by_cases hcb:Cst n b
      · refine ⟨q,?_,hu.kill (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]; omega
      · refine ⟨q + 1,?_,hu.im hs⟩
        rw [ite_eq_right hcb]; omega
end proj
lemma Min.proper {m T k t:ℕ} (hT:T &&& m = T) (hT0:T ≠ 0) (hT1:T ≠ m) {S:Finset ℕ} (hS:∀ x ∈ S,x &&& m = x)
    (h:Min R m T k t S):0 ∉ S ∧ m ∉ S:=by
  obtain ⟨q,hq,hs⟩:=h.const (n:=m) (by simp) (by rwa [hT]) (by rwa [hT])
  have hi:Im m S = (S:Set ℕ):=by
    ext x; constructor
    · rintro ⟨y,hy,rfl⟩; have:=hS y hy; simp only; rw [this]; exact hy
    · intro hx; exact ⟨x,hx,hS x hx⟩
  rw [hi,hT] at hs
  have key:∀ x ∈ S,¬ Cst m x:=by
    intro x hx hc
    have:0 < (S.filter (Cst m)).card:=Finset.card_pos.2 ⟨x,by simp [hx,hc]⟩
    exact h.2 q (by omega) hs
  exact ⟨fun h0 => key 0 h0 (Or.inl (by simp)),fun h1 => key m h1 (Or.inr (by simp))⟩
def sepb (N:ℕ) (d:Bool) (w i:ℕ):Bool :=
  bif d then xor (w.testBit i) (w.testBit (N + i)) else w.testBit i && !w.testBit (N + i)
def pos' (t:ℕ):Bool:=decide (0 < t)
section cov
variable {N m T i:ℕ} (m1:m.testBit i = true) (m2:m.testBit (N + i) = true)
  (t1:T.testBit i = true) (t2:T.testBit (N + i) = false)
include t1 t2 m1 m2
lemma Live.cov {k t:ℕ} {S:Finset ℕ} (h:Live R m T k t S):∃ w ∈ S,sepb N (pos' t) w i = true:=by
  induction h with
  | stop => exact ⟨T,by simp,by simp [sepb,pos',t1,t2]⟩
  | @un k t a U _ ih =>
    obtain ⟨w,hw,hs⟩:=ih
    have weak:sepb N true w i = true:=by
      revert hs; cases pos' t <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨a,by simp,?_⟩
      revert weak; simp [sepb,pos',m1,m2]
    · exact ⟨w,by simp [hw],by simpa [pos'] using weak⟩
  | @bi k t d a b U _ _ _ ih =>
    obtain ⟨w,hw,hs⟩:=ih
    simp at hw
    rcases hw with rfl | hw
    · by_cases ha:sepb N (pos' t) a i = true
      · exact ⟨a,by simp,ha⟩
      · refine ⟨b,by simp,?_⟩
        revert hs ha
        unfold sepb; simp only [op_bit]
        cases pos' t <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact ⟨w,by simp [hw],hs⟩
end cov
def Uq (N:ℕ) (e:Bool) (S:Finset ℕ) (a i:ℕ):Prop :=
  sepb N e a i = true ∧ ∀ c ∈ S,c ≠ a → sepb N e c i = false
lemma sepb_weak {N w i:ℕ} (e:Bool) (h:sepb N e w i = true):sepb N true w i = true:=by
  revert h; cases e <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
section rect
variable {N m T:ℕ}
def Lg (N m T i:ℕ):Prop:=m.testBit i = true ∧ m.testBit (N + i) = true ∧ T.testBit i = true ∧ T.testBit (N + i) = false
lemma bi_uq {a b k t c i:ℕ} {d e:Bool} {U:Finset ℕ} (he:e = true ∨ e = pos' t) (hl:Live R m T k t (insert (op d a b) U))
    (ha:a ∉ U) (hb:b ∉ U) (hi:Lg N m T i)
    (hc:c ∈ insert a (insert b U)) (h:Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i:=by
  obtain ⟨w,hw,hs⟩:=hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs:sepb N e w i = true:=by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc:c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hU:∀ x ∈ U,sepb N e x i = false:=by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl
      rcases hcc with rfl | rfl; exacts [ha hx,hb hx]
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs,fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1,fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1:=h.2 a (by simp) (Ne.symm hcc.1)
      have h2:=h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma un_uq {a c i:ℕ} {U:Finset ℕ} (hi:Lg N m T i) (ha:a ∉ U)
    (hc:c ∈ insert a U) (h:Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i:=by
  have hn:sepb N true (a ^^^ m) i = sepb N true a i:=by simp [sepb,hi.1,hi.2.1]
  by_cases hcc:c = a
  · rw [ite_eq_left hcc]; subst hcc
    refine ⟨by rw [hn]; exact h.1,fun x hx hne => ?_⟩
    simp at hx
    exact h.2 x (by simp [hx.resolve_left hne]) (fun e => ha (e ▸ hx.resolve_left hne))
  · rw [ite_eq_right hcc]
    refine ⟨h.1,fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hcc)
    · exact h.2 x (by simp [hx]) hne
lemma phi_mem {x y g c:ℕ} {U:Finset ℕ} (hc:c ∈ insert x (insert y U)) :
    (if c = x ∨ c = y then g else c) ∈ insert g U:=by
  split_ifs with h
  · simp
  · simp only [Finset.mem_insert] at hc ⊢; tauto
lemma phi_ne {x y g a b:ℕ} {U:Finset ℕ} (hg:g ∉ U) (ha:a ∈ insert x (insert y U)) (hb:b ∈ insert x (insert y U))
    (hab:a ≠ b) (h:¬ ((a = x ∨ a = y) ∧ (b = x ∨ b = y))) :
    (if a = x ∨ a = y then g else a) ≠ (if b = x ∨ b = y then g else b):=by
  simp only [Finset.mem_insert] at ha hb
  split_ifs with p q q
  · exact absurd ⟨p,q⟩ h
  · rintro rfl; tauto
  · rintro rfl; tauto
  · exact hab
lemma bi_tight {a b k t:ℕ} {d:Bool} {U:Finset ℕ} (hab:a ≠ b) (hal:Al R d a b) (hl:Live R m T k t (insert (op d a b) U))
    (hm:∀ q < k + 1,¬ Sol Z0 m T q (C m ((insert a (insert b U):Finset ℕ):Set ℕ)))
    (hc:(insert a (insert b U)).card + t = k + 2) :
    a ∉ U ∧ b ∉ U ∧ op d a b ∉ U ∧ (insert (op d a b) U).card + t = k + 1 ∧ Min R m T k t (insert (op d a b) U):=by
  have hu:Bi R d a b (insert a (insert b U)) (insert (op d a b) U):=⟨hab,U,rfl,rfl,hal⟩
  have hf:op d a b ∉ U:=fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin:=hu.min hl hm
  have hs:=hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1:=Finset.card_insert_le a (insert b U)
  have h2:=Finset.card_insert_le b U
  have ha:a ∉ insert b U:=fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  have hb:b ∉ U:=fun h => by rw [Finset.insert_eq_of_mem h] at hc h1; omega
  exact ⟨fun h => ha (by simp [h]),hb,hf,by omega,hmin⟩
lemma un_tight {a k t:ℕ} {U:Finset ℕ} (hl:Live R m T k t (insert (a ^^^ m) U))
    (hm:∀ q < k + 1,¬ Sol Z0 m T q (C m ((insert a U:Finset ℕ):Set ℕ)))
    (hc:(insert a U).card + (t + 1) = k + 2) :
    a ∉ U ∧ a ^^^ m ∉ U ∧ (insert (a ^^^ m) U).card + t = k + 1 ∧ Min R m T k t (insert (a ^^^ m) U):=by
  have hu:Un m a (insert a U) (insert (a ^^^ m) U):=⟨U,rfl,rfl⟩
  have hf:a ^^^ m ∉ U:=fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin:=hu.min hl hm
  have hs:=hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1:=Finset.card_insert_le a U
  have ha:a ∉ U:=fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  exact ⟨ha,hf,by omega,hmin⟩
lemma rect0 {k:ℕ} {S:Finset ℕ} (hl:Live R m T k 0 S) (hm:∀ q < k,¬ Sol Z0 m T q (C m (S:Set ℕ)))
    (hc:S.card = k + 1) {i1 i2 j1 j2:ℕ} (h1:Lg N m T i1) (h2:Lg N m T i2) (h3:Lg N m T j1) (h4:Lg N m T j2) :
    ∀ {a b:ℕ},a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S,w.testBit i1 = w.testBit i2) → (∀ w ∈ S,w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N false S a i1 → Uq N false S b i2 → Uq N false S a j1 → Uq N false S b j2 → False:=by
  generalize ht:0 = t at hl
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | un => omega
  | @bi k t d x y U hxy hal hl ih =>
    subst ht
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx,hy,hg,hc',hmin⟩:=bi_tight hxy hal hl hm (by simpa using hc)
    have tr:∀ {c i},Lg N m T i → c ∈ insert x (insert y U) → Uq N false (insert x (insert y U)) c i →
        Uq N false (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inr (by simp [pos'])) hl hx hy hi hc h
    by_cases hab':(a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1:=tr h1 ha u1; have v2:=tr h2 hb u2; have v3:=tr h3 ha u3; have v4:=tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hop:op d x y = op d a b:=by
        rcases hab' with ⟨rfl | rfl,rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4
      have e1:=r1 b hb; have e2:=r2 b hb
      have n1:=u1.2 b hb (Ne.symm hab); have n3:=u3.2 b hb (Ne.symm hab)
      have s1:=v1.1; have s3:=v3.1; have s2:=u2.1; have s4:=u4.1
      revert e1 e2 n1 n3 s1 s3 s2 s4
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 (by simpa using hc') rfl ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit,r1 x (by simp),r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit,r2 x (by simp),r2 y (by simp)]
        · exact r2 w (by simp [hw])
lemma polar {k t:ℕ} {S:Finset ℕ} (hl:Live R m T k t S) (hm:∀ q < k,¬ Sol Z0 m T q (C m (S:Set ℕ)))
    (hc:S.card + t = k + 1) {i j:ℕ} (h1:Lg N m T i) (h2:Lg N m T j) :
    ∀ {a:ℕ},a ∈ S → Uq N true S a i → Uq N true S a j → a.testBit i = a.testBit j:=by
  induction hl with
  | stop => intro a ha _ _; simp at ha; subst ha; rw [h1.2.2.1,h2.2.2.1]
  | @un k t x U hl ih =>
    intro a ha u1 u2
    obtain ⟨hx,hg,hc',hmin⟩:=un_tight hl hm (by omega)
    have:=ih hmin.2 hc' (a:=if a = x then x ^^^ m else a) (by split_ifs with h <;> simp at ha ⊢; tauto)
      (un_uq h1 hx ha u1) (un_uq h2 hx ha u2)
    split_ifs at this with h
    · subst h; simpa [h1.1,h2.1] using this
    · exact this
  | @bi k t d x y U hxy hal hl ih =>
    intro a ha u1 u2
    obtain ⟨hx,hy,hg,hc',hmin⟩:=bi_tight hxy hal hl hm (by omega)
    have v1:=bi_uq (Or.inl rfl) hl hx hy h1 ha u1
    have v2:=bi_uq (Or.inl rfl) hl hx hy h2 ha u2
    have:=ih hmin.2 hc' (phi_mem ha) v1 v2
    split_ifs at this v1 v2 with h
    · obtain ⟨b,hb,hab,hop⟩:∃ b ∈ insert x (insert y U),b ≠ a ∧ op d x y = op d a b:=by
        rcases h with rfl | rfl
        · exact ⟨y,by simp,Ne.symm hxy,rfl⟩
        · exact ⟨x,by simp,hxy,op_comm _ _ _⟩
      rw [hop] at this v1 v2
      have n1:=u1.2 b hb hab; have n2:=u2.2 b hb hab
      have s1:=v1.1; have s2:=v2.1; have p1:=u1.1; have p2:=u2.1
      revert this n1 n2 s1 s2 p1 p2
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · exact this
lemma rect1 {k t:ℕ} {S:Finset ℕ} (hl:Live R m T k t S) (hm:∀ q < k,¬ Sol Z0 m T q (C m (S:Set ℕ)))
    (hc:S.card + t = k + 1) {i1 i2 j1 j2:ℕ} (h1:Lg N m T i1) (h2:Lg N m T i2) (h3:Lg N m T j1) (h4:Lg N m T j2) :
    ∀ {a b:ℕ},a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S,w.testBit i1 = w.testBit i2) → (∀ w ∈ S,w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N true S a i1 → Uq N true S b i2 → Uq N true S a j1 → Uq N true S b j2 → False:=by
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t x U hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx,hg,hc',hmin⟩:=un_tight hl hm (by omega)
    refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (un_uq h1 hx ha u1) (un_uq h2 hx hb u2) (un_uq h3 hx ha u3) (un_uq h4 hx hb u4)
    · split_ifs with h <;> simp at ha ⊢; tauto
    · split_ifs with h <;> simp at hb ⊢; tauto
    · split_ifs with p q q
      · exact absurd (p.trans q.symm) hab
      · intro e; simp at hb; rw [← e] at hb; rcases hb with h | h
        · exact q (by rw [← e,h])
        · exact hg h
      · intro e; simp at ha; rw [e] at ha; rcases ha with h | h
        · exact p (by rw [e,h])
        · exact hg h
      · exact hab
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r1 x (by simp),h1.1,h2.1]
      · exact r1 w (by simp [hw])
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r2 x (by simp),h3.2.1,h4.2.1]
      · exact r2 w (by simp [hw])
  | @bi k t d x y U hxy hal hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx,hy,hg,hc',hmin⟩:=bi_tight hxy hal hl hm (by omega)
    have tr:∀ {c i},Lg N m T i → c ∈ insert x (insert y U) → Uq N true (insert x (insert y U)) c i →
        Uq N true (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inl rfl) hl hx hy hi hc h
    by_cases hab':(a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1:=tr h1 ha u1; have v2:=tr h2 hb u2; have v3:=tr h3 ha u3; have v4:=tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hpol:=polar hl hmin.2 hc' h1 h3 (by simp) v1 v3
      have hop:op d x y = op d a b:=by
        rcases hab' with ⟨rfl | rfl,rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4 hpol
      have e1:=r1 a ha; have e2:=r2 a ha; have e1b:=r1 b hb; have e2b:=r2 b hb
      have n1:=u1.2 b hb (Ne.symm hab); have n3:=u3.2 b hb (Ne.symm hab)
      have n2:=u2.2 a ha hab; have n4:=u4.2 a ha hab
      have s1:=v1.1; have s3:=v3.1; have s2:=v2.1; have s4:=v4.1
      have p1:=u1.1; have p2:=u2.1; have p3:=u3.1; have p4:=u4.1
      revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 p1 p2 p3 p4 hpol
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit,r1 x (by simp),r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit,r2 x (by simp),r2 y (by simp)]
        · exact r2 w (by simp [hw])
end rect
section chrom
variable {N m T:ℕ}
def Ht (N m T:ℕ) (e:Bool) (S:Finset ℕ) (a b:ℕ):Prop:=∃ i1 i2 j1 j2,Lg N m T i1 ∧ Lg N m T i2 ∧ Lg N m T j1 ∧ Lg N m T j2 ∧
  (∀ w ∈ S,w.testBit i1 = w.testBit i2) ∧ (∀ w ∈ S,w.testBit (N + j1) = w.testBit (N + j2)) ∧
  Uq N e S a i1 ∧ Uq N e S b i2 ∧ Uq N e S a j1 ∧ Uq N e S b j2 ∧ a.testBit i1 = a.testBit j1 ∧ b.testBit i2 = b.testBit j2
lemma Ht.symm {e:Bool} {S:Finset ℕ} {a b:ℕ} (h:Ht N m T e S a b):Ht N m T e S b a:=by
  obtain ⟨i1,i2,j1,j2,l1,l2,l3,l4,r1,r2,u1,u2,u3,u4,p1,p2⟩:=h
  exact ⟨i2,i1,j2,j1,l2,l1,l4,l3,fun w hw => (r1 w hw).symm,fun w hw => (r2 w hw).symm,u2,u1,u4,u3,p2,p1⟩
lemma bi_uq2 {a b k t c i:ℕ} {d e:Bool} {U:Finset ℕ} (he:e = true ∨ e = pos' t) (hl:Live R m T k t (insert (op d a b) U))
    (hi:Lg N m T i) (hc:c ∈ insert a (insert b U)) (h1:c = a → a ∉ U) (h2:c = b → b ∉ U)
    (h:Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i:=by
  obtain ⟨w,hw,hs⟩:=hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs:sepb N e w i = true:=by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc:c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hcU:c ∉ U:=by
      rcases hcc with rfl | rfl; exacts [h1 rfl,h2 rfl]
    have hU:∀ x ∈ U,sepb N e x i = false:=by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl; exact hcU hx
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs,fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1,fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1:=h.2 a (by simp) (Ne.symm hcc.1)
      have h2:=h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma pol_op {a b i:ℕ} {d e:Bool} (ha:sepb N e a i = true) (hb:sepb N e b i = false) (ho:sepb N e (op d a b) i = true) :
    (op d a b).testBit i = a.testBit i:=by
  revert ha hb ho; unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
    cases b.testBit (N + i) <;> simp
lemma pol_phi {a b c i:ℕ} {d e:Bool} {U:Finset ℕ} (hab:a ≠ b) (h:Uq N e (insert a (insert b U)) c i)
    (hu:Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i) :
    (if c = a ∨ c = b then op d a b else c).testBit i = c.testBit i:=by
  by_cases hcc:c = a ∨ c = b
  · rw [ite_eq_left hcc] at hu ⊢
    rcases hcc with rfl | rfl
    · exact pol_op h.1 (h.2 b (by simp) (Ne.symm hab)) hu.1
    · rw [op_comm] at hu ⊢
      exact pol_op h.1 (h.2 a (by simp) hab) hu.1
  · rw [ite_eq_right hcc]
lemma ht_bi {a b k t c1 c2:ℕ} {d e:Bool} {U:Finset ℕ} (hab:a ≠ b) (he:e = true ∨ e = pos' t) (hl:Live R m T k t (insert (op d a b) U))
    (hc1:c1 ∈ insert a (insert b U)) (hc2:c2 ∈ insert a (insert b U))
    (h1:c1 = a → a ∉ U) (h1':c1 = b → b ∉ U) (h2:c2 = a → a ∉ U) (h2':c2 = b → b ∉ U)
    (h:Ht N m T e (insert a (insert b U)) c1 c2) :
    Ht N m T e (insert (op d a b) U) (if c1 = a ∨ c1 = b then op d a b else c1) (if c2 = a ∨ c2 = b then op d a b else c2):=by
  obtain ⟨i1,i2,j1,j2,l1,l2,l3,l4,r1,r2,u1,u2,u3,u4,p1,p2⟩:=h
  have v1:=bi_uq2 he hl l1 hc1 h1 h1' u1
  have v2:=bi_uq2 he hl l2 hc2 h2 h2' u2
  have v3:=bi_uq2 he hl l3 hc1 h1 h1' u3
  have v4:=bi_uq2 he hl l4 hc2 h2 h2' u4
  refine ⟨i1,i2,j1,j2,l1,l2,l3,l4,?_,?_,v1,v2,v3,v4,?_,?_⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit,r1 a (by simp),r1 b (by simp)]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit,r2 a (by simp),r2 b (by simp)]
    · exact r2 w (by simp [hw])
  · rw [pol_phi hab u1 v1,pol_phi hab u3 v3,p1]
  · rw [pol_phi hab u2 v2,pol_phi hab u4 v4,p2]
lemma ht_merge {a b k t:ℕ} {d e:Bool} {U:Finset ℕ} (hab:a ≠ b) (he:e = true ∨ e = pos' t) (hl:Live R m T k t (insert (op d a b) U))
    (ha:a ∉ U) (hb:b ∉ U) (h:Ht N m T e (insert a (insert b U)) a b):False:=by
  obtain ⟨i1,i2,j1,j2,l1,l2,l3,l4,r1,r2,u1,u2,u3,u4,p1,p2⟩:=h
  have v1:=(bi_uq2 he hl l1 (by simp) (fun _ => ha) (fun _ => hb) u1).1
  have v2:=(bi_uq2 he hl l2 (by simp) (fun _ => ha) (fun _ => hb) u2).1
  have v3:=(bi_uq2 he hl l3 (by simp) (fun _ => ha) (fun _ => hb) u3).1
  have v4:=(bi_uq2 he hl l4 (by simp) (fun _ => ha) (fun _ => hb) u4).1
  simp only [true_or,or_true,if_true] at v1 v2 v3 v4
  have e1:=r1 a (by simp); have e2:=r2 a (by simp); have e1b:=r1 b (by simp); have e2b:=r2 b (by simp)
  have n1:=u1.2 b (by simp) (Ne.symm hab); have n3:=u3.2 b (by simp) (Ne.symm hab)
  have n2:=u2.2 a (by simp) hab; have n4:=u4.2 a (by simp) hab
  have s1:=u1.1; have s2:=u2.1; have s3:=u3.1; have s4:=u4.1
  revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 v1 v2 v3 v4 p1 p2
  unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> simp <;> grind
lemma un_uq2 {a c i:ℕ} {U:Finset ℕ} (hi:Lg N m T i) (h1:c = a → a ∉ U) (hc:c ∈ insert a U) (h:Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i:=by
  by_cases hca:c = a
  · exact un_uq hi (h1 hca) hc h
  · rw [ite_eq_right hca]
    have hn:sepb N true (a ^^^ m) i = sepb N true a i:=by simp [sepb,hi.1,hi.2.1]
    refine ⟨h.1,fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
    · exact h.2 x (by simp [hx]) hne
lemma ht_un {a c1 c2:ℕ} {U:Finset ℕ} (hc1:c1 ∈ insert a U) (hc2:c2 ∈ insert a U) (h1:c1 = a → a ∉ U) (h2:c2 = a → a ∉ U)
    (h:Ht N m T true (insert a U) c1 c2) :
    Ht N m T true (insert (a ^^^ m) U) (if c1 = a then a ^^^ m else c1) (if c2 = a then a ^^^ m else c2):=by
  obtain ⟨i1,i2,j1,j2,l1,l2,l3,l4,r1,r2,u1,u2,u3,u4,p1,p2⟩:=h
  have pp:∀ {c i j:ℕ},m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
      (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j:=by
    intro c i j m1 m2 p
    split_ifs with h
    · subst h; simp [m1,m2,p]
    · exact p
  refine ⟨i1,i2,j1,j2,l1,l2,l3,l4,?_,?_,un_uq2 l1 h1 hc1 u1,un_uq2 l2 h2 hc2 u2,un_uq2 l3 h1 hc1 u3,un_uq2 l4 h2 hc2 u4,
    pp l1.1 l3.1 p1,pp l2.1 l4.1 p2⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r1 a (by simp),l1.1,l2.1]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r2 a (by simp),l3.2.1,l4.2.1]
    · exact r2 w (by simp [hw])
lemma chrom {e:Bool} {k t:ℕ} {S:Finset ℕ} (hl:Live R m T k t S) (hm:∀ q < k,¬ Sol Z0 m T q (C m (S:Set ℕ)))
    (he:e = true ∨ t = 0) :
    ∃ (x:ℕ) (f:ℕ → ℕ),S.card + t + x = k + 1 ∧ (∀ a ∈ S,f a ≤ x) ∧ ∀ a ∈ S,∀ b ∈ S,a ≠ b → Ht N m T e S a b → f a ≠ f b:=by
  induction hl with
  | stop =>
    refine ⟨0,fun _ => 0,by simp,by simp,?_⟩
    intro a ha b hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t a U hl ih =>
    have he1:e = true:=he.resolve_right (by omega)
    subst he1
    have hu:Un m a (insert a U) (insert (a ^^^ m) U):=⟨U,rfl,rfl⟩
    have hf:a ^^^ m ∉ U:=fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have hmin:=hu.min hl hm
    obtain ⟨x,f,hx,hfx,hc⟩:=ih hmin.2 (Or.inl rfl)
    rw [Finset.card_insert_of_notMem hf] at hx
    have sm:∀ {i1 i2:ℕ},m.testBit i1 = true → m.testBit i2 = true → (∀ w ∈ insert a U,w.testBit i1 = w.testBit i2) →
        ∀ w ∈ insert (a ^^^ m) U,w.testBit i1 = w.testBit i2:=by
      intro i1 i2 m1 m2 r w hw
      simp at hw
      rcases hw with rfl | hw
      · simp [r a (by simp),m1,m2]
      · exact r w (by simp [hw])
    by_cases ha:a ∈ U
    · have eS:insert a U = U:=Finset.insert_eq_of_mem ha
      refine ⟨x + 1,fun c => if c = a then x + 1 else f c,by rw [eS]; omega,?_,?_⟩
      · intro c hcS
        rw [eS] at hcS
        by_cases hca:c = a
        · simp [hca]
        · simp only [hca,if_false]
          have:=hfx c (by simp [hcS]); omega
      · intro c1 h1 c2 h2 h12 hh
        rw [eS] at h1 h2
        by_cases q1:c1 = a
        · have q2:c2 ≠ a:=fun e => h12 (q1.trans e.symm)
          have:=hfx c2 (by simp [h2])
          simp only [q1,q2,if_true,if_false]; omega
        · by_cases q2:c2 = a
          · have:=hfx c1 (by simp [h1])
            simp only [q1,q2,if_true,if_false]; omega
          · simp only [q1,q2,if_false]
            refine hc c1 (by simp [h1]) c2 (by simp [h2]) h12 ?_
            obtain ⟨i1,i2,j1,j2,l1,l2,l3,l4,r1,r2,u1,u2,u3,u4,p1,p2⟩:=hh
            have tr:∀ {c i:ℕ},c ≠ a → Lg N m T i → Uq N true (insert a U) c i → Uq N true (insert (a ^^^ m) U) c i:=by
              intro c i hca hi h
              refine ⟨h.1,fun y hy hne => ?_⟩
              simp at hy
              rcases hy with rfl | hy
              · have hn:sepb N true (a ^^^ m) i = sepb N true a i:=by simp [sepb,hi.1,hi.2.1]
                rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
              · exact h.2 y (by simp [hy]) hne
            exact ⟨i1,i2,j1,j2,l1,l2,l3,l4,sm l1.1 l2.1 r1,sm l3.2.1 l4.2.1 r2,tr q1 l1 u1,tr q2 l2 u2,tr q1 l3 u3,tr q2 l4 u4,p1,p2⟩
    · rw [Finset.card_insert_of_notMem ha]
      have mem:∀ {c:ℕ},c ∈ insert a U → (if c = a then a ^^^ m else c) ∈ insert (a ^^^ m) U:=by
        intro c hcS; split_ifs with h <;> simp at hcS ⊢; tauto
      refine ⟨x,fun c => f (if c = a then a ^^^ m else c),by omega,fun c hcS => hfx _ (mem hcS),?_⟩
      intro c1 h1 c2 h2 h12 hh
      refine hc _ (mem h1) _ (mem h2) ?_ ?_
      · split_ifs with p q q
        · exact absurd (p.trans q.symm) h12
        · intro e; simp at h2; rw [← e] at h2; rcases h2 with h | h
          · exact q (by rw [← e,h])
          · exact hf h
        · intro e; simp at h1; rw [e] at h1; rcases h1 with h | h
          · exact p (by rw [e,h])
          · exact hf h
        · exact h12
      · obtain ⟨i1,i2,j1,j2,l1,l2,l3,l4,r1,r2,u1,u2,u3,u4,p1,p2⟩:=hh
        have pp:∀ {c i j:ℕ},m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
            (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j:=by
          intro c i j m1 m2 p
          split_ifs with h
          · subst h; simp [m1,m2,p]
          · exact p
        exact ⟨i1,i2,j1,j2,l1,l2,l3,l4,sm l1.1 l2.1 r1,sm l3.2.1 l4.2.1 r2,un_uq l1 ha h1 u1,un_uq l2 ha h2 u2,un_uq l3 ha h1 u3,un_uq l4 ha h2 u4,
          pp l1.1 l3.1 p1,pp l2.1 l4.1 p2⟩
  | @bi k t d a b U hab hal hl ih =>
    have hu:Bi R d a b (insert a (insert b U)) (insert (op d a b) U):=⟨hab,U,rfl,rfl,hal⟩
    have hfS:op d a b ∉ insert a (insert b U):=fun h => hu.fresh hl hm (sub_C _ _ (by simpa using h))
    have hf:op d a b ∉ U:=fun h => hfS (by simp [h])
    have hmin:=hu.min hl hm
    have he2:e = true ∨ e = pos' t:=by
      rcases he with h | h
      · exact Or.inl h
      · subst h; cases e <;> simp [pos']
    obtain ⟨x,f,hx,hfx,hc⟩:=ih hmin.2 he
    rw [Finset.card_insert_of_notMem hf] at hx
    have mem:∀ {c:ℕ},c ∈ insert a (insert b U) → (if c = a ∨ c = b then op d a b else c) ∈ insert (op d a b) U:=fun h => phi_mem h
    by_cases ha:a ∈ U
    · by_cases hb:b ∈ U
      · have eS:insert a (insert b U) = U:=by rw [Finset.insert_eq_of_mem hb,Finset.insert_eq_of_mem ha]
        refine ⟨x + 2,fun c => if c = a then x + 2 else if c = b then x + 1 else f c,by rw [eS]; omega,?_,?_⟩
        · intro c hcS
          rw [eS] at hcS
          have:=hfx c (by simp [hcS])
          dsimp only; split_ifs <;> omega
        · intro c1 h1 c2 h2 h12 hh
          have k1:=h1; have k2:=h2
          rw [eS] at h1 h2
          have f1:=hfx c1 (by simp [h1]); have f2:=hfx c2 (by simp [h2])
          by_cases q1:c1 = a
          · have q2:c2 ≠ a:=fun e => h12 (q1.trans e.symm)
            simp only [q1,q2,if_true,if_false]; split_ifs <;> omega
          · by_cases q2:c2 = a
            · simp only [q1,q2,if_true,if_false]; split_ifs <;> omega
            · by_cases q3:c1 = b
              · have q4:c2 ≠ b:=fun e => h12 (q3.trans e.symm)
                simp only [q1,q2,q3,q4,if_true,if_false]; rw [if_neg (Ne.symm hab)]; omega
              · by_cases q4:c2 = b
                · simp only [q1,q2,q3,q4,if_true,if_false]; rw [if_neg (Ne.symm hab)]; omega
                · simp only [q1,q2,q3,q4,if_false]
                  have:=ht_bi hab he2 hl k1 k2 (fun e => absurd e q1) (fun e => absurd e q3) (fun e => absurd e q2) (fun e => absurd e q4) hh
                  simp only [q1,q2,q3,q4,or_self,if_false] at this
                  exact hc c1 (by simp [h1]) c2 (by simp [h2]) h12 this
      · have eS:insert a (insert b U) = insert b U:=Finset.insert_eq_of_mem (by simp [ha])
        refine ⟨x + 1,fun c => if c = a then x + 1 else f (if c = a ∨ c = b then op d a b else c),?_,?_,?_⟩
        · rw [eS,Finset.card_insert_of_notMem hb]; omega
        · intro c hcS
          have:=hfx _ (mem hcS)
          dsimp only; by_cases hca:c = a
          · simp [hca]
          · simp only [hca,if_false,false_or] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1:=hfx _ (mem h1); have f2:=hfx _ (mem h2)
          by_cases q1:c1 = a
          · have q2:c2 ≠ a:=fun e => h12 (q1.trans e.symm)
            simp only [q1,q2,if_true,if_false,false_or] at f2 ⊢; omega
          · by_cases q2:c2 = a
            · simp only [q1,q2,if_true,if_false,false_or] at f1 ⊢; omega
            · have:=ht_bi hab he2 hl h1 h2 (fun e => absurd e q1) (fun _ => hb) (fun e => absurd e q2) (fun _ => hb) hh
              simp only [q1,q2,if_false,false_or] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1':c1 = b ∨ c1 ∈ U:=by simp at h1; tauto
              have h2':c2 = b ∨ c2 ∈ U:=by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
    · by_cases hb:b ∈ U
      · have eS:insert a (insert b U) = insert a U:=by rw [Finset.insert_eq_of_mem hb]
        refine ⟨x + 1,fun c => if c = b then x + 1 else f (if c = a ∨ c = b then op d a b else c),?_,?_,?_⟩
        · rw [eS,Finset.card_insert_of_notMem ha]; omega
        · intro c hcS
          have:=hfx _ (mem hcS)
          dsimp only; by_cases hca:c = b
          · simp [hca]
          · simp only [hca,if_false,or_false] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1:=hfx _ (mem h1); have f2:=hfx _ (mem h2)
          by_cases q1:c1 = b
          · have q2:c2 ≠ b:=fun e => h12 (q1.trans e.symm)
            simp only [q1,q2,if_true,if_false,or_false] at f2 ⊢; omega
          · by_cases q2:c2 = b
            · simp only [q1,q2,if_true,if_false,or_false] at f1 ⊢; omega
            · have:=ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun e => absurd e q1) (fun _ => ha) (fun e => absurd e q2) hh
              simp only [q1,q2,if_false,or_false] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1':c1 = a ∨ c1 ∈ U:=by simp at h1; tauto
              have h2':c2 = a ∨ c2 ∈ U:=by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
      · refine ⟨x,fun c => f (if c = a ∨ c = b then op d a b else c),?_,fun c hcS => hfx _ (mem hcS),?_⟩
        · rw [Finset.card_insert_of_notMem (by simp [hab,ha]),Finset.card_insert_of_notMem hb]; omega
        · intro c1 h1 c2 h2 h12 hh
          by_cases hab':(c1 = a ∨ c1 = b) ∧ (c2 = a ∨ c2 = b)
          · exfalso
            have:Ht N m T e (insert a (insert b U)) a b:=by
              rcases hab' with ⟨rfl | rfl,rfl | rfl⟩
              · exact absurd rfl h12
              · exact hh
              · exact hh.symm
              · exact absurd rfl h12
            exact ht_merge hab he2 hl ha hb this
          · exact hc _ (mem h1) _ (mem h2) (phi_ne hf h1 h2 h12 hab')
              (ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun _ => hb) (fun _ => ha) (fun _ => hb) hh)
end chrom
structure W where
  s:Nat
  a:Nat
  b:Nat
  c:Nat
  r:Nat
structure X where
  w:W
  s:Nat
  q:Nat
  u:Nat
structure Cm where
  a:List Nat
  b:List Nat
def NN:Nat:=501
def AA:Nat:=(List.foldr (fun a b => a + b * 1000000000000000000) 0 [10680774620872704,715234948972014187,124645358009780528,20012900803184522,735604019182077490,938431350882492032,2382324645710741,120852817932023020,3273378])
def HX:Nat:=(List.foldr (fun a b => a + b * 1000000000000000000) 0 [549231732136869888,497859752932937855,211186106257859023,355228270894117441,37050616367514994])
def HY:Nat:=(List.foldr (fun a b => a + b * 1000000000000000000) 0 [779450076587884544,928923732608139709,978470309100615567,734525368487349844,963537632043216864,153654778696474549,391272873658722542,94939465808003359,3273403])
noncomputable section core
def st (n:Nat) (f:Nat → Bool):Bool:=Nat.rec (motive:=fun _ => Bool) (f 0) (fun m _ => f m) (Nat.succ n)
def sp (d:Bool) (l s:Nat):Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) (Bool.rec (motive:=fun _ => Nat) (Nat.land s l) l d)
def cov (d:Bool) (l:Nat) (v:List W):Nat :=
  List.rec (motive:=fun _ => Nat) 0 (fun w _ ih => Nat.lor (sp d l w.s) ih) v
def twice (d:Bool) (l:Nat) (v:List W):Nat :=
  List.rec (motive:=fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (sp d l w.s) (cov d l t)) ih) v
def hit (f e:Nat):Bool:=(Bool.rec (motive:=fun _ => Bool) ((Bool.rec (motive:=fun _ => Bool) (true) (false) (Nat.beq (Nat.land (Nat.land f e) HY) 0))) (false) (Nat.beq (Nat.land (Nat.land f e) HX) 0))
def hits (f:Nat) (m:List Nat):Bool:=(List.rec (motive:=fun _ => Bool) (false) (fun e _ ih => (Bool.rec (motive:=fun _ => Bool) (ih) (true) (hit f e))) (m))
def flag (d:Bool) (l o:Nat) (w:W):Nat:=Nat.add (Nat.land (sp d l w.s) o) AA
def rect (d:Bool) (l o:Nat) (v:List W):List Nat → Bool :=
  List.rec (motive:=fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => (Bool.rec (motive:=fun _ => Bool) (ih (flag d l o w :: m)) (true) (hits (flag d l o w) m))) v
def app (x y:List Nat):List Nat:=List.rec (motive:=fun _ => List Nat) y (fun e _ ih => e :: ih) x
def join (k:List Cm → Bool) (f:Nat) (cs:List Cm):List Nat → List Nat → List Cm → Bool :=
  List.rec (motive:=fun _ => List Nat → List Nat → List Cm → Bool) (fun S O R => k (⟨S,O⟩ :: R))
    (fun c _ ih S O R => Bool.rec (motive:=fun _ => Bool)
      (Bool.rec (motive:=fun _ => Bool) (ih S O (c :: R)) (ih (app c.a S) (app c.b O) R) (hits f c.b))
      (Bool.rec (motive:=fun _ => Bool) (ih (app c.b S) (app c.a O) R) true (hits f c.b)) (hits f c.a)) cs
def bip (l o:Nat) (v:List W):List Cm → Bool :=
  List.rec (motive:=fun _ => List Cm → Bool) (fun _ => false)
    (fun w _ ih cs => (fun f => join ih f cs [f] [] []) (flag false l o w)) v
def anyE (m:List Nat):Bool:=List.rec (motive:=fun _ => Bool) false (fun f t ih => Bool.rec (motive:=fun _ => Bool) ih true (hits f t)) m
def rmF (f:Nat) (m:List Nat):List Nat :=
  List.rec (motive:=fun _ => List Nat) [] (fun e t ih => Bool.rec (motive:=fun _ => List Nat) (e :: ih) t (hit f e)) m
def star (m:List Nat):Bool:=List.rec (motive:=fun _ => Bool) true (fun f t ih => Bool.rec (motive:=fun _ => Bool) ih
  (Bool.rec (motive:=fun _ => Bool) true (Bool.rec (motive:=fun _ => Bool) (Bool.rec (motive:=fun _ => Bool) true false (anyE (rmF f t))) false (hits f (rmF f t))) (anyE t)) (hits f t)) m
def flk (l o:Nat) (v:List W):(List Nat → Bool) → Bool :=
  List.rec (motive:=fun _ => (List Nat → Bool) → Bool) (fun k => k []) (fun w _ ih k => (fun f => ih (fun r => k (f :: r))) (flag false l o w)) v
def mkX (d:Bool) (l o:Nat) (v:List W):List X :=
  List.rec (motive:=fun _ => List X) [] (fun w _ ih => ⟨w,w.s,Nat.shiftRight w.s NN,Nat.land (sp d l w.s) o⟩ :: ih) v
def rm (x y:Nat) (v:List W):(List W → Bool) → Bool :=
  List.rec (motive:=fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => Bool.rec (motive:=fun _ => Bool) (Bool.rec (motive:=fun _ => Bool) (ih (fun r => h (w :: r))) (ih h) (Nat.beq w.s y)) (ih h) (Nat.beq w.s x)) v
def ins (o:W) (v:List W):(List W → Bool) → Bool :=
  List.rec (motive:=fun _ => (List W → Bool) → Bool) (fun h => h [o]) (fun w t ih h => Bool.rec (motive:=fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive:=fun _ => Bool) (h (o :: w :: t)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def child (f:Nat → List W → Bool) (g:Nat) (mk:(List W → Bool) → Bool) (z:Nat):Bool :=
  Bool.rec (motive:=fun _ => Bool) false (st z (fun z => mk (f z))) (Nat.beq (Nat.land z g) g)
def put (m s x y:Nat) (v:List W) (h:List W → Bool):Bool :=
  (st (s) (fun s => (Bool.rec (motive:=fun _ => Bool) ((Bool.rec (motive:=fun _ => Bool) ((st (x) (fun x1 => (st (y) (fun y1 => (st (Nat.lor x y) (fun w => ins ⟨s,x1,y1,w,0⟩ v h))))))) (false) (Nat.beq s m))) (false) (Nat.beq s 0))))
def kids (c:((List W → Bool) → Bool) → Nat → Bool) (e n z x y a c':Nat) (oa oc:Bool) (mk:(List W → Bool) → Bool):Bool :=
  (Bool.rec (motive:=fun _ => Bool) ((Bool.rec (motive:=fun _ => Bool) ((Bool.rec (motive:=fun _ => Bool) (false) (c mk (Nat.sub (Nat.sub z x) y)) (Nat.ble (Nat.succ (Nat.succ n)) e))) (true) ((Bool.rec (motive:=fun _ => Bool) (false) ((Bool.rec (motive:=fun _ => Bool) ((Bool.rec (motive:=fun _ => Bool) (false) (c (fun h => mk (fun r => rm a a r h)) (Nat.sub z y)) (oa))) (true) ((Bool.rec (motive:=fun _ => Bool) (false) (c (fun h => mk (fun r => rm c' c' r h)) (Nat.sub z x)) (oc))))) (Nat.ble (Nat.succ n) e))))) (true) ((Bool.rec (motive:=fun _ => Bool) (false) ((Bool.rec (motive:=fun _ => Bool) (false) (c (fun h => mk (fun r => rm a c' r h)) z) (oc))) (oa))))
def mid (f:Nat → List W → Bool) (m g e n z:Nat) (v:List W) (a c:W) (da dc s x y:Nat):Bool :=
  (Bool.rec (motive:=fun _ => Bool) (false) ((st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) (fun z => kids (child f g) e n z a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v)))) (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g))
def f0 (h:W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c:W) (da dc s x y:Nat):Bool :=
  (Bool.rec (motive:=fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.lor da dc) 0))
def f1 (h:W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c:W) (da dc s x y:Nat):Bool :=
  (Bool.rec (motive:=fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.mul da dc) 0))
def f2 (h:W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c:W) (da dc s x y:Nat):Bool:=h a c da dc s x y
def pair (h:W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c:X):Bool :=
  X.rec (motive:=fun _ => Bool) (fun a s q u => X.rec (motive:=fun _ => Bool) (fun c s' q' u' => (Bool.rec (motive:=fun _ => Bool) (h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)) (true) (h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b)))) c) a
def scan (p:X → Bool) (xs:List X):Bool:=(List.rec (motive:=fun _ => Bool) (false) (fun c _ jh => (Bool.rec (motive:=fun _ => Bool) (jh) (true) (p c))) (xs))
def pairs (h:X → X → Bool) (xs:List X):Bool :=
  (List.rec (motive:=fun _ => Bool) (false) (fun a r ih => (Bool.rec (motive:=fun _ => Bool) (ih) (true) (scan (h a) r))) (xs))
def pairsP (q:Nat) (h:X → X → Bool) (xs:List X):Bool :=
  scan (fun a => (Bool.rec (motive:=fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive:=fun _ => Bool) (h a c) (false) (Nat.beq c.s q))) xs) (Nat.beq a.s q))) xs
def pairsQ (q q':Nat) (h:X → X → Bool) (xs:List X):Bool :=
  scan (fun a => (Bool.rec (motive:=fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive:=fun _ => Bool) (false) (h a c) (Nat.beq c.s q'))) xs) (Nat.beq a.s q))) xs
def fr (xs:List X):List X:=List.rec (motive:=fun _ => List X) [] (fun a _ ih => Bool.rec (motive:=fun _ => List X) ih (a :: ih) (Nat.beq a.w.r 0)) xs
def fs (xs:List X):List X:=List.rec (motive:=fun _ => List X) [] (fun a _ ih => Bool.rec (motive:=fun _ => List X) (a :: ih) ih (Nat.beq a.w.r 0)) xs
def pairsN (h:X → X → Bool) (xs:List X):Bool :=
  Bool.rec (motive:=fun _ => Bool) (scan (fun a => scan (h a) (fs xs)) (fr xs)) true (pairs h (fr xs))
def pairsS (h:X → X → Bool) (xs:List X):Bool:=pairs h (fs xs)
def nots (f:Nat → Nat → List W → Bool) (m g e n z q:Nat) (v r:List W):Bool :=
  (List.rec (motive:=fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive:=fun _ => Bool) (ih) (true) ((Bool.rec (motive:=fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st (Nat.sub z a.c) (fun z => ins ⟨s,a.b,a.a,a.c,0⟩ v (fun v => (Bool.rec (motive:=fun _ => Bool) ((Bool.rec (motive:=fun _ => Bool) (false) (child (f s) g (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive:=fun _ => Bool) (false) (child (f s) g (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))
def pos (t:Nat):Bool:=Nat.rec (motive:=fun _ => Bool) false (fun _ _ => true) t
def wst (d:Bool) (l:Nat) (v:List W):Nat:=Nat.xor l (twice d l v)
def node (f:Nat → List W → Bool) (d:Bool) (l m g e n z:Nat) (v:List W) (go:(X → X → Bool) → List X → Bool):Bool :=
  (fun h => (fun xs => Bool.rec (motive:=fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive:=fun _ => Bool) (go (pair (f1 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkX d l (wst d l v) v))
  (mid f m g e (Nat.pred n) z v)
def prd (t:Nat) (h:Nat → Bool):Bool:=Nat.rec (motive:=fun _ => Bool) false (fun s _ => h s) t
def cv (d:Bool) (l:Nat) (v:List W) (b:Bool):Bool :=
  Bool.rec (motive:=fun _ => Bool) (Bool.rec (motive:=fun _ => Bool) false b (Nat.beq (cov d l v) l)) b d
def tst (d:Bool) (l e:Nat) (v:List W) (F:Nat → Bool):Bool :=
  (fun n => Bool.rec (motive:=fun _ => Bool)
    (Bool.rec (motive:=fun _ => Bool) (F 0) (Bool.rec (motive:=fun _ => Bool) (Bool.rec (motive:=fun _ => Bool) (F 1) (F 0) (flk l (wst d l v) v star)) false (bip l (wst d l v) v []))
      (Nat.beq (Nat.succ n) e))
    (Bool.rec (motive:=fun _ => Bool) (F 0) false (rect d l (wst d l v) v [])) (Nat.beq n e)) v.length
def mv (F:Nat → Nat → Nat → List W → Bool) (l m g k t z:Nat) (v:List W) (y:Nat):Bool :=
  (fun n => Bool.rec (motive:=fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive:=fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          node (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (node (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v v)) true
    (node (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length
def look (l m g:Nat) (fuel:Nat):Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive:=fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive:=fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mv ih l m g k t z v y)) true (Nat.ble v.length 1)) fuel
def look1 (l m g K:Nat) (fuel:Nat):Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive:=fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive:=fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive:=fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) fuel
end core
lemma bR (c e t:Bool):(Bool.rec (motive:=fun _ => Bool) e t c:Bool) = bif c then t else e:=by cases c <;> rfl
lemma st_eq (n:ℕ) (f:ℕ → Bool):st n f = f n:=by cases n <;> rfl
lemma nl (a b:ℕ):Nat.land a b = a &&& b:=rfl
lemma no (a b:ℕ):Nat.lor a b = a ||| b:=rfl
lemma nx (a b:ℕ):Nat.xor a b = a ^^^ b:=rfl
lemma nsr (a b:ℕ):Nat.shiftRight a b = a >>> b:=rfl
lemma sp_bit (d:Bool) (l s i:ℕ):(sp d l s).testBit i = (l.testBit i && sepb NN d s i):=by
  cases d <;> simp [sp,sepb,nl,nx,nsr,Nat.testBit_shiftRight] <;>
    cases l.testBit i <;> cases s.testBit i <;> cases s.testBit (NN + i) <;> rfl
lemma cov_bit (d:Bool) (l i:ℕ) (v:List W):(cov d l v).testBit i = true ↔ ∃ w ∈ v,(sp d l w.s).testBit i = true:=by
  induction v with
  | nil => simp [cov]
  | cons w v ih =>
    change (Nat.lor (sp d l w.s) (cov d l v)).testBit i = true ↔ _
    simp [no,ih]
lemma twice_bit (d:Bool) (l i:ℕ) (v:List W) (h:(twice d l v).testBit i = false) :
    v.Pairwise (fun w w' => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)):=by
  induction v with
  | nil => simp
  | cons w v ih =>
    change (Nat.lor (Nat.land (sp d l w.s) (cov d l v)) (twice d l v)).testBit i = false at h
    simp only [no,nl,Nat.testBit_or,Nat.testBit_and,Bool.or_eq_false_iff] at h
    refine List.pairwise_cons.2 ⟨fun w' hw' ⟨h1,h2⟩ => ?_,ih h.2⟩
    have:=(cov_bit d l i v).2 ⟨w',hw',h2⟩
    simp [h1,this] at h
def Rep (v:List W) (S:Finset ℕ):Prop:=(v.map W.s).Nodup ∧ (v.map W.s).toFinset = S
lemma Rep.mem {v:List W} {S:Finset ℕ} (h:Rep v S) {x:ℕ}:x ∈ S ↔ ∃ w ∈ v,w.s = x:=by
  rw [← h.2]; simp
lemma Rep.inj {v:List W} {S:Finset ℕ} (h:Rep v S) {w w':W} (hw:w ∈ v) (hw':w' ∈ v) (e:w.s = w'.s):w = w' :=
  List.inj_on_of_nodup_map h.1 hw hw' e
lemma Rep.card {v:List W} {S:Finset ℕ} (h:Rep v S):S.card = v.length:=by
  rw [← h.2,List.toFinset_card_of_nodup h.1,List.length_map]
lemma uq_of {d:Bool} {l i:ℕ} {v:List W} {S:Finset ℕ} (h:Rep v S) {w:W} (hw:w ∈ v)
    (hu:(Nat.land (sp d l w.s) (wst d l v)).testBit i = true):l.testBit i = true ∧ Uq NN d S w.s i:=by
  simp only [nl,wst,nx,Nat.testBit_and,Nat.testBit_xor,Bool.and_eq_true,sp_bit] at hu
  obtain ⟨⟨hl,hs⟩,ht⟩:=hu
  have ht:(twice d l v).testBit i = false:=by simpa [hl] using ht
  refine ⟨hl,hs,fun c hc hne => ?_⟩
  obtain ⟨w',hw',rfl⟩:=h.mem.1 hc
  have hp:=twice_bit d l i v ht
  haveI:Std.Symm (fun w w':W => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) :=
    ⟨fun a b h h' => h h'.symm⟩
  have:=hp.forall hw hw' (fun e => hne (by rw [e]))
  simp only [sp_bit,hl,hs,Bool.true_and,true_and] at this
  simpa using this
def segsX:List (ℕ × ℕ):=[(63,76),(76,79),(79,92),(92,95),(95,98),(98,101),(101,114),(114,127),(127,129),(129,142),(142,144),(144,147),(147,149),(149,152),(152,165),(165,178),(178,180),(180,182),(182,185),(185,198),(198,200),(200,203),(203,205),(205,207),(207,210),(210,213),(213,226),(226,229),(229,242),(242,245),(245,258),(258,260),(260,262),(262,264),(264,266),(266,269),(269,271),(271,274),(274,287),(287,289),(289,291),(291,294)]
def segsY:List (ℕ × ℕ):=[(294,307),(307,312),(312,316),(316,334),(334,338),(338,356),(356,360),(360,378),(378,396),(396,400),(400,418),(418,423),(423,441),(441,459),(459,464),(464,482),(482,500)]
def segOk (s:ℕ × ℕ):Bool:=decide (s.1 < s.2) && decide (AA % 2 ^ s.2 + 2 ^ (s.1 + 1) = 2 ^ s.2 + AA % 2 ^ s.1) &&
  !AA.testBit s.1 && !AA.testBit s.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segX_ok:segsX.all segOk = true:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segY_ok:segsY.all segOk = true:=by decide +kernel
def bitsOf (L:List (ℕ × ℕ)):ℕ:=L.foldr (fun s x => 2 ^ s.2 ||| x) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HX_eq:HX = bitsOf segsX:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HY_eq:HY = bitsOf segsY:=by decide +kernel
lemma bitsOf_bit {L:List (ℕ × ℕ)} {h:ℕ} (hh:(bitsOf L).testBit h = true):∃ s ∈ L,s.2 = h:=by
  induction L with
  | nil => simp [bitsOf] at hh
  | cons s L ih =>
    change (2 ^ s.2 ||| bitsOf L).testBit h = true at hh
    rw [Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact ⟨s,by simp,by simpa using hh⟩
    · obtain ⟨s',hs',e⟩:=ih hh; exact ⟨s',by simp [hs'],e⟩
lemma carry {u A p h:ℕ} (hp:p < h) (hA:A % 2 ^ h + 2 ^ (p + 1) = 2 ^ h + A % 2 ^ p) (hAh:A.testBit h = false)
    (huh:u.testBit h = false) (hup:u.testBit p = false) (hs:(u + A).testBit h = true) :
    ∃ i,p < i ∧ i < h ∧ u.testBit i = true:=by
  by_contra hno
  push Not at hno
  have e1:u % 2 ^ h = u % 2 ^ p:=by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_mod_two_pow]
    by_cases h1:i < p
    · simp [h1,show i < h by omega]
    · by_cases h2:i < h
      · rcases Nat.lt_or_ge p i with h3 | h3
        · simp [h1,hno i h3 h2]
        · obtain rfl:i = p:=by omega
          simp [hup]
      · simp [h1,h2]
  have l1:=Nat.mod_lt u (Nat.two_pow_pos p)
  have l2:=Nat.mod_lt A (Nat.two_pow_pos p)
  have hlt:u % 2 ^ h + A % 2 ^ h < 2 ^ h:=by rw [e1]; have:=Nat.pow_succ 2 p; omega
  have e2:(u + A).testBit h = (u / 2 ^ h + A / 2 ^ h).testBit 0:=by
    have:u + A = 2 ^ h * (u / 2 ^ h + A / 2 ^ h) + (u % 2 ^ h + A % 2 ^ h):=by
      have a1:=Nat.div_add_mod u (2 ^ h); have a2:=Nat.div_add_mod A (2 ^ h)
      rw [Nat.mul_add]; omega
    rw [this,Nat.testBit_two_pow_mul_add _ hlt]; simp
  have b1:(u / 2 ^ h).testBit 0 = false:=by rw [← huh,Nat.testBit_div_two_pow]; simp
  have b2:(A / 2 ^ h).testBit 0 = false:=by rw [← hAh,Nat.testBit_div_two_pow]; simp
  rw [e2] at hs
  simp [Nat.testBit_zero] at hs b1 b2
  omega
def Same (L:List (ℕ × ℕ)) (i j:ℕ):Prop:=∃ s ∈ L,s.1 < i ∧ i < s.2 ∧ s.1 < j ∧ j < s.2
def Good (l s:ℕ):Prop:=(∀ i j,Same segsX i j → l.testBit i = true → l.testBit j = true → s.testBit i = s.testBit j) ∧
  (∀ i j,Same segsY i j → l.testBit i = true → l.testBit j = true → s.testBit (NN + i) = s.testBit (NN + j))
lemma flag_seg {L:List (ℕ × ℕ)} (hL:L.all segOk = true) {u:ℕ} (hu:∀ i,u.testBit i = true → AA.testBit i = true)
    {s:ℕ × ℕ} (hs:s ∈ L) (hb:(u + AA).testBit s.2 = true):∃ i,s.1 < i ∧ i < s.2 ∧ u.testBit i = true:=by
  have h:=List.all_eq_true.1 hL s hs
  simp only [segOk,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at h
  refine carry h.1.1.1 h.1.1.2 h.2 ?_ ?_ hb
  · by_contra hc; have:=hu _ (by simpa using hc); rw [h.2] at this; simp at this
  · by_contra hc; have:=hu _ (by simpa using hc); rw [h.1.2] at this; simp at this
lemma hit_spec {f e:ℕ} (h:hit f e = true) :
    (∃ s ∈ segsX,f.testBit s.2 = true ∧ e.testBit s.2 = true) ∧ (∃ s ∈ segsY,f.testBit s.2 = true ∧ e.testBit s.2 = true):=by
  have aux:∀ H,Nat.beq (Nat.land (Nat.land f e) H) 0 = false → ∃ i,f.testBit i = true ∧ e.testBit i = true ∧ H.testBit i = true:=by
    intro H hH
    have hne:(f &&& e &&& H) ≠ 0:=fun h0 => by rw [nl,nl,h0] at hH; simp at hH
    obtain ⟨i,hi⟩:=Nat.exists_testBit_of_ne_zero hne
    simp at hi; exact ⟨i,hi.1.1,hi.1.2,hi.2⟩
  simp only [hit,bR] at h
  cases h1:Nat.beq (Nat.land (Nat.land f e) HX) 0 with
  | true => rw [h1] at h; simp only [cond_true,Bool.false_eq_true] at h
  | false =>
    cases h2:Nat.beq (Nat.land (Nat.land f e) HY) 0 with
    | true => rw [h1,h2] at h; simp only [cond_true,cond_false,Bool.false_eq_true] at h
    | false =>
      obtain ⟨i,a1,a2,a3⟩:=aux _ h1
      obtain ⟨j,b1,b2,b3⟩:=aux _ h2
      rw [HX_eq] at a3; rw [HY_eq] at b3
      obtain ⟨s,hs,rfl⟩:=bitsOf_bit a3
      obtain ⟨s',hs',rfl⟩:=bitsOf_bit b3
      exact ⟨⟨s,hs,a1,a2⟩,⟨s',hs',b1,b2⟩⟩
lemma hits_false {f:ℕ} {m:List ℕ} (h:∀ e ∈ m,hit f e = false):hits f m = false:=by
  induction m with
  | nil => rfl
  | cons e m ih =>
    change (Bool.rec (motive:=fun _ => Bool) (hits f m) true (hit f e):Bool) = false
    rw [bR,h e (by simp),ih (fun x hx => h x (by simp [hx]))]; rfl
lemma rect_false {d:Bool} {l o:ℕ} {v:List W}:∀ {m:List ℕ},v.Pairwise (fun a b => hit (flag d l o b) (flag d l o a) = false) →
    (∀ w ∈ v,∀ e ∈ m,hit (flag d l o w) e = false) → rect d l o v m = false:=by
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro m hp hm
    change (Bool.rec (motive:=fun _ => Bool) (rect d l o v (flag d l o w :: m)) true (hits (flag d l o w) m):Bool) = false
    rw [List.pairwise_cons] at hp
    rw [bR,hits_false (hm w (by simp)),ih hp.2]; · rfl
    intro w' hw' e he
    simp at he
    rcases he with rfl | he
    · exact hp.1 w' hw'
    · exact hm w' (by simp [hw']) e he
lemma Live.pos {m T k t:ℕ} {S:Finset ℕ} (h:Live R m T k t S):0 < S.card:=by
  cases h with
  | stop => simp
  | un => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
  | bi => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
def pk (n:ℕ) (f:ℕ → ℕ):ℕ:=∑ j ∈ Finset.range n,f j * 2 ^ (5 * j)
lemma pk_succ (n:ℕ) (f:ℕ → ℕ):pk (n + 1) f = 2 ^ (5 * n) * f n + pk n f:=by
  rw [pk,Finset.sum_range_succ,← pk]; ring
lemma pk_lt {n:ℕ} {f:ℕ → ℕ} (h:∀ j < n,f j < 32):pk n f < 2 ^ (5 * n):=by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have:=ih (fun j hj => h j (by omega))
    have h2:=h n (by omega)
    rw [pk_succ,show 5 * (n + 1) = 5 * n + 5 by ring,pow_add]
    have:2 ^ (5 * n) * f n ≤ 2 ^ (5 * n) * 31:=Nat.mul_le_mul_left _ (by omega)
    omega
lemma pk_add (n:ℕ) (f g:ℕ → ℕ):pk n f + pk n g = pk n (fun j => f j + g j):=by
  simp [pk,← Finset.sum_add_distrib,add_mul]
lemma pk_congr {n:ℕ} {f g:ℕ → ℕ} (h:∀ j < n,f j = g j):pk n f = pk n g :=
  Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]
lemma pk_sub {n:ℕ} {f g:ℕ → ℕ} (h:∀ j < n,g j ≤ f j):pk n f - pk n g = pk n (fun j => f j - g j):=by
  have:pk n (fun j => f j - g j) + pk n g = pk n f:=by
    rw [pk_add]; exact pk_congr fun j hj => Nat.sub_add_cancel (h j hj)
  omega
lemma pk_guard {n:ℕ} {f:ℕ → ℕ} (h:∀ j < n,16 ≤ f j ∧ f j < 32) :
    pk n f &&& pk n (fun _ => 16) = pk n (fun _ => 16):=by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have ih:=ih (fun j hj => h j (by omega))
    have h1:pk n f < 2 ^ (5 * n):=pk_lt fun j hj => (h j (by omega)).2
    have h2:pk n (fun _ => 16) < 2 ^ (5 * n):=pk_lt fun _ _ => by omega
    have h3:f n &&& 16 = 16:=by
      obtain ⟨a,b⟩:=h n (by omega)
      generalize f n = x at *
      interval_cases x <;> rfl
    rw [pk_succ,pk_succ]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and,Nat.testBit_two_pow_mul_add _ h1,Nat.testBit_two_pow_mul_add _ h2]
    split_ifs with hi
    · rw [← Nat.testBit_and,ih]
    · rw [← Nat.testBit_and,h3]
def isPk (n x:ℕ):Prop:=∀ i,x.testBit i = true → i % 5 = 0 ∧ i / 5 < n
lemma pk_of {n:ℕ}:∀ {x:ℕ},isPk n x → x = pk n (fun j => (x.testBit (5 * j)).toNat):=by
  induction n with
  | zero =>
    intro x h
    simp only [pk,Finset.range_zero,Finset.sum_empty]
    apply Nat.eq_of_testBit_eq; intro i
    by_contra hc
    have:=h i (by simpa using hc); omega
  | succ n ih =>
    intro x h
    have hm:isPk n (x % 2 ^ (5 * n)):=by
      intro i hi
      simp only [Nat.testBit_mod_two_pow,Bool.and_eq_true,decide_eq_true_eq] at hi
      exact ⟨(h i hi.2).1,by omega⟩
    have e:=ih hm
    have hd:x / 2 ^ (5 * n) = (x.testBit (5 * n)).toNat:=by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_div_two_pow]
      cases i with
      | zero => cases hb:x.testBit (5 * n) <;> simp [hb]
      | succ i =>
        have e1:x.testBit (i + 1 + 5 * n) = false:=by
          by_contra hc
          have:=h _ (by simpa using hc); omega
        rw [e1]
        cases x.testBit (5 * n) <;> simp [Nat.testBit_succ]
    rw [pk_succ,← hd]
    have e2:pk n (fun j => (x.testBit (5 * j)).toNat) = x % 2 ^ (5 * n):=by
      conv_rhs => rw [e]
      refine pk_congr fun j hj => ?_
      rw [Nat.testBit_mod_two_pow]; simp [show 5 * j < 5 * n by omega]
    rw [e2]; exact (Nat.div_add_mod x _).symm
lemma isPk_and {n x y:ℕ} (hx:isPk n x):isPk n (x &&& y):=fun i hi => hx i (by simp at hi; exact hi.1)
lemma isPk_or {n x y:ℕ} (hx:isPk n x) (hy:isPk n y):isPk n (x ||| y):=fun i hi => by
  simp at hi; exact hi.elim (hx i) (hy i)
def fl (w:W) (j:ℕ):ℕ:=(w.c.testBit (5 * j)).toNat
lemma fl_le (w:W) (j:ℕ):fl w j ≤ 1:=by unfold fl; cases w.c.testBit (5 * j) <;> simp
def cnt (v:List W) (j:ℕ):ℕ:=(v.map (fun w => fl w j)).sum
lemma cnt_cons (w:W) (v:List W) (j:ℕ):cnt (w :: v) j = fl w j + cnt v j:=by simp [cnt]
lemma cnt_perm {v v':List W} (h:v.Perm v') (j:ℕ):cnt v j = cnt v' j:=(h.map _).sum_eq
structure WOk (P:List ℕ) (w:W):Prop where
  pa:isPk P.length w.a
  pb:isPk P.length w.b
  ec:w.c = w.a ||| w.b
  ca:∀ j < P.length,w.a.testBit (5 * j) = true → w.s &&& P.getD j 0 = 0
  cb:∀ j < P.length,w.b.testBit (5 * j) = true → w.s &&& P.getD j 0 = P.getD j 0
lemma WOk.pc {P:List ℕ} {w:W} (h:WOk P w):isPk P.length w.c:=by rw [h.ec]; exact isPk_or h.pa h.pb
lemma WOk.cst {P:List ℕ} {w:W} (h:WOk P w) {j:ℕ} (hj:j < P.length) (hf:w.c.testBit (5 * j) = true) :
    Cst (P.getD j 0) w.s:=by
  rw [h.ec,Nat.testBit_or,Bool.or_eq_true] at hf
  exact hf.elim (fun h1 => Or.inl (h.ca j hj h1)) (fun h1 => Or.inr (h.cb j hj h1))
def Cl (P:List ℕ) (T k:ℕ) (b:ℕ → ℕ) (S:Finset ℕ):Prop:=∀ j < P.length,∀ q,q + b j < k →
  ¬ Sol Z0 (P.getD j 0) (T &&& P.getD j 0) q (C (P.getD j 0) (Im (P.getD j 0) S))
structure StOk (P:List ℕ) (T l k z:ℕ) (v:List W) (S:Finset ℕ):Prop where
  rep:Rep v S
  wok:∀ w ∈ v,WOk P w
  good:∀ w ∈ v,Good l w.s
  bud:∃ b:ℕ → ℕ,(∀ j < P.length,b j ≤ 15) ∧ Cl P T k b S ∧ z = pk P.length (fun j => 16 + b j - cnt v j)
structure Ctx (P:List ℕ) (l m g T:ℕ):Prop where
  lg:∀ i,l.testBit i = true → Lg NN m T i ∧ AA.testBit i = true
  hP:∀ j < P.length,P.getD j 0 &&& m = P.getD j 0 ∧ T &&& P.getD j 0 ≠ 0 ∧ T &&& P.getD j 0 ≠ P.getD j 0
  hg:g = pk P.length (fun _ => 16)
section sound
variable {P:List ℕ} {l m g T:ℕ} (X:Ctx P l m g T)
include X
lemma cnt_le {k k' t:ℕ} {v:List W} {S:Finset ℕ} {b:ℕ → ℕ} (hr:Rep v S) (hw:∀ w ∈ v,WOk P w)
    (hc:Cl P T k b S) (hm:Min R m T k' t S) (hk:k' ≤ k):∀ j < P.length,cnt v j ≤ b j:=by
  intro j hj
  obtain ⟨p1,p2,p3⟩:=X.hP j hj
  obtain ⟨q,hq,hs⟩:=hm.const p1 p2 p3
  have hqb:¬ q + b j < k:=fun h => hc j hj q h hs
  have:cnt v j ≤ (S.filter (Cst (P.getD j 0))).card:=by
    have e:cnt v j = (v.filter (fun w => w.c.testBit (5 * j))).length:=by
      clear hr hw
      induction v with
      | nil => rfl
      | cons w v ih =>
        rw [cnt_cons,ih,List.filter_cons,fl]
        cases w.c.testBit (5 * j) <;> simp; omega
    rw [e,← List.length_map W.s,← List.toFinset_card_of_nodup (hr.1.sublist (List.filter_sublist.map _))]
    apply Finset.card_le_card
    intro x hx
    simp only [List.mem_toFinset,List.mem_map,List.mem_filter] at hx
    obtain ⟨w,⟨h1,h2⟩,rfl⟩:=hx
    rw [Finset.mem_filter]
    exact ⟨hr.mem.2 ⟨w,h1,rfl⟩,(hw w h1).cst hj h2⟩
  omega
lemma guard_ok {k k' t z:ℕ} {v:List W} {S:Finset ℕ} (hr:StOk P T l k z v S) (hm:Min R m T k' t S) (hk:k' ≤ k) :
    Nat.beq (Nat.land z g) g = true:=by
  obtain ⟨b,hb,hc,hz⟩:=hr.bud
  have hle:=cnt_le X hr.rep hr.wok hc hm hk
  rw [nl,hz,X.hg,pk_guard]; · simp
  intro j hj
  have:=hb j hj; have:=hle j hj; omega
lemma child_sound {f:ℕ → List W → Bool} {z t k k':ℕ} {r:List W} {S:Finset ℕ}
    {mk:(List W → Bool) → Bool} (hmk:∀ h,mk h = h r)
    (hr:StOk P T l k z r S) (hm:Min R m T k' t S) (hk:k' ≤ k) (h:child f g mk z = false):f z r = false:=by
  simp only [child,bR,st_eq,guard_ok X hr hm hk,cond_true,hmk] at h
  exact h
end sound
lemma rm_eq (x y:ℕ) (v:List W):∀ h,rm x y v h = h (v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y))):=by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change (Bool.rec (motive:=fun _ => Bool) (Bool.rec (motive:=fun _ => Bool) (rm x y v (fun r => h (w :: r)))
      (rm x y v h) (Nat.beq w.s y)) (rm x y v h) (Nat.beq w.s x):Bool) = _
    rw [bR,bR,ih,ih,List.filter_cons]
    cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> simp
lemma ins_spec (o:W) (v:List W) (hv:∀ w ∈ v,w.s ≠ o.s):∃ r:List W,r.Perm (o :: v) ∧ ∀ h,ins o v h = h r:=by
  induction v with
  | nil => exact ⟨[o],List.Perm.refl _,fun h => rfl⟩
  | cons w v ih =>
    obtain ⟨r,hp,hr⟩:=ih fun w' hw' => hv w' (by simp [hw'])
    have e:∀ h,ins o (w :: v) h = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then false else h (o :: w :: v)) else ins o v (fun r => h (w :: r)):=by
      intro h
      change (Bool.rec (motive:=fun _ => Bool) (ins o v (fun r => h (w :: r)))
        (Bool.rec (motive:=fun _ => Bool) (h (o :: w :: v)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s):Bool) = _
      rw [bR,bR]
    cases hb:Nat.ble w.s o.s with
    | true =>
      refine ⟨o :: w :: v,List.Perm.refl _,fun h => ?_⟩
      have:Nat.beq o.s w.s = false:=Bool.eq_false_iff.2 fun h => hv w (by simp) (Nat.eq_of_beq_eq_true h).symm
      rw [e,hb,this]; rfl
    | false =>
      refine ⟨w :: r,(List.Perm.cons w hp).trans (List.Perm.swap _ _ _),fun h => ?_⟩
      rw [e,hb,hr]; rfl
lemma filter_perm {v:List W} (hv:(v.map W.s).Nodup) {a:W} (ha:a ∈ v) :
    (a :: v.filter (fun w => !Nat.beq w.s a.s)).Perm v:=by
  induction v with
  | nil => simp at ha
  | cons w v ih =>
    simp only [List.map_cons,List.nodup_cons,List.mem_map,not_exists,not_and] at hv
    have hne:∀ x y:ℕ,x ≠ y → Nat.beq x y = false:=fun x y h => Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · have:v.filter (fun w => !Nat.beq w.s a.s) = v:=by
        rw [List.filter_eq_self]
        intro w' hw'
        rw [hne _ _ (hv.1 w' hw')]; rfl
      rw [List.filter_cons,this]; simp
    · rw [List.filter_cons,hne w.s a.s (fun e => hv.1 a ha e.symm)]
      simp only [Bool.not_false,if_true]
      exact (List.Perm.swap _ _ _).trans ((ih hv.2 ha).cons w)
lemma filter2 {v:List W} {x y:ℕ}:v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y)) =
    (v.filter (fun w => !Nat.beq w.s x)).filter (fun w => !Nat.beq w.s y):=by
  rw [List.filter_filter]; congr 1; funext w; cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> rfl
lemma filter1 {v:List W} {x:ℕ}:v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s x)) = v.filter (fun w => !Nat.beq w.s x):=by
  congr 1; funext w; cases Nat.beq w.s x <;> rfl
inductive Shape (o a c:W) (v:List W):Bool → Bool → List W → Prop
  | ff {r}:(a :: c :: r).Perm (o :: v) → Shape o a c v false false r
  | tf {r}:(c :: r).Perm (o :: v) → Shape o a c v true false r
  | ft {r}:(a :: r).Perm (o :: v) → Shape o a c v false true r
  | tt {r}:r.Perm (o :: v) → Shape o a c v true true r
lemma Shape.cnt {o a c:W} {v r:List W} {ka kc:Bool} (h:Shape o a c v ka kc r) (j:ℕ) :
    cnt r j + (bif ka then 0 else fl a j) + (bif kc then 0 else fl c j) = fl o j + cnt v j:=by
  cases h with
  | ff h => have:=cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tf h => have:=cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | ft h => have:=cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tt h => have:=cnt_perm h j; simp only [cnt_cons] at this; simp; omega
lemma Shape.mem {o a c:W} {v r:List W} {ka kc:Bool} (h:Shape o a c v ka kc r) {w:W} (hw:w ∈ r):w = o ∨ w ∈ v:=by
  have:w ∈ o :: v:=by
    cases h with
    | ff h => exact h.subset (by simp [hw])
    | tf h => exact h.subset (by simp [hw])
    | ft h => exact h.subset (by simp [hw])
    | tt h => exact h.subset (by simp [hw])
  simpa using this
lemma Shape.len {o a c:W} {v r:List W} {ka kc:Bool} (h:Shape o a c v ka kc r) :
    r.length + (bif ka then 0 else 1) + (bif kc then 0 else 1) = v.length + 1:=by
  cases h with
  | ff h => have:=h.length_eq; simp at this ⊢; omega
  | tf h => have:=h.length_eq; simp at this ⊢; omega
  | ft h => have:=h.length_eq; simp at this ⊢; omega
  | tt h => have:=h.length_eq; simp at this ⊢; omega
lemma Shape.rep {o a c:W} {v r:List W} {ka kc:Bool} (h:Shape o a c v ka kc r) {S S':Finset ℕ} (hr:Rep v S)
    (ha:a ∈ v) (hc:c ∈ v) (hac:a.s ≠ c.s) (ho:o.s ∉ S)
    (hS:∀ x,x ∈ S' ↔ x = o.s ∨ (x ∈ S ∧ (x = a.s → ka = true) ∧ (x = c.s → kc = true))):Rep r S':=by
  have hov:((o :: v).map W.s).Nodup:=by
    simp only [List.map_cons,List.nodup_cons]
    refine ⟨fun hm => ho ?_,hr.1⟩
    rw [← hr.2]; simpa using hm
  have hvS:∀ x,x ∈ v.map W.s ↔ x ∈ S:=fun x => by rw [← hr.2]; simp
  have hm:∀ x,x ∈ (o :: v).map W.s ↔ x = o.s ∨ x ∈ S:=fun x => by simp only [List.map_cons,List.mem_cons,hvS]
  have haS:=(hvS a.s).1 (List.mem_map_of_mem ha)
  have hcS:=(hvS c.s).1 (List.mem_map_of_mem hc)
  have hao:a.s ≠ o.s:=fun e => ho (e ▸ haS)
  have hco:c.s ≠ o.s:=fun e => ho (e ▸ hcS)
  cases h with
  | ff h =>
    have hn:=(h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons,List.nodup_cons,List.mem_cons,not_or] at hn
    refine ⟨hn.2.2,Finset.ext fun x => ?_⟩
    have hx:=(h.map W.s).mem_iff (a:=x)
    rw [hm] at hx; simp only [List.map_cons,List.mem_cons] at hx
    rw [List.mem_toFinset,hS]
    constructor
    · intro h1
      have n1:x ≠ a.s:=fun e => hn.1.2 (e ▸ h1)
      have n2:x ≠ c.s:=fun e => hn.2.1 (e ▸ h1)
      rcases hx.1 (Or.inr (Or.inr h1)) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e,fun e => absurd e n1,fun e => absurd e n2⟩
    · rintro (e | ⟨e,f1,f2⟩)
      · rcases hx.2 (Or.inl e) with e' | e' | e'
        · exact absurd (e'.symm.trans e) hao
        · exact absurd (e'.symm.trans e) hco
        · exact e'
      · rcases hx.2 (Or.inr e) with e' | e' | e'
        · exact absurd (f1 e') (by simp)
        · exact absurd (f2 e') (by simp)
        · exact e'
  | tf h =>
    have hn:=(h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons,List.nodup_cons] at hn
    refine ⟨hn.2,Finset.ext fun x => ?_⟩
    have hx:=(h.map W.s).mem_iff (a:=x)
    rw [hm] at hx; simp only [List.map_cons,List.mem_cons] at hx
    rw [List.mem_toFinset,hS]
    constructor
    · intro h1
      have n2:x ≠ c.s:=fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e,fun _ => rfl,fun e => absurd e n2⟩
    · rintro (e | ⟨e,f1,f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hco (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f2 e'
  | ft h =>
    have hn:=(h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons,List.nodup_cons] at hn
    refine ⟨hn.2,Finset.ext fun x => ?_⟩
    have hx:=(h.map W.s).mem_iff (a:=x)
    rw [hm] at hx; simp only [List.map_cons,List.mem_cons] at hx
    rw [List.mem_toFinset,hS]
    constructor
    · intro h1
      have n2:x ≠ a.s:=fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e,fun e => absurd e n2,fun _ => rfl⟩
    · rintro (e | ⟨e,f1,f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hao (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  | tt h =>
    have hn:=(h.map W.s).nodup_iff.2 hov
    refine ⟨hn,Finset.ext fun x => ?_⟩
    have hx:=(h.map W.s).mem_iff (a:=x)
    rw [hm] at hx
    rw [List.mem_toFinset,hS,hx]; simp
lemma shape_all {o a c:W} {v r:List W} (ho:∀ w ∈ v,w.s ≠ o.s) (hp:r.Perm (o :: v)) (hv:(v.map W.s).Nodup)
    (ha:a ∈ v) (hc:c ∈ v) (hac:a.s ≠ c.s) :
    Shape o a c v false false (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s c.s))) ∧
    Shape o a c v true false (r.filter (fun w => !(Nat.beq w.s c.s || Nat.beq w.s c.s))) ∧
    Shape o a c v false true (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))) ∧ Shape o a c v true true r:=by
  have hnd:(r.map W.s).Nodup:=by
    refine (hp.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons,List.nodup_cons,List.mem_map,not_exists,not_and]
    exact ⟨fun w hw => ho w hw,hv⟩
  have har:a ∈ r:=hp.symm.subset (by simp [ha])
  have hcr:c ∈ r:=hp.symm.subset (by simp [hc])
  refine ⟨.ff ?_,.tf ?_,.ft ?_,.tt hp⟩
  · rw [filter2]
    have h1:=filter_perm hnd har
    have h2:c ∈ r.filter (fun w => !Nat.beq w.s a.s):=by
      rw [List.mem_filter]; refine ⟨hcr,?_⟩
      rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
    exact ((filter_perm (hnd.sublist (List.filter_sublist.map _)) h2).cons a).trans (h1.trans hp)
  · rw [filter1]; exact (filter_perm hnd hcr).trans hp
  · rw [filter1]; exact (filter_perm hnd har).trans hp
lemma cnt_two {v:List W} {a c:W} (ha:a ∈ v) (hc:c ∈ v) (hv:(v.map W.s).Nodup) (hac:a.s ≠ c.s) (j:ℕ) :
    fl a j + fl c j ≤ cnt v j:=by
  have h1:=cnt_perm (filter_perm hv ha) j
  have h2:c ∈ v.filter (fun w => !Nat.beq w.s a.s):=by
    rw [List.mem_filter]; refine ⟨hc,?_⟩
    rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
  have h3:=cnt_perm (filter_perm (hv.sublist (List.filter_sublist.map _)) h2) j
  simp only [cnt_cons] at h1 h3; omega
lemma cnt_one {v:List W} {a:W} (ha:a ∈ v) (hv:(v.map W.s).Nodup) (j:ℕ):fl a j ≤ cnt v j:=by
  have h1:=cnt_perm (filter_perm hv ha) j
  simp only [cnt_cons] at h1; omega
def opW (d:Bool) (a c:W):W:=bif d then ⟨a.s ||| c.s,a.a &&& c.a,a.b ||| c.b,(a.a &&& c.a) ||| (a.b ||| c.b),0⟩
  else ⟨a.s &&& c.s,a.a ||| c.a,a.b &&& c.b,(a.a ||| c.a) ||| (a.b &&& c.b),0⟩
lemma opW_s (d:Bool) (a c:W):(opW d a c).s = op d a.s c.s:=by cases d <;> rfl
lemma opW_ok {P:List ℕ} {a c:W} (d:Bool) (ha:WOk P a) (hc:WOk P c):WOk P (opW d a c):=by
  cases d
  · refine ⟨isPk_or ha.pa hc.pa,isPk_and ha.pb,rfl,fun j hj h => ?_,fun j hj h => ?_⟩
    · have h:(a.a ||| c.a).testBit (5 * j) = true:=h
      rw [Nat.testBit_or,Bool.or_eq_true] at h
      rw [opW_s,and_op]
      rcases h with h | h
      · rw [ha.ca j hj h]; simp [op]
      · rw [hc.ca j hj h]; simp [op]
    · have h:(a.b &&& c.b).testBit (5 * j) = true:=h
      rw [Nat.testBit_and,Bool.and_eq_true] at h
      rw [opW_s,and_op,ha.cb j hj h.1,hc.cb j hj h.2,op_self]
  · refine ⟨isPk_and ha.pa,isPk_or ha.pb hc.pb,rfl,fun j hj h => ?_,fun j hj h => ?_⟩
    · have h:(a.a &&& c.a).testBit (5 * j) = true:=h
      rw [Nat.testBit_and,Bool.and_eq_true] at h
      rw [opW_s,and_op,ha.ca j hj h.1,hc.ca j hj h.2,op_self]
    · have h:(a.b ||| c.b).testBit (5 * j) = true:=h
      rw [Nat.testBit_or,Bool.or_eq_true] at h
      rw [opW_s,and_op]
      rcases h with h | h
      · rw [ha.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
      · rw [hc.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_good {l x y:ℕ} (d:Bool) (hx:Good l x) (hy:Good l y):Good l (op d x y):=by
  refine ⟨fun i j h h1 h2 => ?_,fun i j h h1 h2 => ?_⟩
  · rw [op_bit,op_bit,hx.1 i j h h1 h2,hy.1 i j h h1 h2]
  · rw [op_bit,op_bit,hx.2 i j h h1 h2,hy.2 i j h h1 h2]
lemma fl_and {P:List ℕ} {a c:W} (ha:WOk P a):a.c &&& c.c = pk P.length (fun j => fl a j * fl c j):=by
  rw [pk_of (isPk_and (y:=c.c) ha.pc)]
  refine pk_congr fun j _ => ?_
  rw [Nat.testBit_and]; unfold fl; cases a.c.testBit (5 * j) <;> cases c.c.testBit (5 * j) <;> rfl
lemma fl_pk {P:List ℕ} {a:W} (ha:WOk P a):a.c = pk P.length (fl a):=pk_of ha.pc
section sound
variable {P:List ℕ} {l m g T:ℕ} (X:Ctx P l m g T)
include X
lemma bi_st {k k' t z:ℕ} {v r:List W} {S S':Finset ℕ} {d':Bool} {a c:W} {ka kc:Bool}
    (hs:StOk P T l (k + 1) z v S) (hm:Min R m T (k' + 1) t S) (hk:k' ≤ k) (hb:Bi R d' a.s c.s S S')
    (hl:Live R m T k' t S') (ha:a ∈ v) (hc:c ∈ v) (hka:ka = decide (a.s ∈ S')) (hkc:kc = decide (c.s ∈ S'))
    (hsh:Shape (opW d' a c) a c v ka kc r) :
    StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
    Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true:=by
  obtain ⟨b,hb15,hcl,hz⟩:=hs.bud
  have hle:=cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hab:a.s ≠ c.s:=hb.1
  have hfr:=hb.fresh hl hm.2
  have hfS:(opW d' a c).s ∉ S:=by rw [opW_s]; exact fun h => hfr (sub_C _ _ (by simpa using h))
  have wa:=hs.wok a ha; have wc:=hs.wok c hc
  have wo:=opW_ok d' wa wc
  have hrep:Rep r S':=by
    refine hsh.rep hs.rep ha hc hab hfS fun x => ?_
    obtain ⟨_,U,e1,e2,_⟩:=hb
    rw [opW_s] at hfS ⊢
    rw [e2,Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h],?_,?_⟩
        · rintro rfl; rw [hka,e2]; simp [h]
        · rintro rfl; rw [hkc,e2]; simp [h]
    · rintro (h | ⟨h,f1,f2⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h | h
        · have:=f1 h; rw [hka,decide_eq_true_eq,e2,Finset.mem_insert] at this; rw [h]; exact this
        · have:=f2 h; rw [hkc,decide_eq_true_eq,e2,Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hwok:∀ w ∈ r,WOk P w:=fun w hw => (hsh.mem hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood:∀ w ∈ r,Good l w.s:=fun w hw => by
    rcases hsh.mem hw with rfl | h
    · rw [opW_s]; exact op_good _ (hs.good a ha) (hs.good c hc)
    · exact hs.good w h
  let b':ℕ → ℕ:=fun j => b j - max (fl a j) (fl c j)
  have hcl':Cl P T k b' S':=by
    intro j hj q hq hsol
    have hl1:=hle j hj
    have h2:=cnt_two ha hc hs.rep.1 hab j
    simp only [b'] at hq
    by_cases hkill:a.c.testBit (5 * j) = true ∨ c.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (hkill.imp (wa.cst hj) (wc.cst hj)) hsol)
      have:1 ≤ max (fl a j) (fl c j):=by
        rcases hkill with h | h <;> simp [fl,h]
      have:=fl_le a j; have:=fl_le c j; omega
    · push Not at hkill
      refine hcl j hj (q + 1) ?_ (hb.im hsol)
      have e1:fl a j = 0:=by simp [fl,hkill.1]
      have e2:fl c j = 0:=by simp [fl,hkill.2]
      rw [e1,e2] at hq; simp at hq; omega
  have hmin:=hb.min hl hm.2
  have hle':=cnt_le X hrep hwok hcl' hmin hk
  have num:∀ j < P.length,1 ≤ 16 + b j - cnt v j + fl a j * fl c j ∧ fl (opW d' a c) j ≤ 1 ∧
      16 ≤ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j ∧ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j < 32 ∧
      16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j - (bif ka then fl a j else 0) - (bif kc then fl c j else 0) = 16 + b' j - cnt r j:=by
    intro j hj
    have q1:=hle j hj; have q2:=hle' j hj; have q3:=cnt_two ha hc hs.rep.1 hab j; have q4:=hb15 j hj
    have q5:=hsh.cnt j; have q6:=fl_le a j; have q7:=fl_le c j; have q8:=fl_le (opW d' a c) j
    simp only [b'] at q2 ⊢
    generalize fl a j = fa at *; generalize fl c j = fc at *; generalize fl (opW d' a c) j = fo at *
    interval_cases fa <;> interval_cases fc <;> cases ka <;> cases kc <;> simp at q2 q3 q5 ⊢ <;> omega
  have e1:z + (a.c &&& c.c) - (opW d' a c).c = pk P.length (fun j => 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j):=by
    rw [hz,fl_and wa,fl_pk wo,pk_add,pk_sub]
    intro j hj; have:=num j hj; omega
  refine ⟨⟨hrep,hwok,hgood,b',fun j hj => ?_,hcl',?_⟩,?_⟩
  · have:=hb15 j hj; simp only [b']; omega
  · rw [e1]
    have ea:(bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0):=by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have ec:(bif kc then c.c else 0) = pk P.length (fun j => bif kc then fl c j else 0):=by
      cases kc
      · simp [pk]
      · exact fl_pk wc
    have le1:∀ j,(bif ka then fl a j else 0) ≤ 1:=fun j => by cases ka <;> simp [fl_le]
    have le2:∀ j,(bif kc then fl c j else 0) ≤ 1:=fun j => by cases kc <;> simp [fl_le]
    rw [ea,ec,pk_sub,pk_sub]
    · exact pk_congr fun j hj => (num j hj).2.2.2.2
    · intro j hj; have:=num j hj; have:=le1 j; have:=le2 j; omega
    · intro j hj; have:=num j hj; have:=le1 j; omega
  · rw [e1,nl,X.hg,pk_guard]; · simp
    intro j hj; have:=num j hj; omega
lemma drop_ok {k' t:ℕ} {v:List W} {S S':Finset ℕ} {d':Bool} {a c:W} {i:ℕ} (hr:Rep v S)
    (hb:Bi R d' a.s c.s S S') (hl:Live R m T k' t S')
    (ha:a ∈ v) (hk:a.s ∉ S')
    (hu:(Nat.land (sp (pos' t) l a.s) (wst (pos' t) l v)).testBit i = true) :
    bif d' then c.s.testBit (NN + i) = false else c.s.testBit i = true:=by
  obtain ⟨hli,u1,u2⟩:=uq_of hr ha hu
  obtain ⟨⟨m1,m2,t1,t2⟩,_⟩:=X.lg i hli
  obtain ⟨w,hw,hs⟩:=hl.cov m1 m2 t1 t2
  have hac:c.s ≠ a.s:=hb.1.symm
  have hsub:=hb.sub.2.2 hw
  rw [Finset.mem_insert] at hsub
  have hg:sepb NN (pos' t) (op d' a.s c.s) i = true:=by
    rcases hsub with rfl | h
    · exact hs
    · have:=u2 w h (fun e => hk (e ▸ hw))
      rw [this] at hs; simp at hs
  have hcn:=u2 c.s hb.sub.2.1 hac
  revert hg hcn u1
  unfold sepb; simp only [op_bit]
  cases pos' t <;> cases d' <;> cases a.s.testBit i <;> cases a.s.testBit (NN + i) <;> cases c.s.testBit i <;>
    cases c.s.testBit (NN + i) <;> simp
end sound
def mkx (d:Bool) (l o:ℕ) (w:W):X:=⟨w,w.s,Nat.shiftRight w.s NN,Nat.land (sp d l w.s) o⟩
lemma mkX_eq (d:Bool) (l o:ℕ) (v:List W):mkX d l o v = v.map (mkx d l o):=by
  induction v with
  | nil => rfl
  | cons w v ih => change _ :: mkX d l o v = _; rw [ih]; rfl
def modeF (n e:ℕ):(W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ n) e then f2 else f1) else f0
lemma node_eq (f:ℕ → List W → Bool) (d:Bool) (l m g e n z:ℕ) (v:List W) (go:(X → X → Bool) → List X → Bool) :
    node f d l m g e n z v go = go (pair (modeF n e (mid f m g e (Nat.pred n) z v))) (v.map (mkx d l (wst d l v))):=by
  rw [← mkX_eq]; unfold node modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl
lemma modeF_false {n e:ℕ} {h:W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {a c:W} {da dc:ℕ} {s x y:ℕ}
    (hf:modeF n e h a c da dc s x y = false) (h0:¬ n ≤ e → da = 0 ∧ dc = 0) (h1:¬ n + 1 ≤ e → da = 0 ∨ dc = 0) :
    h a c da dc s x y = false:=by
  unfold modeF at hf
  cases b1:Nat.ble n e with
  | false =>
    have:=h0 (fun h => by rw [Nat.ble_eq_true_of_le h] at b1; simp at b1)
    rw [b1,this.1,this.2] at hf; rw [this.1,this.2]; exact hf
  | true =>
    cases b2:Nat.ble (Nat.succ n) e with
    | false =>
      have:=h1 (fun h => by rw [Nat.ble_eq_true_of_le h] at b2; simp at b2)
      have h3:Nat.beq (Nat.mul da dc) 0 = true:=by
        change Nat.beq (da * dc) 0 = true
        rcases this with h | h <;> simp [h]
      rw [b1,b2] at hf
      simp only [Bool.cond_true,Bool.cond_false,f1,h3] at hf
      exact hf
    | true => rw [b1,b2] at hf; exact hf
def dfc (d d':Bool) (l o:ℕ) (a c:W):ℕ:=bif d' then Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s NN)
  else Nat.xor (Nat.land (Nat.land (sp d l a.s) o) c.s) (Nat.land (sp d l a.s) o)
lemma pair_false {h:W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {d:Bool} {l o:ℕ} {a c:W}
    (hp:pair h (mkx d l o a) (mkx d l o c) = false) (d':Bool) :
    h a c (dfc d d' l o a c) (dfc d d' l o c a) (opW d' a c).s (opW d' a c).a (opW d' a c).b = false:=by
  simp only [pair,mkx,bR] at hp
  rw [Bool.cond_eq_ite] at hp
  split_ifs at hp with h1
  · cases d'
    · rw [Bool.not_eq_true] at h1; exact h1
    · exact hp
lemma put_eq {m:ℕ} {o:W} {v:List W} (ho:Nat.lor o.a o.b = o.c) (hr:o.r = 0) (h0:o.s ≠ 0) (h1:o.s ≠ m) (h:List W → Bool) :
    put m o.s o.a o.b v h = ins o v h:=by
  have hb0:Nat.beq o.s 0 = false:=Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
  have hb1:Nat.beq o.s m = false:=Bool.eq_false_iff.2 fun h => h1 (Nat.eq_of_beq_eq_true h)
  simp only [put,st_eq,hb0,hb1,ho]
  rw [← hr]
lemma mid_false {f:ℕ → List W → Bool} {m g e n z:ℕ} {v:List W} {a c:W} {da dc:ℕ} {d':Bool}
    (h:mid f m g e n z v a c da dc (opW d' a c).s (opW d' a c).a (opW d' a c).b = false)
    (hg:Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true) :
    kids (child f g) e n (z + (a.c &&& c.c) - (opW d' a c).c) a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0)
      (put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v) = false:=by
  have ec:Nat.lor (opW d' a c).a (opW d' a c).b = (opW d' a c).c:=by cases d' <;> rfl
  simp only [mid,st_eq,ec] at h
  have hg':Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (opW d' a c).c) g) g = true:=hg
  rw [hg'] at h
  exact h
lemma kids_false {ch:((List W → Bool) → Bool) → ℕ → Bool} {e n z x y a c:ℕ} {oa oc:Bool} {mk:(List W → Bool) → Bool}
    (h:kids ch e n z x y a c oa oc mk = false) :
    (oa = true → oc = true → ch (fun h => mk (fun r => rm a c r h)) z = false) ∧
    (oc = true → n + 1 ≤ e → ch (fun h => mk (fun r => rm c c r h)) (z - x) = false) ∧
    (oa = true → n + 1 ≤ e → ch (fun h => mk (fun r => rm a a r h)) (z - y) = false) ∧
    (n + 2 ≤ e → ch mk (z - x - y) = false):=by
  simp only [kids,bR] at h
  have b1:n + 1 ≤ e → Nat.ble (Nat.succ n) e = true:=fun h => Nat.ble_eq_true_of_le h
  have b2:n + 2 ≤ e → Nat.ble (Nat.succ (Nat.succ n)) e = true:=fun h => Nat.ble_eq_true_of_le h
  refine ⟨?_,?_,?_,?_⟩
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
lemma Live.rel {R':ℕ → ℕ} {m T k t:ℕ} {S:Finset ℕ} (h:Live R m T k t S) (hR:∀ d a b,Al R d a b → Al R' d a b):Live R' m T k t S:=by
  induction h with
  | stop => exact .stop
  | un _ ih => exact .un ih
  | bi hab hal _ ih => exact .bi hab (hR _ _ _ hal) ih
lemma Bi.rel {R':ℕ → ℕ} {a b:ℕ} {d:Bool} {S S':Finset ℕ} (h:Bi R d a b S S') (hR:∀ d a b,Al R d a b → Al R' d a b):Bi R' d a b S S':=by
  obtain ⟨hab,U,e1,e2,hal⟩:=h; exact ⟨hab,U,e1,e2,hR _ _ _ hal⟩
section sound
variable {P:List ℕ} {l m g T:ℕ} (X:Ctx P l m g T)
include X
lemma rect_ok {t k k' z:ℕ} {r:List W} {S:Finset ℕ} (hr:StOk P T l k z r S) (hm:Min R m T k' t S) (hk:k' ≤ k)
    (hn:r.length + t = k + 1):rect (pos' t) l (wst (pos' t) l r) r [] = false:=by
  cases hrect:rect (pos' t) l (wst (pos' t) l r) r [] with
  | false => rfl
  | true =>
      exfalso
      have hs:=hm.size
      have hcard:=hr.rep.card
      have hpos:0 < S.card:=hm.1.pos
      have htight:S.card + t = k' + 1:=by omega
      rw [rect_false (o:=wst (pos' t) l r)] at hrect; · simp at hrect
      · have hnd:r.Pairwise (fun a b => a.s ≠ b.s):=List.pairwise_map.1 hr.rep.1
        refine hnd.imp_of_mem fun {a b} ha hb' hab => ?_
        by_contra hhit
        rw [Bool.not_eq_false] at hhit
        obtain ⟨⟨s,hs1,x1,x2⟩,⟨s',hs2,y1,y2⟩⟩:=hit_spec hhit
        have hu:∀ w,∀ i,(Nat.land (sp (pos' t) l w) (wst (pos' t) l r)).testBit i = true → AA.testBit i = true:=by
          intro w i hi
          simp only [nl,Nat.testBit_and,sp_bit,Bool.and_eq_true] at hi
          exact (X.lg i hi.1.1).2
        obtain ⟨i2,b1,b2,b3⟩:=flag_seg segX_ok (hu b.s) hs1 x1
        obtain ⟨i1,a1,a2,a3⟩:=flag_seg segX_ok (hu a.s) hs1 x2
        obtain ⟨j2,d1,d2,d3⟩:=flag_seg segY_ok (hu b.s) hs2 y1
        obtain ⟨j1,c1,c2,c3⟩:=flag_seg segY_ok (hu a.s) hs2 y2
        obtain ⟨l1,u1⟩:=uq_of hr.rep ha a3
        obtain ⟨l2,u2⟩:=uq_of hr.rep hb' b3
        obtain ⟨l3,u3⟩:=uq_of hr.rep ha c3
        obtain ⟨l4,u4⟩:=uq_of hr.rep hb' d3
        have g1:∀ w ∈ S,w.testBit i1 = w.testBit i2:=by
          intro w hw; obtain ⟨w',hw',rfl⟩:=hr.rep.mem.1 hw
          exact (hr.good w' hw').1 _ _ ⟨s,hs1,a1,a2,b1,b2⟩ l1 l2
        have g2:∀ w ∈ S,w.testBit (NN + j1) = w.testBit (NN + j2):=by
          intro w hw; obtain ⟨w',hw',rfl⟩:=hr.rep.mem.1 hw
          exact (hr.good w' hw').2 _ _ ⟨s',hs2,c1,c2,d1,d2⟩ l3 l4
        have ma:=hr.rep.mem.2 ⟨a,ha,rfl⟩
        have mb:=hr.rep.mem.2 ⟨b,hb',rfl⟩
        rcases Nat.eq_zero_or_pos t with rfl | htp
        · have hd':pos' 0 = false:=by simp [pos']
          rw [hd'] at u1 u2 u3 u4
          exact rect0 hm.1 hm.2 (by simpa using htight) (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
        · have hd':pos' t = true:=by simp [pos',htp]
          rw [hd'] at u1 u2 u3 u4
          exact rect1 hm.1 hm.2 htight (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
      · simp
lemma hit_ht {k z:ℕ} {r:List W} {S:Finset ℕ} {d:Bool} (hr:StOk P T l k z r S) {a b:W} (ha:a ∈ r) (hb:b ∈ r)
    (h:hit (flag false l (wst d l r) a) (flag false l (wst d l r) b) = true):Ht NN m T d S a.s b.s:=by
  obtain ⟨⟨s,hs1,x1,x2⟩,⟨s',hs2,y1,y2⟩⟩:=hit_spec h
  have hu:∀ w,∀ i,(Nat.land (sp false l w) (wst d l r)).testBit i = true → AA.testBit i = true:=by
    intro w i hi
    simp only [nl,Nat.testBit_and,sp_bit,Bool.and_eq_true] at hi
    exact (X.lg i hi.1.1).2
  have uq:∀ {w:W} {i:ℕ},w ∈ r → (Nat.land (sp false l w.s) (wst d l r)).testBit i = true →
      l.testBit i = true ∧ Uq NN d S w.s i ∧ w.s.testBit i = true:=by
    intro w i hw hi
    have hi2:=hi
    simp only [nl,Nat.testBit_and,sp_bit,Bool.and_eq_true] at hi2
    obtain ⟨⟨hl,hs⟩,ho⟩:=hi2
    have hsd:sepb NN d w.s i = true:=by
      cases d
      · exact hs
      · exact sepb_weak _ hs
    obtain ⟨q1,q2⟩:=uq_of hr.rep hw (d:=d) (l:=l) (i:=i) (by
      simp only [nl,Nat.testBit_and,sp_bit,Bool.and_eq_true]; exact ⟨⟨hl,hsd⟩,ho⟩)
    refine ⟨q1,q2,?_⟩
    revert hs; simp only [sepb,cond_false]; cases w.s.testBit i <;> simp
  obtain ⟨i1,a1,a2,a3⟩:=flag_seg segX_ok (hu a.s) hs1 x1
  obtain ⟨i2,b1,b2,b3⟩:=flag_seg segX_ok (hu b.s) hs1 x2
  obtain ⟨j1,c1,c2,c3⟩:=flag_seg segY_ok (hu a.s) hs2 y1
  obtain ⟨j2,d1,d2,d3⟩:=flag_seg segY_ok (hu b.s) hs2 y2
  obtain ⟨l1,u1,p1⟩:=uq ha a3
  obtain ⟨l2,u2,p2⟩:=uq hb b3
  obtain ⟨l3,u3,p3⟩:=uq ha c3
  obtain ⟨l4,u4,p4⟩:=uq hb d3
  refine ⟨i1,i2,j1,j2,(X.lg _ l1).1,(X.lg _ l2).1,(X.lg _ l3).1,(X.lg _ l4).1,?_,?_,u1,u2,u3,u4,by rw [p1,p3],by rw [p2,p4]⟩
  · intro w hw; obtain ⟨w',hw',rfl⟩:=hr.rep.mem.1 hw
    exact (hr.good w' hw').1 _ _ ⟨s,hs1,a1,a2,b1,b2⟩ l1 l2
  · intro w hw; obtain ⟨w',hw',rfl⟩:=hr.rep.mem.1 hw
    exact (hr.good w' hw').2 _ _ ⟨s',hs2,c1,c2,d1,d2⟩ l3 l4
end sound
lemma hits_true {f:ℕ} {m:List ℕ} (h:hits f m = true):∃ e ∈ m,hit f e = true:=by
  by_contra hc
  push Not at hc
  rw [hits_false fun e he => by simpa using hc e he] at h; simp at h
lemma app_mem {x y:List ℕ} {e:ℕ}:e ∈ app x y ↔ e ∈ x ∨ e ∈ y:=by
  induction x with
  | nil => simp [app]
  | cons a x ih =>
    change e ∈ a :: app x y ↔ _
    simp only [List.mem_cons,ih,or_assoc]
def CmOk (F:W → ℕ) (r:List W) (col:ℕ → ℕ) (c:Cm):Prop:=∃ κ ≤ 1,(∀ e ∈ c.a,∃ w ∈ r,F w = e ∧ col w.s = κ) ∧
  ∀ e ∈ c.b,∃ w ∈ r,F w = e ∧ col w.s = 1 - κ
lemma join_false {F:W → ℕ} {r:List W} {col:ℕ → ℕ} {k:List Cm → Bool} {w:W} (hw1:col w.s ≤ 1)
    (hh:∀ w' ∈ r,hit (F w) (F w') = true → col w.s ≠ col w'.s)
    (hk:∀ cs,(∀ c ∈ cs,CmOk F (w :: r) col c) → k cs = false):∀ (cs:List Cm) (S O:List ℕ) (Q:List Cm),
    (∀ c ∈ cs,CmOk F r col c) → (∀ c ∈ Q,CmOk F (w :: r) col c) → (∀ e ∈ S,∃ w' ∈ w :: r,F w' = e ∧ col w'.s = col w.s) →
    (∀ e ∈ O,∃ w' ∈ w :: r,F w' = e ∧ col w'.s = 1 - col w.s) → join k (F w) cs S O Q = false:=by
  intro cs
  induction cs with
  | nil =>
    intro S O Q _ hQ hS hO
    refine hk _ fun c hc => ?_
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨col w.s,hw1,hS,hO⟩
    · exact hQ c hc
  | cons c cs ih =>
    intro S O Q hcs hQ hS hO
    have hc:=hcs c (by simp)
    have hcs':∀ c ∈ cs,CmOk F r col c:=fun c' h => hcs c' (by simp [h])
    obtain ⟨κ,hκ,ha,hb⟩:=hc
    have e:join k (F w) (c :: cs) S O Q = bif hits (F w) c.a then (bif hits (F w) c.b then true else join k (F w) cs (app c.b S) (app c.a O) Q)
        else (bif hits (F w) c.b then join k (F w) cs (app c.a S) (app c.b O) Q else join k (F w) cs S O (c :: Q)):=by
      change (Bool.rec (motive:=fun _ => Bool)
        (Bool.rec (motive:=fun _ => Bool) (join k (F w) cs S O (c :: Q)) (join k (F w) cs (app c.a S) (app c.b O) Q) (hits (F w) c.b))
        (Bool.rec (motive:=fun _ => Bool) (join k (F w) cs (app c.b S) (app c.a O) Q) true (hits (F w) c.b)) (hits (F w) c.a):Bool) = _
      rw [bR,bR,bR]
    rw [e]
    have hA:hits (F w) c.a = true → κ = 1 - col w.s:=by
      intro h
      obtain ⟨x,hx,hhx⟩:=hits_true h
      obtain ⟨w',hw',e1,e2⟩:=ha x hx
      have:=hh w' hw' (by rw [e1]; exact hhx)
      omega
    have hB:hits (F w) c.b = true → κ = col w.s:=by
      intro h
      obtain ⟨x,hx,hhx⟩:=hits_true h
      obtain ⟨w',hw',e1,e2⟩:=hb x hx
      have:=hh w' hw' (by rw [e1]; exact hhx)
      omega
    have up:∀ {κ':ℕ} {L:List ℕ},(∀ e ∈ L,∃ w' ∈ r,F w' = e ∧ col w'.s = κ') → ∀ e ∈ L,∃ w' ∈ w :: r,F w' = e ∧ col w'.s = κ':=by
      intro κ' L h e he
      obtain ⟨w',h1,h2⟩:=h e he
      exact ⟨w',by simp [h1],h2⟩
    cases h1:hits (F w) c.a with
    | true =>
      have k1:=hA h1
      cases h2:hits (F w) c.b with
      | true => have k2:=hB h2; omega
      | false =>
        simp only [cond_true,cond_false]
        refine ih _ _ _ hcs' hQ ?_ ?_
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w',q1,q2,q3⟩:=up hb e h; exact ⟨w',q1,q2,by omega⟩
          · exact hS e h
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w',q1,q2,q3⟩:=up ha e h; exact ⟨w',q1,q2,by omega⟩
          · exact hO e h
    | false =>
      cases h2:hits (F w) c.b with
      | true =>
        have k2:=hB h2
        simp only [cond_true,cond_false]
        refine ih _ _ _ hcs' hQ ?_ ?_
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w',q1,q2,q3⟩:=up ha e h; exact ⟨w',q1,q2,by omega⟩
          · exact hS e h
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w',q1,q2,q3⟩:=up hb e h; exact ⟨w',q1,q2,by omega⟩
          · exact hO e h
      | false =>
        simp only [cond_false]
        refine ih _ _ _ hcs' ?_ hS hO
        intro c' hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact ⟨κ,hκ,up ha,up hb⟩
        · exact hQ c' hc'
lemma bip_aux {l o:ℕ} {col:ℕ → ℕ}:∀ (v r:List W) (cs:List Cm),(∀ w ∈ v,col w.s ≤ 1) → (∀ c ∈ cs,CmOk (flag false l o) r col c) →
    (∀ w ∈ v,∀ w' ∈ r,hit (flag false l o w) (flag false l o w') = true → col w.s ≠ col w'.s) →
    v.Pairwise (fun a b => hit (flag false l o b) (flag false l o a) = true → col b.s ≠ col a.s) → bip l o v cs = false:=by
  intro v
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro r cs h1 h2 h3 h4
    rw [List.pairwise_cons] at h4
    change join (bip l o v) (flag false l o w) cs [flag false l o w] [] [] = false
    refine join_false (F:=flag false l o) (h1 w (by simp)) (h3 w (by simp)) ?_ cs _ _ _ h2 (by simp) ?_ (by simp)
    · intro cs' hcs'
      refine ih (w :: r) cs' (fun x hx => h1 x (by simp [hx])) hcs' ?_ h4.2
      intro x hx w' hw'
      simp only [List.mem_cons] at hw'
      rcases hw' with rfl | hw'
      · exact h4.1 x hx
      · exact h3 x (by simp [hx]) w' hw'
    · intro e he
      simp only [List.mem_singleton] at he
      exact ⟨w,by simp,he.symm,rfl⟩
lemma anyE_false:∀ {m:List ℕ},m.Pairwise (fun p q => hit p q = false) → anyE m = false:=by
  intro m
  induction m with
  | nil => intro _; rfl
  | cons f t ih =>
    intro h
    rw [List.pairwise_cons] at h
    change (Bool.rec (motive:=fun _ => Bool) (anyE t) true (hits f t):Bool) = false
    rw [bR,hits_false h.1,ih h.2]; rfl
lemma rmF_eq (F:W → ℕ) (f:ℕ) (t:List W):rmF f (t.map F) = (t.eraseP (fun q => hit f (F q))).map F:=by
  induction t with
  | nil => rfl
  | cons x t ih =>
    change (Bool.rec (motive:=fun _ => List ℕ) (F x :: rmF f (t.map F)) (t.map F) (hit f (F x)):List ℕ) = _
    rw [List.eraseP_cons]
    cases h:hit f (F x)
    · simp [ih]
    · simp
lemma eraseP_not {α:Type} {p:α → Bool} {a:α}:∀ {t:List α},t.Nodup → a ∈ t → p a = true → (∀ x ∈ t,p x = true → x = a) → a ∉ t.eraseP p:=by
  intro t
  induction t with
  | nil => intro _ h; simp at h
  | cons x t ih =>
    intro hn ha hp hx
    rw [List.nodup_cons] at hn
    rw [List.eraseP_cons]
    cases h:p x
    · have hax:a ≠ x:=fun e => by rw [← e,hp] at h; simp at h
      simp only [Bool.false_eq_true,if_false,List.mem_cons,not_or]
      simp only [List.mem_cons] at ha
      exact ⟨hax,ih hn.2 (ha.resolve_left hax) hp fun y hy => hx y (by simp [hy])⟩
    · have:=hx x (by simp) h
      subst this
      simpa using hn.1
lemma star_false {F:W → ℕ} {a:W}:∀ {v:List W},v.Nodup → star (v.map F) = false →
    ∃ p q:W,[p,q].Sublist v ∧ hit (F p) (F q) = true ∧ p ≠ a ∧ q ≠ a:=by
  intro v hn hst
  by_contra hno
  push Not at hno
  have bad:∀ p q:W,[p,q].Sublist v → hit (F p) (F q) = true → p = a ∨ q = a:=by
    intro p q h1 h2
    by_cases h:p = a
    · exact Or.inl h
    · exact Or.inr (hno p q h1 h2 h)
  clear hno
  have key:star (v.map F) = true:=by
    clear hst
    induction v with
    | nil => rfl
    | cons w t ih =>
      rw [List.nodup_cons] at hn
      have bt:∀ p q:W,[p,q].Sublist t → hit (F p) (F q) = true → p = a ∨ q = a:=fun p q h => bad p q (h.cons w)
      have e:star ((w :: t).map F) = bif hits (F w) (t.map F) then (bif anyE (t.map F) then (bif hits (F w) (rmF (F w) (t.map F)) then false else
          (bif anyE (rmF (F w) (t.map F)) then false else true)) else true) else star (t.map F):=by
        change (Bool.rec (motive:=fun _ => Bool) (star (t.map F)) (Bool.rec (motive:=fun _ => Bool) true (Bool.rec (motive:=fun _ => Bool)
          (Bool.rec (motive:=fun _ => Bool) true false (anyE (rmF (F w) (t.map F)))) false (hits (F w) (rmF (F w) (t.map F)))) (anyE (t.map F))) (hits (F w) (t.map F)):Bool) = _
        rw [bR,bR,bR,bR]
      rw [e]
      have edge:∀ u:List W,u.Sublist t → a ∉ u → anyE (u.map F) = false:=by
        intro u hu ha
        refine anyE_false ?_
        rw [List.pairwise_map,List.pairwise_iff_forall_sublist]
        intro p q hpq
        by_contra hc
        rw [Bool.not_eq_false] at hc
        have hm:∀ x ∈ [p,q],x ∈ u:=fun x hx => hpq.subset hx
        rcases bt p q (hpq.trans hu) hc with rfl | rfl
        · exact ha (hm p (by simp))
        · exact ha (hm q (by simp))
      cases h1:hits (F w) (t.map F) with
      | false => rw [cond_false]; exact ih hn.2 bt
      | true =>
        rw [cond_true]
        have part:∀ q ∈ t,hit (F w) (F q) = true → w = a ∨ q = a:=fun q hq h => bad w q ((List.singleton_sublist.2 hq).cons_cons w) h
        by_cases hwa:w = a
        · subst hwa
          rw [edge t (List.Sublist.refl t) hn.1]; rfl
        · have pa:∀ q ∈ t,hit (F w) (F q) = true → q = a:=fun q hq h => (part q hq h).resolve_left hwa
          obtain ⟨x,hx,hhx⟩:=hits_true h1
          obtain ⟨q,hq,rfl⟩:=List.mem_map.1 hx
          have hqa:=pa q hq hhx
          subst hqa
          have hna:q ∉ t.eraseP (fun q => hit (F w) (F q)):=eraseP_not hn.2 hq hhx pa
          rw [rmF_eq,edge _ List.eraseP_sublist hna]
          have:hits (F w) ((t.eraseP (fun q => hit (F w) (F q))).map F) = false:=by
            refine hits_false fun e he => ?_
            obtain ⟨y,hy,rfl⟩:=List.mem_map.1 he
            by_contra hc
            rw [Bool.not_eq_false] at hc
            have hyt:y ∈ t:=List.eraseP_sublist.subset hy
            exact hna (pa y hyt hc ▸ hy)
          rw [this]
          cases anyE (t.map F) <;> rfl
  rw [key] at hst; simp at hst
lemma flk_eq (l o:ℕ) (v:List W):∀ k,flk l o v k = k (v.map (flag false l o)):=by
  induction v with
  | nil => intro k; rfl
  | cons w v ih =>
    intro k
    change flk l o v (fun r => k (flag false l o w :: r)) = _
    rw [ih]; rfl
def NK (R:ℕ → ℕ) (m T k' t:ℕ) (S:Finset ℕ):Prop :=
  (∀ d a b S1 k0,k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → S1.card < S.card) ∧
  ∀ a S1 k0 t0,k' = k0 + 1 → t = t0 + 1 → Un m a S S1 → Live R m T k0 t0 S1 → S1.card ≤ S.card
lemma Rep.nodup {v:List W} {S:Finset ℕ} (h:Rep v S):v.Nodup:=List.Nodup.of_map _ h.1
section sound
variable {P:List ℕ} {l m g T:ℕ} (X:Ctx P l m g T)
include X
lemma nk_ok {k k' t z:ℕ} {v:List W} {S:Finset ℕ} (hs:StOk P T l k z v S) (hm:Min R m T k' t S)
    (hx:k' ≤ S.card + t) (hst:flk l (wst (pos' t) l v) v star = false):NK R m T k' t S:=by
  rw [flk_eq] at hst
  have hsz:=hm.size
  have av:∀ a:ℕ,a ∈ S → ∃ p q:ℕ,p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ p ≠ a ∧ q ≠ a ∧ Ht NN m T (pos' t) S p q:=by
    intro a ha
    obtain ⟨wa,hwa,rfl⟩:=hs.rep.mem.1 ha
    obtain ⟨p,q,hpq,hh,h1,h2⟩:=star_false (F:=flag false l (wst (pos' t) l v)) (a:=wa) hs.rep.nodup hst
    have hp:p ∈ v:=hpq.subset (by simp)
    have hq:q ∈ v:=hpq.subset (by simp)
    have hne:p ≠ q:=by
      have:=hs.rep.nodup.sublist hpq
      simpa using this
    refine ⟨p.s,q.s,hs.rep.mem.2 ⟨p,hp,rfl⟩,hs.rep.mem.2 ⟨q,hq,rfl⟩,fun e => hne (hs.rep.inj hp hq e),fun e => h1 (hs.rep.inj hp hwa e),
      fun e => h2 (hs.rep.inj hq hwa e),hit_ht X hs hp hq hh⟩
  have he:∀ t',pos' t = true ∨ t = t' → pos' t = true ∨ t' = 0:=by
    intro t' h
    rcases h with h | h
    · exact Or.inl h
    · subst h
      rcases Nat.eq_zero_or_pos t with h | h
      · exact Or.inr h
      · exact Or.inl (by simp [pos',h])
  have kb:∀ d a b S1 k0,k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → ∀ U,S = insert a (insert b U) → S1 = insert (op d a b) U → a ∈ U → b ∉ U → False:=by
    rintro d a b S1 k0 rfl hb hl U rfl rfl ha hbU
    have hab:=hb.1
    have hfS:op d a b ∉ insert a (insert b U):=fun h => hb.fresh hl hm.2 (sub_C _ _ (by simpa using h))
    have hf:op d a b ∉ U:=fun h => hfS (by simp [h])
    have eS:insert a (insert b U) = insert b U:=Finset.insert_eq_of_mem (by simp [ha])
    obtain ⟨x,f,h1,h2,h3⟩:=chrom (N:=NN) (e:=pos' t) hl (hb.min hl hm.2).2 (he t (Or.inr rfl))
    rw [Finset.card_insert_of_notMem hf] at h1
    rw [eS,Finset.card_insert_of_notMem hbU] at hx
    obtain ⟨p,q,hp,hq,hpq,hpa,hqa,hh⟩:=av a (by simp)
    have:=ht_bi hab (Or.inr rfl) hl hp hq (fun e => absurd e hpa) (fun _ => hbU) (fun e => absurd e hqa) (fun _ => hbU) hh
    have m1:=phi_mem (g:=op d a b) hp
    have m2:=phi_mem (g:=op d a b) hq
    have hne:(if p = a ∨ p = b then op d a b else p) ≠ (if q = a ∨ q = b then op d a b else q):=by
      simp only [hpa,hqa,false_or]
      have h1':p = b ∨ p ∈ U:=by simp at hp; tauto
      have h2':q = b ∨ q ∈ U:=by simp at hq; tauto
      split_ifs with r s s
      · exact absurd (r.trans s.symm) hpq
      · intro e; exact hf (e ▸ h2'.resolve_left s)
      · intro e; exact hf (e ▸ h1'.resolve_left r)
      · exact hpq
    have k1:=h3 _ m1 _ m2 hne this
    have c1:=h2 _ m1; have c2:=h2 _ m2
    omega
  constructor
  · intro d a b S1 k0 hk' hb hl
    by_contra hc
    obtain ⟨hab,U,e1,e2,hal⟩:=id hb
    have hfS:op d a b ∉ S:=fun h => hb.fresh hl (by rw [← hk']; exact hm.2) (sub_C _ _ (by simpa using h))
    have hf:op d a b ∉ U:=fun h => hfS (by rw [e1]; simp [h])
    have hs1:=(hb.min hl (by rw [← hk']; exact hm.2)).size.1
    have hcS1:S1.card = U.card + 1:=by rw [e2,Finset.card_insert_of_notMem hf]
    by_cases ha:a ∈ U
    · by_cases hbU:b ∈ U
      · have:S = U:=by rw [e1,Finset.insert_eq_of_mem hbU,Finset.insert_eq_of_mem ha]
        rw [this] at hx; omega
      · exact kb d a b S1 k0 hk' hb hl U e1 e2 ha hbU
    · by_cases hbU:b ∈ U
      · exact kb d b a S1 k0 hk' hb.symm hl U (by rw [e1,Finset.insert_comm]) (by rw [e2,op_comm]) hbU ha
      · have:S.card = U.card + 2:=by
          rw [e1,Finset.card_insert_of_notMem (by simp [hab,ha]),Finset.card_insert_of_notMem hbU]
        omega
  · rintro a S1 k0 t0 rfl rfl hu hl
    by_contra hc
    obtain ⟨U,rfl,rfl⟩:=id hu
    have hf:a ^^^ m ∉ U:=fun h => hu.fresh hl hm.2 (sub_C _ _ (by simp [h]))
    have ha:a ∈ U:=by
      by_contra ha
      rw [Finset.card_insert_of_notMem hf,Finset.card_insert_of_notMem ha] at hc; omega
    have eS:insert a U = U:=Finset.insert_eq_of_mem ha
    obtain ⟨x,f,h1,h2,h3⟩:=chrom (N:=NN) (e:=true) hl (hu.min hl hm.2).2 (Or.inl rfl)
    rw [Finset.card_insert_of_notMem hf] at h1
    rw [eS] at hx
    obtain ⟨p,q,hp,hq,hpq,hpa,hqa,hh⟩:=av a (by simp)
    have hpos:pos' (t0 + 1) = true:=by simp [pos']
    rw [hpos] at hh
    have:=ht_un hp hq (fun e => absurd e hpa) (fun e => absurd e hqa) hh
    simp only [hpa,hqa,if_false] at this
    have m1:p ∈ insert (a ^^^ m) U:=by rw [eS] at hp; simp [hp]
    have m2:q ∈ insert (a ^^^ m) U:=by rw [eS] at hq; simp [hq]
    have k1:=h3 _ m1 _ m2 hpq this
    have c1:=h2 _ m1; have c2:=h2 _ m2
    omega
lemma tst_sound {k k' t z:ℕ} {v:List W} {S:Finset ℕ} (hs:StOk P T l k z v S) (hm:Min R m T k' t S) (hk:k' ≤ k) :
    ∃ y,(∀ F:ℕ → Bool,tst (pos' t) l (k + 1 - t) v F = F y) ∧ (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK R m T k' t S)):=by
  have hsz:=hm.size
  have hcard:=hs.rep.card
  have e:∀ F:ℕ → Bool,tst (pos' t) l (k + 1 - t) v F = bif Nat.beq v.length (k + 1 - t) then (bif rect (pos' t) l (wst (pos' t) l v) v [] then false else F 0) else
      (bif Nat.beq (v.length + 1) (k + 1 - t) then (bif bip l (wst (pos' t) l v) v [] then false else
        (bif flk l (wst (pos' t) l v) v star then F 0 else F 1)) else F 0):=by
    intro F
    change (Bool.rec (motive:=fun _ => Bool)
      (Bool.rec (motive:=fun _ => Bool) (F 0) (Bool.rec (motive:=fun _ => Bool) (Bool.rec (motive:=fun _ => Bool) (F 1) (F 0) (flk l (wst (pos' t) l v) v star)) false
        (bip l (wst (pos' t) l v) v [])) (Nat.beq (v.length + 1) (k + 1 - t)))
      (Bool.rec (motive:=fun _ => Bool) (F 0) false (rect (pos' t) l (wst (pos' t) l v) v [])) (Nat.beq v.length (k + 1 - t)):Bool) = _
    rw [bR,bR,bR,bR,bR]
  cases h1:Nat.beq v.length (k + 1 - t) with
  | true =>
    have h1':=Nat.eq_of_beq_eq_true h1
    have hr:=rect_ok X hs hm hk (by omega)
    exact ⟨0,fun F => by rw [e,h1,hr]; rfl,Or.inl rfl⟩
  | false =>
    cases h2:Nat.beq (v.length + 1) (k + 1 - t) with
    | false => exact ⟨0,fun F => by rw [e,h1,h2]; rfl,Or.inl rfl⟩
    | true =>
      have h2':=Nat.eq_of_beq_eq_true h2
      have hbip:bip l (wst (pos' t) l v) v [] = false:=by
        obtain ⟨x,f,q1,q2,q3⟩:=chrom (N:=NN) (e:=pos' t) hm.1 hm.2 (by
          rcases Nat.eq_zero_or_pos t with h | h
          · exact Or.inr h
          · exact Or.inl (by simp [pos',h]))
        refine bip_aux (col:=f) v [] [] ?_ (by simp) (by simp) ?_
        · intro w hw
          have:=q2 w.s (hs.rep.mem.2 ⟨w,hw,rfl⟩); omega
        · have hnd:v.Pairwise (fun a b => a.s ≠ b.s):=List.pairwise_map.1 hs.rep.1
          refine hnd.imp_of_mem fun {a b} ha hb hab hh => ?_
          exact q3 b.s (hs.rep.mem.2 ⟨b,hb,rfl⟩) a.s (hs.rep.mem.2 ⟨a,ha,rfl⟩) (Ne.symm hab) (hit_ht X hs hb ha hh)
      cases h3:flk l (wst (pos' t) l v) v star with
      | true => exact ⟨0,fun F => by rw [e,h1,h2,hbip,h3]; rfl,Or.inl rfl⟩
      | false => exact ⟨1,fun F => by rw [e,h1,h2,hbip,h3]; rfl,Or.inr ⟨rfl,by omega,nk_ok X hs hm (by omega) h3⟩⟩
lemma cv_ok {t k k' z:ℕ} {v:List W} {S:Finset ℕ} {b:Bool} (hs:StOk P T l k z v S) (hl:Live R m T k' t S)
    (h:cv (pos' t) l v b = false):b = false:=by
  have hcov:Nat.beq (cov (pos' t) l v) l = true:=by
    rw [Nat.beq_eq]
    apply Nat.eq_of_testBit_eq; intro i
    cases hli:l.testBit i with
    | false =>
      by_contra hc
      obtain ⟨w,_,hw⟩:=(cov_bit _ _ _ _).1 (by simpa using hc)
      rw [sp_bit,hli] at hw; simp at hw
    | true =>
      rw [cov_bit]
      obtain ⟨⟨m1,m2,t1,t2⟩,_⟩:=X.lg i hli
      obtain ⟨w,hw,hs1⟩:=hl.cov m1 m2 t1 t2
      obtain ⟨w',hw',rfl⟩:=hs.rep.mem.1 hw
      exact ⟨w',hw',by rw [sp_bit,hli,hs1]; rfl⟩
  simp only [cv,bR,hcov,cond_true] at h
  cases hp:pos' t <;> rw [hp] at h <;> simpa using h
end sound
section sound
variable {P:List ℕ} {l m g T:ℕ} (X:Ctx P l m g T)
include X
lemma gate_sound {f:ℕ → List W → Bool} {d:Bool} {e n z t k k':ℕ} {v:List W} {S S':Finset ℕ} {a c:W} {d':Bool}
    (hs:StOk P T l (k + 1) z v S) (hm:Min R m T (k' + 1) t S) (hk:k' ≤ k) (hd:d = pos' t) (hn:n = v.length)
    (hSe:S'.card ≤ e) (hb:Bi R d' a.s c.s S S') (hl:Live R m T k' t S') (ha:a ∈ v) (hc:c ∈ v)
    (hp:pair (modeF n e (mid f m g e (Nat.pred n) z v)) (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r,f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r,w = opW d' a c ∨ w ∈ v:=by
  subst hd hn
  have hmin:=hb.min hl hm.2
  have hpos:=hl.pos
  have hfr:=hb.fresh hl hm.2
  have hosS:∀ w ∈ v,w.s ≠ (opW d' a c).s:=fun w hw e => hfr (by
    rw [← opW_s,← e]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w,hw,rfl⟩))
  have ho0:(opW d' a c).s ≠ 0:=fun e => hfr (by rw [← opW_s,e]; simp [C])
  have ho1:(opW d' a c).s ≠ m:=fun e => hfr (by rw [← opW_s,e]; simp [C])
  obtain ⟨r0,hr0,hins⟩:=ins_spec (opW d' a c) v hosS
  obtain ⟨s1,s2,s3,s4⟩:=shape_all hosS hr0 hs.rep.1 ha hc hb.1
  have hp:=pair_false hp d'
  generalize hoa:dfc (pos' t) d' l (wst (pos' t) l v) a c = da at hp
  generalize hoc:dfc (pos' t) d' l (wst (pos' t) l v) c a = dc at hp
  have filt:∀ {x y:W},(∀ i,(Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (NN + i) = false else y.s.testBit i = true) →
      dfc (pos' t) d' l (wst (pos' t) l v) x y = 0:=by
    intro x y hu
    unfold dfc
    generalize Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v) = u at *
    cases d'
    · simp only [Bool.cond_false,nl,nx] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have:=hu i
      rw [Nat.testBit_xor,Nat.testBit_and]; cases h1:u.testBit i <;> simp_all
    · simp only [Bool.cond_true,nl,nsr] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have:=hu i
      rw [Nat.testBit_and,Nat.testBit_shiftRight]; cases h1:u.testBit i <;> simp_all
  have fa:a.s ∉ S' → da = 0:=fun h => by
    rw [← hoa]; exact filt fun i hi => drop_ok X hs.rep hb hl ha h hi
  have fc:c.s ∉ S' → dc = 0:=fun h => by
    rw [← hoc]; exact filt fun i hi => drop_ok X hs.rep hb.symm hl hc h hi
  have b0:∀ {q:ℕ},q = 0 → Nat.beq q 0 = true:=fun h => by rw [h]; rfl
  have hput:∀ h,put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v h = h r0:=fun h => by
    rw [put_eq (by cases d' <;> rfl) (by cases d' <;> rfl) ho0 ho1,hins]
  have hv2:2 ≤ v.length:=by
    rw [← hs.rep.card]
    have:({a.s,c.s}:Finset ℕ) ⊆ S:=by
      intro x hx; simp at hx; rcases hx with rfl | rfl; exacts [hb.sub.1,hb.sub.2.1]
    have h2:=Finset.card_le_card this
    rwa [Finset.card_pair hb.1] at h2
  have hpr:Nat.pred v.length + 1 = v.length:=by simp [Nat.pred_eq_sub_one]; omega
  have main:∀ {ka kc:Bool} {r:List W},ka = decide (a.s ∈ S') → kc = decide (c.s ∈ S') → Shape (opW d' a c) a c v ka kc r →
      r.length = S'.card ∧ StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
      ∀ w ∈ r,w = opW d' a c ∨ w ∈ v:=by
    intro ka kc r h1 h2 h3
    have:=(bi_st X hs hm hk hb hl ha hc h1 h2 h3).1
    exact ⟨this.rep.card.symm,this,fun w hw => h3.mem hw⟩
  have hguard:Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true:=by
    by_cases q1:a.s ∈ S' <;> by_cases q2:c.s ∈ S'
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s4).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s2).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s3).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s1).2
  have fin:∀ {z':ℕ} {r:List W} {mk:(List W → Bool) → Bool},(∀ h,mk h = h r) → StOk P T l k z' r S' → (∀ w ∈ r,w = opW d' a c ∨ w ∈ v) →
      child f g mk z' = false → ∃ z' r,f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r,w = opW d' a c ∨ w ∈ v :=
    fun {z' r mk} h1 h2 h3 h4 => ⟨z',r,child_sound X h1 h2 hmin hk h4,h2,h3⟩
  by_cases q1:a.s ∈ S' <;> by_cases q2:c.s ∈ S'
  · obtain ⟨c1,c3,c4⟩:=main (by simp [q1]) (by simp [q2]) s4
    have hlen:=s4.len; simp at hlen
    have hmid:=mid_false (modeF_false hp (fun h => by omega) (fun h => by omega)) hguard
    exact fin hput c3 c4 ((kids_false hmid).2.2.2 (by omega))
  · obtain ⟨c1,c3,c4⟩:=main (by simp [q1]) (by simp [q2]) s2
    have hlen:=s2.len; simp only [Bool.cond_true,Bool.cond_false] at hlen
    have hmid:=mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inr (fc q2))) hguard
    exact fin (fun h => by rw [hput,rm_eq]) (by simpa using c3) c4 ((kids_false hmid).2.1 (b0 (fc q2)) (by omega))
  · obtain ⟨c1,c3,c4⟩:=main (by simp [q1]) (by simp [q2]) s3
    have hlen:=s3.len; simp only [Bool.cond_true,Bool.cond_false] at hlen
    have hmid:=mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput,rm_eq]) (by simpa using c3) c4 ((kids_false hmid).2.2.1 (b0 (fa q1)) (by omega))
  · obtain ⟨c1,c3,c4⟩:=main (by simp [q1]) (by simp [q2]) s1
    have hlen:=s1.len; simp only [Bool.cond_false] at hlen
    have hmid:=mid_false (modeF_false hp (fun h => ⟨fa q1,fc q2⟩) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput,rm_eq]) (by simpa using c3) c4 ((kids_false hmid).1 (b0 (fa q1)) (b0 (fc q2)))
end sound
def notW (m:ℕ) (a:W):W:=⟨a.s ^^^ m,a.b,a.a,a.c,0⟩
section sound
variable {P:List ℕ} {l m g T:ℕ} (X:Ctx P l m g T)
include X
lemma un_st {k k' t z:ℕ} {v r:List W} {S S':Finset ℕ} {a:W} {ka:Bool}
    (hs:StOk P T l (k + 1) z v S) (hm:Min R m T (k' + 1) (t + 1) S) (hk:k' ≤ k) (hb:Un m a.s S S')
    (hl:Live R m T k' t S') (ha:a ∈ v) (hka:ka = decide (a.s ∈ S'))
    (hsh:bif ka then r.Perm (notW m a :: v) else (a :: r).Perm (notW m a :: v)) :
    StOk P T l k (z - a.c - (bif ka then a.c else 0)) r S':=by
  obtain ⟨b,hb15,hcl,hz⟩:=hs.bud
  have hle:=cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hfr:=hb.fresh hl hm.2
  have hfS:a.s ^^^ m ∉ S:=fun h => hfr (sub_C _ _ (by simpa using h))
  have wa:=hs.wok a ha
  have haS:a.s ∈ S:=hb.sub.1
  have wo:WOk P (notW m a):=by
    refine ⟨wa.pb,wa.pa,by rw [Nat.or_comm]; exact wa.ec,fun j hj h => ?_,fun j hj h => ?_⟩
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1,wa.cb j hj h]; simp
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1,wa.ca j hj h]; simp
  have hov:((notW m a :: v).map W.s).Nodup:=by
    simp only [List.map_cons,List.nodup_cons]
    refine ⟨fun hm => hfS ?_,hs.rep.1⟩
    rw [← hs.rep.2]; simpa [notW] using hm
  have hov2:∀ x,x ∈ (notW m a :: v).map W.s ↔ x = a.s ^^^ m ∨ x ∈ S:=fun x => by
    rw [← hs.rep.2]; simp [notW]
  have hS':∀ x,x ∈ S' ↔ x = a.s ^^^ m ∨ (x ∈ S ∧ (x = a.s → ka = true)):=by
    intro x
    obtain ⟨U,e1,e2⟩:=hb
    rw [e2,Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h],?_⟩
        rintro rfl; rw [hka,e2]; simp [h]
    · rintro (h | ⟨h,f1⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h
        · have:=f1 h; rw [hka,decide_eq_true_eq,e2,Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hne:a.s ≠ a.s ^^^ m:=fun e => hfS (e ▸ haS)
  have hrep:Rep r S':=by
    cases hkk:ka with
    | true =>
      rw [hkk] at hsh hS'
      have hn:=(hsh.map W.s).nodup_iff.2 hov
      refine ⟨hn,Finset.ext fun x => ?_⟩
      rw [List.mem_toFinset,(hsh.map W.s).mem_iff,hov2,hS']; simp
    | false =>
      rw [hkk] at hsh hS'
      have hn:=(hsh.map W.s).nodup_iff.2 hov
      simp only [List.map_cons,List.nodup_cons] at hn
      refine ⟨hn.2,Finset.ext fun x => ?_⟩
      have hx:=(hsh.map W.s).mem_iff (a:=x)
      rw [hov2] at hx; simp only [List.map_cons,List.mem_cons] at hx
      rw [List.mem_toFinset,hS']
      constructor
      · intro h1
        rcases hx.1 (Or.inr h1) with e | e
        · exact Or.inl e
        · exact Or.inr ⟨e,fun e => absurd (e ▸ h1) hn.1⟩
      · rintro (e | ⟨e,f1⟩)
        · exact (hx.2 (Or.inl e)).resolve_left fun e' => hne (e'.symm.trans e)
        · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  have hmem:∀ w ∈ r,w = notW m a ∨ w ∈ v:=by
    intro w hw
    have:w ∈ notW m a :: v:=by
      cases hkk:ka <;> rw [hkk] at hsh
      · exact List.Perm.subset hsh (by simp [hw])
      · exact List.Perm.subset hsh hw
    simpa using this
  have hcnt:∀ j,cnt r j + (bif ka then 0 else fl a j) = fl a j + cnt v j:=by
    intro j
    have ef:fl (notW m a) j = fl a j:=rfl
    cases hkk:ka <;> rw [hkk] at hsh
    · have:=cnt_perm hsh j; simp only [cnt_cons,ef] at this; simp; omega
    · have:=cnt_perm hsh j; simp only [cnt_cons,ef] at this; simp; omega
  have hwok:∀ w ∈ r,WOk P w:=fun w hw => (hmem w hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood:∀ w ∈ r,Good l w.s:=fun w hw => by
    rcases hmem w hw with rfl | h
    · have hg:=hs.good a ha
      refine ⟨fun i j h h1 h2 => ?_,fun i j h h1 h2 => ?_⟩
      · change (a.s ^^^ m).testBit i = (a.s ^^^ m).testBit j
        rw [Nat.testBit_xor,Nat.testBit_xor,hg.1 i j h h1 h2,(X.lg i h1).1.1,(X.lg j h2).1.1]
      · change (a.s ^^^ m).testBit (NN + i) = (a.s ^^^ m).testBit (NN + j)
        rw [Nat.testBit_xor,Nat.testBit_xor,hg.2 i j h h1 h2,(X.lg i h1).1.2.1,(X.lg j h2).1.2.1]
    · exact hs.good w h
  let b':ℕ → ℕ:=fun j => b j - fl a j
  have hcl':Cl P T k b' S':=by
    intro j hj q hq hsol
    have hl1:=hle j hj
    have h2:=cnt_one ha hs.rep.1 j
    simp only [b'] at hq
    by_cases hkill:a.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (X.hP j hj).1 (wa.cst hj hkill) hsol)
      have:fl a j = 1:=by simp [fl,hkill]
      omega
    · refine hcl j hj (q + 1) ?_ (hb.im (X.hP j hj).1 hsol)
      have e1:fl a j = 0:=by simp [fl,hkill]
      omega
  have hle':=cnt_le X hrep hwok hcl' (hb.min hl hm.2) hk
  refine ⟨hrep,hwok,hgood,b',fun j hj => ?_,hcl',?_⟩
  · have:=hb15 j hj; simp only [b']; omega
  · have ea:(bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0):=by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have le1:∀ j,(bif ka then fl a j else 0) ≤ 1:=fun j => by cases ka <;> simp [fl_le]
    rw [ea,hz]
    conv_lhs => rw [fl_pk wa]
    rw [pk_sub,pk_sub]
    · refine pk_congr fun j hj => ?_
      have q1:=hle j hj; have q2:=hle' j hj; have q3:=cnt_one ha hs.rep.1 j; have q4:=hb15 j hj
      have q5:=hcnt j; have q6:=fl_le a j
      simp only [b'] at q2 ⊢
      cases ka <;> simp at q5 ⊢ <;> omega
    · intro j hj; have:=hle j hj; have:=le1 j; have:=fl_le a j; omega
    · intro j hj; have:=hle j hj; have:=fl_le a j; omega
end sound
lemma nots_false {f:ℕ → ℕ → List W → Bool} {m g e n z q:ℕ} {v r:List W} (h:nots f m g e n z q v r = false)
    {a:W} (ha:a ∈ r) (hq:a.s + 1 ≠ q):ins (notW m a) v (fun v =>
      (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
      (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) = false:=by
  induction r with
  | nil => simp at ha
  | cons w r ih =>
    change (Bool.rec (motive:=fun _ => Bool) (nots f m g e n z q v r) true (Bool.rec (motive:=fun _ => Bool)
      (st (Nat.xor w.s m) (fun s => st (Nat.sub z w.c) (fun z => ins ⟨s,w.b,w.a,w.c,0⟩ v (fun v =>
        Bool.rec (motive:=fun _ => Bool) (Bool.rec (motive:=fun _ => Bool) false
          (child (f s) g (fun h => h v) (Nat.sub z w.c)) (Nat.ble (Nat.succ n) e)) true
          (Bool.rec (motive:=fun _ => Bool) false (child (f s) g (rm w.s w.s v) z) (Nat.ble n e)))))) false (Nat.beq (Nat.succ w.s) q)):Bool) = false at h
    rw [bR,bR] at h
    simp only [st_eq,bR] at h
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [Bool.eq_false_iff.2 fun h => hq (Nat.eq_of_beq_eq_true h),Bool.cond_false] at h
      cases hh:ins (notW m a) v (fun v =>
        (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
        (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) with
      | false => rfl
      | true =>
        have h:(bif ins (notW m a) v (fun v =>
          (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
          (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) then true
          else nots f m g e n z q v r) = false:=h
        rw [hh] at h; simp at h
    · refine ih ?_ ha
      revert h
      cases nots f m g e n z q v r <;> simp
section sound
variable {P:List ℕ} {l m g T:ℕ} (X:Ctx P l m g T)
include X
lemma nots_sound {f:ℕ → ℕ → List W → Bool} {e n z q t k k':ℕ} {v:List W} {S S':Finset ℕ} {a:W}
    (hs:StOk P T l (k + 1) z v S) (hm:Min R m T (k' + 1) (t + 1) S) (hk:k' ≤ k) (hn:n = v.length)
    (hSe:S'.card ≤ e) (hb:Un m a.s S S') (hl:Live R m T k' t S') (ha:a ∈ v) (hq:a.s + 1 ≠ q) {rr:List W} (har':a ∈ rr)
    (hp:nots f m g e n z q v rr = false):∃ z' r,f (a.s ^^^ m) z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r,w = notW m a ∨ w ∈ v:=by
  subst hn
  have hmin:=hb.min hl hm.2
  have hfr:=hb.fresh hl hm.2
  have hosS:∀ w ∈ v,w.s ≠ (notW m a).s:=fun w hw e => hfr (by
    change a.s ^^^ m ∈ _
    have:w.s = a.s ^^^ m:=e
    rw [← this]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w,hw,rfl⟩))
  obtain ⟨r0,hr0,hins⟩:=ins_spec (notW m a) v hosS
  have h:=nots_false hp har' hq
  rw [hins] at h
  have hl0:r0.length = v.length + 1:=by rw [hr0.length_eq]; simp
  have hnd:(r0.map W.s).Nodup:=by
    refine (hr0.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons,List.nodup_cons,List.mem_map,not_exists,not_and]
    exact ⟨fun w hw => hosS w hw,hs.rep.1⟩
  have har:a ∈ r0:=hr0.symm.subset (by simp [ha])
  have hmem:∀ w ∈ r0,w = notW m a ∨ w ∈ v:=fun w hw => by simpa using hr0.subset hw
  by_cases q1:a.s ∈ S'
  · have hst:=un_st X hs hm hk hb hl ha (ka:=true) (by simp [q1]) hr0
    have hc:=hst.rep.card
    have hb1:Nat.ble (v.length + 1) e = true:=Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h:child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c - a.c) = false:=by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c - a.c) <;> simp
    exact ⟨_,_,child_sound X (fun h => rfl) hst hmin hk h,hst,hmem⟩
  · have hperm:(a :: r0.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))).Perm (notW m a :: v):=by
      rw [filter1]; exact (filter_perm hnd har).trans hr0
    have hst:=un_st X hs hm hk hb hl ha (ka:=false) (by simp [q1]) hperm
    simp only [Bool.cond_false,Nat.sub_zero] at hst
    have hc:=hst.rep.card
    have hlen:=hperm.length_eq
    simp only [List.length_cons] at hlen
    have hb1:Nat.ble v.length e = true:=Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h:child (f (a.s ^^^ m)) g (rm a.s a.s r0) (z - a.c) = false:=by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (rm a.s a.s r0) (z - a.c) <;> simp
    exact ⟨_,_,child_sound X (rm_eq _ _ _) hst hmin hk h,hst,fun w hw => hmem w (List.mem_of_mem_filter hw)⟩
end sound
lemma scan_false {p:X → Bool} {xs:List X} (h:scan p xs = false):∀ c ∈ xs,p c = false:=by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive:=fun _ => Bool) (scan p r) true (p a):Bool) = false at h
    rw [bR] at h
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · revert h; cases p c <;> simp
    · refine ih ?_ c hc
      revert h; cases scan p r <;> simp
lemma pairs_false {h:X → X → Bool} {xs:List X} (hp:pairs h xs = false):xs.Pairwise (fun a c => h a c = false):=by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive:=fun _ => Bool) (pairs h r) true (scan (h a) r):Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · apply scan_false; revert hp; cases scan (h a) r <;> simp
    · apply ih; revert hp; cases pairs h r <;> simp
lemma beq_f {x y:ℕ} (h:x ≠ y):Nat.beq x y = false:=Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
lemma pairsP_false {h:X → X → Bool} {xs:List X} {q:ℕ} {a c:X} (hp:pairsP q h xs = false) (ha:a ∈ xs) (hq:a.s = q)
    (hc:c ∈ xs) (hcq:c.s ≠ q):h a c = false:=by
  have h1:=scan_false hp a ha
  simp only [bR] at h1
  rw [hq,Nat.beq_refl,Bool.cond_true] at h1
  have h2:=scan_false h1 c hc
  beta_reduce at h2
  rwa [beq_f hcq,Bool.cond_false] at h2
lemma pairsQ_false {h:X → X → Bool} {xs:List X} {q q':ℕ} {a c:X} (hp:pairsQ q q' h xs = false) (ha:a ∈ xs) (hq:a.s = q)
    (hc:c ∈ xs) (hcq:c.s = q'):h a c = false:=by
  have h1:=scan_false hp a ha
  simp only [bR] at h1
  rw [hq,Nat.beq_refl,Bool.cond_true] at h1
  have h2:=scan_false h1 c hc
  beta_reduce at h2
  rwa [hcq,Nat.beq_refl,Bool.cond_true] at h2
lemma pos_eq (t:ℕ):pos t = pos' t:=by cases t <;> simp [pos,pos']
lemma fr_mem {xs:List X} {a:X} (ha:a ∈ xs) (h:a.w.r = 0):a ∈ fr xs:=by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive:=fun _ => List X) (fr xs) (x :: fr xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [h]; simp
    · cases Nat.beq x.w.r 0
      · exact ih ha
      · exact List.mem_cons_of_mem _ (ih ha)
lemma fs_mem {xs:List X} {a:X} (ha:a ∈ xs) (h:a.w.r ≠ 0):a ∈ fs xs:=by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive:=fun _ => List X) (x :: fs xs) (fs xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [beq_f h]; simp
    · cases Nat.beq x.w.r 0
      · exact List.mem_cons_of_mem _ (ih ha)
      · exact ih ha
lemma pairs_any {h:X → X → Bool} {xs:List X} (hp:pairs h xs = false) {a c:X} (ha:a ∈ xs) (hc:c ∈ xs) (hne:a ≠ c) :
    h a c = false ∨ h c a = false:=by
  have hpw:=pairs_false hp
  have:Std.Symm (fun a c:L_meta_10760.X => h a c = false ∨ h c a = false):=⟨fun a b h => h.symm⟩
  exact (hpw.imp (S:=fun a c => h a c = false ∨ h c a = false) fun h => Or.inl h).forall ha hc hne
lemma pairsN_false {h:X → X → Bool} {xs:List X} (hp:pairsN h xs = false) {a c:X} (ha:a ∈ xs) (hc:c ∈ xs) (hne:a ≠ c)
    (hr:a.w.r = 0 ∨ c.w.r = 0):h a c = false ∨ h c a = false:=by
  simp only [pairsN,bR] at hp
  cases h1:pairs h (fr xs) with
  | true => rw [h1] at hp; simp at hp
  | false =>
    rw [h1,cond_false] at hp
    by_cases hra:a.w.r = 0
    · by_cases hrc:c.w.r = 0
      · exact pairs_any h1 (fr_mem ha hra) (fr_mem hc hrc) hne
      · exact Or.inl (scan_false (scan_false hp a (fr_mem ha hra)) c (fs_mem hc hrc))
    · have hrc:=hr.resolve_left hra
      exact Or.inr (scan_false (scan_false hp c (fr_mem hc hrc)) a (fs_mem ha hra))
def Cod (R:ℕ → ℕ) (v:List W):Prop:=∀ w ∈ v,w.r = 0 ∨ w.r = R w.s
def RR (R:ℕ → ℕ):Prop:=∀ d a b,R a ≠ 0 → R b ≠ 0 → ¬ Al R d a b
lemma opW_r (d:Bool) (a c:W):(opW d a c).r = 0:=by cases d <;> rfl
lemma mv_false (F:ℕ → ℕ → ℕ → List W → Bool) (l m g k t z:ℕ) (v:List W) (y:ℕ) (h:mv F l m g k t z v y = false) :
    node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN = false ∧
    ∀ s,t = s + 1 → nots (fun q z v => cv (pos' s) l v (tst (pos' s) l (k - s) v (fun y =>
      bif node (F (k - 2) s) (pos' s) l m g (k - 1 - s - y) v.length z v (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => cv (pos' s) l v (tst (pos' s) l (k - 1 - s) v (fun y =>
        node (F (k - 3) s) (pos' s) l m g (k - 2 - s - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s - y) v.length z (q + 1) v v)))) m g (k - s - y) v.length z 0 v v = false:=by
  change (Bool.rec (motive:=fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (k - s) v (fun y =>
      (Bool.rec (motive:=fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (k - 1 - s) v (fun y =>
        node (F (k - 3) s) (pos s) l m g (k - 2 - s - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s - y) v.length z (q + 1) v v)) true
        (node (F (k - 2) s) (pos s) l m g (k - 1 - s - y) v.length z v (pairsP q)):Bool)))) m g (k - s - y) v.length z 0 v v)) true
      (node (F (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsN):Bool) = false at h
  simp only [bR,pos_eq] at h
  cases h1:node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN with
  | true => rw [h1] at h; simp at h
  | false =>
    rw [h1,Bool.cond_false] at h
    refine ⟨rfl,?_⟩
    rintro s rfl
    exact h
lemma NK.sizeB {m T k k' t:ℕ} {S S1:Finset ℕ} {d:Bool} {a b n y:ℕ} (hn:S.card = n) (hm:Min R m T (k' + 1) t S) (hk:k' + 1 ≤ k)
    (hb:Bi R d a b S S1) (hl:Live R m T k' t S1) (hy:y = 0 ∨ (y = 1 ∧ n + t = k ∧ NK R m T (k' + 1) t S)):S1.card ≤ k - t - y:=by
  have hs:=(hb.min hl hm.2).size.1
  rcases hy with rfl | ⟨rfl,h1,h2⟩
  · omega
  · have:=h2.1 d a b S1 k' rfl hb hl; omega
lemma NK.sizeU {m T k k' t:ℕ} {S S1:Finset ℕ} {a n y:ℕ} (hn:S.card = n) (hm:Min R m T (k' + 1) (t + 1) S) (hk:k' + 1 ≤ k)
    (hb:Un m a S S1) (hl:Live R m T k' t S1) (hy:y = 0 ∨ (y = 1 ∧ n + (t + 1) = k ∧ NK R m T (k' + 1) (t + 1) S)):S1.card ≤ k - t - y:=by
  have hs:=(hb.min hl hm.2).size.1
  rcases hy with rfl | ⟨rfl,h1,h2⟩
  · omega
  · have:=h2.2 a S1 k' t rfl rfl hb hl; omega
section sound
variable {P:List ℕ} {l m g T:ℕ} (X:Ctx P l m g T)
include X
lemma node_bi {f:ℕ → List W → Bool} {d:Bool} {e n z t k k':ℕ} {v:List W} {S S':Finset ℕ} {x y:ℕ} {d':Bool}
    {go:(L_meta_10760.X → L_meta_10760.X → Bool) → List L_meta_10760.X → Bool}
    (hs:StOk P T l (k + 1) z v S) (hm:Min R m T (k' + 1) t S) (hk:k' ≤ k) (hd:d = pos' t) (hn:n = v.length)
    (hSe:S'.card ≤ e) (hb:Bi R d' x y S S') (hl:Live R m T k' t S')
    (hgo:∀ h xs,go h xs = false → ∀ a c:W,a ∈ v → c ∈ v → a.s = x → c.s = y → xs = v.map (mkx d l (wst d l v)) →
      h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false ∨ h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false)
    (hp:node f d l m g e n z v go = false):∃ z' r,f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r,(w.s = op d' x y ∧ w.r = 0) ∨ w ∈ v:=by
  rw [node_eq] at hp
  obtain ⟨a,ha,rfl⟩:=hs.rep.mem.1 hb.sub.1
  obtain ⟨c,hc,rfl⟩:=hs.rep.mem.1 hb.sub.2.1
  rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
  · obtain ⟨z',r,h1,h2,h3⟩:=gate_sound X hs hm hk hd hn hSe hb hl ha hc h
    exact ⟨z',r,h1,h2,fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e,opW_s],by rw [e,opW_r]⟩) id⟩
  · obtain ⟨z',r,h1,h2,h3⟩:=gate_sound X hs hm hk hd hn hSe hb.symm hl hc ha h
    exact ⟨z',r,h1,h2,fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e,opW_s,op_comm],by rw [e,opW_r]⟩) id⟩
lemma mv_sound (hR:RR R) {F:ℕ → ℕ → ℕ → List W → Bool}
    (hF:∀ (k t z:ℕ) (v:List W) (S:Finset ℕ),F k t z v = false → StOk P T l k z v S → Cod R v → ∀ k' ≤ k,¬ Min R m T k' t S)
    {k t z y:ℕ} {v:List W} {S:Finset ℕ} (hs:StOk P T l k z v S) (hcod:Cod R v) (hlen:2 ≤ v.length)
    (h:mv F l m g k t z v y = false):∀ k' ≤ k,Min R m T k' t S → (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK R m T k' t S)) → False:=by
  intro k' hk hm hy
  obtain ⟨hA,hN⟩:=mv_false F l m g k t z v y h
  have hcard:=hs.rep.card
  have codB:∀ {v r:List W} {o:ℕ},Cod R v → (∀ w ∈ r,(w.s = o ∧ w.r = 0) ∨ w ∈ v) → Cod R r:=by
    intro v r o hv hr w hw
    rcases hr w hw with ⟨_,h⟩ | h
    · exact Or.inl h
    · exact hv w h
  have codU:∀ {v r:List W} {a:W},Cod R v → (∀ w ∈ r,w = notW m a ∨ w ∈ v) → Cod R r:=by
    intro v r o hv hr w hw
    rcases hr w hw with h | h
    · exact Or.inl (by rw [h]; rfl)
    · exact hv w h
  rcases first_move k' t S hm (by omega) with
    ⟨k0,d,a,b,S1,rfl,hb,hl⟩ | ⟨k0,t0,a,d,c,S1,S2,rfl,rfl,hu,hb,hl⟩ |
    ⟨k0,t0,a,a',d,S1,S2,S3,rfl,rfl,hu,hne,hu',hb,hl⟩
  · obtain ⟨k,rfl⟩:∃ j,k = j + 1:=⟨k - 1,by omega⟩
    obtain ⟨z',r,hf,hst,hmem⟩:=node_bi X hs hm (by omega) rfl rfl (NK.sizeB hcard hm hk hb hl hy) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      refine pairsN_false hp (List.mem_map_of_mem ha) (List.mem_map_of_mem hc) ?_ ?_
      · intro e
        have:a.s = c.s:=congrArg L_meta_10760.X.s e
        exact hb.1 (by rw [← hax,← hcy,this])
      · by_contra hc'
        push Not at hc'
        obtain ⟨_,U,_,_,hal⟩:=hb
        have h1:a.r = R a.s:=(hcod a ha).resolve_left hc'.1
        have h2:c.r = R c.s:=(hcod c hc).resolve_left hc'.2
        have g1:a.r ≠ 0:=hc'.1
        have g2:c.r ≠ 0:=hc'.2
        rw [← hax,← hcy] at hal
        exact hR _ _ _ (by rw [← h1]; exact g1) (by rw [← h2]; exact g2) hal) hA
    exact hF _ _ _ _ _ hf hst (codB hcod hmem) k0 (by simpa using hk) (hb.min hl hm.2)
  · obtain ⟨k,rfl⟩:∃ j,k = j + 2:=⟨k - 2,by omega⟩
    have hl1:=hb.live hl
    obtain ⟨wa,hwa,rfl⟩:=hs.rep.mem.1 hu.sub.1
    have h2:=hN t0 rfl
    obtain ⟨z1,r1,hf1,hst1,hmem1⟩:=nots_sound X (k:=k + 1) hs hm (by omega) rfl (NK.sizeU hcard hm hk hu hl1 hy) hu hl1 hwa (by omega) hwa h2
    have hm1:=hu.min hl1 hm.2
    have hf1:=cv_ok X hst1 hl1 hf1
    obtain ⟨y1,hF1,hy1⟩:=tst_sound X hst1 hm1 (by omega)
    have hf1:=(hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    rw [Bool.not_eq_true] at hf2
    obtain ⟨z',r,hf,hst,hmem⟩:=node_bi X hst1 hm1 (by omega) rfl rfl (NK.sizeB hst1.rep.card hm1 (by omega) hb hl hy1) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsP_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) (fun e => hb.1 (by rw [← hcy,← e]; rfl)))) hf2
    exact hF _ _ _ _ _ hf hst (codB (codU hcod hmem1) hmem) k0 (by simpa using hk) (hb.min hl hm1.2)
  · obtain ⟨k,rfl⟩:∃ j,k = j + 3:=⟨k - 3,by omega⟩
    have hl1:=hb.live hl
    have hl2:=hu'.live hl1
    obtain ⟨wa,hwa,rfl⟩:=hs.rep.mem.1 hu.sub.1
    have h2:=hN (t0 + 1) rfl
    obtain ⟨z1,r1,hf1,hst1,hmem1⟩:=nots_sound X (k:=k + 2) hs hm (by omega) rfl (NK.sizeU hcard hm hk hu hl2 hy) hu hl2 hwa (by omega) hwa h2
    have hm1:=hu.min hl2 hm.2
    have hf1:=cv_ok X hst1 hl2 hf1
    obtain ⟨y1,hF1,hy1⟩:=tst_sound X hst1 hm1 (by omega)
    have hf1:=(hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    obtain ⟨wa',hwa',rfl⟩:=hst1.rep.mem.1 hu'.sub.1
    obtain ⟨z2,r2,hf3,hst2,hmem2⟩:=nots_sound X (k:=k + 1) hst1 hm1 (by omega) rfl (NK.sizeU hst1.rep.card hm1 (by omega) hu' hl1 hy1) hu' hl1 hwa' (by omega) hwa' hf1
    have hm2:=hu'.min hl1 hm1.2
    have hf3:=cv_ok X hst2 hl1 hf3
    obtain ⟨y2,hF3,hy2⟩:=tst_sound X hst2 hm2 (by omega)
    have hf3:=(hF3 _).symm.trans hf3
    beta_reduce at hf3
    obtain ⟨z',r,hf,hst,hmem⟩:=node_bi X hst2 hm2 (by omega) rfl rfl (NK.sizeB hst2.rep.card hm2 (by omega) hb hl hy2) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsQ_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) hcy)) hf3
    exact hF _ _ _ _ _ hf hst (codB (codU (codU hcod hmem1) hmem2) hmem) k0 (by simpa using hk) (hb.min hl hm2.2)
theorem look_sound (hR:RR R):∀ (fuel k t z:ℕ) (v:List W) (S:Finset ℕ),look l m g fuel k t z v = false → StOk P T l k z v S → Cod R v →
    ∀ k' ≤ k,¬ Min R m T k' t S:=by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hm
    change (Bool.rec (motive:=fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => mv (look l m g fuel) l m g k t z v y)) true (Nat.ble v.length 1):Bool) = false at h
    rw [bR,pos_eq] at h
    cases h0:Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0,cond_false] at h
      have hlen:2 ≤ v.length:=by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      obtain ⟨y,hFy,hyk⟩:=tst_sound X hs hm hk
      have hy:=(hFy _).symm.trans h
      beta_reduce at hy
      exact mv_sound X hR ih hs hcod hlen hy k' hk hm hyk
end sound
lemma Live.W {m T k t:ℕ} {S:Finset ℕ} {Q:Set ℕ} (hl:Live R m T k t S) (hQ:(S:Set ℕ) ⊆ Q):Sol Z0 m T k Q:=hl.sol.mono le_rfl hQ
lemma front {m T:ℕ} (hR:∀ d a b,(R a = 0 ∨ R b = 0) → Al R d a b) {k t:ℕ} {S:Finset ℕ} (hl:Live Z0 m T k t S)
    (hm:∀ q < k,¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S:Set ℕ)))) :
    Live R m T k t S ∨ ∃ k0 d a b S1,k = k0 + 1 ∧ R a ≠ 0 ∧ R b ≠ 0 ∧ Bi Z0 d a b S S1 ∧ Live Z0 m T k0 t S1:=by
  induction hl with
  | stop => exact Or.inl .stop
  | @un k t a U hl ih =>
    set Q:Set ℕ:={x | R x ≠ 0} with hQ
    have hfr:a ^^^ m ∉ C m (Q ∪ ((insert a U:Finset ℕ):Set ℕ)):=by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert,Set.mem_insert_iff,Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU:a ^^^ m ∉ U:=fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR:R (a ^^^ m) = 0:=by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm':∀ q < k,¬ Sol Z0 m T q (C m (Q ∪ ((insert (a ^^^ m) U:Finset ℕ):Set ℕ))):=by
      intro q hq hs
      refine hm (q + 1) (by omega) (.un (a:=a) (Or.inl (Or.inr (by simp))) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert,Set.mem_insert_iff,Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0,d,x,y,S1,rfl,hx,hy,⟨hxy,V,e1,rfl,hal⟩,hl1⟩
    · exact Or.inl (.un h)
    · have nx:x ≠ a ^^^ m:=fun e => hx (e ▸ hfR)
      have ny:y ≠ a ^^^ m:=fun e => hy (e ▸ hfR)
      have hmV:a ^^^ m ∈ V:=by
        have:a ^^^ m ∈ insert x (insert y V):=by rw [← e1]; simp
        simp at this
        rcases this with h | h | h
        · exact absurd h.symm nx
        · exact absurd h.symm ny
        · exact h
      have eU:U = insert x (insert y (V.erase (a ^^^ m))):=by
        ext z
        by_cases hz:z = a ^^^ m
        · subst hz
          simp [hfU,Ne.symm nx,Ne.symm ny]
        · have:z ∈ insert (a ^^^ m) U ↔ z ∈ insert x (insert y V):=by rw [e1]
          simp only [Finset.mem_insert,hz,false_or,Finset.mem_erase,ne_eq,not_false_eq_true,true_and] at this ⊢
          exact this
      refine Or.inr ⟨k0 + 1,d,x,y,insert a (insert (op d x y) (V.erase (a ^^^ m))),rfl,hx,hy,
        ⟨hxy,insert a (V.erase (a ^^^ m)),?_,?_,hal⟩,?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]; tauto
      · ext z; simp only [Finset.mem_insert]; tauto
      · refine .un ?_
        have:insert (a ^^^ m) (insert (op d x y) (V.erase (a ^^^ m))) = insert (op d x y) V:=by
          rw [Finset.insert_comm,Finset.insert_erase hmV]
        rw [this]; exact hl1
  | @bi k t d0 a b U hab hal0 hl ih =>
    set Q:Set ℕ:={x | R x ≠ 0} with hQ
    have hb0:Bi Z0 d0 a b (insert a (insert b U)) (insert (op d0 a b) U):=⟨hab,U,rfl,rfl,hal0⟩
    by_cases hW:R a ≠ 0 ∧ R b ≠ 0
    · exact Or.inr ⟨k,d0,a,b,_,rfl,hW.1,hW.2,hb0,hl⟩
    have hal:Al R d0 a b:=hR _ _ _ (by
      by_contra hc; push Not at hc; exact hW hc)
    have hfr:op d0 a b ∉ C m (Q ∪ ((insert a (insert b U):Finset ℕ):Set ℕ)):=by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert,Set.mem_insert_iff,Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU:op d0 a b ∉ U:=fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfa:op d0 a b ≠ a:=fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfb:op d0 a b ≠ b:=fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR:R (op d0 a b) = 0:=by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm':∀ q < k,¬ Sol Z0 m T q (C m (Q ∪ ((insert (op d0 a b) U:Finset ℕ):Set ℕ))):=by
      intro q hq hs
      refine hm (q + 1) (by omega) (.bi (d:=d0) (a:=a) (b:=b) (Or.inl (Or.inr (by simp))) (Or.inl (Or.inr (by simp))) (al0 _ _ _) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert,Set.mem_insert_iff,Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0,d,x,y,S1,rfl,hx,hy,⟨hxy,V,e1,rfl,hal'⟩,hl1⟩
    · exact Or.inl (.bi hab hal h)
    · set o:=op d0 a b with ho
      have nx:x ≠ o:=fun e => hx (e ▸ hfR)
      have ny:y ≠ o:=fun e => hy (e ▸ hfR)
      have hmV:o ∈ V:=by
        have:o ∈ insert x (insert y V):=by rw [← e1]; simp
        simp at this
        rcases this with h | h | h
        · exact absurd h.symm nx
        · exact absurd h.symm ny
        · exact h
      have eU:U = insert x (insert y (V.erase o)):=by
        ext z
        by_cases hz:z = o
        · subst hz
          simp [hfU,Ne.symm nx,Ne.symm ny]
        · have:z ∈ insert o U ↔ z ∈ insert x (insert y V):=by rw [e1]
          simp only [Finset.mem_insert,hz,false_or,Finset.mem_erase,ne_eq,not_false_eq_true,true_and] at this ⊢
          exact this
      refine Or.inr ⟨k0 + 1,d,x,y,insert a (insert b (insert (op d x y) (V.erase o))),rfl,hx,hy,
        ⟨hxy,insert a (insert b (V.erase o)),?_,?_,hal'⟩,?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h | h) <;> simp only [h,true_or,or_true])
      · ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h) <;> simp only [h,true_or,or_true])
      · refine .bi hab hal0 ?_
        have:insert (op d0 a b) (insert (op d x y) (V.erase o)) = insert (op d x y) V:=by
          rw [Finset.insert_comm,← ho,Finset.insert_erase hmV]
        rw [this]; exact hl1
lemma Min.Z {m T k t:ℕ} {S:Finset ℕ} (h:Min R m T k t S):Min Z0 m T k t S:=⟨h.1.rel fun d a b _ => al0 d a b,h.2⟩
lemma NK.toR {m T k t:ℕ} {S:Finset ℕ} (h:NK Z0 m T k t S):NK R m T k t S :=
  ⟨fun d a b S1 k0 e hb hl => h.1 d a b S1 k0 e (hb.rel fun d a b _ => al0 d a b) (hl.rel fun d a b _ => al0 d a b),
    fun a S1 k0 t0 e e' hu hl => h.2 a S1 k0 t0 e e' hu (hl.rel fun d a b _ => al0 d a b)⟩
section sound
variable {P:List ℕ} {l m g T:ℕ} (X:Ctx P l m g T)
include X
lemma one_sound (hR:RR R) (hR2:∀ d a b,(R a = 0 ∨ R b = 0) → Al R d a b) {K:ℕ} {f:ℕ → ℕ → ℕ → List W → Bool}
    (hF:∀ (k t z:ℕ) (v:List W) (S:Finset ℕ),f k t z v = false → StOk P T l k z v S → (∀ w ∈ v,w.r = R w.s) →
      ∀ k' ≤ k,Live Z0 m T k' t S → (∀ q < k',¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S:Set ℕ)))) → False)
    {k t z y:ℕ} {v:List W} {S:Finset ℕ} (hs:StOk P T l k z v S) (hcod:∀ w ∈ v,w.r = R w.s) (hlen:2 ≤ v.length)
    {k':ℕ} (hk:k' ≤ k) (hl:Live Z0 m T k' t S) (hmW:∀ q < k',¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S:Set ℕ))))
    (hy:y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK Z0 m T k' t S))
    (h2:mv (look l m g K) l m g k t z v y = false)
    (h1:∀ a ∈ v,∀ c ∈ v,a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go:(L_meta_10760.X → L_meta_10760.X → Bool) → List L_meta_10760.X → Bool,
      node (f (k - 1) t) (pos' t) l m g (k - t - y) v.length z v go = false ∧
      ∀ h,go h (v.map (mkx (pos' t) l (wst (pos' t) l v))) = false →
        h (mkx (pos' t) l (wst (pos' t) l v) a) (mkx (pos' t) l (wst (pos' t) l v) c) = false ∨
        h (mkx (pos' t) l (wst (pos' t) l v) c) (mkx (pos' t) l (wst (pos' t) l v) a) = false):False:=by
  have hmin:Min Z0 m T k' t S:=⟨hl,fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  have hcard:=hs.rep.card
  rcases front hR2 hl hmW with hlR | ⟨k0,d,a,b,S1,rfl,ha,hb',hb,hl1⟩
  · exact mv_sound X hR (look_sound X hR K) hs (fun w hw => Or.inr (hcod w hw)) hlen h2 k' hk ⟨hlR,hmin.2⟩ (hy.imp id fun ⟨q1,q2,q3⟩ => ⟨q1,q2,q3.toR⟩)
  · obtain ⟨k,rfl⟩:∃ j,k = j + 1:=⟨k - 1,by omega⟩
    obtain ⟨wa,hwa,rfl⟩:=hs.rep.mem.1 hb.sub.1
    obtain ⟨wb,hwb,rfl⟩:=hs.rep.mem.1 hb.sub.2.1
    obtain ⟨go,hg1,hg2⟩:=h1 wa hwa wb hwb hb.1 (by rw [hcod wa hwa]; exact ha) (by rw [hcod wb hwb]; exact hb')
    obtain ⟨z',r,hf,hst,hmem⟩:=node_bi X hs hmin (by omega) rfl rfl (NK.sizeB hcard hmin hk hb hl1 hy) hb hl1 (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      rw [hs.rep.inj ha hwa hax,hs.rep.inj hc hwb hcy]
      exact hg2 h hp) hg1
    have hfr:R (op d wa.s wb.s) = 0:=by
      by_contra hne
      refine hmW k0 (by omega) (hl1.sol.mono le_rfl fun x hx => ?_)
      have hx':=hb.sub.2.2 hx
      simp only [Finset.mem_insert] at hx'
      rcases hx' with rfl | hx'
      · exact Or.inl (Or.inl hne)
      · exact Or.inl (Or.inr hx')
    refine hF _ _ _ _ _ hf hst ?_ k0 (by simpa using hk) hl1 ?_
    · intro w hw
      rcases hmem w hw with ⟨e1,e2⟩ | h
      · rw [e1,e2,hfr]
      · exact hcod w h
    · intro q hq hs'
      refine hmW (q + 1) (by omega) (.bi (d:=d) (a:=wa.s) (b:=wb.s) (Or.inl (Or.inr hb.sub.1)) (Or.inl (Or.inr hb.sub.2.1)) (al0 _ _ _) (hs'.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · have hx':=hb.sub.2.2 hx
        simp only [Finset.mem_insert] at hx'
        rcases hx' with rfl | hx'
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr hx'))
      · exact Or.inr (Or.inr hx)
lemma or_false' {a b:Bool} (h:(Bool.rec (motive:=fun _ => Bool) b true a:Bool) = false):a = false ∧ b = false:=by
  clear X
  cases a <;> simp_all
theorem look1_sound (hR:RR R) (hR2:∀ d a b,(R a = 0 ∨ R b = 0) → Al R d a b) {K:ℕ}:∀ (fuel k t z:ℕ) (v:List W) (S:Finset ℕ),
    look1 l m g K fuel k t z v = false → StOk P T l k z v S → (∀ w ∈ v,w.r = R w.s) →
      ∀ k' ≤ k,Live Z0 m T k' t S → (∀ q < k',¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S:Set ℕ)))) → False:=by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look1] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hl hmW
    change (Bool.rec (motive:=fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => Bool.rec (motive:=fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (look1 l m g K fuel (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsS))) true (Nat.ble v.length 1):Bool) = false at h
    rw [bR,pos_eq] at h
    cases h0:Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0,cond_false] at h
      have hlen:2 ≤ v.length:=by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      have hmin:Min Z0 m T k' t S:=⟨hl,fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
      obtain ⟨y,hFy,hyk⟩:=tst_sound X hs hmin hk
      have hy:=(hFy _).symm.trans h
      beta_reduce at hy
      obtain ⟨hy1,hy2⟩:=or_false' X hy
      refine one_sound X hR hR2 ih hs hcod hlen hk hl hmW hyk hy2 fun a ha c hc hne har hcr => ⟨pairsS,hy1,fun h hp => ?_⟩
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_10760.X.s e))
end sound
def rawP:List ℕ:=[(List.foldr (fun a b => a + b * 1000000000000000000) 0 [125884897017388527,911360519918072575,190247476646018120,926587479695646280,152169335154869692,895222811556010842,395136992461053825,60977000104647449,307775363510052985,201775676720014114,882747967876508870,86345317615860846,222794324751136322,25607833661378867,4030536655947]),(List.foldr (fun a b => a + b * 1000000000000000000) 0 [427619820268908279,611673282006495178,523537263712844650,131876886382522293,995358805795456267,287564695230135095,405037506368680297,564053669723801351,250477970701718343,234522927300080226,811496922856592449,41706082574002843,497560289521829611,600555301428375995,709516083655031862,378445393885503883,81748995]),(List.foldr (fun a b => a + b * 1000000000000000000) 0 [637022721258583931,897427741173461161,506185934454709344,786185082414072109,921801486952861309,900222034017710744,590321865934574010,188043668106042607,878222087060015540,384608361675769147,612985753261276173,268041607143096155,71638142305163954,132188871851879598,897733956164046393,37175139085978]),(List.foldr (fun a b => a + b * 1000000000000000000) 0 [329111169589282749,34572616682882841,350307357897506162,971206976080027883,78818288397222396,905201929187825175,307765115227596131,587806948023060355,707589006869568137,758927451570637130,788652996915148506,264998155877128801,764625236457824633,992553925158528041,975975929574923879,4431622]),(List.foldr (fun a b => a + b * 1000000000000000000) 0 [367868192963164222,826894839732050953,550464876680779732,242221721010312716,655954627452690796,6538401540553826,211456277817069234,476097375284536394,978248091538689899,902819589515085269,489420809790826709,162240845434442989,400868156395060688,919733201335939524,296113667201193658,934574382089097975,21430008644496]),(List.foldr (fun a b => a + b * 1000000000000000000) 0 [43184682485678016,168682726317634565,972695316055168822,124379035787045336,948242578219173922,514972211611741498,573397593586256290,966704419898104496,3091321451432668,66856418841845548,357773858522199022,193821631862703454,171254021463135443,854278577812418273,948622156903045479,745276835826610840,9]),(List.foldr (fun a b => a + b * 1000000000000000000) 0 [905839562234789888,215171260361302992,540077729529840949,900717764651871085,688702739003043006,783599008106436768,568699314428056730,514987753722767027,781870334931103451,864873027590543296,372905638022283770,284076639801647192,612324462995814985,252999375877676026,695221132673708737,927200457415567441,21430090393774])]
def xw (e:ℕ × ℕ):ℕ:=rawP.getD e.1 0 ||| rawP.getD e.2 0
def rawL (E:List (ℕ × ℕ)):List ℕ:=rawP ++ E.map xw
def six:List (ℕ × ℕ):=[]
def rawG:List ℕ:=rawL six
def FPM:ℕ:=2 ^ 64 - 1
def FULL:ℕ:=2 ^ NN - 1
def TG:ℕ:=(List.foldr (fun a b => a + b * 1000000000000000000) 0 [457424848330424319,715234948972014205,124645358009780528,20012900803184522,735604019182077490,938431350882492032,2382324645710741,120852817932023020,3273378])
def kz (Z:ℕ):ℕ:=(List.range 7).foldr (fun i x => bif Nat.testBit Z i then Nat.lor x (Nat.land (Nat.lor (rawP.getD i 0) (Nat.shiftRight (rawP.getD i 0) NN)) FULL) else x) 0
def lz (Z:ℕ):ℕ:=Nat.land AA (Nat.xor (kz Z) FULL)
def fz (Z:ℕ):ℕ:=Nat.land FPM (Nat.xor (kz Z) FULL)
def mz (Z:ℕ):ℕ:=Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) NN)
def tz (Z:ℕ):ℕ:=Nat.land TG (mz Z)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_TG:AA &&& TG = AA:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_lt:TG < 2 ^ NN:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_lt:AA < 2 ^ NN:=by decide +kernel
lemma lz_lg (Z i:ℕ) (h:(lz Z).testBit i = true):Lg NN (mz Z) (tz Z) i ∧ AA.testBit i = true:=by
  have hA:AA.testBit i = true:=by
    simp only [lz,nl,Nat.testBit_and,Bool.and_eq_true] at h; exact h.1
  have hT:TG.testBit i = true:=by
    have:=congrArg (fun x => x.testBit i) AA_TG
    simp [hA] at this; exact this
  have m1:(mz Z).testBit i = true:=by simp [mz,no,h]
  have m2:(mz Z).testBit (NN + i) = true:=by
    simp only [mz,no,Nat.testBit_or,Nat.shiftLeft_eq,Bool.or_eq_true]
    right
    change (lz Z <<< NN).testBit (NN + i) = true
    rw [Nat.testBit_shiftLeft]; simp [h]
  refine ⟨⟨m1,m2,?_,?_⟩,hA⟩
  · simp only [tz,nl,Nat.testBit_and,hT,m1]; rfl
  · simp only [tz,nl,Nat.testBit_and]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le TG_lt (Nat.pow_le_pow_right (by omega) (by omega)))]; rfl
def segGood (w o:ℕ) (s:ℕ × ℕ):Bool :=
  Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) 0 || Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) (2 ^ (s.2 - s.1 - 1) - 1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raw_good:rawG.all (fun w => segsX.all (segGood w 0) && segsY.all (segGood w NN)) = true:=by decide +kernel
lemma segGood_eq {w o:ℕ} {s:ℕ × ℕ} (h:segGood w o s = true) {i j:ℕ} (h1:s.1 < i) (h2:i < s.2) (h3:s.1 < j) (h4:j < s.2) :
    w.testBit (o + i) = w.testBit (o + j):=by
  have key:∀ i,s.1 < i → i < s.2 → w.testBit (o + i) = ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)).testBit (i - s.1 - 1):=by
    intro i h1 h2
    rw [Nat.testBit_mod_two_pow,Nat.testBit_shiftRight,show o + s.1 + 1 + (i - s.1 - 1) = o + i by omega]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega]
  rw [key i h1 h2,key j h3 h4]
  simp only [segGood,Bool.or_eq_true,Nat.beq_eq] at h
  rcases h with h | h <;> rw [h]
  · simp
  · rw [Nat.testBit_two_pow_sub_one,Nat.testBit_two_pow_sub_one]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega,show j - s.1 - 1 < s.2 - s.1 - 1 by omega]
lemma wire_good {w:ℕ} (hw:w ∈ rawG) (Z:ℕ):Good (lz Z) (w &&& mz Z):=by
  have h:=List.all_eq_true.1 raw_good w hw
  simp only [Bool.and_eq_true,List.all_eq_true] at h
  refine ⟨fun i j hij h1 h2 => ?_,fun i j hij h1 h2 => ?_⟩ <;> obtain ⟨s,hs,a1,a2,a3,a4⟩:=hij
  · have:=segGood_eq (h.1 s hs) a1 a2 a3 a4
    simp only [Nat.zero_add] at this
    rw [Nat.testBit_and,Nat.testBit_and,this,(lz_lg Z i h1).1.1,(lz_lg Z j h2).1.1]
  · have:=segGood_eq (h.2 s hs) a1 a2 a3 a4
    rw [Nat.testBit_and,Nat.testBit_and,this,(lz_lg Z i h1).1.2.1,(lz_lg Z j h2).1.2.1]
noncomputable section packedDigits
def pL (L:List ℕ):ℕ:=List.rec (motive:=fun _ => ℕ) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih 5) d) L
end packedDigits
lemma pL_cons (d:ℕ) (L:List ℕ):pL (d :: L) = 2 ^ 5 * pL L + d:=by
  change (pL L <<< 5) + d = _; rw [Nat.shiftLeft_eq]; ring
lemma pL_pk (L:List ℕ):pL L = pk L.length (fun j => L.getD j 0):=by
  induction L with
  | nil => simp [pL,pk]
  | cons d L ih =>
    rw [pL_cons,ih,pk,pk,List.length_cons,Finset.sum_range_succ',Finset.mul_sum]
    simp only [Nat.mul_zero,pow_zero,mul_one,List.getD_cons_zero,List.getD_cons_succ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 5 * (j + 1) = 5 * j + 5 by ring,pow_add]; ring
lemma pL_bit {L:List ℕ} (h:∀ d ∈ L,d ≤ 1):∀ i,(pL L).testBit i = true ↔ (i % 5 = 0 ∧ i / 5 < L.length ∧ L.getD (i / 5) 0 = 1):=by
  induction L with
  | nil => intro i; simp [pL]
  | cons d L ih =>
    intro i
    have hd:=h d (by simp)
    have ih:=ih fun x hx => h x (by simp [hx])
    rw [pL_cons,Nat.testBit_two_pow_mul_add _ (by omega)]
    split_ifs with hi
    · have:i / 5 = 0:=by omega
      rw [this]
      rcases Nat.eq_zero_or_pos i with rfl | hp
      · interval_cases d <;> simp
      · constructor
        · intro hb
          have:d.testBit i = false:=Nat.testBit_lt_two_pow (lt_of_le_of_lt hd (Nat.one_lt_two_pow (by omega)))
          rw [this] at hb; simp at hb
        · intro hb; omega
    · rw [ih,show i / 5 = (i - 5) / 5 + 1 by omega]
      simp only [List.length_cons,List.getD_cons_succ]
      constructor
      · rintro ⟨a,b,c⟩; exact ⟨by omega,by omega,c⟩
      · rintro ⟨a,b,c⟩; exact ⟨by omega,by omega,c⟩
lemma pL_isPk {L:List ℕ} (h:∀ d ∈ L,d ≤ 1):isPk L.length (pL L):=fun i hi => by
  have:=(pL_bit h i).1 hi; exact ⟨this.1,this.2.1⟩
def bit01 (b:Bool):ℕ:=bif b then 1 else 0
def mkW (P:List ℕ) (s:ℕ):W:=⟨s,pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0)),pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)),
  Nat.lor (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0))) (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n))),3⟩
lemma mkW_ok (P:List ℕ) (s:ℕ):WOk P (mkW P s):=by
  have h01:∀ f:ℕ → Bool,∀ d ∈ P.map (fun n => bit01 (f n)),d ≤ 1:=by
    intro f d hd; simp only [List.mem_map] at hd
    obtain ⟨n,_,rfl⟩:=hd; cases f n <;> simp [bit01]
  have bt:∀ f:ℕ → Bool,∀ j < P.length,(pL (P.map fun n => bit01 (f n))).testBit (5 * j) = true → f (P.getD j 0) = true:=by
    intro f j hj h
    have h:=((pL_bit (h01 f) _).1 h).2.2
    rw [show 5 * j / 5 = j by omega,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hj] at h
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
    simp at h ⊢
    cases hf:f P[j] <;> simp [bit01,hf] at h ⊢
  refine ⟨?_,?_,rfl,fun j hj h => ?_,fun j hj h => ?_⟩
  · have:=pL_isPk (h01 fun n => Nat.beq (Nat.land s n) 0); rwa [List.length_map] at this
  · have:=pL_isPk (h01 fun n => Nat.beq (Nat.land s n) n); rwa [List.length_map] at this
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) 0) j hj h)
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) n) j hj h)
noncomputable section stateData
def addS (o:W) (v:List W):List W:=List.rec (motive:=fun _ => List W) [o]
  (fun w t ih => Bool.rec (motive:=fun _ => List W) (w :: ih) (Bool.rec (motive:=fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def avl (P:List ℕ) (m:ℕ) (L:List ℕ):List W:=List.rec (motive:=fun _ => List W) []
  (fun w _ ih => Bool.rec (motive:=fun _ => List W) (Bool.rec (motive:=fun _ => List W) (addS (mkW P (Nat.land w m)) ih) ih (Nat.beq (Nat.land w m) m)) ih (Nat.beq (Nat.land w m) 0)) L
def frc (v:List W):(List W → Bool) → Bool:=List.rec (motive:=fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => st w.s fun s => st w.a fun a => st w.b fun b => st w.c fun c => ih fun r => h (⟨s,a,b,c,w.r⟩ :: r)) v
def anySub (d:Bool) (l:ℕ) (v:List W):ℕ → (List W → Bool) → Bool:=List.rec (motive:=fun _ => ℕ → (List W → Bool) → Bool) (fun _ h => h [])
  (fun w t ih c h => Bool.rec (motive:=fun _ => Bool) (Bool.rec (motive:=fun _ => Bool) false (ih c h) (Nat.beq (Nat.lor c (cov d l t)) l)) true
    (st (Nat.lor c (sp d l w.s)) fun c => ih c fun r => h (w :: r))) v
def sumc (v:List W):ℕ:=List.rec (motive:=fun _ => ℕ) 0 (fun w _ ih => Nat.add w.c ih) v
def MM:ℕ:=214
def hb (H x:ℕ):Bool:=Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1
def pairsC (H:ℕ) (h:X → X → Bool) (xs:List X):Bool :=
  List.rec (motive:=fun _ => Bool) false (fun a r ih => Bool.rec (motive:=fun _ => Bool) ih true
    (scan (fun x => Bool.rec (motive:=fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r)) xs
def topC (l m g K H ph k t z:ℕ) (v:List W):Bool :=
  Bool.rec (motive:=fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive:=fun _ => Bool) (Bool.rec (motive:=fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (node (look1 l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
def hasP (p:ℕ) (v:List W):Bool:=Bool.rec (motive:=fun _ => Bool)
  (List.rec (motive:=fun _ => Bool) false (fun w _ ih => Bool.rec (motive:=fun _ => Bool) ih true (Nat.beq w.s p)) v) true (Nat.beq p 0)
def startv (l m g B K t p H ph:ℕ) (v:List W):Bool :=
  Bool.rec (motive:=fun _ => Bool) false (Bool.rec (motive:=fun _ => Bool) false
    (child (fun z r => topC l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
end stateData
lemma frc_eq (v:List W):∀ h,frc v h = h v:=by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change st w.s (fun s => st w.a fun a => st w.b fun b => st w.c fun c => frc v fun r => h (⟨s,a,b,c,w.r⟩ :: r)) = _
    simp only [st_eq]; rw [ih]
lemma anySub_false {d:Bool} {l:ℕ} {v:List W}:∀ {c:ℕ} {h:List W → Bool},(∀ i,c.testBit i = true → l.testBit i = true) → anySub d l v c h = false →
    ∀ r,r.Sublist v → (∀ i,l.testBit i = true → c.testBit i = true ∨ (cov d l r).testBit i = true) → h r = false:=by
  induction v with
  | nil => intro c h _ hh r hr _; rw [List.sublist_nil.1 hr]; exact hh
  | cons w v ih =>
    intro c h hcl hh r hr hcov
    change (Bool.rec (motive:=fun _ => Bool) (Bool.rec (motive:=fun _ => Bool) false (anySub d l v c h) (Nat.beq (Nat.lor c (cov d l v)) l)) true
      (st (Nat.lor c (sp d l w.s)) fun c => anySub d l v c fun r => h (w :: r)):Bool) = false at hh
    rw [bR,bR,st_eq] at hh
    cases h1:anySub d l v (Nat.lor c (sp d l w.s)) (fun r => h (w :: r)) with
    | true => rw [h1] at hh; simp at hh
    | false =>
      rw [h1,Bool.cond_false] at hh
      have hc2:∀ i,(cov d l v).testBit i = true → l.testBit i = true:=by
        intro i hi
        obtain ⟨w',_,hw'⟩:=(cov_bit _ _ _ _).1 hi
        rw [sp_bit,Bool.and_eq_true] at hw'; exact hw'.1
      cases hr with
      | cons _ hr =>
        have:Nat.beq (Nat.lor c (cov d l v)) l = true:=by
          rw [Nat.beq_eq]
          apply Nat.eq_of_testBit_eq; intro i
          rw [no,Nat.testBit_or]
          cases hli:l.testBit i with
          | false =>
            by_contra hc
            rw [Bool.not_eq_false,Bool.or_eq_true] at hc
            rcases hc with h | h
            · rw [hcl i h] at hli; simp at hli
            · rw [hc2 i h] at hli; simp at hli
          | true =>
            rcases hcov i hli with h | h
            · rw [h]; rfl
            · obtain ⟨w',hw',h2⟩:=(cov_bit _ _ _ _).1 h
              rw [(cov_bit d l i v).2 ⟨w',hr.subset hw',h2⟩]; simp
        rw [this,Bool.cond_true] at hh
        exact ih hcl hh r hr hcov
      | cons_cons _ hr =>
        rename_i r'
        refine ih (c:=Nat.lor c (sp d l w.s)) ?_ h1 r' hr ?_
        · intro i hi
          rw [no,Nat.testBit_or,Bool.or_eq_true] at hi
          rcases hi with h | h
          · exact hcl i h
          · rw [sp_bit,Bool.and_eq_true] at h; exact h.1
        · intro i hi
          rw [no,Nat.testBit_or,Bool.or_eq_true]
          rcases hcov i hi with h | h
          · exact Or.inl (Or.inl h)
          · change (Nat.lor (sp d l w.s) (cov d l r')).testBit i = true at h
            rw [no,Nat.testBit_or,Bool.or_eq_true] at h
            rcases h with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
lemma addS_cons (o w:W) (t:List W):addS o (w :: t) = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then w :: t else o :: w :: t) else w :: addS o t:=by
  change Bool.rec (motive:=fun _ => List W) (w :: addS o t) (Bool.rec (motive:=fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s) = _
  cases Nat.ble w.s o.s <;> cases Nat.beq o.s w.s <;> rfl
def Srt (v:List W):Prop:=v.Pairwise (fun a b => b.s < a.s)
lemma addS_spec {o:W} {v:List W} (hv:Srt v):Srt (addS o v) ∧ (∀ w ∈ addS o v,w = o ∨ w ∈ v) ∧
    (∃ w ∈ addS o v,w.s = o.s) ∧ ∀ w ∈ v,w ∈ addS o v:=by
  induction v with
  | nil => exact ⟨List.pairwise_singleton _ _,by simp [addS],⟨o,by simp [addS],rfl⟩,by simp⟩
  | cons x t ih =>
    have hp:=List.pairwise_cons.1 hv
    obtain ⟨i1,i2,i3,i4⟩:=ih hp.2
    rw [addS_cons]
    cases h1:Nat.ble x.s o.s with
    | true =>
      have hle:=Nat.le_of_ble_eq_true h1
      cases h2:Nat.beq o.s x.s with
      | true => exact ⟨hv,fun w hw => Or.inr hw,⟨x,by simp,(Nat.eq_of_beq_eq_true h2).symm⟩,fun w hw => hw⟩
      | false =>
        have hne:o.s ≠ x.s:=fun e => by rw [e,Nat.beq_refl] at h2; simp at h2
        refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_,hv⟩,fun w hw => by simpa using hw,⟨o,by simp,rfl⟩,fun w hw => by simp at hw ⊢; tauto⟩
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · omega
        · have:=hp.1 w hw; omega
    | false =>
      have hlt:o.s < x.s:=by
        by_contra hc; rw [Nat.ble_eq_true_of_le (by omega)] at h1; simp at h1
      refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_,i1⟩,fun w hw => ?_,?_,fun w hw => ?_⟩
      · rcases i2 w hw with rfl | h
        · exact hlt
        · exact hp.1 w h
      · simp only [Bool.cond_false,List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · rcases i2 w hw with h | h <;> simp [h]
      · obtain ⟨w,hw,e⟩:=i3; exact ⟨w,by simp [hw],e⟩
      · simp only [Bool.cond_false,List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · exact Or.inr (i4 w hw)
lemma avl_spec (P:List ℕ) (m:ℕ) (L:List ℕ):Srt (avl P m L) ∧ (∀ w ∈ avl P m L,∃ x ∈ L,w = mkW P (x &&& m)) ∧
    ∀ x ∈ L,x &&& m ≠ 0 → x &&& m ≠ m → ∃ w ∈ avl P m L,w.s = x &&& m:=by
  induction L with
  | nil => exact ⟨List.Pairwise.nil,by simp [avl],by simp⟩
  | cons y L ih =>
    obtain ⟨i1,i2,i3⟩:=ih
    have e:avl P m (y :: L) = bif Nat.beq (Nat.land y m) 0 then avl P m L else bif Nat.beq (Nat.land y m) m then avl P m L else addS (mkW P (Nat.land y m)) (avl P m L):=by
      change Bool.rec (motive:=fun _ => List W) (Bool.rec (motive:=fun _ => List W) (addS (mkW P (Nat.land y m)) (avl P m L)) (avl P m L) (Nat.beq (Nat.land y m) m)) (avl P m L) (Nat.beq (Nat.land y m) 0) = _
      cases Nat.beq (Nat.land y m) 0 <;> cases Nat.beq (Nat.land y m) m <;> rfl
    have old:∀ w ∈ avl P m L,∃ x ∈ y :: L,w = mkW P (x &&& m):=fun w hw => by
      obtain ⟨x,hx,e⟩:=i2 w hw; exact ⟨x,by simp [hx],e⟩
    rw [e]
    cases h1:Nat.beq (Nat.land y m) 0 with
    | true =>
      refine ⟨i1,old,fun x hx h2 h3 => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact absurd (Nat.eq_of_beq_eq_true h1) h2
      · exact i3 x hx h2 h3
    | false =>
      cases h1':Nat.beq (Nat.land y m) m with
      | true =>
        refine ⟨i1,old,fun x hx h2 h3 => ?_⟩
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd (Nat.eq_of_beq_eq_true h1') h3
        · exact i3 x hx h2 h3
      | false =>
        obtain ⟨j1,j2,j3,j4⟩:=addS_spec (o:=mkW P (Nat.land y m)) i1
        refine ⟨j1,fun w hw => ?_,fun x hx h2 h3 => ?_⟩
        · rcases j2 w hw with rfl | h
          · exact ⟨y,by simp,rfl⟩
          · exact old w h
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact j3
          · obtain ⟨w,hw,e⟩:=i3 x hx h2 h3; exact ⟨w,j4 w hw,e⟩
lemma pairsC_false {H:ℕ} {h:X → X → Bool} {xs:List X} (hp:pairsC H h xs = false) :
    xs.Pairwise (fun a b => hb H (a.s + b.s) = true → h a b = false):=by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive:=fun _ => Bool) (pairsC H h r) true
      (scan (fun x => Bool.rec (motive:=fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r):Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · intro b hbm hi
      have h1:scan (fun x => Bool.rec (motive:=fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r = false:=by
        revert hp
        cases scan (fun x => Bool.rec (motive:=fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r <;> simp
      have h2:=scan_false h1 b hbm
      beta_reduce at h2
      rw [bR] at h2
      have h3:hb H (Nat.add a.s b.s) = true:=hi
      rwa [h3,Bool.cond_true] at h2
    · apply ih; revert hp; cases pairsC H h r <;> simp
def mFull (M:List (ℕ × ℕ)):Bool:=(List.range MM).all (fun r => M.any (fun p => hb p.1 r)) && M.any (fun p => Nat.beq p.2 1)
lemma hb_mod (H x:ℕ):hb H x = hb H (x % MM):=by
  unfold hb
  change Nat.beq ((H >>> (x % MM)) &&& 1) 1 = Nat.beq ((H >>> (x % MM % MM)) &&& 1) 1
  rw [Nat.mod_mod]
section sound
variable {P:List ℕ} {l m g T:ℕ} (X:Ctx P l m g T)
include X
lemma topC_sound (hR:RR R) (hR2:∀ d a b,(R a = 0 ∨ R b = 0) → Al R d a b) {K k t z:ℕ} {v:List W} {S:Finset ℕ} {M:List (ℕ × ℕ)}
    (hM:mFull M = true) (h:∀ p ∈ M,topC l m g K p.1 p.2 k t z v = false) (hs:StOk P T l k z v S) (hcod:∀ w ∈ v,w.r = R w.s)
    {k':ℕ} (hk:k' ≤ k) (hl:Live Z0 m T k' t S) (hmW:∀ q < k',¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S:Set ℕ)))):False:=by
  simp only [mFull,Bool.and_eq_true,List.all_eq_true,List.mem_range,List.any_eq_true] at hM
  obtain ⟨hM1,p0,hp0,hp1⟩:=hM
  have un:∀ p ∈ M,2 ≤ v.length ∧ tst (pos' t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive:=fun _ => Bool) (Bool.rec (motive:=fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq p.2 1)) true
      (node (look1 l m g K K (k - 1) t) (pos' t) l m g (k - t - y) v.length z v (fun h xs => pairsC p.1 h (fs xs)))) = false:=by
    intro p hp
    have h:=h p hp
    change (Bool.rec (motive:=fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive:=fun _ => Bool) (Bool.rec (motive:=fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq p.2 1)) true
      (node (look1 l m g K K (k - 1) t) (pos t) l m g (k - t - y) v.length z v (fun h xs => pairsC p.1 h (fs xs))))) true (Nat.ble v.length 1):Bool) = false at h
    rw [bR,pos_eq] at h
    cases h0:Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0,cond_false] at h
      refine ⟨?_,h⟩
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
  have hmin:Min Z0 m T k' t S:=⟨hl,fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  obtain ⟨y,hFy,hyk⟩:=tst_sound X hs hmin hk
  have un2:=fun p hp => (hFy _).symm.trans (un p hp).2
  refine one_sound X hR hR2 (K:=K) (f:=look1 l m g K K) (look1_sound X hR hR2 (K:=K) K) hs hcod (un p0 hp0).1 hk hl hmW hyk ?_ ?_
  · have:=(or_false' X (un2 p0 hp0)).2
    rw [bR,hp1,cond_true] at this; exact this
  · intro a ha c hc hne har hcr
    obtain ⟨p,hpM,hpb⟩:=hM1 ((a.s + c.s) % MM) (Nat.mod_lt _ (by decide))
    rw [← hb_mod] at hpb
    refine ⟨_,(or_false' X (un2 p hpM)).1,fun h hp => ?_⟩
    have hpw:=pairsC_false hp
    have:Std.Symm (fun a b:L_meta_10760.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S:=fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_10760.X.s e)) hpb
end sound
def WZ (E:List (ℕ × ℕ)) (Z:ℕ):Set ℕ:={x | ∃ w ∈ rawL E,x = w &&& mz Z}
def Imp (E:List (ℕ × ℕ)) (Z L:ℕ):Prop:=∀ q < L,¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z))
def PZ (Q:List (ℕ × ℕ)):List ℕ:=Q.map (fun e => mz e.1)
def pOk (Z:ℕ) (Q:List (ℕ × ℕ)):Bool:=!Nat.beq (tz Z) 0 && !Nat.beq (tz Z) (mz Z) && Q.all (fun e => Nat.beq (Nat.land (mz e.1) (mz Z)) (mz e.1) &&
  !Nat.beq (tz e.1) 0 && !Nat.beq (tz e.1) (mz e.1))
def pwr (E:List (ℕ × ℕ)) (Z:ℕ):ℕ:=(E.map fun e => Nat.land (xw e) (mz Z)).headD 0
noncomputable def chk (E Q:List (ℕ × ℕ)) (Z K t H ph:ℕ):Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startv l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
lemma tz_sub {Z Z':ℕ} (h:mz Z' &&& mz Z = mz Z'):tz Z &&& mz Z' = tz Z':=by
  simp only [tz,nl,Nat.and_assoc]; rw [Nat.and_comm (mz Z),h]
lemma Im_WZ {E:List (ℕ × ℕ)} {Z Z':ℕ} (h:mz Z' &&& mz Z = mz Z') {S:Finset ℕ} (hS:(S:Set ℕ) ⊆ WZ E Z):Im (mz Z') S ⊆ WZ E Z':=by
  rintro x ⟨y,hy,rfl⟩
  obtain ⟨w,hw,rfl⟩:=hS hy
  exact ⟨w,hw,by simp only [Nat.and_assoc]; rw [Nat.and_comm (mz Z),h]⟩
lemma sumc_eq {P:List ℕ} {v:List W} (hw:∀ w ∈ v,WOk P w):sumc v = pk P.length (cnt v):=by
  induction v with
  | nil => simp [sumc,pk,cnt]
  | cons w v ih =>
    change w.c + sumc v = _
    rw [ih fun x hx => hw x (by simp [hx]),fl_pk (hw w (by simp)),pk_add]
    exact pk_congr fun j _ => by rw [cnt_cons]
lemma pk16 (Q:List (ℕ × ℕ)) (K:ℕ):pL (Q.map fun e => 16 + (K - e.2)) = pk (PZ Q).length (fun j => 16 + (K - (Q.getD j (0,K)).2)):=by
  rw [pL_pk,PZ,List.length_map,List.length_map]
  refine pk_congr fun j hj => ?_
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hj]; rfl
open Classical in
noncomputable def RZ (E:List (ℕ × ℕ)) (Z:ℕ):ℕ → ℕ:=fun s => if s ∈ WZ E Z then 3 else 0
lemma RZ_set (E:List (ℕ × ℕ)) (Z:ℕ):{x | RZ E Z x ≠ 0} = WZ E Z:=by
  ext x; simp only [RZ,Set.mem_setOf_eq]; split_ifs with h <;> simp [h]
lemma RZ_R (E:List (ℕ × ℕ)) (Z:ℕ):RR (RZ E Z):=by
  intro d a b ha hb h
  have h3:∀ x,RZ E Z x ≠ 0 → RZ E Z x = 3:=by
    intro x hx; unfold RZ at hx ⊢; split_ifs at hx ⊢ with h
    · rfl
    · simp at hx
  unfold Al at h
  rw [h3 a ha,h3 b hb] at h
  cases d <;> simp at h
lemma RZ_R2 (E:List (ℕ × ℕ)) (Z:ℕ):∀ d a b,(RZ E Z a = 0 ∨ RZ E Z b = 0) → Al (RZ E Z) d a b:=by
  intro d a b h
  unfold Al
  rcases h with h | h <;> rw [h] <;> simp
lemma hasP_ok {p:ℕ} {v:List W} (h:p = 0 ∨ ∃ w ∈ v,w.s = p):hasP p v = true:=by
  unfold hasP
  rw [bR]
  rcases h with rfl | ⟨w,hw,rfl⟩
  · rfl
  · have:(List.rec (motive:=fun _ => Bool) false (fun w' _ ih => Bool.rec (motive:=fun _ => Bool) ih true (Nat.beq w'.s w.s)) v:Bool) = true:=by
      induction v with
      | nil => simp at hw
      | cons x v ih =>
        change (Bool.rec (motive:=fun _ => Bool) (List.rec (motive:=fun _ => Bool) false (fun w' _ ih => Bool.rec (motive:=fun _ => Bool) ih true (Nat.beq w'.s w.s)) v:Bool) true (Nat.beq x.s w.s):Bool) = true
        rw [bR]
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · rw [Nat.beq_refl]; rfl
        · rw [ih hw]; cases Nat.beq x.s w.s <;> rfl
    rw [this]; cases Nat.beq w.s 0 <;> rfl
lemma rawL_sub {E:List (ℕ × ℕ)} (hE:∀ e ∈ E,e ∈ six) {w:ℕ} (hw:w ∈ rawL E):w ∈ rawG:=by
  simp only [rawG,rawL,List.mem_append,List.mem_map] at hw ⊢
  rcases hw with h | ⟨e,he,rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨e,hE e he,rfl⟩
theorem imp_of {E Q:List (ℕ × ℕ)} {Z L:ℕ} (hE:E = [] ∨ ∃ e ∈ six,E = [e] ∧ Imp [] Z L) (hp:pOk Z Q = true) (hL:L ≤ 15) (hI:∀ e ∈ Q,Imp E e.1 e.2)
    (hb:(∃ e ∈ Q,L ≤ e.2) ∨ ∀ t < L,∃ M:List (ℕ × ℕ),mFull M = true ∧ ∀ p ∈ M,chk E Q Z (L - 1) t p.1 p.2 = false):Imp E Z L:=by
  intro q hq hsol
  simp only [pOk,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hp
  obtain ⟨⟨hp0,hp1⟩,hp2⟩:=hp
  have nb:∀ {x y:ℕ},Nat.beq x y = false → x ≠ y:=fun h e => by rw [e,Nat.beq_refl] at h; simp at h
  have hT:tz Z &&& mz Z = tz Z:=by simp only [tz,nl,Nat.and_assoc,Nat.and_self]
  have hE6:∀ e ∈ E,e ∈ six:=by
    rcases hE with rfl | ⟨e,he,rfl,_⟩
    · simp
    · intro e' he'; simp only [List.mem_singleton] at he'; rw [he']; exact he
  classical
  have hex:∃ q,Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)):=⟨q,hsol⟩
  have hqL:Nat.find hex < L:=lt_of_le_of_lt (Nat.find_min' hex hsol) hq
  obtain ⟨k,hk,t,S,hS,hl⟩:=(Nat.find_spec hex).live
  have hCS:C (mz Z) (S:Set ℕ) ⊆ C (mz Z) (WZ E Z):=by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hkeq:k = Nat.find hex:=le_antisymm hk (Nat.find_min' hex (hl.sol.mono le_rfl hS))
  have hm:Min Z0 (mz Z) (tz Z) k t S:=⟨hl,fun q' hq' hs => Nat.find_min hex (by omega) (hs.mono le_rfl hCS)⟩
  have hbd:∀ x ∈ S,x &&& mz Z = x:=by
    intro x hx
    rcases hS hx with ⟨w,_,rfl⟩ | h
    · rw [Nat.and_assoc,Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0,h1⟩:=hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW:(S:Set ℕ) ⊆ WZ E Z:=by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj:∀ e ∈ Q,mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1:=by
    intro e he
    obtain ⟨⟨a,b⟩,c⟩:=hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a,nb b,nb c⟩
  have hno:∀ e ∈ Q,∀ q < e.2,¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)):=by
    intro e he q hq hs
    have h3:=(hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk:=hm.size.2
  rcases hb with ⟨e,he,hle⟩ | hb
  · have h3:=hproj e he
    obtain ⟨q',hq',hs'⟩:=hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno e he q' (by omega) hs'
  have hpw:pwr E Z = 0 ∨ pwr E Z ∈ S:=by
    rcases hE with rfl | ⟨e,he,rfl,hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k (by omega) (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w,hw,rfl⟩:=hSW hx
      simp only [rawL,List.mem_append,List.map_cons,List.map_nil,List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w,by simp [rawL,hw],rfl⟩
      · have hx:xw e &&& mz Z ∈ S:=by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨M,hMf,hchk⟩:=hb t (by omega)
  obtain ⟨a1,a2,a3⟩:=avl_spec (PZ Q) (mz Z) (rawL E)
  set v:=(avl (PZ Q) (mz Z) (rawL E)).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub:v.Sublist (avl (PZ Q) (mz Z) (rawL E)):=List.filter_sublist
  have hnd:(v.map W.s).Nodup:=by
    rw [List.Nodup,List.pairwise_map]
    exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
  have hrep:Rep v S:=by
    refine ⟨hnd,Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨w,hw,rfl⟩
      rw [hv,List.mem_filter] at hw; simpa using hw.2
    · intro hx
      obtain ⟨w,hw,rfl⟩:=hSW hx
      obtain ⟨w',hw',e⟩:=a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
      exact ⟨w',by rw [hv,List.mem_filter]; exact ⟨hw',by simpa [e] using hx⟩,e⟩
  have hwok:∀ w ∈ v,WOk (PZ Q) w:=by
    intro w hw
    obtain ⟨x,_,rfl⟩:=a2 w (hsub.subset hw); exact mkW_ok _ _
  have hcod:∀ w ∈ v,w.r = RZ E Z w.s:=by
    intro w hw
    obtain ⟨x,hx,rfl⟩:=a2 w (hsub.subset hw)
    have:x &&& mz Z ∈ WZ E Z:=⟨x,hx,rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ,if_pos this]
  have hgood:∀ w ∈ v,Good (lz Z) w.s:=by
    intro w hw
    obtain ⟨x,hx,rfl⟩:=a2 w (hsub.subset hw); exact wire_good (rawL_sub hE6 hx) Z
  have hPlen:(PZ Q).length = Q.length:=by simp [PZ]
  have hPget:∀ j < (PZ Q).length,(PZ Q).getD j 0 = mz (Q.getD j (0,L - 1)).1 ∧ Q.getD j (0,L - 1) ∈ Q:=by
    intro j hj
    rw [hPlen] at hj
    simp [PZ,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hj]
  have X:Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (tz Z):=by
    refine ⟨fun i hi => lz_lg Z i hi,fun j hj => ?_,?_⟩
    · obtain ⟨e1,e2⟩:=hPget j hj
      have h3:=hproj _ e2
      rw [e1,tz_sub h3.1]; exact h3
    · rw [pL_pk,List.length_map,hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hj]; rfl
  have hcl:Cl (PZ Q) (tz Z) (L - 1) (fun j => L - 1 - (Q.getD j (0,L - 1)).2) S:=by
    intro j hj q hq
    obtain ⟨e1,e2⟩:=hPget j hj
    have hq':q + (L - 1 - (Q.getD j (0,L - 1)).2) < L - 1:=hq
    rw [e1]; exact hno _ e2 q (by omega)
  have hle:=cnt_le X hrep hwok hcl hm (by omega)
  have hst:StOk (PZ Q) (tz Z) (lz Z) (L - 1) (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v S:=by
    refine ⟨hrep,hwok,hgood,_,fun j _ => by omega,hcl,?_⟩
    rw [sumc_eq hwok,pk16,pk_sub]
    intro j hj; have:=hle j hj; omega
  have hcov:∀ i,(lz Z).testBit i = true → (0:ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true:=by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1,m2,t1,t2⟩,_⟩:=lz_lg Z i hli
    obtain ⟨w,hw,hs⟩:=hl.cov m1 m2 t1 t2
    obtain ⟨w',hw',rfl⟩:=hrep.mem.1 hw
    exact ⟨w',hw',by rw [sp_bit,hli,pos_eq,hs]; rfl⟩
  have hsz:=hm.size.1
  have hcard:=hrep.card
  have hble:Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true:=Nat.ble_eq_true_of_le (by
    change v.length ≤ L - 1 + 1 - t; omega)
  have hhas:hasP (pwr E Z) v = true:=hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all:∀ p ∈ M,topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false:=by
    intro p hpM
    have h2:=hchk p hpM
    simp only [chk,frc_eq,st_eq] at h2
    have h3:=anySub_false (by simp) h2 v hsub hcov
    simp only [startv,bR,hhas,hble,Bool.cond_true] at h3
    exact child_sound X (f:=fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topC_sound X (RZ_R E Z) (RZ_R2 E Z) hMf all hst hcod (by omega) hl ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine Nat.find_min hex (show q < Nat.find hex by omega) (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx
def FF:ℕ:=2 ^ MM - 1
lemma ffull:mFull [(FF,1)] = true:=by decide +kernel
noncomputable def okT (E Q:List (ℕ × ℕ)) (Z L:ℕ) (ts:List ℕ):Bool:=ts.all (fun t => !chk E Q Z (L - 1) t FF 1)
noncomputable def okE (E Q:List (ℕ × ℕ)) (e:ℕ × ℕ):Bool:=pOk e.1 Q && Nat.ble e.2 15 && (Q.any (fun x => Nat.ble e.2 x.2) || okT E Q e.1 e.2 (List.range e.2))
lemma imp_okE {E Q:List (ℕ × ℕ)} {e:ℕ × ℕ} (hE:E = [] ∨ ∃ e' ∈ six,E = [e'] ∧ Imp [] e.1 e.2) (h:okE E Q e = true) (hI:∀ e' ∈ Q,Imp E e'.1 e'.2):Imp E e.1 e.2:=by
  simp only [okE,okT,Bool.and_eq_true,Bool.or_eq_true,List.any_eq_true,List.all_eq_true,List.mem_range,Bool.not_eq_true'] at h
  refine imp_of hE h.1.1 (Nat.le_of_ble_eq_true h.1.2) hI (h.2.imp (fun ⟨x,hx,hx2⟩ => ⟨x,hx,Nat.le_of_ble_eq_true hx2⟩) fun h t ht =>
    ⟨[(FF,1)],ffull,fun p hp => ?_⟩)
  simp only [List.mem_singleton] at hp; subst hp; exact h t ht
def pr (T:List (ℕ × ℕ)) (Z:ℕ):List (ℕ × ℕ):=T.filter (fun e => Nat.beq (Nat.land Z e.1) Z && !Nat.beq Z e.1)
lemma okAll {T U:List (ℕ × ℕ)} (h:U.all (fun e => okE [] (pr T e.1) e) = true)
    (hT:∀ e ∈ T,Imp [] e.1 e.2):∀ e ∈ U,Imp [] e.1 e.2:=fun e he => imp_okE
  (Or.inl rfl) (List.all_eq_true.1 h e he) (fun e' h' => hT e' (List.mem_of_mem_filter h'))
lemma apI {A B:List (ℕ × ℕ)} (ha:∀ e ∈ A,Imp [] e.1 e.2) (hb:∀ e ∈ B,Imp [] e.1 e.2):∀ e ∈ A ++ B,Imp [] e.1 e.2:=fun e he =>
  (List.mem_append.1 he).elim (ha e) (hb e)
noncomputable def okS (T:List (ℕ × ℕ)) (Z K:ℕ) (p:ℕ × ℕ × ℕ):Bool:=!chk [] (pr T Z) Z K p.1 p.2.1 p.2.2
def selT (M:List (ℕ × ℕ × ℕ)) (t:ℕ):List (ℕ × ℕ):=(M.filter (fun p => Nat.beq p.1 t)).map Prod.snd
def okP (T:List (ℕ × ℕ)) (Z L:ℕ) (M:List (ℕ × ℕ × ℕ)):Bool:=pOk Z (pr T Z) && Nat.ble L 15 && (List.range L).all (fun t => mFull (selT M t))
lemma imp_run {T:List (ℕ × ℕ)} {Z L:ℕ} (M:List (ℕ × ℕ × ℕ)) (hT:∀ e ∈ T,Imp [] e.1 e.2) (hp:okP T Z L M = true) (h:M.all (okS T Z (L - 1)) = true):Imp [] Z L:=by
  simp only [okP,Bool.and_eq_true,List.all_eq_true,List.mem_range] at hp
  refine imp_of (Or.inl rfl) hp.1.1 (Nat.le_of_ble_eq_true hp.1.2) (fun e he => hT e (List.mem_of_mem_filter he)) (Or.inr fun t ht => ⟨selT M t,hp.2 t ht,fun p hq => ?_⟩)
  simp only [selT,List.mem_map,List.mem_filter] at hq
  obtain ⟨q,⟨hq1,hq2⟩,rfl⟩:=hq
  have h1:=List.all_eq_true.1 h q hq1
  have h2:q.1 = t:=Nat.eq_of_beq_eq_true hq2
  simp only [okS,Bool.not_eq_true'] at h1
  rw [← h2]; exact h1
lemma appS {T:List (ℕ × ℕ)} {Z K:ℕ} {A B:List (ℕ × ℕ × ℕ)} (ha:A.all (okS T Z K) = true) (hb:B.all (okS T Z K) = true):(A ++ B).all (okS T Z K) = true:=by
  rw [List.all_append,ha,hb]; rfl
lemma one1 {Z L:ℕ} (h:Imp [] Z L):∀ e ∈ [(Z,L)],Imp [] e.1 e.2:=fun e he => by
  simp only [List.mem_singleton] at he; subst he; exact h
def ac0:List (ℕ × ℕ):=[]
lemma ai0:∀ e ∈ ac0,Imp [] e.1 e.2:=by simp [ac0]
def g4_0:List (ℕ × ℕ):=[(23,4),(30,4),(58,4),(85,4),(106,4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def k4_0:g4_0.all (fun e => okE [] (pr ac0 e.1) e) = true:=by decide +kernel
lemma j4_0:∀ e ∈ g4_0,Imp [] e.1 e.2:=okAll k4_0 ai0
def ac1:List (ℕ × ℕ):=g4_0 ++ ac0
lemma ai1:∀ e ∈ ac1,Imp [] e.1 e.2:=apI j4_0 ai0
def g3_0:List (ℕ × ℕ):=[(14,5),(19,5),(21,5),(22,5),(26,5),(28,5),(42,5),(50,5),(69,5),(74,5),(84,5),(104,5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def k3_0:g3_0.all (fun e => okE [] (pr ac1 e.1) e) = true:=by decide +kernel
lemma j3_0:∀ e ∈ g3_0,Imp [] e.1 e.2:=okAll k3_0 ai1
def ac2:List (ℕ × ℕ):=g3_0 ++ ac1
lemma ai2:∀ e ∈ ac2,Imp [] e.1 e.2:=apI j3_0 ai1
def g2_0:List (ℕ × ℕ):=[(3,7),(5,7),(6,7),(9,7),(10,7),(12,6),(17,7),(18,7),(20,7),(24,7),(33,7),(34,7),(36,7),(40,7),(48,7),(65,7),(66,7),(68,6),(72,6),(80,7),(96,7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def k2_0:g2_0.all (fun e => okE [] (pr ac2 e.1) e) = true:=by decide +kernel
lemma j2_0:∀ e ∈ g2_0,Imp [] e.1 e.2:=okAll k2_0 ai2
def ac3:List (ℕ × ℕ):=g2_0 ++ ac2
lemma ai3:∀ e ∈ ac3,Imp [] e.1 e.2:=apI j2_0 ai2
def g1_0:List (ℕ × ℕ):=[(1,10),(2,10),(4,10),(8,10),(16,10),(32,10),(64,9)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def k1_0:g1_0.all (fun e => okE [] (pr ac3 e.1) e) = true:=by decide +kernel
lemma j1_0:∀ e ∈ g1_0,Imp [] e.1 e.2:=okAll k1_0 ai3
def ac4:List (ℕ × ℕ):=g1_0 ++ ac3
lemma ai4:∀ e ∈ ac4,Imp [] e.1 e.2:=apI j1_0 ai3
def m0_0:List (ℕ × ℕ × ℕ):=[(0,FF,1),(1,FF,1),(2,FF,1),(3,FF,1),(4,FF,1),(5,FF,1),(6,FF,1),(7,FF,1),(8,FF,1),(9,FF,1),(10,FF,1),(11,FF,1),(12,FF,1)]
noncomputable def initL:Nat:=AA
noncomputable def initM:Nat:=Nat.lor (Nat.lor AA FPM) (Nat.shiftLeft AA NN)
noncomputable def initG:Nat:=(List.foldr (fun a b => a + b * 1000000000000000000) 0 [623206300500902416,586501818987791009,983013849822025310,27829622366090])
noncomputable def initW0:W:=⟨rawP.getD 6 0,(List.foldr (fun a b => a + b * 1000000000000000000) 0 [120334134919823360,830120494839523312,855250304338135712,1737652864367]),0,(List.foldr (fun a b => a + b * 1000000000000000000) 0 [120334134919823360,830120494839523312,855250304338135712,1737652864367]),3⟩
noncomputable def initW1:W:=⟨rawP.getD 4 0,(List.foldr (fun a b => a + b * 1000000000000000000) 0 [74063309805715456,830425468208864597,383718679226926389,54354680916]),0,(List.foldr (fun a b => a + b * 1000000000000000000) 0 [74063309805715456,830425468208864597,383718679226926389,54354680916]),3⟩
noncomputable def initW2:W:=⟨rawP.getD 1 0,(List.foldr (fun a b => a + b * 1000000000000000000) 0 [359567522738208800,717711943750158483,785985766192984993,1686695200258]),0,(List.foldr (fun a b => a + b * 1000000000000000000) 0 [359567522738208800,717711943750158483,785985766192984993,1686695200258]),3⟩
noncomputable def initW3:W:=⟨rawP.getD 5 0,(List.foldr (fun a b => a + b * 1000000000000000000) 0 [228346779924692992,154599939986577495,99463365618252235,1686642221471]),0,(List.foldr (fun a b => a + b * 1000000000000000000) 0 [228346779924692992,154599939986577495,99463365618252235,1686642221471]),3⟩
noncomputable def initW4:W:=⟨rawP.getD 2 0,(List.foldr (fun a b => a + b * 1000000000000000000) 0 [679793644683396096,282372146581158413,547116230740940654,52709176360]),0,(List.foldr (fun a b => a + b * 1000000000000000000) 0 [679793644683396096,282372146581158413,547116230740940654,52709176360]),3⟩
noncomputable def initW5:W:=⟨rawP.getD 3 0,(List.foldr (fun a b => a + b * 1000000000000000000) 0 [568352024878940160,516421932309839646,507766106047361665,1686693643537]),0,(List.foldr (fun a b => a + b * 1000000000000000000) 0 [568352024878940160,516421932309839646,507766106047361665,1686693643537]),3⟩
noncomputable def initW6:W:=⟨rawP.getD 0 0,(List.foldr (fun a b => a + b * 1000000000000000000) 0 [911285340439314433,390223550795055862,855347881572293845,52657752773]),0,(List.foldr (fun a b => a + b * 1000000000000000000) 0 [911285340439314433,390223550795055862,855347881572293845,52657752773]),3⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initL_eq:lz 0 = initL:=by rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initM_eq:mz 0 = initM:=by rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initG_eq:pL ((pr ac4 0).map fun _ => 16) = initG:=by rfl

noncomputable section cutCore
noncomputable def topCut (F G:Nat → Nat → Nat → List W → Bool) (l m g K H ph k t z:ℕ) (v:List W):Bool :=
  Bool.rec (motive:=fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive:=fun _ => Bool) (Bool.rec (motive:=fun _ => Bool) false (mv F l m g k t z v y) (Nat.beq ph 1)) true
      (node (G (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
noncomputable def startCut (F G:Nat → Nat → Nat → List W → Bool) (l m g B K t p H ph:ℕ) (v:List W):Bool :=
  Bool.rec (motive:=fun _ => Bool) false (Bool.rec (motive:=fun _ => Bool) false
    (child (fun z r => topCut F G l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
end cutCore
noncomputable def chkCut (F G:Nat → Nat → Nat → List W → Bool) (E Q:List (ℕ × ℕ)) (Z K t H ph:ℕ):Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startCut F G l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)

lemma chkCut_eq (E Q:List (ℕ × ℕ)) (Z K t H ph:ℕ) :
    chkCut (look (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K)
      (look1 (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K K) E Q Z K t H ph =
      chk E Q Z K t H ph:=by
  simp only [chkCut,chk,frc_eq,st_eq,startCut,startv,topCut,topC]

lemma orFold_append {α:Type} (p:α → Bool) (xs ys:List α) :
    List.rec false (fun a _ ih => Bool.rec ih true (p a)) (xs ++ ys) =
      (List.rec false (fun a _ ih => Bool.rec ih true (p a)) xs ||
        List.rec false (fun a _ ih => Bool.rec ih true (p a)) ys):=by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.cons_append]
    rw [ih]
    cases p a <;> rfl

lemma nots_append (f:Nat → Nat → List W → Bool) (m g e n z q:Nat)
    (v xs ys:List W) :
    nots f m g e n z q v (xs ++ ys) =
      (nots f m g e n z q v xs || nots f m g e n z q v ys):=by
  exact orFold_append _ xs ys

lemma nots_false_of_singletons (f:Nat → Nat → List W → Bool) (m g e n z q:Nat)
    (v xs:List W) (h:∀ w ∈ xs,nots f m g e n z q v [w] = false) :
    nots f m g e n z q v xs = false:=by
  revert h
  induction xs with
  | nil => intro _; rfl
  | cons a xs ih =>
    intro h
    have ha:=h a (List.mem_cons_self)
    have hr:=ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    change nots f m g e n z q v ([a] ++ xs) = false
    rw [nots_append,ha,hr]
    rfl

abbrev WKey:=Nat × Nat × Nat × Nat × Nat
abbrev CutState:=Nat × Nat × Nat × List W
abbrev CutKey:=Nat × Nat × Nat × List WKey

noncomputable def wKey (w:W):WKey:=(w.s,w.a,w.b,w.c,w.r)
noncomputable def wUnkey (w:WKey):W:=⟨w.1,w.2.1,w.2.2.1,w.2.2.2.1,w.2.2.2.2⟩
noncomputable def cutKey (s:CutState):CutKey:=(s.1,s.2.1,s.2.2.1,s.2.2.2.map wKey)
noncomputable def cutUnkey (s:CutKey):CutState:=(s.1,s.2.1,s.2.2.1,s.2.2.2.map wUnkey)

lemma wUnkey_key (w:W):wUnkey (wKey w) = w:=by cases w; rfl
lemma cutUnkey_key (s:CutState):cutUnkey (cutKey s) = s:=by
  rcases s with ⟨k,t,z,v⟩
  simp only [cutUnkey,cutKey,List.map_map,Function.comp_def,wUnkey_key]
  change (k,t,z,List.map id v) = (k,t,z,v)
  rw [List.map_id]

lemma cutKey_injective:Function.Injective cutKey:=by
  intro s t h
  have h':=congrArg cutUnkey h
  simpa only [cutUnkey_key] using h'

noncomputable def patchCut (F:Nat → Nat → Nat → List W → Bool) (states:List CutState)
    (k t z:Nat) (v:List W):Bool :=
  if cutKey (k,t,z,v) ∈ states.map cutKey then false else F k t z v

lemma patchCut_eq (F:Nat → Nat → Nat → List W → Bool) (states:List CutState)
    (h:∀ s ∈ states,F s.1 s.2.1 s.2.2.1 s.2.2.2 = false) :
    patchCut F states = F:=by
  funext k t z v
  unfold patchCut
  split_ifs with hm
  · obtain ⟨s,hs,he⟩:=List.mem_map.1 hm
    have he:=cutKey_injective he
    subst s
    exact (h (k,t,z,v) hs).symm
  · rfl

noncomputable section lookCutCore
noncomputable def lookCut (F:Nat → Nat → Nat → List W → Bool) (l m g k t z:Nat)
    (v:List W):Bool :=
  Bool.rec (motive:=fun _ => Bool)
    (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mv F l m g k t z v y))
    true (Nat.ble v.length 1)

noncomputable def look1Cut (F G:Nat → Nat → Nat → List W → Bool) (l m g k t z:Nat)
    (v:List W):Bool :=
  Bool.rec (motive:=fun _ => Bool)
    (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive:=fun _ => Bool) (mv F l m g k t z v y) true
        (node (G (Nat.sub k 1) t) (pos t) l m g
          (Nat.sub (Nat.sub k t) y) v.length z v pairsS)))
    true (Nat.ble v.length 1)
end lookCutCore

lemma lookCut_eq (l m g fuel k t z:Nat) (v:List W) :
    lookCut (look l m g fuel) l m g k t z v =
      look l m g (fuel + 1) k t z v:=by rfl

lemma look1Cut_eq (l m g K fuel k t z:Nat) (v:List W) :
    look1Cut (look l m g K) (look1 l m g K fuel) l m g k t z v =
      look1 l m g K (fuel + 1) k t z v:=by rfl

noncomputable def patchBudget (F:Nat → Nat → Nat → List W → Bool) (rows:Nat → List CutState)
    (k t z:Nat) (v:List W):Bool:=patchCut F (rows z) k t z v

lemma patchBudget_eq (F:Nat → Nat → Nat → List W → Bool) (rows:Nat → List CutState)
    (h:∀ z,∀ s ∈ rows z,F s.1 s.2.1 s.2.2.1 s.2.2.2 = false) :
    patchBudget F rows = F:=by
  funext k t z v
  exact congrArg (fun J => J k t z v) (patchCut_eq F (rows z) (h z))

lemma bucket_index_bound (a:Array (List Nat)) (n:Nat)
    (ha:a.all (fun xs => xs.all (fun j => decide (j < n))) = true)
    (b j:Nat) (hj:j ∈ a.getD b []):j < n:=by
  by_cases hb:b < a.size
  · have h:=Array.all_eq_true.1 ha b hb
    have hj':j ∈ a[b]:=by simpa [Array.getD,hb] using hj
    exact of_decide_eq_true (List.all_eq_true.1 h j hj')
  · simp [Array.getD,hb] at hj

lemma array_all_getD {α:Type} (a:Array α) (p:α → Bool) (d:α)
    (ha:a.all p = true) (hd:p d = true) (i:Nat):p (a.getD i d) = true:=by
  by_cases hi:i < a.size
  · simpa [Array.getD,hi] using Array.all_eq_true.1 ha i hi
  · simpa [Array.getD,hi] using hd

lemma chunk_bucket_index_bound (a:Array (Array (List Nat))) (n:Nat)
    (ha:a.all (fun c => c.all (fun xs => xs.all (fun j => decide (j < n)))) = true)
    (b j:Nat) (hj:j ∈ (a.getD (b / 64) #[]).getD (b % 64) []):j < n:=by
  have hc:=array_all_getD a (fun c => c.all (fun xs => xs.all (fun j => decide (j < n))))
    #[] ha (by simp) (b / 64)
  exact bucket_index_bound _ _ hc _ _ hj

noncomputable def strictSt (n:Nat) (f:Nat → Bool):Bool :=
  Nat.rec (motive:=fun _ => Bool) (f 0) (fun m _ => f (Nat.succ m)) n
lemma strictSt_eq (n:Nat) (f:Nat → Bool):strictSt n f = f n:=by
  cases n <;> rfl
noncomputable def frcAll (v:List W):(List W → Bool) → Bool :=
  List.rec (motive:=fun _ => (List W → Bool) → Bool) (fun h => h [])
    (fun w _ ih h => strictSt w.s fun s => strictSt w.a fun a => strictSt w.b fun b =>
      strictSt w.c fun c => strictSt w.r fun tag => ih fun r => h (⟨s,a,b,c,tag⟩ :: r)) v
lemma frcAll_eq (v:List W):∀ h,frcAll v h = h v:=by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change strictSt w.s (fun s => strictSt w.a fun a => strictSt w.b fun b =>
      strictSt w.c fun c => strictSt w.r fun tag => frcAll v fun r => h (⟨s,a,b,c,tag⟩ :: r)) = _
    simp only [strictSt_eq]
    rw [ih]

noncomputable def binChunkGet {α:Type} (rows:Array (Array α)) (i:ℕ) (fallback:α):α :=
  (rows.getD (i / 64) #[]).getD (i % 64) fallback

noncomputable def binDefaultW:W:=⟨0,0,0,0,0⟩

noncomputable def binInitial:Array W:=#[initW0,initW1,initW2,initW3,initW4,initW5,initW6]

set_option maxRecDepth 100000 in
noncomputable def binOpsChunks:Array (Array ℕ):=#[
  #[0,4,8,12,16,20,24,1,5,9,13,17,21,25,4098,4099,8194,8195,12290,12291,16386,16387,20482,20483,24578,24579,8198,8199,12294,12295,16390,16391,20486,20487,24582,24583,12298,12299,16394,16395,20490,20491,24586,24587,16398,16399,20494,20495,24590,24591,20498,20499,24594,24595,24598,24599,61,69,77,85,93,101,109,117],
  #[125,133,141,149,157,165,173,181,189,197,205,213,221,32770,36866,40962,45058,49154,53250,106499,110594,110595,114691,118786,118787,122883,126978,126979,131075,135170,135171,139267,143362,143363,147459,151554,151555,155651,159746,159747,163843,167938,167939,172035,176130,176131,180227,184322,184323,188419,192514,192515,196611,200706,200707,204803,208898,208899,212995,217090,217091,221187,225282,225283],
  #[28678,28679,36870,40966,45062,49158,53254,65543,69638,73735,77830,81927,86022,90119,94214,98311,102406,147463,151558,151559,155655,159750,159751,163847,167942,167943,172039,176134,176135,180231,184326,184327,188423,192518,192519,196615,200710,200711,204807,208902,208903,212999,217094,217095,221191,225286,225287,28682,28683,32778,40970,45066,49162,53258,57355,61450,73739,77834,81931,86026,90123,94218,98315,102410],
  #[114699,118794,122891,126986,131083,135178,139275,143370,180235,184330,184331,188427,192522,192523,196619,200714,200715,204811,208906,208907,213003,217098,217099,221195,225290,225291,28686,28687,32782,36878,45070,49166,53262,57359,61454,65551,69646,81935,86030,90127,94222,98319,102414,106511,110606,122895,126990,131087,135182,139279,143374,155663,159758,163855,167950,172047,176142,204815,208910,208911,213007,217102,217103,221199],
  #[225294,225295,28690,28691,32786,36882,40978,49170,53266,57363,61458,65555,69650,73747,77842,90131,94226,98323,102418,106515,110610,114707,118802,131091,135186,139283,143378,147475,151570,163859,167954,172051,176146,188435,192530,196627,200722,221203,225298,225299,28694,28695,32790,36886,40982,45078,53270,57367,61462,65559,69654,73751,77846,81943,86038,98327,102422,106519,110614,114711,118806,122903,126998,139287],
  #[143382,147479,151574,155671,159766,172055,176150,180247,184342,196631,200726,213015,217110,28698,28699,32794,36890,40986,45082,49178,57371,61466,65563,69658,73755,77850,81947,86042,90139,94234,106523,110618,114715,118810,122907,127002,131099,135194,147483,151578,155675,159770,163867,167962,180251,184346,188443,192538,204827,208922,61470,69662,77854,86046,94238,102430,106527,110622,110623,114719,118814,118815,122911,127006],
  #[127007,131103,135198,135199,139295,143390,143391,147487,151582,151583,155679,159774,159775,163871,167966,167967,172063,176158,176159,180255,184350,184351,188447,192542,192543,196639,200734,200735,204831,208926,208927,213023,217118,217119,221215,225310,225311,69666,77858,86050,94242,102434,151586,159778,167970,176162,184354,192546,200738,208930,217122,225314,61478,77862,86054,94246,102438,118822,127014,135206,143398,184358,192550,200742],
  #[208934,217126,225318,61482,69674,86058,94250,102442,110634,127018,135210,143402,159786,167978,176170,208938,217130,225322,61486,69678,77870,94254,102446,110638,118830,135214,143406,151598,167982,176174,192558,200750,225326,61490,69682,77874,86066,102450,110642,118834,127026,143410,151602,159794,176178,184370,200754,217138,61494,69686,77878,86070,94262,110646,118838,127030,135222,151606,159798,167990,184374,192566,208950,1481],
  #[1485,1489,1493,1497,1501,1509,1513,1521,1525,1533,1537,1545,1549,1557,1561,1569,1573,1581,1585,1593,1597,1605,1609,1617,1621,1629,1633,1641,1645,1653,1657,1665,1669,1677,1681,1685,1689,1693,1697,1701,1705,1709,1713,1717,1721,1725,1729,1733,1737,1741,1745,1749,1753,1757,1761,1765,1769,1773,1777,1781,1785,1789,1793,1797],
  #[1801,1805,1809,1813,1817,1821,1825,1829,1833,1837,1841,1845,1849,1853,1857,1861,1865,1869,1873,1877,1881,1885,1889,1893,1897,1901,1905,1909,1913,1917,1921,1925,1929,1933,1937,1941,1945,1949,1953,1957,1961,1965,1969,1973,1977,1981,1985,1989,1993,1997,2001,2005,2009,2013,2017,2021,2025,2029,2033,2037,2041,229383,233478,237574],
  #[241670,245766,249862,253959,258055,262151,266247,270343,274438,278534,282630,286726,290822,294918,299014,303110,307206,311302,229386,233483,237578,241674,245770,249866,253963,258058,262154,266250,270346,274443,278539,282635,286731,290826,294922,299018,303114,307210,311306,229390,233486,237583,241678,245774,249870,253966,258063,262158,266254,270350,274447,278542,282638,286734,290831,294927,299023,303118,307214,311310,229394,233490,237586,241683],
  #[245778,249874,253970,258066,262163,266258,270354,274450,278547,282642,286738,290835,294930,299026,303123,307219,311314,229398,233494,237590,241686,245783,249878,253974,258070,262166,266263,270358,274454,278550,282647,286742,290838,294935,299030,303127,307222,311319,229402,233498,237594,241690,245786,249883,253978,258074,262170,266266,270363,274458,278554,282650,286747,290842,294938,299035,303130,307227,311323]
]
noncomputable def binOps:Array ℕ:=(binOpsChunks.toList.flatMap Array.toList).toArray

noncomputable def binNeg (a:W):W:=⟨a.s ^^^ initM,a.b,a.a,a.c,0⟩
noncomputable def binAnd (a b:W):W :=
  ⟨a.s &&& b.s,a.a ||| b.a,a.b &&& b.b,(a.a ||| b.a) ||| (a.b &&& b.b),0⟩
noncomputable def binOr (a b:W):W :=
  ⟨a.s ||| b.s,a.a &&& b.a,a.b ||| b.b,(a.a &&& b.a) ||| (a.b ||| b.b),0⟩
noncomputable def binWRec:ℕ → ℕ → W
  | 0,i => binInitial.getD i binDefaultW
  | n + 1,i =>
    let p:=binChunkGet binOpsChunks i 0
    if p % 4 = 0 then binInitial.getD ((p / 4) % 1024) binDefaultW
    else if p % 4 = 1 then binNeg (binWRec n ((p / 4) % 1024))
    else if p % 4 = 2 then binAnd (binWRec n ((p / 4) % 1024)) (binWRec n (p / 4096))
    else binOr (binWRec n ((p / 4) % 1024)) (binWRec n (p / 4096))
noncomputable def binW (i:ℕ):W:=binWRec 3 i

set_option maxRecDepth 100000 in
noncomputable def binZDataChunks:Array (Array ℕ):=#[
  #[0x343121230220012,0x421100114223422,0x2220000423223,0x333222240210022,0x431100113224411,0x2220000432222,0x443222240120022,0x531100113113322,0x2330000423333,0x433212130220021,0x431100114224322,0x3320000533332,0x243020221220002,0x312211124222422,0x11111101313113,0x23022421200202,0x112013122242422,0x11111103113113,0x243240221022002,0x310231122220242,0x11111121113313,0x25242421002202,0x130033122220222,0x11111123113113,0x223022201220200,0x112213104242224,0x11111301313133,0x134132420211202,0x221012013342423,0x11121102223124,0x124233430201212,0x231012012343412,0x11121102232123,0x441222241020022,0x510221222022222,0x11130121311333,0x223224441000222,0x330023222022202,0x11130123311133,0x233123430210212,0x321012013243413,0x11131102322134,0x241022221220002,0x312221024222422,0x11132101311133,0x223022421200202,0x312023022242402,0x11132103311133,0x223002221220200,0x312223004242224,0x11132301313133,0x135242420112202,0x230022012331333,0x11221112124224,0x125343430102212,0x240022011332322,0x11221112133223,0x224334440101222,0x340012111233312,0x11230112232233,0x333224440110222,0x430012112133313,0x11240112322244,0x225222201022200],
  #[0x130233102220244,0x11311321115333,0x443222241020022,0x531211222002222,0x11330111313333,0x223224441000222,0x331013220022222,0x11330113113333,0x423224221020220,0x331213202022024,0x11330311313353,0x423204221020220,0x330223202022224,0x11330321313353,0x235343430012212,0x340022011221233,0x11331112124334,0x243242221022002,0x331231022200242,0x11332111113333,0x225242421002202,0x331033020220222,0x11332113113333,0x225222221022200,0x331233002220044,0x11332311115333,0x334334440011222,0x440012111122223,0x11340112223344,0x243131320221102,0x311111014332433,0x12121101323224,0x342122330220112,0x411111014233423,0x12131101422234,0x244241320122102,0x320121013321343,0x12221111224324,0x234122310221201,0x221112004342334,0x12221201324234,0x333113320220211,0x321112004243324,0x12231201423244,0x442223340120122,0x520111113123323,0x12240111422344,0x235232310122201,0x230122003331244,0x12321211225334,0x344342330022112,0x430121012211243,0x12331111224434,0x443333340021122,0x530111112112233,0x12340111323444,0x433214330120221,0x430112103133224,0x12340211423354,0x335333320022211,0x340122002221144,0x12431211225444,0x434324330021221,0x440112102122134],
  #[0x12440211324454,0x342231230221012,0x411111014323432,0x13121101432323,0x343341230122012,0x420121013312342,0x13221111333423,0x442332240121022,0x520111113213332,0x13230111432433,0x324213210221210,0x231112004343234,0x13321201434343,0x325323210122210,0x240122003332144,0x13421211335443,0x424314220121220,0x340112103233134,0x13430211434453,0x224334442201222,0x343104332344412,0x22230204342233,0x244132420221202,0x321112014342434,0x22231202324235,0x234233430211212,0x331112013343423,0x22231202333234,0x343123430220212,0x421112014243424,0x22241202423245,0x344133430221212,0x421112014343434,0x22241202424245,0x245242420122202,0x330122013331344,0x22331212225335,0x235343430112212,0x340122012332333,0x22331212234334,0x344233430121212,0x430112113232334,0x22340212324345,0x334334440111222,0x440112112233323,0x22340212333344,0x344233430121212,0x431112013232334,0x22341202324345,0x344233430121212,0x430122013232334,0x22341212324345,0x443224440120222,0x530112113133324,0x22350212423355,0x345343430022212,0x440122012221244,0x22441212225445,0x345343430122212,0x440122013331344,0x22441212225445,0x444334440021222,0x540112112122234,0x22450212324455],
  #[0x444334440121222,0x540112113133334,0x22450212424455,0x343232330221112,0x421112014333433,0x23231202433334,0x334223320221211,0x331112014343334,0x23331202434344,0x344342330122112,0x430122013322343,0x23331212334434,0x443333340121122,0x530112113223333,0x23340212433444,0x335333320122211,0x340122013332244,0x23431212335444,0x434324330121221,0x440112113233234,0x23440212434454,0x442332242221022,0x523302334324432,0x24230202542433,0x424314222221220,0x343304314344234,0x24430402544453,0x444334440221222,0x541102114344434,0x24450202544455,0x23122421200202,0x122213022242402,0x30011303121013,0x241120223020002,0x302433242020222,0x30011323101213,0x23122423000202,0x122235242020202,0x30011325101013,0x25242421002202,0x130233020221222,0x30111313023113,0x243020223020002,0x312433242001222,0x30111313203113,0x23022423000202,0x112235240021222,0x30111315003113,0x223022203020200,0x112435222021024,0x30111513203133,0x243022421020202,0x310213222120224,0x30130313103135,0x223224441000222,0x330213220122202,0x30130313121133,0x243022421020202,0x310233022021224,0x30131313203135,0x241022223020002,0x312433242100222,0x30132313101133,0x223022423000202],
  #[0x312235240120202,0x30132315101133,0x223002223020200,0x312435222120024,0x30132513103133,0x223102203020200,0x122435222020224,0x30211523103233,0x243122421020202,0x322213022020224,0x30231303103235,0x243022421020202,0x310223022022224,0x31130303313135,0x243022421020202,0x310213122220224,0x31131303113135,0x344033431221212,0x412223124343434,0x31142303414145,0x244132421121202,0x321223123231334,0x31231313214235,0x343123431120212,0x421223123132324,0x31241313313245,0x243222421020202,0x331213022020224,0x31330313113335,0x344233431021212,0x431223122121234,0x31341313214345,0x345343431122212,0x441233123330344,0x31442323115445,0x444334441121222,0x541223223033334,0x31450323414455,0x241120221220002,0x302213024222422,0x32011303321213,0x243240221022002,0x310233022201242,0x32111313223313,0x441222241020022,0x510213222102222,0x32130313321333,0x223102201220200,0x122213024242224,0x32211303323233,0x225222201022200,0x130233022221044,0x32311313225333,0x423204221020220,0x330213222122024,0x32330313323353,0x334334442211222,0x443204333344423,0x33340304443344,0x443333342221122,0x533303334334433,0x34340303543444,0x434324332221221,0x443304324344334],
  #[0x34440403544454,0x444334441221222,0x542203224344434,0x34450303544455,0x243122422120202,0x322324133131324,0x41231414213235,0x244132422021202,0x321334132121234,0x41231414214235,0x343123432020212,0x421324232121224,0x41241414213245,0x244132422221202,0x323314134342434,0x42231404324235,0x343123432220212,0x423324034243424,0x42242404423245,0x245242422122202,0x330344133331344,0x42331424225335,0x443224442120222,0x530324333133324,0x42350424423355,0x345343432022212,0x441344032221244,0x42442414225445,0x444334442021222,0x541314332122234,0x42450414324455,0x344233432221212,0x433304234343434,0x43340404434345,0x443224442220222,0x533304334244424,0x43350404533355,0x444334442121222,0x542304333233334,0x43450404434455,0x444334442221222,0x543304334344434,0x44450404544455,0x344033433021212,0x412445342121234,0x50142515204145,0x244132423121202,0x323445243031334,0x50231525204235,0x343123433120212,0x423435343130324,0x50242525103245,0x223222241200022,0x332111222224400,0x101111011331111,0x223442241002022,0x330131220222220,0x101111031131311,0x203224221200220,0x132113202244202,0x101111211331131,0x23242221202002,0x132131022422420,0x101113011131111],
  #[0x5222221202200,0x132133002442222,0x101113211133111,0x205424221002220,0x150133200222222,0x101311231133331,0x134241320212102,0x221021013432432,0x102112011233213,0x124342330202112,0x231021012433421,0x102112011242212,0x223333340201122,0x331011112334411,0x102121011341222,0x332223340210122,0x421011113234412,0x102131011431233,0x125232310212201,0x131022003442333,0x102212111234223,0x115333320202211,0x141022002443322,0x102212111243222,0x224443340102122,0x340021111323321,0x102221021242322,0x214324330201221,0x241012102344312,0x102221111342232,0x323214330210221,0x331012103244313,0x102231111432243,0x215434330102221,0x250022101333222,0x102321121243332,0x334443340012122,0x440021111212232,0x102331021233433,0x325434330012221,0x350022101222133,0x102431121234443,0x221222241200022,0x312012222224420,0x103111012331311,0x223442241002022,0x330032222202220,0x103111032331311,0x421222021220020,0x312212204224222,0x103111210531331,0x233341230212012,0x321021013423431,0x103112011342312,0x223240221202002,0x312032022422420,0x103113012331311,0x223220021222000,0x312232004422242,0x103113210333311,0x332332240211022,0x421011113324421,0x103121011441322,0x234231210222101],
  #[0x221121004432343,0x103212110334323,0x333442240112022,0x430021112313331,0x103221021342422,0x432213230220121,0x421111104234323,0x103231110532343,0x423202021220020,0x332211214224222,0x103311110533331,0x203204221200220,0x132013212244222,0x103311112333331,0x423422021022020,0x330231212222042,0x103311130333531,0x205424221002220,0x150033212222022,0x103311132333331,0x423422021022020,0x330232202202242,0x103311230333531,0x215323210212210,0x141022003443233,0x103312111344332,0x223222001222000,0x132231014422242,0x103313110333331,0x205222201202200,0x132033012442222,0x103313112333331,0x314314220211220,0x241012103344223,0x103321111443342,0x315424220112220,0x250022102333133,0x103421121344442,0x434433230022121,0x440121102212143,0x103431120334543,0x333331120222011,0x321121004423342,0x104212110443422,0x432322130221021,0x421111104324332,0x104221110542432,0x324322110222110,0x231121004433243,0x104312110444432,0x423313120221120,0x331111104334233,0x104321110543442,0x433432130122021,0x430121103313242,0x104321120443532,0x424423120122120,0x340121103323143,0x104421120444542,0x123020223200002,0x214233242222400,0x110003113211001,0x123240223002002,0x212253240220220],
  #[0x110003133011201,0x103022203200200,0x14235222242202,0x110003313211021,0x23022421200202,0x112013222242412,0x110011113112013,0x221222243000022,0x312233440022210,0x110011133110211,0x21022223200002,0x114233242222410,0x110013113110011,0x3002223200200,0x114235222242212,0x110013313112011,0x123022421200202,0x212033022242402,0x110023113211023,0x25242421002202,0x130033221220222,0x110111133013113,0x223222243000022,0x332233441002200,0x110111133211111,0x203224223000220,0x132235421022002,0x110111333211131,0x23242223002002,0x132253241200220,0x110113133011111,0x5222223002200,0x132255221220022,0x110113333013111,0x223224441000222,0x330033221022202,0x110131133211133,0x105222203002200,0x32255220220222,0x110203333013221,0x203204223000220,0x132235420022212,0x110211333112231,0x125242421002202,0x232033020220222,0x110223113013223,0x223224441000222,0x332013220022212,0x110231113112233,0x23241221202002,0x122231022422420,0x111003111131101,0x21021223200002,0x104233242222420,0x111003113111101,0x23241223002002,0x122253242200220,0x111003133111101,0x221021003220000,0x104433224222222,0x111003311311121,0x242020221220002,0x302211224222422,0x111011111312113],
  #[0x222222241200022,0x322211222224400,0x111011111330111,0x222222243000022,0x322233442002200,0x111011133310111,0x222020223200002,0x304233242222400,0x111013113310111,0x222000023220000,0x304433224222222,0x111013311312111,0x241021221220002,0x302231024222422,0x111023111311123,0x5222211202200,0x32233002442222,0x111103311133111,0x223000013220000,0x214433224222222,0x111103311313111,0x3002213200200,0x14235222242222,0x111103313113111,0x223220013022000,0x212453222220042,0x111103331113311,0x5222213002200,0x32255222220022,0x111103333113111,0x243020221220002,0x312211224222422,0x111111111313113,0x223222241200022,0x332211222224400,0x111111111331111,0x23022421200202,0x112013222242422,0x111111113113113,0x243240221022002,0x310231222210242,0x111111131113313,0x243240221022002,0x310231222220242,0x111111131113313,0x223442241002022,0x330231220212220,0x111111131131311,0x223442241002022,0x330231220222220,0x111111131131311,0x221222243000022,0x312233440012220,0x111111133111311,0x221222243000022,0x312233440022220,0x111111133111311,0x25242421002202,0x130033222220222,0x111111133113113,0x223222243000022,0x332233442002200,0x111111133311111,0x223012201220200],
  #[0x112213204242224,0x111111311313133,0x223022201220200,0x112213204242224,0x111111311313133,0x203214221200220,0x132213202244202,0x111111311331131,0x203224221200220,0x132213202244202,0x111111311331131,0x421222023020020,0x312433422012022,0x111111331311331,0x421212023020020,0x312433422022022,0x111111331311331,0x421222023020020,0x312433422022022,0x111111331311331,0x203214223000220,0x132235422022002,0x111111333311131,0x203224223000220,0x132235422022002,0x111111333311131,0x35343430212212,0x141022013443433,0x111112112144114,0x23242221202002,0x132231022422420,0x111113111131111,0x21022223200002,0x114233242222420,0x111113113111111,0x223020223200002,0x314233242222400,0x111113113311111,0x23242223002002,0x132253242200220,0x111113133111111,0x223240223002002,0x312253240210220,0x111113133111311,0x223240223002002,0x312253240220220,0x111113133111311,0x5222221202200,0x132233002442222,0x111113311133111,0x221012003220000,0x114433224222222,0x111113311311131,0x221022003220000,0x114433224222222,0x111113311311131,0x223000023220000,0x314433224222222,0x111113311313111,0x3002223200200,0x114235222242222,0x111113313113111,0x203012203200200,0x114235222242202],
  #[0x111113313311131,0x203022203200200,0x114235222242202,0x111113313311131,0x223220023022000,0x312453222210042,0x111113331113311,0x223220023022000,0x312453222220042,0x111113331113311,0x5222223002200,0x132255222220022,0x111113333113111,0x223002211220200,0x212233004242224,0x111123311313133,0x441222241020022,0x510231222012222,0x111131131311333,0x441222241020022,0x510231222022222,0x111131131311333,0x223224441000222,0x330033222022202,0x111131133311133,0x241022221220002,0x312231024222422,0x111133111311133,0x223022421200202,0x312033022242402,0x111133113311133,0x223002221220200,0x312233004242224,0x111133311313133,0x334334440211222,0x441012113344403,0x111141112441144,0x223221003022000,0x122453222200242,0x111203331113321,0x422202023020020,0x322433422002222,0x111211331312331,0x243241221022002,0x322231022200242,0x111223111113323,0x442222241020022,0x522211222002222,0x111231111312333,0x225222201022200,0x130233202220144,0x111311331115333,0x225222201022200,0x130233202220244,0x111311331115333,0x205424221002220,0x150233200222122,0x111311331133331,0x205424221002220,0x150233200222222,0x111311331133331,0x423202023020020,0x332433422002122,0x111311331313331],
  #[0x423202023020020,0x332433422002222,0x111311331313331,0x203204223000220,0x132235420022122,0x111311333113331,0x203204223000220,0x132235420022222,0x111311333113331,0x223222003022000,0x132453222200142,0x111313331113331,0x223222003022000,0x132453222200242,0x111313331113331,0x205222203002200,0x132255220220122,0x111313333113331,0x205222203002200,0x132255220220222,0x111313333113331,0x225222211022200,0x232233002220044,0x111323311115333,0x443222241020022,0x532211222002222,0x111331111313333,0x223224441000222,0x332013220022222,0x111331113113333,0x423214221020220,0x332213202022024,0x111331311313353,0x423224221020220,0x332213202022024,0x111331311313353,0x423204221020220,0x330233202022124,0x111331331313353,0x423204221020220,0x330233202022224,0x111331331313353,0x243242221022002,0x332231022200242,0x111333111113333,0x225242421002202,0x332033020220222,0x111333113113333,0x225222221022200,0x332233002220044,0x111333311115333,0x335444440112222,0x450022110333333,0x111441122144444,0x123240221202002,0x212033022422420,0x112003113231201,0x221222241200022,0x312013222224410,0x112011113330211,0x223442241002022,0x330033221202220,0x112111133231311,0x105222201202200],
  #[0x32033022442222,0x112203113233221,0x203204221200220,0x132013222244212,0x112211113332231,0x135242420212202,0x231022013442433,0x112222112234224,0x125343430202212,0x241022012443422,0x112222112243223,0x135343430212212,0x241022013443433,0x112222112244224,0x234233430211212,0x331012113343423,0x112231112333234,0x224334440201222,0x341012112344412,0x112231112342233,0x234233430211212,0x331022013343423,0x112232112333234,0x333224440210222,0x431012113244413,0x112241112432244,0x334334440211222,0x441012113344413,0x112241112442244,0x205424221002220,0x150033221222022,0x112311133233331,0x235343430112212,0x340022112332333,0x112331122234334,0x225444440102222,0x350022111333322,0x112331122243333,0x235343430112212,0x341022012332333,0x112332112234334,0x334334440111222,0x441012112233323,0x112341112333344,0x334334440111222,0x440022112233323,0x112341122333344,0x335444440012222,0x450022111222233,0x112441122234444,0x335444440112222,0x450022111333333,0x112441122244444,0x223220011222000,0x212233004422242,0x113103311333311,0x221222241200022,0x312013222224420,0x113111113331311,0x223442241002022,0x330033222202220,0x113111133331311,0x421212021220020,0x312213204224222],
  #[0x113111311531331,0x421222021220020,0x312213204224222,0x113111311531331,0x223240221202002,0x312033022422420,0x113113113331311,0x223220021222000,0x312233004422242,0x113113311333311,0x223221001222000,0x122231024422242,0x113203111333321,0x422202021220020,0x322211224224222,0x113211111532331,0x244241320222102,0x321121014432443,0x113222111334324,0x234342330212112,0x331121013433432,0x113222111343323,0x234342330212112,0x331022013433432,0x113222112343323,0x343232330221112,0x421111114333433,0x113231111433334,0x333333340211122,0x431111113334422,0x113231111442333,0x333333340211122,0x431012113334422,0x113231112442333,0x343232330221112,0x421121014333433,0x113232111433334,0x442223340220122,0x521111114234423,0x113241111532344,0x423202021220020,0x332211224224222,0x113311111533331,0x203204221200220,0x132013222244222,0x113311113333331,0x423422021022020,0x330231222212042,0x113311131333531,0x423422021022020,0x330231222222042,0x113311131333531,0x205424221002220,0x150033222222022,0x113311133333331,0x423422021022020,0x330233202202142,0x113311331333531,0x423422021022020,0x330233202202242,0x113311331333531,0x223222001222000,0x132231024422242,0x113313111333331],
  #[0x205222201202200,0x132033022442222,0x113313113333331,0x225333320212211,0x241022013443333,0x113322112344333,0x235232310222201,0x231122004442344,0x113322211335334,0x225333320212211,0x241122003443333,0x113322211344333,0x443222240220022,0x531111114224422,0x113331111533333,0x223224440200222,0x331012112244422,0x113331112333333,0x324324330211221,0x341012113344323,0x113331112443343,0x443442240022022,0x530121112222242,0x113331121333533,0x344342330122112,0x430121113322343,0x113331121334434,0x334443340112122,0x440121112323332,0x113331121343433,0x225444440002222,0x350022112222222,0x113331122333333,0x334443340112122,0x440022112323332,0x113331122343433,0x334223320221211,0x331112104343334,0x113331211434344,0x324324330211221,0x341112103344323,0x113331211443343,0x423224220220220,0x331112104244224,0x113331211533353,0x243242220222002,0x331121014422442,0x113332111333333,0x344342330122112,0x431121013322343,0x113332111334434,0x225242420202202,0x331022012442422,0x113332112333333,0x235343430212212,0x341022013443433,0x113332112344334,0x225222220222200,0x331122004442244,0x113332211335333,0x334223320221211,0x331122004343334,0x113332211434344,0x443333340121122],
  #[0x531111113223333,0x113341111433444,0x334334440211222,0x441012113344423,0x113341112443344,0x443333340121122,0x530121113223333,0x113341121433444,0x433214330220221,0x431112104244324,0x113341211533354,0x325434330112221,0x350022112333233,0x113431122344443,0x335333320122211,0x340122103332244,0x113431221335444,0x325434330112221,0x350122102333233,0x113431221344443,0x335333320122211,0x341122003332244,0x113432211335444,0x444443340022122,0x540121112212243,0x113441121334544,0x335444440112222,0x450022112333333,0x113441122344444,0x434324330121221,0x441112103233234,0x113441211434454,0x434324330121221,0x440122103233234,0x113441221434454,0x425424220022220,0x350122102222244,0x113531221335553,0x435434330022221,0x450122102222144,0x113541221335554,0x344340330222112,0x411121014433443,0x114112111444414,0x441333340221122,0x511111114334433,0x114141111541444,0x343341230222012,0x421121014423442,0x114222111443423,0x344341330222112,0x421121014433443,0x114222111444424,0x442332240221022,0x521111114324432,0x114231111542433,0x442333340221122,0x521111114334433,0x114241111542444,0x334332220222111,0x331121014433343,0x114322111444433,0x334332220222111,0x331122004433343],
  #[0x114322211444433,0x433323230221121,0x431111114334333,0x114331111543443,0x443442240122022,0x530121113313342,0x114331121443533,0x433323230221121,0x431112104334333,0x114331211543443,0x344342330222112,0x431121014433443,0x114332111444434,0x443333340221122,0x531111114334433,0x114341111543444,0x335333300222211,0x141122004443344,0x114412211445444,0x325323210222210,0x241122004443244,0x114422211445443,0x335333310222211,0x241122004443344,0x114422211445444,0x434433230122121,0x440121113323243,0x114431121444543,0x424314220221220,0x341112104344234,0x114431211544453,0x434433230122121,0x440122103323243,0x114431221444543,0x335333320222211,0x341122004443344,0x114432211445444,0x444443340122122,0x540121113303343,0x114441121444544,0x444443340122122,0x540121113313343,0x114441121444544,0x444443340122122,0x540121113323343,0x114441121444544,0x434304330221221,0x441112104344334,0x114441211544454,0x434314330221221,0x441112104344334,0x114441211544454,0x434324330221221,0x441112104344334,0x114441211544454,0x425424220122220,0x350122103333144,0x114531221445553,0x435434330122221,0x450122103333044,0x114541221445554,0x435434330122221,0x450122103333144,0x114541221445554],
  #[0x435434330122221,0x450122103333244,0x114541221445554,0x23222421200202,0x132113022242402,0x121111213131113,0x25242421002202,0x130133020222222,0x121111213133113,0x134132421211202,0x222123123342423,0x121122213223124,0x124233431201212,0x232123122343412,0x121122213232123,0x123123432200212,0x223124232243412,0x121122214222123,0x124132422201202,0x223134132342412,0x121123214222123,0x223224441000222,0x330113220222202,0x121131213131133,0x233123431210212,0x322123123243413,0x121132213322134,0x135242421112202,0x231133122331333,0x121222223124224,0x125343431102212,0x241133121332322,0x121222223133223,0x125343432002212,0x241144231221222,0x121222234123223,0x125242422102202,0x232144131331322,0x121223224123223,0x224334441101222,0x341123221233312,0x121231223232233,0x223224442100222,0x332124331133312,0x121231224222233,0x224334442001222,0x341134331122212,0x121231234222233,0x333224441110222,0x431123222133313,0x121241223322244,0x235343431012212,0x341133121221233,0x121332223124334,0x334334441011222,0x441123221122223,0x121341223223344,0x243131321221102,0x312222124332433,0x122122212323224,0x342121232220012,0x413322234223422,0x122122212422223,0x242131222221002],
  #[0x313332134322432,0x122123212322223,0x342122331220112,0x412222124233423,0x122132212422234,0x125343430202212,0x241122012443422,0x122222212243223,0x343121232220012,0x423322234223422,0x122222212423223,0x123123432200212,0x223124232243422,0x122222214223223,0x244241321122102,0x321232123321343,0x122222222224324,0x343341232022012,0x421342232211242,0x122222232223423,0x343341232022012,0x421342232221242,0x122222232223423,0x125343432002212,0x241144232221222,0x122222234223223,0x234122311221201,0x222223114342334,0x122222312324234,0x323113212220210,0x223324214243224,0x122222412423243,0x323123212220210,0x223324214243224,0x122222412423243,0x243241222122002,0x322342133311342,0x122223222223323,0x224112212221200,0x223334114342234,0x122223412324233,0x125343432202212,0x243144032443422,0x122224214243223,0x244132420221202,0x321112114342434,0x122231212324235,0x224334440201222,0x341112112344412,0x122231212342233,0x224334442201222,0x343114332344412,0x122231214342233,0x442222242120022,0x522322333113322,0x122231222422333,0x442332242021022,0x521332332112232,0x122231232322433,0x442332242021022,0x521332332122232,0x122231232322433,0x224334442001222,0x341134332122212],
  #[0x122231234322233,0x333113321220211,0x322223114243324,0x122232312423244,0x242132222221002,0x323332134322432,0x122233212322233,0x224132422201202,0x323134132342412,0x122233214322233,0x224112222221200,0x323334114342234,0x122233412324233,0x442223341120122,0x521222223123323,0x122241222422344,0x343123430220212,0x421122014243424,0x122242212423245,0x235232311122201,0x231233113331244,0x122322322225334,0x225222212122200,0x232344113331144,0x122323422225333,0x245242420122202,0x330122113331344,0x122331222225335,0x225444440102222,0x350122111333322,0x122331222243333,0x443222242120022,0x532322333113322,0x122331222423333,0x223224442100222,0x332124331133322,0x122331224223333,0x225444442102222,0x350144331333322,0x122331244243333,0x423214222120220,0x332324313133124,0x122331422423353,0x423224222120220,0x332324313133124,0x122331422423353,0x344342331022112,0x431232122211243,0x122332222224434,0x243242222122002,0x332342133311342,0x122333222223333,0x225242422102202,0x332144131331322,0x122333224223333,0x225222222122200,0x332344113331144,0x122333422225333,0x443333341021122,0x531222222112233,0x122341222323444,0x433214331120221,0x431223213133224,0x122341322423354],
  #[0x443224440120222,0x530122113133324,0x122351222423355,0x325323212022210,0x241344212221144,0x122422432225443,0x325323212022210,0x241344212221244,0x122422432225443,0x424314222021220,0x341334312122134,0x122431432324453,0x424314222021220,0x341334312122234,0x122431432324453,0x335333321022211,0x341233112221144,0x122432322225444,0x434324331021221,0x441223212122134,0x122441322324454,0x345343430022212,0x441122012221244,0x122442212225445,0x444334440021222,0x541112112122234,0x122451212324455,0x241220221220002,0x312212024222422,0x123111212331313,0x243240221022002,0x310232022202242,0x123111212333313,0x342231231221012,0x412222124323432,0x123122212432323,0x441222241020022,0x510212222202222,0x123131212331333,0x343341231122012,0x421232123312342,0x123222222333423,0x442332241121022,0x521222223213332,0x123231222432433,0x223202201220200,0x132213014242224,0x123311312333333,0x225222201022200,0x130233012222044,0x123311312335333,0x324213211221210,0x232223114343234,0x123322312434343,0x243222420220202,0x331112014242424,0x123331212333335,0x245242420022202,0x330122012222244,0x123331212335335,0x423204221020220,0x330213212222024,0x123331312333353,0x344233430221212],
  #[0x431112014343434,0x123341212434345,0x443224440020222,0x530112112222224,0x123351212333355,0x325323211122210,0x241233113332144,0x123422322335443,0x424314221121220,0x341223213233134,0x123431322434453,0x345343430122212,0x440122013332344,0x123441212335445,0x444334440121222,0x540112113233334,0x123451212434455,0x343341230222012,0x421122014423442,0x124222212443423,0x343341232222012,0x423342034423442,0x124224212443423,0x442332240221022,0x521112114324432,0x124231212542433,0x442332242221022,0x523312334324432,0x124231212542433,0x443442240122022,0x530122113313342,0x124331222443533,0x443442242122022,0x530342333313342,0x124331242443533,0x325323210222210,0x241122014443244,0x124422212445443,0x325323212222210,0x243344014443244,0x124424412445443,0x424314220221220,0x341112114344234,0x124431212544453,0x424314222221220,0x343314314344234,0x124431412544453,0x345343430222212,0x441122014443444,0x124442212445445,0x444334440221222,0x541112114344434,0x124451212544455,0x425424220122220,0x350122113333144,0x124531222445553,0x425424222122220,0x350344313333144,0x124531442445553,0x445444440122222,0x550122113333344,0x124551222445555,0x23022423000202,0x112235240022212],
  #[0x130011315112013,0x123022423000202,0x212235240220202,0x130023315011023,0x124033433201212,0x214245342343412,0x130024315212023,0x23222423000202,0x132235241020202,0x130111335011113,0x123123433100212,0x223235341132312,0x130122325112123,0x124233433001212,0x232245341121212,0x130122335112123,0x124132423101202,0x223245241231312,0x130123325112123,0x125343433102212,0x243255341330322,0x130224345013223,0x224334443101222,0x343245441033312,0x130231345212233,0x242020223020002,0x302433242002222,0x131011313312113,0x241021223020002,0x302433242200222,0x131023313111123,0x342031233221012,0x404443344323432,0x131024313412123,0x23222421200202,0x132213022242402,0x131111313131113,0x25242421002202,0x130233020222222,0x131111313133113,0x243020223020002,0x312433242002222,0x131111313313113,0x23022423000202,0x112235240022222,0x131111315113113,0x241220223020002,0x312433242010222,0x131111333111313,0x241220223020002,0x312433242020222,0x131111333111313,0x23222423000202,0x132235242020202,0x131111335111113,0x223012203020200,0x112435222022024,0x131111513313133,0x223022203020200,0x112435222022024,0x131111513313133,0x124233431201212,0x232223122343412,0x131122313232123],
  #[0x133122422210202,0x223224133242413,0x131122314222124,0x342121233120012,0x413433343112322,0x131122323312223,0x342231233021012,0x412443342111232,0x131122333212323,0x342231233021012,0x412443342121232,0x131122333212323,0x124233433001212,0x232245342121212,0x131122335212123,0x242131223121002,0x313443243211332,0x131123323212223,0x223002213020200,0x212435222220024,0x131123513113133,0x342031233221012,0x414443344323432,0x131124313412123,0x124033433201212,0x214245342343412,0x131124315212123,0x324013213221210,0x214445324343234,0x131124513414143,0x243022421020202,0x310213222220224,0x131131313113135,0x223224441000222,0x330213220222202,0x131131313131133,0x243022421020202,0x310233022022224,0x131131313313135,0x241022223020002,0x312433242200222,0x131133313111133,0x223022423000202,0x312235240220202,0x131133315111133,0x223002223020200,0x312435222220024,0x131133513113133,0x344033431221212,0x412223124343434,0x131142313414145,0x125343431102212,0x241233121332322,0x131222323133223,0x343121233120012,0x423433343112322,0x131222323313223,0x135242422012202,0x231244131221233,0x131222324124224,0x123123433100212,0x223235341132322,0x131222325113223,0x323113213120210],
  #[0x223435323132124,0x131222523313243,0x323123213120210,0x223435323132124,0x131222523313243,0x224112213121200,0x223445223231134,0x131223523214233,0x343341233122012,0x423453343310342,0x131224343113423,0x125343433102212,0x243255341330322,0x131224345113223,0x244132421121202,0x321223223231334,0x131231323214235,0x224334441101222,0x341223221233312,0x131231323232233,0x442332243121022,0x523443443013332,0x131231343412433,0x224334443101222,0x343245441033312,0x131231345212233,0x242132223121002,0x323443243211332,0x131233323212233,0x224132423101202,0x323245241231312,0x131233325212233,0x224112223121200,0x323445223231134,0x131233523214233,0x333224442010222,0x431224331122213,0x131241324222244,0x343123431120212,0x421233123132324,0x131242323313245,0x223202203020200,0x132435222020124,0x131311533113333,0x223202203020200,0x132435222020224,0x131311533113333,0x324213213021210,0x232445322121134,0x131322533214343,0x324213213021210,0x232445322121234,0x131322533214343,0x243222421020202,0x332213022020224,0x131331313113335,0x344233431021212,0x432223122121234,0x131342313214345,0x325323213122210,0x243455323330144,0x131424543115443,0x424314223121220,0x343445423033134],
  #[0x131431543414453,0x345343431122212,0x441233123330344,0x131442323115445,0x444334441121222,0x541223223033334,0x131451323414455,0x242121322220102,0x313323134232423,0x132122313322224,0x244241322022102,0x321343132211243,0x132222323224324,0x233112312220201,0x223324124242324,0x132222413323234,0x244132421221202,0x322223124342434,0x132232313324235,0x442223342020122,0x521323332112223,0x132241323322344,0x343123431220212,0x422223124243424,0x132242313423245,0x344133431221212,0x422223124343434,0x132242313424245,0x235232312022201,0x231344122221144,0x132322423225334,0x245242421122202,0x331233123331344,0x132332323225335,0x433214332020221,0x431324322122124,0x132341423323354,0x443224441120222,0x531223223133324,0x132351323423355,0x345343431022212,0x441233122221244,0x132442323225445,0x345343431122212,0x441233123331344,0x132442323225445,0x444334441021222,0x541223222122234,0x132451323324455,0x444334441121222,0x541223223133334,0x132451323424455,0x241220221220002,0x312213024222422,0x133111313331313,0x243240221022002,0x310233022202242,0x133111313333313,0x342231231221012,0x412223124323432,0x133122313432323,0x441222241020022,0x510213222202222,0x133131313331333],
  #[0x343341231122012,0x421233123312342,0x133222323333423,0x442332241121022,0x521223223213332,0x133231323432433,0x223202201220200,0x132213024242224,0x133311313333333,0x225222201022200,0x130233022222044,0x133311313335333,0x324213211221210,0x232223124343234,0x133322313434343,0x423204221020220,0x330213222222024,0x133331313333353,0x235343432212212,0x343244033443433,0x133334314344334,0x334334442211222,0x443214333344423,0x133341314443344,0x344233431221212,0x432223124343434,0x133342313434345,0x325323211122210,0x241233123332144,0x133422323335443,0x424314221121220,0x341223223233134,0x133431323434453,0x335444442112222,0x450244332333333,0x133441344344444,0x345343431122212,0x441233123332344,0x133442323335445,0x444334441121222,0x541223223233334,0x133451323434455,0x344342332222112,0x433343034433443,0x134334313444434,0x443333342221122,0x533313334334433,0x134341313543444,0x335333322222211,0x343344024443344,0x134434413445444,0x444443342122122,0x540343333323343,0x134441343444544,0x434324332221221,0x443314324344334,0x134441413544454,0x345343431222212,0x442233024443444,0x134443313445445,0x444334441221222,0x542213224344434,0x134451313544455,0x435434332122221],
  #[0x450344323333244,0x134541443445554,0x445444441122222,0x550233223333344,0x134551333445555,0x133122423110202,0x223335242131313,0x140122425112124,0x134132423011202,0x222345241121223,0x140122425113124,0x233123433010212,0x322335341121213,0x140132425112134,0x242121323120102,0x313434243121323,0x141122424212224,0x243131323021102,0x312444242111233,0x141122424213224,0x342122333020112,0x412434342111223,0x141132424212234,0x343032333221112,0x414444344333433,0x141134414413134,0x234033433211212,0x314345343343423,0x141134415313134,0x334023323221211,0x314445334343334,0x141134514414144,0x344033432221212,0x413334234343434,0x141143414414145,0x233112313120201,0x223435233131224,0x141222524213234,0x234122313021201,0x222445232121134,0x141222524214234,0x333113323020211,0x322435332121124,0x141232524213244,0x344342333122112,0x433454343320343,0x141334444114434,0x235343433112212,0x343355342330333,0x141334445114334,0x443333343121122,0x533444443023333,0x141341444413444,0x334334443111222,0x443345442033323,0x141341445313344,0x335333323122211,0x343455333330244,0x141434544115444,0x434324333121221,0x443445433033234,0x141441544414454,0x345343432122212,0x442344233330344],
  #[0x141443434115445,0x444334442121222,0x542334333033334,0x141451434414455,0x244132422021202,0x321334132122234,0x142231414324235,0x244132422221202,0x323314134342434,0x142231414324235,0x243122422220202,0x323324134242424,0x142232414323235,0x244132422221202,0x323324134342434,0x142232414324235,0x244132422221202,0x323334134342434,0x142233414324235,0x343123432020212,0x421324232221224,0x142242414223245,0x343123432220212,0x423324034243424,0x142242414423245,0x343123432220212,0x423324134243424,0x142242414423245,0x343123432220212,0x423324234243424,0x142242414423245,0x344133432221212,0x423334234343434,0x142243414424245,0x243222422120202,0x332324133131324,0x142331424223335,0x245242422122202,0x330344133331344,0x142331424225335,0x245242422022202,0x331344132221244,0x142332424225335,0x245242422122202,0x331344133331344,0x142332424225335,0x245242422122202,0x332344133331344,0x142333424225335,0x344233432121212,0x432334233232334,0x142342424324345,0x443224442020222,0x531324332122224,0x142351424323355,0x443224442120222,0x530324333133324,0x142351424423355,0x443224442120222,0x531324333133324,0x142351424423355,0x443224442120222,0x532324333133324,0x142351424423355],
  #[0x345343432022212,0x441344032221244,0x142442414225445,0x345343432022212,0x441344132221244,0x142442424225445,0x345343432022212,0x441344232221244,0x142442434225445,0x345343432122212,0x442344233331344,0x142443434225445,0x444334442021222,0x541314332122234,0x142451414324455,0x444334442021222,0x541324332122234,0x142451424324455,0x444334442021222,0x541334332122234,0x142451434324455,0x444334442121222,0x542334333133334,0x142451434424455,0x245242422222202,0x333344034442444,0x143334414335335,0x344233432221212,0x433314234343434,0x143341414434345,0x344233432221212,0x433324234343434,0x143342414434345,0x344233432221212,0x433334034343434,0x143343414434345,0x344233432221212,0x433334134343434,0x143343414434345,0x443224442220222,0x533314334244424,0x143351414533355,0x345343432122212,0x440344233332344,0x143441434335445,0x345343432122212,0x441344233332344,0x143442434335445,0x345343432122212,0x442344033332344,0x143443414335445,0x345343432122212,0x442344133332344,0x143443424335445,0x444334442121222,0x542314333233334,0x143451414434455,0x444334442121222,0x542324333233334,0x143451424434455,0x444334442121222,0x540334333233334,0x143451434434455,0x444334442121222],
  #[0x541334333233334,0x143451434434455,0x445444442022222,0x550344332222244,0x143551444335555,0x345343432222212,0x443344034443444,0x144444414445445,0x444334442221222,0x543314334344434,0x144451414544455,0x445444442122222,0x550344333333344,0x144551444445555,0x244032423221202,0x314445244342434,0x151134515314135,0x344033433021212,0x412445342121234,0x151142515214145,0x344033433121212,0x413445343232334,0x151143515314145,0x343023433220212,0x414435344243424,0x151143515413145,0x344033433221212,0x414445344343434,0x151144515414145,0x244132423121202,0x323445243031334,0x151231525214235,0x243122423120202,0x323435243131324,0x151232525213235,0x244132423021202,0x322445242121234,0x151232525214235,0x244132423121202,0x323445243131334,0x151232525214235,0x244132423121202,0x323445243231334,0x151233525214235,0x343123433120212,0x423435343130324,0x151242525113245,0x343123433020212,0x422435342121224,0x151242525213245,0x343123433120212,0x423435343131324,0x151242525213245,0x344133433021212,0x422445342121234,0x151242525214245,0x343123433120212,0x423435343132324,0x151242525313245,0x344133433121212,0x423445343232334,0x151243525314245,0x245242423122202,0x333455243330344],
  #[0x151334535115335,0x344233433121212,0x433445343032334,0x151341535314345,0x344233433021212,0x432445342121234,0x151342535214345,0x344233433121212,0x433445343132334,0x151342535314345,0x344233433121212,0x433445343230334,0x151343535114345,0x344233433121212,0x433445343231334,0x151343535214345,0x443224443120222,0x533435443033324,0x151351535413355,0x345343433022212,0x442455342220244,0x151443545115445,0x345343433122212,0x443455343330344,0x151444545115445,0x444334443021222,0x542445442022234,0x151451545314455,0x444334443121222,0x543445443033334,0x151451545414455,0x234342330212112,0x331021113433432,0x203222021343323,0x224443340202122,0x341021112434421,0x203222021352322,0x244241322222102,0x323340134432443,0x203224020334324,0x333333340211122,0x431021113334422,0x203232021442333,0x442223342220122,0x523320334234423,0x203242020532344,0x225333320212211,0x241022103443333,0x203322121344333,0x215434330202221,0x251022102444322,0x203322121353332,0x334443340112122,0x441021112323332,0x203332021343433,0x324324330211221,0x341022103344323,0x203332121443343,0x325434330112221,0x351022102333233,0x203432121344443,0x444443342022122,0x541340332212243,0x203442040334544],
  #[0x333442240212022,0x431021113424431,0x204222021452422,0x334443340212122,0x441021113434431,0x204222021452422,0x324433230212121,0x341021113434332,0x204322021453432,0x334332220222111,0x331121104433343,0x204322120444433,0x324433230212121,0x341121103434332,0x204322120453432,0x324433230212121,0x341022103434332,0x204322121453432,0x433323230221121,0x431121104334333,0x204332120543443,0x315424220212220,0x251022103444233,0x204422121454442,0x315434330212221,0x251022103444333,0x204422121454442,0x434433230122121,0x441121103323243,0x204432120444543,0x433432130222021,0x431121104424342,0x205322120553532,0x424423120222120,0x341121104434243,0x205422120554542,0x434433130222121,0x441121104434343,0x205422120554542,0x444443340222122,0x541120114434443,0x205442020554544,0x23240221202002,0x112031122422422,0x211113121133113,0x25222201202200,0x132033102442222,0x211113121133113,0x221222241200022,0x312021222224402,0x211132121331133,0x223204221200220,0x332023202244202,0x211132121331133,0x223442241002022,0x331031220202222,0x211332131133333,0x225424221002220,0x351033200222022,0x211332131133333,0x134241321212102,0x222132123432432,0x212113122233213,0x124342331202112],
  #[0x232132122433421,0x212113122242212,0x133241222212002,0x223242133422431,0x212114122232212,0x124241322202102,0x223143132432421,0x212114123232212,0x223333341201122,0x332122222334411,0x212122122341222,0x332222242210022,0x423222333224411,0x212122122431222,0x222223342200122,0x323123332234411,0x212122123331222,0x332223341210122,0x422122223234412,0x212132122431233,0x125232311212201,0x132133113442333,0x212213222234223,0x115333321202211,0x142133112443322,0x212213222243222,0x115232312202201,0x133144122442322,0x212214223233222,0x115222212212200,0x133244113442233,0x212214322234222,0x135242420212202,0x231022113442433,0x212222122234224,0x333222242210022,0x433222333224411,0x212222122432222,0x224443341102122,0x341132221323321,0x212222132242322,0x333442242012022,0x431242331212231,0x212222142232422,0x333442242012022,0x431242331222231,0x212222142232422,0x224443342002122,0x341143331212221,0x212222143232322,0x214324331201221,0x242123212344312,0x212222222342232,0x213214332200221,0x233124322244312,0x212222223332232,0x313214222210220,0x233224313244213,0x212222322432242,0x313224222210220,0x233224313244213,0x212222322432242,0x133242222212002,0x233242133422431],
  #[0x212224122232222,0x135242422212202,0x233044133442433,0x212224124234224,0x115222222212200,0x233244113442233,0x212224322234222,0x323214331210221,0x332123213244313,0x212232222432243,0x333224440210222,0x431022113244413,0x212242122432244,0x333224442210222,0x433024333244413,0x212242124432244,0x215434331102221,0x251133211333222,0x212322232243332,0x215434332002221,0x251144321222122,0x212322243233332,0x334443341012122,0x441132221212232,0x212332132233433,0x315424222012220,0x251244311222133,0x212422342234442,0x315424222012220,0x251244311222233,0x212422342234442,0x325434331012221,0x351133211222133,0x212432232234443,0x335444440012222,0x451022111222233,0x212442122234444,0x335444442012222,0x451044331222233,0x212442144234444,0x223220201222000,0x112231104422242,0x213113121333313,0x233341231212012,0x322132123423431,0x213113122342312,0x332332241211022,0x422122223324421,0x213122122441322,0x421202221220020,0x312221204224222,0x213132121531333,0x234231211222101,0x222232114432343,0x213213221334323,0x233231112222001,0x223342124422342,0x213214221333322,0x224221112222100,0x223343114432243,0x213214321334322,0x244241320222102,0x321121114432443,0x213222121334324],
  #[0x224443340202122,0x341121112434421,0x213222121352322,0x222223342200122,0x323123332234421,0x213222123332322,0x333442241112022,0x431132222313331,0x213222132342422,0x224443342002122,0x341143332212221,0x213222143332322,0x432212132220021,0x423322324224322,0x213222221532332,0x422213122220120,0x323323314234223,0x213222321532342,0x422223122220120,0x323323314234223,0x213222321532342,0x244241322222102,0x323341134432443,0x213224121334324,0x224241322202102,0x323143132432421,0x213224123332322,0x224221122222100,0x323343114432243,0x213224321334322,0x432213231220121,0x422222214234323,0x213232221532343,0x442223340220122,0x521121114234423,0x213242121532344,0x442223342220122,0x523321334234423,0x213242121532344,0x215323211212210,0x142133113443233,0x213313222344332,0x235232310222201,0x231122104442344,0x213322221335334,0x215434330202221,0x251122102444322,0x213322221353332,0x433212132220021,0x433322324224322,0x213322221533332,0x314314221211220,0x242123213344223,0x213322222443342,0x213214332200221,0x233124322244322,0x213322223333332,0x433432132022021,0x431342322212142,0x213322241333532,0x433432132022021,0x431342322222142,0x213322241333532,0x215434332002221],
  #[0x251144322222122,0x213322243333332,0x233232112222001,0x233342124422342,0x213324221333332,0x215232312202201,0x233144122442322,0x213324223333332,0x235232312222201,0x233344104442344,0x213324421335334,0x223442240202022,0x331021112424422,0x213332121353333,0x225424220202220,0x351022102444222,0x213332121353333,0x423422221022020,0x331231202202042,0x213332131333533,0x433214330220221,0x431122104244324,0x213342221533354,0x433214332220221,0x433324304244324,0x213342421533354,0x315424221112220,0x251133212333133,0x213422232344442,0x424423122022120,0x341343312212143,0x213422341334542,0x424423122022120,0x341343312212243,0x213422341334542,0x434433231022121,0x441232212212143,0x213432231334543,0x444443340022122,0x541121112212243,0x213442121334544,0x444443342022122,0x541341332212243,0x213442141334544,0x435434330022221,0x451122102222144,0x213542221335554,0x435434332022221,0x451344302222144,0x213542441335554,0x333331121222011,0x322232114423342,0x214213221443422,0x333442240212022,0x431022113424431,0x214222122452422,0x432322131221021,0x422222214324332,0x214222221542432,0x324322111222110,0x232232114433243,0x214313221444432,0x423313121221120,0x332222214334233],
  #[0x214322221543442,0x433432131122021,0x431232213313242,0x214322231443532,0x334443340212122,0x441021113434432,0x214332121453433,0x315424220212220,0x251022113444233,0x214422122454442,0x424423121122120,0x341232213323143,0x214422231444542,0x325434330212221,0x351022103444333,0x214432121454443,0x335444440212222,0x451022113444433,0x214442122454444,0x433432130222021,0x431122104424342,0x215322221553532,0x423422220222020,0x331121104424242,0x215332121553533,0x424423120222120,0x341121114434243,0x215422121554542,0x434433230222121,0x441121104434343,0x215432121554543,0x444443340222122,0x541121114434443,0x215442121554544,0x435434330222221,0x451122104444344,0x215542221555554,0x232121233210012,0x314333343223411,0x221013223321112,0x122122333200112,0x214234342233411,0x221013224221112,0x132131223211002,0x214343243322421,0x221014223221112,0x123131323201102,0x214244242332411,0x221014224221112,0x35343431212212,0x142133123443433,0x221113223144114,0x233121233210012,0x324333343223411,0x221113223322112,0x233341233012012,0x322353341211231,0x221113243122312,0x233341233012012,0x322353341221231,0x221113243122312,0x124342333002112,0x232254341211221,0x221113244122212],
  #[0x113113323200211,0x124235332243312,0x221113324222122,0x213113213210210,0x124335323243213,0x221113423322132,0x213123213210210,0x124335323243213,0x221113423322132,0x133241223112002,0x223353242311331,0x221114233122212,0x124241323102102,0x223254241321321,0x221114234122212,0x114122313201201,0x124245232342312,0x221114324222122,0x114112213211200,0x124345223342223,0x221114423223122,0x134132421211202,0x222123223342423,0x221122223223124,0x332222243110022,0x423333442113311,0x221122233321222,0x222223343100122,0x323234441123311,0x221122234221222,0x332332243011022,0x422343441112221,0x221122243221322,0x332332243011022,0x422343441122221,0x221122243221322,0x223333343001122,0x332244441112211,0x221122244221222,0x132132223211002,0x224343243322421,0x221124223221122,0x114112223211200,0x224345223342223,0x221124423223122,0x233123431210212,0x322133123243413,0x221133223322134,0x334334441211222,0x442123223344403,0x221142223441144,0x115333323002211,0x142255331221122,0x221213344123222,0x115232313102201,0x133255231331222,0x221214334123222,0x115222213112200,0x133355222331133,0x221214433124222,0x135242421112202,0x231133222331333,0x221222233124224,0x333222243110022],
  #[0x433333442113311,0x221222233322222,0x213214333100221,0x233235431133212,0x221222334222232,0x214324333001221,0x242245431122112,0x221222344222232,0x313214223110220,0x233335422133113,0x221222433322242,0x313224223110220,0x233335422133113,0x221222433322242,0x133242223112002,0x233353242311331,0x221224233122222,0x115222223112200,0x233355222331133,0x221224433124222,0x333224441110222,0x431133222133313,0x221242233322244,0x215323213012210,0x142355321221133,0x221313443124332,0x215323213012210,0x142355321221233,0x221313443124332,0x314314223011220,0x242345421122123,0x221322443223342,0x314314223011220,0x242345421122223,0x221322443223342,0x235343431012212,0x342133121221233,0x221333223124334,0x334334441011222,0x442123221122223,0x221342223223344,0x335444441112222,0x451133220333333,0x221442233144444,0x124342331202112,0x232232122433421,0x222113222242212,0x122122333200112,0x214234342233421,0x222113224222212,0x124342333002112,0x232254342211221,0x222113244222212,0x332111123220011,0x314433334223322,0x222113322422222,0x322112113220110,0x214434324233223,0x222113422422232,0x322122113220110,0x214434324233223,0x222113422422232,0x232121113221001,0x214443234322332],
  #[0x222114322322222,0x223111113221100,0x214444224332233,0x222114422323222,0x243131321221102,0x312222224332433,0x222122222323224,0x223333341201122,0x332222222334411,0x222122222341222,0x223333343001122,0x332244442112211,0x222122244321222,0x223131323201102,0x314244242332411,0x222124224321222,0x223111123221100,0x314444224332233,0x222124422323222,0x342122331220112,0x412232124233423,0x222133222422234,0x115333321202211,0x142233112443322,0x222213322243222,0x333111123220011,0x324433334223322,0x222213322423222,0x113113323200211,0x124235332243322,0x222213324223222,0x333331123022011,0x322453332211142,0x222213342223422,0x333331123022011,0x322453332221142,0x222213342223422,0x115333323002211,0x142255332221122,0x222213344223222,0x233231113122001,0x223453233311242,0x222214332223322,0x224221113122100,0x223454223321143,0x222214432224322,0x244241321122102,0x321232223321343,0x222222232224324,0x224443341102122,0x341232221323321,0x222222232242322,0x222223343100122,0x323234441123321,0x222222234222322,0x234122311221201,0x222223214342334,0x222222322324234,0x214324331201221,0x242223212344312,0x222222322342232,0x432212133120021,0x423433433113222,0x222222332422332],
  #[0x432322133021021,0x422443432112132,0x222222342322432,0x432322133021021,0x422443432122132,0x222222342322432,0x214324333001221,0x242245432122112,0x222222344322232,0x422213123120120,0x323434423123123,0x222222432422342,0x422223123120120,0x323434423123123,0x222222432422342,0x135242421212202,0x232133123442433,0x222223223234224,0x125343431202212,0x242133122443422,0x222223223243223,0x135343431212212,0x242133123443433,0x222223223244224,0x135242422212202,0x233144133442433,0x222224224234224,0x125343432202212,0x243144132443422,0x222224224243223,0x224241323102102,0x323254241321321,0x222224234222322,0x232122113221001,0x224443234322332,0x222224322322232,0x214122313201201,0x224245232342312,0x222224324322232,0x224221123122100,0x323454223321143,0x222224432224322,0x224334441201222,0x342123222344412,0x222232223342233,0x223224442200222,0x333124332244412,0x222232224332233,0x224334442201222,0x343124332344412,0x222232224342233,0x333113321220211,0x322233114243324,0x222233322423244,0x334334441211222,0x442123223344413,0x222242223442244,0x333224442210222,0x433124333244413,0x222242224432244,0x442223341120122,0x521232223123323,0x222242232422344,0x324322113022110],
  #[0x232454322211143,0x222313442224432,0x324322113022110,0x232454322211243,0x222313442224432,0x235232311122201,0x231233213331244,0x222322332225334,0x215434331102221,0x251233211333222,0x222322332243332,0x433212133120021,0x433433433113222,0x222322332423332,0x213214333100221,0x233235431133222,0x222322334223332,0x423313123021120,0x332444422112133,0x222322442323442,0x423313123021120,0x332444422112233,0x222322442323442,0x233232113122001,0x233453233311242,0x222324332223332,0x215232313102201,0x233255231331222,0x222324334223332,0x225444441102222,0x351133221333322,0x222332233243333,0x225444442002222,0x351144331222222,0x222332244233333,0x225444442102222,0x351144331333322,0x222332244243333,0x344342331022112,0x432232122211243,0x222333222224434,0x443333341021122,0x532222222112233,0x222342222323444,0x433214331120221,0x431233213133224,0x222342332423354,0x335333321022211,0x342233112221144,0x222433322225444,0x335444441112222,0x451133221333333,0x222442233244444,0x335444442012222,0x451144331222233,0x222442244234444,0x434324331021221,0x442223212122134,0x222442322324454,0x233341231212012,0x322133123423431,0x223113223342312,0x332332241211022,0x422123223324421],
  #[0x223122223441322,0x333442241112022,0x431133222313331,0x223222233342422,0x244241321222102,0x322232124432443,0x223223222334324,0x243241222222002,0x323342134422442,0x223224222333323,0x244241322222102,0x323342134432443,0x223224222334324,0x442222242220022,0x523322334224422,0x223232222532333,0x442223341220122,0x522222224234423,0x223242222532344,0x442223342220122,0x523322334234423,0x223242222532344,0x215323211212210,0x142133123443233,0x223313223344332,0x314314221211220,0x242123223344223,0x223322223443342,0x235232311222201,0x232233114442344,0x223323322335334,0x225222212222200,0x233344114442244,0x223324422335333,0x235232312222201,0x233344114442344,0x223324422335334,0x245242420222202,0x331122114442444,0x223332222335335,0x225444440202222,0x351122112444422,0x223332222353333,0x443222242220022,0x533322334224422,0x223332222533333,0x223224442200222,0x333124332244422,0x223332224333333,0x443442242022022,0x531342332212242,0x223332242333533,0x443442242022022,0x531342332222242,0x223332242333533,0x225444442002222,0x351144332222222,0x223332244333333,0x423214222220220,0x333324314244224,0x223332422533353,0x423224222220220,0x333324314244224,0x223332422533353],
  #[0x235343431212212,0x342133123443433,0x223333223344334,0x243242222222002,0x333342134422442,0x223334222333333,0x225242422202202,0x333144132442422,0x223334224333333,0x225222222222200,0x333344114442244,0x223334422335333,0x334334441211222,0x442123223344423,0x223342223443344,0x433214331220221,0x432223214244324,0x223342322533354,0x433214332220221,0x433324314244324,0x223342422533354,0x443224440220222,0x531122114244424,0x223352222533355,0x315424221112220,0x251133222333133,0x223422233344442,0x444443341022122,0x541232222212243,0x223442232334544,0x335444441112222,0x451133222333333,0x223442233344444,0x444443342022122,0x541342332212243,0x223442242334544,0x425424222022220,0x351344312222144,0x223532442335553,0x425424222022220,0x351344312222244,0x223532442335553,0x435434331022221,0x451233212222144,0x223542332335554,0x435434332022221,0x451344312222144,0x223542442335554,0x445444440022222,0x551122112222244,0x223552222335555,0x440333341221122,0x502222224334433,0x224042222540444,0x344340331222112,0x412232124433443,0x224113222444414,0x441333341221122,0x512222224334433,0x224142222541444,0x333331121222011,0x322233114423342,0x224213322443422,0x432322131221021],
  #[0x422223214324332,0x224222322542432,0x344341331222112,0x422232124433443,0x224223222444424,0x343341232222012,0x423342134423442,0x224224222443423,0x442332241221022,0x522222224324432,0x224232222542433,0x442332242221022,0x523322334324432,0x224232222542433,0x442333341221122,0x522222224334433,0x224242222542444,0x324322111222110,0x232232124433243,0x224313222444432,0x423313121221120,0x332222224334233,0x224322222543442,0x433432131122021,0x431233213313242,0x224322332443532,0x443442241122022,0x531232223313342,0x224332232443533,0x443442242122022,0x531342333313342,0x224332242443533,0x344342331222112,0x432232124433443,0x224333222444434,0x443333341221122,0x532222224334433,0x224342222543444,0x335333301222211,0x142233114443344,0x224413322445444,0x424423121122120,0x341232223323143,0x224422232444542,0x335333311222211,0x242233114443344,0x224423322445444,0x325323212222210,0x243344114443244,0x224424422445443,0x424314221221220,0x342223214344234,0x224432322544453,0x424314222221220,0x343324314344234,0x224432422544453,0x335333321222211,0x342233114443344,0x224433322445444,0x444443341122122,0x541232223303343,0x224442232444544,0x444443341122122,0x541232223313343],
  #[0x224442232444544,0x444443341122122,0x541232223323343,0x224442232444544,0x434304331221221,0x442223214344334,0x224442322544454,0x434314331221221,0x442223214344334,0x224442322544454,0x434324331221221,0x442223214344334,0x224442322544454,0x425424221122220,0x351233213333144,0x224532332445553,0x425424222122220,0x351344313333144,0x224532442445553,0x435434331122221,0x451233213333044,0x224542332445554,0x435434331122221,0x451233213333144,0x224542332445554,0x435434331122221,0x451233213333244,0x224542332445554,0x443442240222022,0x531122114424442,0x225332222553533,0x425424220222220,0x351122114444244,0x225532222555553,0x21120223200002,0x104233242222402,0x230013323121013,0x23102203200200,0x124235222242202,0x230013323121013,0x23240223002002,0x112253240201222,0x230113333023113,0x25222203002200,0x132255220221022,0x230113333023113,0x221222243000022,0x312233440102202,0x230132333121133,0x223204223000220,0x332235420122002,0x230132333121133,0x132121323210102,0x214334243232412,0x231013324221113,0x134241323012102,0x222354241211232,0x231113334123213,0x123112313210201,0x124335233242313,0x231113424222123,0x123123433200212,0x224235342243412,0x231123325222123],
  #[0x124132423201202,0x224245242342412,0x231124325222123,0x124133433201212,0x224245342343412,0x231124325222123,0x332223343010122,0x422334441112212,0x231132334221233,0x125232313012201,0x132355231221133,0x231213434124223,0x125343433002212,0x242255341221222,0x231223345123223,0x125242423102202,0x233255241331322,0x231224335123223,0x125343433102212,0x243255341331322,0x231224345123223,0x223224443100222,0x333235441133312,0x231232335222233,0x224334443001222,0x342245441122212,0x231232345222233,0x224334443101222,0x343245441133312,0x231232345222233,0x323214333010221,0x332335431122113,0x231232434222243,0x221100203220000,0x104433224222222,0x232013323321213,0x223220203022000,0x112453222201042,0x232113333223313,0x232111213220101,0x214434234232323,0x232113423322223,0x342121233220012,0x414433344223422,0x232123323422223,0x242131223221002,0x314443244322432,0x232124323322223,0x342131233221012,0x414443344323432,0x232124323422223,0x421202223020020,0x312433422102022,0x232132333321333,0x234231213022101,0x222454232211143,0x232213433224323,0x133222422210202,0x233224133242413,0x232222324232224,0x135242422012202,0x231244131222233,0x232222324234224,0x125343431202212],
  #[0x242233122443422,0x232223323243223,0x343121233220012,0x424433344223422,0x232223323423223,0x123123433200212,0x224235342243422,0x232223325223223,0x343341233022012,0x422453342211242,0x232223343223423,0x343341233022012,0x422453342221242,0x232223343223423,0x125343433002212,0x242255342221222,0x232223345223223,0x323113213220210,0x224435324243224,0x232223523423243,0x323123213220210,0x224435324243224,0x232223523423243,0x342131233221012,0x424443344323432,0x232224323422223,0x135242422212202,0x233244133442433,0x232224324234224,0x124133433201212,0x224245342343412,0x232224325222223,0x243241223122002,0x323453243311342,0x232224333223323,0x343341233122012,0x423453343311342,0x232224343223423,0x125343433102212,0x243255341331322,0x232224345223223,0x224112213221200,0x224445224342234,0x232224523324233,0x324113213221210,0x224445324343234,0x232224523424243,0x244132421221202,0x322223224342434,0x232232323324235,0x224334441201222,0x342223222344412,0x232232323342233,0x442222243120022,0x523433443113322,0x232232333422333,0x442332243021022,0x522443442112232,0x232232343322433,0x442332243021022,0x522443442122232,0x232232343322433,0x442332243121022,0x523443443113332],
  #[0x232232343422433,0x224334443101222,0x343245441133312,0x232232345222233,0x224334443001222,0x342245442122212,0x232232345322233,0x432213233020121,0x422434432112123,0x232232433322343,0x234233432211212,0x333234233343423,0x232233324333234,0x242132223221002,0x324443244322432,0x232234323322233,0x224132423201202,0x324245242342412,0x232234325322233,0x224112223221200,0x324445224342234,0x232234523324233,0x344133431221212,0x422223124343434,0x232242323424245,0x333224442010222,0x431224331222213,0x232242324232244,0x333224442210222,0x433224333244413,0x232242324432244,0x343123431220212,0x422233124243424,0x232243323423245,0x225222213122200,0x233455223331144,0x232324533225333,0x245242421122202,0x331233223331344,0x232332333225335,0x225444441102222,0x351233221333322,0x232332333243333,0x443222243120022,0x533433443113322,0x232332333423333,0x223224443100222,0x333235441133322,0x232332335223333,0x423214223120220,0x333435423133124,0x232332533423353,0x423224223120220,0x333435423133124,0x232332533423353,0x235343432112212,0x342244232332333,0x232333334234334,0x243242223122002,0x333453243311342,0x232334333223333,0x225242423102202,0x333255241331322,0x232334335223333],
  #[0x225222223122200,0x333455223331144,0x232334533225333,0x334334442111222,0x442234332233323,0x232342334333344,0x443224441120222,0x531233223133324,0x232352333423355,0x325323213022210,0x242455322221144,0x232423543225443,0x325323213022210,0x242455322221244,0x232423543225443,0x325323213122210,0x243455323331144,0x232424543225443,0x424314223021220,0x342445422122134,0x232432543324453,0x424314223021220,0x342445422122234,0x232432543324453,0x424314223121220,0x343445423133134,0x232432543424453,0x345343431122212,0x441233123331344,0x232442323225445,0x335444442012222,0x451244331222233,0x232442344234444,0x345343431022212,0x442233122221244,0x232443323225445,0x444334441021222,0x542223222122234,0x232452323324455,0x444334441121222,0x541223223133334,0x232452323424455,0x242221322220102,0x323323134232423,0x233222323332324,0x244241322022102,0x321343132212243,0x233222323334324,0x244241322222102,0x323343134432443,0x233224323334324,0x343232332221112,0x423333234333433,0x233233323433334,0x442223342020122,0x521323332212223,0x233242323332344,0x442223342220122,0x523323334234423,0x233242323532344,0x233212312220201,0x233324124242324,0x233322423333334,0x235232312022201],
  #[0x231344122222144,0x233322423335334,0x235232312222201,0x233344124442344,0x233324423335334,0x344342332122112,0x432343233322343,0x233333333334434,0x334223322221211,0x333334224343334,0x233333423434344,0x235343432212212,0x343244133443433,0x233334324344334,0x334334442211222,0x443224333344423,0x233342324443344,0x443333342121122,0x532333333223333,0x233342333433444,0x433214332020221,0x431324322222124,0x233342423333354,0x433214332220221,0x433324324244324,0x233342423533354,0x335333322122211,0x342344223332244,0x233433433335444,0x444443342022122,0x541343332212243,0x233442343334544,0x335444442112222,0x451244332333333,0x233442344344444,0x434324332121221,0x442334323233234,0x233442433434454,0x435434332022221,0x451344322222144,0x233542443335554,0x343341231222012,0x422233124423442,0x234223323443423,0x442332241221022,0x522223224324432,0x234232323542433,0x443442241122022,0x531233223313342,0x234332333443533,0x344342332222112,0x433343134433443,0x234334323444434,0x443333342221122,0x533323334334433,0x234342323543444,0x325323211222210,0x242233124443244,0x234423323445443,0x424314221221220,0x342223224344234,0x234432323544453,0x335333322222211,0x343344124443344],
  #[0x234434423445444,0x444443342122122,0x541343333323343,0x234442343444544,0x434324332221221,0x443324324344334,0x234442423544454,0x425424221122220,0x351233223333144,0x234532333445553,0x435434332122221,0x451344323333244,0x234542443445554,0x33123433210212,0x124335343243413,0x240013425122014,0x134132423211202,0x224345243342403,0x240024425221024,0x35343433012212,0x142355341221233,0x240113445024114,0x334334443011222,0x442345441122203,0x240142445221144,0x135242423112202,0x233355240331333,0x240224435024224,0x333224443110222,0x433335440133313,0x240242435122244,0x33123433210212,0x124335343243413,0x241113425122114,0x35343433012212,0x142355341221233,0x241113445124114,0x134132423011202,0x222345241122223,0x241122425223124,0x133122423210202,0x224335243242413,0x241123425222124,0x133123433210212,0x224335343243413,0x241123425222124,0x134132423211202,0x224345243342403,0x241124425221124,0x134132423211202,0x224345243342413,0x241124425222124,0x134132423211202,0x224345243342423,0x241124425223124,0x233123433010212,0x322335341221213,0x241133425122134,0x233123433210212,0x324335343243413,0x241133425322134,0x234133433211212,0x324345343343423,0x241134425323134],
  #[0x334334443011222,0x442345441122203,0x241142445221144,0x133222423110202,0x233335242131313,0x241222435122224,0x135242423012202,0x232355241221233,0x241223435124224,0x135343433012212,0x242355341221233,0x241223445124224,0x135242423112202,0x233355240331333,0x241224435124224,0x135242423112202,0x233355241331333,0x241224435124224,0x135242423112202,0x233355242331333,0x241224435124224,0x234233433111212,0x333345342232323,0x241233435223234,0x333224443110222,0x433335440133313,0x241242435122244,0x333224443110222,0x433335441133313,0x241242435222244,0x333224443110222,0x433335442133313,0x241242435322244,0x334334443011222,0x442345441122213,0x241242445222244,0x235343433012212,0x342355341221233,0x241333445124334,0x235343433112212,0x343355342331333,0x241334445124334,0x334334443011222,0x442345441122223,0x241342445223344,0x334334443111222,0x443345442133323,0x241342445323344,0x342120333220112,0x404434344233423,0x242013424422214,0x241131323221102,0x304444244332433,0x242024424321224,0x440333343021122,0x502444442112233,0x242042444320444,0x342120333220112,0x414434344233423,0x242113424422214,0x344340333022112,0x412454342211243,0x242113444224414,0x243131323021102],
  #[0x312444242112233,0x242122424323224,0x342121333220112,0x414434344233423,0x242123424422224,0x241131323221102,0x314444244332433,0x242124424321224,0x242131323221102,0x314444244332433,0x242124424322224,0x243131323221102,0x314444244332433,0x242124424323224,0x342122333020112,0x412434342211223,0x242133424222234,0x342122333220112,0x414434344233423,0x242133424422234,0x343132333221112,0x414444344333433,0x242134424423234,0x441333343021122,0x512444442112233,0x242142444321444,0x333113303220211,0x124435334243324,0x242213524423244,0x242221323120102,0x323434243121323,0x242222434222324,0x234122313021201,0x222445232122134,0x242222524324234,0x342121333220112,0x424434344233423,0x242223424422224,0x133123433210212,0x224335343243413,0x242223425222224,0x344341333022112,0x422454342211243,0x242223444224424,0x135343433012212,0x242355341221233,0x242223445224224,0x333113313220211,0x224435334243324,0x242223524423244,0x242131323221102,0x324444244332433,0x242224424322224,0x134132423211202,0x224345243342413,0x242224425222224,0x244241323122102,0x323454243301343,0x242224434224324,0x244241323122102,0x323454243311343,0x242224434224324,0x244241323122102,0x323454243321343],
  #[0x242224434224324,0x135242423112202,0x233355241331333,0x242224435224224,0x234102313221201,0x224445234342334,0x242224524324234,0x234112313221201,0x224445234342334,0x242224524324234,0x234122313221201,0x224445234342334,0x242224524324234,0x244132422221202,0x323324134342434,0x242232424324235,0x343232333121112,0x423444343222333,0x242233434323334,0x333113323020211,0x322435332221124,0x242233524223244,0x333113323220211,0x324435334243324,0x242233524423244,0x334123323221211,0x324445334343334,0x242234524424244,0x343123432220212,0x423324134243424,0x242242424423245,0x442223343120122,0x523434443103323,0x242242434422344,0x442223343120122,0x523434443113323,0x242242434422344,0x442223343120122,0x523434443123323,0x242242434422344,0x333224443110222,0x433335441133313,0x242242435222244,0x442333343021122,0x522444442112233,0x242242444322444,0x334334443011222,0x442345441122213,0x242242445222244,0x233212313120201,0x233435233131224,0x242322534223334,0x235232313022201,0x232455232221144,0x242323534225334,0x235232313122201,0x233455233331044,0x242324534225334,0x235232313122201,0x233455233331144,0x242324534225334,0x235232313122201,0x233455233331244,0x242324534225334],
  #[0x245242422122202,0x331344133331344,0x242332424225335,0x344342333022112,0x432454342211243,0x242333444224434,0x334223323121211,0x333445333232234,0x242333534324344,0x344342333122112,0x433454343321343,0x242334444224434,0x443333343021122,0x532444442112233,0x242342444323444,0x443333343121122,0x533444443123333,0x242342444423444,0x433214333020221,0x432435432122124,0x242342534323354,0x433214333120221,0x433435433133024,0x242342534423354,0x433214333120221,0x433435433133124,0x242342534423354,0x433214333120221,0x433435433133224,0x242342534423354,0x443224442120222,0x531324333133324,0x242352424423355,0x335333303022211,0x142455332221144,0x242413544225444,0x335333313022211,0x242455332221144,0x242423544225444,0x335333323022211,0x342455332221144,0x242433544225444,0x335333323122211,0x343455333331244,0x242434544225444,0x345343432022212,0x441344132221244,0x242442424225445,0x434304333021221,0x442445432122134,0x242442544324454,0x434314333021221,0x442445432122134,0x242442544324454,0x434324333021221,0x442445432122134,0x242442544324454,0x434324333121221,0x443445433133234,0x242442544424454,0x444334442021222,0x541324332122234,0x242452424324455,0x243222422220202],
  #[0x333324134242424,0x243332424333335,0x245242422022202,0x331344132222244,0x243332424335335,0x344233432221212,0x433334234343434,0x243343424434345,0x443224442020222,0x531324332222224,0x243352424333355,0x345343432122212,0x442344233332344,0x243443434335445,0x444334442121222,0x542334333233334,0x243452434434455,0x244132423121202,0x323445243131334,0x252232525224235,0x244132423021202,0x322445242122234,0x252232525324235,0x343123433120212,0x423435343131324,0x252242525223245,0x344133433021212,0x422445342121234,0x252242525224245,0x343123433020212,0x422435342221224,0x252243525223245,0x243222423120202,0x333435243131324,0x252332535223335,0x344233433121212,0x433445343232334,0x252343535324345,0x23240221202002,0x112031222422421,0x301003031132102,0x201222023200020,0x114233422224201,0x301003231330120,0x3220023202000,0x114253222422221,0x301005231132100,0x221222241200022,0x312031222224401,0x301023031330122,0x15222201202200,0x32033202442222,0x301103131133112,0x213202023200020,0x234233422224200,0x301103131331110,0x213422023002020,0x232253420222020,0x301103151131310,0x13222003202000,0x34253222422220,0x301105131131110,0x213204221200220,0x232033202244202],
  #[0x301123131331132,0x203422023002020,0x132253420202221,0x301203251132320,0x223442241002022,0x332031220202221,0x301223031132322,0x215424221002220,0x252033200222022,0x301323131133332,0x223220101222000,0x112231204422242,0x303103130333312,0x203422121202020,0x132231202424220,0x303103130351310,0x213422021202020,0x232033202424220,0x303103131351310,0x201202123200020,0x114233422224220,0x303103132331310,0x203422123002020,0x132253422202020,0x303103152331310,0x203220103202000,0x114253222422220,0x303105132331310,0x223422021202020,0x332032202424220,0x303113030351311,0x203422221202020,0x132131202424220,0x303113031351311,0x421202121220020,0x312231204224222,0x303123130531332,0x203422021202020,0x132031222424221,0x303203031352320,0x214433231202121,0x242132212434321,0x303213131352321,0x203422021202020,0x132031212424222,0x303313130353331,0x423422121022020,0x332231202202042,0x303323130333532,0x334443341212122,0x442132223434430,0x304113032451411,0x323432131212021,0x332132213424331,0x304213131452421,0x314423121212120,0x242132213434232,0x304313131453431,0x344342332222112,0x433340234433443,0x304334030444434,0x443333342221122,0x533330334334433,0x304343030543444],
  #[0x305434331212221,0x152133213444333,0x304413232454441,0x444443342122122,0x542340333323343,0x304443040444544,0x434433031222121,0x442232214434343,0x305413230554541,0x444443341222122,0x542230224434443,0x305443030554544,0x23221003202000,0x124253222422220,0x311005131131101,0x222202023200020,0x324233422224200,0x311013131330111,0x3220013202000,0x14253222422222,0x311105331133111,0x23240221202002,0x112031222422422,0x311113131133113,0x25222201202200,0x132033202442222,0x311113131133113,0x223202023200020,0x334233422224200,0x311113131331111,0x223422023002020,0x332253420212020,0x311113151131311,0x223422023002020,0x332253420222020,0x311113151131311,0x201212023200020,0x114233422224202,0x311113331331131,0x201222023200020,0x114233422224202,0x311113331331131,0x23222003202000,0x134253222422220,0x311115131131111,0x3220023202000,0x114253222422222,0x311115331133111,0x221222241200022,0x312031222224402,0x311133131331133,0x223204221200220,0x332033202244202,0x311133131331133,0x203422023002020,0x132253420202122,0x311313351133331,0x203422023002020,0x132253420202222,0x311313351133331,0x223442241002022,0x332031220202222,0x311333131133333,0x225424221002220],
  #[0x352033200222022,0x311333131133333,0x103220203202000,0x14253222422220,0x312005133231201,0x134241323212102,0x224354243432430,0x312005134231201,0x201202223200020,0x114233422224210,0x312013133330211,0x332223343210122,0x424334443234410,0x312013134430211,0x123231113212001,0x124353233422331,0x312105232232211,0x114231213202101,0x124254232432321,0x312105233232211,0x114221113212100,0x124354223432232,0x312105332233211,0x134241321212102,0x222132223432432,0x312113132233213,0x332223343210122,0x424334443234410,0x312113134431211,0x203422223002020,0x132253421202020,0x312113153231311,0x334443343012122,0x442354441212230,0x312113154231411,0x322212133210021,0x324333433224311,0x312113232431221,0x212213233200121,0x224234432234311,0x312113233331221,0x312213123210120,0x224334423234212,0x312113332431231,0x312223123210120,0x224334423234212,0x312113332431231,0x123341232202012,0x223142232423421,0x312114132242212,0x134241323212102,0x224354243432430,0x312115134231211,0x114221123212100,0x224354223432232,0x312115332233211,0x222332242201022,0x323132332324411,0x312123132341222,0x332223341210122,0x422132223234412,0x312133132431233,0x105232313212201,0x34355233442333],
  #[0x312205434234221,0x125232311212201,0x132133213442333,0x312213232234223,0x323212133210021,0x334333433224311,0x312213232432221,0x323432133012021,0x332353431212131,0x312213252232421,0x323432133012021,0x332353431222131,0x312213252232421,0x214433233002121,0x242254431212121,0x312213253232321,0x303214333210221,0x134335433244313,0x312213434432241,0x115323212202210,0x143144212443222,0x312214232243222,0x123232113212001,0x134353233422331,0x312215232232221,0x105232313212201,0x134355233442333,0x312215434234221,0x223442242102022,0x332142331313321,0x312223142242322,0x214314222201220,0x243134312344212,0x312223232342232,0x323214331210221,0x332133213244313,0x312233232432243,0x314423123012120,0x242354421212132,0x312313352233431,0x314423123012120,0x242354421212232,0x312313352233431,0x215424222102220,0x252144311333122,0x312323242243332,0x334443341012122,0x442132221212232,0x312333132233433,0x305434333012221,0x152355431222133,0x312413454234441,0x325434331012221,0x352133211222133,0x312433232234443,0x223220201222000,0x112231204422242,0x313113131333313,0x203422221202020,0x132231202424220,0x313113131351311,0x223422021202020,0x332033202424220,0x313113131351311],
  #[0x201202223200020,0x114233422224220,0x313113133331311,0x203422223002020,0x132253422202020,0x313113153331311,0x203220203202000,0x114253222422220,0x313115133331311,0x421202221220020,0x312231204224222,0x313133131531333,0x234231013222101,0x224454234432343,0x313205431334321,0x234231211222101,0x222232214432343,0x313213231334323,0x214433231202121,0x242232212434321,0x313213231352321,0x212213233200121,0x224234432234321,0x313213233332321,0x214433233002121,0x242254432212121,0x313213253332321,0x432213033220121,0x424434434234323,0x313213431532341,0x214231213202101,0x224254232432321,0x313215233332321,0x234231013222101,0x224454234432343,0x313215431334321,0x224443341202122,0x342132222434421,0x313223132352322,0x432213231220121,0x422232214234323,0x313233231532343,0x203422021202020,0x132031222424222,0x313313131353331,0x215434331202221,0x252133212444322,0x313323232353332,0x423422221022020,0x332231202202042,0x313333131333533,0x235343432212212,0x343044233443433,0x313334134344334,0x334334442211222,0x443034333344423,0x313343134443344,0x434433033022121,0x442454432212143,0x313413451334541,0x434433231022121,0x442232212212143,0x313433231334543,0x335444442112222],
  #[0x452044332333333,0x313443144344444,0x334443341212122,0x442132223434430,0x314113132451411,0x323432131212021,0x332133213424331,0x314213232452421,0x323321112222010,0x223342214423242,0x314214231443422,0x333442241212022,0x432132223424431,0x314223132452422,0x334443341212122,0x442132223434431,0x314223132452422,0x422312122221020,0x323332314324232,0x314223231542432,0x314423121212120,0x242132223434232,0x314313132453431,0x423422122122020,0x332342313313142,0x314323241443532,0x334443341212122,0x442132223434432,0x314333132453433,0x344342332222112,0x433341234433443,0x314334131444434,0x443333342221122,0x533331334334433,0x314343131543444,0x305434331212221,0x152133213444333,0x314413232454441,0x315424221212220,0x252133213444233,0x314423232454442,0x315434331212221,0x252133213444333,0x314423232454442,0x325434331212221,0x352133213444333,0x314433232454443,0x335333322222211,0x343344204443344,0x314434431445444,0x335444441212222,0x452033223444433,0x314443133454444,0x444443342122122,0x542341333323343,0x314443141444544,0x434324332221221,0x443334304344334,0x314443431544454,0x435434332122221,0x452344303333244,0x314543441445554,0x433432131222021,0x432232214424342],
  #[0x315323231553532,0x434433031222121,0x442232214434343,0x315413231554541,0x424423121222120,0x342232214434243,0x315423231554542,0x434433131222121,0x442232214434343,0x315423231554542,0x434433231222121,0x442232214434343,0x315433231554543,0x444443341222122,0x542231224434443,0x315443131554544,0x435434331222221,0x452233204444344,0x315543331555554,0x21220223200002,0x114233242222401,0x321003233130102,0x23240223002002,0x112253240202221,0x321003233132102,0x122231233201012,0x214243342323411,0x321014233231112,0x221222243000022,0x312233440202201,0x321023233130122,0x13202203200200,0x34235222242202,0x321103333131112,0x15222203002200,0x32255220222022,0x321103333133112,0x123341233102012,0x223253341312321,0x321114243132212,0x114213213201210,0x134245322343212,0x321114333232122,0x222332243101022,0x323243441213311,0x321123243231222,0x213204223000220,0x232235420222002,0x321123333131132,0x115323213102210,0x143255321332122,0x321214343133222,0x214314223101220,0x243245421233112,0x321223343232232,0x133241223212002,0x224353243422431,0x322115233232212,0x124241323202102,0x224254242432421,0x322115234232212,0x134241323212102,0x224354243432431,0x322115234232212],
  #[0x332222243210022,0x424333443224411,0x322123233431222,0x222223343200122,0x324234442234411,0x322123234331222,0x332223343210122,0x424334443234411,0x322123234431222,0x115232313202201,0x134255232442322,0x322215334233222,0x115222213212200,0x134355223442233,0x322215433234222,0x115232313212201,0x134355233442333,0x322215434234222,0x135242421212202,0x232133223442433,0x322223233234224,0x333222243210022,0x434333443224411,0x322223233432222,0x332223343210122,0x424334443234411,0x322223234432222,0x333442243012022,0x432353441212231,0x322223253232422,0x333442243012022,0x432353441222231,0x322223253232422,0x224443343002122,0x342254441212221,0x322223254232322,0x334443343012122,0x442354441212231,0x322223254232422,0x213214333200221,0x234235432244312,0x322223334332232,0x313214223210220,0x234335423244213,0x322223433432242,0x313224223210220,0x234335423244213,0x322223433432242,0x313214333210221,0x234335433244313,0x322223434432242,0x123341232202012,0x223142232423422,0x322224232243223,0x125323212202210,0x243144212443222,0x322224232243223,0x125343432202212,0x243144232443422,0x322224234243223,0x133242223212002,0x234353243422431,0x322225233232222,0x134241323212102],
  #[0x224354243432431,0x322225234232222,0x115222223212200,0x234355223442233,0x322225433234222,0x115232313212201,0x234355233442333,0x322225434234222,0x222332242201022,0x323132332324412,0x322233232342233,0x224314222201220,0x343134312344212,0x322233232342233,0x224334442201222,0x343134332344412,0x322233234342233,0x333224441210222,0x432133223244413,0x322243233432244,0x215434333002221,0x252255431222122,0x322323354233332,0x223442242102022,0x332142331313322,0x322333242243333,0x225424222102220,0x352144311333122,0x322333242243333,0x225444442102222,0x352144331333322,0x322333244243333,0x315424223012220,0x252355421222133,0x322423453234442,0x315424223012220,0x252355421222233,0x322423453234442,0x315434333012221,0x252355431222133,0x322423454234442,0x335444441012222,0x452133221222233,0x322443233234444,0x221200103220000,0x114433224222222,0x323103332331312,0x223220103022000,0x112453222202042,0x323103332333312,0x322211113221010,0x214443324323232,0x323114332432322,0x421202123020020,0x312433422202022,0x323123332331332,0x323321113122010,0x223453323312142,0x323214342333422,0x233231113222001,0x224453234422342,0x323215332333322,0x224221113222100,0x224454224432243],
  #[0x323215432334322,0x234231113222101,0x224454234432343,0x323215432334322,0x244241321222102,0x322232224432443,0x323223232334324,0x224443341202122,0x342232222434421,0x323223232352322,0x222223343200122,0x324234442234421,0x323223234332322,0x224443343002122,0x342254442212221,0x323223254332322,0x432212133220021,0x424433434224322,0x323223332532332,0x422312123121020,0x323443423213132,0x323223342432432,0x422213123220120,0x324434424234223,0x323223432532342,0x422223123220120,0x324434424234223,0x323223432532342,0x432213133220121,0x424434434234323,0x323223432532342,0x234342332212112,0x333243233433432,0x323224233343323,0x224241323202102,0x324254242432421,0x323225234332322,0x234231113222101,0x224454234432343,0x323225432334322,0x224221123222100,0x324454224432243,0x323225432334322,0x333333342211122,0x433233333334422,0x323233233442333,0x442223341220122,0x522232224234423,0x323243232532344,0x235232311222201,0x232233214442344,0x323323332335334,0x215434331202221,0x252233212444322,0x323323332353332,0x433212133220021,0x434433434224322,0x323323332533332,0x213214333200221,0x234235432244322,0x323323334333332,0x433432133022021,0x432453432212142,0x323323352333532],
  #[0x433432133022021,0x432453432222142,0x323323352333532,0x215434333002221,0x252255432222122,0x323323354333332,0x225333322212211,0x243244223443333,0x323324333344333,0x233232113222001,0x234453234422342,0x323325332333332,0x215232313202201,0x234255232442322,0x323325334333332,0x334443342112122,0x442243332323332,0x323333243343433,0x324324332211221,0x343234323344323,0x323333333443343,0x235343432212212,0x343144233443433,0x323334234344334,0x334334442211222,0x443134333344423,0x323343234443344,0x433214331220221,0x432233214244324,0x323343332533354,0x424423123022120,0x342454422212143,0x323423452334542,0x424423123022120,0x342454422212243,0x323423452334542,0x434433133022121,0x442454432212143,0x323423452334542,0x325434332112221,0x352244322333233,0x323433343344443,0x444443341022122,0x542232222212243,0x323443232334544,0x335444442112222,0x452144332333333,0x323443244344444,0x435434331022221,0x452233212222144,0x323543332335554,0x334443341212122,0x442132223434431,0x324223232452422,0x333442241212022,0x432133223424431,0x324223233452422,0x323321212222010,0x223342214423242,0x324224232443423,0x343341232222012,0x423342234423442,0x324224232443423,0x422312222221020],
  #[0x323332314324232,0x324233232542433,0x442332242221022,0x523332334324432,0x324233232542433,0x334332222222111,0x333343224433343,0x324324332444433,0x423422222122020,0x332342313313142,0x324333242443533,0x443442242122022,0x532342333313342,0x324333242443533,0x433323232221121,0x433333324334333,0x324333332543443,0x344342332222112,0x433342234433443,0x324334232444434,0x443333342221122,0x533332334334433,0x324343232543444,0x315434331212221,0x252133213444333,0x324423232454442,0x315424221212220,0x252133223444233,0x324423233454442,0x325323212222210,0x243344214443244,0x324424432445443,0x434433232122121,0x442343323323243,0x324433342444543,0x424314222221220,0x343334314344234,0x324433432544453,0x335333322222211,0x343344214443344,0x324434432445444,0x444443342122122,0x542342333323343,0x324443242444544,0x434324332221221,0x443334314344334,0x324443432544454,0x425424222122220,0x352344313333144,0x324533442445553,0x435434332122221,0x452344313333244,0x324543442445554,0x433432131222021,0x432233214424342,0x325323332553532,0x424423121222120,0x342232224434243,0x325423232554542,0x434433131222121,0x442232214434343,0x325423232554542,0x21220223200002,0x114233242222402],
  #[0x331113333131113,0x23202203200200,0x134235222242202,0x331113333131113,0x23240223002002,0x112253240202222,0x331113333133113,0x25222203002200,0x132255220222022,0x331113333133113,0x35343432212212,0x143244233443433,0x331114334144114,0x122231233201012,0x214243342323412,0x331124333232123,0x124213213201210,0x234245322343212,0x331124333232123,0x124233433201212,0x234245342343412,0x331124335232123,0x221222243000022,0x312233440202202,0x331133333131133,0x223204223000220,0x332235420222002,0x331133333131133,0x334334442211222,0x443234333344403,0x331143334441144,0x123341233102012,0x223253341312322,0x331224343133223,0x125323213102210,0x243255321332122,0x331224343133223,0x125343433102212,0x243255341332322,0x331224345133223,0x222332243101022,0x323243441213312,0x331233343232233,0x224314223101220,0x343245421233112,0x331233343232233,0x224334443101222,0x343245441233312,0x331233345232233,0x335444442112222,0x452244330333333,0x331443344144444,0x132221323210102,0x224334243232412,0x332113334231213,0x134241323012102,0x222354241212232,0x332113334233213,0x134241323212102,0x224354243432432,0x332115334233213,0x233232333211112,0x324344343333422,0x332124334332223],
  #[0x332223343010122,0x422334441212212,0x332133334231233,0x332223343210122,0x424334443234412,0x332133334431233,0x123212313210201,0x134335233242313,0x332213434232223,0x125232313012201,0x132355231222133,0x332213434234223,0x125232313212201,0x134355233442333,0x332215434234223,0x135343432212212,0x243244233443433,0x332224334244224,0x234342333112112,0x333354342322332,0x332224344233323,0x224223323211211,0x234345333343323,0x332224434333233,0x333333343111122,0x433344442223322,0x332233344332333,0x323214333010221,0x332335431222113,0x332233434232243,0x323214333210221,0x334335433244313,0x332233434432243,0x334334442211222,0x443234333344413,0x332243334442244,0x225333323112211,0x243355332332233,0x332324444234333,0x334443343012122,0x442354441212232,0x332333354233433,0x324324333111221,0x343345432233223,0x332333444333343,0x325434333012221,0x352355431222133,0x332433454234443,0x335444442112222,0x452244331333333,0x332443344244444,0x221200203220000,0x114433224222222,0x333113333331313,0x223220203022000,0x112453222202042,0x333113333333313,0x322211213221010,0x214443324323232,0x333124333432323,0x342231233221012,0x414443344323432,0x333124333432323,0x421202223020020],
  #[0x312433422202022,0x333133333331333,0x232211213220101,0x224434234232323,0x333213433332323,0x234231213022101,0x222454232212143,0x333213433334323,0x234231213222101,0x224454234432343,0x333215433334323,0x323321213122010,0x223453323312142,0x333224343333423,0x343341233122012,0x423453343312342,0x333224343333423,0x333222223221111,0x324444334333333,0x333224433433333,0x422312223121020,0x323443423213132,0x333233343432433,0x442332243121022,0x523443443213332,0x333233343432433,0x432213233020121,0x422434432212123,0x333233433332343,0x432213233220121,0x424434434234323,0x333233433532343,0x334332223122111,0x333454333322243,0x333324443334433,0x324213213221210,0x234445324343234,0x333324533434343,0x245242421222202,0x332233224442444,0x333333333335335,0x225444441202222,0x352233222444422,0x333333333353333,0x443222243220022,0x534433444224422,0x333333333533333,0x223224443200222,0x334235442244422,0x333333335333333,0x443442243022022,0x532453442222242,0x333333353333533,0x225444443002222,0x352255442222222,0x333333355333333,0x433323233121121,0x433444433223233,0x333333443433443,0x423224223220220,0x334435424244224,0x333333533533353,0x235343432212212,0x343244233443433],
  #[0x333334334344334,0x243242223222002,0x334453244422442,0x333335333333333,0x225242423202202,0x334255242442422,0x333335335333333,0x225222223222200,0x334455224442244,0x333335533335333,0x334334442211222,0x443234333344423,0x333343334443344,0x443224441220222,0x532233224244424,0x333353333533355,0x325323213122210,0x243455323332144,0x333424543335443,0x434433233022121,0x442454432212143,0x333433453334543,0x424314223121220,0x343445423233134,0x333433543434453,0x335444442112222,0x452244332333333,0x333443344344444,0x425424223022220,0x352455422222244,0x333533553335553,0x445444441022222,0x552233222222244,0x333553333335555,0x440333342221122,0x503333334334433,0x334043333540444,0x344340332222112,0x413343234433443,0x334114333444414,0x441333342221122,0x513333334334433,0x334143333541444,0x344341332222112,0x423343234433443,0x334224333444424,0x442333342221122,0x523333334334433,0x334243333542444,0x344342332222112,0x433343234433443,0x334334333444434,0x443333342221122,0x533333334334433,0x334343333543444,0x335333302222211,0x143344224443344,0x334414433445444,0x335333312222211,0x243344224443344,0x334424433445444,0x335333322222211,0x343344224443344,0x334434433445444],
  #[0x444443342122122,0x542343333303343,0x334443343444544,0x444443342122122,0x542343333313343,0x334443343444544,0x444443342122122,0x542343333323343,0x334443343444544,0x434304332221221,0x443334324344334,0x334443433544454,0x434314332221221,0x443334324344334,0x334443433544454,0x434324332221221,0x443334324344334,0x334443433544454,0x435434332122221,0x452344323333044,0x334543443445554,0x435434332122221,0x452344323333144,0x334543443445554,0x435434332122221,0x452344323333244,0x334543443445554,0x443442241222022,0x532233224424442,0x335333333553533,0x425424221222220,0x352233224444244,0x335533333555553,0x34233433211212,0x134345343343423,0x341114435133114,0x35343433112212,0x143355342332333,0x341114445134114,0x35242423212202,0x134355243442433,0x341115435134114,0x134233433211212,0x234345343343423,0x341124435233124,0x234233433211212,0x334345343343403,0x341134435331134,0x234233433211212,0x334345343343413,0x341134435332134,0x333224443210222,0x434335443244403,0x341143435431144,0x334334443111222,0x443345442233303,0x341143445331144,0x135343433112212,0x243355342332333,0x341224445134224,0x334334443111222,0x443345442233313,0x341243445332244,0x235343433112212],
  #[0x343355340332333,0x341334445134334,0x235343433112212,0x343355341332333,0x341334445134334,0x334334443111222,0x443345440233323,0x341343445133344,0x334334443111222,0x443345441233323,0x341343445233344,0x335444443012222,0x452355440222233,0x341443455134444,0x133222423210202,0x234335243242413,0x342223435232224,0x135242423012202,0x232355241222233,0x342223435234224,0x234233433211212,0x334345343343423,0x342234435333234,0x333224443010222,0x432335441222213,0x342243435232244,0x235343433112212,0x343355342332333,0x342334445234334,0x334334443111222,0x443345442233323,0x342343445333344,0x340232333221112,0x404444344333433,0x343034434430334,0x440223343220122,0x504434444234423,0x343043434530344,0x440333343121122,0x503444443223333,0x343043444430444,0x343230333221112,0x414444344333433,0x343114434433314,0x344340333122112,0x413454343322343,0x343114444334414,0x244240323222102,0x314454244432443,0x343115434334314,0x343231333221112,0x414444344333433,0x343124434433324,0x341232333221112,0x414444344333433,0x343134434431334,0x342232333221112,0x414444344333433,0x343134434432334,0x441223343220122,0x514434444234423,0x343143434531344,0x441333343121122,0x513444443223333],
  #[0x343143444431444,0x242221323220102,0x324434244232423,0x343223434332324,0x244241323022102,0x322454242212243,0x343223434334324,0x344341333122112,0x423454343322343,0x343224444334424,0x343232333221112,0x424444344333433,0x343234434433334,0x442223343020122,0x522434442212223,0x343243434332344,0x442333343121122,0x523444443223333,0x343243444432444,0x334223303221211,0x134445334343334,0x343314534434344,0x235232303222201,0x134455234442344,0x343315534335334,0x233212313220201,0x234435234242324,0x343323534333334,0x235232313022201,0x232455232222144,0x343323534335334,0x334223313221211,0x234445334343334,0x343324534434344,0x344342333122112,0x433454343302343,0x343334444334434,0x344342333122112,0x433454343312343,0x343334444334434,0x344342333122112,0x433454343322343,0x343334444334434,0x334203323221211,0x334445334343334,0x343334534434344,0x334213323221211,0x334445334343334,0x343334534434344,0x334223323221211,0x334445334343334,0x343334534434344,0x443333343121122,0x533444443203333,0x343343444433444,0x443333343121122,0x533444443213333,0x343343444433444,0x443333343121122,0x533444443223333,0x343343444433444,0x433214333020221,0x432435432222124,0x343343534333354],
  #[0x433204333220221,0x434435434244324,0x343343534533354,0x335333303122211,0x143455333332244,0x343414544335444,0x335333313122211,0x243455333332244,0x343424544335444,0x335333323122211,0x343455333332044,0x343434544335444,0x335333323122211,0x343455333332144,0x343434544335444,0x335333323122211,0x343455333332244,0x343434544335444,0x444443343022122,0x542454442202243,0x343443454334544,0x434324333121221,0x443445433233034,0x343443544434454,0x434324333121221,0x443445433233134,0x343443544434454,0x434304333121221,0x443445433233234,0x343443544434454,0x434314333121221,0x443445433233234,0x343443544434454,0x434324333121221,0x443445433233234,0x343443544434454,0x435434333022221,0x452455432222044,0x343543554335554,0x243222423220202,0x334435244242424,0x353333535333335,0x245242423022202,0x332455242222244,0x353333535335335,0x443224443020222,0x532435442222224,0x353353535333355,0x213432132202021,0x233142322424321,0x403214141352321,0x214423122202120,0x243143312434221,0x403214141352321,0x224443342202122,0x343141332434421,0x403224041352322,0x215434332202221,0x253144302444322,0x403324241353332,0x313422122212020,0x233242313424231,0x404214141452421,0x333442242212022],
  #[0x433042333424431,0x404224042452422,0x334443342212122,0x443240333434432,0x404334040453433,0x315424222212220,0x253044313444233,0x404424142454442,0x433432132222021,0x433342304424342,0x405324240553532,0x443442242222022,0x533340334424442,0x405334040553533,0x424423122222120,0x343341314434243,0x405424140554542,0x434433232222121,0x443340324434343,0x405434040554543,0x444443342222122,0x543340334434443,0x405444040554544,0x113331123202011,0x124253332423321,0x412105242242211,0x114322113202110,0x134254322433221,0x412105242242211,0x212322133201021,0x224243432324311,0x412114242341221,0x213313123201120,0x234244422334211,0x412114242341221,0x213432133102021,0x233253431313221,0x412214252242321,0x214423123102120,0x243254421323121,0x412214252242321,0x213321113212010,0x124353323423231,0x413105242342311,0x333333343211122,0x434344443334420,0x413114144441311,0x334443343112122,0x443354442323330,0x413114154341411,0x312312123211020,0x224343423324221,0x413114242441321,0x234342333212112,0x334354343433430,0x413115144341311,0x313422123112020,0x233353422313131,0x413214252342421,0x224443342202122,0x343141332434421,0x413224141352322,0x224423122202120,0x343143312434221],
  #[0x413224141352322,0x223442242202022,0x333142332424421,0x413224142352322,0x224443342202122,0x343142332434421,0x413224142352322,0x224443342202122,0x343143332434421,0x413224143352322,0x304324333211221,0x144345433344323,0x413314444443341,0x205333323212211,0x144355333443333,0x413315444344331,0x213432132202021,0x233142322424322,0x413324241353332,0x215434332202221,0x253144302444322,0x413324241353332,0x215424222202220,0x253144312444222,0x413324242353332,0x215434332202221,0x253144312444322,0x413324242353332,0x215434332202221,0x253144322444322,0x413324243353332,0x225444442202222,0x353044332444422,0x413334144353333,0x305434333112221,0x153355432333233,0x413414454344441,0x334443342212122,0x443243333434430,0x414114143451411,0x313422222212020,0x233242313424231,0x414224142452422,0x333442242212022,0x433042333424431,0x414224142452422,0x333442242212022,0x433142333424431,0x414224142452422,0x333442242212022,0x433242333424431,0x414224142452422,0x334443342212122,0x443243333434431,0x414224143452422,0x433323033221121,0x434444434334333,0x414314441543441,0x334332023222111,0x334454334433343,0x414315441444431,0x324433232212121,0x343243323434332,0x414324242453432],
  #[0x334443342212122,0x443241333434432,0x414334141453433,0x334443342212122,0x443242333434432,0x414334142453433,0x334443342212122,0x443043333434432,0x414334143453433,0x334443342212122,0x443143333434432,0x414334143453433,0x305434332212221,0x153244323444333,0x414414343454441,0x434433033122121,0x443454433323243,0x414414451444541,0x315424222212220,0x253044313444233,0x414424142454442,0x315424222212220,0x253144313444233,0x414424242454442,0x315424222212220,0x253244313444233,0x414424342454442,0x315434332212221,0x253244323444333,0x414424343454442,0x325434332212221,0x353044323444333,0x414434143454443,0x325434332212221,0x353144323444333,0x414434243454443,0x325434332212221,0x353244303444333,0x414434341454443,0x325434332212221,0x353244313444333,0x414434342454443,0x335444442212222,0x453044333444433,0x414444144454444,0x423422122222020,0x333342314424242,0x415324241553532,0x433432132222021,0x433342304424342,0x415324241553532,0x433432132222021,0x433342314424342,0x415324241553532,0x433432132222021,0x433342324424342,0x415324241553532,0x443442242222022,0x533341334424442,0x415334141553533,0x434433032222121,0x443343324434343,0x415414341554541,0x424423122222120],
  #[0x343341314434243,0x415424141554542,0x424423122222120,0x343342314434243,0x415424241554542,0x424423122222120,0x343343314434243,0x415424341554542,0x434433132222121,0x443343324434343,0x415424341554542,0x434433232222121,0x443341324434343,0x415434141554543,0x434433232222121,0x443342324434343,0x415434241554543,0x434433232222121,0x443343304434343,0x415434341554543,0x434433232222121,0x443343314434343,0x415434341554543,0x444443342222122,0x543341334434443,0x415444141554544,0x425424222222220,0x353344304444244,0x415534441555553,0x435434332222221,0x453344304444344,0x415544441555554,0x33341233212012,0x124353343423431,0x421005243142102,0x332332243211022,0x424343443324401,0x421024243440122,0x15323213212210,0x44355323443233,0x421105443144112,0x33341233212012,0x124353343423431,0x421115243142112,0x15323213212210,0x144355323443233,0x421115443144112,0x332332243211022,0x424343443324401,0x421124243441122,0x314314223211220,0x244345423344203,0x421124443441142,0x333442243112022,0x433353440313331,0x421224253142422,0x315424223112220,0x253355420333133,0x421424453144442,0x124340333202112,0x214254342433421,0x422005244242202,0x221333343201122,0x314244442334411],
  #[0x422024244340222,0x124322113202110,0x234254322433221,0x422115242242212,0x123341233202012,0x224253342423421,0x422115243242212,0x133341233212012,0x224353343423431,0x422115243242212,0x124340333202112,0x214254342433421,0x422115244242212,0x124341333202112,0x224254342433421,0x422115244242212,0x124342333202112,0x234254342433421,0x422115244242212,0x223313123201120,0x334244422334211,0x422124242341222,0x332332243211022,0x424343443324411,0x422124243441222,0x221333343201122,0x314244442334411,0x422124244341222,0x222333343201122,0x324244442334411,0x422124244341222,0x223333343201122,0x334244442334411,0x422124244341222,0x115333303202211,0x44255332443322,0x422205344243222,0x113331123202011,0x124253332423322,0x422215342243222,0x115323213202210,0x144255322443222,0x422215343243222,0x115333303202211,0x144255332443322,0x422215344243222,0x115333313202211,0x144255332443322,0x422215344243222,0x115333323202211,0x144255332443322,0x422215344243222,0x115323213212210,0x144355323443233,0x422215443244222,0x332332243211022,0x424343443324411,0x422224243442222,0x222333343201122,0x324244442334411,0x422224244342222,0x224423123102120,0x343254421323121,0x422224252242322],
  #[0x333442243112022,0x433353441313331,0x422224253242422,0x224443343102122,0x343254441303321,0x422224254242322,0x224443343102122,0x343254441313321,0x422224254242322,0x224443343102122,0x343254441323321,0x422224254242322,0x212322133201021,0x224243432324312,0x422224342342232,0x214304333201221,0x244245432344312,0x422224344342232,0x214314333201221,0x244245432344312,0x422224344342232,0x214324333201221,0x244245432344312,0x422224344342232,0x314314223211220,0x244345423344213,0x422224443442242,0x133341233212012,0x224353343423431,0x422225243242222,0x124341333202112,0x224254342433421,0x422225244242222,0x115333313202211,0x244255332443322,0x422225344243222,0x115323213212210,0x244355323443233,0x422225443244222,0x213432133102021,0x233253431313222,0x422324352243332,0x215424223102220,0x253255421333122,0x422324353243332,0x215434333102221,0x253255431333022,0x422324354243332,0x215434333102221,0x253255431333122,0x422324354243332,0x215434333102221,0x253255431333222,0x422324354243332,0x315424223112220,0x253355421333133,0x422424453244442,0x213321213212010,0x124353323423231,0x423115243342312,0x233341233212012,0x324353343423431,0x423115243342312,0x234342333212112],
  #[0x334354343433431,0x423115244342312,0x312312223211020,0x224343423324221,0x423124243441322,0x332332243211022,0x424343443324421,0x423124243441322,0x333333343211122,0x434344443334421,0x423124244441322,0x224332223212111,0x234354333433332,0x423215343343322,0x224443342202122,0x343142332434421,0x423224242352322,0x313422223112020,0x233353422313131,0x423224253342422,0x333442243112022,0x433353442313331,0x423224253342422,0x334443343112122,0x443354442323331,0x423224254342422,0x323323233211121,0x334344433334322,0x423224343442332,0x215323213212210,0x144355323443233,0x423315443344332,0x215333323212211,0x144355333443333,0x423315444344332,0x215434332202221,0x253144312444322,0x423324242353332,0x324433233112121,0x343354432323232,0x423324353343432,0x314314223211220,0x244345423344223,0x423324443443342,0x314324333211221,0x244345433344323,0x423324444443342,0x223442242202022,0x333142332424422,0x423334242353333,0x225424222202220,0x353144312444222,0x423334242353333,0x315424223112220,0x253355422333133,0x423424453344442,0x315434333112221,0x253355432333233,0x423424454344442,0x420313123221120,0x304444424334233,0x424024442540442,0x324320113222110,0x214454324433243],
  #[0x424105442444412,0x324320113222110,0x214454324433243,0x424115442444412,0x421313123221120,0x314444424334233,0x424124442541442,0x333331103222011,0x124453334423342,0x424205342443422,0x333331103222011,0x124453334423342,0x424215342443422,0x333331113222011,0x224453334423342,0x424215342443422,0x333331123222011,0x324453334423342,0x424215342443422,0x324321113222110,0x224454324433243,0x424215442444422,0x333442242212022,0x433142333424431,0x424224242452422,0x432302133221021,0x424443434324332,0x424224342542432,0x432312133221021,0x424443434324332,0x424224342542432,0x432322133221021,0x424443434324332,0x424224342542432,0x422313123221120,0x324444424334233,0x424224442542442,0x333331113222011,0x224453334423342,0x424225342443422,0x324321113222110,0x224454324433243,0x424225442444422,0x324322113222110,0x234454324433243,0x424315442444432,0x334332123222111,0x334454334433343,0x424315442444432,0x423422123122020,0x333453423313142,0x424324352443532,0x433432133122021,0x433453433313042,0x424324352443532,0x433432133122021,0x433453433313142,0x424324352443532,0x433432133122021,0x433453433313242,0x424324352443532,0x423313123221120,0x334444424334233,0x424324442543442],
  #[0x433323133221121,0x434444434334333,0x424324442543442,0x334443342212122,0x443243333434432,0x424334243453433,0x315424222212220,0x253144313444233,0x424424242454442,0x424423123122120,0x343454423303143,0x424424452444542,0x424423123122120,0x343454423313143,0x424424452444542,0x424423123122120,0x343454423323143,0x424424452444542,0x434433133122121,0x443454433323243,0x424424452444542,0x325434332212221,0x353244323444333,0x424434343454443,0x433432132222021,0x433342314424342,0x425324242553532,0x423422222222020,0x333342314424242,0x425334242553533,0x424423122222120,0x343342314434243,0x425424242554542,0x434433232222121,0x443343324434343,0x425434342554543,0x34342333212112,0x134354343433432,0x431115344143113,0x25343433202212,0x144255342443422,0x431115345143113,0x25333323212211,0x144355333443333,0x431115444144113,0x333333343211122,0x434344443334402,0x431134344441133,0x224334443201222,0x344245442344402,0x431134345341133,0x324324333211221,0x344345433344303,0x431134444441143,0x334443343112122,0x443354440323332,0x431334354143433,0x225444443102222,0x353255440333322,0x431334355143333,0x325434333112221,0x353355430333233,0x431434454144443,0x134342333212112],
  #[0x234354343433432,0x432115344243213,0x333333343211122,0x434344443334412,0x432134344441233,0x125333323212211,0x144355333443333,0x432215444244223,0x123341233202012,0x224253342423422,0x432225343243223,0x125323213202210,0x244255322443222,0x432225343243223,0x222332243201022,0x324243442324412,0x432234343342233,0x224314223201220,0x344245422344212,0x432234343342233,0x324324333211221,0x344345433344313,0x432234444442243,0x223442243102022,0x333253441313322,0x432334353243333,0x225424223102220,0x353255421333122,0x432334353243333,0x334443343112122,0x443354441323332,0x432334354243433,0x325434333112221,0x353355431333233,0x432434454244443,0x330333343211122,0x404344443334422,0x433034344440333,0x234340333212112,0x314354343433432,0x433115344343313,0x234341333212112,0x324354343433432,0x433115344343313,0x331333343211122,0x414344443334422,0x433134344441333,0x332333343211122,0x424344443334422,0x433134344441333,0x234342333212112,0x334354343433432,0x433225344343323,0x333333343211122,0x434344443334422,0x433234344442333,0x225333303212211,0x144355333443333,0x433315444344333,0x225333313212211,0x144355333443333,0x433315444344333,0x225333323212211,0x244355333443333],
  #[0x433325444344333,0x334443343112122,0x443354442303332,0x433334354343433,0x334443343112122,0x443354442313332,0x433334354343433,0x334443343112122,0x443354442323332,0x433334354343433,0x324304333211221,0x344345433344323,0x433334444443343,0x324314333211221,0x344345433344323,0x433334444443343,0x324324333211221,0x344345433344323,0x433334444443343,0x325434333112221,0x353355432333033,0x433434454344443,0x325434333112221,0x353355432333133,0x433434454344443,0x325434333112221,0x353355432333233,0x433434454344443,0x440332243221022,0x504443444324432,0x434034343540433,0x430323233221121,0x404444434334333,0x434034443540443,0x343340233222012,0x414453344423442,0x434115343443413,0x334330223222111,0x314454334433343,0x434115443444413,0x441332243221022,0x514443444324432,0x434134343541433,0x431323233221121,0x414444434334333,0x434134443541443,0x334331223222111,0x324454334433343,0x434215443444423,0x323321213222010,0x224453324423242,0x434225343443423,0x422312223221020,0x324443424324232,0x434234343542433,0x432323233221121,0x424444434334333,0x434234443542443,0x334332203222111,0x134454334433343,0x434315443444433,0x334332213222111,0x234454334433343,0x434315443444433],
  #[0x334332223222111,0x334454334433343,0x434325443444433,0x423422223122020,0x333453423313142,0x434334353443533,0x443442243122022,0x533453443303342,0x434334353443533,0x433303233221121,0x434444434334333,0x434334443543443,0x433313233221121,0x434444434334333,0x434334443543443,0x433323233221121,0x434444434334333,0x434334443543443,0x325323203222210,0x144455324443244,0x434415543445443,0x434433233122121,0x443454433303243,0x434434453444543,0x434433233122121,0x443454433313243,0x434434453444543,0x434433233122121,0x443454433323043,0x434434453444543,0x434433233122121,0x443454433323143,0x434434453444543,0x434433233122121,0x443454433323243,0x434434453444543,0x424304223221220,0x344445424344234,0x434434543544453,0x425424223122220,0x353455423333044,0x434534553445553,0x35343433212212,0x144355343443433,0x441115445144114,0x334334443211222,0x444345443344403,0x441144445441144,0x335444443112222,0x453355440333333,0x441444455144444,0x440333343221122,0x504444444334433,0x444044444540444,0x344340333222112,0x414454344433443,0x444115444444414,0x441333343221122,0x514444444334433,0x444144444541444,0x335333303222211,0x144455334443344,0x444415544445444,0x444443343122122],
  #[0x543454443303343,0x444444454444544,0x434304333221221,0x444445434344334,0x444444544544454,0x435434333122221,0x453455433333044,0x444544554445554,0x214433033202121,0x244254432434321,0x503205251352320,0x314423123212120,0x244354423434230,0x504105152451410,0x303432133212021,0x134353433424331,0x504205252452420,0x224443343202122,0x344254442434420,0x513115154351311,0x214433033202121,0x244254432434321,0x513215251352321,0x213432133202021,0x234253432424321,0x513215252352321,0x214423123202120,0x244254422434221,0x513215252352321,0x214433133202121,0x244254432434321,0x513215252352321,0x214433233202121,0x244254432434321,0x513215253352321,0x205434333202221,0x154255432444322,0x513315354353331,0x314423123212120,0x244354423434230,0x514115152451411,0x324433233212121,0x344354433434330,0x514115153451411,0x333442243212022,0x434353443424430,0x514115153451411,0x334443343212122,0x444354443434430,0x514115154451411,0x303432133212021,0x134353433424331,0x514215252452421,0x313422123212020,0x234353423424231,0x514215252452421,0x313432133212021,0x234353433424331,0x514215252452421,0x314423123212120,0x244354423434231,0x514215252452421,0x323432133212021,0x334353433424331],
  #[0x514215252452421,0x324433233212121,0x344354433434331,0x514215253452421,0x324433033212121,0x344354433434332,0x514315351453431,0x314423123212120,0x244354423434232,0x514315352453431,0x324433133212121,0x344354433434332,0x514315352453431,0x304433233212121,0x144354433434332,0x514315353453431,0x314433233212121,0x244354433434332,0x514315353453431,0x305424223212220,0x154355423444233,0x514415453454441,0x305434333212221,0x154355433444333,0x514415454454441,0x433432033222021,0x434453434424342,0x515315351553531,0x424423023222120,0x344454424434243,0x515415451554541,0x434433033222121,0x444454434434343,0x515415451554541,0x214433133202121,0x244254432434321,0x523225252352322,0x224423123202120,0x344254422434221,0x523225252352322,0x213432133202021,0x234253432424322,0x523325352353332,0x313432133212021,0x234353433424331,0x524225252452422,0x314423123212120,0x244354423434231,0x524225252452422,0x313422223212020,0x234353423424231,0x524225253452422,0x324433233212121,0x344354433434332,0x524325353453432,0x223442243202022,0x334253442424422,0x533335353353333,0x225424223202220,0x354255422444222,0x533335353353333,0x423422223222020,0x334453424424242,0x535335353553533],
  #[0x335444442212222,0x453244333444433,0x434444344454444,0x345343432222212,0x443344234443444,0x344444434445445,0x445444442122222,0x552344333333344,0x344553444445555,0x444443342222122,0x543343334434443,0x435444343554544,0x444334442221222,0x543334334344434,0x344453434544455,0x435434332222221,0x453344324444344,0x435544443555554,0x235343433212212,0x344355343443433,0x443335445344334,0x335444443112222,0x453355442333333,0x443444455344444,0x334443343212122,0x444354443434432,0x534335354453433,0x334334443211222,0x444345443344423,0x443344445443344,0x325434333212221,0x354355433444333,0x534435454454443,0x345343433122212,0x443455343332344,0x353444545335445,0x344342333222112,0x434454344433443,0x444335444444434,0x344233433221212,0x434445344343434,0x353344535434345,0x335333323222211,0x344455334443344,0x444435544445444,0x444443343122122,0x543454443323343,0x444444454444544,0x444334443121222,0x543445443233334,0x353453545434455,0x435434333122221,0x453455433333244,0x444544554445554,0x443333343221122,0x534444444334433,0x444344444543444,0x434433233222121,0x444454434434343,0x535435453554543,0x434324333221221,0x444445434344334,0x444444544544454,0x225444441202222],
  #[0x352133222444422,0x323333233353333,0x225444440202222,0x351022112444422,0x213332122353333,0x335444440212222,0x451122113444433,0x224442222454444,0x245242421222202,0x332233124442444,0x233333323335335,0x245242420222202,0x331122014442444,0x123332212335335,0x345343430222212,0x441122114443444,0x224442222445445,0x445444441022222,0x551233222222244,0x233552333335555,0x445444440022222,0x550122112222244,0x123551222335555,0x445444440122222,0x551122113333344,0x224552222445555,0x443442241222022,0x532232224424442,0x325333232553533,0x443442240222022,0x531121114424442,0x215332121553533,0x444443340222122,0x541122114434443,0x225442222554544,0x443224441220222,0x532223224244424,0x233352323533355,0x443224440220222,0x531112114244424,0x123351212533355,0x444334440221222,0x541122114344434,0x224452222544455,0x425424221222220,0x352233214444244,0x325533332555553,0x425424220222220,0x351122104444244,0x215532221555553,0x435434330222221,0x451122114444344,0x225542222555554,0x125242423202202,0x234255242442422,0x332225335233223,0x225444443002222,0x352255441222222,0x332333355233333,0x223442243202022,0x334253442424421,0x523225253352322,0x223224443200222,0x334235442244412],
  #[0x332233335332233,0x215424223202220,0x254255422444222,0x523325353353332,0x245242423022202,0x332455242221244,0x252333535225335,0x243241223222002,0x324453244422442,0x333225333333323,0x243122423220202,0x324435244242424,0x252233525323235,0x225222213222200,0x234455224442244,0x333325533335333,0x443442243022022,0x532453442212242,0x333333353333533,0x443224443020222,0x532435442122224,0x252352535323355,0x425424223022220,0x352455422222144,0x333533553335553,0x442222243220022,0x524433444224422,0x333233333532333,0x423422123222020,0x334453424424242,0x525325352553532,0x423214223220220,0x334435424244224,0x333333533533353]
]
noncomputable def binZData:Array ℕ:=(binZDataChunks.toList.flatMap Array.toList).toArray

noncomputable def binSpreadMask32:Nat:=(0xfffffffffffff00 <<< 120)
noncomputable def binSpreadMask16:Nat:=(0xffffffffffffff0 <<< 60) ||| (0xff <<< 120)
noncomputable def binSpreadMask8:Nat:=0xfffffff00000000 ||| (0xff000000000000f <<< 60) ||| (0xffffff <<< 120) ||| (0xfffff000 <<< 180)
noncomputable def binSpreadMask4:Nat:=0xf000000ffff0000 ||| (0xffff000000fff <<< 60) ||| (0xf000000ffff0000 <<< 120) ||| (0xf000000fff <<< 180)
noncomputable def binSpreadMask2:Nat:=0xff000ff000ff00 ||| (0xff000ff000ff00 <<< 60) ||| (0xff000ff000ff00 <<< 120) ||| (0xff000ff00 <<< 180)
noncomputable def binSpreadMask1:Nat:=0x3c0f03c0f03c0f0 ||| (0x3c0f03c0f03c0f0 <<< 60) ||| (0x3c0f03c0f03c0f0 <<< 120) ||| (0x3c0f03c0f0 <<< 180)

noncomputable def binZ (i:ℕ):ℕ :=
  let p:=binChunkGet binZDataChunks (3*i) 0 ||| (binChunkGet binZDataChunks (3*i+1) 0 <<< 60) ||| (binChunkGet binZDataChunks (3*i+2) 0 <<< 120)
  let h:=p &&& binSpreadMask32
  let p:=(p ^^^ h) ||| (h <<< 32)
  let h:=p &&& binSpreadMask16
  let p:=(p ^^^ h) ||| (h <<< 16)
  let h:=p &&& binSpreadMask8
  let p:=(p ^^^ h) ||| (h <<< 8)
  let h:=p &&& binSpreadMask4
  let p:=(p ^^^ h) ||| (h <<< 4)
  let h:=p &&& binSpreadMask2
  let p:=(p ^^^ h) ||| (h <<< 2)
  let h:=p &&& binSpreadMask1
  let p:=(p ^^^ h) ||| (h <<< 1)
  p ||| initG

set_option maxRecDepth 100000 in
noncomputable def binRowDataChunks:Array (Array (List ℕ)):=#[
  #[[4713,15,14,2,3,4,5,6],[2856,15,0,14,2,3,4,5,6],[1221,17,0,1,14,2,3,4,5,6],[1308,19,0,1,14,2,3,4,5,6],[2304,21,0,1,14,2,3,4,5,6],[1263,23,0,1,14,2,3,4,5,6],[2349,25,0,1,14,2,3,4,5,6],[1509,0,1,14,2,3,4,5,6,36],[1587,0,1,14,37,2,3,4,5,6],[669,0,1,14,2,3,4,5,6,38],[2604,0,1,14,39,2,3,4,5,6],[1506,0,1,14,2,3,4,5,6,40],[1533,0,1,14,41,2,3,4,5,6],[687,0,1,14,2,3,4,5,6,42],[2646,0,1,14,43,2,3,4,5,6],[624,0,1,14,2,3,4,44,5,6],[2673,0,1,14,2,45,3,4,5,6],[1569,0,1,14,2,3,4,5,6,46],[1617,0,1,14,2,47,3,4,5,6],[762,0,1,14,2,3,4,5,6,48],[2760,0,1,14,2,49,3,4,5,6],[609,0,1,14,2,3,4,5,50,6],[2631,0,1,14,2,3,51,4,5,6],[4026,0,1,14,2,3,4,5,6,52],[4050,0,1,14,2,3,53,4,5,6],[648,0,1,14,2,3,4,5,6,54],[2682,0,1,14,2,3,4,55,5,6],[3137,0,182,1,2,3,4,5,6],[3242,0,225,1,2,3,4,5,6],[4361,0,1,265,2,3,4,5,6],[3188,0,1,303,2,3,4,5,6],[4406,0,1,340,2,3,4,5,6],[232,0,1,14,2,3,221,4,5,6],[562,0,1,14,2,3,4,261,5,6],[223,0,1,14,2,3,4,5,299,6],[592,0,1,14,2,3,4,5,6,336],[232,0,1,14,2,178,3,4,5,6],[622,0,1,14,2,3,4,5,262,6],[247,0,1,14,2,3,4,5,300,6],[760,0,1,14,2,3,4,5,6,337],[562,0,1,14,2,179,3,4,5,6],[622,0,1,14,2,3,222,4,5,6],[577,0,1,14,2,3,4,5,301,6],[3790,0,1,14,2,3,4,5,6,338],[223,0,1,14,2,180,3,4,5,6],[247,0,1,14,2,3,223,4,5,6],[577,0,1,14,2,3,4,263,5,6],[646,0,1,14,2,3,4,5,6,339],[592,0,1,14,2,181,3,4,5,6],[760,0,1,14,2,3,224,4,5,6],[3790,0,1,14,2,3,4,264,5,6],[646,0,1,14,2,3,4,5,302,6],[2208,15,0,1,2,16,3,4,5,6],[4734,15,17,1,2,3,4,5,6],[2880,15,17,0,1,2,3,4,5,6],[2274,15,0,1,2,3,4,5,6,18],[2910,19,15,0,1,2,3,4,5,6],[2421,15,0,1,2,3,4,5,6,20],[5571,15,21,1,2,3,4,5,6],[4122,15,21,0,1,2,3,4,5,6],[2250,15,0,1,2,3,4,5,6,22],[2892,15,23,0,1,2,3,4,5,6],[2439,15,0,1,2,3,4,5,6,24],[5589,15,25,1,2,3,4,5,6]],
  #[[4140,15,25,0,1,2,3,4,5,6],[2886,15,0,2,3,4,5,6,26],[4281,15,0,27,1,2,3,4,5,6],[4761,15,0,29,2,3,4,5,6],[4317,15,0,29,1,2,3,4,5,6],[5571,15,0,31,2,3,4,5,6],[5127,15,0,31,1,2,3,4,5,6],[4746,15,0,33,2,3,4,5,6],[4302,15,0,33,1,2,3,4,5,6],[5589,15,0,35,2,3,4,5,6],[5148,15,0,35,1,2,3,4,5,6],[3132,15,0,1,2,3,4,5,6,36],[3255,15,0,1,37,2,3,4,5,6],[2238,15,0,1,2,3,4,5,6,38],[4383,15,0,1,39,2,3,4,5,6],[3129,15,0,1,2,3,4,5,6,40],[3210,15,0,1,41,2,3,4,5,6],[2244,15,0,1,2,3,4,5,6,42],[4422,15,0,1,43,2,3,4,5,6],[2220,15,0,1,2,3,4,44,5,6],[4431,15,0,1,2,45,3,4,5,6],[3225,15,0,1,2,3,4,5,6,46],[3267,15,0,1,2,47,3,4,5,6],[2268,15,0,1,2,3,4,5,6,48],[4455,15,0,1,2,49,3,4,5,6],[2211,15,0,1,2,3,4,5,50,6],[4395,15,0,1,2,3,51,4,5,6],[5160,15,0,1,2,3,4,5,6,52],[5181,15,0,1,2,3,53,4,5,6],[2235,15,0,1,2,3,4,5,6,54],[4434,15,0,1,2,3,4,55,5,6],[2714,0,1,2,183,3,4,5,6],[2243,15,0,1,2,183,3,4,5,6],[4736,85,0,1,2,3,4,5,6],[4439,85,15,0,1,2,3,4,5,6],[2807,0,1,2,3,226,4,5,6],[2279,15,0,1,2,3,226,4,5,6],[4763,88,0,1,2,3,4,5,6],[4463,88,15,0,1,2,3,4,5,6],[5528,0,1,2,3,4,5,6,266],[5165,15,0,1,2,3,4,5,6,266],[5573,91,0,1,2,3,4,5,6],[5195,91,15,0,1,2,3,4,5,6],[2747,0,1,2,3,4,5,304,6],[2255,15,0,1,2,3,4,5,304,6],[4748,94,0,1,2,3,4,5,6],[4442,94,15,0,1,2,3,4,5,6],[5576,0,1,2,3,4,5,6,341],[5204,15,0,1,2,3,4,5,6,341],[5591,97,0,1,2,3,4,5,6],[5219,97,15,0,1,2,3,4,5,6],[4147,511,0,1,2,3,4,5,6],[5152,0,637,1,2,3,4,5,6],[2713,0,1,2,3,4,5,6,658],[2242,0,1,2,3,56,4,5,6,658],[4084,0,1,562,2,3,4,5,6],[2806,0,1,2,3,679,4,5,6],[2278,0,1,2,3,56,679,4,5,6],[4096,0,1,2,577,3,4,5,6],[5167,0,1,2,3,4,700,5,6],[5056,0,1,2,3,56,4,700,5,6],[5191,0,1,2,3,592,4,5,6],[2746,0,1,2,3,4,5,721,6],[2254,0,1,2,3,56,4,5,721,6]],
  #[[4087,0,1,2,3,607,4,5,6],[5206,0,1,2,3,4,5,6,742],[5062,0,1,2,3,56,4,5,6,742],[5215,0,1,2,3,622,4,5,6],[5227,15,511,1,2,3,4,5,6],[5227,15,0,637,2,3,4,5,6],[2242,15,0,1,2,3,4,5,6,658],[2278,15,0,1,2,3,679,4,5,6],[5056,15,0,1,2,3,4,700,5,6],[2254,15,0,1,2,3,4,5,721,6],[5062,15,0,1,2,3,4,5,6,742],[2449,0,1,2,3,370,4,5,6],[838,15,0,1,2,3,4,5,6,175],[880,15,0,1,2,3,218,4,5,6],[2113,15,0,1,2,3,4,258,5,6],[856,15,0,1,2,3,4,5,296,6],[2134,15,0,1,2,3,4,5,6,333],[2713,0,436,1,2,3,4,5,6],[2242,15,0,436,1,2,3,4,5,6],[2704,15,78,1,2,3,4,5,6],[838,15,0,78,1,2,3,4,5,6],[1594,15,0,1,2,3,221,4,5,6],[2179,15,0,1,2,3,4,261,5,6],[1537,15,0,1,2,3,4,5,299,6],[2206,15,0,1,2,3,4,5,6,336],[2806,451,0,1,2,3,4,5,6],[2278,15,451,0,1,2,3,4,5,6],[880,15,0,79,1,2,3,4,5,6],[2785,15,0,131,2,3,4,5,6],[1594,15,0,1,2,178,3,4,5,6],[2218,15,0,1,2,3,4,5,262,6],[1636,15,0,1,2,3,4,5,300,6],[2266,15,0,1,2,3,4,5,6,337],[5167,466,0,1,2,3,4,5,6],[5056,15,466,0,1,2,3,4,5,6],[4108,15,80,1,2,3,4,5,6],[2113,15,0,80,1,2,3,4,5,6],[5122,15,0,132,2,3,4,5,6],[2179,15,0,1,2,179,3,4,5,6],[2218,15,0,1,2,3,222,4,5,6],[2188,15,0,1,2,3,4,5,301,6],[5053,15,0,1,2,3,4,5,6,338],[2746,481,0,1,2,3,4,5,6],[2254,15,481,0,1,2,3,4,5,6],[856,15,0,81,1,2,3,4,5,6],[2734,15,0,133,2,3,4,5,6],[1537,15,0,1,2,180,3,4,5,6],[1636,15,0,1,2,3,223,4,5,6],[2188,15,0,1,2,3,4,263,5,6],[2233,15,0,1,2,3,4,5,6,339],[5206,496,0,1,2,3,4,5,6],[5062,15,496,0,1,2,3,4,5,6],[4135,15,82,1,2,3,4,5,6],[2134,15,0,82,1,2,3,4,5,6],[5143,15,0,134,2,3,4,5,6],[2206,15,0,1,2,181,3,4,5,6],[2266,15,0,1,2,3,224,4,5,6],[5053,15,0,1,2,3,4,264,5,6],[2233,15,0,1,2,3,4,5,302,6],[4710,17,1,16,3,4,5,6],[2853,17,0,1,16,3,4,5,6],[1305,19,0,1,2,16,3,4,5,6],[2301,21,0,1,2,16,3,4,5,6],[1260,23,0,1,2,16,3,4,5,6]],
  #[[2346,25,0,1,2,16,3,4,5,6],[633,0,1,2,16,3,28,4,5,6],[2556,0,29,1,2,16,3,4,5,6],[3861,0,1,2,16,3,4,5,6,30],[3927,0,31,1,2,16,3,4,5,6],[612,0,1,2,16,3,4,5,32,6],[2517,0,33,1,2,16,3,4,5,6],[3864,0,1,2,16,3,4,5,6,34],[3969,0,35,1,2,16,3,4,5,6],[618,0,1,2,16,3,4,44,5,6],[2670,0,1,2,16,45,3,4,5,6],[1566,0,1,2,16,3,4,5,6,46],[1614,0,1,2,16,47,3,4,5,6],[756,0,1,2,16,3,4,5,6,48],[2757,0,1,2,16,49,3,4,5,6],[606,0,1,2,16,3,4,5,50,6],[2628,0,1,2,16,3,51,4,5,6],[4023,0,1,2,16,3,4,5,6,52],[4047,0,1,2,16,3,53,4,5,6],[642,0,1,2,16,3,4,5,6,54],[2679,0,1,2,16,3,4,55,5,6],[4244,0,135,1,2,3,4,5,6],[3239,0,1,227,2,3,4,5,6],[4358,0,1,267,2,3,4,5,6],[3185,0,1,305,2,3,4,5,6],[4403,0,1,342,2,3,4,5,6],[532,0,1,2,16,3,220,4,5,6],[3751,0,1,2,16,3,4,260,5,6],[517,0,1,2,16,3,4,5,298,6],[3763,0,1,2,16,3,4,5,6,335],[532,0,1,131,2,16,3,4,5,6],[616,0,1,2,16,3,4,5,262,6],[244,0,1,2,16,3,4,5,300,6],[754,0,1,2,16,3,4,5,6,337],[3751,0,1,132,2,16,3,4,5,6],[616,0,1,2,16,3,222,4,5,6],[574,0,1,2,16,3,4,5,301,6],[3787,0,1,2,16,3,4,5,6,338],[517,0,1,133,2,16,3,4,5,6],[244,0,1,2,16,3,223,4,5,6],[574,0,1,2,16,3,4,263,5,6],[640,0,1,2,16,3,4,5,6,339],[3763,0,1,134,2,16,3,4,5,6],[754,0,1,2,16,3,224,4,5,6],[3787,0,1,2,16,3,4,264,5,6],[640,0,1,2,16,3,4,5,302,6],[1365,17,0,1,2,3,4,5,6,18],[3723,19,17,1,2,3,4,5,6],[1764,19,17,0,1,2,3,4,5,6],[1425,17,0,1,2,3,4,5,6,20],[2976,21,17,0,1,2,3,4,5,6],[1296,17,0,1,2,3,4,5,6,22],[3717,23,17,1,2,3,4,5,6],[1752,23,17,0,1,2,3,4,5,6],[1443,17,0,1,2,3,4,5,6,24],[3000,25,17,0,1,2,3,4,5,6],[2886,17,0,1,3,4,5,6,26],[3162,17,0,27,1,2,3,4,5,6],[1239,17,0,1,2,3,28,4,5,6],[3255,17,0,29,1,2,3,4,5,6],[4275,17,0,1,2,3,4,5,6,30],[4383,17,0,31,1,2,3,4,5,6],[1227,17,0,1,2,3,4,5,32,6],[3210,17,0,33,1,2,3,4,5,6]],
  #[[4278,17,0,1,2,3,4,5,6,34],[4422,17,0,35,1,2,3,4,5,6],[3723,17,0,1,37,3,4,5,6],[1902,17,0,1,37,2,3,4,5,6],[4785,17,0,1,39,3,4,5,6],[3312,17,0,1,39,2,3,4,5,6],[3717,17,0,1,41,3,4,5,6],[1872,17,0,1,41,2,3,4,5,6],[4797,17,0,1,43,3,4,5,6],[3330,17,0,1,43,2,3,4,5,6],[1236,17,0,1,2,3,4,44,5,6],[3333,17,0,1,2,45,3,4,5,6],[1875,17,0,1,2,3,4,5,6,46],[1905,17,0,1,2,47,3,4,5,6],[1350,17,0,1,2,3,4,5,6,48],[3354,17,0,1,2,49,3,4,5,6],[1224,17,0,1,2,3,4,5,50,6],[3315,17,0,1,2,3,51,4,5,6],[4473,17,0,1,2,3,4,5,6,52],[4485,17,0,1,2,3,53,4,5,6],[1248,17,0,1,2,3,4,5,6,54],[3336,17,0,1,2,3,4,55,5,6],[2717,0,1,136,2,3,4,5,6],[1259,17,0,1,136,2,3,4,5,6],[3341,85,17,0,1,2,3,4,5,6],[3695,0,1,2,3,4,5,6,228],[1922,17,0,1,2,3,4,5,6,228],[3725,100,0,1,2,3,4,5,6],[1973,100,17,0,1,2,3,4,5,6],[2951,0,1,2,3,4,5,6,268],[1430,17,0,1,2,3,4,5,6,268],[4787,103,0,1,2,3,4,5,6],[3380,103,17,0,1,2,3,4,5,6],[3614,0,1,2,3,4,5,6,306],[1880,17,0,1,2,3,4,5,6,306],[3719,106,0,1,2,3,4,5,6],[1958,106,17,0,1,2,3,4,5,6],[2993,0,1,2,3,4,5,6,343],[1448,17,0,1,2,3,4,5,6,343],[4799,109,0,1,2,3,4,5,6],[3392,109,17,0,1,2,3,4,5,6],[1786,512,0,1,2,3,4,5,6],[2716,0,1,2,3,638,4,5,6],[1258,0,1,2,57,3,638,4,5,6],[1747,0,547,1,2,3,4,5,6],[1945,0,1,659,2,3,4,5,6],[1924,0,1,2,3,680,4,5,6],[346,0,1,2,57,3,680,4,5,6],[1969,0,1,2,578,3,4,5,6],[2950,0,1,2,3,4,701,5,6],[1429,0,1,2,57,3,4,701,5,6],[1771,0,1,2,593,3,4,5,6],[1882,0,1,2,3,4,5,722,6],[337,0,1,2,57,3,4,5,722,6],[1954,0,1,2,608,3,4,5,6],[2992,0,1,2,3,4,5,6,743],[1447,0,1,2,57,3,4,5,6,743],[1777,0,1,2,623,3,4,5,6],[1990,512,17,1,2,3,4,5,6],[1258,17,0,1,2,3,638,4,5,6],[1990,17,0,1,659,3,4,5,6],[346,17,0,1,2,3,680,4,5,6],[1429,17,0,1,2,3,4,701,5,6],[337,17,0,1,2,3,4,5,722,6]],
  #[[1447,17,0,1,2,3,4,5,6,743],[1456,0,1,2,3,4,5,6,371],[841,17,0,1,2,3,128,4,5,6],[184,17,0,1,2,3,218,4,5,6],[1072,17,0,1,2,3,4,258,5,6],[157,17,0,1,2,3,4,5,296,6],[1108,17,0,1,2,3,4,5,6,333],[2716,0,1,421,2,3,4,5,6],[1258,17,0,1,421,2,3,4,5,6],[2707,17,1,77,2,3,4,5,6],[841,17,0,1,77,2,3,4,5,6],[1186,17,0,1,2,3,220,4,5,6],[3952,17,0,1,2,3,4,260,5,6],[1168,17,0,1,2,3,4,5,298,6],[3988,17,0,1,2,3,4,5,6,335],[1924,452,0,1,2,3,4,5,6],[346,17,452,0,1,2,3,4,5,6],[1705,17,79,1,2,3,4,5,6],[184,17,0,79,1,2,3,4,5,6],[1186,17,0,1,131,2,3,4,5,6],[1897,17,0,1,178,3,4,5,6],[1234,17,0,1,2,3,4,5,262,6],[331,17,0,1,2,3,4,5,300,6],[1348,17,0,1,2,3,4,5,6,337],[2950,467,0,1,2,3,4,5,6],[1429,17,467,0,1,2,3,4,5,6],[1072,17,0,80,1,2,3,4,5,6],[3952,17,0,1,132,2,3,4,5,6],[2824,17,0,1,179,3,4,5,6],[1234,17,0,1,2,3,222,4,5,6],[1213,17,0,1,2,3,4,5,301,6],[4105,17,0,1,2,3,4,5,6,338],[1882,482,0,1,2,3,4,5,6],[337,17,482,0,1,2,3,4,5,6],[1687,17,81,1,2,3,4,5,6],[157,17,0,81,1,2,3,4,5,6],[1168,17,0,1,133,2,3,4,5,6],[1867,17,0,1,180,3,4,5,6],[331,17,0,1,2,3,223,4,5,6],[1213,17,0,1,2,3,4,263,5,6],[1246,17,0,1,2,3,4,5,6,339],[2992,497,0,1,2,3,4,5,6],[1447,17,497,0,1,2,3,4,5,6],[1108,17,0,82,1,2,3,4,5,6],[3988,17,0,1,134,2,3,4,5,6],[2848,17,0,1,181,3,4,5,6],[1348,17,0,1,2,3,224,4,5,6],[4105,17,0,1,2,3,4,264,5,6],[1246,17,0,1,2,3,4,5,302,6],[4767,19,1,2,4,5,6,18],[2928,19,0,1,2,4,5,6,18],[2406,21,0,1,2,3,4,5,6,18],[1368,23,0,1,2,3,4,5,6,18],[2412,25,0,1,2,3,4,5,6,18],[813,0,1,2,3,4,5,6,18,26],[2595,0,27,1,2,3,4,5,6,18],[3900,0,1,2,3,4,5,6,18,30],[4014,0,31,1,2,3,4,5,6,18],[795,0,1,2,3,4,5,32,6,18],[2598,0,33,1,2,3,4,5,6,18],[3903,0,1,2,3,4,5,6,18,34],[4020,0,35,1,2,3,4,5,6,18],[810,0,1,2,3,4,5,6,38,18],[2790,0,1,39,2,3,4,5,6,18]],
  #[[1653,0,1,2,3,4,5,6,18,40],[1656,0,1,41,2,3,4,5,6,18],[816,0,1,2,3,4,5,6,42,18],[2799,0,1,43,2,3,4,5,6,18],[792,0,1,2,3,4,5,50,6,18],[2793,0,1,2,3,51,4,5,6,18],[4080,0,1,2,3,4,5,6,18,52],[4092,0,1,2,3,53,4,5,6,18],[801,0,1,2,3,4,5,6,54,18],[2808,0,1,2,3,4,55,5,6,18],[4769,0,137,2,3,4,5,6],[4331,0,137,1,2,3,4,5,6],[4769,0,1,184,3,4,5,6],[3299,0,1,184,2,3,4,5,6],[4769,0,1,2,3,269,5,6],[4460,0,1,2,3,269,4,5,6],[4769,0,1,2,3,4,307,6],[3302,0,1,2,3,4,307,5,6],[4769,0,1,2,3,4,5,344],[4466,0,1,2,3,4,5,344,6],[556,0,1,2,177,3,4,5,6,18],[3781,0,1,2,3,4,260,5,6,18],[559,0,1,2,3,4,5,298,6,18],[3784,0,1,2,3,4,5,6,335,18],[556,0,1,130,2,3,4,5,6,18],[748,0,1,2,3,4,261,5,6,18],[265,0,1,2,3,4,5,299,6,18],[790,0,1,2,3,4,5,6,336,18],[3781,0,1,132,2,3,4,5,6,18],[748,0,1,2,179,3,4,5,6,18],[751,0,1,2,3,4,5,301,6,18],[3823,0,1,2,3,4,5,6,338,18],[559,0,1,133,2,3,4,5,6,18],[265,0,1,2,180,3,4,5,6,18],[751,0,1,2,3,4,263,5,6,18],[799,0,1,2,3,4,5,6,339,18],[3784,0,1,134,2,3,4,5,6,18],[790,0,1,2,181,3,4,5,6,18],[3823,0,1,2,3,4,264,5,6,18],[799,0,1,2,3,4,5,302,6,18],[1437,19,0,1,2,3,4,5,6,20],[3009,19,21,0,1,2,3,4,5,6],[1344,19,0,1,2,3,4,5,6,22],[3726,19,23,1,2,3,4,5,6],[1767,19,23,0,1,2,3,4,5,6],[1461,19,0,1,2,3,4,5,6,24],[4824,19,25,1,2,3,4,5,6],[3033,19,25,0,1,2,3,4,5,6],[1332,19,0,1,2,3,4,5,6,26],[3255,19,0,27,1,2,3,4,5,6],[3294,19,0,29,1,2,3,4,5,6],[4311,19,0,1,2,3,4,5,6,30],[4431,19,0,31,1,2,3,4,5,6],[1314,19,0,1,2,3,4,5,32,6],[3267,19,0,33,1,2,3,4,5,6],[4314,19,0,1,2,3,4,5,6,34],[4455,19,0,35,1,2,3,4,5,6],[1926,19,0,1,37,2,3,4,5,6],[1329,19,0,1,2,3,4,5,6,38],[3333,19,0,1,39,2,3,4,5,6],[1890,19,0,1,2,3,4,5,6,40],[1905,19,0,1,41,2,3,4,5,6],[1335,19,0,1,2,3,4,5,6,42],[3354,19,0,1,43,2,3,4,5,6]],
  #[[4806,19,0,1,2,45,4,5,6],[3357,19,0,1,2,45,3,4,5,6],[3726,19,0,1,2,47,4,5,6],[1938,19,0,1,2,47,3,4,5,6],[4824,19,0,1,2,49,4,5,6],[3366,19,0,1,2,49,3,4,5,6],[1311,19,0,1,2,3,4,5,50,6],[3345,19,0,1,2,3,51,4,5,6],[4488,19,0,1,2,3,4,5,6,52],[4512,19,0,1,2,3,53,4,5,6],[1323,19,0,1,2,3,4,5,6,54],[3363,19,0,1,2,3,4,55,5,6],[2789,0,1,138,2,3,4,5,6],[1319,19,0,1,138,2,3,4,5,6],[3362,88,19,0,1,2,3,4,5,6],[3650,0,1,2,185,3,4,5,6],[1895,19,0,1,2,185,3,4,5,6],[1967,100,19,0,1,2,3,4,5,6],[2975,0,1,2,3,4,270,5,6],[1442,19,0,1,2,3,4,270,5,6],[4808,112,0,1,2,3,4,5,6],[3395,112,19,0,1,2,3,4,5,6],[3680,0,1,2,3,4,5,6,308],[1913,19,0,1,2,3,4,5,6,308],[3728,115,0,1,2,3,4,5,6],[1985,115,19,0,1,2,3,4,5,6],[3026,0,1,2,3,4,5,6,345],[1466,19,0,1,2,3,4,5,6,345],[4826,118,0,1,2,3,4,5,6],[3404,118,19,0,1,2,3,4,5,6],[1795,513,0,1,2,3,4,5,6],[2788,0,1,2,3,4,639,5,6],[1318,0,1,2,3,4,58,639,5,6],[1762,0,548,1,2,3,4,5,6],[1900,0,1,2,3,4,5,6,660],[340,0,1,2,3,4,58,5,6,660],[1963,0,1,563,2,3,4,5,6],[1987,0,1,2,681,3,4,5,6],[2974,0,1,2,3,4,5,702,6],[1441,0,1,2,3,4,58,5,702,6],[1780,0,1,2,3,594,4,5,6],[1915,0,1,2,3,4,5,723,6],[343,0,1,2,3,4,58,5,723,6],[1981,0,1,2,3,4,609,5,6],[3025,0,1,2,3,4,5,6,744],[1465,0,1,2,3,4,58,5,6,744],[1792,0,1,2,3,4,624,5,6],[1996,19,513,1,2,3,4,5,6],[1318,19,0,1,2,3,4,639,5,6],[340,19,0,1,2,3,4,5,6,660],[1996,19,0,1,2,681,4,5,6],[1441,19,0,1,2,3,4,5,702,6],[343,19,0,1,2,3,4,5,723,6],[1465,19,0,1,2,3,4,5,6,744],[1468,0,1,2,3,372,4,5,6],[868,19,0,1,2,3,128,4,5,6],[163,19,0,1,2,3,4,5,6,175],[1093,19,0,1,2,3,4,258,5,6],[181,19,0,1,2,3,4,5,296,6],[1144,19,0,1,2,3,4,5,6,333],[2788,0,1,422,2,3,4,5,6],[1318,19,0,1,422,2,3,4,5,6],[868,19,0,1,77,2,3,4,5,6],[1189,19,0,1,2,177,3,4,5,6]],
  #[[3997,19,0,1,2,3,4,260,5,6],[1195,19,0,1,2,3,4,5,298,6],[4012,19,0,1,2,3,4,5,6,335],[1900,0,437,1,2,3,4,5,6],[340,19,0,437,1,2,3,4,5,6],[1696,19,78,1,2,3,4,5,6],[163,19,0,78,1,2,3,4,5,6],[1189,19,0,1,130,2,3,4,5,6],[1252,19,0,1,2,3,4,261,5,6],[325,19,0,1,2,3,4,5,299,6],[1303,19,0,1,2,3,4,5,6,336],[2974,468,0,1,2,3,4,5,6],[1441,19,468,0,1,2,3,4,5,6],[1093,19,0,80,1,2,3,4,5,6],[3997,19,0,1,132,2,3,4,5,6],[1252,19,0,1,2,179,3,4,5,6],[2866,19,0,1,2,222,4,5,6],[1270,19,0,1,2,3,4,5,301,6],[4120,19,0,1,2,3,4,5,6,338],[1915,483,0,1,2,3,4,5,6],[343,19,483,0,1,2,3,4,5,6],[1702,19,81,1,2,3,4,5,6],[181,19,0,81,1,2,3,4,5,6],[1195,19,0,1,133,2,3,4,5,6],[325,19,0,1,2,180,3,4,5,6],[1909,19,0,1,2,223,4,5,6],[1270,19,0,1,2,3,4,263,5,6],[1321,19,0,1,2,3,4,5,6,339],[3025,498,0,1,2,3,4,5,6],[1465,19,498,0,1,2,3,4,5,6],[3022,19,82,1,2,3,4,5,6],[1144,19,0,82,1,2,3,4,5,6],[4012,19,0,1,134,2,3,4,5,6],[1303,19,0,1,2,181,3,4,5,6],[2917,19,0,1,2,224,4,5,6],[4120,19,0,1,2,3,4,264,5,6],[1321,19,0,1,2,3,4,5,302,6],[4827,21,1,2,3,5,6,20],[3036,21,0,1,2,3,5,6,20],[1431,23,0,1,2,3,4,5,6,20],[2451,25,0,1,2,3,4,5,6,20],[900,0,1,2,3,4,5,6,20,26],[2811,0,27,1,2,3,4,5,6,20],[891,0,1,2,3,28,4,5,6,20],[2817,0,29,1,2,3,4,5,6,20],[888,0,1,2,3,4,5,32,6,20],[2814,0,33,1,2,3,4,5,6,20],[4029,0,1,2,3,4,5,6,20,34],[4101,0,35,1,2,3,4,5,6,20],[1719,0,1,2,3,4,5,6,20,36],[1728,0,1,37,2,3,4,5,6,20],[1716,0,1,2,3,4,5,6,20,40],[1722,0,1,41,2,3,4,5,6,20],[903,0,1,2,3,4,5,6,42,20],[2940,0,1,43,2,3,4,5,6,20],[1725,0,1,2,3,4,5,6,20,46],[1731,0,1,2,47,3,4,5,6,20],[954,0,1,2,3,4,5,6,20,48],[2967,0,1,2,49,3,4,5,6,20],[897,0,1,2,3,4,5,6,54,20],[2943,0,1,2,3,4,55,5,6,20],[4829,0,139,2,3,4,5,6],[4472,0,139,1,2,3,4,5,6],[4829,0,1,186,3,4,5,6]],
  #[[3371,0,1,186,2,3,4,5,6],[4829,0,1,2,229,4,5,6],[3377,0,1,2,229,3,4,5,6],[4829,0,1,2,3,4,309,6],[3374,0,1,2,3,4,309,5,6],[4829,0,1,2,3,4,5,346],[4535,0,1,2,3,4,5,346,6],[823,0,1,2,177,3,4,5,6,20],[829,0,1,2,3,220,4,5,6,20],[826,0,1,2,3,4,5,298,6,20],[3793,0,1,2,3,4,5,6,335,20],[823,0,1,130,2,3,4,5,6,20],[298,0,1,2,3,221,4,5,6,20],[295,0,1,2,3,4,5,299,6,20],[886,0,1,2,3,4,5,6,336,20],[829,0,1,131,2,3,4,5,6,20],[298,0,1,2,178,3,4,5,6,20],[301,0,1,2,3,4,5,300,6,20],[952,0,1,2,3,4,5,6,337,20],[826,0,1,133,2,3,4,5,6,20],[295,0,1,2,180,3,4,5,6,20],[301,0,1,2,3,223,4,5,6,20],[895,0,1,2,3,4,5,6,339,20],[3793,0,1,134,2,3,4,5,6,20],[886,0,1,2,181,3,4,5,6,20],[952,0,1,2,3,224,4,5,6,20],[895,0,1,2,3,4,5,302,6,20],[2337,21,0,1,2,3,4,5,6,22],[2979,21,23,0,1,2,3,4,5,6],[2457,21,0,1,2,3,4,5,6,24],[5601,21,25,1,2,3,4,5,6],[4170,21,25,0,1,2,3,4,5,6],[2328,21,0,1,2,3,4,5,6,26],[4383,21,0,27,1,2,3,4,5,6],[2313,21,0,1,2,3,28,4,5,6],[4431,21,0,29,1,2,3,4,5,6],[5169,21,0,31,1,2,3,4,5,6],[2307,21,0,1,2,3,4,5,32,6],[4395,21,0,33,1,2,3,4,5,6],[5118,21,0,1,2,3,4,5,6,34],[5181,21,0,35,1,2,3,4,5,6],[3309,21,0,1,2,3,4,5,6,36],[3333,21,0,1,37,2,3,4,5,6],[4476,21,0,1,39,2,3,4,5,6],[3306,21,0,1,2,3,4,5,6,40],[3315,21,0,1,41,2,3,4,5,6],[2331,21,0,1,2,3,4,5,6,42],[4485,21,0,1,43,2,3,4,5,6],[4806,21,0,1,2,45,3,5,6],[4491,21,0,1,2,45,3,4,5,6],[3318,21,0,1,2,3,4,5,6,46],[3345,21,0,1,2,47,3,4,5,6],[2400,21,0,1,2,3,4,5,6,48],[4512,21,0,1,2,49,3,4,5,6],[4788,21,0,1,2,3,51,5,6],[4482,21,0,1,2,3,51,4,5,6],[5601,21,0,1,2,3,53,5,6],[5238,21,0,1,2,3,53,4,5,6],[2322,21,0,1,2,3,4,5,6,54],[4494,21,0,1,2,3,4,55,5,6],[5456,0,1,140,2,3,4,5,6],[5117,21,0,1,140,2,3,4,5,6],[5189,91,21,0,1,2,3,4,5,6],[2828,0,1,2,187,3,4,5,6]],
  #[[2327,21,0,1,2,187,3,4,5,6],[4499,103,21,0,1,2,3,4,5,6],[2915,0,1,2,3,4,230,5,6],[2411,21,0,1,2,3,4,230,5,6],[4523,112,21,0,1,2,3,4,5,6],[2837,0,1,2,3,4,5,310,6],[2342,21,0,1,2,3,4,5,310,6],[4790,121,0,1,2,3,4,5,6],[4502,121,21,0,1,2,3,4,5,6],[5600,0,1,2,3,4,5,6,347],[5249,21,0,1,2,3,4,5,6,347],[5603,124,0,1,2,3,4,5,6],[5264,124,21,0,1,2,3,4,5,6],[4174,514,0,1,2,3,4,5,6],[3850,514,0,1,2,3,59,4,5,6],[5125,0,1,2,3,640,4,5,6],[5047,0,1,2,3,59,640,4,5,6],[5185,0,549,1,2,3,4,5,6],[5059,0,549,1,2,3,59,4,5,6],[2827,0,1,2,3,4,5,6,661],[2326,0,1,2,3,59,4,5,6,661],[4126,0,1,564,2,3,4,5,6],[3835,0,1,564,2,3,59,4,5,6],[2914,0,1,2,3,682,4,5,6],[2410,0,1,2,3,59,682,4,5,6],[4150,0,1,2,579,3,4,5,6],[3844,0,1,2,579,3,59,4,5,6],[5242,0,1,2,703,3,4,5,6],[5068,0,1,2,703,3,59,4,5,6],[2836,0,1,2,3,4,5,724,6],[2341,0,1,2,3,59,4,5,724,6],[4129,0,1,2,3,610,4,5,6],[3838,0,1,2,3,610,59,4,5,6],[5251,0,1,2,3,4,5,6,745],[5071,0,1,2,3,59,4,5,6,745],[5260,0,1,2,3,625,4,5,6],[5074,0,1,2,3,625,59,4,5,6],[5272,514,21,1,2,3,4,5,6],[5077,514,21,1,2,3,59,4,5,6],[3850,514,21,0,1,2,3,4,5,6],[5047,21,0,1,2,3,640,4,5,6],[5059,21,0,549,1,2,3,4,5,6],[2326,21,0,1,2,3,4,5,6,661],[2086,21,0,1,2,3,59,4,5,6,661],[3835,21,0,1,564,2,3,4,5,6],[2410,21,0,1,2,3,682,4,5,6],[2110,21,0,1,2,3,59,682,4,5,6],[3844,21,0,1,2,579,3,4,5,6],[5272,21,0,1,2,703,3,5,6],[5077,21,0,1,2,703,3,59,5,6],[5068,21,0,1,2,703,3,4,5,6],[2341,21,0,1,2,3,4,5,724,6],[2092,21,0,1,2,3,59,4,5,724,6],[3838,21,0,1,2,3,610,4,5,6],[5071,21,0,1,2,3,4,5,6,745],[5074,21,0,1,2,3,625,4,5,6],[2464,0,1,2,3,4,373,5,6],[2152,21,0,1,2,3,4,373,5,6],[2083,21,0,1,2,3,128,4,5,6],[913,21,0,1,2,3,4,5,6,175],[1048,21,0,1,2,3,218,4,5,6],[934,21,0,1,2,3,4,5,296,6],[2146,21,0,1,2,3,4,5,6,333],[5125,0,1,423,2,3,4,5,6]],
  #[[5047,21,0,1,423,2,3,4,5,6],[4069,21,1,77,2,3,4,5,6],[2083,21,0,1,77,2,3,4,5,6],[2182,21,0,1,2,177,3,4,5,6],[2224,21,0,1,2,3,220,4,5,6],[2191,21,0,1,2,3,4,5,298,6],[5044,21,0,1,2,3,4,5,6,335],[2827,0,438,1,2,3,4,5,6],[2326,21,0,438,1,2,3,4,5,6],[913,21,0,78,1,2,3,4,5,6],[2182,21,0,1,130,2,3,4,5,6],[1675,21,0,1,2,3,221,4,5,6],[1672,21,0,1,2,3,4,5,299,6],[2299,21,0,1,2,3,4,5,6,336],[2914,453,0,1,2,3,4,5,6],[2410,21,453,0,1,2,3,4,5,6],[1048,21,0,79,1,2,3,4,5,6],[2224,21,0,1,131,2,3,4,5,6],[1675,21,0,1,2,178,3,4,5,6],[2866,21,0,1,2,3,5,262,6],[1684,21,0,1,2,3,4,5,300,6],[2398,21,0,1,2,3,4,5,6,337],[2836,484,0,1,2,3,4,5,6],[2341,21,484,0,1,2,3,4,5,6],[934,21,0,81,1,2,3,4,5,6],[2191,21,0,1,133,2,3,4,5,6],[1672,21,0,1,2,180,3,4,5,6],[1684,21,0,1,2,3,223,4,5,6],[2830,21,0,1,2,3,263,5,6],[2320,21,0,1,2,3,4,5,6,339],[5251,499,0,1,2,3,4,5,6],[5071,21,499,0,1,2,3,4,5,6],[4165,21,82,1,2,3,4,5,6],[2146,21,0,82,1,2,3,4,5,6],[5044,21,0,1,134,2,3,4,5,6],[2299,21,0,1,2,181,3,4,5,6],[2398,21,0,1,2,3,224,4,5,6],[5230,21,0,1,2,3,264,5,6],[2320,21,0,1,2,3,4,5,302,6],[4749,23,1,2,3,4,6,22],[2901,23,0,1,2,3,4,6,22],[2388,25,0,1,2,3,4,5,6,22],[732,0,1,2,3,4,5,6,22,26],[2541,0,27,1,2,3,4,5,6,22],[726,0,1,2,3,28,4,5,6,22],[2580,0,29,1,2,3,4,5,6,22],[3888,0,1,2,3,4,5,6,22,30],[3963,0,31,1,2,3,4,5,6,22],[3891,0,1,2,3,4,5,6,22,34],[4002,0,35,1,2,3,4,5,6,22],[1572,0,1,2,3,4,5,6,22,36],[1638,0,1,37,2,3,4,5,6,22],[729,0,1,2,3,4,5,6,38,22],[2643,0,1,39,2,3,4,5,6,22],[735,0,1,2,3,4,5,6,42,22],[2739,0,1,43,2,3,4,5,6,22],[723,0,1,2,3,4,44,5,6,22],[2748,0,1,2,45,3,4,5,6,22],[807,0,1,2,3,4,5,6,22,48],[2796,0,1,2,49,3,4,5,6,22],[4041,0,1,2,3,4,5,6,22,52],[4071,0,1,2,3,53,4,5,6,22],[4751,0,141,2,3,4,5,6],[4307,0,141,1,2,3,4,5,6]],
  #[[4751,0,1,188,3,4,5,6],[3233,0,1,188,2,3,4,5,6],[4751,0,1,2,231,4,5,6],[3272,0,1,2,231,3,4,5,6],[4751,0,1,2,3,271,5,6],[4400,0,1,2,3,271,4,5,6],[4751,0,1,2,3,4,5,348],[4445,0,1,2,3,4,5,348,6],[529,0,1,2,177,3,4,5,6,22],[547,0,1,2,3,220,4,5,6,22],[3760,0,1,2,3,4,260,5,6,22],[3775,0,1,2,3,4,5,6,335,22],[529,0,1,130,2,3,4,5,6,22],[250,0,1,2,3,221,4,5,6,22],[589,0,1,2,3,4,261,5,6,22],[718,0,1,2,3,4,5,6,336,22],[547,0,1,131,2,3,4,5,6,22],[250,0,1,2,178,3,4,5,6,22],[721,0,1,2,3,4,5,262,6,22],[805,0,1,2,3,4,5,6,337,22],[3760,0,1,132,2,3,4,5,6,22],[589,0,1,2,179,3,4,5,6,22],[721,0,1,2,3,222,4,5,6,22],[3811,0,1,2,3,4,5,6,338,22],[3775,0,1,134,2,3,4,5,6,22],[718,0,1,2,181,3,4,5,6,22],[805,0,1,2,3,224,4,5,6,22],[3811,0,1,2,3,4,264,5,6,22],[1449,23,0,1,2,3,4,5,6,24],[3018,23,25,0,1,2,3,4,5,6],[1287,23,0,1,2,3,4,5,6,26],[3210,23,0,27,1,2,3,4,5,6],[1278,23,0,1,2,3,28,4,5,6],[3267,23,0,29,1,2,3,4,5,6],[4296,23,0,1,2,3,4,5,6,30],[4395,23,0,31,1,2,3,4,5,6],[3228,23,0,33,1,2,3,4,5,6],[4299,23,0,1,2,3,4,5,6,34],[4434,23,0,35,1,2,3,4,5,6],[1860,23,0,1,2,3,4,5,6,36],[1905,23,0,1,37,2,3,4,5,6],[1284,23,0,1,2,3,4,5,6,38],[3315,23,0,1,39,2,3,4,5,6],[1884,23,0,1,41,2,3,4,5,6],[1290,23,0,1,2,3,4,5,6,42],[3336,23,0,1,43,2,3,4,5,6],[1275,23,0,1,2,3,4,44,5,6],[3345,23,0,1,2,45,3,4,5,6],[3726,23,0,1,2,47,3,4,6],[1917,23,0,1,2,47,3,4,5,6],[1356,23,0,1,2,3,4,5,6,48],[3363,23,0,1,2,49,3,4,5,6],[4788,23,0,1,2,3,51,4,6],[3321,23,0,1,2,3,51,4,5,6],[4479,23,0,1,2,3,4,5,6,52],[4494,23,0,1,2,3,53,4,5,6],[4815,23,0,1,2,3,4,55,6],[3351,23,0,1,2,3,4,55,5,6],[2738,0,1,142,2,3,4,5,6],[1268,23,0,1,142,2,3,4,5,6],[3344,94,23,0,1,2,3,4,5,6],[3599,0,1,2,189,3,4,5,6],[1865,23,0,1,2,189,3,4,5,6],[1952,106,23,0,1,2,3,4,5,6]],
  #[[3710,0,1,2,3,4,5,6,232],[1934,23,0,1,2,3,4,5,6,232],[1979,115,23,0,1,2,3,4,5,6],[2957,0,1,2,3,4,5,272,6],[1436,23,0,1,2,3,4,5,272,6],[3383,121,23,0,1,2,3,4,5,6],[2999,0,1,2,3,4,5,6,349],[1454,23,0,1,2,3,4,5,6,349],[4817,127,0,1,2,3,4,5,6],[3398,127,23,0,1,2,3,4,5,6],[1789,515,0,1,2,3,4,5,6],[322,515,0,1,2,60,3,4,5,6],[2737,0,1,2,3,641,4,5,6],[1267,0,1,2,60,3,641,4,5,6],[1750,0,550,1,2,3,4,5,6],[313,0,550,1,2,60,3,4,5,6],[1870,0,1,2,3,4,5,6,662],[334,0,1,2,60,3,4,5,6,662],[1948,0,1,565,2,3,4,5,6],[352,0,1,565,2,60,3,4,5,6],[1936,0,1,2,3,683,4,5,6],[349,0,1,2,60,3,683,4,5,6],[1975,0,1,2,580,3,4,5,6],[358,0,1,2,580,60,3,4,5,6],[2956,0,1,2,3,4,704,5,6],[1435,0,1,2,60,3,4,704,5,6],[1774,0,1,2,595,3,4,5,6],[316,0,1,2,595,60,3,4,5,6],[1960,0,1,2,725,3,4,5,6],[355,0,1,2,725,60,3,4,5,6],[2998,0,1,2,3,4,5,6,746],[1453,0,1,2,60,3,4,5,6,746],[1783,0,1,2,626,3,4,5,6],[319,0,1,2,626,60,3,4,5,6],[1993,515,23,1,2,3,4,5,6],[361,515,23,1,2,60,3,4,5,6],[322,515,23,0,1,2,3,4,5,6],[1267,23,0,1,2,3,641,4,5,6],[148,23,0,1,2,60,3,641,4,5,6],[313,23,0,550,1,2,3,4,5,6],[334,23,0,1,2,3,4,5,6,662],[352,23,0,1,565,2,3,4,5,6],[349,23,0,1,2,3,683,4,5,6],[358,23,0,1,2,580,3,4,5,6],[1435,23,0,1,2,3,4,704,5,6],[214,23,0,1,2,60,3,4,704,5,6],[316,23,0,1,2,595,3,4,5,6],[1993,23,0,1,2,725,3,4,6],[361,23,0,1,2,725,60,3,4,6],[355,23,0,1,2,725,3,4,5,6],[1453,23,0,1,2,3,4,5,6,746],[217,23,0,1,2,60,3,4,5,6,746],[319,23,0,1,2,626,3,4,5,6],[1459,0,1,2,3,4,5,374,6],[220,23,0,1,2,3,4,5,374,6],[850,23,0,1,2,3,128,4,5,6],[151,23,0,1,2,3,4,5,6,175],[190,23,0,1,2,3,218,4,5,6],[1078,23,0,1,2,3,4,258,5,6],[1117,23,0,1,2,3,4,5,6,333],[2737,0,1,424,2,3,4,5,6],[1267,23,0,1,424,2,3,4,5,6],[850,23,0,1,77,2,3,4,5,6],[1171,23,0,1,2,177,3,4,5,6]],
  #[[1198,23,0,1,2,3,220,4,5,6],[3961,23,0,1,2,3,4,260,5,6],[4000,23,0,1,2,3,4,5,6,335],[1870,0,439,1,2,3,4,5,6],[334,23,0,439,1,2,3,4,5,6],[1681,23,78,1,2,3,4,5,6],[151,23,0,78,1,2,3,4,5,6],[1171,23,0,1,130,2,3,4,5,6],[328,23,0,1,2,3,221,4,5,6],[1216,23,0,1,2,3,4,261,5,6],[1255,23,0,1,2,3,4,5,6,336],[1936,454,0,1,2,3,4,5,6],[349,23,454,0,1,2,3,4,5,6],[1711,23,79,1,2,3,4,5,6],[190,23,0,79,1,2,3,4,5,6],[1198,23,0,1,131,2,3,4,5,6],[328,23,0,1,2,178,3,4,5,6],[1273,23,0,1,2,3,4,5,262,6],[1909,23,0,1,2,3,4,300,6],[1354,23,0,1,2,3,4,5,6,337],[2956,469,0,1,2,3,4,5,6],[1435,23,469,0,1,2,3,4,5,6],[1078,23,0,80,1,2,3,4,5,6],[3961,23,0,1,132,2,3,4,5,6],[1216,23,0,1,2,179,3,4,5,6],[1273,23,0,1,2,3,222,4,5,6],[2830,23,0,1,2,3,4,301,6],[4114,23,0,1,2,3,4,5,6,338],[2998,500,0,1,2,3,4,5,6],[1453,23,500,0,1,2,3,4,5,6],[1117,23,0,82,1,2,3,4,5,6],[4000,23,0,1,134,2,3,4,5,6],[1255,23,0,1,2,181,3,4,5,6],[1354,23,0,1,2,3,224,4,5,6],[4114,23,0,1,2,3,4,264,5,6],[2875,23,0,1,2,3,4,302,6],[4830,25,1,2,3,4,5,24],[3039,25,0,1,2,3,4,5,24],[960,0,1,2,3,4,5,6,26,24],[2838,0,27,1,2,3,4,5,6,24],[948,0,1,2,3,28,4,5,6,24],[2904,0,29,1,2,3,4,5,6,24],[4074,0,1,2,3,4,5,6,30,24],[4116,0,31,1,2,3,4,5,6,24],[939,0,1,2,3,4,5,32,6,24],[2841,0,33,1,2,3,4,5,6,24],[1737,0,1,2,3,4,5,6,24,36],[1755,0,1,37,2,3,4,5,6,24],[957,0,1,2,3,4,5,6,38,24],[2961,0,1,39,2,3,4,5,6,24],[1734,0,1,2,3,4,5,6,24,40],[1740,0,1,41,2,3,4,5,6,24],[945,0,1,2,3,4,44,5,6,24],[2985,0,1,2,45,3,4,5,6,24],[1743,0,1,2,3,4,5,6,24,46],[1758,0,1,2,47,3,4,5,6,24],[936,0,1,2,3,4,5,50,6,24],[2964,0,1,2,3,51,4,5,6,24],[4832,0,143,2,3,4,5,6],[4508,0,143,1,2,3,4,5,6],[4832,0,1,190,3,4,5,6],[3386,0,1,190,2,3,4,5,6],[4832,0,1,2,233,4,5,6],[3401,0,1,2,233,3,4,5,6]],
  #[[4832,0,1,2,3,273,5,6],[4538,0,1,2,3,273,4,5,6],[4832,0,1,2,3,4,311,6],[3389,0,1,2,3,4,311,5,6],[832,0,1,2,177,3,4,5,6,24],[862,0,1,2,3,220,4,5,6,24],[3814,0,1,2,3,4,260,5,6,24],[835,0,1,2,3,4,5,298,6,24],[832,0,1,130,2,3,4,5,6,24],[307,0,1,2,3,221,4,5,6,24],[907,0,1,2,3,4,261,5,6,24],[304,0,1,2,3,4,5,299,6,24],[862,0,1,131,2,3,4,5,6,24],[307,0,1,2,178,3,4,5,6,24],[943,0,1,2,3,4,5,262,6,24],[310,0,1,2,3,4,5,300,6,24],[3814,0,1,132,2,3,4,5,6,24],[907,0,1,2,179,3,4,5,6,24],[943,0,1,2,3,222,4,5,6,24],[910,0,1,2,3,4,5,301,6,24],[835,0,1,133,2,3,4,5,6,24],[304,0,1,2,180,3,4,5,6,24],[310,0,1,2,3,223,4,5,6,24],[910,0,1,2,3,4,263,5,6,24],[2373,25,0,1,2,3,4,5,6,26],[4422,25,0,27,1,2,3,4,5,6],[2367,25,0,1,2,3,28,4,5,6],[4455,25,0,29,1,2,3,4,5,6],[5136,25,0,1,2,3,4,5,6,30],[5181,25,0,31,1,2,3,4,5,6],[2358,25,0,1,2,3,4,5,32,6],[4434,25,0,33,1,2,3,4,5,6],[5208,25,0,35,1,2,3,4,5,6],[3327,25,0,1,2,3,4,5,6,36],[3354,25,0,1,37,2,3,4,5,6],[2370,25,0,1,2,3,4,5,6,38],[4485,25,0,1,39,2,3,4,5,6],[3324,25,0,1,2,3,4,5,6,40],[3336,25,0,1,41,2,3,4,5,6],[4509,25,0,1,43,2,3,4,5,6],[2364,25,0,1,2,3,4,44,5,6],[4512,25,0,1,2,45,3,4,5,6],[3348,25,0,1,2,3,4,5,6,46],[3363,25,0,1,2,47,3,4,5,6],[4824,25,0,1,2,49,3,4,5],[4527,25,0,1,2,49,3,4,5,6],[2352,25,0,1,2,3,4,5,50,6],[4494,25,0,1,2,3,51,4,5,6],[5601,25,0,1,2,3,53,4,5],[5253,25,0,1,2,3,53,4,5,6],[4815,25,0,1,2,3,4,55,5],[4515,25,0,1,2,3,4,55,5,6],[5477,0,1,144,2,3,4,5,6],[5141,25,0,1,144,2,3,4,5,6],[5225,97,25,0,1,2,3,4,5,6],[2852,0,1,2,191,3,4,5,6],[2378,25,0,1,2,191,3,4,5,6],[4520,109,25,0,1,2,3,4,5,6],[2927,0,1,2,3,4,5,6,234],[2417,25,0,1,2,3,4,5,6,234],[4532,118,25,0,1,2,3,4,5,6],[5594,0,1,2,3,4,5,6,274],[5234,25,0,1,2,3,4,5,6,274],[5270,124,25,0,1,2,3,4,5,6]],
  #[[2900,0,1,2,3,4,5,6,312],[2393,25,0,1,2,3,4,5,6,312],[4526,127,25,0,1,2,3,4,5,6],[4177,516,0,1,2,3,4,5,6],[5146,0,1,2,3,642,4,5,6],[5050,0,1,2,61,3,642,4,5,6],[5221,0,551,1,2,3,4,5,6],[2851,0,1,2,3,4,5,6,663],[2377,0,1,2,61,3,4,5,6,663],[4144,0,1,566,2,3,4,5,6],[2926,0,1,2,3,684,4,5,6],[2416,0,1,2,61,3,684,4,5,6],[4156,0,1,2,581,3,4,5,6],[5236,0,1,2,3,4,705,5,6],[5065,0,1,2,61,3,4,705,5,6],[5266,0,1,2,596,3,4,5,6],[2899,0,1,2,3,4,5,726,6],[2392,0,1,2,61,3,4,5,726,6],[4153,0,1,2,611,3,4,5,6],[5275,0,1,2,747,3,4,5,6],[5278,516,25,1,2,3,4,5,6],[5050,25,0,1,2,3,642,4,5,6],[2377,25,0,1,2,3,4,5,6,663],[2416,25,0,1,2,3,684,4,5,6],[5065,25,0,1,2,3,4,705,5,6],[2392,25,0,1,2,3,4,5,726,6],[5278,25,0,1,2,747,3,4,5],[2467,0,1,2,3,4,5,6,375],[2098,25,0,1,2,3,128,4,5,6],[967,25,0,1,2,3,4,5,6,175],[1063,25,0,1,2,3,218,4,5,6],[2143,25,0,1,2,3,4,258,5,6],[1033,25,0,1,2,3,4,5,296,6],[5146,0,1,425,2,3,4,5,6],[5050,25,0,1,425,2,3,4,5,6],[4078,25,1,77,2,3,4,5,6],[2098,25,0,1,77,2,3,4,5,6],[2203,25,0,1,2,177,3,4,5,6],[2260,25,0,1,2,3,220,4,5,6],[5041,25,0,1,2,3,4,260,5,6],[2230,25,0,1,2,3,4,5,298,6],[2851,0,440,1,2,3,4,5,6],[2377,25,0,440,1,2,3,4,5,6],[967,25,0,78,1,2,3,4,5,6],[2203,25,0,1,130,2,3,4,5,6],[1693,25,0,1,2,3,221,4,5,6],[2296,25,0,1,2,3,4,261,5,6],[1678,25,0,1,2,3,4,5,299,6],[2926,455,0,1,2,3,4,5,6],[2416,25,455,0,1,2,3,4,5,6],[2923,25,79,1,2,3,4,5,6],[1063,25,0,79,1,2,3,4,5,6],[2260,25,0,1,131,2,3,4,5,6],[1693,25,0,1,2,178,3,4,5,6],[2362,25,0,1,2,3,4,5,262,6],[1699,25,0,1,2,3,4,5,300,6],[2917,25,0,1,2,3,4,5,337],[5236,470,0,1,2,3,4,5,6],[5065,25,470,0,1,2,3,4,5,6],[4159,25,80,1,2,3,4,5,6],[2143,25,0,80,1,2,3,4,5,6],[5041,25,0,1,132,2,3,4,5,6],[2296,25,0,1,2,179,3,4,5,6],[2362,25,0,1,2,3,222,4,5,6]],
  #[[2317,25,0,1,2,3,4,5,301,6],[5230,25,0,1,2,3,4,5,338],[2899,485,0,1,2,3,4,5,6],[2392,25,485,0,1,2,3,4,5,6],[1033,25,0,81,1,2,3,4,5,6],[2230,25,0,1,133,2,3,4,5,6],[1678,25,0,1,2,180,3,4,5,6],[1699,25,0,1,2,3,223,4,5,6],[2317,25,0,1,2,3,4,263,5,6],[2875,25,0,1,2,3,4,5,339],[4740,0,27,3,4,5,6,26],[684,0,1,2,3,4,44,5,6,26],[2718,0,1,2,45,3,4,5,6,26],[1578,0,1,2,3,4,5,6,26,46],[1629,0,1,2,47,3,4,5,6,26],[786,0,1,2,3,4,5,6,26,48],[2778,0,1,2,49,3,4,5,6,26],[675,0,1,2,3,4,5,50,6,26],[2637,0,1,2,3,51,4,5,6,26],[4038,0,1,2,3,4,5,6,26,52],[4062,0,1,2,3,53,4,5,6,26],[705,0,1,2,3,4,5,6,54,26],[2724,0,1,2,3,4,55,5,6,26],[4742,83,1,2,3,4,5,6],[2888,83,0,1,2,3,4,5,6],[4742,0,1,2,235,4,5,6],[3263,0,1,2,235,3,4,5,6],[4742,0,1,2,3,275,5,6],[4388,0,1,2,3,275,4,5,6],[4742,0,1,2,3,4,313,6],[3218,0,1,2,3,4,313,5,6],[4742,0,1,2,3,4,5,350],[4430,0,1,2,3,4,5,350,6],[85,0,1,2,3,218,4,5,6,26],[439,0,1,2,3,4,258,5,6,26],[46,0,1,2,3,4,5,296,6,26],[478,0,1,2,3,4,5,6,333,26],[1012,0,1,2,376,3,4,5,6],[85,0,79,1,2,3,4,5,6,26],[682,0,1,2,3,4,5,262,6,26],[256,0,1,2,3,4,5,300,6,26],[784,0,1,2,3,4,5,6,337,26],[439,0,80,1,2,3,4,5,6,26],[682,0,1,2,3,222,4,5,6,26],[583,0,1,2,3,4,5,301,6,26],[3802,0,1,2,3,4,5,6,338,26],[46,0,81,1,2,3,4,5,6,26],[256,0,1,2,3,223,4,5,6,26],[583,0,1,2,3,4,263,5,6,26],[703,0,1,2,3,4,5,6,339,26],[478,0,82,1,2,3,4,5,6,26],[784,0,1,2,3,224,4,5,6,26],[3802,0,1,2,3,4,264,5,6,26],[703,0,1,2,3,4,5,302,6,26],[4890,0,27,29,2,3,4,5,6],[4581,0,27,29,1,2,3,4,5,6],[5328,0,27,31,1,2,3,4,5,6],[4884,0,27,33,2,3,4,5,6],[4563,0,27,33,1,2,3,4,5,6],[5361,0,27,35,1,2,3,4,5,6],[3474,0,27,1,37,2,3,4,5,6],[5682,0,27,1,39,3,4,5,6],[4602,0,27,1,39,2,3,4,5,6],[3444,0,27,1,41,2,3,4,5,6]],
  #[[5694,0,27,1,43,3,4,5,6],[4620,0,27,1,43,2,3,4,5,6],[2490,0,27,1,2,3,4,44,5,6],[4626,0,27,1,2,45,3,4,5,6],[3447,0,27,1,2,3,4,5,6,46],[3477,0,27,1,2,47,3,4,5,6],[2586,0,27,1,2,3,4,5,6,48],[4644,0,27,1,2,49,3,4,5,6],[2484,0,27,1,2,3,4,5,50,6],[4605,0,27,1,2,3,51,4,5,6],[5433,0,27,1,2,3,4,5,6,52],[5451,0,27,1,2,3,53,4,5,6],[2502,0,27,1,2,3,4,5,6,54],[4629,0,27,1,2,3,4,55,5,6],[2711,0,84,1,2,3,4,5,6],[2483,0,27,84,1,2,3,4,5,6],[4625,85,0,27,1,2,3,4,5,6],[3566,0,1,2,3,236,4,5,6],[3428,0,27,1,2,3,236,4,5,6],[4892,0,147,1,2,3,4,5,6],[4859,0,147,27,1,2,3,4,5,6],[5405,0,1,2,3,4,5,6,276],[5291,0,27,1,2,3,4,5,6,276],[5684,0,150,1,2,3,4,5,6],[5633,0,150,27,1,2,3,4,5,6],[3560,0,1,2,3,4,5,314,6],[3425,0,27,1,2,3,4,5,314,6],[4886,0,153,1,2,3,4,5,6],[4844,0,153,27,1,2,3,4,5,6],[5414,0,1,2,3,4,5,6,351],[5294,0,27,1,2,3,4,5,6,351],[5696,0,156,1,2,3,4,5,6],[5639,0,156,27,1,2,3,4,5,6],[2710,0,1,2,3,377,4,5,6],[844,0,1,2,7,3,377,4,5,6],[2482,0,27,1,2,3,377,4,5,6],[667,0,27,1,2,7,3,377,4,5,6],[1015,0,378,1,2,3,4,5,6],[844,0,378,27,1,2,3,4,5,6],[841,0,27,129,1,2,3,4,5,6],[838,0,27,1,176,2,3,4,5,6],[1204,0,27,1,2,3,218,4,5,6],[79,0,27,1,2,7,3,218,4,5,6],[871,0,27,1,2,219,3,4,5,6],[2284,0,27,1,2,3,4,258,5,6],[436,0,27,1,2,7,3,4,258,5,6],[919,0,27,1,2,259,3,4,5,6],[1177,0,27,1,2,3,4,5,296,6],[40,0,27,1,2,7,3,4,5,296,6],[853,0,27,1,2,297,3,4,5,6],[2344,0,27,1,2,3,4,5,6,333],[472,0,27,1,2,7,3,4,5,6,333],[964,0,27,1,2,334,3,4,5,6],[2710,0,1,2,518,3,4,5,6],[2482,0,1,2,62,518,3,4,5,6],[4555,517,0,1,2,3,4,5,6],[5608,0,643,1,2,3,4,5,6],[4840,0,1,664,2,3,4,5,6],[3466,0,1,2,3,685,4,5,6],[3412,0,1,2,62,3,685,4,5,6],[4837,0,1,2,582,3,4,5,6],[5320,0,1,2,3,4,706,5,6],[5281,0,1,2,62,3,4,706,5,6],[5605,0,1,2,597,3,4,5,6]],
  #[[3436,0,1,2,3,4,5,727,6],[3406,0,1,2,62,3,4,5,727,6],[4834,0,1,2,612,3,4,5,6],[5365,0,1,2,3,4,5,6,748],[5287,0,1,2,62,3,4,5,6,748],[5611,0,1,2,627,3,4,5,6],[2482,0,27,1,2,518,3,4,5,6],[5803,0,27,643,2,3,4,5,6],[5803,0,27,1,664,3,4,5,6],[3412,0,27,1,2,3,685,4,5,6],[5281,0,27,1,2,3,4,706,5,6],[3406,0,27,1,2,3,4,5,727,6],[5287,0,27,1,2,3,4,5,6,748],[1204,0,79,27,1,2,3,4,5,6],[3466,0,456,1,2,3,4,5,6],[3412,0,27,456,1,2,3,4,5,6],[3085,0,27,131,2,3,4,5,6],[2488,0,27,1,2,3,4,5,262,6],[1804,0,27,1,2,3,4,5,300,6],[2584,0,27,1,2,3,4,5,6,337],[2284,0,80,27,1,2,3,4,5,6],[5320,0,471,1,2,3,4,5,6],[5281,0,27,471,1,2,3,4,5,6],[4216,0,27,1,179,3,4,5,6],[2488,0,27,1,2,3,222,4,5,6],[2470,0,27,1,2,3,4,5,301,6],[5098,0,27,1,2,3,4,5,6,338],[1177,0,81,27,1,2,3,4,5,6],[3436,0,486,1,2,3,4,5,6],[3406,0,27,486,1,2,3,4,5,6],[3070,0,27,133,2,3,4,5,6],[1804,0,27,1,2,3,223,4,5,6],[2470,0,27,1,2,3,4,263,5,6],[2500,0,27,1,2,3,4,5,6,339],[2344,0,82,27,1,2,3,4,5,6],[5365,0,501,1,2,3,4,5,6],[5287,0,27,501,1,2,3,4,5,6],[4237,0,27,1,181,3,4,5,6],[2584,0,27,1,2,3,224,4,5,6],[5098,0,27,1,2,3,4,264,5,6],[2500,0,27,1,2,3,4,5,302,6],[4725,0,29,2,28,4,5,6],[678,0,1,2,3,28,4,5,6,38],[2610,0,1,39,2,3,28,4,5,6],[1524,0,1,2,3,28,4,5,6,40],[1548,0,1,41,2,3,28,4,5,6],[714,0,1,2,3,28,4,5,6,42],[2661,0,1,43,2,3,28,4,5,6],[636,0,1,2,3,28,4,5,50,6],[2634,0,1,2,3,28,51,4,5,6],[4035,0,1,2,3,28,4,5,6,52],[4056,0,1,2,3,28,53,4,5,6],[663,0,1,2,3,28,4,5,6,54],[2694,0,1,2,3,28,4,55,5,6],[2873,86,0,1,2,3,4,5,6],[3152,0,1,192,2,3,4,5,6],[4367,0,1,2,3,277,4,5,6],[3206,0,1,2,3,315,4,5,6],[4421,0,1,2,3,352,4,5,6],[22,0,1,2,3,28,4,5,6,175],[991,0,1,2,379,3,4,5,6],[430,0,1,2,3,28,4,258,5,6],[37,0,1,2,3,28,4,5,296,6],[466,0,1,2,3,28,4,5,6,333]],
  #[[22,0,78,1,2,3,28,4,5,6],[568,0,1,2,3,28,4,261,5,6],[229,0,1,2,3,28,4,5,299,6],[604,0,1,2,3,28,4,5,6,336],[430,0,80,1,2,3,28,4,5,6],[568,0,1,2,179,3,28,4,5,6],[580,0,1,2,3,28,4,5,301,6],[3799,0,1,2,3,28,4,5,6,338],[37,0,81,1,2,3,28,4,5,6],[229,0,1,2,180,3,28,4,5,6],[580,0,1,2,3,28,4,263,5,6],[661,0,1,2,3,28,4,5,6,339],[466,0,82,1,2,3,28,4,5,6],[604,0,1,2,181,3,28,4,5,6],[3799,0,1,2,3,28,4,264,5,6],[661,0,1,2,3,28,4,5,302,6],[5655,0,29,2,3,4,5,6,30],[5385,0,29,31,1,2,3,4,5,6],[4893,0,29,33,2,3,4,5,6],[4590,0,29,33,1,2,3,4,5,6],[5721,0,29,35,2,3,4,5,6],[5427,0,29,35,1,2,3,4,5,6],[4890,0,29,1,37,2,4,5,6],[3492,0,29,1,37,2,3,4,5,6],[2574,0,29,1,2,3,4,5,6,38],[4626,0,29,1,39,2,3,4,5,6],[3459,0,29,1,2,3,4,5,6,40],[3477,0,29,1,41,2,3,4,5,6],[2577,0,29,1,2,3,4,5,6,42],[4644,0,29,1,43,2,3,4,5,6],[5703,0,29,1,2,45,4,5,6],[4647,0,29,1,2,45,3,4,5,6],[3498,0,29,1,2,47,3,4,5,6],[5721,0,29,1,2,49,4,5,6],[4653,0,29,1,2,49,3,4,5,6],[2559,0,29,1,2,3,4,5,50,6],[4632,0,29,1,2,3,51,4,5,6],[5457,0,29,1,2,3,4,5,6,52],[5478,0,29,1,2,3,53,4,5,6],[2571,0,29,1,2,3,4,5,6,54],[4650,0,29,1,2,3,4,55,5,6],[2804,0,1,87,2,3,4,5,6],[2603,0,29,1,87,2,3,4,5,6],[4658,88,0,29,1,2,3,4,5,6],[3587,0,1,2,3,4,5,6,193],[3470,0,29,1,2,3,4,5,6,193],[4868,0,147,29,1,2,3,4,5,6],[5378,0,1,2,3,4,278,5,6],[5303,0,29,1,2,3,4,278,5,6],[5705,0,159,1,2,3,4,5,6],[5663,0,159,29,1,2,3,4,5,6],[3626,0,1,2,3,4,5,316,6],[3482,0,29,1,2,3,4,5,316,6],[4895,0,162,1,2,3,4,5,6],[4874,0,162,29,1,2,3,4,5,6],[5432,0,1,2,3,4,5,6,353],[5306,0,29,1,2,3,4,5,6,353],[5723,0,165,1,2,3,4,5,6],[5666,0,165,29,1,2,3,4,5,6],[2803,0,1,2,380,3,4,5,6],[883,0,1,2,7,380,3,4,5,6],[2602,0,29,1,2,380,3,4,5,6],[820,0,29,1,2,7,380,3,4,5,6],[1051,0,381,1,2,3,4,5,6]],
  #[[883,0,381,29,1,2,3,4,5,6],[2782,0,29,2,3,128,4,5,6],[868,0,29,2,7,3,128,4,5,6],[868,0,129,29,1,2,3,4,5,6],[1180,0,29,1,2,3,4,5,6,175],[52,0,29,1,2,7,3,4,5,6,175],[865,0,29,1,176,2,3,4,5,6],[880,0,29,1,2,219,3,4,5,6],[2311,0,29,1,2,3,4,258,5,6],[451,0,29,1,2,7,3,4,258,5,6],[994,0,29,1,2,259,3,4,5,6],[1201,0,29,1,2,3,4,5,296,6],[61,0,29,1,2,7,3,4,5,296,6],[877,0,29,1,2,297,3,4,5,6],[2395,0,29,1,2,3,4,5,6,333],[484,0,29,1,2,7,3,4,5,6,333],[1036,0,29,1,2,334,3,4,5,6],[2803,0,1,520,2,3,4,5,6],[2602,0,1,63,520,2,3,4,5,6],[4594,519,0,1,2,3,4,5,6],[5626,644,0,1,2,3,4,5,6],[3472,0,1,2,665,3,4,5,6],[3418,0,1,63,2,665,3,4,5,6],[4864,0,1,567,2,3,4,5,6],[4876,0,1,686,2,3,4,5,6],[5377,0,1,2,3,4,5,707,6],[5302,0,1,63,2,3,4,5,707,6],[5623,0,1,598,2,3,4,5,6],[3484,0,1,2,3,4,5,728,6],[3421,0,1,63,2,3,4,5,728,6],[4870,0,1,613,2,3,4,5,6],[5431,0,1,2,3,4,5,6,749],[5305,0,1,63,2,3,4,5,6,749],[5629,0,1,628,2,3,4,5,6],[2602,0,29,1,520,2,3,4,5,6],[5809,644,0,29,2,3,4,5,6],[3418,0,29,1,2,665,3,4,5,6],[5809,0,29,1,686,2,4,5,6],[5302,0,29,1,2,3,4,5,707,6],[3421,0,29,1,2,3,4,5,728,6],[5305,0,29,1,2,3,4,5,6,749],[1180,0,78,29,1,2,3,4,5,6],[3472,0,441,1,2,3,4,5,6],[3418,0,29,441,1,2,3,4,5,6],[3088,0,29,130,2,3,4,5,6],[3463,0,29,1,2,221,4,5,6],[2506,0,29,1,2,3,4,261,5,6],[1798,0,29,1,2,3,4,5,299,6],[2554,0,29,1,2,3,4,5,6,336],[2311,0,80,29,1,2,3,4,5,6],[5377,0,472,1,2,3,4,5,6],[5302,0,29,472,1,2,3,4,5,6],[2506,0,29,1,2,179,3,4,5,6],[4252,0,29,1,2,222,4,5,6],[2521,0,29,1,2,3,4,5,301,6],[5113,0,29,1,2,3,4,5,6,338],[1201,0,81,29,1,2,3,4,5,6],[3484,0,487,1,2,3,4,5,6],[3421,0,29,487,1,2,3,4,5,6],[3094,0,29,133,2,3,4,5,6],[1798,0,29,1,2,180,3,4,5,6],[2521,0,29,1,2,3,4,263,5,6],[2569,0,29,1,2,3,4,5,6,339],[2395,0,82,29,1,2,3,4,5,6]],
  #[[5431,0,502,1,2,3,4,5,6],[5305,0,29,502,1,2,3,4,5,6],[5419,0,29,134,2,3,4,5,6],[2554,0,29,1,2,181,3,4,5,6],[4321,0,29,1,2,224,4,5,6],[5113,0,29,1,2,3,4,264,5,6],[2569,0,29,1,2,3,4,5,302,6],[5943,0,31,2,3,5,6,30],[4548,0,1,2,3,4,5,6,30,36],[4575,0,1,37,2,3,4,5,6,30],[4542,0,1,2,3,4,5,6,30,40],[4557,0,1,41,2,3,4,5,6,30],[3885,0,1,2,3,4,5,6,42,30],[5349,0,1,43,2,3,4,5,6,30],[5655,0,1,2,45,3,5,6,30],[4566,0,1,2,3,4,5,6,30,46],[4584,0,1,2,47,3,4,5,6,30],[3897,0,1,2,3,4,5,6,30,48],[5415,0,1,2,49,3,4,5,6,30],[3879,0,1,2,3,4,5,6,54,30],[5388,0,1,2,3,4,55,5,6,30],[5945,89,1,2,3,4,5,6],[5489,89,0,1,2,3,4,5,6],[5945,0,1,194,3,4,5,6],[5642,0,1,194,2,3,4,5,6],[5945,0,1,2,237,4,5,6],[5657,0,1,2,237,3,4,5,6],[5945,0,1,2,3,4,317,6],[5648,0,1,2,3,4,317,5,6],[5945,0,1,2,3,4,5,354],[5930,0,1,2,3,4,5,354,6],[2155,0,1,2,3,4,5,6,175,30],[2167,0,1,2,3,218,4,5,6,30],[2161,0,1,2,3,4,5,296,6,30],[3820,0,1,2,3,4,5,6,333,30],[2380,0,1,2,382,3,4,5,6],[2155,0,78,1,2,3,4,5,6,30],[3049,0,1,2,3,221,4,5,6,30],[3043,0,1,2,3,4,5,299,6,30],[3859,0,1,2,3,4,5,6,336,30],[2167,0,79,1,2,3,4,5,6,30],[3049,0,1,2,178,3,4,5,6,30],[3055,0,1,2,3,4,5,300,6,30],[3895,0,1,2,3,4,5,6,337,30],[2161,0,81,1,2,3,4,5,6,30],[3043,0,1,2,180,3,4,5,6,30],[3055,0,1,2,3,223,4,5,6,30],[3877,0,1,2,3,4,5,6,339,30],[3820,0,82,1,2,3,4,5,6,30],[3859,0,1,2,181,3,4,5,6,30],[3895,0,1,2,3,224,4,5,6,30],[3877,0,1,2,3,4,5,302,6,30],[5343,0,31,33,1,2,3,4,5,6],[5940,0,31,35,2,3,4,5,6],[5856,0,31,35,1,2,3,4,5,6],[4599,0,31,1,2,3,4,5,6,36],[4626,0,31,1,37,2,3,4,5,6],[5682,0,31,1,39,2,3,5,6],[5436,0,31,1,39,2,3,4,5,6],[4596,0,31,1,2,3,4,5,6,40],[4605,0,31,1,41,2,3,4,5,6],[3957,0,31,1,2,3,4,5,6,42],[5451,0,31,1,43,2,3,4,5,6],[5460,0,31,1,2,45,3,4,5,6]],
  #[[4608,0,31,1,2,3,4,5,6,46],[4632,0,31,1,2,47,3,4,5,6],[4008,0,31,1,2,3,4,5,6,48],[5478,0,31,1,2,49,3,4,5,6],[5445,0,31,1,2,3,51,4,5,6],[5940,0,31,1,2,3,53,5,6],[5886,0,31,1,2,3,53,4,5,6],[3948,0,31,1,2,3,4,5,6,54],[5466,0,31,1,2,3,4,55,5,6],[4469,0,1,90,2,3,4,5,6],[4100,0,31,1,90,2,3,4,5,6],[5174,91,0,31,1,2,3,4,5,6],[4289,0,1,2,3,4,5,6,195],[3956,0,31,1,2,3,4,5,6,195],[5441,0,150,31,1,2,3,4,5,6],[4262,0,1,2,3,238,4,5,6],[3938,0,31,1,2,3,238,4,5,6],[5465,0,159,31,1,2,3,4,5,6],[4250,0,1,2,3,4,5,318,6],[3932,0,31,1,2,3,4,5,318,6],[5687,0,168,1,2,3,4,5,6],[5450,0,168,31,1,2,3,4,5,6],[5936,0,1,2,3,4,5,6,355],[5864,0,31,1,2,3,4,5,6,355],[5942,0,171,1,2,3,4,5,6],[5891,0,171,31,1,2,3,4,5,6],[4111,0,1,2,3,383,4,5,6],[2116,0,1,2,7,3,383,4,5,6],[3826,0,31,1,2,3,383,4,5,6],[2437,0,384,1,2,3,4,5,6],[2116,0,384,31,1,2,3,4,5,6],[4069,0,31,2,3,128,4,5,6],[2083,0,31,2,7,3,128,4,5,6],[2083,0,129,31,1,2,3,4,5,6],[2173,0,31,1,2,3,4,5,6,175],[391,0,31,1,2,7,3,4,5,6,175],[2080,0,31,1,176,2,3,4,5,6],[2263,0,31,1,2,3,218,4,5,6],[421,0,31,1,2,7,3,218,4,5,6],[2101,0,31,1,2,219,3,4,5,6],[2113,0,31,1,2,259,3,4,5,6],[2194,0,31,1,2,3,4,5,296,6],[400,0,31,1,2,7,3,4,5,296,6],[2089,0,31,1,2,297,3,4,5,6],[3832,0,31,1,2,3,4,5,6,333],[2119,0,31,1,2,334,3,4,5,6],[4111,0,1,522,2,3,4,5,6],[3826,0,1,64,522,2,3,4,5,6],[5158,521,0,1,2,3,4,5,6],[5842,645,0,1,2,3,4,5,6],[4222,0,1,2,666,3,4,5,6],[3910,0,1,64,2,666,3,4,5,6],[5110,0,1,568,2,3,4,5,6],[4261,0,1,2,3,4,687,5,6],[3937,0,1,64,2,3,4,687,5,6],[5104,0,1,583,2,3,4,5,6],[5869,0,1,708,2,3,4,5,6],[4231,0,1,2,3,4,5,729,6],[3916,0,1,64,2,3,4,5,729,6],[5101,0,1,614,2,3,4,5,6],[5884,0,1,2,3,4,5,6,750],[5836,0,1,64,2,3,4,5,6,750],[5866,0,1,629,2,3,4,5,6],[3826,0,31,1,522,2,3,4,5,6]],
  #[[5872,645,0,31,2,3,4,5,6],[3910,0,31,1,2,666,3,4,5,6],[3937,0,31,1,2,3,4,687,5,6],[5872,0,31,1,708,2,3,5,6],[3916,0,31,1,2,3,4,5,729,6],[5836,0,31,1,2,3,4,5,6,750],[2173,0,78,31,1,2,3,4,5,6],[4222,0,442,1,2,3,4,5,6],[3910,0,31,442,1,2,3,4,5,6],[3064,0,31,1,2,3,221,4,5,6],[4216,0,31,1,2,3,261,5,6],[3061,0,31,1,2,3,4,5,299,6],[3925,0,31,1,2,3,4,5,6,336],[2263,0,79,31,1,2,3,4,5,6],[4261,0,1,457,2,3,4,5,6],[3937,0,31,1,457,2,3,4,5,6],[3064,0,31,1,2,178,3,4,5,6],[3079,0,31,1,2,3,4,5,300,6],[4006,0,31,1,2,3,4,5,6,337],[2194,0,81,31,1,2,3,4,5,6],[4231,0,488,1,2,3,4,5,6],[3916,0,31,488,1,2,3,4,5,6],[3061,0,31,1,2,180,3,4,5,6],[3079,0,31,1,2,3,223,4,5,6],[3946,0,31,1,2,3,4,5,6,339],[3832,0,82,31,1,2,3,4,5,6],[5884,0,503,1,2,3,4,5,6],[5836,0,31,503,1,2,3,4,5,6],[5851,0,31,134,2,3,4,5,6],[3925,0,31,1,2,181,3,4,5,6],[4006,0,31,1,2,3,224,4,5,6],[5878,0,31,1,2,3,264,5,6],[3946,0,31,1,2,3,4,5,302,6],[4719,0,33,2,3,4,32,6],[1515,0,1,2,3,4,5,32,6,36],[1596,0,1,37,2,3,4,5,32,6],[672,0,1,2,3,4,5,32,6,38],[2607,0,1,39,2,3,4,5,32,6],[699,0,1,2,3,4,5,32,6,42],[2652,0,1,43,2,3,4,5,32,6],[630,0,1,2,3,4,44,5,32,6],[2676,0,1,2,45,3,4,5,32,6],[774,0,1,2,3,4,5,32,6,48],[2766,0,1,2,49,3,4,5,32,6],[4032,0,1,2,3,4,5,32,6,52],[4053,0,1,2,3,53,4,5,32,6],[2864,92,0,1,2,3,4,5,6],[3143,0,1,196,2,3,4,5,6],[3248,0,1,2,239,3,4,5,6],[4364,0,1,2,3,279,4,5,6],[4412,0,1,2,3,4,5,356,6],[16,0,1,2,3,4,5,32,6,175],[70,0,1,2,3,218,4,5,32,6],[427,0,1,2,3,4,258,5,32,6],[976,0,1,2,385,3,4,5,6],[460,0,1,2,3,4,5,32,6,333],[16,0,78,1,2,3,4,5,32,6],[238,0,1,2,3,221,4,5,32,6],[565,0,1,2,3,4,261,5,32,6],[598,0,1,2,3,4,5,32,6,336],[70,0,79,1,2,3,4,5,32,6],[238,0,1,2,178,3,4,5,32,6],[628,0,1,2,3,4,5,32,262,6],[772,0,1,2,3,4,5,32,6,337]],
  #[[427,0,80,1,2,3,4,5,32,6],[565,0,1,2,179,3,4,5,32,6],[628,0,1,2,3,222,4,5,32,6],[3796,0,1,2,3,4,5,32,6,338],[460,0,82,1,2,3,4,5,32,6],[598,0,1,2,181,3,4,5,32,6],[772,0,1,2,3,224,4,5,32,6],[3796,0,1,2,3,4,264,5,32,6],[5397,0,33,35,1,2,3,4,5,6],[3429,0,33,1,2,3,4,5,6,36],[3477,0,33,1,37,2,3,4,5,6],[2535,0,33,1,2,3,4,5,6,38],[4605,0,33,1,39,2,3,4,5,6],[4884,0,33,1,41,2,3,4,6],[3450,0,33,1,41,2,3,4,5,6],[2538,0,33,1,2,3,4,5,6,42],[4629,0,33,1,43,2,3,4,5,6],[2529,0,33,1,2,3,4,44,5,6],[4632,0,33,1,2,45,3,4,5,6],[3486,0,33,1,2,47,3,4,5,6],[2592,0,33,1,2,3,4,5,6,48],[4650,0,33,1,2,49,3,4,5,6],[5685,0,33,1,2,3,51,4,6],[4611,0,33,1,2,3,51,4,5,6],[5442,0,33,1,2,3,4,5,6,52],[5466,0,33,1,2,3,53,4,5,6],[5712,0,33,1,2,3,4,55,6],[4638,0,33,1,2,3,4,55,5,6],[2744,0,1,93,2,3,4,5,6],[2546,0,33,1,93,2,3,4,5,6],[4643,94,0,33,1,2,3,4,5,6],[3575,0,1,2,3,4,5,6,197],[3440,0,33,1,2,3,4,5,6,197],[4850,0,153,33,1,2,3,4,5,6],[3632,0,1,2,3,240,4,5,6],[3458,0,33,1,2,3,240,4,5,6],[4862,0,162,33,1,2,3,4,5,6],[5369,0,1,2,3,4,5,280,6],[5297,0,33,1,2,3,4,5,280,6],[5636,0,168,33,1,2,3,4,5,6],[5402,0,1,2,3,4,5,6,357],[5300,0,33,1,2,3,4,5,6,357],[5714,0,174,1,2,3,4,5,6],[5654,0,174,33,1,2,3,4,5,6],[2743,0,1,2,3,386,4,5,6],[859,0,1,2,7,3,386,4,5,6],[2545,0,33,1,2,3,386,4,5,6],[739,0,33,1,2,7,3,386,4,5,6],[1027,0,387,1,2,3,4,5,6],[859,0,387,33,1,2,3,4,5,6],[2731,0,33,2,3,128,4,5,6],[850,0,33,2,7,3,128,4,5,6],[850,0,129,33,1,2,3,4,5,6],[1162,0,33,1,2,3,4,5,6,175],[28,0,33,1,2,7,3,4,5,6,175],[847,0,33,1,176,2,3,4,5,6],[1207,0,33,1,2,3,218,4,5,6],[91,0,33,1,2,7,3,218,4,5,6],[874,0,33,1,2,219,3,4,5,6],[2287,0,33,1,2,3,4,258,5,6],[445,0,33,1,2,7,3,4,258,5,6],[928,0,33,1,2,259,3,4,5,6],[856,0,33,1,2,297,3,4,5,6],[2356,0,33,1,2,3,4,5,6,333]],
  #[[481,0,33,1,2,7,3,4,5,6,333],[979,0,33,1,2,334,3,4,5,6],[2743,0,1,524,2,3,4,5,6],[2545,0,1,65,524,2,3,4,5,6],[4573,523,0,1,2,3,4,5,6],[5617,646,0,1,2,3,4,5,6],[3442,0,1,2,667,3,4,5,6],[3409,0,1,65,2,667,3,4,5,6],[4846,0,1,569,2,3,4,5,6],[3490,0,1,2,3,688,4,5,6],[3415,0,1,65,2,3,688,4,5,6],[4855,0,1,584,2,3,4,5,6],[5335,0,1,2,3,4,709,5,6],[5284,0,1,65,2,3,4,709,5,6],[5614,0,1,599,2,3,4,5,6],[4852,0,1,730,2,3,4,5,6],[5401,0,1,2,3,4,5,6,751],[5299,0,1,65,2,3,4,5,6,751],[5620,0,1,630,2,3,4,5,6],[2545,0,33,1,524,2,3,4,5,6],[5806,646,0,33,2,3,4,5,6],[3409,0,33,1,2,667,3,4,5,6],[3415,0,33,1,2,3,688,4,5,6],[5284,0,33,1,2,3,4,709,5,6],[5806,0,33,1,730,2,3,4,6],[5299,0,33,1,2,3,4,5,6,751],[1162,0,78,33,1,2,3,4,5,6],[3442,0,443,1,2,3,4,5,6],[3409,0,33,443,1,2,3,4,5,6],[3073,0,33,130,2,3,4,5,6],[1801,0,33,1,2,3,221,4,5,6],[2476,0,33,1,2,3,4,261,5,6],[3433,0,33,1,2,3,4,299,6],[2515,0,33,1,2,3,4,5,6,336],[1207,0,79,33,1,2,3,4,5,6],[3490,0,1,458,2,3,4,5,6],[3415,0,33,1,458,2,3,4,5,6],[3097,0,33,131,2,3,4,5,6],[1801,0,33,1,2,178,3,4,5,6],[2527,0,33,1,2,3,4,5,262,6],[2590,0,33,1,2,3,4,5,6,337],[2287,0,80,33,1,2,3,4,5,6],[5335,0,473,1,2,3,4,5,6],[5284,0,33,473,1,2,3,4,5,6],[2476,0,33,1,2,179,3,4,5,6],[2527,0,33,1,2,3,222,4,5,6],[4225,0,33,1,2,3,4,301,6],[5107,0,33,1,2,3,4,5,6,338],[2356,0,82,33,1,2,3,4,5,6],[5401,0,504,1,2,3,4,5,6],[5299,0,33,504,1,2,3,4,5,6],[2515,0,33,1,2,181,3,4,5,6],[2590,0,33,1,2,3,224,4,5,6],[5107,0,33,1,2,3,4,264,5,6],[4267,0,33,1,2,3,4,302,6],[5946,0,35,2,3,4,5,34],[4551,0,1,2,3,4,5,6,34,36],[4578,0,1,37,2,3,4,5,6,34],[3882,0,1,2,3,4,5,6,38,34],[5313,0,1,39,2,3,4,5,6,34],[4545,0,1,2,3,4,5,6,34,40],[4560,0,1,41,2,3,4,5,6,34],[3873,0,1,2,3,4,44,5,6,34],[5373,0,1,2,45,3,4,5,6,34]],
  #[[4569,0,1,2,3,4,5,6,34,46],[4587,0,1,2,47,3,4,5,6,34],[3867,0,1,2,3,4,5,50,6,34],[5331,0,1,2,3,51,4,5,6,34],[5948,95,1,2,3,4,5,6],[5492,95,0,1,2,3,4,5,6],[5948,0,1,198,3,4,5,6],[5645,0,1,198,2,3,4,5,6],[5948,0,1,2,241,4,5,6],[5660,0,1,2,241,3,4,5,6],[5948,0,1,2,3,281,5,6],[5927,0,1,2,3,281,4,5,6],[5948,0,1,2,3,4,319,6],[5651,0,1,2,3,4,319,5,6],[2158,0,1,2,3,4,5,6,175,34],[2170,0,1,2,3,218,4,5,6,34],[3805,0,1,2,3,4,258,5,6,34],[2164,0,1,2,3,4,5,296,6,34],[2383,0,1,2,388,3,4,5,6],[2158,0,78,1,2,3,4,5,6,34],[3052,0,1,2,3,221,4,5,6,34],[3853,0,1,2,3,4,261,5,6,34],[3046,0,1,2,3,4,5,299,6,34],[2170,0,79,1,2,3,4,5,6,34],[3052,0,1,2,178,3,4,5,6,34],[3871,0,1,2,3,4,5,262,6,34],[3058,0,1,2,3,4,5,300,6,34],[3805,0,80,1,2,3,4,5,6,34],[3853,0,1,2,179,3,4,5,6,34],[3871,0,1,2,3,222,4,5,6,34],[3856,0,1,2,3,4,5,301,6,34],[2164,0,81,1,2,3,4,5,6,34],[3046,0,1,2,180,3,4,5,6,34],[3058,0,1,2,3,223,4,5,6,34],[3856,0,1,2,3,4,263,5,6,34],[4617,0,35,1,2,3,4,5,6,36],[4644,0,35,1,37,2,3,4,5,6],[3990,0,35,1,2,3,4,5,6,38],[5451,0,35,1,39,2,3,4,5,6],[4614,0,35,1,2,3,4,5,6,40],[4629,0,35,1,41,2,3,4,5,6],[5694,0,35,1,43,2,3,4,5],[5469,0,35,1,43,2,3,4,5,6],[3978,0,35,1,2,3,4,44,5,6],[5478,0,35,1,2,45,3,4,5,6],[4635,0,35,1,2,3,4,5,6,46],[4650,0,35,1,2,47,3,4,5,6],[5493,0,35,1,2,49,3,4,5,6],[3972,0,35,1,2,3,4,5,50,6],[5466,0,35,1,2,3,51,4,5,6],[5940,0,35,1,2,3,53,4,5],[5895,0,35,1,2,3,53,4,5,6],[5481,0,35,1,2,3,4,55,5,6],[4505,0,1,96,2,3,4,5,6],[4133,0,35,1,96,2,3,4,5,6],[5213,97,0,35,1,2,3,4,5,6],[4295,0,1,2,3,4,5,6,199],[3995,0,35,1,2,3,4,5,6,199],[5474,0,156,35,1,2,3,4,5,6],[4328,0,1,2,3,242,4,5,6],[4019,0,35,1,2,3,242,4,5,6],[5498,0,165,35,1,2,3,4,5,6],[5933,0,1,2,3,4,5,6,282],[5876,0,35,1,2,3,4,5,6,282]],
  #[[5906,0,171,35,1,2,3,4,5,6],[4274,0,1,2,3,4,5,320,6],[3986,0,35,1,2,3,4,5,320,6],[5486,0,174,35,1,2,3,4,5,6],[4138,0,1,2,3,389,4,5,6],[2137,0,1,2,7,3,389,4,5,6],[3841,0,35,1,2,3,389,4,5,6],[2446,0,390,1,2,3,4,5,6],[2137,0,390,35,1,2,3,4,5,6],[4078,0,35,2,3,128,4,5,6],[2098,0,35,2,7,3,128,4,5,6],[2098,0,129,35,1,2,3,4,5,6],[2197,0,35,1,2,3,4,5,6,175],[403,0,35,1,2,7,3,4,5,6,175],[2095,0,35,1,176,2,3,4,5,6],[2272,0,35,1,2,3,218,4,5,6],[424,0,35,1,2,7,3,218,4,5,6],[2107,0,35,1,2,219,3,4,5,6],[3829,0,35,1,2,3,4,258,5,6],[2128,0,35,1,2,259,3,4,5,6],[2248,0,35,1,2,3,4,5,296,6],[415,0,35,1,2,7,3,4,5,296,6],[2104,0,35,1,2,297,3,4,5,6],[2134,0,35,1,2,334,3,4,5,6],[4138,0,1,526,2,3,4,5,6],[3841,0,1,66,526,2,3,4,5,6],[5197,525,0,1,2,3,4,5,6],[5860,647,0,1,2,3,4,5,6],[4240,0,1,2,668,3,4,5,6],[3967,0,1,66,2,668,3,4,5,6],[5134,0,1,570,2,3,4,5,6],[4327,0,1,2,3,689,4,5,6],[4018,0,1,66,2,3,689,4,5,6],[5155,0,1,585,2,3,4,5,6],[5881,0,1,2,3,4,710,5,6],[5839,0,1,66,2,3,4,710,5,6],[5902,0,1,600,2,3,4,5,6],[4273,0,1,2,3,4,5,731,6],[3985,0,1,66,2,3,4,5,731,6],[5131,0,1,615,2,3,4,5,6],[5908,0,1,752,2,3,4,5,6],[3841,0,35,1,526,2,3,4,5,6],[5911,647,0,35,2,3,4,5,6],[3967,0,35,1,2,668,3,4,5,6],[4018,0,35,1,2,3,689,4,5,6],[5839,0,35,1,2,3,4,710,5,6],[3985,0,35,1,2,3,4,5,731,6],[5911,0,35,1,752,2,3,4,5],[2197,0,78,35,1,2,3,4,5,6],[4240,0,444,1,2,3,4,5,6],[3967,0,35,444,1,2,3,4,5,6],[3082,0,35,1,2,3,221,4,5,6],[3919,0,35,1,2,3,4,261,5,6],[3067,0,35,1,2,3,4,5,299,6],[4237,0,35,1,2,3,4,5,336],[2272,0,79,35,1,2,3,4,5,6],[4327,0,1,459,2,3,4,5,6],[4018,0,35,1,459,2,3,4,5,6],[4309,0,35,131,2,3,4,5,6],[3082,0,35,1,2,178,3,4,5,6],[3976,0,35,1,2,3,4,5,262,6],[3103,0,35,1,2,3,4,5,300,6],[3829,0,80,35,1,2,3,4,5,6],[5881,0,474,1,2,3,4,5,6]],
  #[[5839,0,35,474,1,2,3,4,5,6],[5848,0,35,132,2,3,4,5,6],[3919,0,35,1,2,179,3,4,5,6],[3976,0,35,1,2,3,222,4,5,6],[3940,0,35,1,2,3,4,5,301,6],[5878,0,35,1,2,3,4,5,338],[2248,0,81,35,1,2,3,4,5,6],[4273,0,1,489,2,3,4,5,6],[3985,0,35,1,489,2,3,4,5,6],[3067,0,35,1,2,180,3,4,5,6],[3103,0,35,1,2,3,223,4,5,6],[3940,0,35,1,2,3,4,263,5,6],[5034,0,1,37,4,5,6,36],[1512,0,1,2,3,4,5,50,6,36],[3519,0,1,2,3,51,4,5,6,36],[4662,0,1,2,3,4,5,6,36,52],[4677,0,1,2,3,53,4,5,6,36],[1530,0,1,2,3,4,5,6,54,36],[3552,0,1,2,3,4,55,5,6,36],[5036,98,1,2,3,4,5,6],[3716,98,0,1,2,3,4,5,6],[5036,0,145,2,3,4,5,6],[4883,0,145,1,2,3,4,5,6],[5036,0,1,2,3,283,5,6],[4934,0,1,2,3,283,4,5,6],[5036,0,1,2,3,4,321,6],[3734,0,1,2,3,4,321,5,6],[5036,0,1,2,3,4,5,358],[4958,0,1,2,3,4,5,358,6],[1159,0,1,2,3,128,4,5,6,36],[1375,0,1,2,3,4,258,5,6,36],[268,0,1,2,3,4,5,296,6,36],[1393,0,1,2,3,4,5,6,333,36],[1402,0,1,2,391,3,4,5,6],[1159,0,1,77,2,3,4,5,6,36],[4183,0,1,2,3,4,260,5,6,36],[1471,0,1,2,3,4,5,298,6,36],[4195,0,1,2,3,4,5,6,335,36],[1375,0,80,1,2,3,4,5,6,36],[4183,0,1,132,2,3,4,5,6,36],[1498,0,1,2,3,4,5,301,6,36],[4336,0,1,2,3,4,5,6,338,36],[268,0,81,1,2,3,4,5,6,36],[1471,0,1,133,2,3,4,5,6,36],[1498,0,1,2,3,4,263,5,6,36],[1528,0,1,2,3,4,5,6,339,36],[1393,0,82,1,2,3,4,5,6,36],[4195,0,1,134,2,3,4,5,6,36],[4336,0,1,2,3,4,264,5,6,36],[1528,0,1,2,3,4,5,302,6,36],[3582,0,1,37,39,2,3,4,5,6],[3747,0,1,37,41,3,4,5,6],[2025,0,1,37,41,2,3,4,5,6],[5007,0,1,37,43,3,4,5,6],[3645,0,1,37,43,2,3,4,5,6],[3651,0,1,37,2,45,3,4,5,6],[3747,0,1,37,2,47,4,5,6],[2052,0,1,37,2,47,3,4,5,6],[3687,0,1,37,2,49,3,4,5,6],[1590,0,1,37,2,3,4,5,50,6],[3600,0,1,37,2,3,51,4,5,6],[4683,0,1,37,2,3,4,5,6,52],[4704,0,1,37,2,3,53,4,5,6],[1602,0,1,37,2,3,4,5,6,54]],
  #[[3654,0,1,37,2,3,4,55,5,6],[3293,0,1,2,99,3,4,5,6],[1667,0,1,37,2,99,3,4,5,6],[1931,100,0,1,37,2,3,4,5,6],[3176,0,1,2,3,146,4,5,6],[1613,0,1,37,2,3,146,4,5,6],[3497,0,147,1,37,2,3,4,5,6],[3173,0,1,2,3,4,284,5,6],[1610,0,1,37,2,3,4,284,5,6],[4970,0,1,202,2,3,4,5,6],[3659,0,1,202,37,2,3,4,5,6],[3737,0,1,2,3,4,5,6,322],[2030,0,1,37,2,3,4,5,6,322],[3749,0,1,205,2,3,4,5,6],[2063,0,1,205,37,2,3,4,5,6],[3281,0,1,2,3,4,5,6,359],[1661,0,1,37,2,3,4,5,6,359],[5009,0,1,208,2,3,4,5,6],[3692,0,1,208,37,2,3,4,5,6],[1183,0,1,37,2,3,128,4,5,6],[55,0,1,37,2,7,3,128,4,5,6],[166,0,129,1,37,2,3,4,5,6],[1708,0,1,2,392,3,4,5,6],[187,0,1,2,7,392,3,4,5,6],[289,0,1,37,2,392,3,4,5,6],[1420,0,1,393,2,3,4,5,6],[187,0,1,393,37,2,3,4,5,6],[1696,0,1,37,3,4,5,6,175],[163,0,1,37,7,3,4,5,6,175],[163,0,1,176,37,2,3,4,5,6],[184,0,1,37,2,219,3,4,5,6],[1384,0,1,37,2,3,4,258,5,6],[133,0,1,37,2,7,3,4,258,5,6],[202,0,1,37,2,259,3,4,5,6],[280,0,1,37,2,3,4,5,296,6],[178,0,1,37,2,297,3,4,5,6],[1414,0,1,37,2,3,4,5,6,333],[142,0,1,37,2,7,3,4,5,6,333],[208,0,1,37,2,334,3,4,5,6],[1183,0,1,77,37,2,3,4,5,6],[3091,0,1,426,2,3,4,5,6],[1492,0,1,37,426,2,3,4,5,6],[3085,0,1,37,2,220,4,5,6],[4198,0,1,37,2,3,4,260,5,6],[1483,0,1,37,2,3,4,5,298,6],[4210,0,1,37,2,3,4,5,6,335],[1708,0,528,1,2,3,4,5,6],[289,0,67,528,1,2,3,4,5,6],[1855,527,0,1,2,3,4,5,6],[3091,0,1,648,2,3,4,5,6],[1492,0,67,1,648,2,3,4,5,6],[1840,0,552,1,2,3,4,5,6],[2047,669,0,1,2,3,4,5,6],[2068,0,690,1,2,3,4,5,6],[3172,0,1,2,3,4,5,711,6],[1609,0,67,1,2,3,4,5,711,6],[1837,0,601,1,2,3,4,5,6],[2035,0,1,2,3,4,5,732,6],[370,0,67,1,2,3,4,5,732,6],[2059,0,616,1,2,3,4,5,6],[3280,0,1,2,3,4,5,6,753],[1660,0,67,1,2,3,4,5,6,753],[1849,0,631,1,2,3,4,5,6],[289,0,528,1,37,2,3,4,5,6]],
  #[[1492,0,1,648,37,2,3,4,5,6],[2071,669,0,1,37,3,4,5,6],[2071,0,690,1,37,2,4,5,6],[1609,0,1,37,2,3,4,5,711,6],[370,0,1,37,2,3,4,5,732,6],[1660,0,1,37,2,3,4,5,6,753],[1384,0,80,1,37,2,3,4,5,6],[4198,0,1,132,37,2,3,4,5,6],[3172,0,1,475,2,3,4,5,6],[1609,0,1,37,475,2,3,4,5,6],[1540,0,1,37,2,3,4,5,301,6],[4345,0,1,37,2,3,4,5,6,338],[280,0,81,1,37,2,3,4,5,6],[1483,0,1,133,37,2,3,4,5,6],[2035,0,1,490,2,3,4,5,6],[370,0,1,37,490,2,3,4,5,6],[2017,0,1,37,180,3,4,5,6],[2032,0,1,37,2,223,4,5,6],[1540,0,1,37,2,3,4,263,5,6],[1600,0,1,37,2,3,4,5,6,339],[1414,0,82,1,37,2,3,4,5,6],[4210,0,1,134,37,2,3,4,5,6],[3280,0,1,505,2,3,4,5,6],[1660,0,1,37,505,2,3,4,5,6],[3235,0,1,37,181,3,4,5,6],[4345,0,1,37,2,3,4,264,5,6],[1600,0,1,37,2,3,4,5,302,6],[4737,0,1,39,3,5,6,38],[1575,0,1,2,3,4,5,6,38,46],[1626,0,1,2,47,3,4,5,6,38],[780,0,1,2,3,4,5,6,38,48],[2775,0,1,2,49,3,4,5,6,38],[693,0,1,2,3,4,5,6,54,38],[2721,0,1,2,3,4,55,5,6,38],[2885,101,0,1,2,3,4,5,6],[4286,0,148,1,2,3,4,5,6],[3260,0,1,2,243,3,4,5,6],[3215,0,1,2,3,4,323,5,6],[4427,0,1,2,3,4,5,360,6],[382,0,1,2,3,128,4,5,6,38],[82,0,1,2,3,218,4,5,6,38],[43,0,1,2,3,4,5,296,6,38],[475,0,1,2,3,4,5,6,333,38],[1006,0,1,2,394,3,4,5,6],[382,0,1,77,2,3,4,5,6,38],[541,0,1,2,3,220,4,5,6,38],[523,0,1,2,3,4,5,298,6,38],[3772,0,1,2,3,4,5,6,335,38],[82,0,79,1,2,3,4,5,6,38],[541,0,1,131,2,3,4,5,6,38],[253,0,1,2,3,4,5,300,6,38],[778,0,1,2,3,4,5,6,337,38],[43,0,81,1,2,3,4,5,6,38],[523,0,1,133,2,3,4,5,6,38],[253,0,1,2,3,223,4,5,6,38],[691,0,1,2,3,4,5,6,38,339],[475,0,82,1,2,3,4,5,6,38],[3772,0,1,134,2,3,4,5,6,38],[778,0,1,2,3,224,4,5,6,38],[691,0,1,2,3,4,5,302,6,38],[3531,0,1,39,41,2,3,4,5,6],[5760,0,1,39,43,3,4,5,6],[4680,0,1,39,43,2,3,4,5,6],[4968,0,1,39,2,45,3,5,6]],
  #[[4686,0,1,39,2,45,3,4,5,6],[3534,0,1,39,2,3,4,5,6,46],[3600,0,1,39,2,47,3,4,5,6],[2754,0,1,39,2,3,4,5,6,48],[4704,0,1,39,2,49,3,4,5,6],[4938,0,1,39,2,3,51,5,6],[4668,0,1,39,2,3,51,4,5,6],[5520,0,1,39,2,3,53,4,5,6],[2619,0,1,39,2,3,4,5,6,54],[4689,0,1,39,2,3,4,55,5,6],[2948,0,1,2,102,3,4,5,6],[2936,0,1,39,2,102,3,4,5,6],[4781,103,0,1,39,2,3,4,5,6],[5408,0,1,2,3,4,5,6,149],[5324,0,1,39,2,3,4,5,6,149],[5675,0,150,1,39,2,3,4,5,6],[3563,0,1,2,3,4,244,5,6],[3518,0,1,39,2,3,4,244,5,6],[4937,0,1,202,39,2,3,4,5,6],[3557,0,1,2,3,4,5,324,6],[3515,0,1,39,2,3,4,5,324,6],[4940,0,1,211,2,3,4,5,6],[4916,0,1,211,39,2,3,4,5,6],[5546,0,1,2,3,4,5,6,361],[5507,0,1,39,2,3,4,5,6,361],[5762,0,1,214,2,3,4,5,6],[5744,0,1,214,39,2,3,4,5,6],[2176,0,1,39,2,3,128,4,5,6],[394,0,1,39,2,7,3,128,4,5,6],[916,0,129,1,39,2,3,4,5,6],[2947,0,1,2,3,395,4,5,6],[1075,0,1,2,7,3,395,4,5,6],[2935,0,1,39,2,3,395,4,5,6],[1066,0,1,39,2,7,3,395,4,5,6],[1099,0,1,396,2,3,4,5,6],[1075,0,1,396,39,2,3,4,5,6],[2821,0,1,39,3,4,5,6,175],[913,0,1,39,7,3,4,5,6,175],[913,0,1,176,39,2,3,4,5,6],[1327,0,1,39,2,3,218,4,5,6],[115,0,1,39,2,7,3,218,4,5,6],[1009,0,1,39,2,219,3,4,5,6],[1072,0,1,39,2,259,3,4,5,6],[1219,0,1,39,2,3,4,5,296,6],[97,0,1,39,2,7,3,4,5,296,6],[931,0,1,39,2,297,3,4,5,6],[2428,0,1,39,2,3,4,5,6,333],[496,0,1,39,2,7,3,4,5,6,333],[1084,0,1,39,2,334,3,4,5,6],[2176,0,1,77,39,2,3,4,5,6],[5326,0,1,427,2,3,4,5,6],[5308,0,1,39,427,2,3,4,5,6],[4219,0,1,39,177,3,4,5,6],[2494,0,1,39,2,3,220,4,5,6],[5317,0,1,39,2,3,260,5,6],[2473,0,1,39,2,3,4,5,298,6],[5083,0,1,39,2,3,4,5,6,335],[2947,0,530,1,2,3,4,5,6],[2935,0,68,530,1,2,3,4,5,6],[4774,529,0,1,2,3,4,5,6],[5326,0,1,649,2,3,4,5,6],[5308,0,68,1,649,2,3,4,5,6],[5671,0,553,1,2,3,4,5,6],[4912,670,0,1,2,3,4,5,6]],
  #[[3562,0,1,2,3,691,4,5,6],[3517,0,68,1,2,3,691,4,5,6],[4909,0,586,1,2,3,4,5,6],[5731,0,712,1,2,3,4,5,6],[3523,0,1,2,3,4,5,733,6],[3505,0,68,1,2,3,4,5,733,6],[4906,0,617,1,2,3,4,5,6],[5524,0,1,2,3,4,5,6,754],[5503,0,68,1,2,3,4,5,6,754],[5734,0,632,1,2,3,4,5,6],[2935,0,530,1,39,2,3,4,5,6],[5308,0,1,649,39,2,3,4,5,6],[5815,670,0,1,39,3,4,5,6],[3517,0,1,39,2,3,691,4,5,6],[5815,0,712,1,39,2,3,5,6],[3505,0,1,39,2,3,4,5,733,6],[5503,0,1,39,2,3,4,5,6,754],[1327,0,79,1,39,2,3,4,5,6],[2494,0,1,131,39,2,3,4,5,6],[3562,0,1,460,2,3,4,5,6],[3517,0,1,39,460,2,3,4,5,6],[3145,0,1,39,2,3,5,262,6],[1813,0,1,39,2,3,4,5,300,6],[2752,0,1,39,2,3,4,5,6,337],[1219,0,81,1,39,2,3,4,5,6],[2473,0,1,133,39,2,3,4,5,6],[3523,0,1,491,2,3,4,5,6],[3505,0,1,39,491,2,3,4,5,6],[1813,0,1,39,2,3,223,4,5,6],[3115,0,1,39,2,3,263,5,6],[2617,0,1,39,2,3,4,5,6,339],[2428,0,82,1,39,2,3,4,5,6],[5083,0,1,134,39,2,3,4,5,6],[5524,0,1,506,2,3,4,5,6],[5503,0,1,39,506,2,3,4,5,6],[4351,0,1,39,181,3,4,5,6],[2752,0,1,39,2,3,224,4,5,6],[2617,0,1,39,2,3,4,5,302,6],[5031,0,1,41,3,4,6,40],[4953,0,1,43,3,4,5,6,40],[1521,0,1,2,3,4,44,5,6,40],[3549,0,1,2,45,3,4,5,6,40],[1644,0,1,2,3,4,5,6,48,40],[3633,0,1,2,49,3,4,5,6,40],[4659,0,1,2,3,4,5,6,40,52],[4674,0,1,2,3,53,4,5,6,40],[4953,0,1,2,3,4,55,6,40],[5033,104,1,2,3,4,5,6],[3713,104,0,1,2,3,4,5,6],[5033,0,151,2,3,4,5,6],[4880,0,151,1,2,3,4,5,6],[5033,0,1,2,245,4,5,6],[3746,0,1,2,245,3,4,5,6],[5033,0,1,2,3,285,5,6],[4931,0,1,2,3,285,4,5,6],[5033,0,1,2,3,4,5,362],[4955,0,1,2,3,4,5,362,6],[1156,0,1,2,3,128,4,5,6,40],[283,0,1,2,3,218,4,5,6,40],[1372,0,1,2,3,4,258,5,6,40],[1390,0,1,2,3,4,5,6,333,40],[1399,0,1,2,397,3,4,5,6],[1156,0,1,77,2,3,4,5,6,40],[1480,0,1,2,3,220,4,5,6,40]],
  #[[4180,0,1,2,3,4,260,5,6,40],[4192,0,1,2,3,4,5,6,335,40],[283,0,79,1,2,3,4,5,6,40],[1480,0,1,131,2,3,4,5,6,40],[1519,0,1,2,3,4,5,262,6,40],[1642,0,1,2,3,4,5,6,337,40],[1372,0,80,1,2,3,4,5,6,40],[4180,0,1,132,2,3,4,5,6,40],[1519,0,1,2,3,222,4,5,6,40],[4333,0,1,2,3,4,5,6,338,40],[1390,0,82,1,2,3,4,5,6,40],[4192,0,1,134,2,3,4,5,6,40],[1642,0,1,2,3,224,4,5,6,40],[4333,0,1,2,3,4,264,5,6,40],[3594,0,1,41,43,2,3,4,5,6],[1545,0,1,41,2,3,4,44,5,6],[3600,0,1,41,2,45,3,4,5,6],[3747,0,1,41,2,47,3,4,6],[2040,0,1,41,2,47,3,4,5,6],[1650,0,1,41,2,3,4,5,6,48],[3654,0,1,41,2,49,3,4,5,6],[3537,0,1,41,2,3,51,4,5,6],[4665,0,1,41,2,3,4,5,6,52],[4689,0,1,41,2,3,53,4,5,6],[3606,0,1,41,2,3,4,55,5,6],[3224,0,1,2,105,3,4,5,6],[1586,0,1,41,2,105,3,4,5,6],[1889,106,0,1,41,2,3,4,5,6],[3167,0,1,2,3,4,5,152,6],[1562,0,1,41,2,3,4,5,152,6],[3455,0,153,1,41,2,3,4,5,6],[3740,0,1,2,3,4,5,6,246],[2003,0,1,41,2,3,4,5,6,246],[2045,0,1,205,41,2,3,4,5,6],[3161,0,1,2,3,4,5,286,6],[1559,0,1,41,2,3,4,5,286,6],[3542,0,1,211,41,2,3,4,5,6],[3182,0,1,2,3,4,5,6,363],[1565,0,1,41,2,3,4,5,6,363],[4979,0,1,217,2,3,4,5,6],[3611,0,1,217,41,2,3,4,5,6],[1165,0,1,41,2,3,128,4,5,6],[31,0,1,41,2,7,3,128,4,5,6],[154,0,129,1,41,2,3,4,5,6],[1690,0,1,2,3,4,398,5,6],[160,0,1,2,7,3,4,398,5,6],[274,0,1,41,2,3,4,398,5,6],[1408,0,1,399,2,3,4,5,6],[160,0,1,399,41,2,3,4,5,6],[1681,0,1,41,3,4,5,6,175],[151,0,1,41,7,3,4,5,6,175],[151,0,1,176,41,2,3,4,5,6],[286,0,1,41,2,3,218,4,5,6],[175,0,1,41,2,219,3,4,5,6],[1378,0,1,41,2,3,4,258,5,6],[130,0,1,41,2,7,3,4,258,5,6],[196,0,1,41,2,259,3,4,5,6],[157,0,1,41,2,297,3,4,5,6],[1396,0,1,41,2,3,4,5,6,333],[139,0,1,41,2,7,3,4,5,6,333],[199,0,1,41,2,334,3,4,5,6],[1165,0,1,77,41,2,3,4,5,6],[3076,0,1,428,2,3,4,5,6],[1477,0,1,41,428,2,3,4,5,6]],
  #[[1486,0,1,41,2,3,220,4,5,6],[4186,0,1,41,2,3,4,260,5,6],[3070,0,1,41,2,3,4,298,6],[4201,0,1,41,2,3,4,5,6,335],[1690,0,532,1,2,3,4,5,6],[274,0,69,532,1,2,3,4,5,6],[1825,531,0,1,2,3,4,5,6],[3076,0,1,650,2,3,4,5,6],[1477,0,69,1,650,2,3,4,5,6],[1819,0,554,1,2,3,4,5,6],[1999,671,0,1,2,3,4,5,6],[2038,0,1,2,3,692,4,5,6],[364,0,69,1,2,3,692,4,5,6],[2005,0,587,1,2,3,4,5,6],[3121,0,1,2,3,4,713,5,6],[1504,0,69,1,2,3,4,713,5,6],[1816,0,602,1,2,3,4,5,6],[2008,0,734,1,2,3,4,5,6],[3181,0,1,2,3,4,5,6,755],[1564,0,69,1,2,3,4,5,6,755],[1822,0,633,1,2,3,4,5,6],[274,0,532,1,41,2,3,4,5,6],[1477,0,1,650,41,2,3,4,5,6],[2011,671,0,1,41,3,4,5,6],[364,0,1,41,2,3,692,4,5,6],[1504,0,1,41,2,3,4,713,5,6],[2011,0,734,1,41,2,3,4,6],[1564,0,1,41,2,3,4,5,6,755],[286,0,79,1,41,2,3,4,5,6],[1486,0,1,131,41,2,3,4,5,6],[2038,0,1,461,2,3,4,5,6],[364,0,1,41,461,2,3,4,5,6],[2020,0,1,41,178,3,4,5,6],[1543,0,1,41,2,3,4,5,262,6],[2032,0,1,41,2,3,4,300,6],[1648,0,1,41,2,3,4,5,6,337],[1378,0,80,1,41,2,3,4,5,6],[4186,0,1,132,41,2,3,4,5,6],[3121,0,1,476,2,3,4,5,6],[1504,0,1,41,476,2,3,4,5,6],[1543,0,1,41,2,3,222,4,5,6],[4339,0,1,41,2,3,4,5,6,338],[1396,0,82,1,41,2,3,4,5,6],[4201,0,1,134,41,2,3,4,5,6],[3181,0,1,507,2,3,4,5,6],[1564,0,1,41,507,2,3,4,5,6],[1648,0,1,41,2,3,224,4,5,6],[4339,0,1,41,2,3,4,264,5,6],[4743,0,1,43,3,4,5,42],[711,0,1,2,3,4,44,5,6,42],[2727,0,1,2,45,3,4,5,6,42],[1581,0,1,2,3,4,5,6,42,46],[1632,0,1,2,47,3,4,5,6,42],[696,0,1,2,3,4,5,50,6,42],[2640,0,1,2,3,51,4,5,6,42],[2891,107,0,1,2,3,4,5,6],[4292,0,154,1,2,3,4,5,6],[3266,0,1,2,247,3,4,5,6],[4394,0,1,2,3,287,4,5,6],[3221,0,1,2,3,4,325,5,6],[385,0,1,2,3,128,4,5,6,42],[88,0,1,2,3,218,4,5,6,42],[442,0,1,2,3,4,258,5,6,42],[49,0,1,2,3,4,5,296,6,42]],
  #[[1018,0,1,2,400,3,4,5,6],[385,0,1,77,2,3,4,5,6,42],[544,0,1,2,3,220,4,5,6,42],[3757,0,1,2,3,4,260,5,6,42],[526,0,1,2,3,4,5,298,6,42],[88,0,79,1,2,3,4,5,6,42],[544,0,1,131,2,3,4,5,6,42],[709,0,1,2,3,4,5,262,6,42],[259,0,1,2,3,4,5,300,6,42],[442,0,80,1,2,3,4,5,6,42],[3757,0,1,132,2,3,4,5,6,42],[709,0,1,2,3,222,4,5,6,42],[586,0,1,2,3,4,5,301,6,42],[49,0,81,1,2,3,4,5,6,42],[526,0,1,133,2,3,4,5,6,42],[259,0,1,2,3,223,4,5,6,42],[586,0,1,2,3,4,263,5,6,42],[2658,0,1,43,2,3,4,44,5,6],[4704,0,1,43,2,45,3,4,5,6],[3603,0,1,43,2,3,4,5,6,46],[3654,0,1,43,2,47,3,4,5,6],[5007,0,1,43,2,49,3,4,5],[4752,0,1,43,2,49,3,4,5,6],[2649,0,1,43,2,3,4,5,50,6],[4689,0,1,43,2,3,51,4,5,6],[5547,0,1,43,2,3,53,4,5,6],[4977,0,1,43,2,3,4,55,5],[4707,0,1,43,2,3,4,55,5,6],[2990,0,1,2,108,3,4,5,6],[2984,0,1,43,2,108,3,4,5,6],[4796,109,0,1,43,2,3,4,5,6],[5411,0,1,2,3,4,5,6,155],[5357,0,1,43,2,3,4,5,6,155],[5693,0,156,1,43,2,3,4,5,6],[3686,0,1,2,3,4,5,6,248],[3683,0,1,43,2,3,4,5,6,248],[5000,0,1,208,43,2,3,4,5,6],[5543,0,1,2,3,4,5,6,288],[5516,0,1,43,2,3,4,5,6,288],[5759,0,1,214,43,2,3,4,5,6],[3569,0,1,2,3,4,5,6,326],[3548,0,1,43,2,3,4,5,6,326],[4961,0,1,217,43,2,3,4,5,6],[2200,0,1,43,2,3,128,4,5,6],[406,0,1,43,2,7,3,128,4,5,6],[970,0,129,1,43,2,3,4,5,6],[2989,0,1,2,3,4,5,401,6],[1111,0,1,2,7,3,4,5,401,6],[2983,0,1,43,2,3,4,5,401,6],[1105,0,1,43,2,7,3,4,5,401,6],[1123,0,1,402,2,3,4,5,6],[1111,0,1,402,43,2,3,4,5,6],[2845,0,1,43,3,4,5,6,175],[967,0,1,43,7,3,4,5,6,175],[967,0,1,176,43,2,3,4,5,6],[1360,0,1,43,2,3,218,4,5,6],[124,0,1,43,2,7,3,218,4,5,6],[1045,0,1,43,2,219,3,4,5,6],[2419,0,1,43,2,3,4,258,5,6],[490,0,1,43,2,7,3,4,258,5,6],[1087,0,1,43,2,259,3,4,5,6],[1282,0,1,43,2,3,4,5,296,6],[106,0,1,43,2,7,3,4,5,296,6],[1021,0,1,43,2,297,3,4,5,6]],
  #[[1108,0,1,43,2,334,3,4,5,6],[2200,0,1,77,43,2,3,4,5,6],[5359,0,1,429,2,3,4,5,6],[5347,0,1,43,429,2,3,4,5,6],[4234,0,1,43,177,3,4,5,6],[2548,0,1,43,2,3,220,4,5,6],[5080,0,1,43,2,3,4,260,5,6],[2497,0,1,43,2,3,4,5,298,6],[5353,0,1,43,2,3,4,5,335],[2989,0,534,1,2,3,4,5,6],[2983,0,70,534,1,2,3,4,5,6],[4792,533,0,1,2,3,4,5,6],[5359,0,1,651,2,3,4,5,6],[5347,0,70,1,651,2,3,4,5,6],[5689,0,555,1,2,3,4,5,6],[4951,672,0,1,2,3,4,5,6],[3685,0,1,2,3,693,4,5,6],[3682,0,70,1,2,3,693,4,5,6],[4996,0,588,1,2,3,4,5,6],[5518,0,1,2,3,4,714,5,6],[5512,0,70,1,2,3,4,714,5,6],[5755,0,603,1,2,3,4,5,6],[3568,0,1,2,3,4,5,735,6],[3547,0,70,1,2,3,4,5,735,6],[4948,0,618,1,2,3,4,5,6],[5779,0,756,1,2,3,4,5,6],[2983,0,534,1,43,2,3,4,5,6],[5347,0,1,651,43,2,3,4,5,6],[5821,672,0,1,43,3,4,5,6],[3682,0,1,43,2,3,693,4,5,6],[5512,0,1,43,2,3,4,714,5,6],[3547,0,1,43,2,3,4,5,735,6],[5821,0,756,1,43,2,3,4,5],[1360,0,79,1,43,2,3,4,5,6],[2548,0,1,131,43,2,3,4,5,6],[3685,0,1,462,2,3,4,5,6],[3682,0,1,43,462,2,3,4,5,6],[3637,0,1,43,178,3,4,5,6],[2656,0,1,43,2,3,4,5,262,6],[1834,0,1,43,2,3,4,5,300,6],[3274,0,1,43,2,3,4,5,337],[2419,0,80,1,43,2,3,4,5,6],[5080,0,1,132,43,2,3,4,5,6],[5518,0,1,477,2,3,4,5,6],[5512,0,1,43,477,2,3,4,5,6],[4348,0,1,43,179,3,4,5,6],[2656,0,1,43,2,3,222,4,5,6],[2614,0,1,43,2,3,4,5,301,6],[1282,0,81,1,43,2,3,4,5,6],[2497,0,1,133,43,2,3,4,5,6],[3568,0,1,492,2,3,4,5,6],[3547,0,1,43,492,2,3,4,5,6],[1834,0,1,43,2,3,223,4,5,6],[2614,0,1,43,2,3,4,263,5,6],[3154,0,1,43,2,3,4,5,339],[4722,0,1,2,45,44,5,6],[657,0,1,2,3,4,44,5,6,54],[2691,0,1,2,3,4,44,55,5,6],[2870,110,0,1,2,3,4,5,6],[4256,0,157,1,2,3,4,5,6],[3149,0,1,200,2,3,4,5,6],[3197,0,1,2,3,327,4,5,6],[4418,0,1,2,3,4,364,5,6],[376,0,1,2,3,128,4,44,5,6]],
  #[[19,0,1,2,3,4,44,5,6,175],[982,0,1,2,403,3,4,5,6],[34,0,1,2,3,4,44,5,296,6],[463,0,1,2,3,4,44,5,6,333],[376,0,1,77,2,3,4,44,5,6],[511,0,1,2,177,3,4,44,5,6],[520,0,1,2,3,4,44,5,298,6],[3769,0,1,2,3,4,44,5,6,335],[19,0,78,1,2,3,4,44,5,6],[511,0,1,130,2,3,4,44,5,6],[226,0,1,2,3,4,44,5,299,6],[601,0,1,2,3,4,44,5,6,336],[34,0,81,1,2,3,4,44,5,6],[520,0,1,133,2,3,4,44,5,6],[226,0,1,2,180,3,4,44,5,6],[655,0,1,2,3,4,44,5,6,339],[463,0,82,1,2,3,4,44,5,6],[3769,0,1,134,2,3,4,44,5,6],[601,0,1,2,181,3,4,44,5,6],[655,0,1,2,3,4,44,5,302,6],[3660,0,1,2,47,45,3,4,5,6],[5793,0,1,2,45,49,4,5,6],[4755,0,1,2,45,49,3,4,5,6],[4986,0,1,2,45,3,51,5,6],[4695,0,1,2,45,3,51,4,5,6],[5793,0,1,2,45,3,53,5,6],[5562,0,1,2,45,3,53,4,5,6],[2700,0,1,2,45,3,4,5,6,54],[4728,0,1,2,45,3,4,55,5,6],[3008,0,1,2,3,4,5,6,111],[3005,0,1,2,45,3,4,5,6,111],[4805,112,0,1,2,45,3,4,5,6],[5384,0,1,2,3,158,4,5,6],[5381,0,1,2,45,3,158,4,5,6],[5702,0,159,1,2,45,3,4,5,6],[3581,0,1,2,3,4,5,6,201],[3578,0,1,2,45,3,4,5,6,201],[4967,0,1,202,2,45,3,4,5,6],[3620,0,1,2,3,4,5,328,6],[3617,0,1,2,45,3,4,5,328,6],[4988,0,1,2,251,3,4,5,6],[4985,0,1,2,251,45,3,4,5,6],[5582,0,1,2,3,4,5,6,365],[5579,0,1,2,45,3,4,5,6,365],[5795,0,1,2,254,3,4,5,6],[5786,0,1,2,254,45,3,4,5,6],[2215,0,1,2,45,3,128,4,5,6],[409,0,1,2,7,45,3,128,4,5,6],[988,0,129,1,2,45,3,4,5,6],[1231,0,1,2,45,3,4,5,6,175],[100,0,1,2,7,45,3,4,5,6,175],[985,0,1,176,2,45,3,4,5,6],[3007,0,1,2,404,3,4,5,6],[1129,0,1,2,7,404,3,4,5,6],[3004,0,1,2,45,404,3,4,5,6],[1126,0,1,2,7,45,404,3,4,5,6],[1132,0,1,2,405,3,4,5,6],[1129,0,1,2,405,45,3,4,5,6],[2908,0,1,2,45,218,4,5,6],[1048,0,1,2,7,45,218,4,5,6],[1048,0,1,2,219,45,3,4,5,6],[2971,0,1,2,45,3,258,5,6],[1093,0,1,2,7,45,3,258,5,6],[1093,0,1,2,259,45,3,4,5,6]],
  #[[1294,0,1,2,45,3,4,5,296,6],[109,0,1,2,7,45,3,4,5,296,6],[1030,0,1,2,297,45,3,4,5,6],[2443,0,1,2,45,3,4,5,6,333],[505,0,1,2,7,45,3,4,5,6,333],[1114,0,1,2,334,45,3,4,5,6],[2215,0,1,77,2,45,3,4,5,6],[2509,0,1,2,177,45,3,4,5,6],[5383,0,1,2,3,430,4,5,6],[5380,0,1,2,45,3,430,4,5,6],[4258,0,1,2,45,220,4,5,6],[2524,0,1,2,45,3,4,5,298,6],[5095,0,1,2,45,3,4,5,6,335],[1231,0,78,1,2,45,3,4,5,6],[2509,0,1,130,2,45,3,4,5,6],[3580,0,1,2,445,3,4,5,6],[3577,0,1,2,45,445,3,4,5,6],[3169,0,1,2,45,3,261,5,6],[1807,0,1,2,45,3,4,5,299,6],[2668,0,1,2,45,3,4,5,6,336],[3007,0,536,1,2,3,4,5,6],[3004,71,0,536,1,2,3,4,5,6],[4801,535,0,1,2,3,4,5,6],[5383,0,1,652,2,3,4,5,6],[5380,71,0,1,652,2,3,4,5,6],[5698,556,0,1,2,3,4,5,6],[3580,0,1,2,673,3,4,5,6],[3577,71,0,1,2,673,3,4,5,6],[4963,571,0,1,2,3,4,5,6],[5011,694,0,1,2,3,4,5,6],[5767,715,0,1,2,3,4,5,6],[3619,0,1,2,3,4,5,736,6],[3616,71,0,1,2,3,4,5,736,6],[4981,619,0,1,2,3,4,5,6],[5581,0,1,2,3,4,5,6,757],[5578,71,0,1,2,3,4,5,6,757],[5782,634,0,1,2,3,4,5,6],[3004,0,536,1,2,45,3,4,5,6],[5380,0,1,652,2,45,3,4,5,6],[3577,0,1,2,673,45,3,4,5,6],[5824,694,0,1,2,45,4,5,6],[5824,715,0,1,2,45,3,5,6],[3616,0,1,2,45,3,4,5,736,6],[5578,0,1,2,45,3,4,5,6,757],[1294,0,81,1,2,45,3,4,5,6],[2524,0,1,133,2,45,3,4,5,6],[1807,0,1,2,180,45,3,4,5,6],[3619,0,1,2,493,3,4,5,6],[3616,0,1,2,45,493,3,4,5,6],[3190,0,1,2,45,3,263,5,6],[2698,0,1,2,45,3,4,5,6,339],[2443,0,82,1,2,45,3,4,5,6],[5095,0,1,134,2,45,3,4,5,6],[2668,0,1,2,181,45,3,4,5,6],[5581,0,1,2,508,3,4,5,6],[5578,0,1,2,45,508,3,4,5,6],[4447,0,1,2,45,224,4,5,6],[5554,0,1,2,45,3,264,5,6],[2698,0,1,2,45,3,4,5,302,6],[5037,0,1,2,47,4,6,46],[4671,0,1,2,3,4,5,6,46,52],[4698,0,1,2,3,53,4,5,6,46],[5039,113,1,2,3,4,5,6],[3722,113,0,1,2,3,4,5,6]],
  #[[5039,0,160,2,3,4,5,6],[4889,0,160,1,2,3,4,5,6],[5039,0,1,203,3,4,5,6],[3743,0,1,203,2,3,4,5,6],[5039,0,1,2,3,289,5,6],[4943,0,1,2,3,289,4,5,6],[5039,0,1,2,3,4,5,366],[4991,0,1,2,3,4,5,366,6],[1174,0,1,2,3,128,4,5,6,46],[271,0,1,2,3,4,5,6,175,46],[1381,0,1,2,3,4,258,5,6,46],[1405,0,1,2,3,4,5,6,333,46],[1411,0,1,2,406,3,4,5,6],[1174,0,1,77,2,3,4,5,6,46],[1474,0,1,2,177,3,4,5,6,46],[4189,0,1,2,3,4,260,5,6,46],[4207,0,1,2,3,4,5,6,335,46],[271,0,78,1,2,3,4,5,6,46],[1474,0,1,130,2,3,4,5,6,46],[1501,0,1,2,3,4,261,5,6,46],[1555,0,1,2,3,4,5,6,336,46],[1381,0,80,1,2,3,4,5,6,46],[4189,0,1,132,2,3,4,5,6,46],[1501,0,1,2,179,3,4,5,6,46],[4342,0,1,2,3,4,5,6,338,46],[1405,0,82,1,2,3,4,5,6,46],[4207,0,1,134,2,3,4,5,6,46],[1555,0,1,2,181,3,4,5,6,46],[4342,0,1,2,3,4,264,5,6,46],[3702,0,1,2,47,49,3,4,5,6],[3621,0,1,2,47,3,51,4,5,6],[4692,0,1,2,47,3,4,5,6,52],[4728,0,1,2,47,3,53,4,5,6],[5025,0,1,2,47,3,4,55,6],[3675,0,1,2,47,3,4,55,5,6],[3305,0,1,2,3,4,5,6,114],[1670,0,1,2,47,3,4,5,6,114],[1943,115,0,1,2,47,3,4,5,6],[3203,0,1,2,3,161,4,5,6],[1625,0,1,2,47,3,161,4,5,6],[3503,0,162,1,2,47,3,4,5,6],[3731,0,1,2,3,4,5,6,204],[2015,0,1,2,47,3,4,5,6,204],[2057,0,1,205,2,47,3,4,5,6],[3200,0,1,2,3,4,290,5,6],[1622,0,1,2,47,3,4,290,5,6],[3665,0,1,2,251,47,3,4,5,6],[3290,0,1,2,3,4,5,6,367],[1664,0,1,2,47,3,4,5,6,367],[5027,0,1,2,257,3,4,5,6],[3707,0,1,2,257,47,3,4,5,6],[1192,0,1,2,47,3,128,4,5,6],[58,0,1,2,7,47,3,128,4,5,6],[172,0,129,1,2,47,3,4,5,6],[277,0,1,2,47,3,4,5,6,175],[169,0,1,176,2,47,3,4,5,6],[1714,0,1,2,407,3,4,5,6],[193,0,1,2,7,407,3,4,5,6],[292,0,1,2,47,407,3,4,5,6],[1423,0,1,2,408,3,4,5,6],[193,0,1,2,408,47,3,4,5,6],[1711,0,1,2,47,218,4,5,6],[190,0,1,2,7,47,218,4,5,6],[190,0,1,2,219,47,3,4,5,6]],
  #[[1387,0,1,2,47,3,4,258,5,6],[136,0,1,2,7,47,3,4,258,5,6],[205,0,1,2,259,47,3,4,5,6],[1702,0,1,2,47,3,4,296,6],[181,0,1,2,7,47,3,4,296,6],[181,0,1,2,297,47,3,4,5,6],[1417,0,1,2,47,3,4,5,6,333],[145,0,1,2,7,47,3,4,5,6,333],[211,0,1,2,334,47,3,4,5,6],[1192,0,1,77,2,47,3,4,5,6],[1489,0,1,2,177,47,3,4,5,6],[3100,0,1,2,3,431,4,5,6],[1495,0,1,2,47,3,431,4,5,6],[4204,0,1,2,47,3,4,260,5,6],[4213,0,1,2,47,3,4,5,6,335],[277,0,78,1,2,47,3,4,5,6],[1489,0,1,130,2,47,3,4,5,6],[2023,0,1,2,446,3,4,5,6],[367,0,1,2,47,446,3,4,5,6],[2020,0,1,2,47,221,4,5,6],[1552,0,1,2,47,3,4,261,5,6],[2017,0,1,2,47,3,4,299,6],[1606,0,1,2,47,3,4,5,6,336],[1714,0,538,1,2,3,4,5,6],[292,72,0,538,1,2,3,4,5,6],[1858,537,0,1,2,3,4,5,6],[3100,0,1,653,2,3,4,5,6],[1495,72,0,1,653,2,3,4,5,6],[1846,557,0,1,2,3,4,5,6],[2023,0,1,2,674,3,4,5,6],[367,72,0,1,2,674,3,4,5,6],[2050,572,0,1,2,3,4,5,6],[2074,695,0,1,2,3,4,5,6],[3199,0,1,2,3,4,5,6,716],[1621,72,0,1,2,3,4,5,6,716],[1843,604,0,1,2,3,4,5,6],[2065,737,0,1,2,3,4,5,6],[3289,0,1,2,3,4,5,6,758],[1663,72,0,1,2,3,4,5,6,758],[1852,635,0,1,2,3,4,5,6],[292,0,538,1,2,47,3,4,5,6],[1495,0,1,653,2,47,3,4,5,6],[367,0,1,2,674,47,3,4,5,6],[2077,695,0,1,2,47,4,5,6],[1621,0,1,2,47,3,4,5,6,716],[2077,737,0,1,2,47,3,4,6],[1663,0,1,2,47,3,4,5,6,758],[1387,0,80,1,2,47,3,4,5,6],[4204,0,1,132,2,47,3,4,5,6],[1552,0,1,2,179,47,3,4,5,6],[3199,0,1,2,3,478,4,5,6],[1621,0,1,2,47,3,478,4,5,6],[4372,0,1,2,47,3,4,5,6,338],[1417,0,82,1,2,47,3,4,5,6],[4213,0,1,134,2,47,3,4,5,6],[1606,0,1,2,181,47,3,4,5,6],[3289,0,1,2,509,3,4,5,6],[1663,0,1,2,47,509,3,4,5,6],[4372,0,1,2,47,3,4,264,5,6],[3250,0,1,2,47,3,4,302,6],[4764,0,1,2,49,4,5,48],[768,0,1,2,3,4,5,50,6,48],[2772,0,1,2,3,51,4,5,6,48],[4766,116,1,2,3,4,5,6]],
  #[[2921,116,0,1,2,3,4,5,6],[4766,0,163,2,3,4,5,6],[4325,0,163,1,2,3,4,5,6],[4766,0,1,206,3,4,5,6],[3278,0,1,206,2,3,4,5,6],[4766,0,1,2,3,291,5,6],[4451,0,1,2,3,291,4,5,6],[4766,0,1,2,3,4,329,6],[3287,0,1,2,3,4,329,5,6],[388,0,1,2,3,128,4,5,6,48],[64,0,1,2,3,4,5,6,175,48],[469,0,1,2,3,4,258,5,6,48],[76,0,1,2,3,4,5,296,6,48],[1060,0,1,2,409,3,4,5,6],[388,0,1,77,2,3,4,5,6,48],[550,0,1,2,177,3,4,5,6,48],[3778,0,1,2,3,4,260,5,6,48],[553,0,1,2,3,4,5,298,6,48],[64,0,78,1,2,3,4,5,6,48],[550,0,1,130,2,3,4,5,6,48],[742,0,1,2,3,4,261,5,6,48],[262,0,1,2,3,4,5,299,6,48],[469,0,80,1,2,3,4,5,6,48],[3778,0,1,132,2,3,4,5,6,48],[742,0,1,2,179,3,4,5,6,48],[745,0,1,2,3,4,5,301,6,48],[76,0,81,1,2,3,4,5,6,48],[553,0,1,133,2,3,4,5,6,48],[262,0,1,2,180,3,4,5,6,48],[745,0,1,2,3,4,263,5,6,48],[2763,0,1,2,49,3,4,5,50,6],[4728,0,1,2,49,3,51,4,5,6],[5583,0,1,2,49,3,53,4,5,6],[5025,0,1,2,49,3,4,55,5],[4758,0,1,2,49,3,4,55,5,6],[3032,0,1,2,3,4,5,6,117],[3029,0,1,2,49,3,4,5,6,117],[4823,118,0,1,2,49,3,4,5,6],[5426,0,1,2,3,164,4,5,6],[5423,0,1,2,49,3,164,4,5,6],[5720,0,165,1,2,49,3,4,5,6],[3644,0,1,2,3,4,5,6,207],[3641,0,1,2,49,3,4,5,6,207],[5006,0,1,208,2,49,3,4,5,6],[5561,0,1,2,3,4,292,5,6],[5558,0,1,2,49,3,4,292,5,6],[5792,0,1,2,254,49,3,4,5,6],[3674,0,1,2,3,4,5,6,330],[3671,0,1,2,49,3,4,5,6,330],[5018,0,1,2,257,49,3,4,5,6],[2257,0,1,2,49,3,128,4,5,6],[418,0,1,2,7,49,3,128,4,5,6],[1042,0,129,1,2,49,3,4,5,6],[1300,0,1,2,49,3,4,5,6,175],[112,0,1,2,7,49,3,4,5,6,175],[1039,0,1,176,2,49,3,4,5,6],[3031,0,1,2,410,3,4,5,6],[1150,0,1,2,7,410,3,4,5,6],[3028,0,1,2,49,410,3,4,5,6],[1147,0,1,2,7,49,410,3,4,5,6],[1153,0,1,2,411,3,4,5,6],[1150,0,1,2,411,49,3,4,5,6],[2923,0,1,2,49,218,4,5,6],[1063,0,1,2,7,49,218,4,5,6]],
  #[[1063,0,1,2,219,49,3,4,5,6],[2434,0,1,2,49,3,4,258,5,6],[502,0,1,2,7,49,3,4,258,5,6],[1120,0,1,2,259,49,3,4,5,6],[1342,0,1,2,49,3,4,5,296,6],[121,0,1,2,7,49,3,4,5,296,6],[1057,0,1,2,297,49,3,4,5,6],[3022,0,1,2,49,3,4,5,333],[1144,0,1,2,7,49,3,4,5,333],[1144,0,1,2,334,49,3,4,5,6],[2257,0,1,77,2,49,3,4,5,6],[2551,0,1,2,177,49,3,4,5,6],[5425,0,1,2,3,432,4,5,6],[5422,0,1,2,49,3,432,4,5,6],[4309,0,1,2,49,220,4,5,6],[5092,0,1,2,49,3,4,260,5,6],[2563,0,1,2,49,3,4,5,298,6],[1300,0,78,1,2,49,3,4,5,6],[2551,0,1,130,2,49,3,4,5,6],[3643,0,1,2,447,3,4,5,6],[3640,0,1,2,49,447,3,4,5,6],[2665,0,1,2,49,3,4,261,5,6],[1828,0,1,2,49,3,4,5,299,6],[3235,0,1,2,49,3,4,5,336],[3031,0,540,1,2,3,4,5,6],[3028,73,0,540,1,2,3,4,5,6],[4819,539,0,1,2,3,4,5,6],[5425,0,1,654,2,3,4,5,6],[5422,73,0,1,654,2,3,4,5,6],[5716,558,0,1,2,3,4,5,6],[3643,0,1,2,675,3,4,5,6],[3640,73,0,1,2,675,3,4,5,6],[5002,573,0,1,2,3,4,5,6],[5029,696,0,1,2,3,4,5,6],[5560,0,1,2,3,4,5,717,6],[5557,73,0,1,2,3,4,5,717,6],[5788,605,0,1,2,3,4,5,6],[3673,0,1,2,3,4,5,738,6],[3670,73,0,1,2,3,4,5,738,6],[5014,620,0,1,2,3,4,5,6],[5800,759,0,1,2,3,4,5,6],[3028,0,540,1,2,49,3,4,5,6],[5422,0,1,654,2,49,3,4,5,6],[3640,0,1,2,675,49,3,4,5,6],[5830,696,0,1,2,49,4,5,6],[5557,0,1,2,49,3,4,5,717,6],[3670,0,1,2,49,3,4,5,738,6],[5830,759,0,1,2,49,3,4,5],[2434,0,80,1,2,49,3,4,5,6],[5092,0,1,132,2,49,3,4,5,6],[2665,0,1,2,179,49,3,4,5,6],[5560,0,1,2,3,479,4,5,6],[5557,0,1,2,49,3,479,4,5,6],[4414,0,1,2,49,222,4,5,6],[2686,0,1,2,49,3,4,5,301,6],[1342,0,81,1,2,49,3,4,5,6],[2563,0,1,133,2,49,3,4,5,6],[1828,0,1,2,180,49,3,4,5,6],[3673,0,1,2,494,3,4,5,6],[3670,0,1,2,49,494,3,4,5,6],[2686,0,1,2,49,3,4,263,5,6],[3250,0,1,2,49,3,4,5,339],[4716,0,1,2,3,51,50,6],[2861,119,0,1,2,3,4,5,6]],
  #[[4247,0,166,1,2,3,4,5,6],[3140,0,1,209,2,3,4,5,6],[3245,0,1,2,249,3,4,5,6],[4409,0,1,2,3,4,5,368,6],[373,0,1,2,3,128,4,5,50,6],[4,0,129,1,2,3,4,5,50,6],[13,0,1,2,3,4,5,50,6,175],[1,0,1,176,2,3,4,5,50,6],[67,0,1,2,3,218,4,5,50,6],[7,0,1,2,219,3,4,5,50,6],[973,0,1,2,412,3,4,5,6],[457,0,1,2,3,4,5,50,6,333],[10,0,1,2,334,3,4,5,50,6],[373,0,1,77,2,3,4,5,50,6],[508,0,1,2,177,3,4,5,50,6],[535,0,1,2,3,220,4,5,50,6],[3766,0,1,2,3,4,5,50,6,335],[13,0,78,1,2,3,4,5,50,6],[508,0,1,130,2,3,4,5,50,6],[235,0,1,2,3,221,4,5,50,6],[595,0,1,2,3,4,5,50,6,336],[67,0,79,1,2,3,4,5,50,6],[535,0,1,131,2,3,4,5,50,6],[235,0,1,2,178,3,4,5,50,6],[766,0,1,2,3,4,5,50,6,337],[457,0,82,1,2,3,4,5,50,6],[3766,0,1,134,2,3,4,5,50,6],[595,0,1,2,181,3,4,5,50,6],[766,0,1,2,3,224,4,5,50,6],[5535,0,1,2,3,51,53,4,5,6],[5775,0,1,2,3,51,4,55,6],[4701,0,1,2,3,51,4,55,5,6],[2960,0,1,2,3,4,5,6,120],[2939,0,1,2,3,51,4,5,6,120],[4784,121,0,1,2,3,51,4,5,6],[5372,0,1,2,3,4,5,167,6],[5339,0,1,2,3,51,4,5,167,6],[5681,0,168,1,2,3,51,4,5,6],[3572,0,1,2,3,4,5,6,210],[3527,0,1,2,3,51,4,5,6,210],[4922,0,1,211,2,3,51,4,5,6],[3629,0,1,2,3,4,250,5,6],[3545,0,1,2,3,51,4,250,5,6],[4946,0,1,2,251,3,51,4,5,6],[5540,0,1,2,3,4,5,6,369],[5510,0,1,2,3,51,4,5,6,369],[5777,0,1,2,3,295,4,5,6],[5753,0,1,2,3,295,51,4,5,6],[2185,0,1,2,3,128,51,4,5,6],[397,0,1,2,7,3,128,51,4,5,6],[925,0,129,1,2,3,51,4,5,6],[1210,0,1,2,3,51,4,5,6,175],[94,0,1,2,7,3,51,4,5,6,175],[922,0,1,176,2,3,51,4,5,6],[1339,0,1,2,3,218,51,4,5,6],[118,0,1,2,7,3,218,51,4,5,6],[1024,0,1,2,219,3,51,4,5,6],[2959,0,1,2,3,413,4,5,6],[1081,0,1,2,7,3,413,4,5,6],[2938,0,1,2,3,51,413,4,5,6],[1069,0,1,2,7,3,51,413,4,5,6],[1102,0,1,2,414,3,4,5,6],[1081,0,1,2,414,3,51,4,5,6],[2953,0,1,2,3,51,258,5,6]],
  #[[1078,0,1,2,7,3,51,258,5,6],[1078,0,1,2,259,3,51,4,5,6],[2833,0,1,2,3,51,4,296,6],[934,0,1,2,7,3,51,4,296,6],[934,0,1,2,297,3,51,4,5,6],[2431,0,1,2,3,51,4,5,6,333],[499,0,1,2,7,3,51,4,5,6,333],[1090,0,1,2,334,3,51,4,5,6],[2185,0,1,77,2,3,51,4,5,6],[2479,0,1,2,177,3,51,4,5,6],[2533,0,1,2,3,220,51,4,5,6],[5341,0,1,2,3,433,4,5,6],[5311,0,1,2,3,51,433,4,5,6],[4228,0,1,2,3,51,4,298,6],[5089,0,1,2,3,51,4,5,6,335],[1210,0,78,1,2,3,51,4,5,6],[2479,0,1,130,2,3,51,4,5,6],[1810,0,1,2,3,221,51,4,5,6],[3529,0,1,2,3,448,4,5,6],[3508,0,1,2,3,51,448,4,5,6],[3118,0,1,2,3,51,261,5,6],[2626,0,1,2,3,51,4,5,6,336],[1339,0,79,1,2,3,51,4,5,6],[2533,0,1,131,2,3,51,4,5,6],[1810,0,1,2,178,3,51,4,5,6],[3628,0,1,2,3,4,463,5,6],[3544,0,1,2,3,51,4,463,5,6],[3193,0,1,2,3,51,5,262,6],[2770,0,1,2,3,51,4,5,6,337],[2959,0,542,1,2,3,4,5,6],[2938,74,0,542,1,2,3,4,5,6],[4777,541,0,1,2,3,4,5,6],[4771,541,74,0,1,2,3,4,5,6],[5341,0,1,655,2,3,4,5,6],[5311,74,0,1,655,2,3,4,5,6],[5677,559,0,1,2,3,4,5,6],[5668,559,74,0,1,2,3,4,5,6],[3529,0,1,2,676,3,4,5,6],[3508,74,0,1,2,676,3,4,5,6],[4918,574,0,1,2,3,4,5,6],[4897,574,74,0,1,2,3,4,5,6],[3628,0,1,2,3,697,4,5,6],[3544,74,0,1,2,3,697,4,5,6],[4927,589,0,1,2,3,4,5,6],[4903,589,74,0,1,2,3,4,5,6],[5737,718,0,1,2,3,4,5,6],[5725,718,74,0,1,2,3,4,5,6],[4924,739,0,1,2,3,4,5,6],[4900,739,74,0,1,2,3,4,5,6],[5539,0,1,2,3,4,5,6,760],[5509,74,0,1,2,3,4,5,6,760],[5740,636,0,1,2,3,4,5,6],[5728,636,74,0,1,2,3,4,5,6],[2938,0,542,1,2,3,51,4,5,6],[2932,74,0,542,1,2,3,51,4,5,6],[4771,541,0,1,2,3,51,4,5,6],[5311,0,1,655,2,3,51,4,5,6],[5668,559,0,1,2,3,51,4,5,6],[3508,0,1,2,676,3,51,4,5,6],[4897,574,0,1,2,3,51,4,5,6],[3544,0,1,2,3,697,51,4,5,6],[3511,74,0,1,2,3,697,51,4,5,6],[4903,589,0,1,2,3,51,4,5,6],[5818,718,0,1,2,3,51,5,6]],
  #[[5812,718,74,0,1,2,3,51,5,6],[5725,718,0,1,2,3,51,4,5,6],[5818,739,0,1,2,3,51,4,6],[5812,739,74,0,1,2,3,51,4,6],[4900,739,0,1,2,3,51,4,5,6],[5509,0,1,2,3,51,4,5,6,760],[5500,74,0,1,2,3,51,4,5,6,760],[5728,636,0,1,2,3,51,4,5,6],[2431,0,82,1,2,3,51,4,5,6],[5089,0,1,134,2,3,51,4,5,6],[2626,0,1,2,181,3,51,4,5,6],[2770,0,1,2,3,224,51,4,5,6],[5539,0,1,2,3,510,4,5,6],[5509,0,1,2,3,51,510,4,5,6],[4375,0,1,2,3,51,4,302,6],[5949,0,1,2,3,53,5,52],[5951,122,1,2,3,4,5,6],[5597,122,0,1,2,3,4,5,6],[5951,0,169,2,3,4,5,6],[5939,0,169,1,2,3,4,5,6],[5951,0,1,212,3,4,5,6],[5747,0,1,212,2,3,4,5,6],[5951,0,1,2,252,4,5,6],[5765,0,1,2,252,3,4,5,6],[5951,0,1,2,3,4,331,6],[5750,0,1,2,3,4,331,5,6],[3808,0,1,2,3,128,4,5,6,52],[2281,0,1,2,3,4,5,6,175,52],[2386,0,1,2,3,218,4,5,6,52],[2290,0,1,2,3,4,5,296,6,52],[2455,0,1,2,415,3,4,5,6],[3808,0,1,77,2,3,4,5,6,52],[3907,0,1,2,177,3,4,5,6,52],[3934,0,1,2,3,220,4,5,6,52],[3913,0,1,2,3,4,5,298,6,52],[2281,0,78,1,2,3,4,5,6,52],[3907,0,1,130,2,3,4,5,6,52],[3109,0,1,2,3,221,4,5,6,52],[3106,0,1,2,3,4,5,299,6,52],[2386,0,79,1,2,3,4,5,6,52],[3934,0,1,131,2,3,4,5,6,52],[3109,0,1,2,178,3,4,5,6,52],[3124,0,1,2,3,4,5,300,6,52],[2290,0,81,1,2,3,4,5,6,52],[3913,0,1,133,2,3,4,5,6,52],[3106,0,1,2,180,3,4,5,6,52],[3124,0,1,2,3,223,4,5,6,52],[5565,0,1,2,3,53,4,55,5,6],[4541,0,1,2,3,4,5,6,123],[4163,0,1,2,3,53,4,5,6,123],[5258,124,0,1,2,3,53,4,5,6],[5924,0,1,2,3,4,5,6,170],[5846,0,1,2,3,53,4,5,6,170],[5900,0,171,1,2,3,53,4,5,6],[4391,0,1,2,3,4,5,6,213],[4067,0,1,2,3,53,4,5,6,213],[5552,0,1,214,2,3,53,4,5,6],[4454,0,1,2,3,4,253,5,6],[4091,0,1,2,3,53,4,253,5,6],[5588,0,1,2,254,3,53,4,5,6],[4382,0,1,2,3,4,5,332,6],[4061,0,1,2,3,53,4,5,332,6],[5570,0,1,2,3,295,53,4,5,6],[3817,0,1,2,3,128,53,4,5,6]],
  #[[2125,0,129,1,2,3,53,4,5,6],[2293,0,1,2,3,53,4,5,6,175],[448,0,1,2,7,3,53,4,5,6,175],[2122,0,1,176,2,3,53,4,5,6],[2404,0,1,2,3,218,53,4,5,6],[487,0,1,2,7,3,218,53,4,5,6],[2140,0,1,2,219,3,53,4,5,6],[4168,0,1,2,3,416,4,5,6],[2149,0,1,2,7,3,416,4,5,6],[3847,0,1,2,3,53,416,4,5,6],[2461,0,1,2,417,3,4,5,6],[2149,0,1,2,417,3,53,4,5,6],[4159,0,1,2,3,53,258,5,6],[2143,0,1,2,7,3,53,258,5,6],[2143,0,1,2,259,3,53,4,5,6],[2335,0,1,2,3,53,4,5,296,6],[454,0,1,2,7,3,53,4,5,296,6],[2131,0,1,2,297,3,53,4,5,6],[4165,0,1,2,3,53,4,5,333],[2146,0,1,2,7,3,53,4,5,333],[2146,0,1,2,334,3,53,4,5,6],[3817,0,1,77,2,3,53,4,5,6],[3922,0,1,2,177,3,53,4,5,6],[3982,0,1,2,3,220,53,4,5,6],[5854,0,1,2,3,434,4,5,6],[5833,0,1,2,3,53,434,4,5,6],[5848,0,1,2,3,53,260,5,6],[3943,0,1,2,3,53,4,5,298,6],[5851,0,1,2,3,53,4,5,335],[2293,0,78,1,2,3,53,4,5,6],[3922,0,1,130,2,3,53,4,5,6],[3127,0,1,2,3,221,53,4,5,6],[4354,0,1,2,3,449,4,5,6],[4045,0,1,2,3,53,449,4,5,6],[3112,0,1,2,3,53,4,5,299,6],[2404,0,79,1,2,3,53,4,5,6],[3982,0,1,131,2,3,53,4,5,6],[3127,0,1,2,178,3,53,4,5,6],[4453,0,1,2,3,4,5,464,6],[4090,0,1,2,3,53,4,5,464,6],[4414,0,1,2,3,53,5,262,6],[3208,0,1,2,3,53,4,5,300,6],[4168,0,544,1,2,3,4,5,6],[3847,75,0,544,1,2,3,4,5,6],[5245,543,0,1,2,3,4,5,6],[5854,0,1,656,2,3,4,5,6],[5833,75,0,1,656,2,3,4,5,6],[5893,560,0,1,2,3,4,5,6],[4354,0,1,2,677,3,4,5,6],[4045,75,0,1,2,677,3,4,5,6],[5179,575,0,1,2,3,4,5,6],[4453,0,1,2,3,698,4,5,6],[4090,75,0,1,2,3,698,4,5,6],[5200,590,0,1,2,3,4,5,6],[5914,719,0,1,2,3,4,5,6],[4381,0,1,2,3,4,5,740,6],[4060,75,0,1,2,3,4,5,740,6],[5176,621,0,1,2,3,4,5,6],[5917,761,0,1,2,3,4,5,6],[3847,0,544,1,2,3,53,4,5,6],[5833,0,1,656,2,3,53,4,5,6],[4045,0,1,2,677,3,53,4,5,6],[4090,0,1,2,3,698,53,4,5,6],[5920,719,0,1,2,3,53,5,6]],
  #[[4060,0,1,2,3,53,4,5,740,6],[5920,761,0,1,2,3,53,4,5],[2335,0,81,1,2,3,53,4,5,6],[3943,0,1,133,2,3,53,4,5,6],[3112,0,1,2,180,3,53,4,5,6],[3208,0,1,2,3,223,53,4,5,6],[4381,0,1,2,3,4,495,5,6],[4060,0,1,2,3,53,4,495,5,6],[4731,0,1,2,3,4,55,54],[2879,125,0,1,2,3,4,5,6],[4271,0,172,1,2,3,4,5,6],[3158,0,1,215,2,3,4,5,6],[3254,0,1,2,255,3,4,5,6],[4379,0,1,2,3,293,4,5,6],[379,0,1,2,3,128,4,5,6,54],[25,0,1,2,3,4,5,6,54,175],[73,0,1,2,3,218,4,5,6,54],[433,0,1,2,3,4,258,5,6,54],[1003,0,1,2,418,3,4,5,6],[379,0,1,77,2,3,4,5,6,54],[514,0,1,2,177,3,4,5,6,54],[538,0,1,2,3,220,4,5,6,54],[3754,0,1,2,3,4,260,5,6,54],[25,0,78,1,2,3,4,5,6,54],[514,0,1,130,2,3,4,5,6,54],[241,0,1,2,3,221,4,5,6,54],[571,0,1,2,3,4,261,5,6,54],[73,0,79,1,2,3,4,5,6,54],[538,0,1,131,2,3,4,5,6,54],[241,0,1,2,178,3,4,5,6,54],[652,0,1,2,3,4,5,262,6,54],[433,0,80,1,2,3,4,5,6,54],[3754,0,1,132,2,3,4,5,6,54],[571,0,1,2,179,3,4,5,6,54],[652,0,1,2,3,222,4,5,6,54],[3017,0,1,2,3,4,5,6,126],[3014,0,1,2,3,4,55,5,6,126],[4814,127,0,1,2,3,4,55,5,6],[5396,0,1,2,3,4,5,173,6],[5393,0,1,2,3,4,55,5,173,6],[5711,0,174,1,2,3,4,55,5,6],[3593,0,1,2,3,4,5,6,216],[3590,0,1,2,3,4,55,5,6,216],[4976,0,1,217,2,3,4,55,5,6],[3701,0,1,2,3,4,5,6,256],[3698,0,1,2,3,4,55,5,6,256],[5024,0,1,2,257,3,4,55,5,6],[5534,0,1,2,3,4,5,294,6],[5531,0,1,2,3,4,55,5,294,6],[5774,0,1,2,3,295,4,55,5,6],[2227,0,1,2,3,128,4,55,5,6],[412,0,1,2,7,3,128,4,55,5,6],[1000,0,129,1,2,3,4,55,5,6],[1243,0,1,2,3,4,55,5,6,175],[103,0,1,2,7,3,4,55,5,6,175],[997,0,1,176,2,3,4,55,5,6],[1363,0,1,2,3,218,4,55,5,6],[127,0,1,2,7,3,218,4,55,5,6],[1054,0,1,2,219,3,4,55,5,6],[2425,0,1,2,3,4,258,55,5,6],[493,0,1,2,7,3,4,258,55,5,6],[1096,0,1,2,259,3,4,55,5,6],[3016,0,1,2,3,4,419,5,6],[1138,0,1,2,7,3,4,419,5,6]],
  #[[3013,0,1,2,3,4,55,419,5,6],[1135,0,1,2,7,3,4,55,419,5,6],[1141,0,1,2,420,3,4,5,6],[1138,0,1,2,420,3,4,55,5,6],[2896,0,1,2,3,4,55,296,6],[1033,0,1,2,7,3,4,55,296,6],[1033,0,1,2,297,3,4,55,5,6],[2995,0,1,2,3,4,55,5,333],[1117,0,1,2,7,3,4,55,5,333],[1117,0,1,2,334,3,4,55,5,6],[2227,0,1,77,2,3,4,55,5,6],[2512,0,1,2,177,3,4,55,5,6],[2566,0,1,2,3,220,4,55,5,6],[5086,0,1,2,3,4,260,55,5,6],[5395,0,1,2,3,4,5,435,6],[5392,0,1,2,3,4,55,5,435,6],[4264,0,1,2,3,4,55,298,6],[1243,0,78,1,2,3,4,55,5,6],[2512,0,1,130,2,3,4,55,5,6],[1831,0,1,2,3,221,4,55,5,6],[2623,0,1,2,3,4,261,55,5,6],[3592,0,1,2,3,4,450,5,6],[3589,0,1,2,3,4,55,450,5,6],[3178,0,1,2,3,4,55,5,336],[1363,0,79,1,2,3,4,55,5,6],[2566,0,1,131,2,3,4,55,5,6],[1831,0,1,2,178,3,4,55,5,6],[2689,0,1,2,3,4,55,5,262,6],[3700,0,1,2,3,4,465,5,6],[3697,0,1,2,3,4,55,465,5,6],[3667,0,1,2,3,4,55,300,6],[3283,0,1,2,3,4,55,5,337],[2425,0,80,1,2,3,4,55,5,6],[5086,0,1,132,2,3,4,55,5,6],[2623,0,1,2,179,3,4,55,5,6],[2689,0,1,2,3,222,4,55,5,6],[5533,0,1,2,3,4,5,480,6],[5530,0,1,2,3,4,55,5,480,6],[4369,0,1,2,3,4,55,301,6],[3016,0,546,1,2,3,4,5,6],[3013,76,0,546,1,2,3,4,5,6],[4810,545,0,1,2,3,4,5,6],[5395,0,1,657,2,3,4,5,6],[5392,76,0,1,657,2,3,4,5,6],[5707,561,0,1,2,3,4,5,6],[3592,0,1,2,678,3,4,5,6],[3589,76,0,1,2,678,3,4,5,6],[4972,576,0,1,2,3,4,5,6],[3700,0,1,2,3,699,4,5,6],[3697,76,0,1,2,3,699,4,5,6],[5020,591,0,1,2,3,4,5,6],[5533,0,1,2,3,4,720,5,6],[5530,76,0,1,2,3,4,720,5,6],[5770,606,0,1,2,3,4,5,6],[4993,741,0,1,2,3,4,5,6],[5797,762,0,1,2,3,4,5,6],[3013,0,546,1,2,3,4,55,5,6],[5392,0,1,657,2,3,4,55,5,6],[3589,0,1,2,678,3,4,55,5,6],[3697,0,1,2,3,699,4,55,5,6],[5530,0,1,2,3,4,720,55,5,6],[5827,741,0,1,2,3,4,55,6],[5827,762,0,1,2,3,4,55,5]]
]
noncomputable def binRowData:Array (List ℕ):=(binRowDataChunks.toList.flatMap Array.toList).toArray

noncomputable def binMode (i:ℕ):ℕ:=(binChunkGet binRowDataChunks i []).headD 0 % 3
noncomputable def binRow (i:ℕ):ℕ × ℕ × ℕ × List W :=
  let p:=binChunkGet binRowDataChunks i []
  let tag:=p.headD 0
  ((if tag % 3 = 1 then 10 else 11),(if tag % 3 = 1 then 0 else 1),binZ (tag / 3),p.tail.map binW)

set_option maxRecDepth 100000 in
noncomputable def rootRowData:Array (ℕ × List ℕ):=#[
  (1571,[0,1,14,2,3,4,5,6]),(1984,[15,0,1,2,3,4,5,6]),(1570,[0,1,2,16,3,4,5,6]),(1985,[17,0,1,2,3,4,5,6]),
  (1589,[0,1,2,3,4,5,6,18]),(1986,[19,0,1,2,3,4,5,6]),(1609,[0,1,2,3,4,5,6,20]),(1987,[21,0,1,2,3,4,5,6]),
  (1583,[0,1,2,3,4,5,6,22]),(1988,[23,0,1,2,3,4,5,6]),(1610,[0,1,2,3,4,5,6,24]),(1989,[25,0,1,2,3,4,5,6]),
  (1580,[0,1,2,3,4,5,6,26]),(1990,[0,27,1,2,3,4,5,6]),(1575,[0,1,2,3,28,4,5,6]),(1991,[0,29,1,2,3,4,5,6]),
  (1981,[0,1,2,3,4,5,6,30]),(1992,[0,31,1,2,3,4,5,6]),(1573,[0,1,2,3,4,5,32,6]),(1993,[0,33,1,2,3,4,5,6]),
  (1982,[0,1,2,3,4,5,6,34]),(1994,[0,35,1,2,3,4,5,6]),(1678,[0,1,2,3,4,5,6,36]),(1995,[0,1,37,2,3,4,5,6]),
  (1579,[0,1,2,3,4,5,6,38]),(1996,[0,1,39,2,3,4,5,6]),(1677,[0,1,2,3,4,5,6,40]),(1997,[0,1,41,2,3,4,5,6]),
  (1581,[0,1,2,3,4,5,6,42]),(1998,[0,1,43,2,3,4,5,6]),(1574,[0,1,2,3,4,44,5,6]),(1999,[0,1,2,45,3,4,5,6]),
  (1679,[0,1,2,3,4,5,6,46]),(2000,[0,1,2,47,3,4,5,6]),(1588,[0,1,2,3,4,5,6,48]),(2001,[0,1,2,49,3,4,5,6]),
  (1572,[0,1,2,3,4,5,50,6]),(2002,[0,1,2,3,51,4,5,6]),(1983,[0,1,2,3,4,5,6,52]),(2003,[0,1,2,3,53,4,5,6]),
  (1577,[0,1,2,3,4,5,6,54]),(2004,[0,1,2,3,4,55,5,6])
]

noncomputable def rootRow (i:ℕ):ℕ × ℕ × ℕ × List W :=
  let p:=rootRowData.getD i (0,[])
  (12,1,binZ p.1,p.2.map binW)

set_option maxRecDepth 100000 in
noncomputable def unaryRowData:Array (List ℕ):=#[
  [2005,0,1,2,3,128,4,5,6],[2006,0,1,2,7,3,128,4,5,6],[2007,0,129,1,2,3,4,5,6],[2008,0,1,2,3,4,5,6,175],
  [2009,0,1,2,7,3,4,5,6,175],[2010,0,1,176,2,3,4,5,6],[2011,0,1,2,3,218,4,5,6],[2012,0,1,2,7,3,218,4,5,6],
  [2013,0,1,2,219,3,4,5,6],[2014,0,1,2,3,4,258,5,6],[2015,0,1,2,7,3,4,258,5,6],[2016,0,1,2,259,3,4,5,6],
  [2017,0,1,2,3,4,5,296,6],[2018,0,1,2,7,3,4,5,296,6],[2019,0,1,2,297,3,4,5,6],[2020,0,1,2,3,4,5,6,333],
  [2021,0,1,2,7,3,4,5,6,333],[2022,0,1,2,334,3,4,5,6],[2005,0,1,77,2,3,4,5,6],[2023,0,1,2,177,3,4,5,6],
  [2024,0,1,2,3,220,4,5,6],[2025,0,1,2,3,4,260,5,6],[2026,0,1,2,3,4,5,298,6],[2027,0,1,2,3,4,5,6,335],
  [2008,0,78,1,2,3,4,5,6],[2023,0,1,130,2,3,4,5,6],[2028,0,1,2,3,221,4,5,6],[2029,0,1,2,3,4,261,5,6],
  [2030,0,1,2,3,4,5,299,6],[2031,0,1,2,3,4,5,6,336],[2011,0,79,1,2,3,4,5,6],[2024,0,1,131,2,3,4,5,6],
  [2028,0,1,2,178,3,4,5,6],[2032,0,1,2,3,4,5,262,6],[2033,0,1,2,3,4,5,300,6],[2034,0,1,2,3,4,5,6,337],
  [2014,0,80,1,2,3,4,5,6],[2025,0,1,132,2,3,4,5,6],[2029,0,1,2,179,3,4,5,6],[2032,0,1,2,3,222,4,5,6],
  [2035,0,1,2,3,4,5,301,6],[2036,0,1,2,3,4,5,6,338],[2017,0,81,1,2,3,4,5,6],[2026,0,1,133,2,3,4,5,6],
  [2030,0,1,2,180,3,4,5,6],[2033,0,1,2,3,223,4,5,6],[2035,0,1,2,3,4,263,5,6],[2037,0,1,2,3,4,5,6,339],
  [2020,0,82,1,2,3,4,5,6],[2027,0,1,134,2,3,4,5,6],[2031,0,1,2,181,3,4,5,6],[2034,0,1,2,3,224,4,5,6],
  [2036,0,1,2,3,4,264,5,6],[2037,0,1,2,3,4,5,302,6]
]

noncomputable def unaryRow (i:ℕ):ℕ × ℕ × ℕ × List W :=
  let p:=unaryRowData.getD i []
  (11,0,binZ (p.headD 0),p.tail.map binW)

set_option maxRecDepth 100000 in
noncomputable def binBudgetBucketChunks:Array (Array (List ℕ)):=#[
  #[[1291,1295],[],[1960,1969,2075,2097],[79,865,884,2758],[1169],[934],[1114,2057,2199,2328],[2950],[778,788,1328,1370,1382,1395],[1173,1583,2351,2355],[2660],[],[698,706,1504,1505],[],[],[1739,2250],[635,823,1007,1211,1225,1231],[],[],[1144,1582],[1389],[1014],[],[1015,1031,1065],[123,161],[2203],[],[],[2356,2372],[70,2713,2717],[1603,1607,2152],[867,880],[],[1743,1751],[2053,2069,3129],[2932,2951],[],[],[741,1089,1922],[2066],[],[],[],[],[630,647,820],[665],[],[1615],[1869,1979,2496,2540],[],[],[],[2228,2268],[],[2690],[112,200],[],[692,852,907,2967],[228,232,1786],[],[],[585,595],[889,910,2622,2623],[2944,2947]],
  #[[],[],[270],[],[106,1783],[1441,1452],[1887,1898],[331,339],[],[392],[],[1784,2638,2678],[16],[2081],[2155,2781],[],[1507,1753,1757,2730,2772,2783,2795],[],[],[213,2089],[],[2327],[],[],[],[2204],[2340],[],[1110],[],[],[1006],[1635,2104,2144],[3135,3139],[7],[2273,2280],[2724,2746,2777,2793],[],[],[383],[1318,1475,1772,1919],[946,2698,2703,2706,2707],[710,738,775,2164],[2365,2416],[],[913,921],[],[],[],[371,1913,2817],[129,178,458],[2856,3049,3077],[],[1056,1092,3141,3142],[2557],[],[1118],[],[],[451,2815],[],[1799,2850,2995],[1763],[]],
  #[[2016],[1896,1900],[],[939],[1310,1329],[1491],[743,766,768,770,772,774,936,1906],[14,354,1498,1518,2465,2505,2520,2534],[],[2013],[],[1177,2970,2975],[],[],[1810,1854],[],[267,443,618,1331],[6,716,730],[2565],[99,120,153],[],[781,785],[1670,1691,2529],[],[],[2070],[425,1878,2363],[2308,2318],[],[],[1968,2114],[671],[],[2626],[],[27,1770],[],[252],[2415,2421],[],[1036],[3167],[163],[2969],[1921],[1,992],[],[1365,1386],[1088,1096],[],[2767,2801,3118],[1548,1565],[],[2298],[324,346,1283,1293,2090],[762,2481,2503,2509,2510],[43,50],[],[],[],[777,784,839,863,882,925,2169,2174,3003],[307,374],[22],[1152,1183,1524,1769]],
  #[[2731,2915],[2483],[2141],[],[],[],[],[2301,2309],[],[63,73,113],[2470,2527,2543,2725,3090],[265,1517],[732,832,922,1439,1444,2346],[966,976,2612],[2911,3032,3053],[],[1729],[],[2251,2270],[],[1367],[247],[],[1590],[864],[],[1480,1625,1633,1777],[],[1167,1187,1206,1222],[1269],[1936,1981,1989,2007],[1051],[636],[],[2076,3119,3172,3187],[2194,2206],[1630,2430],[1723],[432],[],[],[254,652],[],[],[],[817],[],[615],[390,1567,1861],[],[],[],[149,157,866,879],[1955],[1492,1622,2311,2315],[3098,3105],[289,2044],[1273],[1982],[],[351,367,1053,1061,1067,1068,2357,2358],[],[],[]],
  #[[2423,2644,2673],[],[273,621,810],[],[],[761],[],[2382],[1656,1698],[],[],[],[604,1158,2246],[21],[1819],[571,1917],[1587,1592,2497,2982,2989],[2916,2937,3018],[],[233,237],[],[3110,3150,3178],[87,1985,1986,2499,2547],[],[568],[456],[750,1042,2177,2187],[754],[],[],[],[2912,2935],[],[384],[3055],[],[1215,3149,3169,3190],[2035,2042],[],[1511],[],[1776,2867,2889,2895,2896],[],[1442,1456],[657,1888,1902],[],[3006],[],[],[],[],[52,2208,2869],[],[],[2655],[1703,1709],[],[],[],[377],[1319],[],[],[1812,1862]],
  #[[759],[1443,2851],[467,487,499,524],[],[2546,2554,2747],[1312,2816],[3035,3075],[2853],[],[],[444,745],[932,954,956,958,960,962,2366],[],[],[201],[],[],[272,1488,1526,1538,1551],[],[2342,2480],[],[],[],[],[798],[1455,1459],[969,973,1155,1305,1464,1901,1905],[1547,1558,1678],[769,1020],[1530,1540,1557,2848,2873,2909],[42,46,1282,1289,1791],[],[],[],[2893],[],[84,436,611,1935,1980,2006],[1218,2116,2134,2138,2140],[744],[325,355,1499,1502,2233],[293,311,361,2049],[],[],[],[],[],[],[724,731,1591,1604],[],[791,795,1674,1686,1700],[626,3012,3043],[2238,2247],[],[461,480,496,509,1258,1637],[2292],[107,126,170],[678,689,2822,2830,2833,2834],[2061],[75,1860,1867,2488],[],[],[2223],[206,1944,1967,1983],[1330,2275,2286]],
  #[[1196,1236,1938],[965,972,2198],[1059,1801,2823],[2,553],[296],[405,412],[],[],[2885,2952],[915,929],[142,164,1512],[822,1332],[1176],[],[2349,2490],[],[2201],[838,862,924],[2852],[],[2728],[622,1153,1523,1537,1544],[1710,2729,2771,2782],[1490,2482],[],[],[214],[2422],[],[],[],[82,257,985,1724,2339,2385,2397,2404],[],[1372,1401],[350,359],[],[1963,1991],[931,1097,1216,1244],[],[],[],[64],[1366,1380,1387,2723,2744,2776],[],[],[841],[512,526,1669,2849,2875,2910,2933],[1827,1837,1856,2454],[],[3155,3162],[],[],[594,601],[2354],[],[469,1619],[],[],[2321],[53,97,1128,1135,1482],[1188],[],[1101],[]],
  #[[],[2974],[],[],[1000,1426,1628,1644,1666],[2733,2787,2797,2804,2866],[1242,1255,1804,1840],[],[],[847,871,1357],[949],[],[1161,1468,1612],[2272,2643],[1026],[1261,2697,2702],[169,185,1806,1825],[321,2474,2530,2550],[],[],[843,868],[2753,2800],[90,614,803,2211,2428],[2827,2841],[1576,3148,3161],[800],[],[641],[2117,2127,2139],[],[],[938],[942,1296,1422,1434,2426],[],[147],[1317,1790],[],[653,3197,3198],[],[403,563],[1657],[124,136,162],[2326],[],[1281,1285,2222,2245,2261,2877,2998],[2477],[2986,2990],[2696],[212,2062],[2493,2556],[],[],[1005,1701],[],[2500],[],[2727,2765,2780,2794],[],[2515,2549],[],[],[],[],[2934]],
  #[[],[],[],[369,394,396,398,400,402],[555,1942,1966],[],[1909,1937,2325],[2791],[1579],[2868],[],[],[216,2642,2654,2666],[],[],[1447,1457,2641,2653],[430,452,476,1004],[],[2501],[],[753,1306,1528,2821],[],[2241,2277],[491],[],[2891,2913],[],[1160],[],[2478,2502],[2022],[1813],[897,919],[957,2460,2592,2719],[],[940],[1584],[89],[],[],[],[],[2209],[933],[],[],[1297],[3015,3050],[767],[1199,1243],[],[1885,1890],[1826,1855,3085],[],[1428,2055],[47,51,1874,2553,2659],[2103,2137],[1553,1559],[2011,2606],[143,172,1662,2119,2145],[243,953,1472],[2455,2472,2874,2878],[],[]],
  #[[633],[180],[709,729,1831],[130,138,179],[],[],[3088,3099],[3131,3168],[],[],[221,234],[],[650],[326,363,1676,1706,2368],[662,684],[],[],[],[1436,3013],[1595,1605,1704,1716,1882],[2709,2716],[1624,1789],[2434,2444],[],[2347,2369],[],[],[365],[2331],[],[103],[131,1469],[1197],[],[1052,1060,1262,1802,1803],[776,780,1487,1525,1550,2879],[100,121,135,154,2087,2129],[],[1011],[],[2886],[1147],[2892,2914,2936],[2014],[1241,1248,2901,2954],[],[700,720,2491,2492],[1529,1556,1718],[2029,2033,2718],[],[15,1972],[74],[329],[3102,3106],[168,176,301],[],[2215,2330],[1501],[189,1371],[360,368,2508,2548,2996],[1923],[],[],[]],
  #[[297],[1719,1732,1734,1736,1738,1740],[824,840,1010],[2345,2391,2399,2419],[1220,1228,1252,2887],[],[2575,2582,2756,2807],[290],[],[],[2745,2749],[952,2253],[1108,2818],[],[1771,2859,2876],[2864,2888],[1748,1752],[249,1893,1903],[],[1925,2847],[],[2413],[],[376],[],[],[114,1495],[54],[1373,1383,1402,2257],[],[846],[831],[1221,1460],[1911],[20,533,2514,2542,2627],[],[1645,1649],[139,3025],[1805],[1522,1543],[1116],[842,2307,2314,2361],[2427],[449],[],[582,904,912],[],[638],[],[639,659,711,2371,2381,2395],[2120,2128,2146],[],[],[2754],[266,1417],[1446,1453],[],[],[1121,1126,3061],[2836,2843,3183],[],[387],[28,1775],[]],
  #[[435],[2806,2812,2978,2988],[140,148,1192],[],[],[697,2195,3177],[],[373,1795,1951,1990],[],[549,573,575,577,579,581,2115],[2240,2269],[],[3033,3054,3068],[1481],[2121],[199,668,690,818],[],[505,525,2494,2495],[2376],[2828],[896,911],[],[656,680,704],[],[588,592],[397,2552],[1300,1313,1337],[310,378,2785],[182,979,983,1910],[2432,2437,2440,2441,2545],[2820,2829],[2469,2923],[2872],[],[2708,2712],[370],[1943,1946],[3166],[271,447,994],[1071,1094],[2567],[1127,1131,2463],[],[1533,1541,1563],[191],[35,48,2894,2953,2972,2983],[415,422],[],[431,2157],[],[],[],[389],[955,1636],[],[294,312,320,362],[],[],[569,1571],[],[2343],[2479],[995],[584,591,2341]],
  #[[1727,2927],[246,1181],[239,258,283],[357],[437,2555,2558,2560,2562,2564,2566],[],[747],[1534],[],[],[1478,2056],[2732,2786,2803],[2166,2364],[1267,1995,2009,2741,2763,2769,2770],[],[3016,3019],[60],[1200],[1572],[313,1916,2050,2192],[26,634],[],[1720,2173],[530,547,1202,1250,2743],[2064,2112,2131],[1924],[2018],[],[],[455,627,815],[643,664,685,719,2170,2178],[],[],[144,181,1815],[],[],[683],[463,1253,1846],[1744,1755],[1170,2288,3132],[964,968,1419],[517,1272,1388,1947],[],[760],[1174,3065],[],[],[314,316,2825],[30,1780,2924,2942],[],[619,802],[807],[],[],[],[830],[1509,1549,2348],[2230,2276],[],[],[2435,2448,2832,2842],[],[2726,2764,2779],[]],
  #[[877],[],[],[388,890,918,2880,2881],[194,2088],[1249,1256],[1926],[],[108,127,137,171],[],[280],[2338,2384,2403],[1626,1642],[2180,2184,2737,3052],[2190],[177,186,224,231],[],[2928,2948],[203],[],[322,330,1191,3121],[1822],[],[1735],[277,813,998],[],[],[763],[],[2306,2310],[561,3062],[],[1109],[1733],[797,1915],[],[],[66],[2757],[1679],[],[1102],[1945,2447,2451],[],[454],[],[],[2865],[],[673,734],[1731],[828,870],[244,262,291,1536,1539],[1070,1086,1311],[],[771,1694,1702],[1954,1996],[],[],[1189],[1038,1048,1082],[489,531,1809],[],[2281,2287,3125,3147,3153,3154]],
  #[[1154],[],[506,534,2628,2629],[566],[],[2197],[],[],[542,608,2759],[886,923,930,1594,1601,3127],[83],[],[98],[552],[],[821,2065,2113,2125,2132,3180],[2025,2036],[348,381,3114,3158,3182,3194],[],[1978,1988,1999],[8,414,418,1213,1237],[34,44,1450,1454],[115],[2093],[1423],[1019,1035,1047,1073,1620],[],[901,1352,1393,1693,2225],[2591],[],[3],[576],[],[557],[],[855,875,3116,3164,3184],[],[3108,3136,3176,3192],[783,793,2290],[1952],[],[550,2570,2581,2740],[],[2214,2259,2267,2285],[9,1494],[395,3001,3046,3059],[1178],[2135,2148],[1159,1309,1764],[1845,1865],[334,364],[1994,2002,2466],[488],[2467,2511,2522],[198,2683,2813],[],[3152],[238,725,740,1335,1375,1408],[88,440,987],[1420,2407,2420],[],[529,538],[2323],[]],
  #[[],[1730],[2396,2400],[],[1634],[1079,1095],[1324],[2260],[1002,1765],[2461,2484,2516],[],[935],[1142,1171,1302,2302,2313],[1696],[],[],[2748],[2110],[],[],[],[62,1338],[67,101],[1745,1759,2001,2274],[259],[],[2563],[],[],[],[1479],[],[404,408,1811],[537,914,1268,1399,1413,3039,3045],[240,1184],[2263,2266],[1074,2019,2559,2750],[],[],[1316,1473,1618],[],[2572],[2999],[],[502,620],[2742],[],[2584,2588],[948],[474,492,540],[],[],[],[],[644],[1203],[],[2471,2528,2538,2544],[3143],[],[1466],[1532,1562,1609],[1023],[1259,1574]],
  #[[676,695],[],[646,670,691,727],[],[],[152,183,1129,1139,2705,2715],[12,612],[1107,2295],[3031,3044],[504,511,518,519,610,1948,1949],[],[],[829],[477,1659,1705],[],[],[5,470],[],[1758,1762],[1204,2805,3048],[],[836,857,876,917],[],[],[1510,2294],[1977,1998,2231],[],[2388,2398,2412,3124],[],[1632],[],[2694],[210,2443,2450,2854],[1828],[220,230,1165,1616,1768],[33,40],[2506],[],[],[779,792],[3094,3104],[],[],[1821,1835,1842],[94,806,991],[3017,3051,3067],[],[104,2344,2390,2418],[1037,1081],[2637,2672],[],[],[],[],[1315],[256,1928,1975,1987,1993,2788],[],[],[],[],[215,959],[],[1145,1179,1613],[1844,1858]],
  #[[],[],[3138],[2431,2436],[],[],[],[2425],[71,109,827,845,869,893],[],[263],[],[1355,1400],[755,1018,1034,1072],[],[],[],[2458],[],[1711,1717,2507,2541],[245],[],[],[426,560,861,881],[],[1623],[1125],[125,1239,1546],[],[2370,2380],[885,1742,1747,1956,2004],[3126],[116],[1672],[95,117,145],[2429],[],[756],[],[1872,2293],[507,543,648,2760,2761],[666,687,1892,1899,2181,2188],[1497],[1515,2156],[2008,2775],[419,423,1276,1641,1681,1689,1714,2255,2265,2279],[],[1195],[],[2608,2662,2670,2681,2855],[],[38,45,574,2249,2738,2762],[2607,2661,2680],[],[17,2026,2040],[2722],[854],[],[],[888,895,902,903,1353,2226,2227],[],[223,227,482,515,1025,1041,1049,1091,2303,2317],[],[241]],
  #[[],[],[],[375,1554,1566,1880],[1301],[3137],[],[132,133,1398,1405],[1266],[1682],[],[],[1782,2003,2010,2329],[55,1973,2663],[2207,2375,2417],[1345,1853,1866],[2610],[284,3004,3063,3078],[1773],[2593,2609,2721],[1440,1448],[],[539,548,1009],[],[1064,1093],[13],[],[1941],[],[],[],[],[],[2439,2449],[1148,2379],[],[2039,2043],[1684,1688],[583,587,3080],[],[2045,2073],[2485,2489,2667,2669],[1246,1581,2242],[],[76,251,433,752],[151,174],[963,2561],[308,352],[1820,1841],[],[606,632,651,1008],[],[173,1336,1376,1384,1409,3040,3056],[3097,3101],[56,1467],[342,358],[2316,2320],[1260],[268,834,2359,2401],[],[],[1927,1974,1992],[],[]],
  #[[],[285,305,344,1325,1788,1824,1836,1849],[],[2845],[77,1054,1075,2751,2752],[],[1585],[1326],[304,1217,1227,1245,2442,2446],[],[],[],[2212],[],[],[],[1377,2234,2282],[1323,2296],[281,1198],[1348,1385,2992],[1209],[1673,1699],[337,3186],[],[1588,1596],[300],[891,926,3144,3145],[672,693],[782,789,3093,3100],[715,722,1350],[1168,3159],[],[],[2569,2574,2577,2578],[],[],[],[3122,3146],[],[],[],[2406,2414],[835,856,916],[],[1379,1381,2304],[1410,1660],[],[],[],[2870,2902],[1210,1230],[1078,1087],[211,278,298,327],[2051],[1608],[1792,1914],[1013,2774,2809],[],[2101,2130,2525],[],[],[204],[1120],[465,628,1934]],
  #[[2176,2183,2475,2531,2539,2551],[453,1650],[],[292,2205],[708,721,2098,2108],[2133],[3120,3173,3188,3196],[1598,1602],[],[478],[],[],[],[2219],[],[528,723,2015],[],[1781],[943],[971,981],[1151,2000,2645],[],[],[],[],[],[1098,1111,1113,1115,1117,1119],[],[190,429,637,2532],[826,844,892],[80,255,799],[2074],[],[749],[464],[411,421],[1212],[2459],[1726],[2755],[61,3023,3074],[],[944],[2020],[860,1356],[],[2452],[],[2925],[1024,1040,1090,2210],[1358,1407],[598,602],[],[],[3130],[1671,1685,1692],[2536,2537],[2191,3111,3151,3179,3193],[1427],[150,166,1873],[],[],[1957],[]],
  #[[2571,2585,2824,2837],[677,688],[2652],[814,851,873,1424,2048],[24,2882],[1653,1690],[1787,1823,1848],[2220,2244],[],[554],[393],[1103,3089,3103],[522,545],[625,2959,2960,2962,2964,2966,2968],[],[1655],[],[],[758,2393],[57,2739],[2624,2671],[],[],[],[],[],[1030,1958],[],[1486,2981,2985],[119,2464,2504,2519],[],[],[29,1406,1414,1779],[],[2151,2158,2168],[617],[],[1939,1959],[401,1483],[],[658,681],[1920,2196,2324],[2736,2790,2798,2811],[],[2433,2473],[],[],[503,510,1346,1347],[],[],[1737],[459,819,1003],[],[],[1143],[],[],[],[490,500,532],[2099,2109,2123],[1461,1477,1496,1778,2252,2264,2271,3083],[2023,2028,2734],[2046,2150,2159,2161,2163,2165,2167],[1274,2857,2905,2921]],
  #[[68],[1234,1247,2017,2926,2945],[2333,2352,2378,2394,2603],[2977,2984],[947,1156],[1668,1907,1912,1933,2193],[2773,2802,3081],[],[275,623,996],[],[333,356],[159,175],[2597],[],[85,796,1807,1847],[427,450,472,816],[],[],[607],[],[],[],[1343],[1639],[],[225,235,1100,3133],[2360,2676,2682],[209,1257,1364],[1573],[2021],[570],[],[2590],[37,41,970,977],[2513],[],[260,287,407,420,484,1663,1712],[1794,1830,1838,1864],[613],[102,1545,1552],[1208],[],[3191],[3002,3047,3060,3070],[1012],[],[],[2154,3009,3030,3037,3038],[2235],[81,1321,1339,1361],[859,878,2124,2126,2498],[1349],[2175,2179,3066],[2054],[323,338,1950],[],[1818],[3011],[578],[],[1044,1050],[1852,1859],[906,928,1166,1185,1205],[631,1122,1130]],
  #[[],[],[],[1965,2005],[],[3123],[1857,3034],[2387,2411],[2602],[1474],[],[410,417,1314,2084,2100,2601],[1363,2236,2289],[514,544],[],[],[2858,2906,2922,2940],[2871],[],[462],[],[],[],[1971,2217,2237],[],[1397],[],[2031,2041,2200,2599],[3058],[],[984,2598],[1451,1458],[],[887,894,1651,1652],[382,1871],[],[1741],[341,349,825],[196,937],[],[1146],[193,590,600],[],[],[],[2367],[475,493,501,541,1039],[],[],[975,982],[72],[441],[521,536,950],[],[],[],[3156,3170],[],[65,248,1112],[],[],[765,2153],[],[1531]],
  #[[],[],[],[],[],[1133,1140],[],[],[1648,3024],[],[494],[442,1106],[],[471,1617],[2524],[1485],[572,1746],[2111],[1359,1418],[2704,2711],[2900],[649],[1392,1411,1638],[661,1471],[25,850,2297,2518],[110,773,1953],[2091,2136],[2060],[2649],[2239,2248,2262],[],[],[1022],[18,654,679,2408,2941],[],[1599,1606,2171,2182,2965],[701,728,1182,2580,2587,2883,2884],[1580,1654],[495,498],[2221,2224],[2229],[380],[302,335,736,1793,1829,1863,3026],[546,1080],[580],[1463,2961],[1360],[],[219,226,1521],[],[2919],[96,118,134,146],[2625],[2243,2283],[10],[],[],[],[2202],[],[385,2908,2955],[1320,1621,1774],[309,319,353],[898,927]],
  #[[4,1277,1284],[],[997],[],[2383],[1940],[372],[2568,2573],[1721],[1750,1760],[],[3008],[],[],[2334],[],[286,306,318,345,3082],[2336],[439,1163,1470,1766],[2405],[1043],[1263],[2600],[],[941,2958],[409,413,1298,1333],[786,790,1105],[1908],[92,276,616,989],[],[2160],[986],[1722],[282],[2353],[],[],[269,445,808,1527,1629,1646,1667,1683],[],[],[],[2185,2189],[586,599,2300,2305],[111],[],[],[1149,1175,1465,1808],[428],[1123,1134],[1271],[],[],[],[],[],[1891,1895],[58,69,105],[2438,2445],[261,483,497,516,1850,2766],[1270],[],[809],[2118],[]],
  #[[1193,1229],[],[520,527],[279,299,315,328,2920,2939,3087,3092,3095,3096],[242,1664],[1675],[1287,1294],[858],[1697,1715],[1476],[141,155,1351,2299],[2232,2840,2844],[1265,2614,2634,2639,2640],[2389],[696],[3005,3010,3064,3072,3079],[562],[589,596,1340,1344,2684,2687,2689,2691,2693,2695],[217,1033,2107],[],[],[],[2615],[],[667,1798,1817,1833],[],[424,1520],[],[2374,2410,3115],[],[1186,1190],[655,703],[1665],[],[],[2973,2987],[],[2576,2586],[1063,1085,3000,3109],[2720],[],[1976,2768,2796,2799,2808],[],[699,707,713,714,1132,1136,2085,2086],[1322,1341,1362,1378],[],[187],[1233,1240,1627],[2735,2789,2810,2994],[],[3041,3057,3069],[2386],[],[],[],[1214,1226,1238,2218,2898,2917],[2102],[158,167],[1725],[],[],[39,49,1303],[1391,1404],[23]],
  #[[],[1814],[165],[2453,2457,2476],[805,967,980],[1403],[],[434],[],[],[],[],[],[],[],[386],[],[2993],[],[2067],[1021],[1304],[],[811,1749,1756],[1438],[1884,2826],[],[1264],[],[],[961],[205,2256],[2034,2038],[],[1368,2521],[2012],[218,222,1834,1839,2468,2512,2523,2535],[2063],[],[642,663,718],[],[1083,3020],[],[2630,2677],[2636,2651,2665],[640,660,682,712,1354],[849,872,900,1513,1555,1677,1687,1707],[559,757,1172,2635,2650],[11],[1278,1288],[],[],[905,920,1415,1429,1431,1433,1435,1437],[1412,1868,1875,1877,1879,1881,1883],[],[2963],[446,2462,2486,2517,2533],[603],[2092],[2058,2078,2105],[1658,2618,2648,2664],[],[],[2616,2647]],
  #[[2094,2143],[343,366],[564],[274,1445,1449],[1029,1045,1058],[],[2213,2258,2284],[],[2899,2918,2938],[],[702,737,3027,3028],[],[551,1767],[],[2147],[],[379],[],[1327,1369,1394],[],[2027],[3007,3029],[],[],[2337],[2991],[485],[],[1586],[1796,1816],[],[974,978],[],[1223,1224,1484],[2216],[],[],[1425,2392],[1164,1462],[1754,1761],[2162,2613],[],[1728,2971,2976,2979,2980],[],[1286,1290],[202],[2142,2149,2332,2350,2377],[1157,1307,1610,1930],[93],[705,1503],[],[288,1069,1077],[],[2846,2862],[2699,2710],[],[733,742,1569],[86,438,801],[],[],[],[2077],[1374],[]],
  #[[],[],[195],[],[1150],[746,1647],[1017],[1593,1597,1611,3128,3160],[],[],[466,486,523,2068],[2424],[1390,1396],[1832],[78,253,609],[340,1932],[1027,2373,2402],[250],[],[],[1334],[],[1124,1138],[],[59],[],[686,1062,1076,2579,2583],[],[837],[],[],[1661],[1194,2897,2904],[1180,1889],[],[909,2621],[556,2082],[],[1219,1251,3014],[2692],[1016,1032,1046,1066],[853,874,908,1578],[812,2860,2929,2956],[],[1232,1962],[],[],[593,597],[3112],[2688],[192,567,2059,2080,2106,2122,3113,3157,3181],[],[],[1506,1542],[156,787,794,3163,3171],[1489],[122,764,1275,1280,2071,3189],[],[391,1500,1519,1535,2997],[],[406,416],[460,479,508],[],[1508,2784]],
  #[[],[1631,1961,1970,1984],[2686],[],[1137,1141,2589,2819],[],[197,2863,3107,3134,3175],[2890,2903],[],[1416,2778],[],[],[473,1342],[],[188],[1564,2596,3036],[],[],[2595,2907],[],[],[565],[399],[3084],[332,347],[229,236,1918,2052,2322],[1886,1894,3042,3076,3140],[1964,1997],[2526],[2656],[],[208,951],[2814],[1614],[],[457,629,1001],[],[513,535],[],[],[],[],[],[804],[],[674,694,735],[1421],[2835,2839],[],[],[],[1201,2030,2037],[945],[1929,2047],[31],[1577],[988,1028,1057],[303,317,336,993],[2172,2186],[2861,2930,2949,2957],[],[],[605,1695,1708],[448,468,624,1099,2362,2409]],
  #[[],[],[1308],[751,848,899],[],[],[748],[3117,3165,3185,3195],[2254,2278],[675,1055,1084,3021,3022],[1432,2605,2658,2668,2675],[645,669,726,1235,1254,1785,2631],[],[1162,1570,2312,2319,2604,2657,2674],[1514,3071,3073],[2646,2679],[481,2291,2456],[1640,1680,1713,2685],[0],[2792],[1430,1516,1561],[160,184,1876,1931,3174],[558,2831,2838],[91,1279,1292,2931],[2487],[],[],[2079,2083],[],[1589,1600],[999],[2024,2032,2617,2620],[1897,1904,2095],[32,36],[2619],[],[],[],[1870],[2632,2700,2714],[2701],[1493,3086,3091],[128],[],[883],[1643],[207,717,739],[1104,2072],[],[],[1575,2611,2633],[2943,2946],[],[],[2594],[],[],[],[264,295],[],[833,990,2096],[1797,1800,1843,1851,2335],[],[]],
  #[[],[1207],[1560,1568],[19,1299],[]]
]
noncomputable def binBudgetBuckets:Array (List ℕ):=(binBudgetBucketChunks.toList.flatMap Array.toList).toArray

set_option maxRecDepth 100000 in
noncomputable def rootBudgetBucketChunks:Array (Array (List ℕ)):=#[
  #[[],[],[],[],[],[],[],[],[20],[37],[],[],[],[],[0],[],[],[],[39],[28],[25],[],[],[8],[],[],[],[31],[30],[],[40],[],[],[],[36],[17],[],[],[],[],[],[],[41],[],[24,27],[],[],[],[],[],[4],[33],[],[29],[],[],[],[],[],[2,19],[35],[],[23],[7]],
  #[[],[],[34],[],[21],[],[12,13],[],[10],[],[],[],[],[6,15],[],[32],[],[],[],[],[26],[],[],[9],[],[],[],[38],[],[],[],[22],[11],[],[3],[],[],[],[14],[],[],[5],[],[],[],[16],[],[],[],[1],[],[],[],[],[],[18],[],[],[],[],[],[],[]]
]
noncomputable def rootBudgetBuckets:Array (List ℕ):=(rootBudgetBucketChunks.toList.flatMap Array.toList).toArray

set_option maxRecDepth 100000 in
noncomputable def unaryBudgetBucketChunks:Array (Array (List ℕ)):=#[
  #[[],[],[],[],[],[],[12,42],[],[],[9,36],[8],[],[33,39],[4,27,38],[],[],[],[26,32],[],[],[],[17],[],[],[],[],[22,43],[],[47,53],[],[],[],[],[],[],[3,24],[],[],[],[],[],[],[],[23,49],[],[],[],[],[],[],[],[],[],[],[],[],[],[28,44],[],[],[14],[],[],[]],
  #[[35,51],[],[],[],[],[1],[],[],[],[],[],[],[19,25],[],[5],[7],[],[16],[],[],[],[],[],[11],[],[],[],[0,18],[],[],[],[],[],[29,50],[41,52],[20,31],[],[6,30],[],[15,48],[],[],[],[],[],[],[],[13],[],[],[10],[],[],[],[],[2],[],[],[],[],[21,37,40,46],[34,45],[]]
]
noncomputable def unaryBudgetBuckets:Array (List ℕ):=(unaryBudgetBucketChunks.toList.flatMap Array.toList).toArray

set_option maxRecDepth 100000 in
noncomputable def low0BudgetBucketChunks:Array (Array (List ℕ)):=#[
  #[[],[20],[],[13],[],[],[],[],[],[],[16],[],[14],[],[],[],[],[],[9],[17],[],[11],[3],[],[],[],[],[10],[],[6],[],[],[],[],[],[],[7],[],[],[],[],[],[],[],[],[],[4],[],[],[],[],[],[],[],[],[5],[],[1],[],[],[],[],[],[]],
  #[[2],[],[],[],[],[],[],[],[0],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[18],[],[],[],[],[],[],[],[],[19],[],[12],[],[],[],[],[],[],[15],[],[],[],[],[],[],[],[8],[],[],[],[],[]]
]
noncomputable def low0BudgetBuckets:Array (List ℕ):=(low0BudgetBucketChunks.toList.flatMap Array.toList).toArray

noncomputable def binBudgetAt (i:ℕ):List ℕ:=binChunkGet binBudgetBucketChunks i []
noncomputable def rootBudgetAt (i:ℕ):List ℕ:=binChunkGet rootBudgetBucketChunks i []
noncomputable def unaryBudgetAt (i:ℕ):List ℕ:=binChunkGet unaryBudgetBucketChunks i []
noncomputable def low0BudgetAt (i:ℕ):List ℕ:=binChunkGet low0BudgetBucketChunks i []

noncomputable def binFCandidates (z:ℕ):List ℕ :=
  (binBudgetAt (z % 2053)).filter (fun i => decide (binMode i ≠ 0))
noncomputable def binGCandidates (z:ℕ):List ℕ :=
  (binBudgetAt (z % 2053)).filter (fun i => decide (binMode i = 0))
noncomputable def rootCandidates (z:ℕ):List ℕ:=rootBudgetAt (z % 127)
noncomputable def unaryCandidates (z:ℕ):List ℕ:=unaryBudgetAt (z % 127)
noncomputable def low0Candidates (z:ℕ):List ℕ:=low0BudgetAt (z % 127)

noncomputable def low0Row (i:ℕ):ℕ × ℕ × ℕ × List W :=
  let r:=rootRow (2 * i + 1)
  (11,0,r.2.2.1 - initG / 16,r.2.2.2)

noncomputable def low0Rows:List CutState:=(List.range 21).map low0Row

noncomputable def lowForceLook1 (K fuel k t z:Nat) (v:List W):Bool :=
  strictSt initL (fun l => strictSt initM (fun m => strictSt initG (fun g => strictSt K (fun K => strictSt fuel (fun fuel => strictSt k (fun k => strictSt t (fun t => strictSt z (fun z => frcAll v (fun v => look1 l m g K fuel k t z v)))))))))
lemma lowForceLook1_eq (K fuel k t z:Nat) (v:List W) :
    lowForceLook1 K fuel k t z v = look1 initL initM initG K fuel k t z v:=by
  simp only [lowForceLook1,strictSt_eq,frcAll_eq]
noncomputable def low0Check (i:Nat):Bool :=
  let r:=low0Row i
  lowForceLook1 12 12 r.1 r.2.1 r.2.2.1 r.2.2.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK0:low0Check 0 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK1:low0Check 1 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK2:low0Check 2 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK3:low0Check 3 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK4:low0Check 4 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK5:low0Check 5 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK6:low0Check 6 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK7:low0Check 7 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK8:low0Check 8 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK9:low0Check 9 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK10:low0Check 10 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK11:low0Check 11 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK12:low0Check 12 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK13:low0Check 13 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK14:low0Check 14 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK15:low0Check 15 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK16:low0Check 16 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK17:low0Check 17 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK18:low0Check 18 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK19:low0Check 19 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0OK20:low0Check 20 = false:=by decide +kernel
lemma low0Checked:∀ s ∈ low0Rows,
    look1 initL initM initG 12 12 s.1 s.2.1 s.2.2.1 s.2.2.2 = false:=by
  intro s hs
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hs
  have hi:i < 21:=List.mem_range.mp hi
  have h:low0Check i = false:=by
    interval_cases i
    · exact low0OK0
    · exact low0OK1
    · exact low0OK2
    · exact low0OK3
    · exact low0OK4
    · exact low0OK5
    · exact low0OK6
    · exact low0OK7
    · exact low0OK8
    · exact low0OK9
    · exact low0OK10
    · exact low0OK11
    · exact low0OK12
    · exact low0OK13
    · exact low0OK14
    · exact low0OK15
    · exact low0OK16
    · exact low0OK17
    · exact low0OK18
    · exact low0OK19
    · exact low0OK20
  simpa only [low0Check,lowForceLook1_eq] using h

noncomputable def low0BucketRows (z:Nat):List CutState:=(low0Candidates z).map low0Row

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0BucketsBound:low0BudgetBucketChunks.all (fun c => c.all (fun xs => xs.all (fun j => decide (j < 21)))) = true:=by
  decide +kernel

lemma low0BucketRowsChecked (z:Nat):∀ s ∈ low0BucketRows z,
    look1 initL initM initG 12 12 s.1 s.2.1 s.2.2.1 s.2.2.2 = false:=by
  intro s hs
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hs
  have hb:i < 21:=chunk_bucket_index_bound _ _ low0BucketsBound _ _ hi
  exact low0Checked _ (List.mem_map.mpr ⟨i,List.mem_range.mpr hb,rfl⟩)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def low0Coverage :
    chkCut (look initL initM initG 12)
      (patchBudget (look1 initL initM initG 12 12) low0BucketRows)
      [] (pr ac4 0) 0 12 0 FF 1 = false:=by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma low0Root:chk [] (pr ac4 0) 0 12 0 FF 1 = false:=by
  have hl:lz 0 = initL:=by rfl
  have hm:mz 0 = initM:=by rfl
  have hg:pL ((pr ac4 0).map fun _ => 16) = initG:=by rfl
  have h:=low0Coverage
  rw [patchBudget_eq _ _ low0BucketRowsChecked] at h
  simpa only [← hl,← hm,← hg,chkCut_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def lower13Case0:chk [] (pr ac4 0) 0 12 0 FF 1 = false:=low0Root

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def lower13Case1:chk [] (pr ac4 0) 0 12 1 FF 1 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def lower13Case2:chk [] (pr ac4 0) 0 12 2 FF 1 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def lower13Case3:chk [] (pr ac4 0) 0 12 3 FF 1 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def lower13Case4:chk [] (pr ac4 0) 0 12 4 FF 1 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def lower13Case5:chk [] (pr ac4 0) 0 12 5 FF 1 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def lower13Case6:chk [] (pr ac4 0) 0 12 6 FF 1 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def lower13Case7:chk [] (pr ac4 0) 0 12 7 FF 1 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def lower13Case8:chk [] (pr ac4 0) 0 12 8 FF 1 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def lower13Case9:chk [] (pr ac4 0) 0 12 9 FF 1 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def lower13Case10:chk [] (pr ac4 0) 0 12 10 FF 1 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def lower13Case11:chk [] (pr ac4 0) 0 12 11 FF 1 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def lower13Case12:chk [] (pr ac4 0) 0 12 12 FF 1 = false:=by decide +kernel

noncomputable def lower13Split:m0_0.all (okS ac4 0 12) = true:=by
  apply List.all_eq_true.mpr
  intro p hp
  simp only [m0_0,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [okS,Bool.not_eq_true'] using lower13Case0
  · simpa only [okS,Bool.not_eq_true'] using lower13Case1
  · simpa only [okS,Bool.not_eq_true'] using lower13Case2
  · simpa only [okS,Bool.not_eq_true'] using lower13Case3
  · simpa only [okS,Bool.not_eq_true'] using lower13Case4
  · simpa only [okS,Bool.not_eq_true'] using lower13Case5
  · simpa only [okS,Bool.not_eq_true'] using lower13Case6
  · simpa only [okS,Bool.not_eq_true'] using lower13Case7
  · simpa only [okS,Bool.not_eq_true'] using lower13Case8
  · simpa only [okS,Bool.not_eq_true'] using lower13Case9
  · simpa only [okS,Bool.not_eq_true'] using lower13Case10
  · simpa only [okS,Bool.not_eq_true'] using lower13Case11
  · simpa only [okS,Bool.not_eq_true'] using lower13Case12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def h0_0:m0_0.all (okS ac4 0 12) = true:=lower13Split
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def p0:okP ac4 0 13 m0_0 = true:=by decide +kernel
lemma iroot:Imp [] 0 13:=imp_run m0_0 ai4 p0 h0_0
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
section circuit
variable (m:ℕ)
def gv (w:List ℕ) (g:Gate):ℕ:=match g.op,g.inputs with
  | .and,[] => m
  | .and,[i] => w.getD i 0
  | .and,i :: j :: _ => w.getD i 0 &&& w.getD j 0
  | .or,[] => 0
  | .or,[i] => w.getD i 0
  | .or,i :: j :: _ => w.getD i 0 ||| w.getD j 0
  | .not,[] => m
  | .not,i :: _ => w.getD i 0 ^^^ m
  | _,_ => 0
def ex (gs:List Gate) (w:List ℕ):List ℕ:=gs.foldl (fun w g => w ++ [gv m w g]) w
lemma getD_mem {S:Set ℕ} {w:List ℕ} (hw:∀ x ∈ w,x ∈ S) (h0:0 ∈ S) (i:ℕ):w.getD i 0 ∈ S:=by
  rw [List.getD_eq_getElem?_getD]
  by_cases h:i < w.length
  · rw [List.getElem?_eq_getElem h]; exact hw _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none (by omega)]; exact h0
lemma ex_sol {T:ℕ} (gs:List Gate):∀ (w:List ℕ) (S:Set ℕ),(∀ x ∈ w,x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i,(ex m gs w).getD i 0 = T) → Sol Z0 m T gs.length S:=by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i,rfl⟩
    exact .done (getD_mem hw h0 i)
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs:=fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd:=fun i => getD_mem hw h0 i
    have stay:gv m w g ∈ S → Sol Z0 m T (g :: gs).length S:=fun h =>
      (ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append,List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT).mono (by simp) subset_rfl
    have go:Sol Z0 m T gs.length (insert (gv m w g) S):=ih (w ++ [gv m w g]) _ (fun x hx => by
        simp only [List.mem_append,List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop,hlen⟩:=hg g List.mem_cons_self
    obtain ⟨o,l⟩:=g
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d:=false) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d:=true) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay hm
      | i :: _ => exact .un (rd i) go
lemma gv_sub {w:List ℕ} (hw:∀ x ∈ w,x &&& m = x) (g:Gate):gv m w g &&& m = gv m w g:=by
  have rd:∀ i,w.getD i 0 &&& m = w.getD i 0:=fun i => getD_mem (S:={x | x &&& m = x}) hw (by simp) i
  unfold gv
  split
  · simp
  · exact rd _
  · rw [Nat.and_assoc,rd]
  · simp
  · exact rd _
  · rw [Nat.and_or_distrib_right,rd,rd]
  · simp
  · rw [and_neg (Nat.and_self m),rd]
  · simp
lemma ex_sub {gs:List Gate}:∀ {w:List ℕ},(∀ x ∈ w,x &&& m = x) → ∀ x ∈ ex m gs w,x &&& m = x:=by
  induction gs with
  | nil => intro w hw; exact hw
  | cons g gs ih =>
    intro w hw
    refine ih (w:=w ++ [gv m w g]) fun x hx => ?_
    simp only [List.mem_append,List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hw x hx
    · exact gv_sub m hw g
lemma getD_map (w:List ℕ) (b i:ℕ):(w.map (fun x => x.testBit b)).getD i false = (w.getD i 0).testBit b:=by
  rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> simp
lemma gv_bit {b:ℕ} (hb:m.testBit b = true) (w:List ℕ) (g:Gate)
    (hg:g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp) ∧ g.inputs.length ≤ 2) :
    (gv m w g).testBit b = g.op.eval (g.inputs.map fun i => (w.map (fun x => x.testBit b)).getD i false):=by
  have e1:∀ l,GateOp.and.eval l = l.all id:=fun _ => rfl
  have e2:∀ l,GateOp.or.eval l = l.any id:=fun _ => rfl
  have e3:∀ l,GateOp.not.eval l = !(l.headD false):=fun _ => rfl
  obtain ⟨o,l⟩:=g
  obtain ⟨hop,hlen⟩:=hg
  simp only [getD_map]
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  simp only at hlen
  rcases hop with rfl | rfl | rfl
  · match l,hlen with
    | [],_ => simp [gv,e1,hb]
    | [i],_ => simp [gv,e1]
    | [i,j],_ => simp [gv,e1]
  · match l,hlen with
    | [],_ => simp [gv,e2]
    | [i],_ => simp [gv,e2]
    | [i,j],_ => simp [gv,e2]
  · match l,hlen with
    | [],_ => simp [gv,e3,hb]
    | [i],_ => simp [gv,e3,hb]
    | [i,j],_ => simp [gv,e3,hb]
lemma ex_bit {b:ℕ} (hb:m.testBit b = true) (gs:List Gate):∀ (w:List ℕ),
    (∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp) ∧ g.inputs.length ≤ 2) →
    (ex m gs w).map (fun x => x.testBit b) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.map (fun x => x.testBit b)):=by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hg
    rw [List.foldl_cons,← gv_bit m hb w g (hg g List.mem_cons_self)]
    have:=ih (w ++ [gv m w g]) (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    rw [List.map_append] at this
    exact this
end circuit
def f (x:Fin 7 → Bool):Bool:=(x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6)
def EF:ℕ:=(rawP.getD 0 0 &&& rawP.getD 2 0) ||| (rawP.getD 1 0 &&& rawP.getD 3 0) ||| (rawP.getD 0 0 &&& rawP.getD 4 0) ||| (rawP.getD 1 0 &&& rawP.getD 4 0) ||| (rawP.getD 2 0 &&& rawP.getD 4 0) ||| (rawP.getD 0 0 &&& rawP.getD 5 0) ||| (rawP.getD 1 0 &&& rawP.getD 5 0) ||| (rawP.getD 3 0 &&& rawP.getD 5 0) ||| (rawP.getD 0 0 &&& rawP.getD 6 0) ||| (rawP.getD 2 0 &&& rawP.getD 6 0) ||| (rawP.getD 3 0 &&& rawP.getD 6 0) ||| (rawP.getD 5 0 &&& rawP.getD 6 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok:EF &&& mz 0 = tz 0:=by decide +kernel
lemma rawP_len:rawP.length = 7:=rfl
lemma row_list (b:ℕ):List.ofFn (fun v:Fin 7 => (rawP.getD v.val 0).testBit b) = rawP.map (fun x => x.testBit b):=by
  apply List.ext_getElem
  · simp [rawP_len]
  · intro i h1 h2
    have:i < rawP.length:=by simpa using h2
    rw [List.getElem_ofFn,List.getElem_map,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem this]; rfl
lemma f_bit (k:ℕ):EF.testBit k = f (fun v:Fin 7 => (rawP.getD v.val 0).testBit k):=by
  simp only [f,EF,Nat.testBit_or,Nat.testBit_and]
  rfl
theorem bridge (D:PEqualNP.CircuitLowerBounds.Circuit) (hD:PEqualNP.MetaComplexity.FanInTwo D)
    (hf:∀ y:Fin 7 → Bool,D.eval (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) D.size (C (mz 0) (WZ [] 0)):=by
  obtain ⟨gates,out⟩:=D
  let row:ℕ → Fin 7 → Bool:=fun k v => (rawP.getD v.val 0).testBit k
  let init:List ℕ:=rawP.map (· &&& mz 0)
  have hinit_sub:∀ x ∈ init,x &&& mz 0 = x:=by
    intro x hx
    simp only [init,List.mem_map] at hx
    obtain ⟨w,_,rfl⟩:=hx
    rw [Nat.and_assoc,Nat.and_self]
  have hinit_mem:∀ x ∈ init,x ∈ C (mz 0) (WZ [] 0):=by
    intro x hx
    simp only [init,List.mem_map] at hx
    obtain ⟨w,hw,rfl⟩:=hx
    exact Or.inl ⟨w,by simp [rawL,hw],rfl⟩
  have hinit_bits:∀ k,(mz 0).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k):=by
    intro k hk
    simp only [init,List.map_map,Function.comp_def,Nat.testBit_and,hk,Bool.and_true]
    rw [row_list]
  have hout:(ex (mz 0) gates init).getD out 0 = tz 0:=by
    rw [← EF_ok]
    have hsub:∀ x ∈ ex (mz 0) gates init,x &&& mz 0 = x:=ex_sub (mz 0) hinit_sub
    have hsub':=getD_mem (S:={x | x &&& mz 0 = x}) hsub (by simp) out
    apply Nat.eq_of_testBit_eq; intro k
    have e1:=congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1
    rw [← e1,Nat.testBit_and]
    cases hk:(mz 0).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]
      rw [← getD_map,ex_bit (mz 0) hk gates init hD,hinit_bits k hk]
      have h:=hf (row k)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn (row k))).getD out false = f (row k) at h
      rw [h]
      exact (f_bit k).symm
  exact ex_sol (mz 0) gates init (C (mz 0) (WZ [] 0))
    hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl))
    hD ⟨out,hout⟩
lemma lower13 (D:PEqualNP.CircuitLowerBounds.Circuit) (hD:PEqualNP.MetaComplexity.FanInTwo D)
    (hf:∀ y:Fin 7 → Bool,D.eval (List.ofFn y) = f y):13 ≤ D.size:=by
  by_contra h
  exact iroot D.size (by omega) (bridge D hD hf)



open PEqualNP.CircuitLowerBounds

def graph (x:Fin 7 → Bool):Bool:=(x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6)

def witness:List Gate:=[⟨.or,[0,2]⟩,⟨.or,[3,5]⟩,⟨.or,[7,8]⟩,⟨.and,[6,9]⟩,⟨.or,[1,5]⟩,⟨.and,[3,11]⟩,⟨.or,[0,1]⟩,⟨.or,[4,5]⟩,⟨.and,[13,14]⟩,⟨.or,[0,4]⟩,⟨.and,[2,16]⟩,⟨.or,[10,12]⟩,⟨.or,[15,17]⟩,⟨.or,[18,19]⟩]

lemma witness_length:witness.length = 14:=rfl

lemma witness_basis:∀ g ∈ witness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2:=by
  simp [witness]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma witness_correct:∀ x:Fin 7 → Bool,
    Circuit.eval ⟨witness,20⟩ (List.ofFn x) = graph x:=by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma graph_correct:∀ x:Fin 7 → Bool,graph x = decide (∃ i < ([0,2,1,3,0,4,1,4,2,4,0,5,1,5,3,5,0,6,2,6,3,6,5,6]:List ℕ).length / 2,(List.ofFn x).getD (([0,2,1,3,0,4,1,4,2,4,0,5,1,5,3,5,0,6,2,6,3,6,5,6]:List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0,2,1,3,0,4,1,4,2,4,0,5,1,5,3,5,0,6,2,6,3,6,5,6]:List ℕ).getD (2 * i + 1) 0) false = true):=by
  decide +kernel


inductive SolCount (R:ℕ → ℕ) (m T:ℕ):ℕ → ℕ → Set ℕ → Prop
  | done {S:Set ℕ}:T ∈ S → SolCount R m T 0 0 S
  | pad {q n e:ℕ} {S:Set ℕ}:e ≤ 1 → SolCount R m T q n S →
      SolCount R m T (q + 1) (n + e) S
  | un {q n:ℕ} {S:Set ℕ} {a:ℕ}:a ∈ S →
      SolCount R m T q n (insert (a ^^^ m) S) → SolCount R m T (q + 1) (n + 1) S
  | bi {q n:ℕ} {S:Set ℕ} {d:Bool} {a b:ℕ}:a ∈ S → b ∈ S → Al R d a b →
      SolCount R m T q n (insert (op d a b) S) → SolCount R m T (q + 1) n S

lemma SolCount.live {m T q n:ℕ} {S:Set ℕ} (h:SolCount R m T q n S) :
    ∃ k t:ℕ,t ≤ n ∧ k + (n - t) ≤ q ∧
      ∃ S0:Finset ℕ,(S0:Set ℕ) ⊆ S ∧ Live R m T k t S0:=by
  induction h with
  | @done S h => exact ⟨0,0,by omega,by omega,{T},by simpa using h,.stop⟩
  | @pad q n e S he h ih =>
    obtain ⟨k,t,ht,hk,S0,hs,hl⟩:=ih
    exact ⟨k,t,by omega,by omega,S0,hs,hl⟩
  | @un q n S a ha h ih =>
    obtain ⟨k,t,ht,hk,S1,hs,hl⟩:=ih
    by_cases hg:a ^^^ m ∈ S1
    · refine ⟨k + 1,t + 1,by omega,by omega,
        insert a (S1.erase (a ^^^ m)),?_,.un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1,h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k,t,by omega,by omega,S1,
        fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)),hl⟩
  | @bi q n S d a b ha hb hal h ih =>
    obtain ⟨k,t,ht,hk,S1,hs,hl⟩:=ih
    by_cases hg:op d a b ∈ S1
    · by_cases hab:a = b
      · subst hab
        rw [op_self] at hs
        exact ⟨k,t,ht,by omega,S1,
          fun x hx => (hs hx).elim (fun e => e ▸ ha) id,hl⟩
      refine ⟨k + 1,t,ht,by omega,
        insert a (insert b (S1.erase (op d a b))),?_,
        .bi hab hal (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1,h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
    · exact ⟨k,t,ht,by omega,S1,
        fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)),hl⟩

open PEqualNP.CircuitLowerBounds

noncomputable def notCount (gs:List Gate):ℕ:=by
  classical
  exact gs.countP (fun g => decide (g.op = GateOp.not))

lemma notCount_nil:notCount [] = 0:=by simp [notCount]

lemma notCount_cons (g:Gate) (gs:List Gate) :
    notCount (g :: gs) = notCount gs + notCount [g]:=by
  classical
  simp [notCount,List.countP_cons]

lemma notCount_single_le (g:Gate):notCount [g] ≤ 1:=by
  classical
  simp only [notCount,List.countP_cons,List.countP_nil,zero_add]
  split_ifs <;> omega

lemma ex_solCount (m:ℕ) {T:ℕ} (gs:List Gate):∀ (w:List ℕ) (S:Set ℕ),
    (∀ x ∈ w,x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i,(ex m gs w).getD i 0 = T) → SolCount Z0 m T gs.length (notCount gs) S:=by
  classical
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i,rfl⟩
    exact .done (getD_mem hw h0 i)
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs:=fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd:=fun i => getD_mem hw h0 i
    have stay:gv m w g ∈ S → SolCount Z0 m T (g :: gs).length (notCount (g :: gs)) S:=by
      intro hv
      rw [List.length_cons,notCount_cons]
      apply SolCount.pad (notCount_single_le g)
      exact ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append,List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact hv) h0 hm hgs hT
    have go:SolCount Z0 m T gs.length (notCount gs) (insert (gv m w g) S) :=
      ih (w ++ [gv m w g]) _ (fun x hx => by
        simp only [List.mem_append,List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop,hlen⟩:=hg g List.mem_cons_self
    obtain ⟨o,l⟩:=g
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ =>
        simpa [notCount_cons,notCount,op,gv] using
          (SolCount.bi (d:=false) (rd i) (rd j) (al0 _ _ _) go)
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ =>
        simpa [notCount_cons,notCount,op,gv] using
          (SolCount.bi (d:=true) (rd i) (rd j) (al0 _ _ _) go)
    · match l with
      | [] => exact stay hm
      | i :: _ =>
        simpa [notCount_cons,notCount,gv] using (SolCount.un (rd i) go)

lemma bridgeCount (D:PEqualNP.CircuitLowerBounds.Circuit)
    (hD:PEqualNP.MetaComplexity.FanInTwo D)
    (hf:∀ y:Fin 7 → Bool,D.eval (List.ofFn y) = f y) :
    SolCount Z0 (mz 0) (tz 0) D.size (notCount D.gates) (C (mz 0) (WZ [] 0)):=by
  obtain ⟨gates,out⟩:=D
  let row:ℕ → Fin 7 → Bool:=fun k v => (rawP.getD v.val 0).testBit k
  let init:List ℕ:=rawP.map (· &&& mz 0)
  have hinit_sub:∀ x ∈ init,x &&& mz 0 = x:=by
    intro x hx
    simp only [init,List.mem_map] at hx
    obtain ⟨w,_,rfl⟩:=hx
    rw [Nat.and_assoc,Nat.and_self]
  have hinit_mem:∀ x ∈ init,x ∈ C (mz 0) (WZ [] 0):=by
    intro x hx
    simp only [init,List.mem_map] at hx
    obtain ⟨w,hw,rfl⟩:=hx
    exact Or.inl ⟨w,by simp [rawL,hw],rfl⟩
  have hinit_bits:∀ k,(mz 0).testBit k = true →
      init.map (fun x => x.testBit k) = List.ofFn (row k):=by
    intro k hk
    simp only [init,List.map_map,Function.comp_def,Nat.testBit_and,hk,Bool.and_true]
    rw [row_list]
  have hout:(ex (mz 0) gates init).getD out 0 = tz 0:=by
    rw [← EF_ok]
    have hsub:∀ x ∈ ex (mz 0) gates init,x &&& mz 0 = x:=ex_sub (mz 0) hinit_sub
    have hsub':=getD_mem (S:={x | x &&& mz 0 = x}) hsub (by simp) out
    apply Nat.eq_of_testBit_eq
    intro k
    have e1:=congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1
    rw [← e1,Nat.testBit_and]
    cases hk:(mz 0).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]
      rw [← getD_map,ex_bit (mz 0) hk gates init hD,hinit_bits k hk]
      have h:=hf (row k)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn (row k))).getD out false = f (row k) at h
      rw [h]
      exact (f_bit k).symm
  exact ex_solCount (mz 0) gates init (C (mz 0) (WZ [] 0))
    hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl))
    hD ⟨out,hout⟩

lemma circuit_live_count (D:PEqualNP.CircuitLowerBounds.Circuit)
    (hD:PEqualNP.MetaComplexity.FanInTwo D)
    (hf:∀ y:Fin 7 → Bool,D.eval (List.ofFn y) = f y) :
    ∃ k t:ℕ,t ≤ notCount D.gates ∧ k + (notCount D.gates - t) ≤ D.size ∧
      ∃ S:Finset ℕ,(S:Set ℕ) ⊆ C (mz 0) (WZ [] 0) ∧
        Live Z0 (mz 0) (tz 0) k t S :=
  (bridgeCount D hD hf).live

lemma unique_not_count (gs:List Gate)
    (h:∀ i j:Fin gs.length,
      (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j) :
    notCount gs ≤ 1:=by
  classical
  unfold notCount
  induction gs with
  | nil => simp
  | cons g gs ih =>
    by_cases hg:g.op = GateOp.not
    · have hz:gs.countP (fun g => decide (g.op = GateOp.not)) = 0:=by
        apply List.countP_eq_zero.mpr
        intro a ha
        simp only [decide_eq_true_eq]
        intro haNot
        obtain ⟨i,hi⟩:=List.mem_iff_get.mp ha
        have hiNot:(gs.get i).op = GateOp.not:=by rw [hi]; exact haNot
        have hh:=h ⟨0,by simp⟩ i.succ (by simpa using hg)
          (by simpa using hiNot)
        have hv:=congrArg Fin.val hh
        simp at hv
      simp [List.countP_cons,hg,hz]
    · have ht:∀ i j:Fin gs.length,
          (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j:=by
        intro i j hi hj
        exact Fin.succ_inj.mp (h i.succ j.succ (by simpa using hi) (by simpa using hj))
      simpa [List.countP_cons,hg] using ih ht


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma live_certificate_false {E Q:List (ℕ × ℕ)} {Z L k t:ℕ} {S:Finset ℕ}
    (hE:E = [] ∨ ∃ e ∈ six,E = [e] ∧ Imp [] Z L)
    (hp:pOk Z Q = true) (hL:L ≤ 15) (hk:k < L)
    (hI:∀ e ∈ Q,Imp E e.1 e.2)
    (hS:(S:Set ℕ) ⊆ C (mz Z) (WZ E Z))
    (hl:Live Z0 (mz Z) (tz Z) k t S)
    (hmin:∀ q < k,¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)))
    (hb:∃ M:List (ℕ × ℕ),mFull M = true ∧
      ∀ p ∈ M,chk E Q Z (L - 1) t p.1 p.2 = false):False:=by
  simp only [pOk,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hp
  obtain ⟨⟨hp0,hp1⟩,hp2⟩:=hp
  have nb:∀ {x y:ℕ},Nat.beq x y = false → x ≠ y:=fun h e => by rw [e,Nat.beq_refl] at h; simp at h
  have hT:tz Z &&& mz Z = tz Z:=by simp only [tz,nl,Nat.and_assoc,Nat.and_self]
  have hE6:∀ e ∈ E,e ∈ six:=by
    rcases hE with rfl | ⟨e,he,rfl,_⟩
    · simp
    · intro e' he'; simp only [List.mem_singleton] at he'; rw [he']; exact he
  classical
  have hCS:C (mz Z) (S:Set ℕ) ⊆ C (mz Z) (WZ E Z):=by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm:Min Z0 (mz Z) (tz Z) k t S :=
    ⟨hl,fun q' hq' hs => hmin q' hq' (hs.mono le_rfl hCS)⟩
  have hbd:∀ x ∈ S,x &&& mz Z = x:=by
    intro x hx
    rcases hS hx with ⟨w,_,rfl⟩ | h
    · rw [Nat.and_assoc,Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0,h1⟩:=hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW:(S:Set ℕ) ⊆ WZ E Z:=by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj:∀ e ∈ Q,mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1:=by
    intro e he
    obtain ⟨⟨a,b⟩,c⟩:=hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a,nb b,nb c⟩
  have hno:∀ e ∈ Q,∀ q < e.2,¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)):=by
    intro e he q hq hs
    have h3:=(hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk:=hm.size.2
  have hpw:pwr E Z = 0 ∨ pwr E Z ∈ S:=by
    rcases hE with rfl | ⟨e,he,rfl,hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k (by omega) (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w,hw,rfl⟩:=hSW hx
      simp only [rawL,List.mem_append,List.map_cons,List.map_nil,List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w,by simp [rawL,hw],rfl⟩
      · have hx:xw e &&& mz Z ∈ S:=by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨M,hMf,hchk⟩:=hb
  obtain ⟨a1,a2,a3⟩:=avl_spec (PZ Q) (mz Z) (rawL E)
  set v:=(avl (PZ Q) (mz Z) (rawL E)).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub:v.Sublist (avl (PZ Q) (mz Z) (rawL E)):=List.filter_sublist
  have hnd:(v.map W.s).Nodup:=by
    rw [List.Nodup,List.pairwise_map]
    exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
  have hrep:Rep v S:=by
    refine ⟨hnd,Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨w,hw,rfl⟩
      rw [hv,List.mem_filter] at hw; simpa using hw.2
    · intro hx
      obtain ⟨w,hw,rfl⟩:=hSW hx
      obtain ⟨w',hw',e⟩:=a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
      exact ⟨w',by rw [hv,List.mem_filter]; exact ⟨hw',by simpa [e] using hx⟩,e⟩
  have hwok:∀ w ∈ v,WOk (PZ Q) w:=by
    intro w hw
    obtain ⟨x,_,rfl⟩:=a2 w (hsub.subset hw); exact mkW_ok _ _
  have hcod:∀ w ∈ v,w.r = RZ E Z w.s:=by
    intro w hw
    obtain ⟨x,hx,rfl⟩:=a2 w (hsub.subset hw)
    have:x &&& mz Z ∈ WZ E Z:=⟨x,hx,rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ,if_pos this]
  have hgood:∀ w ∈ v,Good (lz Z) w.s:=by
    intro w hw
    obtain ⟨x,hx,rfl⟩:=a2 w (hsub.subset hw); exact wire_good (rawL_sub hE6 hx) Z
  have hPlen:(PZ Q).length = Q.length:=by simp [PZ]
  have hPget:∀ j < (PZ Q).length,(PZ Q).getD j 0 = mz (Q.getD j (0,L - 1)).1 ∧ Q.getD j (0,L - 1) ∈ Q:=by
    intro j hj
    rw [hPlen] at hj
    simp [PZ,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hj]
  have X:Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (tz Z):=by
    refine ⟨fun i hi => lz_lg Z i hi,fun j hj => ?_,?_⟩
    · obtain ⟨e1,e2⟩:=hPget j hj
      have h3:=hproj _ e2
      rw [e1,tz_sub h3.1]; exact h3
    · rw [pL_pk,List.length_map,hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hj]; rfl
  have hcl:Cl (PZ Q) (tz Z) (L - 1) (fun j => L - 1 - (Q.getD j (0,L - 1)).2) S:=by
    intro j hj q hq
    obtain ⟨e1,e2⟩:=hPget j hj
    have hq':q + (L - 1 - (Q.getD j (0,L - 1)).2) < L - 1:=hq
    rw [e1]; exact hno _ e2 q (by omega)
  have hle:=cnt_le X hrep hwok hcl hm (by omega)
  have hst:StOk (PZ Q) (tz Z) (lz Z) (L - 1) (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v S:=by
    refine ⟨hrep,hwok,hgood,_,fun j _ => by omega,hcl,?_⟩
    rw [sumc_eq hwok,pk16,pk_sub]
    intro j hj; have:=hle j hj; omega
  have hcov:∀ i,(lz Z).testBit i = true → (0:ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true:=by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1,m2,t1,t2⟩,_⟩:=lz_lg Z i hli
    obtain ⟨w,hw,hs⟩:=hl.cov m1 m2 t1 t2
    obtain ⟨w',hw',rfl⟩:=hrep.mem.1 hw
    exact ⟨w',hw',by rw [sp_bit,hli,pos_eq,hs]; rfl⟩
  have hsz:=hm.size.1
  have hcard:=hrep.card
  have hble:Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true:=Nat.ble_eq_true_of_le (by
    change v.length ≤ L - 1 + 1 - t; omega)
  have hhas:hasP (pwr E Z) v = true:=hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all:∀ p ∈ M,topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false:=by
    intro p hpM
    have h2:=hchk p hpM
    simp only [chk,frc_eq,st_eq] at h2
    have h3:=anySub_false (by simp) h2 v hsub hcov
    simp only [startv,bR,hhas,hble,Bool.cond_true] at h3
    exact child_sound X (f:=fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topC_sound X (RZ_R E Z) (RZ_R2 E Z) hMf all hst hcod (by omega) hl ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine hmin q hq (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx


noncomputable def indexMask (xs:List Nat):Nat :=
  bitsOf (xs.map fun i => (0,i))

lemma indexMask_mem {xs:List Nat} {i:Nat}
    (h:(indexMask xs).testBit i = true):i ∈ xs:=by
  obtain ⟨s,hs,he⟩:=bitsOf_bit h
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hs
  change j = i at he
  exact he ▸ hj

lemma mem_of_indexMask {xs:List Nat} {n i:Nat}
    (h:indexMask xs = 2 ^ n - 1) (hi:i < n):i ∈ xs:=by
  apply indexMask_mem
  rw [h,Nat.testBit_two_pow_sub_one]
  simp only [hi,decide_true]

noncomputable def forceLook (fuel k t z:ℕ) (v:List W):Bool :=
  strictSt initL fun l => strictSt initM fun m => strictSt initG fun g => strictSt fuel fun fuel =>
    strictSt k fun k => strictSt t fun t => strictSt z fun z =>
    frcAll v fun v => look l m g fuel k t z v
lemma forceLook_eq (fuel k t z:ℕ) (v:List W) :
    forceLook fuel k t z v = look initL initM initG fuel k t z v:=by
  simp only [forceLook,strictSt_eq,frcAll_eq]



noncomputable def unaryRows:List (ℕ × ℕ × ℕ × List W):=(List.range 54).map unaryRow
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def unaryTableChecked:∀ p ∈ unaryRows,
    look initL initM initG 13 p.1 p.2.1 p.2.2.1 p.2.2.2 = false:=by
  intro p hp
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hp
  have hb:i < 54:=List.mem_range.mp hi
  interval_cases i
  all_goals
    rw [← forceLook_eq]
    decide +kernel

noncomputable def binCheck (i:ℕ):Bool :=
  let p:=binRow i
  !(if binMode i = 0 then
    look1 initL initM initG 13 12 p.1 p.2.1 p.2.2.1 p.2.2.2
  else look initL initM initG 13 p.1 p.2.1 p.2.2.1 p.2.2.2)
noncomputable def forceBinCheck (i:ℕ):Bool :=
  let p:=binRow i
  strictSt initL fun l => strictSt initM fun m => strictSt initG fun g =>
    strictSt p.1 fun k => strictSt p.2.1 fun t => strictSt p.2.2.1 fun z =>
    frcAll p.2.2.2 fun v =>
      !(if binMode i = 0 then look1 l m g 13 12 k t z v
      else look l m g 13 k t z v)
lemma forceBinCheck_eq (i:ℕ):forceBinCheck i = binCheck i:=by
  simp only [forceBinCheck,binCheck,strictSt_eq,frcAll_eq]
noncomputable def binGroupCheck (q:List ℕ):Bool:=q.all forceBinCheck

noncomputable def binLargeGroups:List (List ℕ):=[
  [369],
  [430],
  [452],
  [932],
  [1004],
  [2555],
  [2959]
]
noncomputable def binLane0Groups:List (List ℕ):=[
  [450],
  [1415],
  [427],
  [632],
  [448],
  [1310],
  [2592],
  [2453],
  [457],
  [67],
  [264],
  [624],
  [549],
  [743],
  [53],
  [239],
  [1909],
  [1912],
  [275],
  [447],
  [459],
  [1001],
  [1477],
  [58],
  [244],
  [630],
  [820],
  [1461],
  [73],
  [2455],
  [611],
  [440],
  [994],
  [1626],
  [2047],
  [436],
  [2557],
  [627],
  [823],
  [262],
  [2324],
  [2322],
  [815],
  [1769],
  [806],
  [997],
  [267],
  [801],
  [0],
  [76],
  [2423],
  [3080],
  [1002],
  [1152],
  [2155],
  [253],
  [1257],
  [2288],
  [2192],
  [626],
  [822],
  [1298],
  [2045],
  [2814],
  [2907,2908,2909,2910,2911,2912,2913,2914,2915,2916,2917,2918,2919,2920,2921,2922,2923,2924,2925,2926,2927,2928,2929,2930,2931,2932],
  [2018,2019,2020,2021,2022,2023,2024,2025,2026,2027,2028,2029,2030,2031,2032,2033,2034,2035,2036,2037,2038,2039,2040,2041,2042],
  [470,471,472,473,474,475],
  [1072,1073,1074,1075,1076,1077,1078,1079,1080,1081,1082,1083,1084,1085,1086,1087,1088,1089,1090,1091,1092,1093,1094,1095],
  [2220,2221,2222,2223,2224,2225,2226,2227,2228,2229,2230,2231,2232,2233,2234,2235,2236,2237,2238,2239,2240,2241,2242,2243,2244,2245,2246,2247,2248,2249,2250,2251,2252,2253,2254,2255,2256,2257,2258,2259,2260],
  [24,25,26,27,28,29],
  [1643,1644,1645,1646,1647,1648,1649,1650,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1666,1667,1668,1669,1670,1671,1672],
  [2969,2970,2971,2972,2973,2974,2975,2976,2977,2978,2979,2980,2981,2982,2983,2984,2985,2986,2987],
  [1937,1938,1939,1940,1941,1942,1943,1944,1945],
  [2766,2767,2768,2769,2770,2771,2772,2773,2774,2775,2776,2777,2778,2779,2780,2781,2782,2783,2784,2785,2786,2787,2788,2789,2790,2791],
  [287,288,289],
  [2998,2999,3000,3001,3002,3003,3004,3005,3006,3007,3008,3009,3010,3011,3012,3013,3014,3015,3016,3017],
  [906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927,928,929],
  [1622],
  [210,211,212,213,214,215],
  [953,954,955],
  [453,454],
  [1005,1006],
  [2515,2516,2517,2518,2519,2520,2521,2522,2523,2524,2525,2526,2527,2528,2529,2530,2531,2532,2533,2534,2535,2536,2537,2538,2539,2540],
  [1781,1782,1783,1784,1785,1786,1787,1788,1789,1790,1791],
  [2073,2074,2075,2076,2077,2078,2079,2080,2081,2082,2083,2084,2085,2086],
  [400,401,402,403],
  [2087,2088,2089,2090,2091,2092,2093,2094,2095,2096,2097,2098,2099,2100,2101,2102,2103,2104,2105,2106,2107,2108,2109,2110,2111,2112,2113,2114,2115,2116,2117,2118,2119],
  [3046,3047,3048,3049,3050,3051,3052,3053,3054,3055,3056,3057,3058,3059,3060,3061,3062,3063,3064,3065,3066,3067,3068,3069,3070,3071,3072,3073,3074],
  [2397,2398,2399,2400,2401,2402,2403,2404,2405,2406,2407,2408,2409,2410,2411,2412,2413,2414,2415,2416,2417],
  [1,2,3,4,5,6,7,8,9,10,11],
  [1209,1210,1211,1212,1213,1214,1215,1216,1217,1218,1219,1220,1221,1222,1223,1224,1225,1226,1227,1228,1229,1230,1231,1232,1233,1234,1235,1236,1237,1238,1239,1240,1241,1242,1243,1244,1245,1246,1247,1248],
  [1498,1499,1500,1501,1502,1503,1504,1505,1506,1507,1508,1509,1510,1511,1512,1513,1514,1515,1516,1517,1518,1519,1520,1521,1522,1523,1524,1525,1526,1527,1528,1529,1530,1531,1532,1533,1534,1535,1536,1537,1538,1539],
  [1427,1428],
  [844,845,846,847,848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863,864,865,866,867,868,869,870,871,872,873,874],
  [2196],
  [3161,3162,3163,3164,3165,3166,3167,3168,3169,3170,3171,3172,3173,3174,3175,3176,3177],
  [2368,2369,2370,2371,2372,2373,2374,2375,2376,2377,2378,2379,2380,2381,2382,2383,2384,2385,2386,2387,2388,2389,2390,2391,2392,2393,2394,2395,2396],
  [1156,1157,1158],
  [1337,1338,1339,1340,1341,1342,1343,1344],
  [2723,2724,2725,2726,2727,2728],
  [1422],
  [1946,1947,1948,1949,1950,1951,1952,1953,1954,1955,1956,1957,1958,1959,1960,1961,1962,1963,1964,1965,1966,1967,1968,1969,1970,1971,1972,1973,1974,1975,1976,1977,1978,1979,1980,1981],
  [2213,2214,2215,2216,2217,2218,2219],
  [1117,1118,1119,1120,1121],
  [1882,1883,1884,1885,1886,1887,1888,1889,1890,1891,1892,1893],
  [2992,2993,2994,2995,2996,2997],
  [2200,2201,2202,2203,2204,2205,2206,2207,2208,2209,2210,2211,2212],
  [1617,1618,1619],
  [718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740],
  [117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149],
  [3122,3123,3124,3125,3126,3127,3128,3129,3130,3131,3132,3133,3134,3135,3136,3137,3138,3139,3140,3141,3142,3143,3144,3145],
  [300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,327,328,329,330,331],
  [940,941,942],
  [1329,1330,1331,1332],
  [2647,2648,2649,2650,2651,2652,2653,2654,2655,2656,2657,2658,2659,2660,2661,2662,2663,2664,2665,2666,2667,2668,2669,2670,2671,2672,2673,2674,2675],
  [3107,3108,3109,3110,3111,3112],
  [1015,1016,1017,1018,1019,1020,1021],
  [1627,1628,1629,1630,1631,1632,1633,1634,1635,1636],
  [2498,2499,2500,2501,2502,2503,2504,2505,2506,2507,2508,2509,2510,2511,2512,2513,2514],
  [2863,2864,2865,2866,2867,2868,2869,2870,2871,2872,2873,2874,2875,2876,2877,2878,2879,2880,2881,2882,2883,2884],
  [1096,1097,1098],
  [1377,1378,1379,1380,1381,1382,1383,1384,1385,1386,1387,1388,1389,1390,1391,1392,1393,1394,1395,1396,1397,1398,1399],
  [2331,2332,2333],
  [77,78],
  [254,255],
  [1438,1439,1440,1441,1442,1443,1444,1445,1446,1447,1448,1449,1450,1451,1452,1453,1454],
  [2815,2816,2817,2818,2819,2820,2821,2822,2823,2824,2825,2826,2827,2828,2829,2830,2831,2832,2833,2834,2835,2836,2837,2838,2839,2840,2841,2842,2843,2844],
  [1429,1430,1431],
  [2159,2160,2161],
  [433],
  [1874,1875,1876],
  [100,101,102],
  [1732,1733,1734,1735],
  [515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538],
  [1424,1425],
  [608,609],
  [798,799],
  [2012,2013,2014,2015,2016,2017],
  [1143,1144,1145],
  [1569],
  [2011],
  [2151],
  [2850,2851,2852,2853,2854,2855,2856,2857,2858,2859],
  [1578,1579,1580,1581,1582,1583],
  [1773],
  [2558,2559,2560],
  [1729,1730,1731],
  [437,438],
  [559,560,561],
  [1306,1307],
  [2289,2290,2291,2292,2293,2294,2295],
  [2689,2690,2691,2692,2693,2694],
  [604],
  [1615,1616],
  [3081,3082,3083,3084,3085,3086,3087,3088,3089,3090,3091,3092,3093,3094,3095,3096,3097,3098,3099,3100,3101,3102,3103,3104,3105,3106],
  [198,199,200,201,202,203],
  [1465,1466],
  [1913,1914],
  [1637,1638,1639,1640,1641,1642],
  [646,647,648],
  [2435,2436,2437,2438,2439,2440,2441,2442,2443,2444,2445,2446,2447,2448,2449,2450,2451,2452],
  [82],
  [251],
  [2472,2473],
  [1165],
  [188,189,190,191,192,193,194,195,196,197],
  [768,769,770,771],
  [445],
  [61,62],
  [744,745,746,747,748],
  [455],
  [242,243],
  [2860,2861,2862],
  [956,957,958,959],
  [988],
  [54,55],
  [2165,2166,2167],
  [377,378,379],
  [620],
  [1099,1100,1101],
  [393,394,395],
  [567,568],
  [1175,1176,1177,1178,1179,1180,1181,1182],
  [404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424],
  [2326,2327],
  [575,576,577,578],
  [804,805],
  [109,110],
  [2162,2163,2164],
  [89,90],
  [272,273],
  [2060,2061,2062,2063,2064,2065,2066,2067,2068],
  [765,766,767],
  [1464],
  [1768],
  [1727,1728],
  [1160,1161,1162],
  [777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796],
  [2052],
  [1609,1610,1611],
  [103,104,105,106,107,108],
  [65,66],
  [562,563],
  [283,284,285,286],
  [1470,1471],
  [2454],
  [240,241],
  [1311],
  [749,750],
  [216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238],
  [993],
  [1775,1776],
  [1432,1433,1434],
  [1316],
  [2328],
  [607],
  [964,965,966,967,968,969,970,971,972,973,974,975,976,977,978,979,980,981,982,983],
  [1931,1932,1933,1934,1935,1936],
  [2963,2964,2965],
  [1872,1873],
  [761,762],
  [460,461,462,463,464,465,466,467],
  [1472],
  [1102,1103],
  [616],
  [64],
  [59,60],
  [245,246],
  [290,291,292,293,294],
  [173,174,175,176,177,178,179,180,181,182,183,184,185,186],
  [356,357,358,359,360,361,362,363,364,365,366,367,368],
  [1312],
  [2556],
  [385,386],
  [1915,1916],
  [74,75],
  [984],
  [278,279,280,281,282],
  [2323],
  [390],
  [1303,1304],
  [1623,1624],
  [992],
  [1770,1771],
  [451],
  [1009],
  [949],
  [2156],
  [1854,1855,1856,1857,1858,1859,1860,1861,1862,1863,1864,1865,1866,1867],
  [79],
  [1467],
  [1146,1147,1148],
  [1462,1463],
  [1274,1275,1276,1277,1278,1279,1280,1281,1282,1283,1284,1285,1286,1287,1288,1289,1290,1291,1292,1293,1294,1295],
  [268],
  [807],
  [1612],
  [2467,2468,2469,2470,2471],
  [612,613],
  [265,266],
  [1478,1479],
  [2154],
  [821],
  [270],
  [3075,3076,3077,3078,3079],
  [1249,1250,1251,1252,1253,1254,1255,1256],
  [458],
  [1153,1154],
  [986],
  [1308],
  [2845],
  [605],
  [610],
  [814],
  [81],
  [93],
  [1301],
  [800],
  [68],
  [72],
  [1919],
  [70],
  [1476],
  [930,931],
  [741,742],
  [2148,2149]
]
noncomputable def binLane1Groups:List (List ℕ):=[
  [1008],
  [2150],
  [606],
  [816],
  [1010],
  [2330],
  [2457],
  [2593],
  [2721],
  [1003],
  [1313],
  [2325],
  [824],
  [1719],
  [1868],
  [63],
  [1300],
  [1778],
  [86],
  [2684],
  [987],
  [1774],
  [1918],
  [2193],
  [1473],
  [2199],
  [629],
  [819],
  [1907],
  [258],
  [2846],
  [813],
  [88],
  [271],
  [71],
  [260],
  [998],
  [2591],
  [69],
  [2460],
  [1318],
  [1320],
  [635],
  [1302],
  [618],
  [435],
  [94],
  [623],
  [1764],
  [187],
  [257],
  [456],
  [1142],
  [1426],
  [80],
  [84],
  [277],
  [1480],
  [621],
  [803],
  [1772],
  [1920],
  [1309],
  [1159],
  [751,752,753],
  [875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895,896,897,898,899,900,901,902,903,904,905],
  [204,205,206,207,208,209],
  [476,477,478,479,480,481,482,483,484],
  [1877,1878,1879,1880,1881],
  [772,773,774,775,776],
  [2168,2169,2170,2171,2172,2173,2174,2175,2176,2177,2178,2179,2180,2181,2182,2183,2184],
  [2424,2425,2426,2427,2428,2429,2430,2431,2432,2433,2434],
  [1046,1047,1048,1049,1050,1051,1052,1053,1054,1055,1056,1057,1058,1059,1060,1061,1062,1063,1064,1065,1066,1067,1068,1069,1070,1071],
  [2565,2566,2567,2568,2569],
  [111,112,113,114,115,116],
  [1345,1346,1347,1348,1349,1350,1351,1352,1353,1354,1355,1356,1357,1358,1359,1360,1361,1362,1363,1364,1365,1366,1367,1368,1369,1370,1371,1372,1373,1374,1375,1376],
  [579,580,581,582,583],
  [960,961,962,963],
  [2053],
  [370,371,372,373,374],
  [3113,3114,3115,3116,3117,3118,3119,3120,3121],
  [649,650,651,652,653,654,655,656,657,658,659],
  [1022,1023,1024,1025,1026,1027,1028,1029,1030,1031,1032,1033,1034,1035,1036,1037,1038,1039,1040,1041,1042,1043,1044,1045],
  [2885,2886,2887,2888,2889,2890,2891,2892,2893,2894,2895,2896,2897,2898,2899,2900,2901,2902,2903,2904,2905,2906],
  [2334,2335,2336,2337,2338,2339,2340,2341,2342],
  [2343,2344,2345,2346,2347,2348,2349,2350,2351,2352,2353,2354,2355,2356,2357,2358,2359,2360,2361,2362,2363,2364,2365,2366,2367],
  [1418,1419,1420],
  [2609,2610,2611,2612,2613,2614,2615],
  [1823,1824,1825,1826,1827,1828,1829,1830,1831,1832,1833,1834,1835,1836,1837,1838,1839,1840,1841,1842,1843,1844,1845,1846,1847,1848,1849,1850,1851,1852,1853],
  [2729,2730,2731,2732,2733,2734,2735,2736,2737,2738,2739],
  [396,397,398,399],
  [1492,1493,1494,1495,1496,1497],
  [2474,2475,2476],
  [2152,2153],
  [1475],
  [2792,2793,2794,2795,2796,2797,2798,2799,2800,2801,2802,2803,2804,2805,2806,2807,2808,2809,2810,2811,2812],
  [295,296,297,298,299],
  [2740,2741,2742,2743,2744,2745,2746,2747,2748,2749,2750,2751,2752,2753,2754,2755,2756,2757,2758,2759,2760,2761,2762,2763,2764,2765],
  [1258,1259,1260,1261,1262,1263,1264,1265,1266],
  [2120,2121,2122,2123,2124,2125,2126,2127,2128,2129,2130,2131,2132,2133,2134,2135,2136,2137,2138,2139,2140,2141,2142,2143,2144,2145,2146,2147],
  [1183,1184,1185,1186,1187,1188,1189,1190,1191,1192,1193,1194,1195,1196,1197,1198,1199,1200,1201,1202,1203,1204,1205,1206,1207,1208],
  [1673,1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,1686,1687,1688,1689,1690,1691,1692,1693,1694,1695,1696,1697,1698,1699,1700,1701,1702,1703,1704],
  [2158],
  [150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172],
  [1011,1012,1013,1014],
  [2966,2967,2968],
  [555,556,557,558],
  [95,96,97,98,99],
  [2477,2478,2479,2480,2481,2482,2483,2484,2485,2486,2487,2488,2489,2490,2491,2492,2493,2494,2495,2496,2497],
  [757,758,759,760],
  [840,841,842,843],
  [425,426],
  [332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355],
  [1104,1105,1106],
  [2461,2462,2463,2464,2465,2466],
  [3146,3147,3148,3149,3150,3151,3152,3153,3154,3155,3156,3157,3158,3159,3160],
  [2616,2617,2618,2619,2620,2621,2622,2623,2624,2625,2626,2627,2628,2629,2630,2631,2632,2633,2634,2635,2636,2637,2638,2639,2640,2641,2642,2643,2644,2645,2646],
  [18,19,20,21,22,23],
  [1792,1793,1794,1795,1796,1797,1798,1799,1800,1801,1802,1803,1804,1805,1806,1807,1808,1809,1810,1811,1812,1813,1814,1815,1816,1817,1818,1819,1820,1821,1822],
  [636,637,638,639,640,641,642,643,644,645],
  [1740,1741,1742,1743,1744,1745,1746,1747,1748,1749,1750,1751,1752,1753,1754,1755,1756,1757],
  [1267,1268,1269,1270,1271,1272,1273],
  [660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690],
  [485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511,512,513,514],
  [1113,1114,1115,1116],
  [1982,1983,1984,1985,1986,1987,1988,1989,1990,1991,1992,1993,1994,1995,1996,1997,1998,1999,2000,2001,2002,2003,2004,2005,2006,2007,2008,2009,2010],
  [2594,2595,2596,2597,2598,2599,2600],
  [3018,3019,3020,3021,3022,3023,3024,3025,3026,3027,3028,3029,3030,3031,3032,3033,3034,3035,3036,3037,3038,3039,3040,3041,3042,3043,3044,3045],
  [92],
  [269],
  [985],
  [85],
  [274],
  [2561,2562,2563,2564],
  [248,249,250],
  [443],
  [763,764],
  [991],
  [2296,2297,2298,2299,2300,2301,2302,2303,2304,2305,2306,2307,2308,2309,2310,2311,2312,2313,2314,2315,2316,2317,2318,2319,2320,2321],
  [1779,1780],
  [1296],
  [1723,1724,1725,1726],
  [383,384],
  [946,947,948],
  [1917],
  [1149,1150,1151],
  [431],
  [995,996],
  [691,692,693,694,695,696,697,698,699,700,701,702,703,704,705,706,707,708,709,710,711,712,713,714,715,716,717],
  [1584,1585,1586,1587,1588,1589,1590,1591,1592,1593,1594,1595,1596,1597,1598,1599,1600,1601,1602,1603,1604,1605,1606,1607,1608],
  [468,469],
  [550,551,552,553,554],
  [569,570,571],
  [1570,1571,1572,1573,1574,1575,1576,1577],
  [825,826,827,828,829,830,831,832],
  [810,811],
  [1613,1614],
  [2933,2934,2935,2936,2937,2938,2939,2940,2941,2942,2943,2944,2945,2946,2947,2948,2949,2950,2951,2952,2953,2954,2955,2956,2957,2958],
  [2057,2058,2059],
  [380,381,382],
  [1166,1167,1168,1169,1170,1171,1172,1173,1174],
  [1736,1737,1738,1739],
  [1435,1436,1437],
  [938,939],
  [1155],
  [1333,1334,1335,1336],
  [933,934,935],
  [989],
  [2960,2961,2962],
  [1107,1108,1109],
  [1007],
  [2685,2686,2687,2688],
  [999,1000],
  [12,13,14,15,16,17],
  [444],
  [2847,2848,2849],
  [56,57],
  [2050,2051],
  [802],
  [2695,2696,2697,2698,2699,2700,2701,2702,2703,2704,2705,2706,2707,2708,2709,2710,2711,2712,2713,2714,2715,2716,2717],
  [2541,2542,2543,2544,2545,2546,2547,2548,2549,2550,2551,2552,2553,2554],
  [797],
  [943,944,945],
  [572,573,574],
  [1314,1315],
  [428,429],
  [2589,2590],
  [1929,1930],
  [564,565,566],
  [1540,1541,1542,1543,1544,1545,1546,1547,1548,1549,1550,1551,1552,1553,1554,1555,1556,1557,1558,1559,1560,1561,1562,1563,1564,1565,1566,1567,1568],
  [1416,1417],
  [808,809],
  [1910,1911],
  [2988,2989,2990,2991],
  [1720,1721,1722],
  [2570,2571,2572,2573,2574,2575,2576,2577,2578,2579,2580,2581,2582,2583,2584,2585,2586,2587,2588],
  [2719],
  [1621],
  [1305],
  [1321,1322,1323,1324,1325,1326,1327,1328],
  [584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603],
  [1468,1469],
  [2197,2198],
  [1110,1111,1112],
  [1869,1870,1871],
  [2722],
  [449],
  [1400,1401,1402,1403,1404,1405,1406,1407,1408,1409,1410,1411,1412,1413,1414],
  [2261,2262,2263,2264,2265,2266,2267,2268,2269,2270,2271,2272,2273,2274,2275,2276,2277,2278,2279,2280,2281,2282,2283,2284,2285,2286,2287],
  [754,755,756],
  [439],
  [247],
  [441,442],
  [833,834,835,836,837,838,839],
  [1122,1123,1124,1125,1126,1127,1128,1129,1130,1131,1132,1133,1134,1135,1136,1137,1138,1139,1140,1141],
  [375,376],
  [1481,1482,1483,1484,1485,1486,1487,1488,1489,1490,1491],
  [614],
  [2601,2602,2603,2604,2605,2606,2607,2608],
  [30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52],
  [3178,3179,3180,3181,3182,3183,3184,3185,3186,3187,3188,3189,3190,3191,3192,3193,3194,3195,3196,3197,3198],
  [951,952],
  [2157],
  [617],
  [391,392],
  [2720],
  [434],
  [387,388],
  [936,937],
  [1625],
  [1894,1895,1896,1897,1898,1899,1900,1901,1902,1903,1904,1905,1906],
  [1765,1766],
  [2329],
  [1705,1706,1707,1708,1709,1710,1711,1712,1713,1714,1715,1716,1717,1718],
  [1758,1759,1760,1761,1762,1763],
  [2048,2049],
  [432],
  [1921,1922,1923,1924,1925,1926,1927,1928],
  [1317],
  [1163,1164],
  [950],
  [389],
  [2069,2070,2071,2072],
  [2185,2186,2187,2188,2189,2190,2191],
  [539,540,541,542,543,544,545,546,547,548],
  [1767],
  [817,818],
  [1423],
  [2676,2677,2678,2679,2680,2681,2682,2683],
  [1777],
  [252],
  [256],
  [1455,1456,1457,1458,1459,1460],
  [2458,2459],
  [91],
  [615],
  [633,634],
  [2054,2055,2056],
  [2194,2195],
  [1421],
  [2718],
  [628],
  [631],
  [87],
  [1620],
  [2418,2419,2420,2421,2422],
  [990],
  [1474],
  [446],
  [625],
  [619],
  [2456],
  [812],
  [83],
  [276],
  [1319],
  [1297],
  [622],
  [1908],
  [261],
  [259],
  [2043,2044],
  [263],
  [1299],
  [2046],
  [2813]
]
noncomputable def binGroups:List (List ℕ) :=
  binLargeGroups ++ (binLane0Groups ++ binLane1Groups)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def binGroupsCover:indexMask (binGroups.flatMap id) = 2 ^ 3199 - 1:=by
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def binLargeGroupsChecked:∀ q ∈ binLargeGroups,binGroupCheck q = true:=by
  intro q hq
  simp only [binLargeGroups,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

noncomputable def binaryRows:List CutState:=(List.range 42).map rootRow
noncomputable def binFRows (z:Nat):List CutState:=(binFCandidates z).map binRow
noncomputable def binGRows (z:Nat):List CutState:=(binGCandidates z).map binRow
noncomputable def rootRows (z:Nat):List CutState:=(rootCandidates z).map rootRow
noncomputable def unaryBucketRows (z:Nat):List CutState:=(unaryCandidates z).map unaryRow

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def binBucketsBound:binBudgetBucketChunks.all (fun c => c.all (fun xs => xs.all (fun j => decide (j < 3199)))) = true:=by
  have h:binBudgetBucketChunks.toList.all (fun c => c.toList.all (fun xs => xs.all (fun j => decide (j < 3199)))) = true:=by
    decide +kernel
  simpa only [Array.all_toList] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def rootBucketsBound:rootBudgetBucketChunks.all (fun c => c.all (fun xs => xs.all (fun j => decide (j < 42)))) = true:=by
  have h:rootBudgetBucketChunks.toList.all (fun c => c.toList.all (fun xs => xs.all (fun j => decide (j < 42)))) = true:=by
    decide +kernel
  simpa only [Array.all_toList] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def unaryBucketsBound:unaryBudgetBucketChunks.all (fun c => c.all (fun xs => xs.all (fun j => decide (j < 54)))) = true:=by
  have h:unaryBudgetBucketChunks.toList.all (fun c => c.toList.all (fun xs => xs.all (fun j => decide (j < 54)))) = true:=by
    decide +kernel
  simpa only [Array.all_toList] using h


noncomputable def cutF:Nat → Nat → Nat → List W → Bool:=look initL initM initG 13
noncomputable def cutG:Nat → Nat → Nat → List W → Bool:=look1 initL initM initG 13 12
noncomputable def rootG:Nat → Nat → Nat → List W → Bool:=look1 initL initM initG 13 13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def unaryBucketCoverage :
    chkCut (patchBudget cutF unaryBucketRows) rootG [] (pr ac4 0) 0 13 1 0 1 = false:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def binaryBucketCoverage :
    chkCut cutF (patchBudget rootG rootRows) [] (pr ac4 0) 0 13 1 FF 0 = false:=by decide +kernel

noncomputable def parentBucketGoal (F G:Nat → Nat → Nat → List W → Bool) (i:Nat):Prop :=
  look1Cut (patchBudget F binFRows) (patchBudget G binGRows)
    initL initM initG (rootRow i).1 (rootRow i).2.1 (rootRow i).2.2.1 (rootRow i).2.2.2 = false

noncomputable def forceParentBucket (F G:Nat → Nat → Nat → List W → Bool) (i:Nat):Bool :=
  let p:=rootRow i
  strictSt initL fun l => strictSt initM fun m => strictSt initG fun g =>
    strictSt p.1 fun k => strictSt p.2.1 fun t => strictSt p.2.2.1 fun z =>
      frcAll p.2.2.2 fun v => look1Cut (patchBudget F binFRows) (patchBudget G binGRows) l m g k t z v

lemma forceParentBucket_eq (F G:Nat → Nat → Nat → List W → Bool) (i:Nat) :
    forceParentBucket F G i = look1Cut (patchBudget F binFRows) (patchBudget G binGRows)
      initL initM initG (rootRow i).1 (rootRow i).2.1 (rootRow i).2.2.1 (rootRow i).2.2.2:=by
  simp only [forceParentBucket,strictSt_eq,frcAll_eq]

lemma parentFromForce (F G:Nat → Nat → Nat → List W → Bool) (i:Nat)
    (h:forceParentBucket F G i = false):parentBucketGoal F G i:=by
  simpa only [forceParentBucket_eq,parentBucketGoal] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket0:parentBucketGoal cutF cutG 0 :=
  parentFromForce cutF cutG 0 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket1:parentBucketGoal cutF cutG 1 :=
  parentFromForce cutF cutG 1 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket2:parentBucketGoal cutF cutG 2 :=
  parentFromForce cutF cutG 2 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket3:parentBucketGoal cutF cutG 3 :=
  parentFromForce cutF cutG 3 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket4:parentBucketGoal cutF cutG 4 :=
  parentFromForce cutF cutG 4 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket5:parentBucketGoal cutF cutG 5 :=
  parentFromForce cutF cutG 5 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket6:parentBucketGoal cutF cutG 6 :=
  parentFromForce cutF cutG 6 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket7:parentBucketGoal cutF cutG 7 :=
  parentFromForce cutF cutG 7 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket8:parentBucketGoal cutF cutG 8 :=
  parentFromForce cutF cutG 8 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket9:parentBucketGoal cutF cutG 9 :=
  parentFromForce cutF cutG 9 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket10:parentBucketGoal cutF cutG 10 :=
  parentFromForce cutF cutG 10 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket11:parentBucketGoal cutF cutG 11 :=
  parentFromForce cutF cutG 11 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket12:parentBucketGoal cutF cutG 12 :=
  parentFromForce cutF cutG 12 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket13:parentBucketGoal cutF cutG 13 :=
  parentFromForce cutF cutG 13 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket14:parentBucketGoal cutF cutG 14 :=
  parentFromForce cutF cutG 14 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket15:parentBucketGoal cutF cutG 15 :=
  parentFromForce cutF cutG 15 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket16:parentBucketGoal cutF cutG 16 :=
  parentFromForce cutF cutG 16 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket17:parentBucketGoal cutF cutG 17 :=
  parentFromForce cutF cutG 17 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket18:parentBucketGoal cutF cutG 18 :=
  parentFromForce cutF cutG 18 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket19:parentBucketGoal cutF cutG 19 :=
  parentFromForce cutF cutG 19 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket20:parentBucketGoal cutF cutG 20 :=
  parentFromForce cutF cutG 20 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket21:parentBucketGoal cutF cutG 21 :=
  parentFromForce cutF cutG 21 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket22:parentBucketGoal cutF cutG 22 :=
  parentFromForce cutF cutG 22 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket23:parentBucketGoal cutF cutG 23 :=
  parentFromForce cutF cutG 23 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket24:parentBucketGoal cutF cutG 24 :=
  parentFromForce cutF cutG 24 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket25:parentBucketGoal cutF cutG 25 :=
  parentFromForce cutF cutG 25 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket26:parentBucketGoal cutF cutG 26 :=
  parentFromForce cutF cutG 26 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket27:parentBucketGoal cutF cutG 27 :=
  parentFromForce cutF cutG 27 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket28:parentBucketGoal cutF cutG 28 :=
  parentFromForce cutF cutG 28 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket29:parentBucketGoal cutF cutG 29 :=
  parentFromForce cutF cutG 29 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket30:parentBucketGoal cutF cutG 30 :=
  parentFromForce cutF cutG 30 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket31:parentBucketGoal cutF cutG 31 :=
  parentFromForce cutF cutG 31 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket32:parentBucketGoal cutF cutG 32 :=
  parentFromForce cutF cutG 32 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket33:parentBucketGoal cutF cutG 33 :=
  parentFromForce cutF cutG 33 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket34:parentBucketGoal cutF cutG 34 :=
  parentFromForce cutF cutG 34 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket35:parentBucketGoal cutF cutG 35 :=
  parentFromForce cutF cutG 35 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket36:parentBucketGoal cutF cutG 36 :=
  parentFromForce cutF cutG 36 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket37:parentBucketGoal cutF cutG 37 :=
  parentFromForce cutF cutG 37 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket38:parentBucketGoal cutF cutG 38 :=
  parentFromForce cutF cutG 38 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket39:parentBucketGoal cutF cutG 39 :=
  parentFromForce cutF cutG 39 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket40:parentBucketGoal cutF cutG 40 :=
  parentFromForce cutF cutG 40 (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def parentBucket41:parentBucketGoal cutF cutG 41 :=
  parentFromForce cutF cutG 41 (by decide +kernel)

lemma parentBucketCoverage (i:Nat) (hi:i < 42):parentBucketGoal cutF cutG i:=by
  have h:i ∈ List.range 42:=List.mem_range.2 hi
  change i ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41] at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact parentBucket0
  · exact parentBucket1
  · exact parentBucket2
  · exact parentBucket3
  · exact parentBucket4
  · exact parentBucket5
  · exact parentBucket6
  · exact parentBucket7
  · exact parentBucket8
  · exact parentBucket9
  · exact parentBucket10
  · exact parentBucket11
  · exact parentBucket12
  · exact parentBucket13
  · exact parentBucket14
  · exact parentBucket15
  · exact parentBucket16
  · exact parentBucket17
  · exact parentBucket18
  · exact parentBucket19
  · exact parentBucket20
  · exact parentBucket21
  · exact parentBucket22
  · exact parentBucket23
  · exact parentBucket24
  · exact parentBucket25
  · exact parentBucket26
  · exact parentBucket27
  · exact parentBucket28
  · exact parentBucket29
  · exact parentBucket30
  · exact parentBucket31
  · exact parentBucket32
  · exact parentBucket33
  · exact parentBucket34
  · exact parentBucket35
  · exact parentBucket36
  · exact parentBucket37
  · exact parentBucket38
  · exact parentBucket39
  · exact parentBucket40
  · exact parentBucket41

noncomputable def oneNotMasks:List (Nat × Nat):=[(0,1),(FF,0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def oneNotMaskFull:mFull oneNotMasks = true:=by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma binLane0Checked:∀ q ∈ binLane0Groups,binGroupCheck q = true:=by
  intro q hq
  simp only [binLane0Groups,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma binLane1Checked:∀ q ∈ binLane1Groups,binGroupCheck q = true:=by
  intro q hq
  simp only [binLane1Groups,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

noncomputable def binGroupsChecked (q:List ℕ) (hq:q ∈ binGroups):binGroupCheck q = true:=by
  simp only [binGroups,List.mem_append] at hq
  rcases hq with h | h | h
  · exact binLargeGroupsChecked q h
  · exact binLane0Checked q h
  · exact binLane1Checked q h
lemma binTableChecked (i:ℕ) (hi:i < 3199):binCheck i = true:=by
  have hm:i ∈ binGroups.flatMap id:=mem_of_indexMask binGroupsCover hi
  obtain ⟨q,hq,hqi⟩:=List.mem_flatMap.mp hm
  have hh:=List.all_eq_true.mp (binGroupsChecked q hq) i hqi
  simpa only [forceBinCheck_eq] using hh

lemma binLeafF (j:ℕ) (hj:j < 3199) (hm:binMode j ≠ 0) :
    look initL initM initG 13 (binRow j).1 (binRow j).2.1
      (binRow j).2.2.1 (binRow j).2.2.2 = false:=by
  have hh:=binTableChecked j hj
  simpa [binCheck,hm] using hh
lemma binLeafG (j:ℕ) (hj:j < 3199) (hm:binMode j = 0) :
    look1 initL initM initG 13 12 (binRow j).1 (binRow j).2.1
      (binRow j).2.2.1 (binRow j).2.2.2 = false:=by
  have hh:=binTableChecked j hj
  simpa [binCheck,hm] using hh

lemma binFRowsChecked (z:Nat):∀ s ∈ binFRows z,
    look initL initM initG 13 s.1 s.2.1 s.2.2.1 s.2.2.2 = false:=by
  intro s hs
  obtain ⟨i,hi,rfl⟩:=List.mem_map.1 hs
  change i ∈ (binBudgetAt (z % 2053)).filter (fun j => decide (binMode j ≠ 0)) at hi
  obtain ⟨hmem,hm⟩:=List.mem_filter.1 hi
  exact binLeafF i (chunk_bucket_index_bound _ _ binBucketsBound _ _ hmem) (of_decide_eq_true hm)

lemma binGRowsChecked (z:Nat):∀ s ∈ binGRows z,
    look1 initL initM initG 13 12 s.1 s.2.1 s.2.2.1 s.2.2.2 = false:=by
  intro s hs
  obtain ⟨i,hi,rfl⟩:=List.mem_map.1 hs
  change i ∈ (binBudgetAt (z % 2053)).filter (fun j => decide (binMode j = 0)) at hi
  obtain ⟨hmem,hm⟩:=List.mem_filter.1 hi
  exact binLeafG i (chunk_bucket_index_bound _ _ binBucketsBound _ _ hmem) (of_decide_eq_true hm)

lemma binaryParentChecked (i:Nat) (hi:i < 42) :
    look1 initL initM initG 13 13 (rootRow i).1 (rootRow i).2.1
      (rootRow i).2.2.1 (rootRow i).2.2.2 = false:=by
  have h:=parentBucketCoverage i hi
  unfold parentBucketGoal cutF cutG at h
  rw [patchBudget_eq _ _ binFRowsChecked,patchBudget_eq _ _ binGRowsChecked,look1Cut_eq] at h
  exact h

lemma binaryParentsChecked:∀ s ∈ binaryRows,
    look1 initL initM initG 13 13 s.1 s.2.1 s.2.2.1 s.2.2.2 = false:=by
  intro s hs
  obtain ⟨i,hi,rfl⟩:=List.mem_map.1 hs
  exact binaryParentChecked i (List.mem_range.1 hi)

lemma rootRowsChecked (z:Nat):∀ s ∈ rootRows z,
    look1 initL initM initG 13 13 s.1 s.2.1 s.2.2.1 s.2.2.2 = false:=by
  intro s hs
  obtain ⟨i,hi,rfl⟩:=List.mem_map.1 hs
  have hb:=chunk_bucket_index_bound _ _ rootBucketsBound _ _ hi
  exact binaryParentChecked i hb

lemma unaryBucketRowsChecked (z:Nat):∀ s ∈ unaryBucketRows z,
    look initL initM initG 13 s.1 s.2.1 s.2.2.1 s.2.2.2 = false:=by
  intro s hs
  obtain ⟨i,hi,rfl⟩:=List.mem_map.1 hs
  have hb:=chunk_bucket_index_bound _ _ unaryBucketsBound _ _ hi
  exact unaryTableChecked _ (List.mem_map.2 ⟨i,List.mem_range.2 hb,rfl⟩)

lemma unaryRootChecked:chk [] (pr ac4 0) 0 13 1 0 1 = false:=by
  have h:=unaryBucketCoverage
  unfold cutF rootG at h
  rw [patchBudget_eq _ _ unaryBucketRowsChecked] at h
  simpa only [← initL_eq,← initM_eq,← initG_eq,chkCut_eq] using h

lemma binaryRootChecked:chk [] (pr ac4 0) 0 13 1 FF 0 = false:=by
  have h:=binaryBucketCoverage
  unfold cutF rootG at h
  rw [patchBudget_eq _ _ rootRowsChecked] at h
  simpa only [← initL_eq,← initM_eq,← initG_eq,chkCut_eq] using h

lemma oneNotChecked:∀ p ∈ oneNotMasks,chk [] (pr ac4 0) 0 13 1 p.1 p.2 = false:=by
  intro p hp
  simp only [oneNotMasks,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl
  · exact unaryRootChecked
  · exact binaryRootChecked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma oneNotLiveImpossibleChecked (S:Finset ℕ)
    (hS:(S:Set ℕ) ⊆ C (mz 0) (WZ [] 0))
    (hl:Live Z0 (mz 0) (tz 0) 13 1 S):False:=by
  exact live_certificate_false (E:=[]) (Q:=pr ac4 0) (Z:=0) (L:=14)
    (Or.inl rfl) (by decide +kernel) (by omega) (by omega)
    (fun e he => ai4 e (List.mem_of_mem_filter he)) hS hl
    (fun q hq => iroot q hq) ⟨oneNotMasks,oneNotMaskFull,oneNotChecked⟩

end PEqualNP.Outside.L_meta_10760

open PEqualNP.Outside.L_meta_10760 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_10760 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  classical
  intro gates o legal oneNot computes
  by_cases hbig : 14 ≤ gates.length
  · exact ⟨witness, 20, witness_basis, by simpa [witness_length] using hbig,
      fun x => (witness_correct x).trans (graph_correct x)⟩
  by_cases hzero : notCount gates = 0
  · have hn : ∀ g ∈ gates, g.op ≠ GateOp.not := by
      simpa only [notCount, List.countP_eq_zero, decide_eq_true_eq] using hzero
    refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    refine ⟨?_, (legal g hg).2⟩
    rcases (legal g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hn g hg h)
  have hn : notCount gates = 1 := by
    have := unique_not_count gates oneNot
    omega
  have hok : FanInTwo (⟨gates, o⟩ : Circuit) := by
    intro g hg
    refine ⟨?_, (legal g hg).2⟩
    rcases (legal g hg).1 with h | h | h <;> simp [h]
  have hf : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x :=
    fun x => (computes x).trans (graph_correct x).symm
  obtain ⟨k, t, ht, hb, S, hS, hl⟩ := circuit_live_count ⟨gates, o⟩ hok hf
  have hk : 13 ≤ k := by
    by_contra h
    exact iroot k (by omega) (hl.sol.mono le_rfl hS)
  change t ≤ notCount gates at ht
  change k + (notCount gates - t) ≤ gates.length at hb
  rw [hn] at ht hb
  have hkEq : k = 13 := by omega
  have htEq : t = 1 := by omega
  subst k
  subst t
  exact False.elim (oneNotLiveImpossibleChecked S hS hl)
