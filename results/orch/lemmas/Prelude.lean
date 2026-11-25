import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502.Structural

universe u
variable {α : Type u} [DecidableEq α]

def on (a c : α) : α → Bool := fun i => decide (i = a) || decide (i = c)

theorem on_iff (a c i : α) : on a c i = true ↔ i = a ∨ i = c := by simp [on]

/-- `F` depends only on `N`. -/
def Dep (F : (α → Bool) → Bool) (N : Finset α) : Prop :=
  ∀ x y : α → Bool, (∀ i ∈ N, x i = y i) → F x = F y

/-- `F` is off at no wire, and accepted pairs of wires not accepted alone have no path. -/
def Free (F : (α → Bool) → Bool) : Prop :=
  F (fun _ => false) = false ∧ ∀ a b c d, F (on a a) = false → F (on b b) = false →
    F (on c c) = false → F (on d d) = false → F (on a c) = true → F (on a d) = true →
    F (on b c) = true → F (on b d) = true

theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem free_or {F : (α → Bool) → Bool} {N : Finset α} (hd : Dep F N) (hf : Free F) {t p q : α}
    (hp : p ∉ N.erase t) (hq : q ∉ N.erase t) (z : α) (hz : z ∉ N) :
    Free fun x => F (Function.update x t (x p || x q)) := by
  classical
  let r : α → α := fun a => if a = p ∨ a = q then t else if a ∈ N.erase t then a else z
  have key : ∀ a c, F (Function.update (on a c) t (on a c p || on a c q)) = F (on (r a) (r c)) := by
    intro a c
    refine hd _ _ fun i hi => bool_ext ?_
    have hr : ∀ a, (i = t → (i = r a ↔ a = p ∨ a = q)) ∧ (i ≠ t → (i = r a ↔ i = a)) := by
      intro a
      have hiz : i ≠ z := fun h => hz (h ▸ hi)
      constructor
      · intro hit
        simp only [r]
        split_ifs with h1 h2
        · simp [hit, h1]
        · have := Finset.ne_of_mem_erase h2
          simp only [h1, iff_false]; rw [hit]; exact fun h => this h.symm
        · simp [h1, hiz]
      · intro hit
        have hiN : i ∈ N.erase t := Finset.mem_erase.2 ⟨hit, hi⟩
        simp only [r]
        split_ifs with h1 h2
        · simp only [hit, false_iff]
          rintro rfl
          rcases h1 with rfl | rfl
          · exact hp hiN
          · exact hq hiN
        · rfl
        · simp only [hiz, false_iff]
          rintro rfl; exact h2 hiN
    rw [on_iff]
    by_cases hit : i = t
    · rw [(hr a).1 hit, (hr c).1 hit, hit, Function.update_self, Bool.or_eq_true, on_iff, on_iff]
      constructor
      · rintro ((h | h) | (h | h)) <;> simp [h]
      · rintro ((h | h) | (h | h)) <;> simp [h]
    · rw [(hr a).2 hit, (hr c).2 hit, Function.update_of_ne hit, on_iff]
  refine ⟨?_, ?_⟩
  · show F (Function.update (fun _ => false) t (false || false)) = false
    rw [show Function.update (fun _ : α => false) t (false || false) = fun _ => false from by
      funext i; by_cases h : i = t <;> simp [Function.update, h]]
    exact hf.1
  · intro a b c d
    simp only [key]
    exact hf.2 _ _ _ _

theorem free_and_lift {F : (α → Bool) → Bool} {N : Finset α} (hd : Dep F N) {t p q : α}
    (hf : Free (fun x => F (Function.update x t false)))
    (ht : t ∈ N) (hpq : p ≠ q) (hp : p ∉ N.erase t) (hq : q ∉ N.erase t) (z : α) (hz : z ∉ N) :
    Free fun x => F (Function.update x t (x p && x q)) := by
  classical
  have hzF : F (fun _ => false) = false := by
    simpa using hf.1
  let r : α → α := fun a => if a ∈ N.erase t then a else z
  have rt : ∀ a, r a ≠ t := by
    intro a
    simp only [r]
    split_ifs with h
    · exact Finset.ne_of_mem_erase h
    · exact fun hzt => hz (hzt ▸ ht)
  have kill_eq : ∀ a c,
      F (Function.update (on (r a) (r c)) t false) = F (on (r a) (r c)) := by
    intro a c
    congr 1
    funext i
    by_cases hit : i = t
    · subst i
      simp [on, (rt a).symm, (rt c).symm]
    · simp [Function.update_of_ne hit]
  have rp : r p = z := ite_eq_right hp
  have rq : r q = z := ite_eq_right hq
  have hzz : ∀ x, F (on x z) = F (on x x) := fun x => hd _ _ fun i hi => by
    have : i ≠ z := fun h => hz (h ▸ hi)
    simp [on, this]
  have hzz' : ∀ x, F (on z x) = F (on x x) := fun x => hd _ _ fun i hi => by
    have : i ≠ z := fun h => hz (h ▸ hi)
    simp [on, this]
  have hz0 : F (on z z) = false := by
    rw [← hzF]
    exact hd _ _ fun i hi => by
      have : i ≠ z := fun h => hz (h ▸ hi)
      simp [on, this]
  have key : ∀ a c, ¬ (a = p ∧ c = q) → ¬ (a = q ∧ c = p) →
      F (Function.update (on a c) t (on a c p && on a c q)) = F (on (r a) (r c)) := by
    intro a c h1 h2
    refine hd _ _ fun i hi => bool_ext ?_
    have hiz : i ≠ z := fun h => hz (h ▸ hi)
    have hr : ∀ a, i = r a ↔ i ≠ t ∧ i = a := by
      intro a
      simp only [r]
      split_ifs with h
      · constructor
        · intro e; exact ⟨e ▸ Finset.ne_of_mem_erase h, e⟩
        · exact fun e => e.2
      · simp only [hiz, false_iff]
        rintro ⟨e1, rfl⟩
        exact h (Finset.mem_erase.2 ⟨e1, hi⟩)
    rw [on_iff, hr, hr]
    by_cases hit : i = t
    · rw [hit, Function.update_self, Bool.and_eq_true, on_iff, on_iff]
      constructor
      · rintro ⟨e1 | e1, e2 | e2⟩
        · exact absurd (e1.trans e2.symm) hpq
        · exact absurd ⟨e1.symm, e2.symm⟩ h1
        · exact absurd ⟨e2.symm, e1.symm⟩ h2
        · exact absurd (e1.trans e2.symm) hpq
      · rintro (⟨e, _⟩ | ⟨e, _⟩) <;> exact absurd rfl e
    · rw [Function.update_of_ne hit, on_iff]
      simp [hit]
  have kk : ∀ a, F (Function.update (on a a) t (on a a p && on a a q)) = F (on (r a) (r a)) :=
    fun a => key a a (fun h => hpq (h.1.symm.trans h.2)) (fun h => hpq (h.2.symm.trans h.1))
  refine ⟨?_, ?_⟩
  · show F (Function.update (fun _ => false) t (false && false)) = false
    rw [show Function.update (fun _ : α => false) t (false && false) = fun _ => false from by
      funext i; by_cases h : i = t <;> simp [Function.update, h]]
    exact hzF
  · intro a b c d ha hb hc hd' hac had hbc
    beta_reduce at ha hb hc hd' hac had hbc
    -- a neighbour of `p` or `q` is the other one
    have nb : ∀ e f, (e = p ∨ e = q) →
        F (Function.update (on f f) t (on f f p && on f f q)) = false →
        (F (Function.update (on e f) t (on e f p && on e f q)) = true →
          (e = p ∧ f = q) ∨ (e = q ∧ f = p)) ∧
        (F (Function.update (on f e) t (on f e p && on f e q)) = true →
          (f = p ∧ e = q) ∨ (f = q ∧ e = p)) := by
      intro e f he hf0
      have re : r e = z := by rcases he with rfl | rfl <;> assumption
      rw [kk] at hf0
      constructor
      · intro h
        by_contra hn
        rw [key e f (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h)), re, hzz', hf0] at h
        exact Bool.noConfusion h
      · intro h
        by_contra hn
        rw [key f e (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h)), re, hzz, hf0] at h
        exact Bool.noConfusion h
    by_cases hA : a = p ∨ a = q
    · have e1 := (nb a c hA hc).1 hac
      have e2 := (nb a d hA hd').1 had
      have : c = d := by
        rcases e1 with ⟨x, y⟩ | ⟨x, y⟩ <;> rcases e2 with ⟨x', y'⟩ | ⟨x', y'⟩
        · rw [y, y']
        · exact absurd (x.symm.trans x') hpq
        · exact absurd (x'.symm.trans x) hpq
        · rw [y, y']
      rw [← this]; exact hbc
    · by_cases hB : b = p ∨ b = q
      · have e1 := (nb b c hB hc).1 hbc
        have hC : c = p ∨ c = q := by
          rcases e1 with ⟨_, y⟩ | ⟨_, y⟩
          · exact Or.inr y
          · exact Or.inl y
        have e2 := (nb c a hC ha).2 hac
        exact absurd (by rcases e2 with ⟨x, _⟩ | ⟨x, _⟩ <;> simp [x]) hA
      · have n1 : ∀ e, ¬ (a = p ∧ e = q) ∧ ¬ (a = q ∧ e = p) := fun e =>
          ⟨fun h => hA (Or.inl h.1), fun h => hA (Or.inr h.1)⟩
        have n2 : ∀ e, ¬ (b = p ∧ e = q) ∧ ¬ (b = q ∧ e = p) := fun e =>
          ⟨fun h => hB (Or.inl h.1), fun h => hB (Or.inr h.1)⟩
        rw [kk] at ha hb hc hd'
        rw [key _ _ (n1 c).1 (n1 c).2] at hac
        rw [key _ _ (n1 d).1 (n1 d).2] at had
        rw [key _ _ (n2 c).1 (n2 c).2] at hbc
        show F (Function.update (on b d) t (on b d p && on b d q)) = true
        rw [key _ _ (n2 d).1 (n2 d).2]
        have hfree := hf.2 (r a) (r b) (r c) (r d)
        simp only [kill_eq] at hfree
        exact hfree ha hb hc hd' hac had hbc




def kill (E : Finset α) (x : α → Bool) : α → Bool :=
  fun i => if i ∈ E then false else x i

lemma kill_empty (x : α → Bool) : kill ∅ x = x := by
  funext i
  simp [kill]

lemma kill_zero (E : Finset α) : kill E (fun _ => false) = fun _ => false := by
  funext i
  simp [kill]

lemma kill_union (E D : Finset α) (x : α → Bool) :
    kill E (kill D x) = kill (E ∪ D) x := by
  funext i
  by_cases he : i ∈ E <;> by_cases hd : i ∈ D <;> simp [kill, he, hd]

lemma kill_on (E : Finset α) (a b : α) (ha : a ∉ E) (hb : b ∉ E) :
    kill E (on a b) = on a b := by
  funext i
  by_cases hi : i ∈ E
  · have hia : i ≠ a := fun h => ha (h ▸ hi)
    have hib : i ≠ b := fun h => hb (h ▸ hi)
    simp [kill, on, hi, hia, hib]
  · simp [kill, hi]

lemma kill_on_left (E : Finset α) (a b : α) (ha : a ∈ E) :
    kill E (on a b) = kill E (on b b) := by
  funext i
  by_cases hi : i ∈ E
  · simp [kill, hi]
  · have hia : i ≠ a := fun h => hi (h ▸ ha)
    simp [kill, on, hi, hia]

lemma on_comm (a b : α) : on a b = on b a := by
  funext i
  simp [on, Bool.or_comm]

lemma free_kill {F : (α → Bool) → Bool} (hf : Free F) (E : Finset α) :
    Free (fun x => F (kill E x)) := by
  refine ⟨?_, ?_⟩
  · simpa only [kill_zero] using hf.1
  · intro a b c d ha hb hc hd hac had hbc
    beta_reduce at ha hb hc hd hac had hbc ⊢
    have na : a ∉ E := by
      intro h
      rw [kill_on_left E a c h] at hac
      simp only [hc, Bool.false_eq_true] at hac
    have nb : b ∉ E := by
      intro h
      rw [kill_on_left E b c h] at hbc
      simp only [hc, Bool.false_eq_true] at hbc
    have nc : c ∉ E := by
      intro h
      rw [on_comm a c, kill_on_left E c a h] at hac
      simp only [ha, Bool.false_eq_true] at hac
    have nd : d ∉ E := by
      intro h
      rw [on_comm a d, kill_on_left E d a h] at had
      simp only [ha, Bool.false_eq_true] at had
    rw [kill_on E a a na na] at ha
    rw [kill_on E b b nb nb] at hb
    rw [kill_on E c c nc nc] at hc
    rw [kill_on E d d nd nd] at hd
    rw [kill_on E a c na nc] at hac
    rw [kill_on E a d na nd] at had
    rw [kill_on E b c nb nc] at hbc
    rw [kill_on E b d nb nd]
    exact hf.2 a b c d ha hb hc hd hac had hbc

lemma free_kill_mono {F : (α → Bool) → Bool} {E D : Finset α}
    (hf : Free (fun x => F (kill E x))) (hED : E ⊆ D) :
    Free (fun x => F (kill D x)) := by
  have h := free_kill hf D
  simpa only [kill_union, Finset.union_eq_right.mpr hED] using h

lemma dep_kill {F : (α → Bool) → Bool} {N : Finset α} (hd : Dep F N) (E : Finset α) :
    Dep (fun x => F (kill E x)) (N \ E) := by
  intro x y hxy
  apply hd
  intro i hi
  by_cases he : i ∈ E
  · simp [kill, he]
  · simpa only [kill, ite_eq_right he] using hxy i (Finset.mem_sdiff.mpr ⟨hi, he⟩)


lemma kill_update_zero (E : Finset α) (x : α → Bool) (t : α) :
    Function.update (kill E x) t false = kill (insert t E) x := by
  funext i
  by_cases hit : i = t <;> by_cases hi : i ∈ E <;> simp [kill, Function.update, hit, hi]

lemma kill_update_comm (E : Finset α) (x : α → Bool) (t : α) (v : Bool)
    (ht : t ∉ E) :
    Function.update (kill E x) t v = kill E (Function.update x t v) := by
  funext i
  by_cases hit : i = t
  · subst i
    simp [kill, ht]
  · simp only [Function.update_of_ne hit, kill]

lemma free_mask_sub_zero {F : (α → Bool) → Bool} {E D : Finset α}
    (hf : Free (fun x => F (kill E x))) (op : Bool → Bool → Bool) (t p q : α)
    (hED : E ⊆ insert t D)
    (hzero : ∀ x : α → Bool, op (kill D x p) (kill D x q) = false) :
    Free (fun x => F (Function.update (kill D x) t (op (kill D x p) (kill D x q)))) := by
  have heq : (fun x => F (Function.update (kill D x) t (op (kill D x p) (kill D x q)))) =
      fun x => F (kill (insert t D) x) := by
    funext x
    rw [hzero, kill_update_zero]
  rw [heq]
  exact free_kill_mono hf hED

lemma free_mask_or_fresh {F : (α → Bool) → Bool} {N E : Finset α}
    (hd : Dep F N) (hf : Free (fun x => F (kill E x))) {t p q : α}
    (ht : t ∉ E) (hp : p ∉ E) (hq : q ∉ E)
    (hpN : p ∉ N.erase t) (hqN : q ∉ N.erase t) (z : α) (hz : z ∉ N) :
    Free (fun x => F (Function.update (kill E x) t (kill E x p || kill E x q))) := by
  have hp' : p ∉ (N \ E).erase t := by simp only [Finset.mem_erase, Finset.mem_sdiff] at *; tauto
  have hq' : q ∉ (N \ E).erase t := by simp only [Finset.mem_erase, Finset.mem_sdiff] at *; tauto
  have hz' : z ∉ N \ E := fun h => hz (Finset.mem_sdiff.mp h).1
  have h := free_or (dep_kill hd E) hf hp' hq' z hz'
  have heq : (fun x => F (Function.update (kill E x) t (kill E x p || kill E x q))) =
      fun x => F (kill E (Function.update x t (x p || x q))) := by
    funext x
    simp only [kill, ite_eq_right hp, ite_eq_right hq]
    rw [← kill_update_comm E x t _ ht]
  rw [heq]
  exact h

lemma free_mask_and_fresh {F : (α → Bool) → Bool} {N E : Finset α}
    (hd : Dep F N) (hf : Free (fun x => F (kill E x))) {t p q : α}
    (htN : t ∈ N) (hpq : p ≠ q) (hpE : p ∉ E.erase t) (hqE : q ∉ E.erase t)
    (hpN : p ∉ N.erase t) (hqN : q ∉ N.erase t) (z : α) (hz : z ∉ N) :
    Free (fun x => F (Function.update (kill (E.erase t) x) t
      (kill (E.erase t) x p && kill (E.erase t) x q))) := by
  let D := E.erase t
  have htD : t ∉ D := by simp [D]
  have hp' : p ∉ (N \ D).erase t := by simp only [Finset.mem_erase, Finset.mem_sdiff] at *; tauto
  have hq' : q ∉ (N \ D).erase t := by simp only [Finset.mem_erase, Finset.mem_sdiff] at *; tauto
  have ht' : t ∈ N \ D := Finset.mem_sdiff.mpr ⟨htN, htD⟩
  have hz' : z ∉ N \ D := fun h => hz (Finset.mem_sdiff.mp h).1
  have hFD : Free (fun x => F (kill D (Function.update x t false))) := by
    have heq : (fun x => F (kill D (Function.update x t false))) =
        fun x => F (kill (insert t D) x) := by
      funext x
      rw [← kill_update_comm D x t false htD, kill_update_zero]
    rw [heq]
    apply free_kill_mono hf
    intro i hi
    by_cases hit : i = t
    · simp [hit]
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hit, hi⟩)
  have h := free_and_lift (dep_kill hd D) hFD ht' hpq hp' hq' z hz'
  have heq : (fun x => F (Function.update (kill D x) t (kill D x p && kill D x q))) =
      fun x => F (kill D (Function.update x t (x p && x q))) := by
    funext x
    have hpD : p ∉ D := hpE
    have hqD : q ∉ D := hqE
    simp only [kill, ite_eq_right hpD, ite_eq_right hqD]
    rw [← kill_update_comm D x t _ htD]
  change Free (fun x => F (Function.update (kill D x) t (kill D x p && kill D x q)))
  rw [heq]
  exact h

lemma free_mask_or_old_left {F : (α → Bool) → Bool} {N E D : Finset α}
    (hd : Dep F N) (hf : Free (fun x => F (kill E x))) (hED : E ⊆ D)
    {t p q : α} (ht : t ∉ D) (hp : p ∈ D) (hq : q ∉ D)
    (hqN : q ∉ N.erase t) (z : α) (hz : z ∉ N) :
    Free (fun x => F (Function.update (kill D x) t (kill D x p || kill D x q))) := by
  have hq' : q ∉ (N \ D).erase t := by simp only [Finset.mem_erase, Finset.mem_sdiff] at *; tauto
  have hz' : z ∉ N \ D := fun h => hz (Finset.mem_sdiff.mp h).1
  have h := free_or (dep_kill hd D) (free_kill_mono hf hED) hq' hq' z hz'
  have heq : (fun x => F (Function.update (kill D x) t (kill D x p || kill D x q))) =
      fun x => F (kill D (Function.update x t (x q || x q))) := by
    funext x
    simp only [kill, ite_eq_left hp, ite_eq_right hq, Bool.false_or, Bool.or_self]
    rw [← kill_update_comm D x t _ ht]
  rw [heq]
  exact h

lemma free_mask_or_old_right {F : (α → Bool) → Bool} {N E D : Finset α}
    (hd : Dep F N) (hf : Free (fun x => F (kill E x))) (hED : E ⊆ D)
    {t p q : α} (ht : t ∉ D) (hq : q ∈ D) (hp : p ∉ D)
    (hpN : p ∉ N.erase t) (z : α) (hz : z ∉ N) :
    Free (fun x => F (Function.update (kill D x) t (kill D x p || kill D x q))) := by
  simpa only [Bool.or_comm] using free_mask_or_old_left hd hf hED ht hq hp hpN z hz


def ORClass (F : (α → Bool) → Bool) (S : Finset α) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ x : α → Bool,
    F (Function.update x a true) = F (Function.update x b true)

def classRest (S : Finset α) (t p q : α) : Finset α :=
  ((S.erase t).erase p).erase q

def classSub (F : (α → Bool) → Bool) (op : Bool → Bool → Bool)
    (t p q : α) : (α → Bool) → Bool :=
  fun x => F (Function.update x t (op (x p) (x q)))

lemma classRest_mem {S : Finset α} {t p q a : α} (ha : a ∈ classRest S t p q) :
    a ∈ S ∧ a ≠ t ∧ a ≠ p ∧ a ≠ q := by
  simpa only [classRest, Finset.mem_erase, and_assoc, and_left_comm, and_comm] using ha

lemma classSub_force (F : (α → Bool) → Bool) (op : Bool → Bool → Bool)
    (t p q a : α) (x : α → Bool) (hat : a ≠ t) (hap : a ≠ p) (haq : a ≠ q) :
    classSub F op t p q (Function.update x a true) =
      F (Function.update (Function.update x t (op (x p) (x q))) a true) := by
  simp only [classSub, Function.update_of_ne hap.symm, Function.update_of_ne haq.symm]
  rw [Function.update_comm hat]

lemma orClass_survive {F : (α → Bool) → Bool} {S : Finset α}
    (hclass : ORClass F S) (op : Bool → Bool → Bool) (t p q : α) :
    ORClass (classSub F op t p q) (classRest S t p q) := by
  intro a ha b hb x
  obtain ⟨ha, hat, hap, haq⟩ := classRest_mem ha
  obtain ⟨hb, hbt, hbp, hbq⟩ := classRest_mem hb
  rw [classSub_force F op t p q a x hat hap haq,
    classSub_force F op t p q b x hbt hbp hbq]
  exact hclass a ha b hb _

lemma orClass_empty (F : (α → Bool) → Bool) : ORClass F ∅ := by
  intro a ha
  simp only [Finset.notMem_empty] at ha

lemma orClass_singleton (F : (α → Bool) → Bool) (a : α) : ORClass F {a} := by
  intro b hb c hc x
  simp only [Finset.mem_singleton] at hb hc
  subst b
  subst c
  rfl

lemma orClass_subset {F : (α → Bool) → Bool} {S T : Finset α}
    (hclass : ORClass F S) (hTS : T ⊆ S) : ORClass F T := by
  exact fun a ha b hb => hclass a (hTS ha) b (hTS hb)

lemma class_ignore {F : (α → Bool) → Bool} {N : Finset α} (hd : Dep F N)
    {a : α} (ha : a ∉ N) (x : α → Bool) (v : Bool) :
    F (Function.update x a v) = F x := by
  apply hd
  intro i hi
  have hia : i ≠ a := by
    intro h
    subst i
    exact ha hi
  exact Function.update_of_ne hia v x

lemma class_or_force_old {F : (α → Bool) → Bool} {S : Finset α}
    (hclass : ORClass F S) {t p q a : α} (ht : t ∈ S)
    (ha : a ∈ classRest S t p q) (x : α → Bool) :
    classSub F (· || ·) t p q (Function.update x a true) =
      F (Function.update x t true) := by
  obtain ⟨ha, hat, hap, haq⟩ := classRest_mem ha
  rw [classSub_force F (· || ·) t p q a x hat hap haq, hclass a ha t ht]
  rw [Function.update_idem]

lemma class_or_force_left {F : (α → Bool) → Bool} {N : Finset α}
    (hd : Dep F N) {t p q : α} (hpt : p ≠ t) (hp : p ∉ N) (x : α → Bool) :
    classSub F (· || ·) t p q (Function.update x p true) =
      F (Function.update x t true) := by
  simp only [classSub, Function.update_self, Bool.true_or]
  rw [Function.update_comm hpt]
  exact class_ignore hd hp _ true

lemma class_or_force_right {F : (α → Bool) → Bool} {N : Finset α}
    (hd : Dep F N) {t p q : α} (hqt : q ≠ t) (hq : q ∉ N) (x : α → Bool) :
    classSub F (· || ·) t p q (Function.update x q true) =
      F (Function.update x t true) := by
  simp only [classSub, Function.update_self, Bool.or_true]
  rw [Function.update_comm hqt]
  exact class_ignore hd hq _ true

lemma orClass_or_inherit {F : (α → Bool) → Bool} {N S B : Finset α}
    (hd : Dep F N) (hclass : ORClass F S) {t p q : α} (ht : t ∈ S)
    (hB : ∀ b ∈ B, (b = p ∨ b = q) ∧ b ≠ t ∧ b ∉ N) :
    ORClass (classSub F (· || ·) t p q) (classRest S t p q ∪ B) := by
  have hforce : ∀ a ∈ classRest S t p q ∪ B, ∀ x : α → Bool,
      classSub F (· || ·) t p q (Function.update x a true) =
        F (Function.update x t true) := by
    intro a ha x
    rcases Finset.mem_union.mp ha with ha | ha
    · exact class_or_force_old hclass ht ha x
    · obtain ⟨ha, hat, haN⟩ := hB a ha
      rcases ha with rfl | rfl
      · exact class_or_force_left hd hat haN x
      · exact class_or_force_right hd hat haN x
  intro a ha b hb x
  exact (hforce a ha x).trans (hforce b hb x).symm

def classFresh (rest : Finset α) (p q : α) : Finset α := {p, q} \ rest

def classReused (rest : Finset α) (p q : α) : Finset α := {p, q} ∩ rest

def classOp (isOr : Bool) (x y : Bool) : Bool := if isOr then x || y else x && y

def classNext (isOr : Bool) (rest : Finset α) (t p q : α) (S : Finset α) : Finset α :=
  classRest S t p q ∪ if isOr = true ∧ t ∈ S then classFresh rest p q else ∅

def classFamilyNext (isOr : Bool) (rest : Finset α) (t p q : α)
    (K : Finset (Finset α)) : Finset (Finset α) :=
  K.image (classNext isOr rest t p q) ∪ (classReused rest p q).image (fun a => {a})

def classUnion (K : Finset (Finset α)) : Finset α := K.biUnion id

lemma classNext_closed {F : (α → Bool) → Bool} {rest S : Finset α} {t p q : α}
    (hd : Dep F (insert t rest)) (hclass : ORClass F S)
    (htp : t ≠ p) (htq : t ≠ q) (isOr : Bool) :
    ORClass (classSub F (classOp isOr) t p q) (classNext isOr rest t p q S) := by
  by_cases h : isOr = true ∧ t ∈ S
  · rcases h with ⟨rfl, ht⟩
    simp only [classNext, ht, and_self, ite_true]
    apply orClass_or_inherit hd hclass ht
    intro b hb
    simp only [classFresh, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hb
    have hbt : b ≠ t := by
      rcases hb.1 with rfl | rfl
      · exact htp.symm
      · exact htq.symm
    exact ⟨hb.1, hbt, by simp [hbt, hb.2]⟩
  · simp only [classNext, h, ite_false, Finset.union_empty]
    exact orClass_survive hclass (classOp isOr) t p q

lemma classFamilyNext_closed {F : (α → Bool) → Bool} {rest : Finset α} {t p q : α}
    {K : Finset (Finset α)} (hd : Dep F (insert t rest))
    (hK : ∀ S ∈ K, ORClass F S) (htp : t ≠ p) (htq : t ≠ q) (isOr : Bool) :
    ∀ S ∈ classFamilyNext isOr rest t p q K,
      ORClass (classSub F (classOp isOr) t p q) S := by
  intro S hS
  rcases Finset.mem_union.mp hS with hS | hS
  · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    exact classNext_closed hd (hK T hT) htp htq isOr
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hS
    exact orClass_singleton _ a

lemma classNext_subset {rest S : Finset α} {t p q : α}
    (hS : S ⊆ insert t rest) (isOr : Bool) :
    classNext isOr rest t p q S ⊆ insert p (insert q rest) := by
  intro a ha
  rcases Finset.mem_union.mp ha with ha | ha
  · obtain ⟨ha, hat, _, _⟩ := classRest_mem ha
    have har : a ∈ rest := (Finset.mem_insert.mp (hS ha)).resolve_left hat
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem har)
  · by_cases h : isOr = true ∧ t ∈ S
    · rw [ite_eq_left h] at ha
      simp only [classFresh, Finset.mem_sdiff, Finset.mem_insert,
        Finset.mem_singleton] at ha
      rcases ha.1 with rfl | rfl <;> simp
    · simp only [h, ite_false, Finset.notMem_empty] at ha

lemma classFamilyNext_subset {rest : Finset α} {t p q : α} {K : Finset (Finset α)}
    (hK : ∀ S ∈ K, S ⊆ insert t rest) (isOr : Bool) :
    ∀ S ∈ classFamilyNext isOr rest t p q K, S ⊆ insert p (insert q rest) := by
  intro S hS
  rcases Finset.mem_union.mp hS with hS | hS
  · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    exact classNext_subset (hK T hT) isOr
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hS
    intro b hb
    have hba := Finset.mem_singleton.mp hb
    subst b
    have har : a ∈ rest := (Finset.mem_inter.mp ha).2
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem har)

lemma classFamilyNext_card (isOr : Bool) (rest : Finset α) (t p q : α)
    (K : Finset (Finset α)) :
    (classFamilyNext isOr rest t p q K).card ≤ K.card + (classReused rest p q).card := by
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le))

lemma classUnion_mem (K : Finset (Finset α)) (a : α) :
    a ∈ classUnion K ↔ ∃ S ∈ K, a ∈ S := by
  simp only [classUnion, Finset.mem_biUnion, id_eq]

lemma classFamilyUnion_mem (isOr : Bool) (rest : Finset α) (t p q a : α)
    (K : Finset (Finset α)) :
    a ∈ classUnion (classFamilyNext isOr rest t p q K) ↔
      (∃ S ∈ K, a ∈ classNext isOr rest t p q S) ∨ a ∈ classReused rest p q := by
  rw [classUnion_mem]
  constructor
  · rintro ⟨S, hS, ha⟩
    rcases Finset.mem_union.mp hS with hS | hS
    · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
      exact Or.inl ⟨T, hT, ha⟩
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hS
      have hab := Finset.mem_singleton.mp ha
      subst a
      exact Or.inr hb
  · rintro (⟨S, hS, ha⟩ | ha)
    · exact ⟨_, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨S, hS, rfl⟩), ha⟩
    · exact ⟨{a}, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩),
        Finset.mem_singleton_self _⟩

lemma classFamilyNext_union (isOr : Bool) (rest : Finset α) (t p q : α)
    (K : Finset (Finset α)) (hK : ∀ S ∈ K, S ⊆ insert t rest) :
    classUnion (classFamilyNext isOr rest t p q K) =
      ((classUnion K).erase t ∪ classReused rest p q) ∪
        if isOr = true ∧ t ∈ classUnion K then classFresh rest p q else ∅ := by
  ext a
  rw [classFamilyUnion_mem]
  constructor
  · rintro (⟨S, hS, ha⟩ | ha)
    · rcases Finset.mem_union.mp ha with ha | ha
      · obtain ⟨ha, hat, _, _⟩ := classRest_mem ha
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨hat, (classUnion_mem K a).mpr ⟨S, hS, ha⟩⟩))
      · by_cases h : isOr = true ∧ t ∈ S
        · have h' : isOr = true ∧ t ∈ classUnion K :=
            ⟨h.1, (classUnion_mem K t).mpr ⟨S, hS, h.2⟩⟩
          apply Finset.mem_union_right
          rw [ite_eq_left h']
          rwa [ite_eq_left h] at ha
        · simp only [h, ite_false, Finset.notMem_empty] at ha
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ha)
  · intro ha
    rcases Finset.mem_union.mp ha with ha | ha
    · rcases Finset.mem_union.mp ha with ha | ha
      · obtain ⟨hat, ha⟩ := Finset.mem_erase.mp ha
        obtain ⟨S, hS, haS⟩ := (classUnion_mem K a).mp ha
        by_cases hapq : a = p ∨ a = q
        · apply Or.inr
          have har : a ∈ rest := (Finset.mem_insert.mp (hK S hS haS)).resolve_left hat
          exact Finset.mem_inter.mpr ⟨by simpa only [Finset.mem_insert,
            Finset.mem_singleton] using hapq, har⟩
        · apply Or.inl
          refine ⟨S, hS, Finset.mem_union_left _ ?_⟩
          have hap : a ≠ p := fun h => hapq (Or.inl h)
          have haq : a ≠ q := fun h => hapq (Or.inr h)
          simp only [classRest, Finset.mem_erase]
          exact ⟨haq, hap, hat, haS⟩
      · exact Or.inr ha
    · by_cases h : isOr = true ∧ t ∈ classUnion K
      · rw [ite_eq_left h] at ha
        obtain ⟨S, hS, htS⟩ := (classUnion_mem K t).mp h.2
        apply Or.inl
        refine ⟨S, hS, Finset.mem_union_right _ ?_⟩
        rw [ite_eq_left ⟨h.1, htS⟩]
        exact ha
      · simp only [h, ite_false, Finset.notMem_empty] at ha

lemma class_partition_card (rest : Finset α) (p q : α) (hpq : p ≠ q) :
    (classFresh rest p q).card + (classReused rest p q).card = 2 := by
  simpa [classFresh, classReused, hpq] using
    Finset.card_sdiff_add_card_inter ({p, q} : Finset α) rest

lemma class_frontier_card (rest : Finset α) (p q : α) :
    (insert p (insert q rest)).card = rest.card + (classFresh rest p q).card := by
  simpa [classFresh, Nat.add_comm] using
    (Finset.card_sdiff_add_card ({p, q} : Finset α) rest).symm

lemma classFamilyNext_growth (isOr : Bool) (rest : Finset α) (t p q : α)
    (K : Finset (Finset α)) (ht : t ∉ rest) (hpq : p ≠ q) :
    (insert p (insert q rest)).card + (classFamilyNext isOr rest t p q K).card ≤
      (insert t rest).card + K.card + 1 := by
  have hfamily := classFamilyNext_card isOr rest t p q K
  have hparts := class_partition_card rest p q hpq
  have hfront := class_frontier_card rest p q
  rw [Finset.card_insert_of_notMem ht]
  omega


def classPair (a b : α) : α → Bool := fun x => decide (x = a) || decide (x = b)

lemma classPair_update (a b : α) :
    classPair a b = Function.update (fun x => decide (x = b)) a true := by
  funext x
  by_cases h : x = a
  · subst x
    simp [classPair]
  · simp [classPair, h]

lemma classPair_comm (a b : α) : classPair a b = classPair b a := by
  funext x
  exact Bool.or_comm _ _

lemma orClass_card_le_two {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : (α → Bool) → Bool) (A : ι → κ → Bool) (left : ι → α) (right : κ → α)
    (hpair : ∀ u v, F (classPair (left u) (right v)) = A u v)
    (hrows : Function.Injective A)
    (hcols : Function.Injective (fun v => fun u => A u v))
    (S : Finset α) (hclass : ORClass F S)
    (hsub : S ⊆ Finset.univ.image left ∪ Finset.univ.image right) : S.card ≤ 2 := by
  classical
  let L := Finset.univ.image left
  let R := Finset.univ.image right
  have hL : (S ∩ L).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haS, haL⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbS, hbL⟩ := Finset.mem_inter.mp hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp haL
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hbL
    apply congrArg left
    apply hrows
    funext w
    rw [← hpair u w, ← hpair v w, classPair_update, classPair_update]
    exact hclass _ haS _ hbS _
  have hR : (S ∩ R).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haS, haR⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbS, hbR⟩ := Finset.mem_inter.mp hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp haR
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hbR
    apply congrArg right
    apply hcols
    funext w
    change A w u = A w v
    rw [← hpair w u, ← hpair w v, classPair_comm (left w) (right u),
      classPair_comm (left w) (right v), classPair_update, classPair_update]
    exact hclass _ haS _ hbS _
  have hcover : S = (S ∩ L) ∪ (S ∩ R) := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_union.mp (hsub ha) with hl | hr
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ha, hl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨ha, hr⟩)
    · intro ha
      rcases Finset.mem_union.mp ha with hl | hr
      · exact (Finset.mem_inter.mp hl).1
      · exact (Finset.mem_inter.mp hr).1
  calc
    S.card = ((S ∩ L) ∪ (S ∩ R)).card := congrArg Finset.card hcover
    _ ≤ (S ∩ L).card + (S ∩ R).card := Finset.card_union_le _ _
    _ ≤ 2 := by omega

lemma orClass_valid_card_le_two {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : (α → Bool) → Bool) (A : ι → κ → Bool) (left : ι → α) (right : κ → α)
    (hpair : ∀ u v, F (classPair (left u) (right v)) = A u v)
    (hrows : Function.Injective A)
    (hcols : Function.Injective (fun v => fun u => A u v))
    (S : Finset α) (hclass : ORClass F S) :
    (S ∩ (Finset.univ.image left ∪ Finset.univ.image right)).card ≤ 2 := by
  apply orClass_card_le_two F A left right hpair hrows hcols
  · exact fun a ha b hb => hclass a (Finset.mem_inter.mp ha).1 b (Finset.mem_inter.mp hb).1
  · exact fun a ha => (Finset.mem_inter.mp ha).2


lemma orClasses_valid_union_card {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : (α → Bool) → Bool) (A : ι → κ → Bool) (left : ι → α) (right : κ → α)
    (hpair : ∀ u v, F (classPair (left u) (right v)) = A u v)
    (hrows : Function.Injective A)
    (hcols : Function.Injective (fun v => fun u => A u v))
    (K : Finset (Finset α)) (hK : ∀ S ∈ K, ORClass F S) :
    ((K.biUnion id) ∩ (Finset.univ.image left ∪ Finset.univ.image right)).card ≤ 2 * K.card := by
  classical
  let V := Finset.univ.image left ∪ Finset.univ.image right
  have heq : (K.biUnion id) ∩ V = K.biUnion (fun S => S ∩ V) := by
    ext a
    simp only [Finset.mem_inter, Finset.mem_biUnion, id_eq]
    constructor
    · rintro ⟨⟨S, hS, ha⟩, hv⟩
      exact ⟨S, hS, ha, hv⟩
    · rintro ⟨S, hS, ha, hv⟩
      exact ⟨⟨S, hS, ha⟩, hv⟩
  change ((K.biUnion id) ∩ V).card ≤ _
  rw [heq]
  calc
    (K.biUnion (fun S => S ∩ V)).card ≤ ∑ S ∈ K, (S ∩ V).card := Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ K, 2 := Finset.sum_le_sum fun S hS =>
      orClass_valid_card_le_two F A left right hpair hrows hcols S (hK S hS)
    _ = 2 * K.card := by simp [Nat.mul_comm]


def cycle33 (a b : Fin 33) : Bool :=
  decide (∃ i : Fin 11,
    ((a.val = i.val ∨ a.val = 11 + i.val) ∧
      (b.val = (i.val + 1) % 11 ∨ b.val = 22 + i.val)) ∨
    ((b.val = i.val ∨ b.val = 11 + i.val) ∧
      (a.val = (i.val + 1) % 11 ∨ a.val = 22 + i.val)))

def packedP4A (i : Fin 14) : Fin 33 :=
  ⟨([1, 2, 4, 6, 7, 9, 10, 11, 24, 14, 16, 29, 19, 32] : List Nat)[i.val]! % 33,
    Nat.mod_lt _ (by decide)⟩

def packedP4B (i : Fin 14) : Fin 33 :=
  ⟨([22, 13, 25, 27, 18, 30, 21, 23, 12, 26, 28, 17, 31, 20] : List Nat)[i.val]! % 33,
    Nat.mod_lt _ (by decide)⟩

def packedP4C (i : Fin 14) : Fin 33 :=
  ⟨([11, 24, 14, 16, 29, 19, 32, 1, 2, 4, 6, 7, 9, 10] : List Nat)[i.val]! % 33,
    Nat.mod_lt _ (by decide)⟩

def packedP4D (i : Fin 14) : Fin 33 :=
  ⟨([23, 12, 26, 28, 17, 31, 20, 22, 13, 25, 27, 18, 30, 21] : List Nat)[i.val]! % 33,
    Nat.mod_lt _ (by decide)⟩

def packedP4Wire (i : Fin 14) (j : Fin 4) : Fin 66 :=
  if j.val = 0 then ⟨(packedP4A i).val, by omega⟩
  else if j.val = 1 then ⟨(packedP4B i).val, by omega⟩
  else if j.val = 2 then ⟨33 + (packedP4C i).val, by omega⟩
  else ⟨33 + (packedP4D i).val, by omega⟩

lemma packedP4_edges : ∀ i,
    cycle33 (packedP4A i) (packedP4C i) = true ∧
    cycle33 (packedP4A i) (packedP4D i) = true ∧
    cycle33 (packedP4B i) (packedP4C i) = true ∧
    cycle33 (packedP4B i) (packedP4D i) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma packedP4_disjoint : Function.Injective
    (fun p : Fin 14 × Fin 4 => packedP4Wire p.1 p.2) := by
  decide +kernel

lemma packedP4_hitting_size (S : Finset (Fin 66))
    (h : ∀ i : Fin 14, ∃ j : Fin 4, packedP4Wire i j ∈ S) : 14 ≤ S.card := by
  classical
  choose j hj using h
  let f : Fin 14 → {v // v ∈ S} := fun i => ⟨packedP4Wire i (j i), hj i⟩
  have hf : Function.Injective f := by
    intro i k heq
    have hw : packedP4Wire i (j i) = packedP4Wire k (j k) := congrArg Subtype.val heq
    exact congrArg Prod.fst (@packedP4_disjoint (i, j i) (k, j k) hw)
  have hc := Fintype.card_le_of_injective f hf
  simpa using hc



def zeroWires (S : Finset α) (x : α → Bool) : α → Bool :=
  fun i => if i ∈ S then false else x i

lemma zeroWires_on (S : Finset α) {p q : α} (hp : p ∉ S) (hq : q ∉ S) :
    zeroWires S (on p q) = on p q := by
  funext i
  by_cases hi : i ∈ S
  · have hip : i ≠ p := fun h => hp (h ▸ hi)
    have hiq : i ≠ q := fun h => hq (h ▸ hi)
    simp [zeroWires, hi, on, hip, hiq]
  · simp [zeroWires, hi]


def leftWire (a : Fin 33) : Fin 66 := ⟨a.val, by omega⟩
def rightWire (b : Fin 33) : Fin 66 := ⟨33 + b.val, by omega⟩

omit [DecidableEq α] in
lemma packedP4_hitting_size_generic (wire : Fin 66 → α) (hinj : Function.Injective wire)
    (S : Finset α)
    (h : ∀ i : Fin 14, ∃ j : Fin 4, wire (packedP4Wire i j) ∈ S) : 14 ≤ S.card := by
  classical
  choose j hj using h
  let f : Fin 14 → {v // v ∈ S} := fun i => ⟨wire (packedP4Wire i (j i)), hj i⟩
  have hf : Function.Injective f := by
    intro i k heq
    have hw : packedP4Wire i (j i) = packedP4Wire k (j k) :=
      hinj (congrArg Subtype.val heq)
    exact congrArg Prod.fst (@packedP4_disjoint (i, j i) (k, j k) hw)
  have hc := Fintype.card_le_of_injective f hf
  simpa using hc

theorem cycle33_free_deletion_lower_generic
    (wire : Fin 66 → α) (hinj : Function.Injective wire)
    (F : (α → Bool) → Bool)
    (hrep : ∀ a b : Fin 33, F (on (wire (leftWire a)) (wire (rightWire b))) = cycle33 a b)
    (hsingle : ∀ w : Fin 66, F (on (wire w) (wire w)) = false)
    (S : Finset α)
    (hfree : Free (fun x => F (zeroWires S x))) : 14 ≤ S.card := by
  apply packedP4_hitting_size_generic wire hinj S
  intro i
  by_contra h
  have hn : ∀ j : Fin 4, wire (packedP4Wire i j) ∉ S := by simpa using h
  have hbad := hfree.2 (wire (packedP4Wire i 0)) (wire (packedP4Wire i 1))
    (wire (packedP4Wire i 2)) (wire (packedP4Wire i 3))
  simp only [zeroWires_on S (hn 0) (hn 0), zeroWires_on S (hn 1) (hn 1),
    zeroWires_on S (hn 2) (hn 2), zeroWires_on S (hn 3) (hn 3),
    zeroWires_on S (hn 0) (hn 2), zeroWires_on S (hn 0) (hn 3),
    zeroWires_on S (hn 1) (hn 2), zeroWires_on S (hn 1) (hn 3)] at hbad
  obtain ⟨heac, head, hebc, hebd⟩ := packedP4_edges i
  have he1 : F (on (wire (packedP4Wire i 0)) (wire (packedP4Wire i 2))) = true := by
    simpa [packedP4Wire, leftWire, rightWire, heac] using hrep (packedP4A i) (packedP4C i)
  have he2 : F (on (wire (packedP4Wire i 0)) (wire (packedP4Wire i 3))) = true := by
    simpa [packedP4Wire, leftWire, rightWire, head] using hrep (packedP4A i) (packedP4D i)
  have he3 : F (on (wire (packedP4Wire i 1)) (wire (packedP4Wire i 2))) = true := by
    simpa [packedP4Wire, leftWire, rightWire, hebc] using hrep (packedP4B i) (packedP4C i)
  have he4 : F (on (wire (packedP4Wire i 1)) (wire (packedP4Wire i 3))) = false := by
    simpa [packedP4Wire, leftWire, rightWire, hebd] using hrep (packedP4B i) (packedP4D i)
  have hf := hbad (hsingle _) (hsingle _) (hsingle _) (hsingle _) he1 he2 he3
  rw [he4] at hf
  exact Bool.noConfusion hf


end PEqualNP.Outside.L_meta_9502.Structural
