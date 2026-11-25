import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502.Generic

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



end PEqualNP.Outside.L_meta_9502.Generic
