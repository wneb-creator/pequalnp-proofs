import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502.Structural

variable {α : Type} [DecidableEq α]

def on (a c : α) : α → Bool := fun i => decide (i = a) || decide (i = c)

def Dep (F : (α → Bool) → Bool) (N : Finset α) : Prop :=
  ∀ x y : α → Bool, (∀ i ∈ N, x i = y i) → F x = F y

def Free (F : (α → Bool) → Bool) : Prop :=
  F (fun _ => false) = false ∧ ∀ a b c d, F (on a a) = false → F (on b b) = false →
    F (on c c) = false → F (on d d) = false → F (on a c) = true → F (on a d) = true →
    F (on b c) = true → F (on b d) = true

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

end PEqualNP.Outside.L_meta_9502.Structural
