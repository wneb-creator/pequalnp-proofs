import Mathlib.Logic.Relation
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.Basic

namespace PEqualNP.Outside.L_meta_2590

def combine (t a b : Bool) : Bool := if t then a && b else a || b

def mixed (p a b : ℕ → Bool) (w : ℕ) : Prop :=
  p w = true ∧ a w = false ∧ b w = false

def incoming (n m : ℕ) (left right : ℕ → ℕ) (u v : ℕ) : Prop :=
  ∃ k < m, v = n + k ∧ (u = left k ∨ u = right k)

lemma gate_source_or_predecessor :
    ∀ t pl al bl pr ar br : Bool,
      combine t pl pr = true →
      combine t al ar = false →
      combine t bl br = false →
      (t = true ∧ ((al = true ∧ br = true) ∨ (bl = true ∧ ar = true))) ∨
        (pl = true ∧ al = false ∧ bl = false) ∨
        (pr = true ∧ ar = false ∧ br = false) := by
  decide

lemma unique_source_reachable
    (n m g : ℕ) (left right : ℕ → ℕ) (tag p a b : ℕ → Bool)
    (hinput : ∀ w < n, p w = (a w || b w))
    (hpast : ∀ k < m, left k < n + k ∧ right k < n + k)
    (hval : ∀ k < m,
      p (n + k) = combine (tag k) (p (left k)) (p (right k)) ∧
      a (n + k) = combine (tag k) (a (left k)) (a (right k)) ∧
      b (n + k) = combine (tag k) (b (left k)) (b (right k)))
    (hsource : ∀ k < m, tag k = true →
      ((a (left k) = true ∧ b (right k) = true) ∨
        (b (left k) = true ∧ a (right k) = true)) → k = g) :
    ∀ w < n + m, mixed p a b w →
      Relation.ReflTransGen
        (fun u v => incoming n m left right u v ∧ mixed p a b u ∧ mixed p a b v)
        (n + g) w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hmix
    by_cases hn : w < n
    · obtain ⟨hp, ha, hb⟩ := hmix
      rw [hinput w hn, ha, hb] at hp
      contradiction
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < m := by omega
      obtain ⟨hl, hr⟩ := hpast k hk
      have hmix' := hmix
      obtain ⟨hp, ha, hb⟩ := hmix
      obtain ⟨ep, ea, eb⟩ := hval k hk
      rw [ep] at hp
      rw [ea] at ha
      rw [eb] at hb
      rcases gate_source_or_predecessor (tag k)
          (p (left k)) (a (left k)) (b (left k))
          (p (right k)) (a (right k)) (b (right k)) hp ha hb with hs | hs | hs
      · have hkg : k = g := hsource k hk hs.1 hs.2
        subst k
        exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.tail (ih (left k) hl (by omega) hs)
          ⟨⟨k, hk, rfl, Or.inl rfl⟩, hs, hmix'⟩
      · exact Relation.ReflTransGen.tail (ih (right k) hr (by omega) hs)
          ⟨⟨k, hk, rfl, Or.inr rfl⟩, hs, hmix'⟩

lemma closed_of_earlier_escape
    (R : ℕ → ℕ → Prop) (S : ℕ → Prop) (b : ℕ)
    (hroot : S b)
    (hlt : ∀ u v, R u v → u < v)
    (hexit : ∀ u v, R u v → S u → ¬ S v →
      ∃ z < v, ¬ S z ∧ Relation.ReflTransGen R b z) :
    ∀ w, Relation.ReflTransGen R b w → S w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hp
    rcases Relation.ReflTransGen.cases_tail hp with heq | ⟨u, hu, huv⟩
    · exact heq ▸ hroot
    · by_contra hw
      have hs : S u := ih u (hlt u w huv) hu
      obtain ⟨z, hz, hnz, hpz⟩ := hexit u w huv hs hw
      exact hnz (ih z hz hpz)

lemma le_of_increasing_path
    (R : ℕ → ℕ → Prop) (hlt : ∀ u v, R u v → u < v)
    {u v : ℕ} (hp : Relation.ReflTransGen R u v) : u ≤ v := by
  induction hp with
  | refl => exact Nat.le_refl _
  | tail _ hstep ih => exact Nat.le_trans ih (Nat.le_of_lt (hlt _ _ hstep))

lemma suffix_of_unique_chain
    (R Q : ℕ → ℕ → Prop)
    (hsub : ∀ u v, Q u v → R u v)
    (hlt : ∀ u v, R u v → u < v)
    {s b t : ℕ}
    (hchain : Relation.ReflTransGen
      (fun u v => R u v ∧ ∀ z, R u z → z = v) s b)
    (hbt : b ≤ t)
    (hp : Relation.ReflTransGen Q s t) : Relation.ReflTransGen Q b t := by
  revert hp
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hp => hp
  | @head u v hstep htail ih =>
    intro hp
    rcases Relation.ReflTransGen.cases_head hp with heq | ⟨z, huz, hzt⟩
    · have huv : u < v := hlt u v hstep.1
      have hvb : v ≤ b := le_of_increasing_path _ (fun _ _ h => hlt _ _ h.1) htail
      omega
    · have hzv : z = v := hstep.2 z (hsub u z huz)
      subst z
      exact ih hzt

lemma suffix_before_step_of_unique_chain
    (R Q : ℕ → ℕ → Prop)
    (hsub : ∀ u v, Q u v → R u v)
    (hlt : ∀ u v, R u v → u < v)
    {s b w t : ℕ}
    (hchain : Relation.ReflTransGen
      (fun u v => R u v ∧ ∀ z, R u z → z = v) s b)
    (hbt : b < t)
    (hwt : R w t)
    (hp : Relation.ReflTransGen Q s w) : Relation.ReflTransGen Q b w := by
  revert hp
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hp => hp
  | @head u v hstep htail ih =>
    intro hp
    rcases Relation.ReflTransGen.cases_head hp with heq | ⟨z, huz, hzw⟩
    · have hut : R u t := by simpa only [heq] using hwt
      have htv : t = v := hstep.2 t hut
      have hvb : v ≤ b := le_of_increasing_path _ (fun _ _ h => hlt _ _ h.1) htail
      omega
    · have hzv : z = v := hstep.2 z (hsub u z huz)
      subst z
      exact ih hzw

lemma closed_of_earlier_escape_on_paths
    (R : ℕ → ℕ → Prop) (S : ℕ → Prop) (b : ℕ)
    (hroot : S b)
    (hlt : ∀ u v, R u v → u < v)
    (hexit : ∀ u v, Relation.ReflTransGen R b u → R u v → S u → ¬ S v →
      ∃ z < v, ¬ S z ∧ Relation.ReflTransGen R b z) :
    ∀ w, Relation.ReflTransGen R b w → S w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hp
    rcases Relation.ReflTransGen.cases_tail hp with heq | ⟨u, hu, huv⟩
    · exact heq ▸ hroot
    · by_contra hw
      have hs : S u := ih u (hlt u w huv) hu
      obtain ⟨z, hz, hnz, hpz⟩ := hexit u w hu huv hs hw
      exact hnz (ih z hz hpz)

lemma falling_left : ∀ t cl cr : Bool,
    cl = true → combine t cl cr = false → t = true ∧ cr = false := by
  decide

lemma falling_right : ∀ t cl cr : Bool,
    cr = true → combine t cl cr = false → t = true ∧ cl = false := by
  decide

lemma carrier_obstruction
    (n m g cut out : ℕ) (left right : ℕ → ℕ) (tag p a b c : ℕ → Bool)
    (hinput : ∀ w < n, p w = (a w || b w))
    (hpast : ∀ k < m, left k < n + k ∧ right k < n + k)
    (hval : ∀ k < m,
      p (n + k) = combine (tag k) (p (left k)) (p (right k)) ∧
      a (n + k) = combine (tag k) (a (left k)) (a (right k)) ∧
      b (n + k) = combine (tag k) (b (left k)) (b (right k)) ∧
      c (n + k) = combine (tag k) (c (left k)) (c (right k)))
    (hsource : ∀ k < m, tag k = true →
      ((a (left k) = true ∧ b (right k) = true) ∨
        (b (left k) = true ∧ a (right k) = true)) → k = g)
    (hchain : Relation.ReflTransGen
      (fun u v => incoming n m left right u v ∧
        ∀ z, incoming n m left right u z → z = v) (n + g) cut)
    (hcut : c cut = true)
    (hexit : ∀ k < m, tag k = true → c (n + k) = false →
      (c (left k) = true → a (right k) = false ∧ b (right k) = false) ∧
      (c (right k) = true → a (left k) = false ∧ b (left k) = false))
    (hcutout : cut ≤ out) (hout : out < n + m)
    (hmixout : mixed p a b out) (hcout : c out = false) : False := by
  let R := incoming n m left right
  let Q := fun u v => R u v ∧ mixed p a b u ∧ mixed p a b v
  have hRlt : ∀ u v, R u v → u < v := by
    rintro u v ⟨k, hk, rfl, rfl | rfl⟩
    · exact (hpast k hk).1
    · exact (hpast k hk).2
  have hQlt : ∀ u v, Q u v → u < v := fun u v h => hRlt u v h.1
  have hreach : ∀ w < n + m, mixed p a b w → Relation.ReflTransGen Q (n + g) w :=
    unique_source_reachable n m g left right tag p a b hinput hpast
      (fun k hk => ⟨(hval k hk).1, (hval k hk).2.1, (hval k hk).2.2.1⟩) hsource
  have hclosed : ∀ w, Relation.ReflTransGen Q cut w → c w = true := by
    apply closed_of_earlier_escape_on_paths Q (fun w => c w = true) cut hcut hQlt
    intro u v hcu huv hutrue hvnot
    have hvfalse : c v = false := Bool.eq_false_iff.mpr hvnot
    have hcutv : cut < v := lt_of_le_of_lt (le_of_increasing_path Q hQlt hcu) (hQlt u v huv)
    obtain ⟨k, hk, rfl, hu⟩ := huv.1
    have hptrue := huv.2.2.1
    have hcval := (hval k hk).2.2.2
    have hpval := (hval k hk).1
    rw [hcval] at hvfalse
    rcases hu with rfl | rfl
    · obtain ⟨ht, hother⟩ := falling_left (tag k) _ _ hutrue hvfalse
      have hf : c (n + k) = false := by rw [hcval]; exact hvfalse
      obtain ⟨ha, hb⟩ := (hexit k hk ht hf).1 hutrue
      have hp : p (right k) = true := by
        rw [hpval, combine, ht] at hptrue
        cases h : p (right k) <;> simp_all
      have hz : mixed p a b (right k) := ⟨hp, ha, hb⟩
      have hpath := hreach (right k) (by have := (hpast k hk).2; omega) hz
      have hstep : R (right k) (n + k) := ⟨k, hk, rfl, Or.inr rfl⟩
      have hsuffix := suffix_before_step_of_unique_chain R Q (fun _ _ h => h.1) hRlt
        hchain hcutv hstep hpath
      exact ⟨right k, (hpast k hk).2, by simp [hother], hsuffix⟩
    · obtain ⟨ht, hother⟩ := falling_right (tag k) _ _ hutrue hvfalse
      have hf : c (n + k) = false := by rw [hcval]; exact hvfalse
      obtain ⟨ha, hb⟩ := (hexit k hk ht hf).2 hutrue
      have hp : p (left k) = true := by
        rw [hpval, combine, ht] at hptrue
        cases h : p (left k) <;> simp_all
      have hz : mixed p a b (left k) := ⟨hp, ha, hb⟩
      have hpath := hreach (left k) (by have := (hpast k hk).1; omega) hz
      have hstep : R (left k) (n + k) := ⟨k, hk, rfl, Or.inl rfl⟩
      have hsuffix := suffix_before_step_of_unique_chain R Q (fun _ _ h => h.1) hRlt
        hchain hcutv hstep hpath
      exact ⟨left k, (hpast k hk).1, by simp [hother], hsuffix⟩
  have hpout := suffix_of_unique_chain R Q (fun _ _ h => h.1) hRlt hchain hcutout
    (hreach out hout hmixout)
  have := hclosed out hpout
  simp [hcout] at this

end PEqualNP.Outside.L_meta_2590
