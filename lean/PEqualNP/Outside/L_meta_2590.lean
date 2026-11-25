import PEqualNP.Defs
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

lemma guarded_unique_source_reachable
    (n m g : ℕ) (left right : ℕ → ℕ) (tag p a b : ℕ → Bool)
    (hinput : ∀ w < n, p w = (a w || b w))
    (hpast : ∀ k < m, left k < n + k ∧ right k < n + k)
    (hval : ∀ k < m,
      p (n + k) = combine (tag k) (p (left k)) (p (right k)) ∧
      a (n + k) = combine (tag k) (a (left k)) (a (right k)) ∧
      b (n + k) = combine (tag k) (b (left k)) (b (right k)))
    (hsource : ∀ k < m, tag k = true →
      a (n + k) = false → b (n + k) = false →
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
      · have hkg : k = g := hsource k hk hs.1 hmix'.2.1 hmix'.2.2 hs.2
        subst k
        exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.tail (ih (left k) hl (by omega) hs)
          ⟨⟨k, hk, rfl, Or.inl rfl⟩, hs, hmix'⟩
      · exact Relation.ReflTransGen.tail (ih (right k) hr (by omega) hs)
          ⟨⟨k, hk, rfl, Or.inr rfl⟩, hs, hmix'⟩

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
  exact guarded_unique_source_reachable n m g left right tag p a b hinput hpast hval
    (fun k hk ht _ _ hcross => hsource k hk ht hcross)

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

lemma guarded_carrier_obstruction
    (n m g cut out : ℕ) (left right : ℕ → ℕ) (tag p a b c : ℕ → Bool)
    (hinput : ∀ w < n, p w = (a w || b w))
    (hpast : ∀ k < m, left k < n + k ∧ right k < n + k)
    (hval : ∀ k < m,
      p (n + k) = combine (tag k) (p (left k)) (p (right k)) ∧
      a (n + k) = combine (tag k) (a (left k)) (a (right k)) ∧
      b (n + k) = combine (tag k) (b (left k)) (b (right k)) ∧
      c (n + k) = combine (tag k) (c (left k)) (c (right k)))
    (hsource : ∀ k < m, tag k = true →
      a (n + k) = false → b (n + k) = false →
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
    guarded_unique_source_reachable n m g left right tag p a b hinput hpast
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

lemma guarded_carrier_obstruction_after
    (n m g cut out : ℕ) (left right : ℕ → ℕ) (tag p a b c : ℕ → Bool)
    (hinput : ∀ w < n, p w = (a w || b w))
    (hpast : ∀ k < m, left k < n + k ∧ right k < n + k)
    (hval : ∀ k < m,
      p (n + k) = combine (tag k) (p (left k)) (p (right k)) ∧
      a (n + k) = combine (tag k) (a (left k)) (a (right k)) ∧
      b (n + k) = combine (tag k) (b (left k)) (b (right k)) ∧
      c (n + k) = combine (tag k) (c (left k)) (c (right k)))
    (hsource : ∀ k < m, tag k = true →
      a (n + k) = false → b (n + k) = false →
      ((a (left k) = true ∧ b (right k) = true) ∨
        (b (left k) = true ∧ a (right k) = true)) → k = g)
    (hchain : Relation.ReflTransGen
      (fun u v => incoming n m left right u v ∧
        ∀ z, incoming n m left right u z → z = v) (n + g) cut)
    (hcut : c cut = true)
    (hexit : ∀ k < m, cut < n + k → tag k = true → c (n + k) = false →
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
    guarded_unique_source_reachable n m g left right tag p a b hinput hpast
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
      obtain ⟨ha, hb⟩ := (hexit k hk hcutv ht hf).1 hutrue
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
      obtain ⟨ha, hb⟩ := (hexit k hk hcutv ht hf).2 hutrue
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
  exact guarded_carrier_obstruction n m g cut out left right tag p a b c hinput hpast hval
    (fun k hk ht _ _ hcross => hsource k hk ht hcross)
    hchain hcut hexit hcutout hout hmixout hcout

lemma no_second_path
    (R Q : ℕ → ℕ → Prop)
    (hsub : ∀ u v, Q u v → R u v)
    (hlt : ∀ u v, R u v → u < v)
    {s u v w : ℕ}
    (hchain : Relation.ReflTransGen
      (fun a b => R a b ∧ ∀ z, R a z → z = b) s u)
    (huv : R u v) (hunique : ∀ z, R u z → z = v)
    (hwv : R w v) (hwu : w ≠ u)
    (hp : Relation.ReflTransGen Q s w) : False := by
  have hsuffix := suffix_before_step_of_unique_chain R Q hsub hlt hchain
    (hlt u v huv) hwv hp
  rcases Relation.ReflTransGen.cases_head hsuffix with heq | ⟨z, huz, hzw⟩
  · exact hwu heq.symm
  · have hzv : z = v := hunique z (hsub u z huz)
    have hzwle : z ≤ w := le_of_increasing_path Q (fun a b h => hlt a b (hsub a b h)) hzw
    have hwvlt : w < v := hlt w v hwv
    omega

lemma source_property_of_path
    (R : ℕ → ℕ → Prop) (P : ℕ → Prop)
    (hstep : ∀ u v, R u v → P u)
    {s t : ℕ} (hp : Relation.ReflTransGen R s t) (ht : P t) : P s := by
  rcases Relation.ReflTransGen.cases_head hp with heq | ⟨u, hsu, hut⟩
  · exact heq ▸ ht
  · exact hstep s u hsu

lemma unique_chain_of_all_sources
    {ι : Type} (e₀ : ι) (R : ℕ → ℕ → Prop)
    (Q : ι → ℕ → ℕ → Prop) (P : ι → ℕ → Prop)
    (s out : ℕ)
    (hsub : ∀ e u v, Q e u v → R u v)
    (hlt : ∀ u v, R u v → u < v)
    (hstep : ∀ e u v, Q e u v → P e u)
    (hpaths : ∀ e, Relation.ReflTransGen (Q e) s out)
    (houtput : ∀ e, P e out)
    (hbranch : ∀ u v w, R u v → R u w → v ≠ w → ∃ e, ¬ P e u) :
    Relation.ReflTransGen (fun u v => R u v ∧ ∀ z, R u z → z = v) s out := by
  have hsout : s ≤ out := le_of_increasing_path (Q e₀)
    (fun u v h => hlt u v (hsub e₀ u v h)) (hpaths e₀)
  suffices h : ∀ d w, out - w = d → w ≤ out →
      Relation.ReflTransGen (fun u v => R u v ∧ ∀ z, R u z → z = v) s w →
      Relation.ReflTransGen (fun u v => R u v ∧ ∀ z, R u z → z = v) s out from
    h (out - s) s rfl hsout Relation.ReflTransGen.refl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro w hd hwo hchain
    by_cases hwend : w = out
    · exact hwend ▸ hchain
    have hsuffix (e : ι) : Relation.ReflTransGen (Q e) w out :=
      suffix_of_unique_chain R (Q e) (hsub e) hlt hchain hwo (hpaths e)
    have hwP (e : ι) : P e w :=
      source_property_of_path (Q e) (P e) (hstep e) (hsuffix e) (houtput e)
    rcases Relation.ReflTransGen.cases_head (hsuffix e₀) with heq | ⟨v, hwv, hvout⟩
    · exact (hwend heq).elim
    · have hwvR : R w v := hsub e₀ w v hwv
      have hwvlt : w < v := hlt w v hwvR
      have hvle : v ≤ out := le_of_increasing_path (Q e₀)
        (fun a b h => hlt a b (hsub e₀ a b h)) hvout
      have huniq : ∀ z, R w z → z = v := by
        intro z hwz
        by_contra hz
        obtain ⟨e, he⟩ := hbranch w v z hwvR hwz (Ne.symm hz)
        exact he (hwP e)
      exact ih (out - v) (by omega) v rfl hvle (Relation.ReflTransGen.tail hchain ⟨hwvR, huniq⟩)

lemma source_obstruction
    {ι : Type} (e₀ : ι)
    (n m g out : ℕ) (left right : ℕ → ℕ) (tag q : ℕ → Bool)
    (p a b : ι → ℕ → Bool)
    (hinput : ∀ e w, w < n → p e w = (a e w || b e w))
    (hpast : ∀ k < m, left k < n + k ∧ right k < n + k)
    (hval : ∀ e k, k < m →
      p e (n + k) = combine (tag k) (p e (left k)) (p e (right k)) ∧
      a e (n + k) = combine (tag k) (a e (left k)) (a e (right k)) ∧
      b e (n + k) = combine (tag k) (b e (left k)) (b e (right k)))
    (hqval : ∀ k < m, q (n + k) = combine (tag k) (q (left k)) (q (right k)))
    (hsource : ∀ e k, k < m → tag k = true →
      a e (n + k) = false → b e (n + k) = false →
      ((a e (left k) = true ∧ b e (right k) = true) ∨
        (b e (left k) = true ∧ a e (right k) = true)) → k = g)
    (hbranch : ∀ u v w,
      incoming n m left right u v → incoming n m left right u w → v ≠ w →
      ∃ e, a e u = true ∨ b e u = true)
    (hmiss : ∀ k < m, k ≠ g → tag k = true →
      (∃ e, a e (left k) = false ∧ b e (left k) = false) ∧
      (∃ e, a e (right k) = false ∧ b e (right k) = false))
    (hout : out < n + m)
    (hmixout : ∀ e, mixed (p e) (a e) (b e) out)
    (hqsource : q (n + g) = true) (hqout : q out = false) : False := by
  let R := incoming n m left right
  let Q := fun e u v => R u v ∧ mixed (p e) (a e) (b e) u ∧ mixed (p e) (a e) (b e) v
  have hRlt : ∀ u v, R u v → u < v := by
    rintro u v ⟨k, hk, rfl, rfl | rfl⟩
    · exact (hpast k hk).1
    · exact (hpast k hk).2
  have hreach (e : ι) : ∀ w < n + m, mixed (p e) (a e) (b e) w →
      Relation.ReflTransGen (Q e) (n + g) w :=
    guarded_unique_source_reachable n m g left right tag (p e) (a e) (b e)
      (hinput e) hpast (hval e) (hsource e)
  have hpaths (e : ι) : Relation.ReflTransGen (Q e) (n + g) out :=
    hreach e out hout (hmixout e)
  have hchain : Relation.ReflTransGen
      (fun u v => R u v ∧ ∀ z, R u z → z = v) (n + g) out := by
    apply unique_chain_of_all_sources e₀ R Q (fun e => mixed (p e) (a e) (b e))
      (n + g) out (fun _ _ _ h => h.1) hRlt (fun _ _ _ h => h.2.1) hpaths hmixout
    intro u v w huv huw hvw
    obtain ⟨e, he⟩ := hbranch u v w huv huw hvw
    refine ⟨e, ?_⟩
    rintro ⟨_, ha, hb⟩
    rcases he with he | he
    · rw [ha] at he
      contradiction
    · rw [hb] at he
      contradiction
  have hmixed (e : ι) (w : ℕ)
      (hc : Relation.ReflTransGen
        (fun u v => R u v ∧ ∀ z, R u z → z = v) (n + g) w)
      (hw : w ≤ out) : mixed (p e) (a e) (b e) w :=
    source_property_of_path (Q e) (mixed (p e) (a e) (b e)) (fun _ _ h => h.2.1)
      (suffix_of_unique_chain R (Q e) (fun _ _ h => h.1) hRlt hc hw (hpaths e)) (hmixout e)
  have hpreserve : ∀ w, Relation.ReflTransGen
      (fun u v => R u v ∧ ∀ z, R u z → z = v) (n + g) w → w ≤ out → q w = true := by
    intro w hc
    induction hc with
    | refl => exact fun _ => hqsource
    | @tail u v hprefix hstep ih =>
      intro hvout
      have huv : u < v := hRlt u v hstep.1
      have hqu : q u = true := ih (le_trans (le_of_lt huv) hvout)
      by_contra hqv
      have hqfalse : q v = false := Bool.eq_false_iff.mpr hqv
      have hsu : n + g ≤ u := le_of_increasing_path _ (fun _ _ h => hRlt _ _ h.1) hprefix
      obtain ⟨k, hk, rfl, hu⟩ := hstep.1
      have hkg : k ≠ g := by omega
      rw [hqval k hk] at hqfalse
      rcases hu with rfl | rfl
      · obtain ⟨ht, hother⟩ := falling_left (tag k) _ _ hqu hqfalse
        obtain ⟨e, ha, hb⟩ := (hmiss k hk hkg ht).2
        have hptrue := (hmixed e (n + k) (Relation.ReflTransGen.tail hprefix hstep) hvout).1
        rw [(hval e k hk).1, combine, ht] at hptrue
        have hp : p e (right k) = true := by
          cases h : p e (right k) <;> simp_all
        have hmix : mixed (p e) (a e) (b e) (right k) := ⟨hp, ha, hb⟩
        have hpath := hreach e (right k) (by have := (hpast k hk).2; omega) hmix
        have hmate : R (right k) (n + k) := ⟨k, hk, rfl, Or.inr rfl⟩
        have hne : right k ≠ left k := by
          intro heq
          rw [heq, hqu] at hother
          contradiction
        exact no_second_path R (Q e) (fun _ _ h => h.1) hRlt hprefix
          hstep.1 hstep.2 hmate hne hpath
      · obtain ⟨ht, hother⟩ := falling_right (tag k) _ _ hqu hqfalse
        obtain ⟨e, ha, hb⟩ := (hmiss k hk hkg ht).1
        have hptrue := (hmixed e (n + k) (Relation.ReflTransGen.tail hprefix hstep) hvout).1
        rw [(hval e k hk).1, combine, ht] at hptrue
        have hp : p e (left k) = true := by
          cases h : p e (left k) <;> simp_all
        have hmix : mixed (p e) (a e) (b e) (left k) := ⟨hp, ha, hb⟩
        have hpath := hreach e (left k) (by have := (hpast k hk).1; omega) hmix
        have hmate : R (left k) (n + k) := ⟨k, hk, rfl, Or.inl rfl⟩
        have hne : left k ≠ right k := by
          intro heq
          rw [heq, hqu] at hother
          contradiction
        exact no_second_path R (Q e) (fun _ _ h => h.1) hRlt hprefix
          hstep.1 hstep.2 hmate hne hpath
  have := hpreserve out hchain (le_refl out)
  simp [hqout] at this

lemma unique_chain_or_common_branch
    {ι : Type} (e₀ : ι) (R : ℕ → ℕ → Prop)
    (Q : ι → ℕ → ℕ → Prop) (P : ι → ℕ → Prop)
    (s out : ℕ)
    (hsub : ∀ e u v, Q e u v → R u v)
    (hlt : ∀ u v, R u v → u < v)
    (hstep : ∀ e u v, Q e u v → P e u)
    (hpaths : ∀ e, Relation.ReflTransGen (Q e) s out)
    (houtput : ∀ e, P e out) :
    Relation.ReflTransGen (fun u v => R u v ∧ ∀ z, R u z → z = v) s out ∨
      ∃ cut v w,
        Relation.ReflTransGen (fun u v => R u v ∧ ∀ z, R u z → z = v) s cut ∧
        R cut v ∧ R cut w ∧ v ≠ w ∧ ∀ e, P e cut := by
  have hsout : s ≤ out := le_of_increasing_path (Q e₀)
    (fun u v h => hlt u v (hsub e₀ u v h)) (hpaths e₀)
  suffices h : ∀ d x, out - x = d → x ≤ out →
      Relation.ReflTransGen (fun u v => R u v ∧ ∀ z, R u z → z = v) s x →
      Relation.ReflTransGen (fun u v => R u v ∧ ∀ z, R u z → z = v) s out ∨
        ∃ cut v w,
          Relation.ReflTransGen (fun u v => R u v ∧ ∀ z, R u z → z = v) s cut ∧
          R cut v ∧ R cut w ∧ v ≠ w ∧ ∀ e, P e cut from
    h (out - s) s rfl hsout Relation.ReflTransGen.refl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro x hd hxo hchain
    by_cases hxend : x = out
    · exact Or.inl (hxend ▸ hchain)
    have hsuffix (e : ι) : Relation.ReflTransGen (Q e) x out :=
      suffix_of_unique_chain R (Q e) (hsub e) hlt hchain hxo (hpaths e)
    have hxP (e : ι) : P e x :=
      source_property_of_path (Q e) (P e) (hstep e) (hsuffix e) (houtput e)
    rcases Relation.ReflTransGen.cases_head (hsuffix e₀) with heq | ⟨v, hxv, hvout⟩
    · exact (hxend heq).elim
    · have hxvR : R x v := hsub e₀ x v hxv
      have hxvlt : x < v := hlt x v hxvR
      have hvle : v ≤ out := le_of_increasing_path (Q e₀)
        (fun a b h => hlt a b (hsub e₀ a b h)) hvout
      by_cases hsecond : ∃ w, R x w ∧ v ≠ w
      · obtain ⟨w, hxw, hvw⟩ := hsecond
        exact Or.inr ⟨x, v, w, hchain, hxvR, hxw, hvw, hxP⟩
      · have huniq : ∀ z, R x z → z = v := by
          intro z hxz
          by_contra hz
          exact hsecond ⟨z, hxz, Ne.symm hz⟩
        exact ih (out - v) (by omega) v rfl hvle
          (Relation.ReflTransGen.tail hchain ⟨hxvR, huniq⟩)

lemma chain_source_obstruction
    {ι : Type} (_e₀ : ι)
    (n m g out : ℕ) (left right : ℕ → ℕ) (tag q : ℕ → Bool)
    (p a b : ι → ℕ → Bool)
    (hinput : ∀ e w, w < n → p e w = (a e w || b e w))
    (hpast : ∀ k < m, left k < n + k ∧ right k < n + k)
    (hval : ∀ e k, k < m →
      p e (n + k) = combine (tag k) (p e (left k)) (p e (right k)) ∧
      a e (n + k) = combine (tag k) (a e (left k)) (a e (right k)) ∧
      b e (n + k) = combine (tag k) (b e (left k)) (b e (right k)))
    (hqval : ∀ k < m, q (n + k) = combine (tag k) (q (left k)) (q (right k)))
    (hsource : ∀ e k, k < m → tag k = true →
      a e (n + k) = false → b e (n + k) = false →
      ((a e (left k) = true ∧ b e (right k) = true) ∨
        (b e (left k) = true ∧ a e (right k) = true)) → k = g)
    (hchain : Relation.ReflTransGen
      (fun u v => incoming n m left right u v ∧
        ∀ z, incoming n m left right u z → z = v) (n + g) out)
    (hmiss : ∀ k < m, k ≠ g → tag k = true →
      (∃ e, a e (left k) = false ∧ b e (left k) = false) ∧
      (∃ e, a e (right k) = false ∧ b e (right k) = false))
    (hout : out < n + m)
    (hmixout : ∀ e, mixed (p e) (a e) (b e) out)
    (hqsource : q (n + g) = true) (hqout : q out = false) : False := by
  let R := incoming n m left right
  let Q := fun e u v => R u v ∧ mixed (p e) (a e) (b e) u ∧ mixed (p e) (a e) (b e) v
  have hRlt : ∀ u v, R u v → u < v := by
    rintro u v ⟨k, hk, rfl, rfl | rfl⟩
    · exact (hpast k hk).1
    · exact (hpast k hk).2
  have hreach (e : ι) : ∀ w < n + m, mixed (p e) (a e) (b e) w →
      Relation.ReflTransGen (Q e) (n + g) w :=
    guarded_unique_source_reachable n m g left right tag (p e) (a e) (b e)
      (hinput e) hpast (hval e) (hsource e)
  have hpaths (e : ι) : Relation.ReflTransGen (Q e) (n + g) out :=
    hreach e out hout (hmixout e)
  have hmixed (e : ι) (w : ℕ)
      (hc : Relation.ReflTransGen
        (fun u v => R u v ∧ ∀ z, R u z → z = v) (n + g) w)
      (hw : w ≤ out) : mixed (p e) (a e) (b e) w :=
    source_property_of_path (Q e) (mixed (p e) (a e) (b e)) (fun _ _ h => h.2.1)
      (suffix_of_unique_chain R (Q e) (fun _ _ h => h.1) hRlt hc hw (hpaths e)) (hmixout e)
  have hpreserve : ∀ w, Relation.ReflTransGen
      (fun u v => R u v ∧ ∀ z, R u z → z = v) (n + g) w → w ≤ out → q w = true := by
    intro w hc
    induction hc with
    | refl => exact fun _ => hqsource
    | @tail u v hprefix hstep ih =>
      intro hvout
      have huv : u < v := hRlt u v hstep.1
      have hqu : q u = true := ih (le_trans (le_of_lt huv) hvout)
      by_contra hqv
      have hqfalse : q v = false := Bool.eq_false_iff.mpr hqv
      have hsu : n + g ≤ u := le_of_increasing_path _ (fun _ _ h => hRlt _ _ h.1) hprefix
      obtain ⟨k, hk, rfl, hu⟩ := hstep.1
      have hkg : k ≠ g := by omega
      rw [hqval k hk] at hqfalse
      rcases hu with rfl | rfl
      · obtain ⟨ht, hother⟩ := falling_left (tag k) _ _ hqu hqfalse
        obtain ⟨e, ha, hb⟩ := (hmiss k hk hkg ht).2
        have hptrue := (hmixed e (n + k) (Relation.ReflTransGen.tail hprefix hstep) hvout).1
        rw [(hval e k hk).1, combine, ht] at hptrue
        have hp : p e (right k) = true := by
          cases h : p e (right k) <;> simp_all
        have hmix : mixed (p e) (a e) (b e) (right k) := ⟨hp, ha, hb⟩
        have hpath := hreach e (right k) (by have := (hpast k hk).2; omega) hmix
        have hmate : R (right k) (n + k) := ⟨k, hk, rfl, Or.inr rfl⟩
        have hne : right k ≠ left k := by
          intro heq
          rw [heq, hqu] at hother
          contradiction
        exact no_second_path R (Q e) (fun _ _ h => h.1) hRlt hprefix
          hstep.1 hstep.2 hmate hne hpath
      · obtain ⟨ht, hother⟩ := falling_right (tag k) _ _ hqu hqfalse
        obtain ⟨e, ha, hb⟩ := (hmiss k hk hkg ht).1
        have hptrue := (hmixed e (n + k) (Relation.ReflTransGen.tail hprefix hstep) hvout).1
        rw [(hval e k hk).1, combine, ht] at hptrue
        have hp : p e (left k) = true := by
          cases h : p e (left k) <;> simp_all
        have hmix : mixed (p e) (a e) (b e) (left k) := ⟨hp, ha, hb⟩
        have hpath := hreach e (left k) (by have := (hpast k hk).1; omega) hmix
        have hmate : R (left k) (n + k) := ⟨k, hk, rfl, Or.inl rfl⟩
        have hne : left k ≠ right k := by
          intro heq
          rw [heq, hqu] at hother
          contradiction
        exact no_second_path R (Q e) (fun _ _ h => h.1) hRlt hprefix
          hstep.1 hstep.2 hmate hne hpath
  have := hpreserve out hchain (le_refl out)
  simp [hqout] at this

lemma common_branch_of_separation
    {ι : Type} (e₀ : ι)
    (n m g out : ℕ) (left right : ℕ → ℕ) (tag q : ℕ → Bool)
    (p a b : ι → ℕ → Bool)
    (hinput : ∀ e w, w < n → p e w = (a e w || b e w))
    (hpast : ∀ k < m, left k < n + k ∧ right k < n + k)
    (hval : ∀ e k, k < m →
      p e (n + k) = combine (tag k) (p e (left k)) (p e (right k)) ∧
      a e (n + k) = combine (tag k) (a e (left k)) (a e (right k)) ∧
      b e (n + k) = combine (tag k) (b e (left k)) (b e (right k)))
    (hqval : ∀ k < m, q (n + k) = combine (tag k) (q (left k)) (q (right k)))
    (hsource : ∀ e k, k < m → tag k = true →
      a e (n + k) = false → b e (n + k) = false →
      ((a e (left k) = true ∧ b e (right k) = true) ∨
        (b e (left k) = true ∧ a e (right k) = true)) → k = g)
    (hmiss : ∀ k < m, k ≠ g → tag k = true →
      (∃ e, a e (left k) = false ∧ b e (left k) = false) ∧
      (∃ e, a e (right k) = false ∧ b e (right k) = false))
    (hout : out < n + m)
    (hmixout : ∀ e, mixed (p e) (a e) (b e) out)
    (hqsource : q (n + g) = true) (hqout : q out = false) :
    ∃ cut v w,
      Relation.ReflTransGen
        (fun u v => incoming n m left right u v ∧
          ∀ z, incoming n m left right u z → z = v) (n + g) cut ∧
      incoming n m left right cut v ∧ incoming n m left right cut w ∧
      v ≠ w ∧ ∀ e, mixed (p e) (a e) (b e) cut := by
  let R := incoming n m left right
  let Q := fun e u v => R u v ∧ mixed (p e) (a e) (b e) u ∧ mixed (p e) (a e) (b e) v
  have hRlt : ∀ u v, R u v → u < v := by
    rintro u v ⟨k, hk, rfl, rfl | rfl⟩
    · exact (hpast k hk).1
    · exact (hpast k hk).2
  have hreach (e : ι) : ∀ w < n + m, mixed (p e) (a e) (b e) w →
      Relation.ReflTransGen (Q e) (n + g) w :=
    guarded_unique_source_reachable n m g left right tag (p e) (a e) (b e)
      (hinput e) hpast (hval e) (hsource e)
  have hpaths (e : ι) : Relation.ReflTransGen (Q e) (n + g) out :=
    hreach e out hout (hmixout e)
  rcases unique_chain_or_common_branch e₀ R Q (fun e => mixed (p e) (a e) (b e))
      (n + g) out (fun _ _ _ h => h.1) hRlt (fun _ _ _ h => h.2.1) hpaths hmixout with
      hc | ⟨cut, v, w, hch, hcv, hcw, hvw, hall⟩
  · exact (chain_source_obstruction e₀ n m g out left right tag q p a b
      hinput hpast hval hqval hsource hc hmiss hout hmixout hqsource hqout).elim
  · exact ⟨cut, v, w, hch, hcv, hcw, hvw, hall⟩

-- Circuit normalization and wire counting, adapted from L_meta_971.
namespace DagTools

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

@[local simp] lemma gop_true (a b : Bool) : gop true a b = (a && b) := rfl

@[local simp] lemma gop_false (a b : Bool) : gop false a b = (a || b) := rfl

abbrev Dag := List (Bool × ℕ × ℕ)

def tag (D : Dag) (j : ℕ) : Bool := (D.getD j (false, 0, 0)).1

def opA (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.1

def opB (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.2

def wstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

def wl (D : Dag) (w : List Bool) : List Bool := D.foldl wstep w

def val (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wl D (List.ofFn x)).getD w false

def Strict (n : ℕ) (D : Dag) : Prop :=
  ∀ j, j < D.length → opA D j < n + j ∧ opB D j < n + j ∧ opA D j ≠ opB D j

def readers (D : Dag) (w : ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => opA D j = w ∨ opB D j = w)

def fanout (D : Dag) (w : ℕ) : ℕ := (readers D w).card

def Live (n : ℕ) (D : Dag) : Prop := ∀ w, w + 1 < n + D.length → 1 ≤ fanout D w

def StrictLive (n : ℕ) (D : Dag) : Prop := Strict n D ∧ Live n D ∧ D ≠ []

def outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1

def single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

def supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)

def surplusOn (D : Dag) (K : Finset ℕ) : ℕ := ∑ w ∈ K, (fanout D w - 1)

def inner (n : ℕ) (D : Dag) : Finset ℕ := Finset.range (n + D.length - 1)

def totalSurplus (n : ℕ) (D : Dag) : ℕ := surplusOn D (inner n D)

def Bplus (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => (supp n D w).Nonempty))

def Bzero (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => ¬ (supp n D w).Nonempty))

def branchW (n : ℕ) (D : Dag) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => 2 ≤ fanout D w)

def eligSet (n : ℕ) (D : Dag) : Finset (Fin n) := (branchW n D).biUnion (supp n D)

def ineligSet (n : ℕ) (D : Dag) : Finset (Fin n) := Finset.univ \ eligSet n D

def units (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (inner n D).sigma (fun w => Finset.range (fanout D w - 1))

def unitsPlus (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => (supp n D u.1).Nonempty)

def arcs (D : Dag) : Finset (ℕ × Bool) := Finset.range D.length ×ˢ Finset.univ

def src (D : Dag) (e : ℕ × Bool) : ℕ := if e.2 = true then opB D e.1 else opA D e.1

def exitArcs (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ × Bool) :=
  (arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∉ K)

def merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => n + j ∈ K ∧ opA D j ∈ K ∧ opB D j ∈ K)

def sources (n : ℕ) (K : Finset ℕ) : Finset ℕ := K.filter (fun w => w < n)

def carrierT (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => (supp n D w ∩ T).Nonempty)

def carrierDiff (n : ℕ) (D : Dag) (x y : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)

def PureBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v}

def reservedUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ))

def residualUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  unitsPlus n D \ reservedUnits n D b

lemma tag_eq (D : Dag) (j : ℕ) (h : j < D.length) : tag D j = (D[j]).1 := by
  simp [tag, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma opA_eq (D : Dag) (j : ℕ) (h : j < D.length) : opA D j = (D[j]).2.1 := by
  simp [opA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma opB_eq (D : Dag) (j : ℕ) (h : j < D.length) : opB D j = (D[j]).2.2 := by
  simp [opB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma wl_cons (g : Bool × ℕ × ℕ) (D : Dag) (w : List Bool) :
    wl (g :: D) w = wl D (wstep w g) := rfl

lemma wl_append (D E : Dag) (w : List Bool) : wl (D ++ E) w = wl E (wl D w) := by
  simp [wl, List.foldl_append]

lemma wstep_length (w : List Bool) (g : Bool × ℕ × ℕ) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

lemma wl_length (D : Dag) : ∀ w : List Bool, (wl D w).length = w.length + D.length := by
  induction D with
  | nil => intro w; simp [wl]
  | cons g D ih => intro w; rw [wl_cons, ih, wstep_length]; simp; omega

lemma wstep_getD_lt (w : List Bool) (g : Bool × ℕ × ℕ) (i : ℕ) (h : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma wl_getD_lt (D : Dag) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wl D w).getD i false = w.getD i false := by
  induction D with
  | nil => intro w i _; rfl
  | cons g D ih =>
    intro w i h
    rw [wl_cons, ih _ _ (by rw [wstep_length]; omega), wstep_getD_lt _ _ _ h]

lemma getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma wstep_getD_last (w : List Bool) (g : Bool × ℕ × ℕ) :
    (wstep w g).getD w.length false = gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false) := by
  simp [wstep, List.getD_eq_getElem?_getD]

lemma wl_getD_gate (D : Dag) (w : List Bool) (j : ℕ) (hj : j < D.length) :
    (wl D w).getD (w.length + j) false =
      gop (tag D j) ((wl (D.take j) w).getD (opA D j) false)
        ((wl (D.take j) w).getD (opB D j) false) := by
  have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1) := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  rw [tag_eq D j hj, opA_eq D j hj, opB_eq D j hj]
  conv_lhs => rw [hsplit, wl_append, wl_cons]
  rw [wl_getD_lt _ _ _ (by rw [wstep_length, hlen]; omega), ← hlen, wstep_getD_last]

lemma wl_take_getD (D : Dag) (w : List Bool) (j i : ℕ) (hi : i < w.length + j)
    (hj : j ≤ D.length) :
    (wl (D.take j) w).getD i false = (wl D w).getD i false := by
  have hsplit : D = D.take j ++ D.drop j := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  conv_rhs => rw [hsplit, wl_append]
  rw [wl_getD_lt (D.drop j) (wl (D.take j) w) i (by rw [hlen]; exact hi)]

lemma val_input (D : Dag) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val D x i = x ⟨i, h⟩ := by
  unfold val
  rw [wl_getD_lt _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

lemma val_ge (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : n + D.length ≤ w) :
    val D x w = false := by
  unfold val
  exact getD_ge _ _ (by rw [wl_length]; simpa using h)

lemma val_take (D : Dag) {n : ℕ} (x : Fin n → Bool) (k w : ℕ) (hw : w < n + k)
    (hk : k ≤ D.length) : val (D.take k) x w = val D x w := by
  unfold val
  exact wl_take_getD D _ k w (by simpa using hw) hk

lemma val_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  have h := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [h, wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]

lemma val_unique {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (f : ℕ → Bool)
    (hin : ∀ i (h : i < n), f i = x ⟨i, h⟩)
    (hg : ∀ j, j < D.length → f (n + j) = gop (tag D j) (f (opA D j)) (f (opB D j))) :
    ∀ w, w < n + D.length → val D x w = f w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · rw [val_input D x w hn, hin w hn]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      obtain ⟨ha, hb, -⟩ := hS j hj
      rw [val_gate hS x j hj, hg j hj, ih _ ha (by omega), ih _ hb (by omega)]

abbrev Ref := Bool ⊕ ℕ

def refVal (W : List Bool) : Ref → Bool
  | Sum.inl b => b
  | Sum.inr k => W.getD k false

def na_look (m : List Ref) (i : ℕ) : Ref := m.getD i (Sum.inl false)

def na_comb (t : Bool) : Ref → Ref → Ref ⊕ (ℕ × ℕ)
  | Sum.inl a, r => Sum.inl (if a = t then r else Sum.inl a)
  | Sum.inr i, Sum.inl b => Sum.inl (if b = t then Sum.inr i else Sum.inl b)
  | Sum.inr i, Sum.inr j => if i = j then Sum.inl (Sum.inr i) else Sum.inr (i, j)

def na_isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def na_step (n : ℕ) (st : List Ref × Dag) (g : Gate) : List Ref × Dag :=
  match g.inputs with
  | [] => (st.1 ++ [Sum.inl (na_isAnd g.op)], st.2)
  | [a] => (st.1 ++ [na_look st.1 a], st.2)
  | a :: b :: _ =>
    match na_comb (na_isAnd g.op) (na_look st.1 a) (na_look st.1 b) with
    | Sum.inl r => (st.1 ++ [r], st.2)
    | Sum.inr p => (st.1 ++ [Sum.inr (n + st.2.length)], st.2 ++ [(na_isAnd g.op, p.1, p.2)])

def na_ok (B : ℕ) : Ref → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < B

def na_Good (n : ℕ) (st : List Ref × Dag) : Prop :=
  Strict n st.2 ∧ ∀ r ∈ st.1, na_ok (n + st.2.length) r

lemma na_ok_mono {B B' : ℕ} (h : B ≤ B') (r : Ref) (hr : na_ok B r) : na_ok B' r := by
  rcases r with b | k
  · trivial
  · exact lt_of_lt_of_le hr h

lemma na_look_val (W : List Bool) (m : List Ref) (i : ℕ) :
    refVal W (na_look m i) = (m.map (refVal W)).getD i false := by
  simp only [na_look, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases m[i]? <;> rfl

lemma na_look_ok (B : ℕ) (m : List Ref) (hm : ∀ r ∈ m, na_ok B r) (i : ℕ) :
    na_ok B (na_look m i) := by
  simp only [na_look, List.getD_eq_getElem?_getD]
  rcases h : m[i]? with _ | r
  · trivial
  · exact hm r (List.mem_of_getElem? h)

lemma na_refVal_wstep (W : List Bool) (g : Bool × ℕ × ℕ) (r : Ref) (hr : na_ok W.length r) :
    refVal (wstep W g) r = refVal W r := by
  rcases r with b | k
  · rfl
  · exact wstep_getD_lt W g k hr

lemma na_comb_inl (t : Bool) (W : List Bool) (a b r : Ref) (h : na_comb t a b = Sum.inl r) :
    refVal W r = gop t (refVal W a) (refVal W b) := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h
    cases t <;> cases a <;> simp [refVal]
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h
      cases t <;> cases b <;> simp [refVal]
    · simp only [na_comb] at h
      split_ifs at h with hij
      simp only [Sum.inl.injEq] at h
      subst h; subst hij
      cases t <;> simp [refVal]

lemma na_comb_ok (B : ℕ) (t : Bool) (a b r : Ref) (ha : na_ok B a) (hb : na_ok B b)
    (h : na_comb t a b = Sum.inl r) : na_ok B r := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h; split_ifs
    · exact hb
    · trivial
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h; split_ifs
      · exact ha
      · trivial
    · simp only [na_comb] at h
      split_ifs at h
      simp only [Sum.inl.injEq] at h
      subst h; exact ha

lemma na_comb_inr (t : Bool) (a b : Ref) (p : ℕ × ℕ) (h : na_comb t a b = Sum.inr p) :
    a = Sum.inr p.1 ∧ b = Sum.inr p.2 ∧ p.1 ≠ p.2 := by
  rcases a with a | i
  · simp [na_comb] at h
  · rcases b with b | j
    · simp [na_comb] at h
    · simp only [na_comb] at h
      split_ifs at h with hij
      cases h
      exact ⟨rfl, rfl, hij⟩

lemma na_eval0 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    op.eval [] = na_isAnd op := by
  rcases hop with rfl | rfl <;> rfl

lemma na_eval1 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (u : Bool) :
    op.eval [u] = u := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval]

lemma na_eval2 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (u v : Bool) : op.eval [u, v] = gop (na_isAnd op) u v := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval, na_isAnd]

lemma na_getD_append_lt (D E : Dag) (k : ℕ) (h : k < D.length) :
    (D ++ E).getD k (false, 0, 0) = D.getD k (false, 0, 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma na_getD_snoc (D : Dag) (g : Bool × ℕ × ℕ) :
    (D ++ [g]).getD D.length (false, 0, 0) = g := by
  simp [List.getD_eq_getElem?_getD]

lemma na_strict_snoc {n : ℕ} {D : Dag} (hS : Strict n D) (t : Bool) (i j : ℕ)
    (hi : i < n + D.length) (hj : j < n + D.length) (hij : i ≠ j) :
    Strict n (D ++ [(t, i, j)]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  by_cases hk' : k < D.length
  · simp only [opA, opB, na_getD_append_lt D _ k hk']
    exact hS k hk'
  · have hkD : k = D.length := by omega
    subst hkD
    simp only [opA, opB, na_getD_snoc]
    exact ⟨hi, hj, hij⟩

lemma na_strict_take {n : ℕ} {D : Dag} (hS : Strict n D) (k : ℕ) : Strict n (D.take k) := by
  intro j hj
  simp only [List.length_take] at hj
  have hj1 : j < k := by omega
  have hj2 : j < D.length := by omega
  have e : (D.take k).getD j (false, 0, 0) = D.getD j (false, 0, 0) := by
    simp [List.getD_eq_getElem?_getD, hj1]
  simp only [opA, opB, e]
  exact hS j hj2

lemma na_step_spec (n : ℕ) (st : List Ref × Dag) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : na_Good n st) :
    na_Good n (na_step n st g) ∧ (na_step n st g).2.length ≤ st.2.length + 1 ∧
    ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
      (na_step n st g).1.map (refVal (wl (na_step n st g).2 (List.ofFn x))) =
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
  obtain ⟨m, D⟩ := st
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  obtain ⟨hS, hok⟩ := h
  dsimp only at hS hok hop hlen ⊢
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · trivial
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, refVal, na_eval0 op hop]
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · exact na_look_ok _ m hok a
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, na_eval1 op hop,
        na_look_val]
  · have hla := na_look_ok _ m hok a
    have hlb := na_look_ok _ m hok b
    rcases hc : na_comb (na_isAnd op) (na_look m a) (na_look m b) with r | p
    · refine ⟨⟨by simpa only [na_step, hc] using hS, ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact hok r' hr
        · exact na_comb_ok _ _ _ _ _ hla hlb hc
      · subst hw
        simp only [na_step, hc, List.map_append, List.map_cons, List.map_nil, na_eval2 op hop,
          na_comb_inl _ (wl D (List.ofFn x)) _ _ _ hc, na_look_val]
    · obtain ⟨ea, eb, hne⟩ := na_comb_inr _ _ _ _ hc
      rw [ea] at hla
      rw [eb] at hlb
      have hS' := na_strict_snoc hS (na_isAnd op) p.1 p.2 hla hlb hne
      refine ⟨⟨by simpa only [na_step, hc] using hS', ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton, List.length_append,
          List.length_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact na_ok_mono (by omega) r' (hok r' hr)
        · show n + D.length < n + (D.length + 1)
          omega
      · subst hw
        have hWlen : (wl D (List.ofFn x)).length = n + D.length := by
          rw [wl_length, List.length_ofFn]
        have hW' : wl (D ++ [(na_isAnd op, p.1, p.2)]) (List.ofFn x) =
            wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2) := by
          rw [wl_append]; rfl
        have h1 : m.map (refVal (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2))) =
            m.map (refVal (wl D (List.ofFn x))) :=
          List.map_congr_left (fun r hr => na_refVal_wstep _ _ r (by rw [hWlen]; exact hok r hr))
        have h2 : (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2)).getD (n + D.length) false =
            gop (na_isAnd op) ((m.map (refVal (wl D (List.ofFn x)))).getD a false)
              ((m.map (refVal (wl D (List.ofFn x)))).getD b false) := by
          rw [← hWlen, wstep_getD_last, ← na_look_val, ← na_look_val, ea, eb]; rfl
        simp only [na_step, hc, hW', List.map_append, List.map_cons, List.map_nil, h1, refVal,
          h2, na_eval2 op hop]
  · simp at hlen

lemma na_fold_spec (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ st : List Ref × Dag, na_Good n st →
      na_Good n (gs.foldl (na_step n) st) ∧
      (gs.foldl (na_step n) st).2.length ≤ st.2.length + gs.length ∧
      ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
        (gs.foldl (na_step n) st).1.map
            (refVal (wl (gs.foldl (na_step n) st).2 (List.ofFn x))) =
          gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro st h; exact ⟨h, by simp, fun x w hw => hw⟩
  | cons g gs ih =>
    intro st h
    obtain ⟨h1, h2, h3⟩ := na_step_spec n st g (hgs g (by simp)) h
    obtain ⟨i1, i2, i3⟩ := ih (fun g' hg' => hgs g' (by simp [hg'])) _ h1
    refine ⟨i1, ?_, fun x w hw => ?_⟩
    · simp only [List.foldl_cons, List.length_cons]; omega
    · simp only [List.foldl_cons]; exact i3 x _ (h3 x w hw)

lemma na_init (n : ℕ) (x : Fin n → Bool) :
    ((List.range n).map Sum.inr).map (refVal (wl ([] : Dag) (List.ofFn x))) = List.ofFn x := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [refVal, wl, List.getD_eq_getElem?_getD, h1]

lemma exists_strict_of_monotone2 {n : ℕ} (C : Circuit) (hmono : Monotone2 C) :
    (∃ b : Bool, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = b) ∨
    (∃ i : Fin n, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = x i) ∨
    (∃ D : Dag, Strict n D ∧ D ≠ [] ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x)) := by
  have h0 : na_Good n ((List.range n).map Sum.inr, ([] : Dag)) := by
    refine ⟨fun j hj => absurd hj (by simp), fun r hr => ?_⟩
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    simpa [na_ok] using hk
  obtain ⟨⟨hS, hok⟩, hlen, hsem⟩ := na_fold_spec n C.gates hmono _ h0
  generalize C.gates.foldl (na_step n) ((List.range n).map Sum.inr, ([] : Dag)) = st
    at hS hok hlen hsem
  obtain ⟨m, D⟩ := st
  dsimp only at hS hok hlen hsem
  have hev : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = refVal (wl D (List.ofFn x)) (na_look m C.output) := by
    intro x
    rw [na_look_val, hsem x (List.ofFn x) (na_init n x)]
    rfl
  have hk := na_look_ok _ m hok C.output
  rcases hr : na_look m C.output with b | k
  · exact Or.inl ⟨b, fun x => by rw [hev x, hr]; rfl⟩
  · rw [hr] at hk
    have hk' : k < n + D.length := hk
    by_cases hkn : k < n
    · exact Or.inr (Or.inl ⟨⟨k, hkn⟩, fun x => by rw [hev x, hr]; exact val_input D x k hkn⟩)
    · have hl : (D.take (k - n + 1)).length = k - n + 1 := by
        rw [List.length_take]; omega
      refine Or.inr (Or.inr ⟨D.take (k - n + 1), na_strict_take hS _, ?_, ?_, fun x => ?_⟩)
      · intro h
        rw [h] at hl
        simp at hl
      · rw [hl]
        simp only [List.length_nil, Nat.zero_add] at hlen
        unfold Circuit.size
        omega
      · have ho : outW n (D.take (k - n + 1)) = k := by unfold outW; rw [hl]; omega
        rw [ho, val_take D x (k - n + 1) k (by omega) (by omega), hev x, hr]
        rfl

lemma na_no_reader {D : Dag} {w : ℕ} (h : fanout D w = 0) (j : ℕ) (hj : j < D.length) :
    opA D j ≠ w ∧ opB D j ≠ w := by
  unfold fanout readers at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  have := h (Finset.mem_range.mpr hj)
  tauto

def na_sh (c a : ℕ) : ℕ := if c < a then a - 1 else a

def na_up (c w : ℕ) : ℕ := if w < c then w else w + 1

def na_del (n j : ℕ) (D : Dag) : Dag :=
  (D.eraseIdx j).map (fun g => (g.1, na_sh (n + j) g.2.1, na_sh (n + j) g.2.2))

lemma na_del_length (n j : ℕ) (D : Dag) (hj : j < D.length) :
    (na_del n j D).length = D.length - 1 := by
  simp [na_del, List.length_eraseIdx, hj]

lemma na_del_ops (n j : ℕ) (D : Dag) (k : ℕ) (hk : na_up j k < D.length) :
    tag (na_del n j D) k = tag D (na_up j k) ∧
    opA (na_del n j D) k = na_sh (n + j) (opA D (na_up j k)) ∧
    opB (na_del n j D) k = na_sh (n + j) (opB D (na_up j k)) := by
  have e : (na_del n j D).getD k (false, 0, 0) =
      ((D.getD (na_up j k) (false, 0, 0)).1, na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.1,
        na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.2) := by
    simp only [na_del, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eraseIdx]
    unfold na_up at hk ⊢
    split_ifs at hk ⊢ <;> simp [List.getElem?_eq_getElem hk]
  unfold tag opA opB
  rw [e]
  exact ⟨rfl, rfl, rfl⟩

lemma na_del_strict {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) : Strict n (na_del n j D) := by
  intro k hk
  rw [na_del_length n j D hj] at hk
  have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
  have hk2 : (k < j ∧ na_up j k = k) ∨ (j ≤ k ∧ na_up j k = k + 1) := by
    unfold na_up; split_ifs <;> omega
  obtain ⟨ha, hb, hab⟩ := hS _ hk'
  obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
  obtain ⟨-, ea, eb⟩ := na_del_ops n j D k hk'
  rw [ea, eb]
  generalize na_up j k = k' at *
  generalize opA D k' = a at *
  generalize opB D k' = b at *
  refine ⟨?_, ?_, ?_⟩ <;> unfold na_sh <;> split_ifs <;> omega

lemma na_del_val {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) (x : Fin n → Bool) (w : ℕ) (hw : w < n + (D.length - 1)) :
    val (na_del n j D) x w = val D x (na_up (n + j) w) := by
  refine val_unique (na_del_strict hS j hj hf) x (fun u => val D x (na_up (n + j) u))
    (fun i hi => ?_) (fun k hk => ?_) w (by rw [na_del_length n j D hj]; exact hw)
  · have e : na_up (n + j) i = i := by unfold na_up; split_ifs <;> omega
    show val D x (na_up (n + j) i) = x ⟨i, hi⟩
    rw [e]; exact val_input D x i hi
  · rw [na_del_length n j D hj] at hk
    have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
    obtain ⟨et, ea, eb⟩ := na_del_ops n j D k hk'
    obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
    have e1 : na_up (n + j) (n + k) = n + na_up j k := by unfold na_up; split_ifs <;> omega
    have e2 : ∀ a, a ≠ n + j → na_up (n + j) (na_sh (n + j) a) = a := by
      intro a ha; unfold na_up na_sh; split_ifs <;> omega
    show val D x (na_up (n + j) (n + k)) = gop (tag (na_del n j D) k)
      (val D x (na_up (n + j) (opA (na_del n j D) k)))
      (val D x (na_up (n + j) (opB (na_del n j D) k)))
    rw [e1, et, ea, eb, e2 _ ra, e2 _ rb]
    exact val_gate hS x _ hk'

lemma na_live_aux {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y) :
    ∀ (s : ℕ) (D : Dag), D.length = s → Strict n D → D ≠ [] →
      (∀ x : Fin n → Bool, val D x (outW n D) = F x) →
      ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ s ∧
        ∀ x : Fin n → Bool, val D' x (outW n D') = F x := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro D hlen hS hne hD
    have hpos : 0 < D.length := List.length_pos_iff.mpr hne
    by_cases hL : Live n D
    · exact ⟨D, ⟨hS, hL, hne⟩, hlen.le, hD⟩
    · obtain ⟨w, hw, hf0⟩ : ∃ w, w + 1 < n + D.length ∧ fanout D w = 0 := by
        by_contra hcon
        exact hL (fun w hw => by
          by_contra h0
          exact hcon ⟨w, hw, by omega⟩)
      by_cases hwn : w < n
      · exfalso
        obtain ⟨x, y, hxy, hFne⟩ := hess ⟨w, hwn⟩
        apply hFne
        rw [← hD x, ← hD y]
        have hout : outW n D ≠ w := by unfold outW; omega
        have key := val_unique hS y (fun u => if u = w then y ⟨w, hwn⟩ else val D x u)
          (fun i hi => by
            by_cases hiw : i = w
            · subst hiw; simp
            · simp only [hiw, ite_false]
              rw [val_input D x i hi]
              exact hxy ⟨i, hi⟩ (fun h => hiw (congrArg Fin.val h)))
          (fun j hj => by
            obtain ⟨ha, hb⟩ := na_no_reader hf0 j hj
            have hnj : n + j ≠ w := by omega
            simp only [hnj, ha, hb, ite_false]
            exact val_gate hS x j hj)
          (outW n D) (by unfold outW; omega)
        simp only [hout, ite_false] at key
        exact key.symm
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        have hl := na_del_length n j D hj
        obtain ⟨D', h1, h2, h3⟩ := ih (D.length - 1) (by omega) (na_del n j D) hl
          (na_del_strict hS j hj hf0)
          (fun h => by rw [h] at hl; simp at hl; omega)
          (fun x => by
            have ho : outW n (na_del n j D) = n + (D.length - 1) - 1 := by unfold outW; rw [hl]
            have hu : na_up (n + j) (n + (D.length - 1) - 1) = outW n D := by
              unfold na_up outW; split_ifs <;> omega
            rw [ho, na_del_val hS j hj hf0 x _ (by omega), hu]
            exact hD x)
        exact ⟨D', h1, by omega, h3⟩

lemma exists_strictLive_of_strict {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x : Fin n → Bool, val D x (outW n D) = F x) :
    ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ D.length ∧
      ∀ x : Fin n → Bool, val D' x (outW n D') = F x :=
  na_live_aux F hess D.length D rfl hS hne hD

lemma normalize_strictLive {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (hnc : ∀ b : Bool, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ b)
    (hnp : ∀ i : Fin n, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ x i)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Dag, StrictLive n D ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x) := by
  rcases exists_strict_of_monotone2 (n := n) C hmono with
    ⟨b, hb⟩ | ⟨i, hi⟩ | ⟨D, hS, hne, hlen, hD⟩
  · obtain ⟨x, hx⟩ := hnc b
    exact absurd (hb x) hx
  · obtain ⟨x, hx⟩ := hnp i
    exact absurd (hi x) hx
  · obtain ⟨D', h1, h2, h3⟩ :=
      exists_strictLive_of_strict (fun x => C.eval (List.ofFn x)) hess D hS hne hD
    exact ⟨D', h1, by omega, h3⟩

section SurplusFlow

variable {n : ℕ} {D : Dag}

lemma sb_mem_inner {w : ℕ} : w ∈ inner n D ↔ w + 1 < n + D.length := by
  unfold inner; rw [Finset.mem_range]; omega

lemma sb_src_false (j : ℕ) : src D (j, false) = opA D j := by simp [src]

lemma sb_src_true (j : ℕ) : src D (j, true) = opB D j := by simp [src]

lemma fanout_eq_zero_of_ge (hS : Strict n D) (w : ℕ) (h : n + D.length ≤ w + 1) :
    fanout D w = 0 := by
  unfold fanout readers
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  have hj2 := Finset.mem_range.mp hj
  have := hS j hj2
  omega

lemma lt_of_fanout_pos (hS : Strict n D) {w : ℕ} (h : 1 ≤ fanout D w) :
    w + 1 < n + D.length := by
  by_contra hc
  have := fanout_eq_zero_of_ge hS w (by omega)
  omega

lemma sb_card_arcs_filter (P : ℕ × Bool → Prop) [DecidablePred P] :
    ((arcs D).filter P).card = ∑ j ∈ Finset.range D.length,
      ((if P (j, false) then 1 else 0) + (if P (j, true) then 1 else 0)) := by
  rw [Finset.card_filter, arcs, Finset.sum_product]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fintype.sum_bool, add_comm]

lemma sb_card_arcs : (arcs D).card = 2 * D.length := by
  simp [arcs, Finset.card_product, Nat.mul_comm]

lemma sb_src_lt (hS : Strict n D) (e : ℕ × Bool) (he : e ∈ arcs D) :
    src D e + 1 < n + D.length := by
  obtain ⟨j, c⟩ := e
  have hj : j < D.length := by simpa [arcs] using he
  have := hS j hj
  cases c
  · rw [sb_src_false]; omega
  · rw [sb_src_true]; omega

lemma sb_fanout_arcs (hS : Strict n D) (w : ℕ) :
    fanout D w = ((arcs D).filter (fun e => src D e = w)).card := by
  rw [sb_card_arcs_filter, fanout, readers, Finset.card_filter]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have := (hS j (Finset.mem_range.mp hj)).2.2
  rw [sb_src_false, sb_src_true]
  split_ifs <;> omega

lemma sb_sum_fanout_eq (hS : Strict n D) (K : Finset ℕ) :
    ∑ w ∈ K, fanout D w = ((arcs D).filter (fun e => src D e ∈ K)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := src D)
    (s := (arcs D).filter (fun e => src D e ∈ K)) (t := K)
    (fun e he => Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2)]
  refine Finset.sum_congr rfl (fun w hw => ?_)
  rw [sb_fanout_arcs hS, Finset.filter_filter]
  congr 1
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, rfl⟩; exact ⟨he, hw, rfl⟩
  · rintro ⟨he, -, h⟩; exact ⟨he, h⟩

lemma sb_surplus_add_card {K : Finset ℕ} (hL : ∀ w ∈ K, 1 ≤ fanout D w) :
    surplusOn D K + K.card = ∑ w ∈ K, fanout D w := by
  rw [surplusOn, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w hw => Nat.sub_add_cancel (hL w hw))

lemma surplus_identity (h : StrictLive n D) : totalSurplus n D + n = D.length + 1 := by
  obtain ⟨hS, hL, hne⟩ := h
  have hpos : 0 < D.length := List.length_pos_iff.mpr hne
  have h1 : surplusOn D (inner n D) + (inner n D).card = ∑ w ∈ inner n D, fanout D w :=
    sb_surplus_add_card (fun w hw => hL w (sb_mem_inner.mp hw))
  have h2 : ∑ w ∈ inner n D, fanout D w = 2 * D.length := by
    rw [sb_sum_fanout_eq hS, Finset.filter_true_of_mem, sb_card_arcs]
    intro e he
    exact sb_mem_inner.mpr (sb_src_lt hS e he)
  have h3 : (inner n D).card = n + D.length - 1 := Finset.card_range _
  unfold totalSurplus
  omega

lemma totalSurplus_split (n : ℕ) (D : Dag) : totalSurplus n D = Bplus n D + Bzero n D := by
  unfold totalSurplus Bplus Bzero surplusOn
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

lemma live_reaches_out (h : StrictLive n D) (w : ℕ) (hw : w < n + D.length) :
    Relation.ReflTransGen (fun a b => b < n + D.length ∧ n ≤ b ∧
      (opA D (b - n) = a ∨ opB D (b - n) = a)) w (outW n D) := by
  obtain ⟨hS, hL, -⟩ := h
  generalize hk : n + D.length - w = k
  induction k using Nat.strong_induction_on generalizing w with
  | _ k ih =>
    by_cases hlast : w + 1 = n + D.length
    · have hw2 : w = outW n D := by unfold outW; omega
      rw [hw2]
    · obtain ⟨j, hj⟩ := Finset.card_pos.mp (hL w (by omega))
      simp only [readers, Finset.mem_filter, Finset.mem_range] at hj
      have hs := hS j hj.1
      refine Relation.ReflTransGen.head (b := n + j) ⟨by omega, by omega, ?_⟩
        (ih (n + D.length - (n + j)) (by omega) (n + j) (by omega) rfl)
      simpa using hj.2

lemma mem_supp {v : Fin n} {w : ℕ} : v ∈ supp n D w ↔ val D (single v) w = true := by
  simp [supp]

lemma val_mono (hS : Strict n D) (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) : val D x w = true → val D y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn]; exact hxy _
    · by_cases hw : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        rw [val_gate hS x j hj, val_gate hS y j hj]
        have h1 := ih _ ha
        have h2 := ih _ hb
        cases tag D j <;>
          simp only [gop_true, gop_false, Bool.and_eq_true, Bool.or_eq_true] <;> tauto
      · rw [val_ge D x w (by omega)]; simp

lemma supp_input (D : Dag) (i : Fin n) : supp n D i.val = {i} := by
  ext v
  rw [mem_supp, val_input D (single v) i.val i.isLt]
  simp [single, eq_comm]

lemma supp_ge (D : Dag) (w : ℕ) (h : n + D.length ≤ w) : supp n D w = ∅ := by
  ext v
  simp [mem_supp, val_ge D (single v) w h]

lemma supp_gate (hS : Strict n D) (j : ℕ) (hj : j < D.length) :
    supp n D (n + j) = if tag D j = true then supp n D (opA D j) ∩ supp n D (opB D j)
      else supp n D (opA D j) ∪ supp n D (opB D j) := by
  ext v
  rw [mem_supp, val_gate hS _ j hj]
  cases tag D j <;> simp [mem_supp]

lemma carrier_flow (h : StrictLive n D) (K : Finset ℕ) (hK : K ⊆ inner n D)
    (hpred : ∀ j, j < D.length → n + j ∈ K → opA D j ∈ K ∨ opB D j ∈ K) :
    (exitArcs n D K).card + (merges n D K).card = (sources n K).card + surplusOn D K := by
  obtain ⟨hS, hL, -⟩ := h
  have hKlt : ∀ w ∈ K, w + 1 < n + D.length := fun w hw => sb_mem_inner.mp (hK hw)
  have h1 : surplusOn D K + K.card = ((arcs D).filter (fun e => src D e ∈ K)).card := by
    rw [← sb_sum_fanout_eq hS, sb_surplus_add_card (fun w hw => hL w (hKlt w hw))]
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (arcs D).filter (fun e => src D e ∈ K)) (fun e : ℕ × Bool => n + e.1 ∈ K)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have h3 : ((arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∈ K)).card =
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card + (merges n D K).card := by
    rw [sb_card_arcs_filter, merges, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have := hpred j (Finset.mem_range.mp hj)
    rw [sb_src_false, sb_src_true]
    by_cases hj2 : n + j ∈ K <;> by_cases ha : opA D j ∈ K <;> by_cases hb : opB D j ∈ K <;>
      simp_all
  have h4 : K.card = (sources n K).card +
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := K) (fun w => w < n), sources]
    congr 1
    have himg : K.filter (fun w => ¬ w < n) =
        ((Finset.range D.length).filter (fun j => n + j ∈ K)).image (fun j => n + j) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hw, hn⟩
        have := hKlt w hw
        exact ⟨w - n, ⟨by omega, by rwa [Nat.add_sub_cancel' (by omega)]⟩, by omega⟩
      · rintro ⟨j, ⟨-, hj⟩, rfl⟩
        exact ⟨hj, by omega⟩
    rw [himg, Finset.card_image_of_injective _ (add_right_injective n)]
  unfold exitArcs
  omega

lemma sb_carrierT_sub (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) : carrierT n D T ⊆ inner n D := by
  intro w hw
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hw
  rw [sb_mem_inner]
  by_contra hc
  have hw2 : w = outW n D := by unfold outW; omega
  rw [hw2, hout] at hw
  exact Finset.not_nonempty_empty hw.2

lemma sb_sources_carrierT (D : Dag) (T : Finset (Fin n)) :
    (sources n (carrierT n D T)).card = T.card := by
  have himg : sources n (carrierT n D T) = T.image (fun v : Fin n => v.val) := by
    ext w
    simp only [sources, carrierT, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨⟨-, v, hv⟩, hw⟩
      have hs : supp n D w = {⟨w, hw⟩} := supp_input D ⟨w, hw⟩
      rw [hs, Finset.mem_inter, Finset.mem_singleton] at hv
      exact ⟨v, hv.2, by rw [hv.1]⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨by have := v.isLt; omega, v, ?_⟩, v.isLt⟩
      rw [supp_input]; simp [hv]
  rw [himg, Finset.card_image_of_injective _ Fin.val_injective]

lemma carrier_flow_union (h : StrictLive n D) (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) :
    (exitArcs n D (carrierT n D T)).card + (merges n D (carrierT n D T)).card =
      T.card + surplusOn D (carrierT n D T) := by
  rw [← sb_sources_carrierT D T]
  refine carrier_flow h _ (sb_carrierT_sub T hout) (fun j hj hK => ?_)
  obtain ⟨ha, hb, -⟩ := h.1 j hj
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hK ⊢
  obtain ⟨v, hv⟩ := hK.2
  rw [Finset.mem_inter, supp_gate h.1 j hj] at hv
  split_ifs at hv with ht
  · rw [Finset.mem_inter] at hv
    exact Or.inl ⟨by omega, v, Finset.mem_inter.mpr ⟨hv.1.1, hv.2⟩⟩
  · rw [Finset.mem_union] at hv
    rcases hv.1 with h1 | h1
    · exact Or.inl ⟨by omega, v, Finset.mem_inter.mpr ⟨h1, hv.2⟩⟩
    · exact Or.inr ⟨by omega, v, Finset.mem_inter.mpr ⟨h1, hv.2⟩⟩

lemma carrier_flow_diff (h : StrictLive n D) (x y : Fin n) (hxy : x ≠ y)
    (hout : x ∉ supp n D (outW n D)) :
    (exitArcs n D (carrierDiff n D x y)).card + (merges n D (carrierDiff n D x y)).card =
      1 + surplusOn D (carrierDiff n D x y) := by
  have hsub : carrierDiff n D x y ⊆ inner n D := by
    intro w hw
    simp only [carrierDiff, Finset.mem_filter, Finset.mem_range] at hw
    rw [sb_mem_inner]
    by_contra hc
    have hw2 : w = outW n D := by unfold outW; omega
    rw [hw2] at hw
    exact hout hw.2.1
  have hsrc : sources n (carrierDiff n D x y) = {x.val} := by
    ext w
    simp only [sources, carrierDiff, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨-, hx, -⟩, hw⟩
      have hs : supp n D w = {⟨w, hw⟩} := supp_input D ⟨w, hw⟩
      rw [hs, Finset.mem_singleton] at hx
      rw [hx]
    · rintro rfl
      refine ⟨⟨by have := x.isLt; omega, ?_, ?_⟩, x.isLt⟩
      · rw [supp_input]; exact Finset.mem_singleton_self x
      · rw [supp_input, Finset.mem_singleton]; exact fun hc => hxy hc.symm
  have hfl := carrier_flow h _ hsub (fun j hj hK => ?_)
  · rw [hsrc, Finset.card_singleton] at hfl; exact hfl
  · obtain ⟨ha, hb, -⟩ := h.1 j hj
    simp only [carrierDiff, Finset.mem_filter, Finset.mem_range] at hK ⊢
    obtain ⟨-, hx, hy⟩ := hK
    rw [supp_gate h.1 j hj] at hx hy
    split_ifs at hx hy with ht
    · rw [Finset.mem_inter] at hx hy
      by_cases hya : y ∈ supp n D (opA D j)
      · exact Or.inr ⟨by omega, hx.2, fun hc => hy ⟨hya, hc⟩⟩
      · exact Or.inl ⟨by omega, hx.1, hya⟩
    · rw [Finset.mem_union] at hx hy
      rcases hx with h1 | h1
      · exact Or.inl ⟨by omega, h1, fun hc => hy (Or.inl hc)⟩
      · exact Or.inr ⟨by omega, h1, fun hc => hy (Or.inr hc)⟩

lemma mem_units {u : Σ _ : ℕ, ℕ} :
    u ∈ units n D ↔ u.1 ∈ inner n D ∧ u.2 + 1 < fanout D u.1 := by
  rw [units, Finset.mem_sigma, Finset.mem_range]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

lemma sb_card_units_filter (n : ℕ) (D : Dag) (p : ℕ → Prop) [DecidablePred p] :
    ((units n D).filter (fun u => p u.1)).card = surplusOn D ((inner n D).filter p) := by
  have hs : (units n D).filter (fun u => p u.1) =
      ((inner n D).filter p).sigma (fun w => Finset.range (fanout D w - 1)) := by
    ext u; simp only [units, Finset.mem_filter, Finset.mem_sigma]; tauto
  rw [hs, Finset.card_sigma, surplusOn]
  simp

lemma card_unitsPlus (n : ℕ) (D : Dag) : (unitsPlus n D).card = Bplus n D := by
  unfold unitsPlus Bplus
  exact sb_card_units_filter n D (fun w => (supp n D w).Nonempty)

lemma mem_eligSet {v : Fin n} :
    v ∈ eligSet n D ↔ ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := by
  simp only [eligSet, branchW, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨w, ⟨-, h2⟩, hv⟩; exact ⟨w, h2, hv⟩
  · rintro ⟨w, h2, hv⟩
    refine ⟨w, ⟨?_, h2⟩, hv⟩
    by_contra hc
    rw [supp_ge D w (by omega)] at hv
    exact Finset.notMem_empty v hv

lemma mem_ineligSet {v : Fin n} :
    v ∈ ineligSet n D ↔ ∀ w, v ∈ supp n D w → fanout D w ≤ 1 := by
  rw [ineligSet, Finset.mem_sdiff, mem_eligSet]
  constructor
  · rintro ⟨-, h⟩ w hw
    by_contra hc
    exact h ⟨w, by omega, hw⟩
  · intro h
    refine ⟨Finset.mem_univ v, ?_⟩
    rintro ⟨w, hw, hv⟩
    have := h w hv
    omega

lemma sb_singleton_inter_nonempty {v : Fin n} {T : Finset (Fin n)} :
    (({v} : Finset (Fin n)) ∩ T).Nonempty ↔ v ∈ T := by
  constructor
  · rintro ⟨u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.1 ▸ hu.2
  · intro h
    exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self v, h⟩⟩

lemma sb_reserved_inj (b : Fin n → ℕ) (hb : PureBranch n D b) :
    Set.InjOn (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) (eligSet n D : Set (Fin n)) := by
  intro v hv v2 hv2 he
  have hbv : b v = b v2 := congrArg Sigma.fst he
  have h1 := (hb v hv).2
  rw [hbv, (hb v2 hv2).2] at h1
  exact (Finset.singleton_injective h1).symm

lemma reserved_subset (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    reservedUnits n D b ⊆ unitsPlus n D := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨h2, hs⟩ := hb v hv
  have h1 : 1 ≤ fanout D (b v) := by omega
  rw [unitsPlus, Finset.mem_filter, mem_units]
  refine ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS h1), ?_⟩, ?_⟩
  · show 0 + 1 < fanout D (b v)
    omega
  · show (supp n D (b v)).Nonempty
    rw [hs]; exact Finset.singleton_nonempty v

lemma card_reserved (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (reservedUnits n D b).card = (eligSet n D).card :=
  Finset.card_image_of_injOn (sb_reserved_inj b hb)

lemma elig_le_Bplus (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (eligSet n D).card ≤ Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_le_card (reserved_subset hS b hb)

lemma card_residual (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (residualUnits n D b).card + (eligSet n D).card = Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_sdiff_add_card_eq_card (reserved_subset hS b hb)

lemma surplus_carrierT_eq (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (T : Finset (Fin n)) :
    surplusOn D (carrierT n D T) = (T ∩ eligSet n D).card +
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
  have h1 : surplusOn D (carrierT n D T) =
      ((units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
    rw [sb_card_units_filter n D (fun w => (supp n D w ∩ T).Nonempty)]
    symm
    refine Finset.sum_subset (fun w hw => ?_) (fun w hw hnot => ?_)
    · rw [Finset.mem_filter] at hw
      have := sb_mem_inner.mp hw.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hw.2⟩
    · rw [carrierT, Finset.mem_filter] at hw
      have hni : w ∉ inner n D := fun hc => hnot (Finset.mem_filter.mpr ⟨hc, hw.2⟩)
      rw [sb_mem_inner] at hni
      simp [fanout_eq_zero_of_ge hS w (by omega)]
  have h2 : (units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) ∪
        (residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) := by
    ext u
    have hsub := reserved_subset hS b hb
    simp only [residualUnits, unitsPlus, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · intro hu
      by_cases hr : u ∈ reservedUnits n D b
      · exact Or.inl ⟨hr, hu.2⟩
      · exact Or.inr ⟨⟨⟨hu.1, hu.2.mono Finset.inter_subset_left⟩, hr⟩, hu.2⟩
    · rintro (hu | hu)
      · exact ⟨(Finset.mem_filter.mp (hsub hu.1)).1, hu.2⟩
      · exact ⟨hu.1.1.1, hu.2⟩
  have h3 : Disjoint ((reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty))
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)) :=
    Finset.disjoint_filter_filter Finset.disjoint_sdiff
  have h4 : (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (T ∩ eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) := by
    rw [reservedUnits, Finset.filter_image]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hv, hne⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty] at hne
      exact ⟨hne, hv⟩
    · rintro ⟨hT, hv⟩
      refine ⟨hv, ?_⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty]
      exact hT
  rw [h1, h2, Finset.card_union_of_disjoint h3, h4,
    Finset.card_image_of_injOn ((sb_reserved_inj b hb).mono
      (Finset.coe_subset.mpr Finset.inter_subset_right))]

lemma surplus_carrierT_le (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (T : Finset (Fin n)) :
    surplusOn D (carrierT n D T) + (eligSet n D).card ≤
      (T ∩ eligSet n D).card + Bplus n D := by
  have h1 := surplus_carrierT_eq hS b hb T
  have h2 := card_residual hS b hb
  have h3 := Finset.card_filter_le (residualUnits n D b)
    (fun u => (supp n D u.1 ∩ T).Nonempty)
  omega

end SurplusFlow

def liftP {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (σ ⟨w, h⟩).val else w

def relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) : Dag :=
  D.map (fun g => (g.1, liftP σ g.2.1, liftP σ g.2.2))

lemma tr_liftP_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : w < n) :
    liftP σ w = (σ ⟨w, h⟩).val := by
  simp [liftP, h]

lemma tr_liftP_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : n ≤ w) : liftP σ w = w := by
  simp [liftP, Nat.not_lt.mpr h]

lemma tr_liftP_lt_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n ≤ m) (w : ℕ) :
    liftP σ w < m ↔ w < m := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h]
    have := (σ ⟨w, h⟩).isLt
    constructor <;> intro <;> omega
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h)]

lemma liftP_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ⁻¹ (liftP σ w) = w := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h, tr_liftP_lt σ⁻¹ (σ ⟨w, h⟩).isLt]; simp
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h), tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]

lemma tr_liftP_inv' {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ (liftP σ⁻¹ w) = w := by
  simpa using liftP_inv σ⁻¹ w

lemma tr_liftP_inj {n : ℕ} (σ : Equiv.Perm (Fin n)) {a b : ℕ} :
    liftP σ a = liftP σ b ↔ a = b := by
  refine ⟨fun h => ?_, congrArg _⟩
  have := congrArg (liftP σ⁻¹) h
  rwa [liftP_inv, liftP_inv] at this

lemma relabel_length {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) :
    (relabel σ D).length = D.length := by
  simp [relabel]

lemma tr_tag {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    tag (relabel σ D) j = tag D j := by
  rw [tag_eq _ j (by rw [relabel_length]; exact hj), tag_eq D j hj]; simp [relabel]

lemma tr_opA {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opA (relabel σ D) j = liftP σ (opA D j) := by
  rw [opA_eq _ j (by rw [relabel_length]; exact hj), opA_eq D j hj]; simp [relabel]

lemma tr_opB {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opB (relabel σ D) j = liftP σ (opB D j) := by
  rw [opB_eq _ j (by rw [relabel_length]; exact hj), opB_eq D j hj]; simp [relabel]

lemma relabel_strict {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Strict n (relabel σ D) := by
  intro j hj
  rw [relabel_length] at hj
  obtain ⟨ha, hb, hab⟩ := hS j hj
  rw [tr_opA σ D j hj, tr_opB σ D j hj]
  exact ⟨(tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr ha,
    (tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr hb, fun h => hab ((tr_liftP_inj σ).mp h)⟩

lemma relabel_val {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (w : ℕ) :
    val (relabel σ D) x (liftP σ w) = val D (fun i => x (σ i)) w := by
  by_cases hw : w < n + D.length
  · refine (val_unique (relabel_strict σ hS) x
      (fun w' => val D (fun i => x (σ i)) (liftP σ⁻¹ w')) ?_ ?_ (liftP σ w) ?_).trans ?_
    · intro i hi
      show val D (fun i => x (σ i)) (liftP σ⁻¹ i) = x ⟨i, hi⟩
      rw [tr_liftP_lt σ⁻¹ hi, val_input D _ _ (σ⁻¹ ⟨i, hi⟩).isLt]
      simp
    · intro j hj
      rw [relabel_length] at hj
      show val D (fun i => x (σ i)) (liftP σ⁻¹ (n + j)) =
        gop (tag (relabel σ D) j) (val D (fun i => x (σ i)) (liftP σ⁻¹ (opA (relabel σ D) j)))
          (val D (fun i => x (σ i)) (liftP σ⁻¹ (opB (relabel σ D) j)))
      rw [tr_liftP_ge σ⁻¹ (Nat.le_add_right n j), tr_tag σ D j hj, tr_opA σ D j hj,
        tr_opB σ D j hj, liftP_inv, liftP_inv, val_gate hS _ j hj]
    · rw [relabel_length]; exact (tr_liftP_lt_iff σ (Nat.le_add_right _ _) w).mpr hw
    · show val D (fun i => x (σ i)) (liftP σ⁻¹ (liftP σ w)) = _
      rw [liftP_inv]
  · have hw' := Nat.not_lt.mp hw
    rw [tr_liftP_ge σ (le_trans (Nat.le_add_right _ _) hw'),
      val_ge _ _ _ (by rw [relabel_length]; exact hw'), val_ge _ _ _ hw']

lemma relabel_fanout {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (w : ℕ) :
    fanout (relabel σ D) (liftP σ w) = fanout D w := by
  unfold fanout readers
  rw [relabel_length]
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [tr_opA σ D j hj', tr_opB σ D j hj', tr_liftP_inj, tr_liftP_inj]

lemma relabel_live {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hL : Live n D) :
    Live n (relabel σ D) := by
  rcases eq_or_ne D [] with rfl | hne
  · exact hL
  · intro w' hw'
    rw [relabel_length] at hw'
    have hpos := List.length_pos_iff.mpr hne
    rw [← tr_liftP_inv' σ w', relabel_fanout]
    apply hL
    by_cases h : w' < n
    · have := (tr_liftP_lt_iff σ⁻¹ le_rfl w').mpr h
      omega
    · rw [tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]; exact hw'

lemma relabel_strictLive {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (h : StrictLive n D) :
    StrictLive n (relabel σ D) :=
  ⟨relabel_strict σ h.1, relabel_live σ h.2.1, by simpa [relabel] using h.2.2⟩

lemma relabel_out {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (hne : D ≠ [])
    (x : Fin n → Bool) :
    val (relabel σ D) x (outW n (relabel σ D)) = val D (fun i => x (σ i)) (outW n D) := by
  have hpos := List.length_pos_iff.mpr hne
  have e : outW n (relabel σ D) = liftP σ (outW n D) := by
    rw [tr_liftP_ge σ (by unfold outW; omega)]; simp [outW, relabel_length]
  rw [e, relabel_val σ hS]

lemma tr_single_comp {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    (fun i => single v (σ i)) = single (σ⁻¹ v) := by
  funext i
  simp only [single, decide_eq_decide]
  constructor
  · intro h; rw [← h]; simp
  · intro h; rw [h]; simp

lemma relabel_supp {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (w : ℕ) :
    supp n (relabel σ D) (liftP σ w) = (supp n D w).image σ := by
  ext v
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [relabel_val σ hS, tr_single_comp]
  constructor
  · intro h; exact ⟨σ⁻¹ v, h, by simp⟩
  · rintro ⟨a, ha, rfl⟩; simpa using ha

lemma relabel_eligSet {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    eligSet n (relabel σ D) = (eligSet n D).image σ := by
  ext v
  simp only [eligSet, Finset.mem_biUnion, Finset.mem_image, branchW, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨w', ⟨hw', hf⟩, hv⟩
    obtain ⟨w, rfl⟩ : ∃ w, w' = liftP σ w := ⟨liftP σ⁻¹ w', (tr_liftP_inv' σ w').symm⟩
    rw [relabel_supp σ hS, Finset.mem_image] at hv
    obtain ⟨a, ha, rfl⟩ := hv
    rw [relabel_fanout] at hf
    rw [relabel_length, tr_liftP_lt_iff σ (Nat.le_add_right _ _)] at hw'
    exact ⟨a, ⟨w, ⟨hw', hf⟩, ha⟩, rfl⟩
  · rintro ⟨a, ⟨w, ⟨hw, hf⟩, ha⟩, rfl⟩
    refine ⟨liftP σ w, ⟨?_, ?_⟩, ?_⟩
    · rw [relabel_length]; exact (tr_liftP_lt_iff σ (Nat.le_add_right _ _) w).mpr hw
    · rw [relabel_fanout]; exact hf
    · rw [relabel_supp σ hS]; exact Finset.mem_image_of_mem _ ha

lemma relabel_ineligSet {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    ineligSet n (relabel σ D) = (ineligSet n D).image σ := by
  ext v
  simp only [ineligSet, relabel_eligSet σ hS, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · intro h
    exact ⟨σ⁻¹ v, fun hm => h ⟨σ⁻¹ v, hm, by simp⟩, by simp⟩
  · rintro ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact ha (σ.injective hab ▸ hb)

lemma inelig_card_add (n : ℕ) (D : Dag) : (ineligSet n D).card + (eligSet n D).card = n := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (eligSet n D))
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

def sem_Edge {n : ℕ} (G : Fin n → Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, G u v ∧ x u = true ∧ x v = true

def sem_Comp (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) : Prop :=
  ∀ x : Fin n → Bool, val D x (outW n D) = true ↔ sem_Edge G x

def sem_Gr {n : ℕ} (G : Fin n → Fin n → Prop) : Prop :=
  (∀ u v, G u v → G v u) ∧ (∀ u, ¬ G u u) ∧ (∀ v w, v ≠ w → ∃ z, G v z ∧ ¬ G w z) ∧
    (∀ u v, ∃ a, G u a ∧ a ≠ v)

def sem_step (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  b < n + D.length ∧ n ≤ b ∧ (opA D (b - n) = a ∨ opB D (b - n) = a)

def sem_two {n : ℕ} (u z : Fin n) : Fin n → Bool := fun i => decide (i = u) || decide (i = z)

def sem_ins {n : ℕ} (v : Fin n) (x : Fin n → Bool) : Fin n → Bool := fun i => decide (i = v) || x i

def sem_ind {n : ℕ} (A : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ A)

lemma sem_rtg_mono {α : Type} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih (h _ _ hbc)

section SemCore

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma sem_ins_agree (v : Fin n) (x : Fin n → Bool) : ∀ k, k ≠ v → x k = sem_ins v x k := by
  intro k hk; simp [sem_ins, hk]

lemma sem_ins_self (v : Fin n) (x : Fin n → Bool) : sem_ins v x v = true := by simp [sem_ins]

lemma sem_ins_ge (v : Fin n) (x : Fin n → Bool) : ∀ i, x i = true → sem_ins v x i = true := by
  intro i hi; simp [sem_ins, hi]

lemma sem_single_le {x : Fin n → Bool} {u : Fin n} (hu : x u = true) :
    ∀ i, single u i = true → x i = true := by
  intro i hi
  simp only [single, decide_eq_true_eq] at hi
  rw [hi]; exact hu

lemma sem_val_of_supp (hS : Strict n D) {u : Fin n} {w : ℕ} (hu : u ∈ supp n D w)
    {x : Fin n → Bool} (hx : x u = true) : val D x w = true :=
  val_mono hS (single u) x (sem_single_le hx) w (mem_supp.mp hu)

lemma sem_supp_lt {v : Fin n} {w : ℕ} (hv : v ∈ supp n D w) : w < n + D.length := by
  by_contra hc
  rw [supp_ge D w (by omega)] at hv
  exact Finset.notMem_empty v hv

lemma sem_supp_and (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    supp n D (n + j) = supp n D (opA D j) ∩ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

lemma sem_supp_or (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = false) :
    supp n D (n + j) = supp n D (opA D j) ∪ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

lemma sem_supp_and_sub (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true)
    (s : Bool) : supp n D (n + j) ⊆ supp n D (src D (j, s)) := by
  rw [sem_supp_and hS hj ht]
  cases s
  · rw [sb_src_false]; exact Finset.inter_subset_left
  · rw [sb_src_true]; exact Finset.inter_subset_right

lemma sem_src_lt (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) < n + j := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  cases s
  · rw [sb_src_false]; exact ha
  · rw [sb_src_true]; exact hb

lemma sem_src_ne (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) ≠ src D (j, !s) := by
  obtain ⟨-, -, hne⟩ := hS j hj
  cases s
  · simpa [src] using hne
  · simpa [src] using hne.symm

lemma sem_step_src {j : ℕ} (hj : j < D.length) (s : Bool) :
    sem_step n D (src D (j, s)) (n + j) := by
  refine ⟨by omega, by omega, ?_⟩
  rw [Nat.add_sub_cancel_left]
  cases s
  · exact Or.inl (sb_src_false j).symm
  · exact Or.inr (sb_src_true j).symm

lemma sem_step_iff {a b : ℕ} : sem_step n D a b ↔
    ∃ j s, j < D.length ∧ b = n + j ∧ src D (j, s) = a := by
  constructor
  · rintro ⟨h1, h2, h3 | h3⟩
    · exact ⟨b - n, false, by omega, by omega, by rw [sb_src_false]; exact h3⟩
    · exact ⟨b - n, true, by omega, by omega, by rw [sb_src_true]; exact h3⟩
  · rintro ⟨j, s, hj, rfl, rfl⟩
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    cases s
    · exact Or.inl (sb_src_false j).symm
    · exact Or.inr (sb_src_true j).symm

lemma sem_step_lt (hS : Strict n D) {a b : ℕ} (h : sem_step n D a b) : a < b := by
  obtain ⟨h1, h2, h3⟩ := h
  have := hS (b - n) (by omega)
  omega

lemma sem_step_reader {a c : ℕ} (h : sem_step n D a c) : c - n ∈ readers D a := by
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by have := h.1; have := h.2.1; omega, h.2.2⟩

lemma sem_step_fanout {a c : ℕ} (h : sem_step n D a c) : 1 ≤ fanout D a :=
  Finset.card_pos.mpr ⟨_, sem_step_reader h⟩

lemma sem_step_unique {a c c' : ℕ} (h1 : sem_step n D a c) (h2 : sem_step n D a c')
    (hf : fanout D a = 1) : c = c' := by
  have m1 := sem_step_reader h1
  have m2 := sem_step_reader h2
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (show (readers D a).card = 1 from hf)
  rw [hr, Finset.mem_singleton] at m1 m2
  have := h1.2.1
  have := h2.2.1
  omega

lemma sem_changed_path (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (w : ℕ) (hw : val D x w ≠ val D y w) :
    Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b) v.val w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn] at hw
      have hwv : (⟨w, hn⟩ : Fin n) = v := by
        by_contra hc; exact hw (hxy _ hc)
      rw [← hwv]
    · by_cases hlt : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        have hg := hw
        rw [val_gate hS x j hj, val_gate hS y j hj] at hg
        by_cases h1 : val D x (opA D j) = val D y (opA D j)
        · have h2 : val D x (opB D j) ≠ val D y (opB D j) := by
            intro h2; apply hg; rw [h1, h2]
          exact Relation.ReflTransGen.tail (ih _ hb h2)
            ⟨⟨hlt, by omega, Or.inr (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
        · exact Relation.ReflTransGen.tail (ih _ ha h1)
            ⟨⟨hlt, by omega, Or.inl (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
      · exfalso; apply hw; rw [val_ge D x w (by omega), val_ge D y w (by omega)]

def sem_Dom (n : ℕ) (D : Dag) (b v : ℕ) : Prop :=
  b = v ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v (outW n D)

lemma sem_dom_eq (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (b : ℕ) (hdom : sem_Dom n D b v.val)
    (hb : val D x b = val D y b) : val D x (outW n D) = val D y (outW n D) := by
  by_contra hne
  rcases hdom with rfl | hdom
  · rw [val_input D x _ v.isLt, val_input D y _ v.isLt] at hb
    have hxy2 : x = y := by
      funext k
      by_cases hk : k = v
      · rw [hk]; exact hb
      · exact hxy k hk
    exact hne (by rw [hxy2])
  · exact hdom (sem_rtg_mono
      (fun a c h => ⟨h.1, fun hc => h.2 (by rw [hc]; exact hb)⟩)
      (sem_changed_path hS x y v hxy _ hne))

def sem_Chain (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  Relation.ReflTransGen (fun a c => sem_step n D a c ∧ fanout D a = 1) a b

lemma sem_chain_dom (hS : Strict n D) {v b : ℕ} (h : sem_Chain n D v b) :
    sem_Dom n D b v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | @head a c hstep _ ih =>
    by_cases hba : b = a
    · exact Or.inl hba
    · right
      intro hp
      rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c', hs, hrest⟩
      · have h0 := fanout_eq_zero_of_ge hS a (by rw [heq]; unfold outW; omega)
        have h1 := hstep.2
        omega
      · have hcc : c = c' := sem_step_unique hstep.1 hs.1 hstep.2
        subst hcc
        rcases ih with rfl | ih
        · exact hs.2 rfl
        · exact ih hrest

lemma sem_carrier_chain (hS : Strict n D) (v : Fin n) : ∀ w, v ∈ supp n D w →
    (∀ u, u < w → v ∈ supp n D u → fanout D u ≤ 1) → sem_Chain n D v.val w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv hlow
    by_cases hn : w < n
    · have hs : supp n D w = {⟨w, hn⟩} := supp_input D ⟨w, hn⟩
      rw [hs, Finset.mem_singleton] at hv
      rw [hv]; exact Relation.ReflTransGen.refl
    · have hlt := sem_supp_lt hv
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      have key : ∀ s : Bool, v ∈ supp n D (src D (j, s)) → sem_Chain n D v.val (n + j) := by
        intro s hva
        have hstep : sem_step n D (src D (j, s)) (n + j) := sem_step_src hj s
        have hlt' := sem_src_lt hS hj s
        have h1 := sem_step_fanout hstep
        have h2 := hlow _ hlt' hva
        exact Relation.ReflTransGen.tail (ih _ hlt' hva (fun u hu => hlow u (by omega)))
          ⟨hstep, by omega⟩
      rw [supp_gate hS j hj] at hv
      split_ifs at hv with ht
      · exact key false (by rw [sb_src_false]; exact (Finset.mem_inter.mp hv).1)
      · rcases Finset.mem_union.mp hv with h1 | h1
        · exact key false (by rw [sb_src_false]; exact h1)
        · exact key true (by rw [sb_src_true]; exact h1)

lemma sem_single_no_edge (hG : sem_Gr G) (v : Fin n) : ¬ sem_Edge G (single v) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [single, decide_eq_true_eq] at ha hc
  rw [ha, hc] at hac
  exact hG.2.1 _ hac

lemma sem_two_edge {u v : Fin n} (huv : G u v) : sem_Edge G (sem_two u v) :=
  ⟨u, v, huv, by simp [sem_two], by simp [sem_two]⟩

lemma sem_supp_out (hG : sem_Gr G) (hC : sem_Comp n G D) : supp n D (outW n D) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2
    (fun v hv => sem_single_no_edge hG v ((hC _).1 (mem_supp.1 hv)))

lemma sem_dom_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
    (b : ℕ) (hdom : sem_Dom n D b v.val) : supp n D b ⊆ {v} := by
  intro u hu
  rw [Finset.mem_singleton]
  by_contra huv
  obtain ⟨hsym, hirr, hsep, -⟩ := hG
  obtain ⟨z, hvz, huz⟩ := hsep v u (Ne.symm huv)
  have hxb : val D (sem_two u z) b = true := sem_val_of_supp hS hu (by simp [sem_two])
  have hyb : val D (sem_ins v (sem_two u z)) b = true :=
    sem_val_of_supp hS hu (by simp [sem_ins, sem_two])
  have hout := sem_dom_eq hS _ _ v (sem_ins_agree v (sem_two u z)) b hdom (by rw [hxb, hyb])
  have h1 : ¬ sem_Edge G (sem_two u z) := by
    rintro ⟨a, c, hac, ha, hc⟩
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at ha hc
    rcases ha with ha | ha <;> rcases hc with hc | hc <;> rw [ha, hc] at hac
    · exact hirr _ hac
    · exact huz hac
    · exact huz (hsym _ _ hac)
    · exact hirr _ hac
  have h2 : sem_Edge G (sem_ins v (sem_two u z)) :=
    ⟨v, z, hvz, sem_ins_self v _, by simp [sem_ins, sem_two]⟩
  have h3 := (hC _).mpr h2
  rw [← hout] at h3
  exact h1 ((hC _).mp h3)

lemma sem_first_branch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
    (hv : v ∈ eligSet n D) :
    ∃ b, 2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b := by
  classical
  have hex : ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := mem_eligSet.mp hv
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  have hch : sem_Chain n D v.val (Nat.find hex) :=
    sem_carrier_chain hS v _ h2 (fun u hu huv => by
      have := Nat.find_min hex hu
      by_contra hc
      exact this ⟨by omega, huv⟩)
  exact ⟨Nat.find hex, h1, Finset.Subset.antisymm
    (sem_dom_pure hG hS hC v _ (sem_chain_dom hS hch)) (Finset.singleton_subset_iff.mpr h2), hch⟩

def sem_FirstBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v)

lemma sem_exists_firstBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, sem_FirstBranch n D b := by
  classical
  have h : ∀ v : Fin n, ∃ b, v ∈ eligSet n D →
      2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b := by
    intro v
    by_cases hv : v ∈ eligSet n D
    · obtain ⟨b, hb⟩ := sem_first_branch hG hS hC v hv
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose b hb using h
  exact ⟨b, fun v hv => hb v hv⟩

lemma sem_firstBranch_pure {b : Fin n → ℕ} (hb : sem_FirstBranch n D b) : PureBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1⟩

lemma sem_exists_pureBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, PureBranch n D b := by
  obtain ⟨b, hb⟩ := sem_exists_firstBranch hG hS hC
  exact ⟨b, sem_firstBranch_pure hb⟩

lemma sem_mem_inelig {v : Fin n} : v ∈ ineligSet n D ↔ v ∉ eligSet n D := by
  simp [ineligSet]

lemma sem_inelig_chain (hS : Strict n D) {v : Fin n} (hv : v ∈ ineligSet n D) {w : ℕ}
    (hw : v ∈ supp n D w) : sem_Chain n D v.val w :=
  sem_carrier_chain hS v w hw (fun u _ hu => mem_ineligSet.mp hv u hu)

lemma sem_inelig_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {v : Fin n}
    (hv : v ∈ ineligSet n D) {w : ℕ} (hw : v ∈ supp n D w) : supp n D w = {v} :=
  Finset.Subset.antisymm (sem_dom_pure hG hS hC v w (sem_chain_dom hS (sem_inelig_chain hS hv hw)))
    (Finset.singleton_subset_iff.mpr hw)

lemma sem_mem_carrier1 {v : Fin n} {w : ℕ} : w ∈ carrierT n D {v} ↔ v ∈ supp n D w := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.2 ▸ hu.1
  · intro h
    exact ⟨sem_supp_lt h, v, Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self v⟩⟩

lemma sem_mem_exit1 {v : Fin n} {e : ℕ × Bool} : e ∈ exitArcs n D (carrierT n D {v}) ↔
    e.1 < D.length ∧ v ∈ supp n D (src D e) ∧ v ∉ supp n D (n + e.1) := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, sem_mem_carrier1]

lemma sem_inelig_surplus {v : Fin n} (hv : v ∈ ineligSet n D) :
    surplusOn D (carrierT n D {v}) = 0 := by
  unfold surplusOn
  refine Finset.sum_eq_zero (fun w hw => ?_)
  have := mem_ineligSet.mp hv w (sem_mem_carrier1.mp hw)
  omega

lemma sem_joint_meeting (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) :
    ∃ j, j < D.length ∧ tag D j = true ∧ val D (sem_two u v) (n + j) = true ∧
      u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) ∧
      ∃ s : Bool, u ∈ supp n D (src D (j, s)) ∧ v ∉ supp n D (src D (j, s)) ∧
        v ∈ supp n D (src D (j, !s)) ∧ u ∉ supp n D (src D (j, !s)) := by
  classical
  have hex : ∃ w, val D (sem_two u v) w = true ∧ u ∉ supp n D w ∧ v ∉ supp n D w :=
    ⟨outW n D, (hC _).2 (sem_two_edge huv), by rw [sem_supp_out hG hC]; simp,
      by rw [sem_supp_out hG hC]; simp⟩
  obtain ⟨hw1, hw2, hw3⟩ := Nat.find_spec hex
  have hmin : ∀ a, a < Nat.find hex → val D (sem_two u v) a = true →
      u ∈ supp n D a ∨ v ∈ supp n D a := by
    intro a ha hva
    by_contra hc
    rw [not_or] at hc
    exact Nat.find_min hex ha ⟨hva, hc.1, hc.2⟩
  generalize Nat.find hex = w at hw1 hw2 hw3 hmin
  have hlt : w < n + D.length := by
    by_contra hc
    rw [val_ge D _ w (by omega)] at hw1
    exact Bool.false_ne_true hw1
  have hn : n ≤ w := by
    by_contra hc
    have hc' : w < n := by omega
    rw [val_input D _ w hc'] at hw1
    have hs : supp n D w = {⟨w, hc'⟩} := supp_input D ⟨w, hc'⟩
    rw [hs, Finset.mem_singleton] at hw2 hw3
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hw1
    rcases hw1 with h | h
    · exact hw2 h.symm
    · exact hw3 h.symm
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hval := hw1
  rw [val_gate hS _ j hj] at hw1
  rw [supp_gate hS j hj] at hw2 hw3
  cases ht : tag D j
  · exfalso
    rw [ht] at hw1 hw2 hw3
    simp only [gop_false, Bool.or_eq_true] at hw1
    simp only [Bool.false_eq_true, ite_false, Finset.mem_union, not_or] at hw2 hw3
    rcases hw1 with h | h
    · rcases hmin _ ha h with h' | h'
      · exact hw2.1 h'
      · exact hw3.1 h'
    · rcases hmin _ hb h with h' | h'
      · exact hw2.2 h'
      · exact hw3.2 h'
  · rw [ht] at hw1 hw2 hw3
    simp only [gop_true, Bool.and_eq_true] at hw1
    simp only [ite_true, Finset.mem_inter, not_and] at hw2 hw3
    have hsupp : u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) := by
      rw [sem_supp_and hS hj ht]
      simp only [Finset.mem_inter, not_and]
      exact ⟨hw2, hw3⟩
    refine ⟨j, hj, ht, hval, hsupp.1, hsupp.2, ?_⟩
    rcases hmin _ ha hw1.1 with hA | hA
    · have hB : u ∉ supp n D (opB D j) := hw2 hA
      have hBv : v ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_left hB
      exact ⟨false, by simpa [src] using hA, by simpa [src] using fun h => hw3 h hBv,
        by simpa [src] using hBv, by simpa [src] using hB⟩
    · have hB : v ∉ supp n D (opB D j) := hw3 hA
      have hBu : u ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_right hB
      exact ⟨true, by simpa [src] using hBu, by simpa [src] using hB,
        by simpa [src] using hA, by simpa [src] using fun h => hw2 h hBu⟩

lemma sem_inelig_consumer (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {v : Fin n} (hv : v ∈ ineligSet n D) :
    ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧ supp n D (src D e) = {v} ∧
      supp n D (n + e.1) = ∅ ∧ (∀ a, G v a → a ∈ supp n D (src D (e.1, !e.2))) ∧
      exitArcs n D (carrierT n D {v}) = {e} ∧ merges n D (carrierT n D {v}) = ∅ := by
  have hS := h.1
  have hfl := carrier_flow_union h {v} (by rw [sem_supp_out hG hC]; simp)
  rw [sem_inelig_surplus hv, Finset.card_singleton] at hfl
  have hmeet : ∀ a, G v a → ∃ j s, j < D.length ∧ tag D j = true ∧
      (j, s) ∈ exitArcs n D (carrierT n D {v}) ∧ a ∈ supp n D (src D (j, !s)) := by
    intro a hva
    obtain ⟨j, hj, ht, -, hju, -, s, h1, -, h3, -⟩ := sem_joint_meeting hG hS hC hva
    exact ⟨j, s, hj, ht, sem_mem_exit1.mpr ⟨hj, h1, hju⟩, h3⟩
  obtain ⟨a0, ha0, -⟩ := hG.2.2.2 v v
  obtain ⟨j0, s0, hj0, ht0, hm0, -⟩ := hmeet a0 ha0
  have hcard : (exitArcs n D (carrierT n D {v})).card = 1 := by
    have := Finset.card_pos.mpr ⟨_, hm0⟩
    omega
  have hmer : merges n D (carrierT n D {v}) = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
  rw [he, Finset.mem_singleton] at hm0
  subst hm0
  have hsrc : supp n D (src D (j0, s0)) = {v} :=
    sem_inelig_pure hG hS hC hv
      (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.1
  have hnot : v ∉ supp n D (n + j0) :=
    (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.2
  refine ⟨(j0, s0), hj0, ht0, hsrc, ?_, ?_, he, hmer⟩
  · refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
    have hx2 := sem_supp_and_sub hS hj0 ht0 s0 hx
    rw [hsrc, Finset.mem_singleton] at hx2
    exact hnot (hx2 ▸ hx)
  · intro a hva
    obtain ⟨j, s, -, -, hm, ha⟩ := hmeet a hva
    rw [he, Finset.mem_singleton] at hm
    rw [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ha

lemma sem_elig_cover (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) : u ∈ eligSet n D ∨ v ∈ eligSet n D := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨eu, -, -, -, -, hnu, hxu, -⟩ := sem_inelig_consumer hG h hC (sem_mem_inelig.mpr hc.1)
  obtain ⟨ev, -, -, hsv, -, -, hxv, -⟩ := sem_inelig_consumer hG h hC (sem_mem_inelig.mpr hc.2)
  obtain ⟨j, hj, -, -, hju, hjv, s, h1, -, h3, -⟩ := sem_joint_meeting hG h.1 hC huv
  have m1 : (j, s) ∈ exitArcs n D (carrierT n D {u}) := sem_mem_exit1.mpr ⟨hj, h1, hju⟩
  have m2 : (j, !s) ∈ exitArcs n D (carrierT n D {v}) := sem_mem_exit1.mpr ⟨hj, h3, hjv⟩
  rw [hxu, Finset.mem_singleton] at m1
  rw [hxv, Finset.mem_singleton] at m2
  subst m1
  subst m2
  obtain ⟨a, hua, hav⟩ := hG.2.2.2 u v
  have h5 : a ∈ supp n D (src D (j, !s)) := hnu a hua
  rw [hsv, Finset.mem_singleton] at h5
  exact hav h5

lemma sem_ind_no_edge {A : Finset (Fin n)} (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) :
    ¬ sem_Edge G (sem_ind A) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [sem_ind, decide_eq_true_eq] at ha hc
  exact hA a ha c hc hac

lemma sem_exposure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (A : Finset (Fin n)) (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) (x : Fin n)
    (hnb : ∃ a ∈ A, G x a) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ x ∈ supp n D (src D (j, s)) ∧
      x ∉ supp n D (n + j) ∧ Disjoint (supp n D (src D (j, s))) A := by
  by_contra hcon
  have hmask : ∀ j s, j < D.length → tag D j = true → x ∈ supp n D (src D (j, s)) →
      x ∉ supp n D (n + j) → val D (sem_ind A) (src D (j, s)) = true ∧
        val D (sem_ins x (sem_ind A)) (src D (j, s)) = true := by
    intro j s hj ht h1 h2
    have hnd : ¬ Disjoint (supp n D (src D (j, s))) A :=
      fun hd => hcon ⟨j, s, hj, ht, h1, h2, hd⟩
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨a, ha1, ha2⟩ := hnd
    exact ⟨sem_val_of_supp hS ha1 (by simp [sem_ind, ha2]),
      sem_val_of_supp hS ha1 (by simp [sem_ins, sem_ind, ha2])⟩
  have key : ∀ w, x ∉ supp n D w → val D (sem_ind A) w = val D (sem_ins x (sem_ind A)) w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hn : w < n
      · rw [val_input D _ w hn, val_input D _ w hn]
        have hs : supp n D w = {⟨w, hn⟩} := supp_input D ⟨w, hn⟩
        rw [hs, Finset.mem_singleton] at hw
        exact sem_ins_agree x _ _ (fun hc => hw hc.symm)
      · by_cases hlt : w < n + D.length
        · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
          have hj : j < D.length := by omega
          obtain ⟨ha, hb, -⟩ := hS j hj
          rw [val_gate hS _ j hj, val_gate hS _ j hj]
          cases ht : tag D j
          · rw [sem_supp_or hS hj ht, Finset.mem_union, not_or] at hw
            rw [ih _ ha hw.1, ih _ hb hw.2]
          · have hw2 := hw
            rw [sem_supp_and hS hj ht, Finset.mem_inter, not_and] at hw2
            by_cases hxa : x ∈ supp n D (opA D j)
            · have h1 := hmask j false hj ht (by rw [sb_src_false]; exact hxa) hw
              rw [sb_src_false] at h1
              rw [ih _ hb (hw2 hxa), h1.1, h1.2]
            · by_cases hxb : x ∈ supp n D (opB D j)
              · have h1 := hmask j true hj ht (by rw [sb_src_true]; exact hxb) hw
                rw [sb_src_true] at h1
                rw [ih _ ha hxa, h1.1, h1.2]
              · rw [ih _ ha hxa, ih _ hb hxb]
        · rw [val_ge D _ w (by omega), val_ge D _ w (by omega)]
  have hout := key (outW n D) (by rw [sem_supp_out hG hC]; exact Finset.notMem_empty x)
  obtain ⟨a, ha, hxa⟩ := hnb
  have h2 : sem_Edge G (sem_ins x (sem_ind A)) :=
    ⟨x, a, hxa, sem_ins_self x _, by simp [sem_ins, sem_ind, ha]⟩
  have h3 := (hC _).mpr h2
  rw [← hout] at h3
  exact sem_ind_no_edge hA ((hC _).mp h3)

lemma sem_first_mask (hS : Strict n D) (T M : Finset (Fin n)) (hM : 2 ≤ M.card) (w : ℕ)
    (hw : supp n D w ∩ T = M) :
    ∃ j, j < D.length ∧ n + j ≤ w ∧ supp n D (n + j) ∩ T = M ∧
      j ∈ merges n D (carrierT n D T) ∧ (∀ u, u < n + j → supp n D u ∩ T ≠ M) ∧
      ((tag D j = true ∧ M ⊂ supp n D (opA D j) ∩ T ∧ M ⊂ supp n D (opB D j) ∩ T) ∨
        (tag D j = false ∧ supp n D (opA D j) ∩ T ⊂ M ∧ supp n D (opB D j) ∩ T ⊂ M ∧
          (supp n D (opA D j) ∩ T) ∪ (supp n D (opB D j) ∩ T) = M ∧
          (supp n D (opA D j) ∩ T).Nonempty ∧ (supp n D (opB D j) ∩ T).Nonempty)) := by
  classical
  have hex : ∃ u, supp n D u ∩ T = M := ⟨w, hw⟩
  have hle : Nat.find hex ≤ w := Nat.find_min' hex hw
  have hmin : ∀ u, u < Nat.find hex → supp n D u ∩ T ≠ M := fun u hu => Nat.find_min hex hu
  have hspec := Nat.find_spec hex
  generalize Nat.find hex = f at hle hmin hspec
  have hMne : M.Nonempty := Finset.card_pos.mp (by omega)
  have hmem : ∀ {u : ℕ}, (supp n D u ∩ T).Nonempty → u ∈ carrierT n D T := by
    intro u hu
    obtain ⟨v, hv⟩ := hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (sem_supp_lt (Finset.mem_inter.mp hv).1), v, hv⟩
  have hflt : f < n + D.length := by
    obtain ⟨v, hv⟩ := hMne
    rw [← hspec] at hv
    exact sem_supp_lt (Finset.mem_inter.mp hv).1
  have hfn : n ≤ f := by
    by_contra hc
    have hc' : f < n := by omega
    have hs : supp n D f = {⟨f, hc'⟩} := supp_input D ⟨f, hc'⟩
    have h1 : M.card ≤ 1 := by
      rw [← hspec, hs]
      exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
    omega
  obtain ⟨j, rfl⟩ : ∃ j, f = n + j := ⟨f - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hna := hmin _ ha
  have hnb := hmin _ hb
  refine ⟨j, hj, hle, hspec, ?_, hmin, ?_⟩
  · have hAB : (supp n D (opA D j) ∩ T).Nonempty ∧ (supp n D (opB D j) ∩ T).Nonempty := by
      cases ht : tag D j
      · rw [sem_supp_or hS hj ht, Finset.union_inter_distrib_right] at hspec
        constructor
        · rw [Finset.nonempty_iff_ne_empty]
          intro he
          rw [he, Finset.empty_union] at hspec
          exact hnb hspec
        · rw [Finset.nonempty_iff_ne_empty]
          intro he
          rw [he, Finset.union_empty] at hspec
          exact hna hspec
      · rw [sem_supp_and hS hj ht] at hspec
        obtain ⟨v, hv⟩ := hMne
        rw [← hspec] at hv
        simp only [Finset.mem_inter] at hv
        exact ⟨⟨v, Finset.mem_inter.mpr ⟨hv.1.1, hv.2⟩⟩, ⟨v, Finset.mem_inter.mpr ⟨hv.1.2, hv.2⟩⟩⟩
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, hmem (by rw [hspec]; exact hMne), hmem hAB.1, hmem hAB.2⟩
  · cases ht : tag D j
    · right
      rw [sem_supp_or hS hj ht, Finset.union_inter_distrib_right] at hspec
      have hsa : supp n D (opA D j) ∩ T ⊆ M := by rw [← hspec]; exact Finset.subset_union_left
      have hsb : supp n D (opB D j) ∩ T ⊆ M := by rw [← hspec]; exact Finset.subset_union_right
      refine ⟨rfl, Finset.ssubset_iff_subset_ne.mpr ⟨hsa, hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb, hnb⟩, hspec, ?_, ?_⟩
      · rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he, Finset.empty_union] at hspec
        exact hnb hspec
      · rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he, Finset.union_empty] at hspec
        exact hna hspec
    · left
      rw [sem_supp_and hS hj ht] at hspec
      have hsa : M ⊆ supp n D (opA D j) ∩ T := by
        rw [← hspec]
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        exact ⟨hv.1.1, hv.2⟩
      have hsb : M ⊆ supp n D (opB D j) ∩ T := by
        rw [← hspec]
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        exact ⟨hv.1.2, hv.2⟩
      exact ⟨rfl, Finset.ssubset_iff_subset_ne.mpr ⟨hsa, Ne.symm hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb, Ne.symm hnb⟩⟩

end SemCore

def sem_W (n : ℕ) (D : Dag) (x : Fin n) : Finset (ℕ × Bool) := exitArcs n D (carrierT n D {x})

def sem_bar (e : ℕ × Bool) : ℕ × Bool := (e.1, !e.2)

section SemCodes

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

lemma sem_mem_W {x : Fin n} {e : ℕ × Bool} : e ∈ sem_W n D x ↔
    e.1 < D.length ∧ x ∈ supp n D (src D e) ∧ x ∉ supp n D (n + e.1) := sem_mem_exit1

lemma sem_bar_bar (e : ℕ × Bool) : sem_bar (sem_bar e) = e := by simp [sem_bar]

lemma sem_bar_ne (e : ℕ × Bool) : sem_bar e ≠ e := by
  intro h
  have h2 := congrArg Prod.snd h
  simp [sem_bar] at h2

lemma sem_same_gate {e f : ℕ × Bool} (h : e.1 = f.1) : f = e ∨ f = sem_bar e := by
  obtain ⟨j, s⟩ := e
  obtain ⟨k, t⟩ := f
  simp only at h
  subst h
  cases s <;> cases t <;> simp [sem_bar]

lemma sem_W_and (hS : Strict n D) {x : Fin n} {e : ℕ × Bool} (he : e ∈ sem_W n D x) :
    tag D e.1 = true := by
  obtain ⟨hj, h1, h2⟩ := sem_mem_W.mp he
  by_contra ht
  rw [Bool.not_eq_true] at ht
  apply h2
  rw [sem_supp_or hS hj ht, Finset.mem_union]
  obtain ⟨j, s⟩ := e
  cases s
  · left; simpa [src] using h1
  · right; simpa [src] using h1

lemma sem_flow1 (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (x : Fin n) :
    (sem_W n D x).card + (merges n D (carrierT n D {x})).card =
      1 + surplusOn D (carrierT n D {x}) := by
  have h1 := carrier_flow_union h {x} (by rw [sem_supp_out hG hC]; simp)
  rwa [Finset.card_singleton] at h1

lemma sem_edge_slots (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {x y : Fin n}
    (hxy : G x y) : ∃ e, e ∈ sem_W n D x ∧ sem_bar e ∈ sem_W n D y ∧
      y ∉ supp n D (src D e) ∧ x ∉ supp n D (src D (sem_bar e)) ∧
      val D (sem_two x y) (n + e.1) = true := by
  obtain ⟨j, hj, -, hval, hju, hjv, s, h1, h2, h3, h4⟩ := sem_joint_meeting hG hS hC hxy
  exact ⟨(j, s), sem_mem_W.mpr ⟨hj, h1, hju⟩, sem_mem_W.mpr ⟨hj, h3, hjv⟩, h2, h4, hval⟩

lemma sem_cover_free (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x a b y : Fin n} (hab : ¬ G a b) (hxy : G x y) (hya : ¬ G y a) (hyb : ¬ G y b) :
    ∃ e, e ∈ sem_W n D x ∧ a ∉ supp n D (src D e) ∧ b ∉ supp n D (src D e) := by
  have hsym := hG.1
  have hirr := hG.2.1
  have hA : ∀ u ∈ ({a, b, y} : Finset (Fin n)), ∀ v ∈ ({a, b, y} : Finset (Fin n)),
      ¬ G u v := by
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> rw [hu, hv]
    · exact hirr a
    · exact hab
    · exact fun h => hya (hsym _ _ h)
    · exact fun h => hab (hsym _ _ h)
    · exact hirr b
    · exact fun h => hyb (hsym _ _ h)
    · exact hya
    · exact hyb
    · exact hirr y
  obtain ⟨j, s, hj, -, h1, h2, hd⟩ := sem_exposure hG hS hC {a, b, y} hA x ⟨y, by simp, hxy⟩
  exact ⟨(j, s), sem_mem_W.mpr ⟨hj, h1, h2⟩, fun h => Finset.disjoint_left.mp hd h (by simp),
    fun h => Finset.disjoint_left.mp hd h (by simp)⟩

end SemCodes

end DagTools

namespace DagTools

lemma combine_eq_gop (t a b : Bool) : PEqualNP.Outside.L_meta_2590.combine t a b = gop t a b := by
  cases t <;> rfl

lemma causal_incoming_iff_step {n : ℕ} {D : Dag} {u v : ℕ} :
    PEqualNP.Outside.L_meta_2590.incoming n D.length (opA D) (opB D) u v ↔ sem_step n D u v := by
  constructor
  · rintro ⟨k, hk, rfl, rfl | rfl⟩
    · exact sem_step_src hk false
    · exact sem_step_src hk true
  · intro h
    obtain ⟨k, s, hk, rfl, hs⟩ := sem_step_iff.mp h
    refine ⟨k, hk, rfl, ?_⟩
    cases s
    · exact Or.inl hs.symm
    · exact Or.inr hs.symm

lemma causal_mixed_iff {n : ℕ} {D : Dag} {u v : Fin n} {w : ℕ} :
    PEqualNP.Outside.L_meta_2590.mixed (val D (sem_two u v))
      (val D (single u)) (val D (single v)) w ↔
      val D (sem_two u v) w = true ∧ u ∉ supp n D w ∧ v ∉ supp n D w := by
  unfold PEqualNP.Outside.L_meta_2590.mixed
  simp only [mem_supp, Bool.eq_false_iff]

end DagTools
namespace DagTools

lemma sem_slot_source_of_guards {n : ℕ} {D : Dag} {u v : Fin n} {g : ℕ}
    (hsource : ∀ e ∈ sem_W n D u, sem_bar e ∈ sem_W n D v → e.1 = g)
    (k : ℕ) (hk : k < D.length)
    (hu : u ∉ supp n D (n + k)) (hv : v ∉ supp n D (n + k))
    (hcross : (u ∈ supp n D (opA D k) ∧ v ∈ supp n D (opB D k)) ∨
      (v ∈ supp n D (opA D k) ∧ u ∈ supp n D (opB D k))) : k = g := by
  rcases hcross with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · apply hsource (k, false)
    · exact sem_mem_W.mpr ⟨hk, h1, hu⟩
    · exact sem_mem_W.mpr ⟨hk, h2, hv⟩
  · apply hsource (k, true)
    · exact sem_mem_W.mpr ⟨hk, h2, hu⟩
    · exact sem_mem_W.mpr ⟨hk, h1, hv⟩

lemma sem_slot_source_reachable {n : ℕ} {D : Dag} (hS : Strict n D)
    (g : ℕ) (u v : Fin n)
    (hsource : ∀ e ∈ sem_W n D u, sem_bar e ∈ sem_W n D v → e.1 = g)
    (w : ℕ) (hw : w < n + D.length)
    (hp : val D (sem_two u v) w = true) (hu : u ∉ supp n D w) (hv : v ∉ supp n D w) :
    Relation.ReflTransGen
      (fun a b => sem_step n D a b ∧
        (val D (sem_two u v) a = true ∧ u ∉ supp n D a ∧ v ∉ supp n D a) ∧
        (val D (sem_two u v) b = true ∧ u ∉ supp n D b ∧ v ∉ supp n D b))
      (n + g) w := by
  have hval (k : ℕ) (hk : k < D.length) := fun x : Fin n → Bool =>
    (val_gate hS x k hk).trans (combine_eq_gop _ _ _).symm
  have h := PEqualNP.Outside.L_meta_2590.guarded_unique_source_reachable n D.length g
    (opA D) (opB D) (tag D) (val D (sem_two u v)) (val D (single u)) (val D (single v))
    (by intro i hi; rw [val_input D _ i hi, val_input D _ i hi, val_input D _ i hi]; rfl)
    (fun k hk => ⟨(hS k hk).1, (hS k hk).2.1⟩)
    (fun k hk => ⟨hval k hk _, hval k hk _, hval k hk _⟩)
    (by
      intro k hk ht hau hbv hc
      apply sem_slot_source_of_guards hsource k hk
      · simpa only [mem_supp, Bool.eq_false_iff] using hau
      · simpa only [mem_supp, Bool.eq_false_iff] using hbv
      · simpa only [mem_supp] using hc)
    w hw (causal_mixed_iff.mpr ⟨hp, hu, hv⟩)
  exact sem_rtg_mono (fun _ _ h =>
    ⟨causal_incoming_iff_step.mp h.1, causal_mixed_iff.mp h.2.1, causal_mixed_iff.mp h.2.2⟩) h

lemma sem_slot_carrier_obstruction {n : ℕ} {D : Dag} (hS : Strict n D)
    (g cut out : ℕ) (u v c : Fin n)
    (hsource : ∀ e ∈ sem_W n D u, sem_bar e ∈ sem_W n D v → e.1 = g)
    (hchain : sem_Chain n D (n + g) cut) (hcut : c ∈ supp n D cut)
    (hexit : ∀ e ∈ sem_W n D c,
      u ∉ supp n D (src D (sem_bar e)) ∧ v ∉ supp n D (src D (sem_bar e)))
    (hcutout : cut ≤ out) (hout : out < n + D.length)
    (hp : val D (sem_two u v) out = true)
    (hu : u ∉ supp n D out) (hv : v ∉ supp n D out) (hc : c ∉ supp n D out) : False := by
  have hval (k : ℕ) (hk : k < D.length) := fun x : Fin n → Bool =>
    (val_gate hS x k hk).trans (combine_eq_gop _ _ _).symm
  apply PEqualNP.Outside.L_meta_2590.guarded_carrier_obstruction n D.length g cut out
    (opA D) (opB D) (tag D) (val D (sem_two u v)) (val D (single u))
    (val D (single v)) (val D (single c))
    (by intro i hi; rw [val_input D _ i hi, val_input D _ i hi, val_input D _ i hi]; rfl)
    (fun k hk => ⟨(hS k hk).1, (hS k hk).2.1⟩)
    (fun k hk => ⟨hval k hk _, hval k hk _, hval k hk _, hval k hk _⟩)
    (by
      intro k hk ht hau hbv hh
      apply sem_slot_source_of_guards hsource k hk
      · simpa only [mem_supp, Bool.eq_false_iff] using hau
      · simpa only [mem_supp, Bool.eq_false_iff] using hbv
      · simpa only [mem_supp] using hh)
    (sem_rtg_mono (fun a b h =>
      ⟨causal_incoming_iff_step.mpr h.1, fun z hz =>
        (sem_step_unique h.1 (causal_incoming_iff_step.mp hz) h.2).symm⟩) hchain)
    (mem_supp.mp hcut) ?_ hcutout hout (causal_mixed_iff.mpr ⟨hp, hu, hv⟩)
    (Bool.eq_false_iff.mpr fun hc' => hc (mem_supp.mpr hc'))
  intro k hk ht hcf
  have hcnot : c ∉ supp n D (n + k) := by
    intro hc'
    have := mem_supp.mp hc'
    simp [hcf] at this
  constructor
  · intro hleft
    have he : (k, false) ∈ sem_W n D c :=
      sem_mem_W.mpr ⟨hk, by simpa only [sb_src_false] using (mem_supp.mpr hleft), hcnot⟩
    have hh := hexit (k, false) he
    simpa only [sem_bar, Bool.not_false, sb_src_true, mem_supp, Bool.eq_false_iff] using hh
  · intro hright
    have he : (k, true) ∈ sem_W n D c :=
      sem_mem_W.mpr ⟨hk, by simpa only [sb_src_true] using (mem_supp.mpr hright), hcnot⟩
    have hh := hexit (k, true) he
    simpa only [sem_bar, Bool.not_true, sb_src_false, mem_supp, Bool.eq_false_iff] using hh

lemma sem_slot_carrier_graph {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (g cut : ℕ) (u v c : Fin n) (huv : G u v)
    (hsource : ∀ e ∈ sem_W n D u, sem_bar e ∈ sem_W n D v → e.1 = g)
    (hchain : sem_Chain n D (n + g) cut) (hcut : c ∈ supp n D cut)
    (hexit : ∀ e ∈ sem_W n D c,
      u ∉ supp n D (src D (sem_bar e)) ∧ v ∉ supp n D (src D (sem_bar e))) : False := by
  have hcutlt := sem_supp_lt hcut
  have hlen : 0 < D.length := List.length_pos_iff.mpr h.2.2
  have hs := sem_supp_out hG hC
  apply sem_slot_carrier_obstruction h.1 g cut (outW n D) u v c hsource hchain hcut hexit
  · unfold outW; omega
  · unfold outW; omega
  · exact (hC _).mpr (sem_two_edge huv)
  · rw [hs]; exact Finset.notMem_empty _
  · rw [hs]; exact Finset.notMem_empty _
  · rw [hs]; exact Finset.notMem_empty _

end DagTools
namespace DagTools

lemma sem_slot_family_obstruction {ι : Type} (e₀ : ι)
    {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (g : ℕ) (u v : ι → Fin n) (hedge : ∀ e, G (u e) (v e))
    (hsource : ∀ e s, s ∈ sem_W n D (u e) → sem_bar s ∈ sem_W n D (v e) → s.1 = g)
    (hbranch : ∀ w, 2 ≤ fanout D w → ∃ e, u e ∈ supp n D w ∨ v e ∈ supp n D w)
    (hmiss : ∀ k < D.length, k ≠ g → tag D k = true → ∀ s : Bool,
      ∃ e, u e ∉ supp n D (src D (k, s)) ∧ v e ∉ supp n D (src D (k, s)))
    (q : Fin n → Bool) (hq : ¬ sem_Edge G q) (hqg : val D q (n + g) = true) : False := by
  have hval (k : ℕ) (hk : k < D.length) := fun x : Fin n → Bool =>
    (val_gate h.1 x k hk).trans (combine_eq_gop _ _ _).symm
  have hlen : 0 < D.length := List.length_pos_iff.mpr h.2.2
  have hs := sem_supp_out hG hC
  apply PEqualNP.Outside.L_meta_2590.source_obstruction e₀ n D.length g (outW n D)
    (opA D) (opB D) (tag D) (val D q)
    (fun e => val D (sem_two (u e) (v e)))
    (fun e => val D (single (u e))) (fun e => val D (single (v e)))
    (by intro e i hi; rw [val_input D _ i hi, val_input D _ i hi, val_input D _ i hi]; rfl)
    (fun k hk => ⟨(h.1 k hk).1, (h.1 k hk).2.1⟩)
    (fun e k hk => ⟨hval k hk _, hval k hk _, hval k hk _⟩)
    (fun k hk => hval k hk q)
    (by
      intro e k hk ht hau hbv hh
      apply sem_slot_source_of_guards (hsource e) k hk
      · simpa only [mem_supp, Bool.eq_false_iff] using hau
      · simpa only [mem_supp, Bool.eq_false_iff] using hbv
      · simpa only [mem_supp] using hh)
    (by
      intro w w1 w2 h1 h2 hne
      have hs1 := causal_incoming_iff_step.mp h1
      have hs2 := causal_incoming_iff_step.mp h2
      have hfan : 2 ≤ fanout D w := by
        have hpos := sem_step_fanout hs1
        by_contra hn
        have hone : fanout D w = 1 := by omega
        exact hne (sem_step_unique hs1 hs2 hone)
      obtain ⟨e, he⟩ := hbranch w hfan
      exact ⟨e, by simpa only [mem_supp] using he⟩)
    (by
      intro k hk hkg ht
      constructor
      · obtain ⟨e, he⟩ := hmiss k hk hkg ht false
        exact ⟨e, by simpa only [sb_src_false, mem_supp, Bool.eq_false_iff] using he⟩
      · obtain ⟨e, he⟩ := hmiss k hk hkg ht true
        exact ⟨e, by simpa only [sb_src_true, mem_supp, Bool.eq_false_iff] using he⟩)
    (by unfold outW; omega)
    (by
      intro e
      apply causal_mixed_iff.mpr
      refine ⟨(hC _).mpr (sem_two_edge (hedge e)), ?_, ?_⟩
      · rw [hs]; exact Finset.notMem_empty _
      · rw [hs]; exact Finset.notMem_empty _)
    hqg (Bool.eq_false_iff.mpr fun htrue => hq ((hC q).mp htrue))

lemma sem_slot_family_obstruction_cover {ι : Type} (e₀ : ι)
    {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (g : ℕ) (u v : ι → Fin n) (hedge : ∀ e, G (u e) (v e))
    (hcover : ∀ a : Fin n, ∃ e, u e = a ∨ v e = a)
    (hsource : ∀ e s, s ∈ sem_W n D (u e) → sem_bar s ∈ sem_W n D (v e) → s.1 = g)
    (hbranch : ∀ w, 2 ≤ fanout D w → (supp n D w).Nonempty)
    (hmiss : ∀ k < D.length, k ≠ g → tag D k = true → ∀ s : Bool,
      ∃ e, u e ∉ supp n D (src D (k, s)) ∧ v e ∉ supp n D (src D (k, s)))
    (q : Fin n → Bool) (hq : ¬ sem_Edge G q) (hqg : val D q (n + g) = true) : False := by
  apply sem_slot_family_obstruction e₀ hG h hC g u v hedge hsource ?_ hmiss q hq hqg
  intro w hw
  obtain ⟨a, ha⟩ := hbranch w hw
  obtain ⟨e, he | he⟩ := hcover a
  · exact ⟨e, Or.inl (by simpa only [he] using ha)⟩
  · exact ⟨e, Or.inr (by simpa only [he] using ha)⟩

lemma causal_bzero_branch {n : ℕ} {D : Dag} (hS : Strict n D)
    (hB0 : Bzero n D = 0) {w : ℕ} (hf : 2 ≤ fanout D w) :
    (supp n D w).Nonempty := by
  by_contra hne
  have hmem : w ∈ (inner n D).filter (fun z => ¬ (supp n D z).Nonempty) :=
    Finset.mem_filter.mpr ⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (by omega)), hne⟩
  have hle : fanout D w - 1 ≤
      ∑ z ∈ (inner n D).filter (fun z => ¬ (supp n D z).Nonempty), (fanout D z - 1) :=
    Finset.single_le_sum (f := fun z => fanout D z - 1) (fun _ _ => Nat.zero_le _) hmem
  unfold Bzero surplusOn at hB0
  omega

lemma sem_slot_family_obstruction_bzero {ι : Type} (e₀ : ι)
    {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (g : ℕ) (u v : ι → Fin n) (hedge : ∀ e, G (u e) (v e))
    (hcover : ∀ a : Fin n, ∃ e, u e = a ∨ v e = a)
    (hsource : ∀ e s, s ∈ sem_W n D (u e) → sem_bar s ∈ sem_W n D (v e) → s.1 = g)
    (hB0 : Bzero n D = 0)
    (hmiss : ∀ k < D.length, k ≠ g → tag D k = true → ∀ s : Bool,
      ∃ e, u e ∉ supp n D (src D (k, s)) ∧ v e ∉ supp n D (src D (k, s)))
    (q : Fin n → Bool) (hq : ¬ sem_Edge G q) (hqg : val D q (n + g) = true) : False := by
  exact sem_slot_family_obstruction_cover e₀ hG h hC g u v hedge hcover hsource
    (fun _ hw => causal_bzero_branch h.1 hB0 hw) hmiss q hq hqg

end DagTools

namespace DagTools

lemma sem_slot_carrier_obstruction_after {n : ℕ} {D : Dag} (hS : Strict n D)
    (g cut out : ℕ) (u v c : Fin n)
    (hsource : ∀ e ∈ sem_W n D u, sem_bar e ∈ sem_W n D v → e.1 = g)
    (hchain : sem_Chain n D (n + g) cut) (hcut : c ∈ supp n D cut)
    (hexit : ∀ e ∈ sem_W n D c, cut < n + e.1 →
      u ∉ supp n D (src D (sem_bar e)) ∧ v ∉ supp n D (src D (sem_bar e)))
    (hcutout : cut ≤ out) (hout : out < n + D.length)
    (hp : val D (sem_two u v) out = true)
    (hu : u ∉ supp n D out) (hv : v ∉ supp n D out) (hc : c ∉ supp n D out) : False := by
  have hval (k : ℕ) (hk : k < D.length) := fun x : Fin n → Bool =>
    (val_gate hS x k hk).trans (combine_eq_gop _ _ _).symm
  apply PEqualNP.Outside.L_meta_2590.guarded_carrier_obstruction_after n D.length g cut out
    (opA D) (opB D) (tag D) (val D (sem_two u v)) (val D (single u))
    (val D (single v)) (val D (single c))
    (by intro i hi; rw [val_input D _ i hi, val_input D _ i hi, val_input D _ i hi]; rfl)
    (fun k hk => ⟨(hS k hk).1, (hS k hk).2.1⟩)
    (fun k hk => ⟨hval k hk _, hval k hk _, hval k hk _, hval k hk _⟩)
    (by
      intro k hk ht hau hbv hh
      apply sem_slot_source_of_guards hsource k hk
      · simpa only [mem_supp, Bool.eq_false_iff] using hau
      · simpa only [mem_supp, Bool.eq_false_iff] using hbv
      · simpa only [mem_supp] using hh)
    (sem_rtg_mono (fun a b h =>
      ⟨causal_incoming_iff_step.mpr h.1, fun z hz =>
        (sem_step_unique h.1 (causal_incoming_iff_step.mp hz) h.2).symm⟩) hchain)
    (mem_supp.mp hcut) ?_ hcutout hout (causal_mixed_iff.mpr ⟨hp, hu, hv⟩)
    (Bool.eq_false_iff.mpr fun hc' => hc (mem_supp.mpr hc'))
  intro k hk hafter ht hcf
  have hcnot : c ∉ supp n D (n + k) := by
    intro hc'
    have := mem_supp.mp hc'
    simp [hcf] at this
  constructor
  · intro hleft
    have he : (k, false) ∈ sem_W n D c :=
      sem_mem_W.mpr ⟨hk, by simpa only [sb_src_false] using (mem_supp.mpr hleft), hcnot⟩
    have hh := hexit (k, false) he hafter
    simpa only [sem_bar, Bool.not_false, sb_src_true, mem_supp, Bool.eq_false_iff] using hh
  · intro hright
    have he : (k, true) ∈ sem_W n D c :=
      sem_mem_W.mpr ⟨hk, by simpa only [sb_src_true] using (mem_supp.mpr hright), hcnot⟩
    have hh := hexit (k, true) he hafter
    simpa only [sem_bar, Bool.not_true, sb_src_false, mem_supp, Bool.eq_false_iff] using hh

lemma sem_slot_carrier_graph_after {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (g cut : ℕ) (u v c : Fin n) (huv : G u v)
    (hsource : ∀ e ∈ sem_W n D u, sem_bar e ∈ sem_W n D v → e.1 = g)
    (hchain : sem_Chain n D (n + g) cut) (hcut : c ∈ supp n D cut)
    (hexit : ∀ e ∈ sem_W n D c, cut < n + e.1 →
      u ∉ supp n D (src D (sem_bar e)) ∧ v ∉ supp n D (src D (sem_bar e))) : False := by
  have hcutlt := sem_supp_lt hcut
  have hlen : 0 < D.length := List.length_pos_iff.mpr h.2.2
  have hs := sem_supp_out hG hC
  apply sem_slot_carrier_obstruction_after h.1 g cut (outW n D) u v c hsource hchain hcut hexit
  · unfold outW; omega
  · unfold outW; omega
  · exact (hC _).mpr (sem_two_edge huv)
  · rw [hs]; exact Finset.notMem_empty _
  · rw [hs]; exact Finset.notMem_empty _
  · rw [hs]; exact Finset.notMem_empty _


end DagTools

namespace DagTools

lemma sem_step_of_reader {n : ℕ} {D : Dag} {u k : ℕ} (hk : k ∈ readers D u) :
    sem_step n D u (n + k) := by
  obtain ⟨hk, hread⟩ := Finset.mem_filter.mp hk
  have hkl := Finset.mem_range.mp hk
  exact ⟨by omega, by omega, by simpa only [Nat.add_sub_cancel_left] using hread⟩

lemma sem_fanout_one_of_unique_step {n : ℕ} {D : Dag} {u v : ℕ}
    (hstep : sem_step n D u v)
    (hunique : ∀ z, sem_step n D u z → z = v) : fanout D u = 1 := by
  have hle : (readers D u).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro k hk j hj
    have h1 := hunique (n + k) (sem_step_of_reader hk)
    have h2 := hunique (n + j) (sem_step_of_reader hj)
    omega
  have hpos := sem_step_fanout hstep
  change (readers D u).card = 1
  change 1 ≤ (readers D u).card at hpos
  omega

lemma sem_Chain_of_unique_chain {n : ℕ} {D : Dag} {a b : ℕ}
    (hchain : Relation.ReflTransGen
      (fun u v => PEqualNP.Outside.L_meta_2590.incoming n D.length (opA D) (opB D) u v ∧
        ∀ z, PEqualNP.Outside.L_meta_2590.incoming n D.length (opA D) (opB D) u z → z = v) a b) :
    sem_Chain n D a b := by
  apply sem_rtg_mono ?_ hchain
  intro u v h
  have hstep := causal_incoming_iff_step.mp h.1
  exact ⟨hstep, sem_fanout_one_of_unique_step hstep
    (fun z hz => h.2 z (causal_incoming_iff_step.mpr hz))⟩

lemma sem_slot_common_branch {ι : Type} (e₀ : ι)
    {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (g : ℕ) (u v : ι → Fin n) (hedge : ∀ e, G (u e) (v e))
    (hsource : ∀ e s, s ∈ sem_W n D (u e) → sem_bar s ∈ sem_W n D (v e) → s.1 = g)
    (hmiss : ∀ k < D.length, k ≠ g → tag D k = true → ∀ s : Bool,
      ∃ e, u e ∉ supp n D (src D (k, s)) ∧ v e ∉ supp n D (src D (k, s)))
    (q : Fin n → Bool) (hq : ¬ sem_Edge G q) (hqg : val D q (n + g) = true) :
    ∃ cut, sem_Chain n D (n + g) cut ∧ 2 ≤ fanout D cut ∧
      ∀ e, val D (sem_two (u e) (v e)) cut = true ∧
        u e ∉ supp n D cut ∧ v e ∉ supp n D cut := by
  have hval (k : ℕ) (hk : k < D.length) := fun x : Fin n → Bool =>
    (val_gate h.1 x k hk).trans (combine_eq_gop _ _ _).symm
  have hlen : 0 < D.length := List.length_pos_iff.mpr h.2.2
  have hs := sem_supp_out hG hC
  have hbranch := PEqualNP.Outside.L_meta_2590.common_branch_of_separation e₀ n D.length g (outW n D)
    (opA D) (opB D) (tag D) (val D q)
    (fun e => val D (sem_two (u e) (v e)))
    (fun e => val D (single (u e))) (fun e => val D (single (v e)))
    (by intro e i hi; rw [val_input D _ i hi, val_input D _ i hi, val_input D _ i hi]; rfl)
    (fun k hk => ⟨(h.1 k hk).1, (h.1 k hk).2.1⟩)
    (fun e k hk => ⟨hval k hk _, hval k hk _, hval k hk _⟩)
    (fun k hk => hval k hk q)
    (by
      intro e k hk ht hau hbv hh
      apply sem_slot_source_of_guards (hsource e) k hk
      · simpa only [mem_supp, Bool.eq_false_iff] using hau
      · simpa only [mem_supp, Bool.eq_false_iff] using hbv
      · simpa only [mem_supp] using hh)
    (by
      intro k hk hkg ht
      constructor
      · obtain ⟨e, he⟩ := hmiss k hk hkg ht false
        exact ⟨e, by simpa only [sb_src_false, mem_supp, Bool.eq_false_iff] using he⟩
      · obtain ⟨e, he⟩ := hmiss k hk hkg ht true
        exact ⟨e, by simpa only [sb_src_true, mem_supp, Bool.eq_false_iff] using he⟩)
    (by unfold outW; omega)
    (by
      intro e
      apply causal_mixed_iff.mpr
      refine ⟨(hC _).mpr (sem_two_edge (hedge e)), ?_, ?_⟩
      · rw [hs]; exact Finset.notMem_empty _
      · rw [hs]; exact Finset.notMem_empty _)
    hqg (Bool.eq_false_iff.mpr fun htrue => hq ((hC q).mp htrue))
  obtain ⟨cut, w1, w2, hchain, h1, h2, hne, hall⟩ := hbranch
  refine ⟨cut, sem_Chain_of_unique_chain hchain, ?_, fun e => causal_mixed_iff.mp (hall e)⟩
  have hs1 := causal_incoming_iff_step.mp h1
  have hs2 := causal_incoming_iff_step.mp h2
  have hpos := sem_step_fanout hs1
  by_contra hnot
  have hone : fanout D cut = 1 := by omega
  exact hne (sem_step_unique hs1 hs2 hone)

end DagTools

namespace DagTools

lemma h9_branch_nonempty {n : ℕ} {D : Dag}
    (hS : Strict n D) (hB0 : Bzero n D = 0) {w : ℕ} (hf : 2 ≤ fanout D w) :
    (supp n D w).Nonempty := by
  by_contra hne
  have hmem : w ∈ (inner n D).filter (fun v => ¬ (supp n D v).Nonempty) :=
    Finset.mem_filter.mpr ⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (by omega)), hne⟩
  have hsum : fanout D w - 1 ≤ ∑ v ∈ (inner n D).filter (fun v => ¬ (supp n D v).Nonempty),
      (fanout D v - 1) :=
    Finset.single_le_sum (f := fun v => fanout D v - 1) (fun _ _ => Nat.zero_le _) hmem
  unfold Bzero surplusOn at hB0
  omega

lemma h9_all_branch_pure {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (hBp : Bplus n D = (eligSet n D).card) (hB0 : Bzero n D = 0) :
    ∀ w, 2 ≤ fanout D w → ∃ v : Fin n, supp n D w = {v} ∧ fanout D w = 2 := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch hG hS hC
  have hc := card_residual hS b hb
  have hres : residualUnits n D b = ∅ := Finset.card_eq_zero.mp (by omega)
  have hreserved : ∀ u : Σ _ : ℕ, ℕ, u ∈ unitsPlus n D → u ∈ reservedUnits n D b := by
    intro u hu
    by_contra hn
    have hm : u ∈ residualUnits n D b := Finset.mem_sdiff.mpr ⟨hu, hn⟩
    rw [hres] at hm
    exact Finset.notMem_empty _ hm
  intro w hf
  have hne := h9_branch_nonempty hS hB0 hf
  have hin : w ∈ inner n D := sb_mem_inner.mpr (lt_of_fanout_pos hS (by omega))
  have hzero : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus n D := by
    apply Finset.mem_filter.mpr
    exact ⟨mem_units.mpr ⟨hin, by change 0 + 1 < fanout D w; omega⟩, hne⟩
  obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp (hreserved _ hzero)
  have hvw : b v = w := congrArg Sigma.fst hveq
  have hs : supp n D w = {v} := by rw [← hvw]; exact (hb v hv).2
  refine ⟨v, hs, ?_⟩
  by_contra htwo
  have hthree : 3 ≤ fanout D w := by omega
  have hone : (⟨w, 1⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus n D := by
    apply Finset.mem_filter.mpr
    exact ⟨mem_units.mpr ⟨hin, by change 1 + 1 < fanout D w; omega⟩, hne⟩
  obtain ⟨v', hv', hveq'⟩ := Finset.mem_image.mp (hreserved _ hone)
  have hbad : (0 : ℕ) = 1 := congrArg (fun u : Σ _ : ℕ, ℕ => u.2) hveq'
  omega

end DagTools

namespace FourGroupGeometry
abbrev V := Fin 10

def edges : List (Nat × Nat) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
   (5,7),(7,9),(9,6),(6,8),(8,5)]

def adj (u v : V) : Prop := (u.val,v.val) ∈ edges ∨ (v.val,u.val) ∈ edges

def mask (m : Nat) : Finset V := Finset.univ.filter (fun v => m.testBit v.val)

def witnessMasks : List (List Nat) := [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [73, 18, 0, 40, 18, 34, 72, 144, 274, 546], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [5, 42, 5, 40, 0, 40, 65, 193, 261, 516], [5, 146, 5, 73, 144, 0, 65, 144, 260, 517], [261, 18, 260, 42, 18, 34, 0, 146, 260, 516], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def witness (v w : V) : Finset V := mask ((witnessMasks.getD v.val []).getD w.val 0)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1000 in
lemma finite_isolation : ∀ v : V, v ∈ mask 116 → ∀ w : V, w ≠ v →
    (∀ a ∈ witness v w, ∀ b ∈ witness v w, ¬ adj a b) ∧
    w ∈ witness v w ∧
    (∃ u ∈ witness v w, u ∈ mask 116) ∧
    (∃ a ∈ witness v w, adj v a) := by
  unfold adj
  decide +kernel

lemma spare_pure (v : V) (T : Finset V)
    (hv : v ∈ mask 116) (hT : v ∈ T)
    (hfilter : ∀ S : Finset V,
      (∀ a ∈ S, ∀ b ∈ S, ¬ adj a b) →
      (∃ a ∈ S, adj v a) → Disjoint (mask 116) S ∨ Disjoint T S) :
    T = {v} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hT,?_⟩
  intro w hw
  by_contra hne
  obtain ⟨hind,hws,hQ,hnb⟩ := finite_isolation v hv w hne
  obtain h | h := hfilter (witness v w) hind hnb
  · obtain ⟨u,hu,huQ⟩ := hQ
    exact Finset.disjoint_left.mp h huQ hu
  · exact Finset.disjoint_left.mp h hw hws

lemma other_of_card_two {α : Type} [DecidableEq α] {W : Finset α}
    (hc : W.card ≤ 2) {a b : α} (ha : a ∈ W) (hb : b ∈ W) (hab : a ≠ b)
    {c : α} (hcw : c ∈ W) : c = a ∨ c = b := by
  by_contra! hn
  have ht : 2 < W.card := Finset.two_lt_card.mpr
    ⟨a,ha,b,hb,c,hcw,hab,Ne.symm hn.1,Ne.symm hn.2⟩
  omega

lemma isolate_extra_slot {α : Type} [DecidableEq α]
    (W : Finset α) (supp : α → Finset V) (big : α) (v : V)
    (hv : v ∈ mask 116) (hc : W.card ≤ 2) (hbig : big ∈ W)
    (hQ : mask 116 ⊆ supp big) (hmem : ∀ e ∈ W, v ∈ supp e)
    (hexpose : ∀ S : Finset V,
      (∀ a ∈ S, ∀ b ∈ S, ¬ adj a b) →
      (∃ a ∈ S, adj v a) → ∃ e ∈ W, Disjoint (supp e) S) :
    ∃ e ∈ W, e ≠ big ∧ supp e = {v} := by
  have zero_ne : (0 : V) ≠ v := by
    intro h
    subst v
    have hh : (0 : V) ∉ mask 116 := by decide +kernel
    exact hh hv
  have big_hits (w : V) (hne : w ≠ v) : ¬ Disjoint (supp big) (witness v w) := by
    obtain ⟨u,hu,hQ'⟩ := (finite_isolation v hv w hne).2.2.1
    intro hd
    exact Finset.disjoint_left.mp hd (hQ hQ') hu
  obtain ⟨e,he,hdis⟩ := hexpose (witness v 0)
    (finite_isolation v hv 0 zero_ne).1 (finite_isolation v hv 0 zero_ne).2.2.2
  have hne : e ≠ big := by
    intro heq
    subst e
    exact big_hits 0 zero_ne hdis
  refine ⟨e,he,hne,?_⟩
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hmem e he,?_⟩
  intro w hw
  by_contra hnv
  obtain ⟨f,hf,hdf⟩ := hexpose (witness v w)
    (finite_isolation v hv w hnv).1 (finite_isolation v hv w hnv).2.2.2
  have hnf : f ≠ big := by
    intro heq
    subst f
    exact big_hits w hnv hdf
  have hfe : f = e := (other_of_card_two hc hbig he (Ne.symm hne) hf).resolve_left hnf
  subst f
  exact Finset.disjoint_left.mp hdf hw (finite_isolation v hv w hnv).2.1
end FourGroupGeometry

namespace DagTools.FourCase

open PEqualNP.Outside.L_meta_2590.FourGroupGeometry

abbrev V := Fin 10
abbrev Slot := ℕ × Bool
def Q : Finset V := mask 116
def R : Finset V := mask 907

set_option synthInstance.maxSize 5000 in
set_option maxRecDepth 100000 in
lemma graph : sem_Gr adj := by
  unfold sem_Gr adj
  decide +kernel

lemma partition : ∀ v : V, v ∈ Q ∨ v ∈ R := by decide +kernel

lemma disjoint : Disjoint Q R := by decide +kernel

lemma required_cover : ∀ z : V, ∃ u : V, ∃ v : V,
    u ∈ Q ∧ v ∈ R ∧ adj u v ∧ (u = z ∨ v = z) := by
  unfold adj
  decide +kernel

lemma required_avoid : ∀ z : V, ∃ u : V, ∃ v : V,
    u ∈ Q ∧ v ∈ R ∧ adj u v ∧ u ≠ z ∧ v ≠ z := by
  unfold adj
  decide +kernel

lemma code_budget {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hall : eligSet 10 D = Finset.univ) (hB : Bplus 10 D = 10) (v : V) :
    (sem_W 10 D v).card + (merges 10 D (carrierT 10 D {v})).card ≤ 2 := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch graph h.1 hC
  have hs := surplus_carrierT_le h.1 b hb {v}
  simp only [hall, Finset.inter_univ, Finset.card_singleton,
    Finset.card_univ, Fintype.card_fin, hB] at hs
  have hf := sem_flow1 graph h hC v
  omega

lemma pure_extra {D : Dag} (h : Strict 10 D) (hC : sem_Comp 10 adj D)
    (hW : ∀ v : V, (sem_W 10 D v).card ≤ 2) (big : Slot)
    (hQ : ∀ v ∈ Q, big ∈ sem_W 10 D v) :
    ∀ v ∈ Q, ∃ e ∈ sem_W 10 D v, e ≠ big ∧ supp 10 D (src D e) = {v} := by
  intro v hv
  apply isolate_extra_slot (sem_W 10 D v) (fun e => supp 10 D (src D e)) big v
    hv (hW v) (hQ v hv)
  · intro u hu
    exact (sem_mem_W.mp (hQ u hu)).2.1
  · intro e he
    exact (sem_mem_W.mp he).2.1
  · intro S hind hnb
    obtain ⟨j, s, hj, _, hx, hn, hd⟩ := sem_exposure graph h hC S hind v hnb
    exact ⟨(j,s), sem_mem_W.mpr ⟨hj,hx,hn⟩,hd⟩

lemma W_two {D : Dag} (big : Slot) (matchSlot : V → Slot)
    (hbudget : ∀ v : V, (sem_W 10 D v).card +
      (merges 10 D (carrierT 10 D {v})).card ≤ 2)
    (hQ : ∀ v ∈ Q, big ∈ sem_W 10 D v)
    (hextra : ∀ v ∈ Q, ∃ e ∈ sem_W 10 D v,
      e ≠ big ∧ supp 10 D (src D e) = {v})
    (hR : ∀ v ∈ R, sem_bar big ∈ sem_W 10 D v ∧ matchSlot v ∈ sem_W 10 D v)
    (hdiff : ∀ v ∈ R, (matchSlot v).1 ≠ big.1) :
    ∀ v : V, (sem_W 10 D v).card = 2 ∧ merges 10 D (carrierT 10 D {v}) = ∅ := by
  intro v
  have hlo : 2 ≤ (sem_W 10 D v).card := by
    rcases partition v with hv | hv
    · obtain ⟨e, he, hne, _⟩ := hextra v hv
      exact Nat.succ_le_of_lt (Finset.one_lt_card.mpr ⟨big, hQ v hv, e, he, Ne.symm hne⟩)
    · have hne : sem_bar big ≠ matchSlot v := by
        intro he
        exact hdiff v hv (congrArg Prod.fst he).symm
      exact Nat.succ_le_of_lt (Finset.one_lt_card.mpr
        ⟨sem_bar big, (hR v hv).1, matchSlot v, (hR v hv).2, hne⟩)
  have hb := hbudget v
  exact ⟨by omega, Finset.card_eq_zero.mp (by omega)⟩

lemma and_supp_empty {D : Dag} (h : Strict 10 D)
    (hmerge : ∀ v : V, merges 10 D (carrierT 10 D {v}) = ∅)
    (k : ℕ) (hk : k < D.length) (ht : tag D k = true) : supp 10 D (10+k) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  have hab := hv
  rw [sem_supp_and h hk ht, Finset.mem_inter] at hab
  have hm : k ∈ merges 10 D (carrierT 10 D {v}) := by
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hk, sem_mem_carrier1.mpr hv,
      sem_mem_carrier1.mpr hab.1, sem_mem_carrier1.mpr hab.2⟩
  rw [hmerge v] at hm
  exact Finset.notMem_empty _ hm

lemma matching_support {D : Dag} (h : Strict 10 D) (big : Slot) (matchSlot : V → Slot)
    (hW : ∀ v : V, (sem_W 10 D v).card ≤ 2)
    (hQ : ∀ v ∈ Q, big ∈ sem_W 10 D v)
    (hextra : ∀ v ∈ Q, ∃ e ∈ sem_W 10 D v,
      e ≠ big ∧ supp 10 D (src D e) = {v})
    (hR : ∀ v ∈ R, sem_bar big ∈ sem_W 10 D v ∧ matchSlot v ∈ sem_W 10 D v)
    (hdiff : ∀ v ∈ R, (matchSlot v).1 ≠ big.1)
    (hinj : ∀ u ∈ R, ∀ v ∈ R, matchSlot u = matchSlot v → u = v)
    (hempty : ∀ k < D.length, tag D k = true → supp 10 D (10+k) = ∅) :
    ∀ v ∈ R, supp 10 D (src D (matchSlot v)) = {v} := by
  intro v hv
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨(sem_mem_W.mp (hR v hv).2).2.1, ?_⟩
  intro u hu
  have hslot := (hR v hv).2
  have hk := (sem_mem_W.mp hslot).1
  have ht := sem_W_and h hslot
  have huW : matchSlot v ∈ sem_W 10 D u := by
    apply sem_mem_W.mpr
    refine ⟨hk, hu, ?_⟩
    rw [hempty _ hk ht]
    exact Finset.notMem_empty _
  rcases partition u with huQ | huR
  · obtain ⟨e, he, hne, hpure⟩ := hextra u huQ
    have hchoices := other_of_card_two (hW u) (hQ u huQ) he (Ne.symm hne) huW
    rcases hchoices with hb | heq
    · exact False.elim (hdiff v hv (by simpa only [sem_bar] using congrArg Prod.fst hb))
    · have hvsrc := (sem_mem_W.mp (hR v hv).2).2.1
      rw [heq, hpure, Finset.mem_singleton] at hvsrc
      exact hvsrc.symm
  · have hne : sem_bar big ≠ matchSlot u := by
      intro he
      exact hdiff u huR (congrArg Prod.fst he).symm
    rcases other_of_card_two (hW u) (hR u huR).1 (hR u huR).2 hne huW with hb | hm
    · exact False.elim (hdiff v hv (by simpa only [sem_bar] using congrArg Prod.fst hb))
    · exact (hinj v hv u huR hm).symm

lemma nonbig_side_pure {D : Dag} (big : Slot) (matchSlot : V → Slot)
    (hW : ∀ v : V, (sem_W 10 D v).card ≤ 2)
    (hQ : ∀ v ∈ Q, big ∈ sem_W 10 D v)
    (hextra : ∀ v ∈ Q, ∃ e ∈ sem_W 10 D v,
      e ≠ big ∧ supp 10 D (src D e) = {v})
    (hR : ∀ v ∈ R, sem_bar big ∈ sem_W 10 D v ∧ matchSlot v ∈ sem_W 10 D v)
    (hdiff : ∀ v ∈ R, (matchSlot v).1 ≠ big.1)
    (hpure : ∀ v ∈ R, supp 10 D (src D (matchSlot v)) = {v})
    (hempty : ∀ k < D.length, tag D k = true → supp 10 D (10+k) = ∅)
    (k : ℕ) (hk : k < D.length) (hkg : k ≠ big.1) (ht : tag D k = true)
    (s : Bool) : ∃ v : V, supp 10 D (src D (k,s)) ⊆ {v} := by
  by_cases hn : (supp 10 D (src D (k,s))).Nonempty
  · obtain ⟨v,hv⟩ := hn
    have hvW : (k,s) ∈ sem_W 10 D v := sem_mem_W.mpr
      ⟨hk,hv,by rw [hempty k hk ht]; exact Finset.notMem_empty _⟩
    rcases partition v with hvQ | hvR
    · obtain ⟨e,he,hne,hpure⟩ := hextra v hvQ
      rcases other_of_card_two (hW v) (hQ v hvQ) he (Ne.symm hne) hvW with hb | heq
      · exact False.elim (hkg (by simpa only [sem_bar] using congrArg Prod.fst hb))
      · exact ⟨v, by rw [heq,hpure]⟩
    · have hne : sem_bar big ≠ matchSlot v := by
        intro he
        exact hdiff v hvR (congrArg Prod.fst he).symm
      rcases other_of_card_two (hW v) (hR v hvR).1 (hR v hvR).2 hne hvW with hb | heq
      · exact False.elim (hkg (by simpa only [sem_bar] using congrArg Prod.fst hb))
      · exact ⟨v, by rw [heq,hpure v hvR]⟩
  · exact ⟨0, by rw [Finset.not_nonempty_iff_eq_empty.mp hn]; exact Finset.empty_subset _⟩

lemma opposite_source {D : Dag} (big : Slot) (matchSlot : V → Slot)
    (hW : ∀ v : V, (sem_W 10 D v).card ≤ 2)
    (hR : ∀ v ∈ R, sem_bar big ∈ sem_W 10 D v ∧ matchSlot v ∈ sem_W 10 D v)
    (hdiff : ∀ v ∈ R, (matchSlot v).1 ≠ big.1)
    (hopp : ∀ v ∈ R, ∃ w ∈ R, sem_bar (matchSlot v) = matchSlot w)
    (hpure : ∀ v ∈ R, supp 10 D (src D (matchSlot v)) = {v})
    (u v : V) (hu : u ∈ Q) (hv : v ∈ R) (e : Slot)
    (he : e ∈ sem_W 10 D u) (hbe : sem_bar e ∈ sem_W 10 D v) : e.1 = big.1 := by
  have hne : sem_bar big ≠ matchSlot v := by
    intro h
    exact hdiff v hv (congrArg Prod.fst h).symm
  rcases other_of_card_two (hW v) (hR v hv).1 (hR v hv).2 hne hbe with hb | hm
  · simpa only [sem_bar] using congrArg Prod.fst hb
  · have heq : e = sem_bar (matchSlot v) := by
      simpa only [sem_bar_bar] using congrArg sem_bar hm
    obtain ⟨w,hw,hbw⟩ := hopp v hv
    have hu' := (sem_mem_W.mp he).2.1
    rw [heq,hbw,hpure w hw,Finset.mem_singleton] at hu'
    exact False.elim (Finset.disjoint_left.mp disjoint hu (by simpa only [hu'] using hw))

lemma branch_nonempty {D : Dag} (h : Strict 10 D) (hB : Bzero 10 D = 0)
    (w : ℕ) (hw : 2 ≤ fanout D w) : (supp 10 D w).Nonempty := by
  by_contra hn
  have hm : w ∈ (inner 10 D).filter (fun w => ¬ (supp 10 D w).Nonempty) :=
    Finset.mem_filter.mpr ⟨sb_mem_inner.mpr (lt_of_fanout_pos h (by omega)),hn⟩
  have hs := Finset.single_le_sum (f := fun w => fanout D w - 1)
    (fun _ _ => Nat.zero_le _) hm
  unfold Bzero surplusOn at hB
  omega

abbrev E := {p : V × V // p.1 ∈ Q ∧ p.2 ∈ R ∧ adj p.1 p.2}

lemma abstract_four_impossible {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hall : eligSet 10 D = Finset.univ) (hB : Bplus 10 D = 10) (hB0 : Bzero 10 D = 0)
    (big : Slot) (matchSlot : V → Slot)
    (hQ : ∀ v ∈ Q, big ∈ sem_W 10 D v)
    (hR : ∀ v ∈ R, sem_bar big ∈ sem_W 10 D v ∧ matchSlot v ∈ sem_W 10 D v)
    (hdiff : ∀ v ∈ R, (matchSlot v).1 ≠ big.1)
    (hinj : ∀ u ∈ R, ∀ v ∈ R, matchSlot u = matchSlot v → u = v)
    (hopp : ∀ v ∈ R, ∃ w ∈ R, sem_bar (matchSlot v) = matchSlot w) : False := by
  have hb := code_budget h hC hall hB
  have hW (v : V) : (sem_W 10 D v).card ≤ 2 := by have := hb v; omega
  have hextra := pure_extra h.1 hC hW big hQ
  have htwo := W_two big matchSlot hb hQ hextra hR hdiff
  have hempty := and_supp_empty h.1 (fun v => (htwo v).2)
  have hpure := matching_support h.1 big matchSlot hW hQ hextra hR hdiff hinj hempty
  let e₀ : E := ⟨(2,1),by unfold adj; decide +kernel⟩
  have hsource (e : E) (s : Slot) (hs : s ∈ sem_W 10 D e.val.1)
      (hbs : sem_bar s ∈ sem_W 10 D e.val.2) : s.1 = big.1 :=
    opposite_source big matchSlot hW hR hdiff hopp hpure
      e.val.1 e.val.2 e.property.1 e.property.2.1 s hs hbs
  have hcover (v : V) : ∃ e : E, e.val.1 = v ∨ e.val.2 = v := by
    obtain ⟨u,w,hu,hw,he,hv⟩ := required_cover v
    exact ⟨⟨(u,w),hu,hw,he⟩,hv⟩
  have hmiss (k : ℕ) (hk : k < D.length) (hkg : k ≠ big.1) (ht : tag D k = true)
      (s : Bool) : ∃ e : E, e.val.1 ∉ supp 10 D (src D (k,s)) ∧
        e.val.2 ∉ supp 10 D (src D (k,s)) := by
    obtain ⟨z,hz⟩ := nonbig_side_pure big matchSlot hW hQ hextra hR hdiff hpure hempty k hk hkg ht s
    obtain ⟨u,v,hu,hv,he,huz,hvz⟩ := required_avoid z
    exact ⟨⟨(u,v),hu,hv,he⟩,fun h => huz (Finset.mem_singleton.mp (hz h)),
      fun h => hvz (Finset.mem_singleton.mp (hz h))⟩
  have hq : ¬ sem_Edge adj (sem_two (2 : V) 0) := by
    unfold sem_Edge adj
    decide +kernel
  have h2 := hQ (2 : V) (by decide +kernel)
  have h0 := (hR (0 : V) (by decide +kernel)).1
  have hleft : val D (sem_two (2 : V) 0) (src D big) = true :=
    sem_val_of_supp h.1 (sem_mem_W.mp h2).2.1 (by simp [sem_two])
  have hright : val D (sem_two (2 : V) 0) (src D (sem_bar big)) = true :=
    sem_val_of_supp h.1 (sem_mem_W.mp h0).2.1 (by simp [sem_two])
  have hqg : val D (sem_two (2 : V) 0) (10 + big.1) = true := by
    rw [val_gate h.1 _ _ (sem_mem_W.mp h2).1, sem_W_and h.1 h2, gop_true]
    cases hs : big.2
    · simp only [src, sem_bar, hs, Bool.not_false, Bool.false_eq_true, ite_false, ite_true] at hleft hright
      simp [hleft,hright]
    · simp only [src, sem_bar, hs, Bool.not_true, Bool.false_eq_true, ite_false, ite_true] at hleft hright
      simp [hleft,hright]
  exact sem_slot_family_obstruction_cover e₀ graph h hC big.1
    (fun e : E => e.val.1) (fun e : E => e.val.2) (fun e => e.property.2.2)
    hcover hsource (branch_nonempty h.1 hB0) hmiss (sem_two (2 : V) 0) hq hqg

def matching (a b c : Slot) (v : V) : Slot :=
  if v = 0 then a else if v = 1 then sem_bar a else
  if v = 3 then b else if v = 8 then sem_bar b else
  if v = 7 then c else sem_bar c

lemma mem_R : ∀ v : V, v ∈ R ↔
    v = 0 ∨ v = 1 ∨ v = 3 ∨ v = 8 ∨ v = 7 ∨ v = 9 := by decide +kernel

lemma matching_opposite (a b c : Slot) :
    ∀ v ∈ R, ∃ w ∈ R, sem_bar (matching a b c v) = matching a b c w := by
  intro v hv
  rw [mem_R] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1,by decide +kernel,by simp [matching]⟩
  · exact ⟨0,by decide +kernel,by simp [matching,sem_bar_bar]⟩
  · exact ⟨8,by decide +kernel,by simp [matching]⟩
  · exact ⟨3,by decide +kernel,by simp [matching,sem_bar_bar]⟩
  · exact ⟨9,by decide +kernel,by simp [matching]⟩
  · exact ⟨7,by decide +kernel,by simp [matching,sem_bar_bar]⟩

lemma matching_injective (a b c : Slot)
    (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1) (hbc : b.1 ≠ c.1) :
    ∀ u ∈ R, ∀ v ∈ R, matching a b c u = matching a b c v → u = v := by
  intro u hu v hv he
  rw [mem_R] at hu hv
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [matching] at he
  all_goals try rfl
  all_goals try {
    have hf := congrArg Prod.fst he
    try simp only [sem_bar] at hf
    omega }
  all_goals first
    | exact False.elim (sem_bar_ne a he)
    | exact False.elim (sem_bar_ne a he.symm)
    | exact False.elim (sem_bar_ne b he)
    | exact False.elim (sem_bar_ne b he.symm)
    | exact False.elim (sem_bar_ne c he)
    | exact False.elim (sem_bar_ne c he.symm)

lemma canonical_four_impossible {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hall : eligSet 10 D = Finset.univ) (hB : Bplus 10 D = 10) (hB0 : Bzero 10 D = 0)
    (big a b c : Slot)
    (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1) (hbc : b.1 ≠ c.1)
    (hag : a.1 ≠ big.1) (hbg : b.1 ≠ big.1) (hcg : c.1 ≠ big.1)
    (hQ : ∀ v ∈ Q, big ∈ sem_W 10 D v)
    (hR : ∀ v ∈ R, sem_bar big ∈ sem_W 10 D v)
    (ha0 : a ∈ sem_W 10 D (0 : V)) (ha1 : sem_bar a ∈ sem_W 10 D (1 : V))
    (hb3 : b ∈ sem_W 10 D (3 : V)) (hb8 : sem_bar b ∈ sem_W 10 D (8 : V))
    (hc7 : c ∈ sem_W 10 D (7 : V)) (hc9 : sem_bar c ∈ sem_W 10 D (9 : V)) : False := by
  apply abstract_four_impossible h hC hall hB hB0 big (matching a b c) hQ
  · intro v hv
    refine ⟨hR v hv,?_⟩
    rw [mem_R] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [matching]
  · intro v hv
    rw [mem_R] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [matching,sem_bar]
  · exact matching_injective a b c hab hac hbc
  · exact matching_opposite a b c

end DagTools.FourCase

namespace FiveGroupGeometry
abbrev V := Fin 10
abbrev Slot := ℕ × Bool

def mask (m : ℕ) : Finset V := Finset.univ.filter (fun v => m.testBit v.val)
def inner : Finset V := mask 972

def sides (i : Fin 5) (s : Bool) : Finset V :=
  mask (if s then ([50,68,520,384,772] : List ℕ).getD i.val 0
    else ([1,2,16,32,200] : List ℕ).getD i.val 0)

def bar (e : Slot) : Slot := (e.1, !e.2)

def flip (s : Bool) (e : Slot) : Slot := if s then bar e else e

def known (P : Fin 5 → Slot) (v : V) : Finset Slot :=
  ((Finset.univ ×ˢ Finset.univ).filter (fun p : Fin 5 × Bool => v ∈ sides p.1 p.2)).image
    (fun p => flip p.2 (P p.1))

lemma flip_fst (s : Bool) (e : Slot) : (flip s e).1 = e.1 := by cases s <;> rfl

lemma flip_bar (s : Bool) (e : Slot) : bar (flip s e) = flip (!s) e := by
  rcases e with ⟨k,b⟩
  cases s <;> cases b <;> rfl

lemma flip_injective (e : Slot) : Function.Injective (fun s => flip s e) := by
  rcases e with ⟨k,b⟩
  intro s t h
  cases s <;> cases t <;> cases b <;> simp_all [flip,bar]

lemma flip_exists (p e : Slot) (h : p.1 = e.1) : ∃ s, flip s p = e := by
  rcases p with ⟨k,b⟩
  rcases e with ⟨l,c⟩
  dsimp at h
  subst l
  cases b <;> cases c
  · exact ⟨false,rfl⟩
  · exact ⟨true,rfl⟩
  · exact ⟨true,rfl⟩
  · exact ⟨false,rfl⟩

def leafCover (v : V) : Finset V :=
  mask (if v = 1 then 68 else if v = 4 then 520 else if v = 5 then 384 else 0)

lemma member_known {P : Fin 5 → Slot} {v : V} {e : Slot} :
    e ∈ known P v ↔ ∃ i : Fin 5, ∃ s : Bool, v ∈ sides i s ∧ flip s (P i) = e := by
  simp only [known, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
    Finset.mem_univ, true_and, Prod.exists]

set_option maxHeartbeats 0 in
lemma clean_side_size : ∀ i : Fin 5, i ≠ 4 → ∀ s : Bool,
    (sides i s ∩ inner).card ≤ 2 := by decide +kernel

set_option maxHeartbeats 0 in
lemma leaf_cover_geometry : ∀ v : V, (v = 1 ∨ v = 4 ∨ v = 5) →
    (leafCover v).card ≤ 2 ∧ ∀ i : Fin 5, ∀ s : Bool,
      v ∈ sides i s → sides i (!s) ∩ inner ⊆ leafCover v := by decide +kernel

set_option maxHeartbeats 0 in
lemma center_other_empty : sides 0 true ∩ inner = ∅ := by decide +kernel

lemma support_at_slot (P : Fin 5 → Slot) (hP : Function.Injective (fun i => (P i).1))
    (supp : Slot → Finset V) (e : Slot)
    (htype : ∀ v ∈ inner, v ∈ supp e → e ∈ known P v)
    (i : Fin 5) (s : Bool) (hi : flip s (P i) = e) :
    supp e ∩ inner ⊆ sides i s ∩ inner := by
  intro v hv
  obtain ⟨hs, hn⟩ := Finset.mem_inter.mp hv
  obtain ⟨j,t,hj,he⟩ := member_known.mp (htype v hn hs)
  have hf := congrArg Prod.fst (he.trans hi.symm)
  simp only [flip_fst] at hf
  have hji : j = i := hP hf
  subst j
  have hts : t = s := flip_injective (P i) (he.trans hi.symm)
  exact Finset.mem_inter.mpr ⟨hts ▸ hj, hn⟩

lemma support_size (P : Fin 5 → Slot) (hP : Function.Injective (fun i => (P i).1))
    (supp : Slot → Finset V) (e : Slot)
    (htype : ∀ v ∈ inner, v ∈ supp e → e ∈ known P v)
    (hne : e.1 ≠ (P 4).1) : (supp e ∩ inner).card ≤ 2 := by
  classical
  by_cases hi : ∃ i, (P i).1 = e.1
  · obtain ⟨i,hi⟩ := hi
    obtain ⟨s,hs⟩ := flip_exists (P i) e hi
    have hni : i ≠ 4 := by intro h; subst i; exact hne hi.symm
    exact (Finset.card_le_card (support_at_slot P hP supp e htype i s hs)).trans
      (clean_side_size i hni s)
  · have he : supp e ∩ inner = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hs,hn⟩ := Finset.mem_inter.mp hv
      obtain ⟨j,t,_,hj⟩ := member_known.mp (htype v hn hs)
      have hf := congrArg Prod.fst hj
      rw [flip_fst] at hf
      exact hi ⟨j,hf⟩
    simp [he]

lemma leaf_exit_cover (P : Fin 5 → Slot) (hP : Function.Injective (fun i => (P i).1))
    (supp : Slot → Finset V) (v : V) (hv : v = 1 ∨ v = 4 ∨ v = 5)
    (e : Slot) (he : e ∈ known P v)
    (htype : ∀ w ∈ inner, w ∈ supp (bar e) → bar e ∈ known P w) :
    supp (bar e) ∩ inner ⊆ leafCover v := by
  obtain ⟨i,s,hi,hie⟩ := member_known.mp he
  have hbar : flip (!s) (P i) = bar e := by rw [← flip_bar, hie]
  exact (support_at_slot P hP supp (bar e) htype i (!s) hbar).trans
    ((leaf_cover_geometry v hv).2 i s hi)

lemma at_most_two_cover {α : Type} [DecidableEq α] (W : Finset α)
    (a : α) (ha : a ∈ W) (hc : W.card ≤ 2) :
    ∃ b ∈ W, ∀ e ∈ W, e = a ∨ e = b := by
  classical
  by_cases hb : ∃ b ∈ W, b ≠ a
  · obtain ⟨b,hb,hba⟩ := hb
    refine ⟨b,hb,?_⟩
    intro e he
    by_contra! hne
    have ht : 2 < W.card := Finset.two_lt_card.mpr
      ⟨a,ha,b,hb,e,he,Ne.symm hba,Ne.symm hne.1,Ne.symm hne.2⟩
    omega
  · exact ⟨a,ha,fun e he => Or.inl (by by_contra h; exact hb ⟨e,he,h⟩)⟩

lemma center_exit_cover (P : Fin 5 → Slot) (hP : Function.Injective (fun i => (P i).1))
    (supp : Slot → Finset V) (W : Finset Slot) (hW : W.card ≤ 2)
    (hknown : P 0 ∈ W)
    (htype : ∀ e ∈ W, ∀ w ∈ inner, w ∈ supp (bar e) → bar e ∈ known P w)
    (cut : ℕ) (hcut : 10 + (P 4).1 ≤ cut) :
    ∃ T : Finset V, T.card ≤ 2 ∧
      ∀ e ∈ W, cut < 10 + e.1 → supp (bar e) ∩ inner ⊆ T := by
  classical
  have hzero : supp (bar (P 0)) ∩ inner = ∅ := by
    have hh := support_at_slot P hP supp (bar (P 0)) (htype _ hknown) 0 true rfl
    rw [center_other_empty] at hh
    exact Finset.subset_empty.mp hh
  obtain ⟨f,hf,hcover⟩ := at_most_two_cover W (P 0) hknown hW
  by_cases hafter : cut < 10 + f.1
  · refine ⟨supp (bar f) ∩ inner,?_,?_⟩
    · apply support_size P hP supp (bar f) (htype f hf)
      change f.1 ≠ (P 4).1
      omega
    · intro e he hpost
      rcases hcover e he with rfl | rfl
      · rw [hzero]; exact Finset.empty_subset _
      · exact Finset.Subset.refl _
  · refine ⟨∅,by simp,?_⟩
    intro e he hpost
    rcases hcover e he with rfl | rfl
    · rw [hzero]
    · exact (hafter hpost).elim

lemma matching_edge_missed (T : Finset V) (hT : T.card ≤ 2) :
    ((2 : V) ∉ T ∧ (3 : V) ∉ T) ∨
    ((6 : V) ∉ T ∧ (8 : V) ∉ T) ∨
    ((7 : V) ∉ T ∧ (9 : V) ∉ T) := by
  classical
  by_contra! hn
  obtain ⟨h1,h2,h3⟩ := hn
  have h1' : (2 : V) ∈ T ∨ (3 : V) ∈ T := by
    by_cases h : (2 : V) ∈ T
    · exact Or.inl h
    · exact Or.inr (h1 h)
  have h2' : (6 : V) ∈ T ∨ (8 : V) ∈ T := by
    by_cases h : (6 : V) ∈ T
    · exact Or.inl h
    · exact Or.inr (h2 h)
  have h3' : (7 : V) ∈ T ∨ (9 : V) ∈ T := by
    by_cases h : (7 : V) ∈ T
    · exact Or.inl h
    · exact Or.inr (h3 h)
  rcases h1' with h1 | h1 <;> rcases h2' with h2 | h2 <;> rcases h3' with h3 | h3
  all_goals
    have ht : 2 < T.card := Finset.two_lt_card.mpr
      ⟨_,h1,_,h2,_,h3,by decide,by decide,by decide⟩
    omega
end FiveGroupGeometry

namespace DagTools.FiveCase

open PEqualNP.Outside.L_meta_2590.FiveGroupGeometry (sides known flip bar leafCover member_known)

abbrev V := Fin 10
abbrev Slot := ℕ × Bool
abbrev G := PEqualNP.Outside.L_meta_2590.FourGroupGeometry.adj
abbrev I := PEqualNP.Outside.L_meta_2590.FiveGroupGeometry.inner

def U (i : Fin 3) : V := ![2,6,7] i
def Vv (i : Fin 3) : V := ![3,8,9] i

lemma matching_edges : ∀ i : Fin 3, G (U i) (Vv i) := by
  unfold G PEqualNP.Outside.L_meta_2590.FourGroupGeometry.adj
  decide +kernel

lemma matching_inner : ∀ i : Fin 3, U i ∈ I ∧ Vv i ∈ I := by decide +kernel

lemma matching_cover : ∀ v ∈ I, ∃ i : Fin 3, U i = v ∨ Vv i = v := by decide +kernel

lemma inner_nonzero : ∀ v ∈ I, v ≠ (0 : V) := by decide +kernel

lemma outside_inner : ∀ v : V, v ∉ I → v = 0 ∨ v = 1 ∨ v = 4 ∨ v = 5 := by
  decide +kernel

lemma raw_known_card : ∀ v : V, v ≠ 0 →
    (((Finset.univ ×ˢ Finset.univ).filter
      (fun p : Fin 5 × Bool => v ∈ sides p.1 p.2))).card = 2 := by decide +kernel

lemma opposite_inner_only : ∀ u ∈ I, ∀ v ∈ I, ∀ i : Fin 5, ∀ s : Bool,
    u ∈ sides i s → v ∈ sides i (!s) → i = 4 := by decide +kernel

lemma known_card (P : Fin 5 → Slot) (hP : Function.Injective (fun i => (P i).1))
    (v : V) (hv : v ≠ 0) : (known P v).card = 2 := by
  have hinj : Function.Injective (fun p : Fin 5 × Bool => flip p.2 (P p.1)) := by
    rintro ⟨i,s⟩ ⟨j,t⟩ he
    have hf := congrArg Prod.fst he
    simp only [PEqualNP.Outside.L_meta_2590.FiveGroupGeometry.flip_fst] at hf
    have hij := hP hf
    subst j
    have hst : s = t := PEqualNP.Outside.L_meta_2590.FiveGroupGeometry.flip_injective (P i) he
    subst t
    rfl
  rw [known, Finset.card_image_of_injOn (fun _ _ _ _ he => hinj he)]
  exact raw_known_card v hv

lemma known_subset {D : Dag} (P : Fin 5 → Slot)
    (hslots : ∀ i : Fin 5, ∀ s : Bool, ∀ v ∈ sides i s, flip s (P i) ∈ sem_W 10 D v)
    (v : V) : known P v ⊆ sem_W 10 D v := by
  intro e he
  obtain ⟨i,s,hv,rfl⟩ := member_known.mp he
  exact hslots i s v hv

lemma known_eq_W {D : Dag} (P : Fin 5 → Slot)
    (hP : Function.Injective (fun i => (P i).1))
    (hW : ∀ v : V, (sem_W 10 D v).card ≤ 2)
    (hslots : ∀ i : Fin 5, ∀ s : Bool, ∀ v ∈ sides i s, flip s (P i) ∈ sem_W 10 D v)
    (v : V) (hv : v ≠ 0) : sem_W 10 D v = known P v := by
  symm
  apply Finset.eq_of_subset_of_card_le (known_subset P hslots v)
  rw [known_card P hP v hv]
  exact hW v

lemma nonzero_merge_empty {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hall : eligSet 10 D = Finset.univ) (hB : Bplus 10 D = 10)
    (P : Fin 5 → Slot) (hP : Function.Injective (fun i => (P i).1))
    (hslots : ∀ i : Fin 5, ∀ s : Bool, ∀ v ∈ sides i s, flip s (P i) ∈ sem_W 10 D v)
    (v : V) (hv : v ≠ 0) : merges 10 D (carrierT 10 D {v}) = ∅ := by
  have hb := FourCase.code_budget h hC hall hB v
  have hlo : 2 ≤ (sem_W 10 D v).card := by
    rw [← known_card P hP v hv]
    exact Finset.card_le_card (known_subset P hslots v)
  exact Finset.card_eq_zero.mp (by omega)

lemma nonzero_and_absent {D : Dag} (h : Strict 10 D)
    (hM : ∀ v : V, v ≠ 0 → merges 10 D (carrierT 10 D {v}) = ∅)
    (k : ℕ) (hk : k < D.length) (ht : tag D k = true) (v : V) (hv : v ≠ 0) :
    v ∉ supp 10 D (10+k) := by
  intro hm
  have hab := hm
  rw [sem_supp_and h hk ht, Finset.mem_inter] at hab
  have hmer : k ∈ merges 10 D (carrierT 10 D {v}) := by
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hk,sem_mem_carrier1.mpr hm,
      sem_mem_carrier1.mpr hab.1,sem_mem_carrier1.mpr hab.2⟩
  rw [hM v hv] at hmer
  exact Finset.notMem_empty _ hmer

lemma and_input_typed {D : Dag} (h : Strict 10 D) (P : Fin 5 → Slot)
    (hknown : ∀ v : V, v ≠ 0 → sem_W 10 D v = known P v)
    (hM : ∀ v : V, v ≠ 0 → merges 10 D (carrierT 10 D {v}) = ∅)
    (e : Slot) (he : e.1 < D.length) (ht : tag D e.1 = true) :
    ∀ v ∈ I, v ∈ supp 10 D (src D e) → e ∈ known P v := by
  intro v hv hs
  rw [← hknown v (inner_nonzero v hv)]
  exact sem_mem_W.mpr ⟨he,hs,nonzero_and_absent h hM e.1 he ht v (inner_nonzero v hv)⟩

lemma inner_opposite_source {D : Dag} (P : Fin 5 → Slot)
    (hP : Function.Injective (fun i => (P i).1))
    (hknown : ∀ v : V, v ≠ 0 → sem_W 10 D v = known P v)
    (u v : V) (hu : u ∈ I) (hv : v ∈ I) (e : Slot)
    (he : e ∈ sem_W 10 D u) (hbe : sem_bar e ∈ sem_W 10 D v) : e.1 = (P 4).1 := by
  rw [hknown u (inner_nonzero u hu)] at he
  rw [hknown v (inner_nonzero v hv)] at hbe
  obtain ⟨i,s,his,hie⟩ := member_known.mp he
  obtain ⟨j,t,hjt,hje⟩ := member_known.mp hbe
  have hf : (P j).1 = (P i).1 := by
    rw [← PEqualNP.Outside.L_meta_2590.FiveGroupGeometry.flip_fst t, hje]
    change e.1 = (P i).1
    rw [← hie,PEqualNP.Outside.L_meta_2590.FiveGroupGeometry.flip_fst]
  have hji := hP hf
  subst j
  have hts : t = !s := PEqualNP.Outside.L_meta_2590.FiveGroupGeometry.flip_injective (P i) (by
    change flip t (P i) = flip (!s) (P i)
    rw [← PEqualNP.Outside.L_meta_2590.FiveGroupGeometry.flip_bar,hie]
    exact hje)
  have hi : i = 4 := opposite_inner_only u hu v hv i s his (by simpa only [hts] using hjt)
  rw [← hie,PEqualNP.Outside.L_meta_2590.FiveGroupGeometry.flip_fst,hi]

lemma missed_of_small (T : Finset V) (hT : (T ∩ I).card ≤ 2) :
    ∃ i : Fin 3, U i ∉ T ∧ Vv i ∉ T := by
  rcases PEqualNP.Outside.L_meta_2590.FiveGroupGeometry.matching_edge_missed (T ∩ I) hT with h | h | h
  · refine ⟨0,?_,?_⟩
    · intro hm; exact h.1 (Finset.mem_inter.mpr ⟨hm,by decide +kernel⟩)
    · intro hm; exact h.2 (Finset.mem_inter.mpr ⟨hm,by decide +kernel⟩)
  · refine ⟨1,?_,?_⟩
    · intro hm; exact h.1 (Finset.mem_inter.mpr ⟨hm,by decide +kernel⟩)
    · intro hm; exact h.2 (Finset.mem_inter.mpr ⟨hm,by decide +kernel⟩)
  · refine ⟨2,?_,?_⟩
    · intro hm; exact h.1 (Finset.mem_inter.mpr ⟨hm,by decide +kernel⟩)
    · intro hm; exact h.2 (Finset.mem_inter.mpr ⟨hm,by decide +kernel⟩)

lemma exit_cover {D : Dag} (h : Strict 10 D) (P : Fin 5 → Slot)
    (hP : Function.Injective (fun i => (P i).1))
    (hW : ∀ v : V, (sem_W 10 D v).card ≤ 2)
    (hknown : ∀ v : V, v ≠ 0 → sem_W 10 D v = known P v)
    (hM : ∀ v : V, v ≠ 0 → merges 10 D (carrierT 10 D {v}) = ∅)
    (hcenter : P 0 ∈ sem_W 10 D (0 : V))
    (cut : ℕ) (hafter : 10 + (P 4).1 ≤ cut)
    (c : V) (hc : c ∉ I) :
    ∃ T : Finset V, T.card ≤ 2 ∧ ∀ e ∈ sem_W 10 D c,
      cut < 10 + e.1 → supp 10 D (src D (sem_bar e)) ∩ I ⊆ T := by
  have htype (v : V) (e : Slot) (he : e ∈ sem_W 10 D v) :
      ∀ w ∈ I, w ∈ supp 10 D (src D (bar e)) → bar e ∈ known P w := by
    have ht : tag D e.1 = true := sem_W_and h he
    exact and_input_typed h P hknown hM (bar e) (sem_mem_W.mp he).1 ht
  by_cases hc0 : c = 0
  · subst c
    exact PEqualNP.Outside.L_meta_2590.FiveGroupGeometry.center_exit_cover P hP (fun e => supp 10 D (src D e))
      (sem_W 10 D (0 : V)) (hW 0) hcenter (htype 0) cut hafter
  · have hleaf : c = 1 ∨ c = 4 ∨ c = 5 := (outside_inner c hc).resolve_left hc0
    refine ⟨leafCover c,(PEqualNP.Outside.L_meta_2590.FiveGroupGeometry.leaf_cover_geometry c hleaf).1,?_⟩
    intro e he _
    exact PEqualNP.Outside.L_meta_2590.FiveGroupGeometry.leaf_exit_cover P hP (fun e => supp 10 D (src D e)) c hleaf e
      (by rw [← hknown c hc0]; exact he) (htype c e he)

lemma canonical_five_impossible {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hall : eligSet 10 D = Finset.univ) (hB : Bplus 10 D = 10) (hB0 : Bzero 10 D = 0)
    (P : Fin 5 → Slot) (hP : Function.Injective (fun i => (P i).1))
    (hslots : ∀ i : Fin 5, ∀ s : Bool, ∀ v ∈ sides i s, flip s (P i) ∈ sem_W 10 D v) :
    False := by
  have hbudget := FourCase.code_budget h hC hall hB
  have hW (v : V) : (sem_W 10 D v).card ≤ 2 := by have := hbudget v; omega
  have hknown := known_eq_W P hP hW hslots
  have hM := nonzero_merge_empty h hC hall hB P hP hslots
  have htype := and_input_typed h.1 P hknown hM
  have hsource (i : Fin 3) (e : Slot) (he : e ∈ sem_W 10 D (U i))
      (hbe : sem_bar e ∈ sem_W 10 D (Vv i)) : e.1 = (P 4).1 :=
    inner_opposite_source P hP hknown (U i) (Vv i)
      (matching_inner i).1 (matching_inner i).2 e he hbe
  have hmiss (k : ℕ) (hk : k < D.length) (hkg : k ≠ (P 4).1)
      (ht : tag D k = true) (s : Bool) :
      ∃ i : Fin 3, U i ∉ supp 10 D (src D (k,s)) ∧ Vv i ∉ supp 10 D (src D (k,s)) :=
    missed_of_small _ (PEqualNP.Outside.L_meta_2590.FiveGroupGeometry.support_size P hP (fun e => supp 10 D (src D e))
      (k,s) (htype (k,s) hk ht) hkg)
  have h6 : P 4 ∈ sem_W 10 D (6 : V) := hslots 4 false 6 (by decide +kernel)
  have h2 : sem_bar (P 4) ∈ sem_W 10 D (2 : V) := hslots 4 true 2 (by decide +kernel)
  have hq : ¬ sem_Edge G (sem_two (2 : V) 6) := by
    unfold sem_Edge G PEqualNP.Outside.L_meta_2590.FourGroupGeometry.adj
    decide +kernel
  have hleft : val D (sem_two (2 : V) 6) (src D (P 4)) = true :=
    sem_val_of_supp h.1 (sem_mem_W.mp h6).2.1 (by simp [sem_two])
  have hright : val D (sem_two (2 : V) 6) (src D (sem_bar (P 4))) = true :=
    sem_val_of_supp h.1 (sem_mem_W.mp h2).2.1 (by simp [sem_two])
  have hqg : val D (sem_two (2 : V) 6) (10 + (P 4).1) = true := by
    rw [val_gate h.1 _ _ (sem_mem_W.mp h6).1, sem_W_and h.1 h6, gop_true]
    cases hs : (P 4).2
    · simp only [src,sem_bar,hs,Bool.not_false,Bool.false_eq_true,ite_false,ite_true] at hleft hright
      simp [hleft,hright]
    · simp only [src,sem_bar,hs,Bool.not_true,Bool.false_eq_true,ite_false,ite_true] at hleft hright
      simp [hleft,hright]
  obtain ⟨cut,hchain,hfan,hmixed⟩ := sem_slot_common_branch (0 : Fin 3)
    FourCase.graph h hC (P 4).1 U Vv matching_edges hsource hmiss (sem_two (2 : V) 6) hq hqg
  have hB' : Bplus 10 D = (eligSet 10 D).card := by
    rw [hall,Finset.card_univ,Fintype.card_fin,hB]
  obtain ⟨c,hpure,_⟩ := h9_all_branch_pure FourCase.graph h.1 hC hB' hB0 cut hfan
  have hcut : c ∈ supp 10 D cut := by rw [hpure]; exact Finset.mem_singleton_self _
  have hc : c ∉ I := by
    intro hc
    obtain ⟨i,hi | hi⟩ := matching_cover c hc
    · exact (hmixed i).2.1 (by rw [hi]; exact hcut)
    · exact (hmixed i).2.2 (by rw [hi]; exact hcut)
  have hafter : 10 + (P 4).1 ≤ cut :=
    PEqualNP.Outside.L_meta_2590.le_of_increasing_path _ (fun _ _ hh => sem_step_lt h.1 hh.1) hchain
  have hcenter : P 0 ∈ sem_W 10 D (0 : V) := hslots 0 false 0 (by decide +kernel)
  obtain ⟨T,hT,hcover⟩ := exit_cover h.1 P hP hW hknown hM hcenter cut hafter c hc
  obtain ⟨i,hu,hv⟩ := missed_of_small T
    ((Finset.card_le_card Finset.inter_subset_left).trans hT)
  apply sem_slot_carrier_graph_after FourCase.graph h hC (P 4).1 cut (U i) (Vv i) c
    (matching_edges i) (hsource i) hchain hcut
  intro e he heafter
  have hsub := hcover e he heafter
  exact ⟨fun hm => hu (hsub (Finset.mem_inter.mpr ⟨hm,(matching_inner i).1⟩)),
    fun hm => hv (hsub (Finset.mem_inter.mpr ⟨hm,(matching_inner i).2⟩))⟩

end DagTools.FiveCase

namespace SixCase
open PEqualNP.Outside.L_meta_2590.DagTools

abbrev V := Fin 10
abbrev Slot := ℕ × Bool

def leftSide : Fin 6 → Finset V := ![{0}, {0}, {1}, {2}, {6}, {4, 7, 8}]
def rightSide : Fin 6 → Finset V := ![{1}, {4, 5}, {2, 6}, {3, 7}, {8, 9}, {3, 5, 9}]
def side (i : Fin 6) (s : Bool) : Finset V := if s then rightSide i else leftSide i
def edgeU : Fin 6 → V := ![4, 4, 7, 7, 8, 8]
def edgeV : Fin 6 → V := ![3, 9, 5, 9, 3, 5]

lemma side_nonempty : ∀ i s, (side i s).Nonempty := by decide +kernel

lemma two_positions : ∀ v : V, ∃ (i : Fin 6) (s : Bool) (j : Fin 6) (t : Bool),
    i ≠ j ∧ v ∈ side i s ∧ v ∈ side j t := by decide +kernel

lemma cross_unique : ∀ (e i : Fin 6) (s : Bool),
    edgeU e ∈ side i s → edgeV e ∈ side i (!s) → i = 5 := by decide +kernel

lemma side_misses : ∀ i : Fin 6, i ≠ 5 → ∀ s : Bool,
    ∃ e : Fin 6, edgeU e ∉ side i s ∧ edgeV e ∉ side i s := by decide +kernel

lemma outside_misses : ∀ v : V,
    (∀ e : Fin 6, v ≠ edgeU e ∧ v ≠ edgeV e) →
    ∃ e : Fin 6, ∀ (i : Fin 6) (s : Bool), v ∈ side i s →
      edgeU e ∉ side i (!s) ∧ edgeV e ∉ side i (!s) := by decide +kernel

def slotPos (slots : Fin 6 → Slot) (i : Fin 6) (s : Bool) : Slot :=
  if s then sem_bar (slots i) else slots i

lemma slotPos_fst (slots : Fin 6 → Slot) (i : Fin 6) (s : Bool) :
    (slotPos slots i s).1 = (slots i).1 := by cases s <;> rfl

lemma slotPos_bar (slots : Fin 6 → Slot) (i : Fin 6) (s : Bool) :
    sem_bar (slotPos slots i s) = slotPos slots i (!s) := by
  cases s <;> simp [slotPos, sem_bar_bar]

lemma slotPos_injective (slots : Fin 6 → Slot)
    (hinj : Function.Injective (fun i => (slots i).1)) :
    Function.Injective (fun p : Fin 6 × Bool => slotPos slots p.1 p.2) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ he
  have hij : i = j := hinj (by simpa only [slotPos_fst] using congrArg Prod.fst he)
  subst j
  have hst : s = t := by
    cases s <;> cases t
    · rfl
    · exact False.elim (sem_bar_ne (slots i) he.symm)
    · exact False.elim (sem_bar_ne (slots i) he)
    · rfl
  exact Prod.ext rfl hst

lemma code_budget {D : Dag} {G : V → V → Prop}
    (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hBp : Bplus 10 D = (eligSet 10 D).card) (v : V) :
    (sem_W 10 D v).card + (merges 10 D (carrierT 10 D {v})).card ≤ 2 := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch hG h.1 hC
  have hs := surplus_carrierT_le h.1 b hb {v}
  have hcard : (({v} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans_eq (Finset.card_singleton v)
  have hf := sem_flow1 hG h hC v
  omega

lemma slots_exhaust {D : Dag} (slots : Fin 6 → Slot)
    (hinj : Function.Injective (fun i => (slots i).1))
    (hbudget : ∀ v : V, (sem_W 10 D v).card +
      (merges 10 D (carrierT 10 D {v})).card ≤ 2)
    (hslots : ∀ (i : Fin 6) (s : Bool) (v : V), v ∈ side i s →
      slotPos slots i s ∈ sem_W 10 D v) :
    (∀ v : V, (sem_W 10 D v).card = 2 ∧ merges 10 D (carrierT 10 D {v}) = ∅) ∧
    (∀ v e, e ∈ sem_W 10 D v →
      ∃ i s, v ∈ side i s ∧ e = slotPos slots i s) := by
  have hlocal (v : V) :
      (sem_W 10 D v).card = 2 ∧ merges 10 D (carrierT 10 D {v}) = ∅ ∧
      ∀ e ∈ sem_W 10 D v, ∃ i s, v ∈ side i s ∧ e = slotPos slots i s := by
    obtain ⟨i, s, j, t, hij, hi, hj⟩ := two_positions v
    have hp := hslots i s v hi
    have hq := hslots j t v hj
    have hpq : slotPos slots i s ≠ slotPos slots j t := by
      intro he
      exact hij (hinj (by simpa only [slotPos_fst] using congrArg Prod.fst he))
    have hsub : {slotPos slots i s, slotPos slots j t} ⊆ sem_W 10 D v := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl <;> assumption
    have hb := hbudget v
    have heq : {slotPos slots i s, slotPos slots j t} = sem_W 10 D v :=
      Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hpq]; omega)
    have hc : (sem_W 10 D v).card = 2 := by rw [← heq, Finset.card_pair hpq]
    refine ⟨hc, Finset.card_eq_zero.mp (by omega), ?_⟩
    intro e he
    rw [← heq] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact ⟨i, s, hi, rfl⟩
    · exact ⟨j, t, hj, rfl⟩
  exact ⟨fun v => ⟨(hlocal v).1, (hlocal v).2.1⟩, fun v e he => (hlocal v).2.2 e he⟩

lemma and_supp_empty {D : Dag} (h : Strict 10 D)
    (hmerge : ∀ v : V, merges 10 D (carrierT 10 D {v}) = ∅)
    (k : ℕ) (hk : k < D.length) (ht : tag D k = true) : supp 10 D (10 + k) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  have hab := hv
  rw [sem_supp_and h hk ht, Finset.mem_inter] at hab
  have hm : k ∈ merges 10 D (carrierT 10 D {v}) := by
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hk, sem_mem_carrier1.mpr hv,
      sem_mem_carrier1.mpr hab.1, sem_mem_carrier1.mpr hab.2⟩
  rw [hmerge v] at hm
  exact Finset.notMem_empty _ hm

lemma slot_valid {D : Dag} (h : Strict 10 D) (slots : Fin 6 → Slot)
    (hslots : ∀ (i : Fin 6) (s : Bool) (v : V), v ∈ side i s →
      slotPos slots i s ∈ sem_W 10 D v) (i : Fin 6) (s : Bool) :
    (slotPos slots i s).1 < D.length ∧ tag D (slotPos slots i s).1 = true := by
  obtain ⟨v, hv⟩ := side_nonempty i s
  have he := hslots i s v hv
  exact ⟨(sem_mem_W.mp he).1, sem_W_and h he⟩

lemma side_exact {D : Dag} (h : Strict 10 D) (slots : Fin 6 → Slot)
    (hinj : Function.Injective (fun i => (slots i).1))
    (hslots : ∀ (i : Fin 6) (s : Bool) (v : V), v ∈ side i s →
      slotPos slots i s ∈ sem_W 10 D v)
    (hcover : ∀ v e, e ∈ sem_W 10 D v → ∃ i s, v ∈ side i s ∧ e = slotPos slots i s)
    (hempty : ∀ k < D.length, tag D k = true → supp 10 D (10 + k) = ∅) :
    ∀ i s, supp 10 D (src D (slotPos slots i s)) = side i s := by
  intro i s
  ext v
  constructor
  · intro hv
    have hk := slot_valid h slots hslots i s
    have hw : slotPos slots i s ∈ sem_W 10 D v := by
      apply sem_mem_W.mpr
      refine ⟨hk.1, hv, ?_⟩
      rw [hempty _ hk.1 hk.2]
      exact Finset.notMem_empty _
    obtain ⟨j, t, hvt, he⟩ := hcover v _ hw
    have hpair : (i, s) = (j, t) := slotPos_injective slots hinj he
    cases hpair
    exact hvt
  · intro hv
    exact (sem_mem_W.mp (hslots i s v hv)).2.1

lemma pair_source {D : Dag} (slots : Fin 6 → Slot)
    (hcover : ∀ v e, e ∈ sem_W 10 D v → ∃ i s, v ∈ side i s ∧ e = slotPos slots i s)
    (hsides : ∀ i s, supp 10 D (src D (slotPos slots i s)) = side i s) :
    ∀ e : Fin 6, ∀ p ∈ sem_W 10 D (edgeU e),
      sem_bar p ∈ sem_W 10 D (edgeV e) → p.1 = (slots 5).1 := by
  intro e p hp hbar
  obtain ⟨i, s, hu, rfl⟩ := hcover _ _ hp
  have hv := (sem_mem_W.mp hbar).2.1
  rw [slotPos_bar, hsides] at hv
  have hi : i = 5 := cross_unique e i s hu hv
  subst i
  exact slotPos_fst slots 5 s

lemma other_operand_misses {D : Dag} (slots : Fin 6 → Slot)
    (hcover : ∀ v e, e ∈ sem_W 10 D v → ∃ i s, v ∈ side i s ∧ e = slotPos slots i s)
    (hsides : ∀ i s, supp 10 D (src D (slotPos slots i s)) = side i s)
    (hempty : ∀ k < D.length, tag D k = true → supp 10 D (10 + k) = ∅) :
    ∀ k < D.length, k ≠ (slots 5).1 → tag D k = true → ∀ s : Bool,
      ∃ e : Fin 6, edgeU e ∉ supp 10 D (src D (k, s)) ∧
        edgeV e ∉ supp 10 D (src D (k, s)) := by
  intro k hk hkg ht s
  by_cases hne : (supp 10 D (src D (k, s))).Nonempty
  · obtain ⟨v, hv⟩ := hne
    have hw : (k, s) ∈ sem_W 10 D v := by
      apply sem_mem_W.mpr
      refine ⟨hk, hv, ?_⟩
      rw [hempty k hk ht]
      exact Finset.notMem_empty _
    obtain ⟨i, t, _, he⟩ := hcover v _ hw
    have hi : i ≠ 5 := by
      intro hi
      subst i
      exact hkg (by simpa only [slotPos_fst] using congrArg Prod.fst he)
    obtain ⟨e, hu, hv⟩ := side_misses i hi t
    refine ⟨e, ?_, ?_⟩ <;> rw [he, hsides] <;> assumption
  · have he : supp 10 D (src D (k, s)) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    exact ⟨0, by rw [he]; exact Finset.notMem_empty _, by rw [he]; exact Finset.notMem_empty _⟩

lemma bad_pair_at_source {D : Dag} (h : Strict 10 D) (slots : Fin 6 → Slot)
    (hslots : ∀ (i : Fin 6) (s : Bool) (v : V), v ∈ side i s →
      slotPos slots i s ∈ sem_W 10 D v)
    (hsides : ∀ i s, supp 10 D (src D (slotPos slots i s)) = side i s) :
    val D (sem_two (4 : V) 5) (10 + (slots 5).1) = true := by
  have hk := slot_valid h slots hslots 5 false
  change (slots 5).1 < D.length ∧ tag D (slots 5).1 = true at hk
  have h4 : (4 : V) ∈ supp 10 D (src D (slotPos slots 5 false)) := by
    rw [hsides]
    decide
  have h5 : (5 : V) ∈ supp 10 D (src D (slotPos slots 5 true)) := by
    rw [hsides]
    decide
  have hleft := sem_val_of_supp h h4 (show sem_two (4 : V) 5 4 = true by simp [sem_two])
  have hright := sem_val_of_supp h h5 (show sem_two (4 : V) 5 5 = true by simp [sem_two])
  change val D (sem_two (4 : V) 5) (src D (slots 5)) = true at hleft
  change val D (sem_two (4 : V) 5) (src D (sem_bar (slots 5))) = true at hright
  rw [val_gate h _ _ hk.1, hk.2, gop_true]
  cases hs : (slots 5).2
  · have ha : val D (sem_two (4 : V) 5) (opA D (slots 5).1) = true := by
      simpa only [src, hs, Bool.false_eq_true, ite_false] using hleft
    have hb : val D (sem_two (4 : V) 5) (opB D (slots 5).1) = true := by
      simpa only [src, sem_bar, hs, Bool.not_false, ite_true] using hright
    simp only [ha, hb, Bool.and_self]
  · have hb : val D (sem_two (4 : V) 5) (opB D (slots 5).1) = true := by
      simpa only [src, hs, ite_true] using hleft
    have ha : val D (sem_two (4 : V) 5) (opA D (slots 5).1) = true := by
      simpa only [src, sem_bar, hs, Bool.not_true, Bool.false_eq_true, ite_false] using hright
    simp only [ha, hb, Bool.and_self]

lemma bad_pair_at_output {D : Dag} {G : V → V → Prop}
    (hG : sem_Gr G) (hC : sem_Comp 10 G D) (hbad : ¬ G 4 5) :
    val D (sem_two (4 : V) 5) (outW 10 D) = false := by
  have hnon : ¬ sem_Edge G (sem_two (4 : V) 5) := by
    rintro ⟨u, v, huv, hu, hv⟩
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact hG.2.1 _ huv
    · exact hbad huv
    · exact hbad (hG.1 _ _ huv)
    · exact hG.2.1 _ huv
  exact Bool.eq_false_iff.mpr (fun hp => hnon ((hC _).mp hp))

open PEqualNP.Outside.L_meta_2590.DagTools

lemma canonical_six_impossible {D : Dag} {G : V → V → Prop}
    (hG : sem_Gr G) (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hBp : Bplus 10 D = (eligSet 10 D).card) (hB0 : Bzero 10 D = 0)
    (slots : Fin 6 → Slot) (hinj : Function.Injective (fun i => (slots i).1))
    (hslots : ∀ (i : Fin 6) (s : Bool) (v : V), v ∈ side i s →
      slotPos slots i s ∈ sem_W 10 D v)
    (hedge : ∀ e : Fin 6, G (edgeU e) (edgeV e)) (hbad : ¬ G 4 5) : False := by
  have hbudget := code_budget hG h hC hBp
  obtain ⟨hcounts, hcover⟩ := slots_exhaust slots hinj hbudget hslots
  have hempty := and_supp_empty h.1 (fun v => (hcounts v).2)
  have hsides := side_exact h.1 slots hinj hslots hcover hempty
  have hsources := pair_source slots hcover hsides
  have hmiss := other_operand_misses slots hcover hsides hempty
  have hqg := bad_pair_at_source h.1 slots hslots hsides
  have hq : ¬ sem_Edge G (sem_two (4 : V) 5) := by
    intro hx
    have hp := (hC _).mpr hx
    have hf := bad_pair_at_output hG hC hbad
    rw [hf] at hp
    contradiction
  obtain ⟨cut, hchain, hbranch, hall⟩ := sem_slot_common_branch (0 : Fin 6)
    hG h hC (slots 5).1 edgeU edgeV hedge hsources hmiss
    (sem_two (4 : V) 5) hq hqg
  obtain ⟨v, hsupp, _⟩ := h9_all_branch_pure hG h.1 hC hBp hB0 cut hbranch
  have hv : v ∈ supp 10 D cut := by rw [hsupp]; exact Finset.mem_singleton_self v
  have hout : ∀ e : Fin 6, v ≠ edgeU e ∧ v ≠ edgeV e := by
    intro e
    exact ⟨fun he => (hall e).2.1 (he ▸ hv), fun he => (hall e).2.2 (he ▸ hv)⟩
  obtain ⟨e, he⟩ := outside_misses v hout
  apply sem_slot_carrier_graph hG h hC (slots 5).1 cut (edgeU e) (edgeV e) v
    (hedge e) (hsources e) hchain hv
  intro p hp
  obtain ⟨i, s, hvs, rfl⟩ := hcover v p hp
  simpa only [slotPos_bar, hsides] using he i s hvs
end SixCase

namespace DagTools.FiveCase

open PEqualNP.Outside.L_meta_2590.FiveGroupGeometry (sides known flip bar leafCover member_known)

lemma code_budget_tight {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hBp : Bplus 10 D = (eligSet 10 D).card) (v : V) :
    (sem_W 10 D v).card + (merges 10 D (carrierT 10 D {v})).card ≤ 2 := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch FourCase.graph h.1 hC
  have hs := surplus_carrierT_le h.1 b hb {v}
  have hcard : (({v} : Finset V) ∩ eligSet 10 D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans_eq (Finset.card_singleton v)
  have hf := sem_flow1 FourCase.graph h hC v
  omega

lemma nonzero_merge_empty_tight {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hBp : Bplus 10 D = (eligSet 10 D).card)
    (P : Fin 5 → Slot) (hP : Function.Injective (fun i => (P i).1))
    (hslots : ∀ i : Fin 5, ∀ s : Bool, ∀ v ∈ PEqualNP.Outside.L_meta_2590.FiveGroupGeometry.sides i s,
      PEqualNP.Outside.L_meta_2590.FiveGroupGeometry.flip s (P i) ∈ sem_W 10 D v)
    (v : V) (hv : v ≠ 0) : merges 10 D (carrierT 10 D {v}) = ∅ := by
  have hb := code_budget_tight h hC hBp v
  have hlo : 2 ≤ (sem_W 10 D v).card := by
    rw [← known_card P hP v hv]
    exact Finset.card_le_card (known_subset P hslots v)
  exact Finset.card_eq_zero.mp (by omega)

lemma canonical_five_tight_impossible {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 G D)
    (hBp : Bplus 10 D = (eligSet 10 D).card) (hB0 : Bzero 10 D = 0)
    (P : Fin 5 → Slot) (hP : Function.Injective (fun i => (P i).1))
    (hslots : ∀ i : Fin 5, ∀ s : Bool, ∀ v ∈ sides i s, flip s (P i) ∈ sem_W 10 D v) :
    False := by
  have hbudget := code_budget_tight h hC hBp
  have hW (v : V) : (sem_W 10 D v).card ≤ 2 := by have := hbudget v; omega
  have hknown := known_eq_W P hP hW hslots
  have hM := nonzero_merge_empty_tight h hC hBp P hP hslots
  have htype := and_input_typed h.1 P hknown hM
  have hsource (i : Fin 3) (e : Slot) (he : e ∈ sem_W 10 D (U i))
      (hbe : sem_bar e ∈ sem_W 10 D (Vv i)) : e.1 = (P 4).1 :=
    inner_opposite_source P hP hknown (U i) (Vv i)
      (matching_inner i).1 (matching_inner i).2 e he hbe
  have hmiss (k : ℕ) (hk : k < D.length) (hkg : k ≠ (P 4).1)
      (ht : tag D k = true) (s : Bool) :
      ∃ i : Fin 3, U i ∉ supp 10 D (src D (k,s)) ∧ Vv i ∉ supp 10 D (src D (k,s)) :=
    missed_of_small _ (PEqualNP.Outside.L_meta_2590.FiveGroupGeometry.support_size P hP (fun e => supp 10 D (src D e))
      (k,s) (htype (k,s) hk ht) hkg)
  have h6 : P 4 ∈ sem_W 10 D (6 : V) := hslots 4 false 6 (by decide +kernel)
  have h2 : sem_bar (P 4) ∈ sem_W 10 D (2 : V) := hslots 4 true 2 (by decide +kernel)
  have hq : ¬ sem_Edge G (sem_two (2 : V) 6) := by
    unfold sem_Edge G PEqualNP.Outside.L_meta_2590.FourGroupGeometry.adj
    decide +kernel
  have hleft : val D (sem_two (2 : V) 6) (src D (P 4)) = true :=
    sem_val_of_supp h.1 (sem_mem_W.mp h6).2.1 (by simp [sem_two])
  have hright : val D (sem_two (2 : V) 6) (src D (sem_bar (P 4))) = true :=
    sem_val_of_supp h.1 (sem_mem_W.mp h2).2.1 (by simp [sem_two])
  have hqg : val D (sem_two (2 : V) 6) (10 + (P 4).1) = true := by
    rw [val_gate h.1 _ _ (sem_mem_W.mp h6).1, sem_W_and h.1 h6, gop_true]
    cases hs : (P 4).2
    · simp only [src,sem_bar,hs,Bool.not_false,Bool.false_eq_true,ite_false,ite_true] at hleft hright
      simp [hleft,hright]
    · simp only [src,sem_bar,hs,Bool.not_true,Bool.false_eq_true,ite_false,ite_true] at hleft hright
      simp [hleft,hright]
  obtain ⟨cut,hchain,hfan,hmixed⟩ := sem_slot_common_branch (0 : Fin 3)
    FourCase.graph h hC (P 4).1 U Vv matching_edges hsource hmiss (sem_two (2 : V) 6) hq hqg
  obtain ⟨c,hpure,_⟩ := h9_all_branch_pure FourCase.graph h.1 hC hBp hB0 cut hfan
  have hcut : c ∈ supp 10 D cut := by rw [hpure]; exact Finset.mem_singleton_self _
  have hc : c ∉ I := by
    intro hc
    obtain ⟨i,hi | hi⟩ := matching_cover c hc
    · exact (hmixed i).2.1 (by rw [hi]; exact hcut)
    · exact (hmixed i).2.2 (by rw [hi]; exact hcut)
  have hafter : 10 + (P 4).1 ≤ cut :=
    PEqualNP.Outside.L_meta_2590.le_of_increasing_path _ (fun _ _ hh => sem_step_lt h.1 hh.1) hchain
  have hcenter : P 0 ∈ sem_W 10 D (0 : V) := hslots 0 false 0 (by decide +kernel)
  obtain ⟨T,hT,hcover⟩ := exit_cover h.1 P hP hW hknown hM hcenter cut hafter c hc
  obtain ⟨i,hu,hv⟩ := missed_of_small T
    ((Finset.card_le_card Finset.inter_subset_left).trans hT)
  apply sem_slot_carrier_graph_after FourCase.graph h hC (P 4).1 cut (U i) (Vv i) c
    (matching_edges i) (hsource i) hchain hcut
  intro e he heafter
  have hsub := hcover e he heafter
  exact ⟨fun hm => hu (hsub (Finset.mem_inter.mpr ⟨hm,(matching_inner i).1⟩)),
    fun hm => hv (hsub (Finset.mem_inter.mpr ⟨hm,(matching_inner i).2⟩))⟩

end DagTools.FiveCase

namespace DagTools

lemma h9_exit_budget_tight {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hBp : Bplus n D = (eligSet n D).card) (v : Fin n) :
    (sem_W n D v).card + (merges n D (carrierT n D {v})).card ≤ 2 := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch hG h.1 hC
  have hs := surplus_carrierT_le h.1 b hb {v}
  have hcard : (({v} : Finset (Fin n)) ∩ eligSet n D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans_eq (Finset.card_singleton v)
  have hf := sem_flow1 hG h hC v
  omega

lemma h9_eligible_of_two_exits {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hBp : Bplus n D = (eligSet n D).card) (v : Fin n)
    (hW : 2 ≤ (sem_W n D v).card) : v ∈ eligSet n D := by
  by_contra hv
  obtain ⟨b, hb⟩ := sem_exists_pureBranch hG h.1 hC
  have hs := surplus_carrierT_le h.1 b hb {v}
  have he : ({v} : Finset (Fin n)) ∩ eligSet n D = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro u hu
    obtain ⟨huv, hue⟩ := Finset.mem_inter.mp hu
    have huv' : u = v := Finset.mem_singleton.mp huv
    exact hv (huv' ▸ hue)
  have hcard : (({v} : Finset (Fin n)) ∩ eligSet n D).card = 0 := by rw [he]; rfl
  have hf := sem_flow1 hG h hC v
  omega

end DagTools

namespace DagTools.FourCase

open PEqualNP.Outside.L_meta_2590.FourGroupGeometry

lemma abstract_four_forces_all_eligible {D : Dag}
    (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hBp : Bplus 10 D = (eligSet 10 D).card)
    (big : Slot) (matchSlot : V → Slot)
    (hQ : ∀ v ∈ Q, big ∈ sem_W 10 D v)
    (hR : ∀ v ∈ R, sem_bar big ∈ sem_W 10 D v ∧ matchSlot v ∈ sem_W 10 D v)
    (hdiff : ∀ v ∈ R, (matchSlot v).1 ≠ big.1) : eligSet 10 D = Finset.univ := by
  have hbudget := h9_exit_budget_tight graph h hC hBp
  have hW (v : V) : (sem_W 10 D v).card ≤ 2 := by have := hbudget v; omega
  have hextra := pure_extra h.1 hC hW big hQ
  have hcounts := W_two big matchSlot hbudget hQ hextra hR hdiff
  ext v
  constructor
  · intro _
    exact Finset.mem_univ v
  · intro _
    apply h9_eligible_of_two_exits graph h hC hBp v
    rw [(hcounts v).1]

lemma canonical_four_tight_impossible {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 adj D)
    (hBp : Bplus 10 D = (eligSet 10 D).card) (hB0 : Bzero 10 D = 0)
    (big a b c : Slot)
    (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1) (hbc : b.1 ≠ c.1)
    (hag : a.1 ≠ big.1) (hbg : b.1 ≠ big.1) (hcg : c.1 ≠ big.1)
    (hQ : ∀ v ∈ Q, big ∈ sem_W 10 D v)
    (hR : ∀ v ∈ R, sem_bar big ∈ sem_W 10 D v)
    (ha0 : a ∈ sem_W 10 D (0 : V)) (ha1 : sem_bar a ∈ sem_W 10 D (1 : V))
    (hb3 : b ∈ sem_W 10 D (3 : V)) (hb8 : sem_bar b ∈ sem_W 10 D (8 : V))
    (hc7 : c ∈ sem_W 10 D (7 : V)) (hc9 : sem_bar c ∈ sem_W 10 D (9 : V)) : False := by
  have hRR : ∀ v ∈ R, sem_bar big ∈ sem_W 10 D v ∧ matching a b c v ∈ sem_W 10 D v := by
    intro v hv
    refine ⟨hR v hv, ?_⟩
    rw [mem_R] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [matching]
  have hdiff : ∀ v ∈ R, (matching a b c v).1 ≠ big.1 := by
    intro v hv
    rw [mem_R] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [matching, sem_bar]
  have hall := abstract_four_forces_all_eligible h hC hBp big (matching a b c) hQ hRR hdiff
  have hB : Bplus 10 D = 10 := by
    rw [hBp, hall, Finset.card_univ, Fintype.card_fin]
  exact canonical_four_impossible h hC hall hB hB0 big a b c hab hac hbc hag hbg hcg
    hQ hR ha0 ha1 hb3 hb8 hc7 hc9

end DagTools.FourCase

namespace DagTools

lemma h9_two_exits_implies_eligible {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (v : Fin n) (hW : 2 ≤ (sem_W n D v).card) : v ∈ eligSet n D := by
  by_contra hv
  have hs := sem_inelig_surplus (sem_mem_inelig.mpr hv)
  have hf := sem_flow1 hG h hC v
  omega

end DagTools

namespace DagTools

lemma relabel_mem_image {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (v : Fin n) :
    σ v ∈ S.image σ ↔ v ∈ S := by
  constructor
  · intro hv
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hv
    exact σ.injective huv ▸ hu
  · intro hv
    exact Finset.mem_image_of_mem σ hv

lemma relabel_src {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (e : ℕ × Bool)
    (he : e.1 < D.length) : src (relabel σ D) e = liftP σ (src D e) := by
  rcases e with ⟨k,s⟩
  cases s
  · exact tr_opA σ D k he
  · exact tr_opB σ D k he

lemma relabel_port_support {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) (e : ℕ × Bool) (he : e.1 < D.length) :
    supp n (relabel σ D) (src (relabel σ D) e) = (supp n D (src D e)).image σ := by
  rw [relabel_src σ D e he, relabel_supp σ hS]

lemma relabel_gate_support {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) (k : ℕ) :
    supp n (relabel σ D) (n + k) = (supp n D (n + k)).image σ := by
  simpa only [tr_liftP_ge σ (Nat.le_add_right n k)] using relabel_supp σ hS (n + k)

lemma relabel_W {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (v : Fin n) :
    sem_W n (relabel σ D) (σ v) = sem_W n D v := by
  ext e
  rw [sem_mem_W, sem_mem_W, relabel_length]
  by_cases he : e.1 < D.length
  · simp only [he, true_and]
    rw [relabel_port_support σ hS e he, relabel_gate_support σ hS,
      relabel_mem_image, relabel_mem_image]
  · simp only [he, false_and]

lemma relabel_W_preimage {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) (v : Fin n) :
    sem_W n (relabel σ D) v = sem_W n D (σ.symm v) := by
  simpa only [Equiv.apply_symm_apply] using relabel_W σ hS (σ.symm v)

lemma relabel_comp {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    {G H : Fin n → Fin n → Prop}
    (h : StrictLive n D) (hC : sem_Comp n G D)
    (hσ : ∀ u v, H (σ u) (σ v) ↔ G u v) : sem_Comp n H (relabel σ D) := by
  intro x
  rw [relabel_out σ h.1 h.2.2, hC]
  constructor
  · rintro ⟨u,v,huv,hu,hv⟩
    exact ⟨σ u,σ v,(hσ u v).mpr huv,hu,hv⟩
  · rintro ⟨u,v,huv,hu,hv⟩
    refine ⟨σ.symm u,σ.symm v,(hσ _ _).mp (by simpa using huv),?_,?_⟩
    · simpa using hu
    · simpa using hv

lemma relabel_sem_Gr {n : ℕ} (σ : Equiv.Perm (Fin n))
    {G H : Fin n → Fin n → Prop} (hG : sem_Gr G)
    (hσ : ∀ u v, H (σ u) (σ v) ↔ G u v) : sem_Gr H := by
  have hf (u v : Fin n) : H u v ↔ G (σ.symm u) (σ.symm v) := by
    simpa using hσ (σ.symm u) (σ.symm v)
  refine ⟨?_,?_,?_,?_⟩
  · intro u v huv
    exact (hf v u).mpr (hG.1 _ _ ((hf u v).mp huv))
  · intro u huu
    exact hG.2.1 _ ((hf u u).mp huu)
  · intro v w hvw
    obtain ⟨z,hvz,hwz⟩ := hG.2.2.1 (σ.symm v) (σ.symm w)
      (fun he => hvw (σ.symm.injective he))
    refine ⟨σ z,?_,?_⟩
    · exact (hf v (σ z)).mpr (by simpa using hvz)
    · intro hw
      exact hwz (by simpa using (hf w (σ z)).mp hw)
  · intro u v
    obtain ⟨a,ha,hav⟩ := hG.2.2.2 (σ.symm u) (σ.symm v)
    refine ⟨σ a,(hf u (σ a)).mpr (by simpa using ha),?_⟩
    intro he
    exact hav (by simpa using congrArg σ.symm he)

lemma relabel_comp_auto {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    {G : Fin n → Fin n → Prop}
    (h : StrictLive n D) (hC : sem_Comp n G D)
    (hσ : ∀ u v, G (σ u) (σ v) ↔ G u v) : sem_Comp n G (relabel σ D) :=
  relabel_comp σ h hC hσ

end DagTools

namespace DagTools

lemma relabel_inner {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (hne : D ≠ []) :
    (inner n D).image (liftP σ) = inner n (relabel σ D) := by
  have hlen : 0 < D.length := List.length_pos_iff.mpr hne
  have hcut : n ≤ n + D.length - 1 := by omega
  ext w
  simp only [Finset.mem_image, inner, Finset.mem_range, relabel_length]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (tr_liftP_lt_iff σ hcut v).2 hv
  · intro hw
    refine ⟨liftP σ⁻¹ w, ?_, tr_liftP_inv' σ w⟩
    exact (tr_liftP_lt_iff σ⁻¹ hcut w).2 hw

lemma relabel_Bplus {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) (hne : D ≠ []) : Bplus n (relabel σ D) = Bplus n D := by
  classical
  unfold Bplus surplusOn
  rw [Finset.sum_filter, Finset.sum_filter, ← relabel_inner σ D hne, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro w hw
    rw [relabel_supp σ hS]
    simp only [Finset.image_nonempty, relabel_fanout]
  · intro a ha b hb he
    exact (tr_liftP_inj σ).mp he

lemma relabel_Bzero {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) (hne : D ≠ []) : Bzero n (relabel σ D) = Bzero n D := by
  classical
  unfold Bzero surplusOn
  rw [Finset.sum_filter, Finset.sum_filter, ← relabel_inner σ D hne, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro w hw
    rw [relabel_supp σ hS]
    simp only [Finset.image_nonempty, relabel_fanout]
  · intro a ha b hb he
    exact (tr_liftP_inj σ).mp he

end DagTools

namespace DagTools

lemma relabel_all_eligible {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) (hall : eligSet n D = Finset.univ) :
    eligSet n (relabel σ D) = Finset.univ := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro v
  rw [relabel_eligSet σ hS]
  exact Finset.mem_image.mpr
    ⟨σ.symm v, by rw [hall]; exact Finset.mem_univ _, σ.apply_symm_apply v⟩

lemma relabel_slot_exclusion {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    {G H : Fin n → Fin n → Prop}
    (h : StrictLive n D) (hC : sem_Comp n G D)
    (hσ : ∀ u v, H (σ u) (σ v) ↔ G u v)
    (b z : ℕ) (S : (Fin n → Finset (ℕ × Bool)) → Prop)
    (hcanonical : ∀ E : Dag, StrictLive n E → sem_Comp n H E →
      eligSet n E = Finset.univ → Bplus n E = b → Bzero n E = z →
      S (sem_W n E) → False)
    (hall : eligSet n D = Finset.univ) (hb : Bplus n D = b) (hz : Bzero n D = z)
    (hslots : S (fun v => sem_W n D (σ.symm v))) : False := by
  apply hcanonical (relabel σ D) (relabel_strictLive σ h) (relabel_comp σ h hC hσ)
    (relabel_all_eligible σ h.1 hall)
  · rw [relabel_Bplus σ h.1 h.2.2]
    exact hb
  · rw [relabel_Bzero σ h.1 h.2.2]
    exact hz
  · have hW : sem_W n (relabel σ D) = fun v => sem_W n D (σ.symm v) :=
      funext (relabel_W_preimage σ h.1)
    rw [hW]
    exact hslots

end DagTools

namespace DagTools

lemma relabel_elig_card {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) :
    (eligSet n (relabel σ D)).card = (eligSet n D).card := by
  rw [relabel_eligSet σ hS, Finset.card_image_of_injective _ σ.injective]

lemma relabel_tight_budget {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (hS : Strict n D) (hne : D ≠ [])
    (hb : Bplus n D = (eligSet n D).card) :
    Bplus n (relabel σ D) = (eligSet n (relabel σ D)).card := by
  rw [relabel_Bplus σ hS hne, relabel_elig_card σ hS]
  exact hb

lemma relabel_tight_slot_exclusion {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag}
    {G H : Fin n → Fin n → Prop}
    (h : StrictLive n D) (hC : sem_Comp n G D)
    (hσ : ∀ u v, H (σ u) (σ v) ↔ G u v)
    (z : ℕ) (S : (Fin n → Finset (ℕ × Bool)) → Prop)
    (hcanonical : ∀ E : Dag, StrictLive n E → sem_Comp n H E →
      Bplus n E = (eligSet n E).card → Bzero n E = z →
      S (sem_W n E) → False)
    (hb : Bplus n D = (eligSet n D).card) (hz : Bzero n D = z)
    (hslots : S (fun v => sem_W n D (σ.symm v))) : False := by
  apply hcanonical (relabel σ D) (relabel_strictLive σ h) (relabel_comp σ h hC hσ)
    (relabel_tight_budget σ h.1 h.2.2 hb)
  · rw [relabel_Bzero σ h.1 h.2.2]
    exact hz
  · have hW : sem_W n (relabel σ D) = fun v => sem_W n D (σ.symm v) :=
      funext (relabel_W_preimage σ h.1)
    rw [hW]
    exact hslots

end DagTools

end PEqualNP.Outside.L_meta_2590
