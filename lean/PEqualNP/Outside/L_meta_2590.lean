import PEqualNP.Defs
import Mathlib.Logic.Relation
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto

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

lemma sem_src_lt (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) < n + j := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  cases s
  · rw [sb_src_false]; exact ha
  · rw [sb_src_true]; exact hb

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

end DagTools

namespace Petersen

abbrev V := Fin 10

def edges : Finset (Sym2 V) := {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0), s(0, 5), s(1, 6), s(2, 7), s(3, 8),
      s(4, 9), s(5, 7), s(6, 8), s(7, 9), s(8, 5), s(9, 6)}

def related (v w : V) : Bool := decide (s(v, w) ∈ edges)

def digit (w i : ℕ) (t : List ℕ) : ℕ :=
  (t[i / 16]?.getD 0 >>> (w * (i % 16))) % (2 ^ w)

def Autom (f : V → V) : Prop := ∀ v w, related (f v) (f w) = related v w

def permWord (i : ℕ) : ℕ := digit 40 i ([126226149157589975746341902316111795087821178652033608920161735958946923079870511985886294867129905945234916616031849721433987644004584800004927027771687814726114274588084853161905303621743120, 2660427616327399435269531481718178401646082027935301662405787220980513690381215809495705737399288358085788155882573235272057163748261904316948553213991739791448677035952218303664639833339474945, 1239776632479440460244602490183314676691547349958322777359778274831490461234906931871140444825865134744593906462442277757210676840076939554254334611650596719953180810767997775417393455447621720, 680685397305202844481730047074739049850684476135515465580967989292822686912974557059058932175023691582793193531654587653421625127084123126121360498644757611592746733010595291706279375578552370, 2359441078723314407906557783535630859696363947135212612127674429424469707800345139931796134771291749332960158557197026408827764011363104189937445598002369409681521431006698551114156449727010595, 1791754269936980387159954496114408964656880037637619497637505127712020123491113231000397111323065666707872711214067982177652391611727069481362886028575371653022816591766911860414686323241216320, 1541088152341823624237729883312090527910832664816948779100557851341024978419659269577389250850737176470168489800182385030007969897233769982389941546953591982700802455662121076718277292290230645, 835185793909363909917313300847005245958202268679457184379754624500360860895227543323517272014935] : List ℕ)

def permV (k : Fin 120) (v : V) : V := ⟨((permWord k.val >>> (4*v.val)) % 16) % 10, by omega⟩

lemma permVgood : ∀ k : Fin 120, Autom (permV k) := by
  unfold Autom
  decide +kernel

lemma permVinj : ∀ k : Fin 120, Function.Injective (permV k) := by
  unfold Function.Injective
  decide +kernel

noncomputable def permEquiv (k : Fin 120) : Equiv.Perm V :=
  Equiv.ofBijective (permV k) (Finite.injective_iff_bijective.mp (permVinj k))

end Petersen

namespace SlotGeometry

abbrev V := Fin 10

def mask (m : ℕ) : Finset V := Finset.univ.filter fun i => m.testBit i.val

def edges : List (V × V) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

def cross (r : ℕ × ℕ) (e : V × V) : Bool :=
  decide ((e.1 ∈ mask r.1 ∧ e.2 ∈ mask r.2) ∨
    (e.2 ∈ mask r.1 ∧ e.1 ∈ mask r.2))

def dirtyOf (r : ℕ × ℕ) : List (V × V) := edges.filter (cross r)

def oppositeOf (p : List (ℕ × ℕ)) (v : V) : Finset V := p.foldl (fun acc r =>
  acc ∪ (if v ∈ mask r.1 then mask r.2 else ∅) ∪
    (if v ∈ mask r.2 then mask r.1 else ∅)) ∅

def geometry (p : List (ℕ × ℕ)) : Prop :=
  p.length = 6 ∧
  (∀ v : V, ((p.map fun r => (if v ∈ mask r.1 then 1 else 0) +
      (if v ∈ mask r.2 then 1 else 0)).sum : ℕ) = 2) ∧
  (∀ e ∈ edges, (p.filter fun r => cross r e).length = 1) ∧
  ∃ r ∈ p,
    (mask r.1).card = 3 ∧ (mask r.2).card = 3 ∧
    Disjoint (mask r.1) (mask r.2) ∧ (dirtyOf r).length = 6 ∧
    (∀ S : Finset V, S.card ≤ 2 → ∃ e ∈ dirtyOf r, e.1 ∉ S ∧ e.2 ∉ S) ∧
    (∀ v : V, v ∉ mask r.1 ∪ mask r.2 →
      ∃ e ∈ dirtyOf r, e.1 ∉ oppositeOf p v ∧ e.2 ∉ oppositeOf p v) ∧
    ∀ q ∈ p, q ≠ r → (mask q.1).card ≤ 2 ∧ (mask q.2).card ≤ 2

end SlotGeometry

namespace ExtraGeometry

abbrev V := Fin 10

def mask (m : ℕ) : Finset V := Finset.univ.filter fun i => m.testBit i.val

def edges : List (V × V) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

def cross (r : ℕ × ℕ) (e : V × V) : Bool :=
  decide ((e.1 ∈ mask r.1 ∧ e.2 ∈ mask r.2) ∨
    (e.2 ∈ mask r.1 ∧ e.1 ∈ mask r.2))

def dirtyOf (r : ℕ × ℕ) : List (V × V) := edges.filter (cross r)

def oppositeOf (p : List (ℕ × ℕ)) (v : V) : Finset V := p.foldl (fun acc r =>
  acc ∪ (if v ∈ mask r.1 then mask r.2 else ∅) ∪
    (if v ∈ mask r.2 then mask r.1 else ∅)) ∅

end ExtraGeometry



namespace FiniteSlots

abbrev V := Fin 10
abbrev H := Fin 15 × Bool
abbrev Slot := ℕ × Bool

def edges : Fin 15 → V × V := ![(0,1),(1,2),(2,3),(3,4),(4,0),
  (0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def endpoint (h : H) : V := if h.2 then (edges h.1).2 else (edges h.1).1
def barH (h : H) : H := (h.1, !h.2)
def bar (s : Slot) : Slot := (s.1, !s.2)
def incident (v : V) : Finset H := Finset.univ.filter fun h => endpoint h = v
def selected (t : H → Slot) (v : V) : Finset Slot := (incident v).image t

def lower (t : H → Slot) (h : H) : Finset V :=
  Finset.univ.filter fun v => ∃ k : H, endpoint k = v ∧ t k = t h

def independent (A : Finset V) : Prop :=
  ∀ e : Fin 15, ¬((edges e).1 ∈ A ∧ (edges e).2 ∈ A)
def touches (v : V) (A : Finset V) : Prop :=
  ∃ h : H, endpoint h = v ∧ endpoint (barH h) ∈ A

def Conditions (t : H → Slot) : Prop :=
  (∀ h, t (barH h) = bar (t h)) ∧
  (∀ h, endpoint h ∉ lower t (barH h)) ∧
  (∀ v, (selected t v).card ≤ 2) ∧
  ∀ v A, independent A → touches v A → (selected t v).card = 2 →
    ∃ h : H, endpoint h = v ∧ Disjoint (lower t h) A

lemma mem_selected {t : H → Slot} {v : V} {s : Slot} :
    s ∈ selected t v ↔ ∃ h : H, endpoint h = v ∧ t h = s := by
  simp only [selected, incident, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]

lemma lower_subset (t : H → Slot) (S : Slot → Finset V) (W : V → Finset Slot)
    (hw : ∀ h, t h ∈ W (endpoint h))
    (hs : ∀ v s, s ∈ W v → v ∈ S s) (h : H) : lower t h ⊆ S (t h) := by
  intro v hv
  obtain ⟨k, hk, he⟩ := (Finset.mem_filter.mp hv).2
  have hvS := hs (endpoint k) (t k) (hw k)
  simpa only [hk, he] using hvS

lemma conditions_of_exits (t : H → Slot) (S : Slot → Finset V) (W : V → Finset Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (hw : ∀ h, t h ∈ W (endpoint h))
    (hs : ∀ v s, s ∈ W v → v ∈ S s)
    (ho : ∀ h, endpoint h ∉ S (t (barH h)))
    (hc : ∀ v, (W v).card ≤ 2)
    (he : ∀ v A, independent A → touches v A →
      ∃ s ∈ W v, Disjoint (S s) A) : Conditions t := by
  have hsub (v : V) : selected t v ⊆ W v := by
    intro s hs'
    obtain ⟨h, rfl, rfl⟩ := mem_selected.mp hs'
    exact hw h
  refine ⟨hb, ?_, ?_, ?_⟩
  · intro h hh
    exact ho h (lower_subset t S W hw hs (barH h) hh)
  · intro v
    exact (Finset.card_le_card (hsub v)).trans (hc v)
  · intro v A hA hv htwo
    have hEq : selected t v = W v :=
      Finset.eq_of_subset_of_card_le (hsub v) (by rw [htwo]; exact hc v)
    obtain ⟨s, hsW, hsA⟩ := he v A hA hv
    rw [← hEq] at hsW
    obtain ⟨h, hvh, hsh⟩ := mem_selected.mp hsW
    refine ⟨h, hvh, ?_⟩
    apply hsA.mono_left
    simpa only [hsh] using lower_subset t S W hw hs h

def around : V → Fin 3 → H := ![
  ![(0,false),(4,true),(5,false)], ![(0,true),(1,false),(6,false)],
  ![(1,true),(2,false),(7,false)], ![(2,true),(3,false),(8,false)],
  ![(3,true),(4,false),(9,false)], ![(5,true),(10,false),(14,true)],
  ![(6,true),(12,true),(13,false)], ![(7,true),(10,true),(11,false)],
  ![(8,true),(13,true),(14,false)], ![(9,true),(11,true),(12,false)]]

lemma around_endpoint : ∀ v i, endpoint (around v i) = v := by decide +kernel
lemma around_complete : ∀ v h, endpoint h = v → ∃ i, around v i = h := by decide +kernel

def block : Fin 4 → Fin 3 → Fin 2 := ![![0,0,1], ![0,1,0], ![0,1,1], ![0,0,0]]
def localCode (t : H → Slot) (v : V) : Fin 4 :=
  if t (around v 0) = t (around v 1) then
    if t (around v 0) = t (around v 2) then 3 else 0
  else if t (around v 0) = t (around v 2) then 1 else 2

lemma repeated_at_vertex (t : H → Slot) (v : V) (hc : (selected t v).card ≤ 2) :
    t (around v 0) = t (around v 1) ∨ t (around v 0) = t (around v 2) ∨
      t (around v 1) = t (around v 2) := by
  by_contra hn
  simp only [not_or] at hn
  have hmem (i : Fin 3) : t (around v i) ∈ selected t v :=
    mem_selected.mpr ⟨around v i, around_endpoint v i, rfl⟩
  have hsub : {t (around v 0), t (around v 1), t (around v 2)} ⊆ selected t v := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact hmem 0
    · exact hmem 1
    · exact hmem 2
  have hh := (Finset.card_le_card hsub).trans hc
  simp [hn.1, hn.2.1, hn.2.2] at hh

lemma localCode_exact (t : H → Slot) (v : V) (hc : (selected t v).card ≤ 2)
    (i j : Fin 3) :
    t (around v i) = t (around v j) ↔
      block (localCode t v) i = block (localCode t v) j := by
  have hr := repeated_at_vertex t v hc
  by_cases h01 : t (around v 0) = t (around v 1)
  · by_cases h02 : t (around v 0) = t (around v 2)
    · have h12 := h01.symm.trans h02
      fin_cases i <;> fin_cases j <;> simp [localCode, block, h01, h02, h12]
    · have h12 : t (around v 1) ≠ t (around v 2) := fun h => h02 (h01.trans h)
      fin_cases i <;> fin_cases j <;> simp [localCode, block, h01, h02, h12, Ne.symm h02, Ne.symm h12]
  · by_cases h02 : t (around v 0) = t (around v 2)
    · have h12 : t (around v 1) ≠ t (around v 2) := fun h => h01 (h02.trans h.symm)
      fin_cases i <;> fin_cases j <;> simp [localCode, block, h01, h02, h12, Ne.symm h01, Ne.symm h12]
    · have h12 := hr.resolve_left h01 |>.resolve_left h02
      fin_cases i <;> fin_cases j <;> simp [localCode, block, h01, h02, h12, Ne.symm h01, Ne.symm h02]

def seed (q : V → Fin 4) (h k : H) : Prop :=
  ∃ v : V, ∃ i j : Fin 3, block (q v) i = block (q v) j ∧
    ((h = around v i ∧ k = around v j) ∨
      (h = barH (around v i) ∧ k = barH (around v j)))
def closed (q : V → Fin 4) : H → H → Prop := Relation.ReflTransGen (seed q)

lemma seed_sound (t : H → Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (hc : ∀ v, (selected t v).card ≤ 2) {h k : H}
    (hr : seed (localCode t) h k) : t h = t k := by
  obtain ⟨v, i, j, hij, hcases⟩ := hr
  have he := (localCode_exact t v (hc v) i j).mpr hij
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact he
  · rw [hb, hb, he]

lemma closed_sound (t : H → Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (hc : ∀ v, (selected t v).card ≤ 2) {h k : H}
    (hr : closed (localCode t) h k) : t h = t k := by
  induction hr with
  | refl => rfl
  | tail _ hseed ih => exact ih.trans (seed_sound t hb hc hseed)

lemma closed_local_exact (t : H → Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (hc : ∀ v, (selected t v).card ≤ 2) (v : V) (i j : Fin 3) :
    closed (localCode t) (around v i) (around v j) ↔
      block (localCode t v) i = block (localCode t v) j := by
  constructor
  · intro hr
    exact (localCode_exact t v (hc v) i j).mp (closed_sound t hb hc hr)
  · intro hij
    exact Relation.ReflTransGen.single ⟨v, i, j, hij, Or.inl ⟨rfl, rfl⟩⟩

lemma card_two_of_code_ne_three (t : H → Slot) (v : V)
    (hc : (selected t v).card ≤ 2) (hq : localCode t v ≠ 3) :
    (selected t v).card = 2 := by
  have hblocks : ∀ q : Fin 4, q ≠ 3 → ∃ i j : Fin 3, block q i ≠ block q j := by
    decide +kernel
  obtain ⟨i, j, hij⟩ := hblocks (localCode t v) hq
  have hne : t (around v i) ≠ t (around v j) :=
    fun he => hij ((localCode_exact t v hc i j).mp he)
  have hmem (k : Fin 3) : t (around v k) ∈ selected t v :=
    mem_selected.mpr ⟨around v k, around_endpoint v k, rfl⟩
  have hsub : {t (around v i), t (around v j)} ⊆ selected t v := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact hmem i
    · exact hmem j
  have hh := Finset.card_le_card hsub
  simp [hne] at hh
  omega

def CodeConditions (q : V → Fin 4) : Prop :=
  (∀ v i j, closed q (around v i) (around v j) ↔ block (q v) i = block (q v) j) ∧
  (∀ h k, endpoint k = endpoint h → ¬ closed q k (barH h)) ∧
  ∀ v A, independent A → touches v A → q v ≠ 3 →
    ∃ i : Fin 3, ∀ h : H, closed q h (around v i) → endpoint h ∉ A

lemma code_conditions (t : H → Slot) (ht : Conditions t) :
    CodeConditions (localCode t) := by
  obtain ⟨hb, ho, hc, he⟩ := ht
  refine ⟨closed_local_exact t hb hc, ?_, ?_⟩
  · intro h k hv hrel
    apply ho h
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, k, hv, closed_sound t hb hc hrel⟩
  · intro v A hA hv hq
    obtain ⟨h, hhv, hdis⟩ := he v A hA hv (card_two_of_code_ne_three t v (hc v) hq)
    obtain ⟨i, hi⟩ := around_complete v h hhv
    refine ⟨i, ?_⟩
    intro k hrel hkA
    have hlower : endpoint k ∈ lower t h := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, k, rfl, ?_⟩
      rw [hi] at hrel
      exact closed_sound t hb hc hrel
    exact Finset.disjoint_left.mp hdis hlower hkA

end FiniteSlots

namespace FiniteSlots

lemma closed_of_local (q : V → Fin 4) (v : V) (i j : Fin 3)
    (hij : block (q v) i = block (q v) j) :
    closed q (around v i) (around v j) :=
  Relation.ReflTransGen.single ⟨v, i, j, hij, Or.inl ⟨rfl, rfl⟩⟩

lemma closed_of_bar_local (q : V → Fin 4) (v : V) (i j : Fin 3)
    (hij : block (q v) i = block (q v) j) :
    closed q (barH (around v i)) (barH (around v j)) :=
  Relation.ReflTransGen.single ⟨v, i, j, hij, Or.inr ⟨rfl, rfl⟩⟩

lemma reject_local {q : V → Fin 4} (hq : CodeConditions q) (v : V) (i j : Fin 3)
    (hc : closed q (around v i) (around v j))
    (hne : block (q v) i ≠ block (q v) j) : False :=
  hne ((hq.1 v i j).mp hc)

lemma reject_opposite {q : V → Fin 4} (hq : CodeConditions q) (h k : H)
    (hv : endpoint k = endpoint h) (hc : closed q k (barH h)) : False :=
  hq.2.1 h k hv hc

lemma reject_exposure {q : V → Fin 4} (hq : CodeConditions q) (v : V) (A : Finset V)
    (hA : independent A) (hv : touches v A) (htwo : q v ≠ 3)
    (hhit : ∀ i : Fin 3, ∃ h : H, closed q h (around v i) ∧ endpoint h ∈ A) : False := by
  obtain ⟨i, hi⟩ := hq.2.2 v A hA hv htwo
  obtain ⟨h, hc, hm⟩ := hhit i
  exact hi h hc hm

lemma closed_of_code (q : V → Fin 4) (v : V) (c : Fin 4) (i j : Fin 3)
    (hq : q v = c) (hij : block c i = block c j) :
    closed q (around v i) (around v j) :=
  closed_of_local q v i j (by rw [hq]; exact hij)

lemma closed_of_bar_code (q : V → Fin 4) (v : V) (c : Fin 4) (i j : Fin 3)
    (hq : q v = c) (hij : block c i = block c j) :
    closed q (barH (around v i)) (barH (around v j)) :=
  closed_of_bar_local q v i j (by rw [hq]; exact hij)

lemma reject_local_of_code {q : V → Fin 4} (hq : CodeConditions q)
    (v : V) (c : Fin 4) (i j : Fin 3) (hv : q v = c)
    (hc : closed q (around v i) (around v j))
    (hne : block c i ≠ block c j) : False :=
  reject_local hq v i j hc (by rw [hv]; exact hne)

end FiniteSlots

namespace SlotTables
open PEqualNP.Outside.L_meta_2590.FiniteSlots

abbrev Step := V × Fin 3 × Fin 3 × Bool

def stepStart (d : Step) : H :=
  if d.2.2.2 then barH (around d.1 d.2.1) else around d.1 d.2.1

def stepEnd (d : Step) : H :=
  if d.2.2.2 then barH (around d.1 d.2.2.1) else around d.1 d.2.2.1

abbrev stepValid (q : V → Fin 4) (d : Step) : Prop :=
  block (q d.1) d.2.1 = block (q d.1) d.2.2.1

lemma step_seed (q : V → Fin 4) (d : Step) (hv : stepValid q d) :
    seed q (stepStart d) (stepEnd d) := by
  rcases d with ⟨v, i, j, s⟩
  cases s
  · exact ⟨v, i, j, hv, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨v, i, j, hv, Or.inr ⟨rfl, rfl⟩⟩

def checkPath (q : V → Fin 4) (h : H) : List Step → H → Bool
  | [], k => decide (h = k)
  | d :: ds, k => decide (h = stepStart d) && decide (stepValid q d) &&
      checkPath q (stepEnd d) ds k

lemma checkPath_closed (q : V → Fin 4) (ds : List Step) (h k : H)
    (hc : checkPath q h ds k = true) : closed q h k := by
  induction ds generalizing h with
  | nil =>
    have he : h = k := by simpa [checkPath] using hc
    subst h
    exact Relation.ReflTransGen.refl
  | cons d ds ih =>
    simp only [checkPath, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with ⟨⟨rfl, hv⟩, ht⟩
    exact (Relation.ReflTransGen.single (step_seed q d hv)).trans (ih _ ht)

lemma seed_symm (q : V → Fin 4) {h k : H} (hs : seed q h k) : seed q k h := by
  obtain ⟨v, i, j, hij, hcases⟩ := hs
  refine ⟨v, j, i, hij.symm, ?_⟩
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

lemma closed_symm (q : V → Fin 4) {h k : H} (hc : closed q h k) : closed q k h := by
  induction hc with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact (Relation.ReflTransGen.single (seed_symm q hs)).trans ih

def codeWords : Fin 45 → ℕ := ![
  0x1a9aa,
  0x8696a,
  0x63f3a,
  0x86969,
  0xa1959,
  0xd8dcd,
  0x86968,
  0x44908,
  0x44508,
  0x44108,
  0x44d08,
  0x3db9c,
  0xa1a59,
  0xa1859,
  0xa1b59,
  0x1a9a6,
  0x1a9a2,
  0x1a9ae,
  0x8696b,
  0x6a6a6,
  0x8f0e7,
  0x12022,
  0x10022,
  0x11022,
  0x13022,
  0xf6673,
  0x6a696,
  0x6a686,
  0x6a6b6,
  0xa8295,
  0x49484,
  0x45484,
  0x41484,
  0x4d484,
  0xa8255,
  0xa8215,
  0xa82d5,
  0x24210,
  0x4210,
  0x14210,
  0x34210,
  0x91441,
  0x11441,
  0x51441,
  0xd1441]

def code (p : Fin 45) (v : V) : Fin 4 :=
  ⟨(Nat.shiftRight (codeWords p) (2 * v.val)) % 4, Nat.mod_lt _ (by decide)⟩

def slotWords : Fin 45 → ℕ := ![
  0xba9889baabbaab76543223ab765410,
  0x89baabba9876baab54322367ab5410,
  0x455445765454325445455445544510,
  0x89baabba9876baab54320167ab5432,
  0x8998abba9876549889320167458932,
  0x765467766776673267760167766776,
  0x89baabba9876baab54320167ab5410,
  0x457689ba549876ab89320189988910,
  0x457689ba329876ab89450189988910,
  0x457689ba329876ab89230189988910,
  0x235467983276548967230167766710,
  0x766745766776676776107667327667,
  0x8998abba9876549889107632458910,
  0x8998abba9876329889104554238910,
  0x677689987654327667105445236710,
  0xba9889baabbaab76541001ab763245,
  0xba9889baabbaab76541001ab763223,
  0x987667988998895432100189543223,
  0x679889987654988932100145893210,
  0x899889baab98765432899876541023,
  0x457667766732766767766776671076,
  0x459889ba76ba547632677667761001,
  0x237689ba54ba325489455445541001,
  0x237689ba54ba325467455445541001,
  0x237667985498325467455445541001,
  0x677667765476766710677632677667,
  0x899889baab98765410899876324501,
  0x899889baab98765410899876322301,
  0x677667988976543210677654322301,
  0x8998abbaab765432abba76541023ba,
  0x457689baab98763267456776100176,
  0x457689ba329876ab67456776100176,
  0x237689ba5498765467236776100176,
  0x235467988976548945234554100154,
  0x8998abbaab765410abba76324501ba,
  0x8998abbaab765410abba76322301ba,
  0x677689988954321089985432230198,
  0x899867ba54ba32ab6745ba1001baab,
  0x459867ba32ba98ab6723ba1001baab,
  0x457689ba32ba54ab8923ba1001baab,
  0x677645983298768945239810019889,
  0x6798abba5432765489670110677667,
  0x457689ba32ba543267450110455445,
  0x457689ba3298543267450110455445,
  0x457689983298543267450110455445]

def slotValue (p : Fin 45) (k : ℕ) : Fin 30 :=
  ⟨(Nat.shiftRight (slotWords p) (4 * k)) % 16,
    (Nat.mod_lt _ (by decide)).trans (by decide : 16 < 30)⟩

def slotData (p : Fin 45) (e : Fin 15) : Fin 30 × Fin 30 :=
  (slotValue p (2 * e.val), slotValue p (2 * e.val + 1))

def slot (i : Fin 45) (h : H) : Fin 30 :=
  if h.2 then (slotData i h.1).2 else (slotData i h.1).1

def repWords : Fin 45 → ℕ := ![
  0x31f192906242420,
  0x216b431c6242420,
  0xbd8438c020,
  0x216b431c6208109,
  0xbd84331c8508109,
  0x837a7b909,
  0x216b431c625a820,
  0x73c438c2b45a820,
  0x73c438c14bad020,
  0x73c438c39d52c20,
  0x1cf10e3052c20,
  0x7192916a,
  0xbd8434a08539820,
  0xbd8439c8e621420,
  0x2f610cc721420,
  0x31f192900118909,
  0x31f19291ac00509,
  0xc7c64a400509,
  0x85ad0c718820,
  0xa5528398a400462,
  0x839d9c862,
  0x9cb19292306b001,
  0x9c98dde8a48c001,
  0x9cb19634a48c001,
  0x272634a48c001,
  0x6b4399ac,
  0xa55283984329001,
  0xa5528399ee10c01,
  0x2954a0e610c01,
  0x837a4a0e610ca4,
  0xa56720814b7b843,
  0x73e720814bad043,
  0xbda72081ee52c43,
  0x1cf9c82052c43,
  0x837a4a08539843,
  0x837a4a23021443,
  0x20de92821443,
  0x77a6354b8c085,
  0x6306379d52c85,
  0x58ddea3052c85,
  0x18c18d52c85,
  0xbd98d005ee9c8e6,
  0x9cb19634017b8e6,
  0xbda72634017b8e6,
  0x272634017b8e6]

def representative (p : Fin 45) (c : Fin 30) : H :=
  let z := (Nat.shiftRight (repWords p) (5 * c.val)) % 32
  (⟨(z / 2) % 15, Nat.mod_lt _ (by decide)⟩, z.testBit 0)

def pathWords : Fin 45 → ℕ := ![
  0x6394400b18a200002cc800006640000000000000000490330004919ac628cae63942570000248800002440000b1a000018d00002c4800006240000b0a000018500002c080000604000000000000000000000000000000000000000000000000000000000000000000000000,
  0x32a00005950048c310004718847184b7230c65b0018a4f002c427800000000000000000024880000244000091a000008d00002c4800006240000b0a000018500002c080000604000000000000000000000000000000000000000000000000000000000000000000000000,
  0x451732f220bd97001864d002c226801610b40030c5a00000000000000001220bc001145e8904e4984a2624c000000000000000000244800002240000b0a00001851145c8bc882f45e24138a612898530004a27002241380000892000004900000000000000000000000000000,
  0x32a00005950048c310004718847184b7230c65b0018a4f002c427800000000000000000024880000244000091a000008d00002c4800006240000b0a0000185000024080000204000000000000000000000000000000000000000000000000000000000000000000000000,
  0x451732f220bd97001864d002c22680000b4a00001a500000000000000001220bc001145e000024880000244000091a000008d0000244800002240000b0a0000185000024080000204000000000000000000000000000000000000000000000000000000000000000000000000,
  0x12012c001049600000000000000001210b40010c5a90056cf8822a67c00208ac009005610c5913c842d89e221291e118908f000000000000000000090a0000085000024080000204000000000000008884a278462413c0011894008884a00002228000011400000000000000,
  0x32a00005950048c310004718847184b7230c65b0018a4f002c427800000000000000000024880000244000091a000008d00002c4800006240000b0a0000185000000000000000000008200004410000000000000000000000000000000000000000000000000000000000,
  0x32a000059500000308000118401610b40030c5a000024e80000274000000000000008904e4984a2624c000000000000000000000000000000000b0a0000185000000000000000000008200004410004a27002241380000892000004900000000000000000000000000000,
  0x12a000049500000308000118401610b40030c5a000024e80000274000000000000008904e4984a2624c000000000000000000000000000000000b0a0000185000000000000000000008200004410004a27002241380000892000004900000000000000000000000000000,
  0x308000118401610b40030c5a000024e8000027400008aa00000558904e4984a2624c000000000000000000000000000000000b0a0000185000000000000000000008200004410004a27002241380000892000004900000000000000000000000000000,
  0x12a000049500000308000118401610b40030c5a000024e8000027400008aa00000558904e4984a2624c000000000000000000000000000000000b0a0000185000000000000000000008200004410004a27002241380000892000004900000000000000000000000000000,
  0x24226b4621931a3000864d00242268000000000000008888a4f8464427c23220bf111145f00042c90022064a2044b1e10a218f000464500222228000090a0000085000000000000000000008200004410044089000214480000000000000000002228000011400000000000000,
  0x451732f220bd97001864d002c22680000b4a00001a500000000000000001220bc001145e00002c880000644000091a000008d0000244800002240000b0a0000185000024080000204000000000000000000000000000000000000000000000000000000000000000000000000,
  0x451732f220bd97001864d002c22680000b4a00001a500000000000000001220bc001145e000000000000000000091a000008d0000244800002240000b0a000018500002408000020400008a200000510000000000000000000000000000000000000000000000000000000000,
  0x451732f220bd97001864d002c22680000b4a00001a500000000000000001220bc001145e000024880000244000091a000008d0000244800002240000b0a000018500002408000020400008a200000510000000000000000000000000000000000000000000000000000000000,
  0x6394400b18a200002cc800006640000000000000000490330004919ac628cae63942570000248800002440000b1a000018d00002c480000624000090a000008500002c080000604000000000000000000000000000000000000000000000000000000000000000000000000,
  0x6394400b18a200002cc800006640000000000000000490330004919ac628cae63942570000248800002440000b1a000018d00002c4800006240000000000000000002c080000604000000000000000000000000000000000000000000000002228000011400000000000000,
  0x6394400b18a200002cc800006640000000000000000490330004919ac628cae63942570000248800002440000b1a000018d00002c480000624000090a000008500002c080000604000000000000000000000000000000000000000000000002228000011400000000000000,
  0x32a00005950048c310004718847184b7230c65b0018a4f002c427800000000000000000024880000244000091a000008d00002c4800006240000b0a0000185000024080000204000008200004410000000000000000000000000000000000000000000000000000000000,
  0x16012c0030496b20a6cd9925266c006494c00b20a600002ce800006740000000000000000002c8800006440000b1a000018d00002c480000624000090a000008500002c080000604000000000000000000000000000000000000000000000000000000000000000000000000,
  0x864d0024226801210b40010c5a90056cf8822a67c00208ac00900560000000000000022044b1e10a218f104548fc802b47c000090a000008500002408000020400000820000441004408900021448214421f102250f00000000000000000000000000000,
  0x94200000a100002cc800006640000000000000000000328000119401620bc003145e0000000000000000000000000000000002c4800006240000000000000089852c184e2860c00138a400898520000226800001340000000000000000002228000011400000000000000,
  0x94200000a100000000000000000000b2000045900000328000119401620bc003145e0000000000000000000000000000000002c4800006240000000000000089852c184e2860c00138a400898520000226800001340000000000000000002228000011400000000000000,
  0x94200000a1000024c800002640000000000000000000328000119401620bc003145e0000000000000000000000000000000002c4800006240000000000000089852c184e2860c00138a400898520000226800001340000000000000000002228000011400000000000000,
  0x94200000a1000024c8000026400000b2000045900000328000119401620bc003145e0000000000000000000000000000000002c4800006240000000000000089852c184e2860c00138a400898520000226800001340000000000000000002228000011400000000000000,
  0x12012c00104961049531c804b98e206494e10b20a78888a4f8464427c0000000000000000042c90022064a221291e118908f00046450022222800000000000000000024080000204000008200004410000000000000000011894008884a00002228000011400000000000000,
  0x16012c0030496b20a6cd9925266c006494c00b20a600002ce800006740000000000000000002c8800006440000b1a000018d000024480000224000090a000008500002c080000604000000000000000000000000000000000000000000000000000000000000000000000000,
  0x16012c0030496b20a6cd9925266c006494c00b20a600002ce800006740000000000000000002c8800006440000b1a000018d000000000000000000090a000008500002c080000604000000000000000000000000000000000892000004900000000000000000000000000000,
  0x16012c0030496b20a6cd9925266c006494c00b20a600002ce800006740000000000000000002c8800006440000b1a000018d000024480000224000090a000008500002c080000604000000000000000000000000000000000892000004900000000000000000000000000000,
  0xb4200001a100000000000000001210b40010c5a90056cf8822a67c00208ac009005600002c8800006440000b1a000018d000024480000224000090a0000085000024080000204000000000000000000000000000000000000000000000000000000000000000000000000,
  0x12a0000495000864d00242268000094a00000a500002ce80000674000000000000000000000000000022044b1e10a218f000000000000000000090a0000085000000000000000000008200004410044089000214480000892000004900000000000000000000000000000,
  0x12a0000495000864d00242268000094a00000a5000024e80000274000000000000000000000000000022044b1e10a218f000000000000000000090a0000085000000000000000000008200004410044089000214480000892000004900000000000000000000000000000,
  0x12a0000495000864d00242268000094a00000a500000000000000000000ba000045d0000000000000022044b1e10a218f000000000000000000090a0000085000000000000000000008200004410044089000214480000892000004900000000000000000000000000000,
  0x12a0000495000864d00242268000094a00000a5000024e8000027400000ba000045d0000000000000022044b1e10a218f000000000000000000090a0000085000000000000000000008200004410044089000214480000892000004900000000000000000000000000000,
  0xb4200001a100000000000000001210b40010c5a90056cf8822a67c00208ac009005600002c880000644000091a000008d000024480000224000090a0000085000024080000204000000000000000000000000000000000000000000000000000000000000000000000000,
  0xb4200001a100000000000000001210b40010c5a90056cf8822a67c00208ac009005600002c88000064400000000000000000024480000224000090a0000085000024080000204000000000000000000226800001340000000000000000000000000000000000000000000,
  0xb4200001a100000000000000001210b40010c5a90056cf8822a67c00208ac009005600002c880000644000091a000008d000024480000224000090a0000085000024080000204000000000000000000226800001340000000000000000000000000000000000000000000,
  0xb4200001a100000000000000000000b200004598888a4f8464427c00008aa000005500042c9002206480000000000000000046450022222800000000000000000000000000000000008200004410000226800001340000000000000000002228000011400000000000000,
  0x308000118400000b200004598888a4f8464427c00008aa000005500042c9002206480000000000000000046450022222800000000000000000000000000000000008200004410000226800001340000000000000000002228000011400000000000000,
  0x94200000a100000000000000000000b200004598888a4f8464427c00008aa000005500042c9002206480000000000000000046450022222800000000000000000000000000000000008200004410000226800001340000000000000000002228000011400000000000000,
  0x94200000a100000308000118400000b200004598888a4f8464427c00008aa000005500042c9002206480000000000000000046450022222800000000000000000000000000000000008200004410000226800001340000000000000000002228000011400000000000000,
  0x12012c0010496000024c800002640000b4a00001a500000000000000000000ba000045d000000000000002221291e118908f0000000000000000000000000000000002408000020400008a200000510000000000000000011894008884a00002228000011400000000000000,
  0x12012c0010496000024c800002640000000000000000000328000119400000ba000045d000000000000002221291e118908f0000000000000000000000000000000002408000020400008a200000510000000000000000011894008884a00002228000011400000000000000,
  0x12012c0010496000024c80000264000094a00000a500000000000000000000ba000045d000000000000002221291e118908f0000000000000000000000000000000002408000020400008a200000510000000000000000011894008884a00002228000011400000000000000,
  0x12012c0010496000024c80000264000094a00000a500000328000119400000ba000045d000000000000002221291e118908f0000000000000000000000000000000002408000020400008a200000510000000000000000011894008884a00002228000011400000000000000]

def unpackStep (z : ℕ) : Step :=
  (⟨(z % 16) % 10, Nat.mod_lt _ (by decide)⟩,
   ⟨((z / 16) % 4) % 3, Nat.mod_lt _ (by decide)⟩,
   ⟨((z / 64) % 4) % 3, Nat.mod_lt _ (by decide)⟩, z.testBit 8)

def unpackPath (z : ℕ) : List Step :=
  List.ofFn fun i : Fin (z % 4) => unpackStep (Nat.shiftRight z (2 + 9 * i.val))

def pathAt (p : Fin 45) (k : ℕ) : List Step :=
  unpackPath ((Nat.shiftRight (pathWords p) (29 * k)) % 536870912)

def pathData (p : Fin 45) (e : Fin 15) : List Step × List Step :=
  (pathAt p (2 * e.val), pathAt p (2 * e.val + 1))

def paths (i : Fin 45) (h : H) : List Step :=
  if h.2 then (pathData i h.1).2 else (pathData i h.1).1

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma seed_table_check : ∀ (r : Fin 45) (v : V) (a b : Fin 3),
    block (code r v) a = block (code r v) b →
      slot r (around v a) = slot r (around v b) ∧
      slot r (barH (around v a)) = slot r (barH (around v b)) := by
  decide +kernel

lemma seed_slots (r : Fin 45) {h k : H} (hs : seed (code r) h k) : slot r h = slot r k := by
  obtain ⟨v, i, j, hij, hcases⟩ := hs
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (seed_table_check r v i j hij).1
  · exact (seed_table_check r v i j hij).2

lemma closed_slots (r : Fin 45) {h k : H} (hc : closed (code r) h k) : slot r h = slot r k := by
  induction hc with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (seed_slots r hs)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_0 : ∀ h : H, checkPath (code 0) h (paths 0 h) (representative 0 (slot 0 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_1 : ∀ h : H, checkPath (code 1) h (paths 1 h) (representative 1 (slot 1 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_2 : ∀ h : H, checkPath (code 2) h (paths 2 h) (representative 2 (slot 2 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_3 : ∀ h : H, checkPath (code 3) h (paths 3 h) (representative 3 (slot 3 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_4 : ∀ h : H, checkPath (code 4) h (paths 4 h) (representative 4 (slot 4 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_5 : ∀ h : H, checkPath (code 5) h (paths 5 h) (representative 5 (slot 5 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_6 : ∀ h : H, checkPath (code 6) h (paths 6 h) (representative 6 (slot 6 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_7 : ∀ h : H, checkPath (code 7) h (paths 7 h) (representative 7 (slot 7 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_8 : ∀ h : H, checkPath (code 8) h (paths 8 h) (representative 8 (slot 8 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_9 : ∀ h : H, checkPath (code 9) h (paths 9 h) (representative 9 (slot 9 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_10 : ∀ h : H, checkPath (code 10) h (paths 10 h) (representative 10 (slot 10 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_11 : ∀ h : H, checkPath (code 11) h (paths 11 h) (representative 11 (slot 11 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_12 : ∀ h : H, checkPath (code 12) h (paths 12 h) (representative 12 (slot 12 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_13 : ∀ h : H, checkPath (code 13) h (paths 13 h) (representative 13 (slot 13 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_14 : ∀ h : H, checkPath (code 14) h (paths 14 h) (representative 14 (slot 14 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_15 : ∀ h : H, checkPath (code 15) h (paths 15 h) (representative 15 (slot 15 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_16 : ∀ h : H, checkPath (code 16) h (paths 16 h) (representative 16 (slot 16 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_17 : ∀ h : H, checkPath (code 17) h (paths 17 h) (representative 17 (slot 17 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_18 : ∀ h : H, checkPath (code 18) h (paths 18 h) (representative 18 (slot 18 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_19 : ∀ h : H, checkPath (code 19) h (paths 19 h) (representative 19 (slot 19 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_20 : ∀ h : H, checkPath (code 20) h (paths 20 h) (representative 20 (slot 20 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_21 : ∀ h : H, checkPath (code 21) h (paths 21 h) (representative 21 (slot 21 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_22 : ∀ h : H, checkPath (code 22) h (paths 22 h) (representative 22 (slot 22 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_23 : ∀ h : H, checkPath (code 23) h (paths 23 h) (representative 23 (slot 23 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_24 : ∀ h : H, checkPath (code 24) h (paths 24 h) (representative 24 (slot 24 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_25 : ∀ h : H, checkPath (code 25) h (paths 25 h) (representative 25 (slot 25 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_26 : ∀ h : H, checkPath (code 26) h (paths 26 h) (representative 26 (slot 26 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_27 : ∀ h : H, checkPath (code 27) h (paths 27 h) (representative 27 (slot 27 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_28 : ∀ h : H, checkPath (code 28) h (paths 28 h) (representative 28 (slot 28 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_29 : ∀ h : H, checkPath (code 29) h (paths 29 h) (representative 29 (slot 29 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_30 : ∀ h : H, checkPath (code 30) h (paths 30 h) (representative 30 (slot 30 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_31 : ∀ h : H, checkPath (code 31) h (paths 31 h) (representative 31 (slot 31 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_32 : ∀ h : H, checkPath (code 32) h (paths 32 h) (representative 32 (slot 32 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_33 : ∀ h : H, checkPath (code 33) h (paths 33 h) (representative 33 (slot 33 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_34 : ∀ h : H, checkPath (code 34) h (paths 34 h) (representative 34 (slot 34 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_35 : ∀ h : H, checkPath (code 35) h (paths 35 h) (representative 35 (slot 35 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_36 : ∀ h : H, checkPath (code 36) h (paths 36 h) (representative 36 (slot 36 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_37 : ∀ h : H, checkPath (code 37) h (paths 37 h) (representative 37 (slot 37 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_38 : ∀ h : H, checkPath (code 38) h (paths 38 h) (representative 38 (slot 38 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_39 : ∀ h : H, checkPath (code 39) h (paths 39 h) (representative 39 (slot 39 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_40 : ∀ h : H, checkPath (code 40) h (paths 40 h) (representative 40 (slot 40 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_41 : ∀ h : H, checkPath (code 41) h (paths 41 h) (representative 41 (slot 41 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_42 : ∀ h : H, checkPath (code 42) h (paths 42 h) (representative 42 (slot 42 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_43 : ∀ h : H, checkPath (code 43) h (paths 43 h) (representative 43 (slot 43 h)) = true := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma paths_44 : ∀ h : H, checkPath (code 44) h (paths 44 h) (representative 44 (slot 44 h)) = true := by
  decide +kernel

lemma paths_checked (i : Fin 45) (h : H) : checkPath (code i) h (paths i h) (representative i (slot i h)) = true := by
  fin_cases i
  · exact paths_0 h
  · exact paths_1 h
  · exact paths_2 h
  · exact paths_3 h
  · exact paths_4 h
  · exact paths_5 h
  · exact paths_6 h
  · exact paths_7 h
  · exact paths_8 h
  · exact paths_9 h
  · exact paths_10 h
  · exact paths_11 h
  · exact paths_12 h
  · exact paths_13 h
  · exact paths_14 h
  · exact paths_15 h
  · exact paths_16 h
  · exact paths_17 h
  · exact paths_18 h
  · exact paths_19 h
  · exact paths_20 h
  · exact paths_21 h
  · exact paths_22 h
  · exact paths_23 h
  · exact paths_24 h
  · exact paths_25 h
  · exact paths_26 h
  · exact paths_27 h
  · exact paths_28 h
  · exact paths_29 h
  · exact paths_30 h
  · exact paths_31 h
  · exact paths_32 h
  · exact paths_33 h
  · exact paths_34 h
  · exact paths_35 h
  · exact paths_36 h
  · exact paths_37 h
  · exact paths_38 h
  · exact paths_39 h
  · exact paths_40 h
  · exact paths_41 h
  · exact paths_42 h
  · exact paths_43 h
  · exact paths_44 h

lemma closed_iff_slot (i : Fin 45) (h k : H) : closed (code i) h k ↔ slot i h = slot i k := by
  constructor
  · exact closed_slots i
  · intro he
    have hh := checkPath_closed (code i) (paths i h) h _ (paths_checked i h)
    have hk := checkPath_closed (code i) (paths i k) k _ (paths_checked i k)
    rw [← he] at hk
    exact hh.trans (closed_symm _ hk)

end SlotTables

namespace SlotTree

open FiniteSlots

abbrev Partial := V → Option (Fin 4)

def Agrees (q : V → Fin 4) (p : Partial) : Prop :=
  ∀ v c, p v = some c → q v = c

lemma agrees_update {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (v : V) (c : Fin 4) (hc : q v = c) :
    Agrees q (Function.update p v (some c)) := by
  intro w d hd
  by_cases hw : w = v
  · subst w
    simp only [Function.update_self, Option.some.injEq] at hd
    exact hc.trans hd
  · rw [Function.update_of_ne hw] at hd
    exact ha w d hd

def position (h : H) : Fin 3 :=
  if h.2 then
    (![0,0,0,0,1,0,0,0,0,0,1,1,1,1,2] : Fin 15 → Fin 3) h.1
  else
    (![0,1,1,1,1,2,2,2,2,2,1,2,2,2,2] : Fin 15 → Fin 3) h.1

lemma around_position : ∀ h : H, around (endpoint h) (position h) = h := by
  decide +kernel

lemma barH_barH (h : H) : barH (barH h) = h := by
  rcases h with ⟨e, b⟩
  cases b <;> rfl

def directCheck (p : Partial) (h k : H) : Bool :=
  match p (endpoint h) with
  | none => false
  | some c => decide (endpoint k = endpoint h ∧ block c (position h) = block c (position k))

lemma directCheck_sound {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (h k : H) (sw : Bool) (ht : directCheck p h k = true) :
    closed q (if sw then barH h else h) (if sw then barH k else k) := by
  cases hp : p (endpoint h) with
  | none => simp [directCheck, hp] at ht
  | some c =>
    have hh : endpoint k = endpoint h ∧ block c (position h) = block c (position k) := by
      simpa only [directCheck, hp, decide_eq_true_eq] using ht
    have hk : around (endpoint h) (position k) = k := by
      rw [← hh.1]
      exact around_position k
    have hv := ha (endpoint h) c hp
    cases sw
    · simpa only [Bool.false_eq_true, ↓reduceIte, around_position, hk] using
        closed_of_code q (endpoint h) c (position h) (position k) hv hh.2
    · simpa only [↓reduceIte, around_position, hk] using
        closed_of_bar_code q (endpoint h) c (position h) (position k) hv hh.2

def linkCheck (p : Partial) (h k : H) : Bool :=
  decide (h = k) || directCheck p h k || directCheck p (barH h) (barH k)

lemma linkCheck_sound {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (h k : H) (ht : linkCheck p h k = true) : closed q h k := by
  simp only [linkCheck, Bool.or_eq_true, decide_eq_true_eq] at ht
  rcases ht with (rfl | hd) | hb
  · exact Relation.ReflTransGen.refl
  · exact directCheck_sound ha h k false hd
  · simpa only [↓reduceIte, barH_barH] using directCheck_sound ha (barH h) (barH k) true hb

def half (n : ℕ) : H := (⟨(n / 2) % 15, by omega⟩, decide (n % 2 = 1))
def vertex (n : ℕ) : V := ⟨n % 10, by omega⟩
def localIndex (n : ℕ) : Fin 3 := ⟨n % 3, by omega⟩

def pathCheck (p : Partial) (h : H) (bits : ℕ) : ℕ → H → Bool
  | 0, k => decide (h = k)
  | n + 1, k => linkCheck p h (half (bits % 32)) &&
      pathCheck p (half (bits % 32)) (bits / 32) n k

lemma pathCheck_sound {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (n : ℕ) (h k : H) (bits : ℕ) (ht : pathCheck p h bits n k = true) :
    closed q h k := by
  induction n generalizing h bits with
  | zero =>
    have he : h = k := by simpa only [pathCheck, decide_eq_true_eq] using ht
    subst h
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    simp only [pathCheck, Bool.and_eq_true] at ht
    exact (linkCheck_sound ha _ _ ht.1).trans (ih _ _ ht.2)

def reaches (p : Partial) (h k : H) (bits : ℕ) : Bool := pathCheck p h bits 8 k

lemma reaches_sound {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (h k : H) (bits : ℕ) (ht : reaches p h k bits = true) : closed q h k :=
  pathCheck_sound ha 8 h k bits ht

def rowBits : Fin 15 → ℕ := ![50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]
def row (r : Fin 15) : Finset V := Finset.univ.filter fun v => (rowBits r).testBit v.val

lemma row_independent : ∀ r, independent (row r) := by
  unfold independent
  decide +kernel

lemma mem_row (r : Fin 15) (v : V) : v ∈ row r ↔ (rowBits r).testBit v.val = true := by
  simp [row]

def oppositeCheck (p : Partial) (bits : ℕ) : Bool :=
  let h := half (bits % 32)
  let k := half ((bits / 32) % 32)
  decide (endpoint k = endpoint h) && reaches p k (barH h) (bits / 1024)

lemma oppositeCheck_false {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (hq : CodeConditions q) (bits : ℕ) (ht : oppositeCheck p bits = true) : False := by
  simp only [oppositeCheck, Bool.and_eq_true, decide_eq_true_eq] at ht
  exact reject_opposite hq _ _ ht.1 (reaches_sound ha _ _ _ ht.2)

def localCheck (p : Partial) (bits : ℕ) : Bool :=
  let v := vertex (bits % 16)
  let i := localIndex ((bits / 16) % 4)
  let j := localIndex ((bits / 64) % 4)
  match p v with
  | none => false
  | some c => decide (block c i ≠ block c j) &&
      reaches p (around v i) (around v j) (bits / 256)

lemma localCheck_false {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (hq : CodeConditions q) (bits : ℕ) (ht : localCheck p bits = true) : False := by
  unfold localCheck at ht
  dsimp only at ht
  cases hp : p (vertex (bits % 16)) with
  | none => simp only [hp, Bool.false_eq_true] at ht
  | some c =>
    rw [hp] at ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    exact reject_local_of_code hq _ c _ _ (ha _ _ hp) (reaches_sound ha _ _ _ ht.2) ht.1

def exposureStart (bits : ℕ) (i : Fin 3) : H :=
  half ((bits / (2 ^ (8 + i.val * 45))) % 32)
def exposurePath (bits : ℕ) (i : Fin 3) : ℕ := bits / (2 ^ (13 + i.val * 45))

def exposureCheck (p : Partial) (bits : ℕ) : Bool :=
  let v := vertex (bits % 16)
  let r : Fin 15 := ⟨((bits / 16) % 16) % 15, by omega⟩
  match p v with
  | none => false
  | some c => decide (c ≠ 3) && (decide (∃ h : H, endpoint h = v ∧ (rowBits r).testBit (endpoint (barH h)).val = true) &&
      decide (∀ i : Fin 3,
        (rowBits r).testBit (endpoint (exposureStart bits i)).val = true ∧
        reaches p (exposureStart bits i) (around v i) (exposurePath bits i) = true))

lemma exposureCheck_false {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (hq : CodeConditions q) (bits : ℕ) (ht : exposureCheck p bits = true) : False := by
  unfold exposureCheck at ht
  dsimp only at ht
  cases hp : p (vertex (bits % 16)) with
  | none => simp only [hp, Bool.false_eq_true] at ht
  | some c =>
    rw [hp] at ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    have htouch : touches (vertex (bits % 16)) (row ⟨((bits / 16) % 16) % 15, by omega⟩) := by
      obtain ⟨h, hv, hh⟩ := ht.2.1
      exact ⟨h, hv, (mem_row _ _).mpr hh⟩
    apply reject_exposure hq (vertex (bits % 16)) _ (row_independent _) htouch
    · rw [ha _ _ hp]
      exact ht.1
    · intro i
      exact ⟨exposureStart bits i, reaches_sound ha _ _ _ (ht.2.2 i).2,
        (mem_row _ _).mpr (ht.2.2 i).1⟩

def rejects (p : Partial) (n : ℕ) : Bool :=
  if n % 8 = 1 then oppositeCheck p (n / 8)
  else if n % 8 = 2 then localCheck p (n / 8)
  else if n % 8 = 3 then exposureCheck p (n / 8)
  else false

lemma rejects_false {q : V → Fin 4} {p : Partial} (ha : Agrees q p)
    (hq : CodeConditions q) (n : ℕ) (ht : rejects p n = true) : False := by
  unfold rejects at ht
  split at ht
  · exact oppositeCheck_false ha hq _ ht
  · split at ht
    · exact localCheck_false ha hq _ ht
    · split at ht
      · exact exposureCheck_false ha hq _ ht
      · cases ht

def good (codes : Fin 45 → V → Fin 4) (p : Partial) (n : ℕ) : Bool :=
  decide (∀ v, p v = some (codes ⟨n % 45, by omega⟩ v))

lemma good_sound (codes : Fin 45 → V → Fin 4) {q : V → Fin 4} {p : Partial}
    (ha : Agrees q p) (n : ℕ) (ht : good codes p n = true) :
    ∃ i, q = codes i := by
  refine ⟨⟨n % 45, by omega⟩, ?_⟩
  apply funext
  intro v
  exact ha v _ ((decide_eq_true_eq.mp ht) v)

def scanFour (f : Fin 4 → List ℕ → Option (List ℕ)) (ns : List ℕ) : Option (List ℕ) :=
  (f 0 ns).bind fun ns0 => (f 1 ns0).bind fun ns1 => (f 2 ns1).bind fun ns2 => f 3 ns2

lemma bind_some_exists {α β : Type} {a : Option α} {f : α → Option β} {b : β}
    (h : a.bind f = some b) : ∃ x, a = some x ∧ f x = some b := by
  cases a with
  | none => cases h
  | some x => exact ⟨x, rfl, h⟩

lemma scanFour_success (f : Fin 4 → List ℕ → Option (List ℕ))
    (ns rest : List ℕ) (ht : scanFour f ns = some rest) (c : Fin 4) :
    ∃ a b, f c a = some b := by
  obtain ⟨ns0, h0, hrest0⟩ := bind_some_exists ht
  obtain ⟨ns1, h1, hrest1⟩ := bind_some_exists hrest0
  obtain ⟨ns2, h2, h3⟩ := bind_some_exists hrest1
  fin_cases c
  · exact ⟨_, _, h0⟩
  · exact ⟨_, _, h1⟩
  · exact ⟨_, _, h2⟩
  · exact ⟨_, _, h3⟩

def check (codes : Fin 45 → V → Fin 4) :
    List V → Partial → List ℕ → Option (List ℕ)
  | _, _, [] => none
  | todo, p, n :: ns =>
    if n % 8 = 0 then
      match todo with
      | [] => none
      | v :: vs => scanFour (fun c => check codes vs (Function.update p v (some c))) ns
    else if n % 8 = 4 then
      if good codes p (n / 8) then some ns else none
    else if rejects p n then some ns else none

lemma check_sound (codes : Fin 45 → V → Fin 4) (todo : List V) (p : Partial)
    (ns rest : List ℕ) (q : V → Fin 4) (ht : check codes todo p ns = some rest)
    (ha : Agrees q p) (hq : CodeConditions q) : ∃ i, q = codes i := by
  induction todo generalizing p ns rest with
  | nil =>
    cases ns with
    | nil => cases ht
    | cons n ns =>
      by_cases h0 : n % 8 = 0
      · simp only [check, if_pos h0] at ht
        cases ht
      · by_cases h4 : n % 8 = 4
        · simp only [check, if_neg h0, if_pos h4] at ht
          by_cases hg : good codes p (n / 8) = true
          · exact good_sound codes ha _ hg
          · simp only [if_neg hg] at ht
            cases ht
        · simp only [check, if_neg h0, if_neg h4] at ht
          by_cases hr : rejects p n = true
          · exact (rejects_false ha hq _ hr).elim
          · simp only [if_neg hr] at ht
            cases ht
  | cons v vs ih =>
    cases ns with
    | nil => cases ht
    | cons n ns =>
      by_cases h0 : n % 8 = 0
      · simp only [check, if_pos h0] at ht
        obtain ⟨a, b, hab⟩ := scanFour_success _ _ _ ht (q v)
        exact ih _ _ _ hab (agrees_update ha v (q v) rfl)
      · by_cases h4 : n % 8 = 4
        · simp only [check, if_neg h0, if_pos h4] at ht
          by_cases hg : good codes p (n / 8) = true
          · exact good_sound codes ha _ hg
          · simp only [if_neg hg] at ht
            cases ht
        · simp only [check, if_neg h0, if_neg h4] at ht
          by_cases hr : rejects p n = true
          · exact (rejects_false ha hq _ hr).elim
          · simp only [if_neg hr] at ht
            cases ht

end SlotTree


namespace SlotTree

open FiniteSlots

abbrev code : Fin 45 → V → Fin 4 := SlotTables.code

def order : List V := [6,4,0,1,9,3,2,8,5,7]

def c0 : Nat := 40285217132025004452164840870658545442554899
def c1 : Nat := 34530186113891079769029748219665682433997835
def c2 : Nat := 4648876938730377
def c3 : Nat := 4067767319680633
def c4 : Nat := 34530186112958088927261770659588168495487243
def c5 : Nat := 34530186113024006758473638588465997062166795
def c6 : Nat := 4067767312922233
def c7 : Nat := 581109719901209
def c8 : Nat := 1162219249280553
def c9 : Nat := 46040248151837298530002109249233043495906715
def c10 : Nat := 40285217131900774693342474389311868528428051
def c11 : Nat := 46040248151829692626400739152248122896697499
def c12 : Nat := 51795279170797731404486006749425816615176483
def c13 : Nat := 4067767309391225
def c14 : Nat := 4067767322383737
def c15 : Nat := 2905548137307481
def c16 : Nat := 290554824149249
def c17 : Nat := 1743328977971257
def c18 : Nat := 5229986571581593
def c19 : Nat := 28775155094923777046131687776702302567537539
def c20 : Nat := 34530186112950483023660402003755128655528715
def c21 : Nat := 46040248150975296121846912535639344936221723
def c22 : Nat := 74815403246690904981617960455383509931728307
def c23 : Nat := 3486657682757993
def c24 : Nat := 77111817
def c25 : Nat := 28775155094906029937728513533841213760383491
def c26 : Nat := 51795279170790125500884636652440896015960611
def c27 : Nat := 51795279170790125500884636652440896016658979
def c28 : Nat := 51795279170790125500884661224080462949354531
def c29 : Nat := 581109622563865
def c30 : Nat := 28775155094923777046131712636572245652675459
def c31 : Nat := 80570434264713276411932965248756244158691395
def c32 : Nat := 80570434265537249302081314359729101242185795
def c33 : Nat := 83447949775113152913663093301513426284775979
def c34 : Nat := 2905548063726937
def c35 : Nat := 46040248151837298530002105718410935636660251
def c36 : Nat := 51795279169852064056715747615909276023203235
def c37 : Nat := 51795279170797731404486006749425816614492451
def c38 : Nat := 5811096214722217
def c39 : Nat := 1162219347666473
def c40 : Nat := 51795279170790125500884635499519391409081379
def c41 : Nat := 74815403246581887029998329628378249825164211
def c42 : Nat := 83447949775113152913663050715475349869365803
def c43 : Nat := 4648876951673737
def c44 : Nat := 5811096370493097
def c45 : Nat := 46040248150909378290635044606761516369542171
def c46 : Nat := 3486657693014377
def c47 : Nat := 89514505
def c48 : Nat := 51795279170797731404486030816662225282343075
def c49 : Nat := 1162220099579945
def c50 : Nat := 3486657683634793
def c51 : Nat := 2926412297
def c52 : Nat := 46040248151829692626400763435657313678359323
def c53 : Nat := 46040248151000649133851477844245219379582619
def c54 : Nat := 80570434265613308338094984488928058994139331
def c55 : Nat := 40285217131999651440160275562052670999194387
def c56 : Nat := 74815403246657946066012023680698428170023475
def c57 : Nat := 74815403246690904981617957356906966301642803
def c58 : Nat := 34530186113049359770478203897071871505548043
def c59 : Nat := 34530186113891079769029748219665682434677771
def c60 : Nat := 46040248150876419375029111362898542465455771
def c61 : Nat := 83447949775138505925667658610119300728177451
def c62 : Nat := 34530186153188248376130350184069586883795339
def c63 : Nat := 69060372227677230781924475537483532468433483
def c64 : Nat := 1162219252830249
def c65 : Nat := 28775155094906029937728516920548133542324995
def c66 : Nat := 69060372227715260299931310674140605382347851
def c67 : Nat := 74815403245562695947414833477805276599747635
def c68 : Nat := 74815403246592028234800155751820599602512947
def c69 : Nat := 28775155094074451143978795046459376456984835
def c70 : Nat := 28775155094786870781307059970100523658406147
def c71 : Nat := 34530186113891079769029745409419514954728331
def c72 : Nat := 34530186113891079769029772142786903025992587
def c73 : Nat := 40285216283393774828176441731842948339034387
def c74 : Nat := 40285217132843906739912276343449475334027283
def c75 : Nat := 74815403245570301851016202565983880667274163
def c76 : Nat := 1743329644982841
def c77 : Nat := 1743332530202681
def c78 : Nat := 1961020394512962
def c79 : Nat := 5229983705274265
def c80 : Nat := 5229986575653017
def c81 : Nat := 290554826893825
def c82 : Nat := 40285217131933733608948407633174842432514835
def c83 : Nat := 40285217132851512643513642909612288073991443
def c84 : Nat := 46040247301558123125716988830041640087681819
def c85 : Nat := 83447949775138505925667615807908442198983467
def c86 : Nat := 1743328882119225
def c87 : Nat := 290555046750738
def c88 : Nat := 435833132552730
def c89 : Nat := 28775155142161509013036450099584039073686915
def c90 : Nat := 34530186113883473865428378122680761835465995
def c91 : Nat := 3486657690344041
def c92 : Nat := 4648876942212233
def c93 : Nat := 28775155094049098131974231395178164885921155
def c94 : Nat := 28775155094819829696912994871288160434789763
def c95 : Nat := 28775155094906029937728516920548133571244547
def c96 : Nat := 28775155094923777046131709682210890098337411
def c97 : Nat := 34530186113883473865428402550205140692983179
def c98 : Nat := 34530186145559527063931375127856322698228363
def c99 : Nat := 40284279733468293337354821317351610650412179
def c100 : Nat := 40285217131933733608948638505706139953621267
def c101 : Nat := 46040247200384393420301336744261498848763291
def c102 : Nat := 46040248151000649133851477844245219373047195
def c103 : Nat := 46040248185110591484817993744765992120450203
def c104 : Nat := 51795279169950940803533549509226018873222563
def c105 : Nat := 51795279170797731404486003939179649135222947
def c106 : Nat := 69060372227677230781924463575922922172396107
def c107 : Nat := 83447949775138505925645470203417577723994283
def c108 : Nat := 1162219346964521
def c109 : Nat := 1743331745220665
def c110 : Nat := 3486661939222889
def c111 : Nat := 290555205863681
def c112 : Nat := 290556841994753
def c113 : Nat := 290557664323841
def c114 : Nat := 3705266697
def c115 : Nat := 843541513
def c116 : Nat := 69060372227715260299931323500392344133520459
def c117 : Nat := 1162222083900969
def c118 : Nat := 28775155094819829696912994871288160463809923
def c119 : Nat := 28775155094906029937728513533841213760287235
def c120 : Nat := 28775155142161509013040230601255238231943555
def c121 : Nat := 34530185190136340274315788137397102847373963
def c122 : Nat := 34530186113883473865428378122680761836160267
def c123 : Nat := 46040248151829692626400737278750677910518555
def c124 : Nat := 46040248151829692626400739152248122897387675
def c125 : Nat := 51795279169885022972321680859772249927290531
def c126 : Nat := 83447949775113152913663073053329501628237099
def c127 : Nat := 1162222951278121
def c128 : Nat := 1525412012632634
def c129 : Nat := 1525413258727994
def c130 : Nat := 1743328878536761
def c131 : Nat := 1743329730941497
def c132 : Nat := 2905548061004889
def c133 : Nat := 3486654819424617
def c134 : Nat := 91450377
def c135 : Nat := 28775155123828746032535796495138717302730243
def c136 : Nat := 28775155124447359525450449478330764637510019
def c137 : Nat := 40285217131933733608949423212905212988844691
def c138 : Nat := 40285217132025004452164840870658545465013267
def c139 : Nat := 40285217132843906739912300338628289963976979
def c140 : Nat := 83447949775138505925667658610119300721615019
def c141 : Nat := 3486661091768937
def c142 : Nat := 4648879796173961
def c143 : Nat := 145284155335178
def c144 : Nat := 928975881
def c145 : Nat := 28774285300896136944925761770190280016512515
def c146 : Nat := 28775095158152050790232613418359330829265283
def c147 : Nat := 28775155094049098131974026679553503132653955
def c148 : Nat := 28775155094906029937729287504458775150234755
def c149 : Nat := 34530185291700506364602533349037762930629003
def c150 : Nat := 34530186113883473865428376249183316849286539
def c151 : Nat := 34530186113891079769029979092196980030873355
def c152 : Nat := 46040248150909378290635252420862721753709339
def c153 : Nat := 46040248151837298530002133028239076011347995
def c154 : Nat := 51795279170790125500881969656770364220598947
def c155 : Nat := 69060372194654932645980596048549799617835339
def c156 : Nat := 69060372227715260299920788680143999047048139
def c157 : Nat := 74815402097755783464762239598600392232481331
def c158 : Nat := 74815403246592028234800155751820599574999603
def c159 : Nat := 80570434265641196651299789146806090538877635
def c160 : Nat := 83447949775138505925667636992841089351012523
def c161 : Nat := 1162220187111465
def c162 : Nat := 1743328699369529
def c163 : Nat := 1743332523993145
def c164 : Nat := 4648874074938249
def c165 : Nat := 4648880559823753
def c166 : Nat := 290554913122561
def c167 : Nat := 581109623459353
def c168 : Nat := 28775155124447359525447150537560520220744067
def c169 : Nat := 40285217131900774693342728392330852224402067
def c170 : Nat := 46040248151837298530002109249233043495230875
def c171 : Nat := 80570434264705670508331596737038392394589635
def c172 : Nat := 80570434265567672916486792730056150574245315
def c173 : Nat := 80570434265641196651300029170651830905692739
def c174 : Nat := 1452793099586090
def c175 : Nat := 2106521481776170
def c176 : Nat := 2905548140770393
def c177 : Nat := 5229986568066969
def c178 : Nat := 581109719166489
def c179 : Nat := 28775155094049098131974026895726285246437763
def c180 : Nat := 28775155094074451143979565774485206134188419
def c181 : Nat := 28775155094074451143979566206830770361755907
def c182 : Nat := 28775155094786870781307059970100523665629443
def c183 : Nat := 28775155094923777046131478809679592577229955
def c184 : Nat := 28775155143023511421191645155853074760975875
def c185 : Nat := 34530185190136340274315787416821162468094603
def c186 : Nat := 34530186113049359770478203897071871528370827
def c187 : Nat := 34530186113883473865429382821714432762439435
def c188 : Nat := 40285217131933733608948662356769766507768467
def c189 : Nat := 40285217132025004452164840870658545465005203
def c190 : Nat := 40285217132025004452164840870658568515962003
def c191 : Nat := 40285217148146984785867462398893617582916755
def c192 : Nat := 46040248150909378290636046639664207795420187
def c193 : Nat := 51795278255054543703214456484616401292322339
def c194 : Nat := 51795279169925587791528984200620144429862563
def c195 : Nat := 74815403246657946066011994425315248770450739
def c196 : Nat := 74815403246690904981617928605926945167580595
def c197 : Nat := 74815403246690904981617957356906966301730867
def c198 : Nat := 80570433287407904961177683194352062775362883
def c199 : Nat := 80570434171419262837535954192359134717878467
def c200 : Nat := 80570434264705670508331355848501523601498307
def c201 : Nat := 80570434265567672916486792730056150546056515
def c202 : Nat := 1452793813680682
def c203 : Nat := 1743328977302073
def c204 : Nat := 1961243936569922
def c205 : Nat := 2106522195870762
def c206 : Nat := 2899346682420569
def c207 : Nat := 5229986578339737
def c208 : Nat := 290554913982977
def c209 : Nat := 3712000521
def c210 : Nat := 28775155094786870781307059970100523665636867
def c211 : Nat := 28775155123828746032535796495138716587236867
def c212 : Nat := 34530186113883473865429382821714432665372427
def c213 : Nat := 34530186113891079769029772142786903048240907
def c214 : Nat := 46040248151829692626401738374904646844076443
def c215 : Nat := 51795279180880624278701343408930594680149539
def c216 : Nat := 80570434216593259627270421066306217944627651
def c217 : Nat := 83447949775138505925667658610119300722373291
def c218 : Nat := 1598051181466682
def c219 : Nat := 1598051689966650
def c220 : Nat := 2033882434315330
def c221 : Nat := 3486661054437993
def c222 : Nat := 726388258905090
def c223 : Nat := 28775154273212375568589759961623925150615043
def c224 : Nat := 28775155001944140820591334825606041636444547
def c225 : Nat := 28775155094074451144771137900542234751691139
def c226 : Nat := 28775155094786870781307059970100530406737411
def c227 : Nat := 28775155094819829696912994871288160463783427
def c228 : Nat := 28775155094906029937728516920548133548887171
def c229 : Nat := 28775155094906029937729287504458775144344707
def c230 : Nat := 28775155094923777046131712636572245681616003
def c231 : Nat := 28775155094923777046132482716079728989234051
def c232 : Nat := 34530186113024006758473638588465997077983883
def c233 : Nat := 34530186113883473865428402550205140708042123
def c234 : Nat := 34530186145904328027193450714817257703293323
def c235 : Nat := 34530186153188248376104857071990096435173771
def c236 : Nat := 34530186154116168615471922867383128167688843
def c237 : Nat := 40285216182349345483984045266009438311605395
def c238 : Nat := 40285216217290866628674961209440505872094355
def c239 : Nat := 40285216284240565429128923039279154748129939
def c240 : Nat := 40285217132843906739913289833509618791130643
def c241 : Nat := 40285217132851512643513669931210052319505939
def c242 : Nat := 46040247201309778358467943486778151810156315
def c243 : Nat := 46040247329464183439142024012527639923621019
def c244 : Nat := 46040248150975296121846912535639344930413595
def c245 : Nat := 46040248151837298530002316342758308575209883
def c246 : Nat := 46040248177481870172619190041511350122645275
def c247 : Nat := 46040248185896534856934176088070524837973787
def c248 : Nat := 51795279170797731404486030816662225304726179
def c249 : Nat := 63305341208721868509841473512310111948705851
def c250 : Nat := 63305341208721868509841489220865612217488315
def c251 : Nat := 63305341208721868509841490806132681051410491
def c252 : Nat := 63305341208739615618244683135449873379578043
def c253 : Nat := 63305341208739615618244683135449873379674299
def c254 : Nat := 63305341208739615618244686522156793161787707
def c255 : Nat := 69060372194654932645979087666933803672351051
def c256 : Nat := 69060372227263976686250070590867786085648587
def c257 : Nat := 69060372227677230781924473808101275558502475
def c258 : Nat := 69060372227715260299920578776372566557005003
def c259 : Nat := 69060372227715260299931323500392344105352267
def c260 : Nat := 69060372227715260299931323500392344111291339
def c261 : Nat := 74815402105141115861691904091720185112968371
def c262 : Nat := 74815403218990204065430659508248204609913907
def c263 : Nat := 74815403246592028234800155751820599580986419
def c264 : Nat := 74815403246690904981587740725423101572625971
def c265 : Nat := 80570434265641196651300029170651830905776707
def c266 : Nat := 80570434265641196651300032125013186460072771
def c267 : Nat := 1162219071604265
def c268 : Nat := 1525387728892474
def c269 : Nat := 1525414694556218
def c270 : Nat := 1525415203056186
def c271 : Nat := 1525427511407162
def c272 : Nat := 1598041874017338
def c273 : Nat := 1598057272224826
def c274 : Nat := 3486661843245417
def c275 : Nat := 3970842583258745
def c276 : Nat := 3977830113949305
def c277 : Nat := 4648876948937865
def c278 : Nat := 28775155094049098131738584111526908560153475
def c279 : Nat := 34530186113891079769029772142786903048221579
def c280 : Nat := 40285216310975316587943040964173755299621523
def c281 : Nat := 40285217131933733608949422420271678571637395
def c282 : Nat := 40285217132851512643514659209918599010368787
def c283 : Nat := 46040248150876419375030112675225293512053915
def c284 : Nat := 46040248151000649133851477844245219401619227
def c285 : Nat := 46040248151829692626398071436001650722036123
def c286 : Nat := 46040248151837298530003109480695884070543387
def c287 : Nat := 69060372194720850477192465850925073170647755
def c288 : Nat := 74815403246592028234800155751820599580966067
def c289 : Nat := 74815403246657946066012025554195873155319091
def c290 : Nat := 80570434265567672916486792730056150552698307
def c291 : Nat := 80570434265641196651300032125013186439197251
def c292 : Nat := 83447949775138505925667658610119300706630315
def c293 : Nat := 1162240498152474
def c294 : Nat := 1888605581149234
def c295 : Nat := 2815610797383001
def c296 : Nat := 3967117014283897
def c297 : Nat := 3980742130554489
def c298 : Nat := 28774313642026812873498420143046895667719683
def c299 : Nat := 28775058989071023752877985006948543014902147
def c300 : Nat := 28775155094074451144771164489794434747099907
def c301 : Nat := 28775155094786870781307059970100530406795779
def c302 : Nat := 28775155094819829696912994871288190077363843
def c303 : Nat := 28775155094906029915527376633152324956118147
def c304 : Nat := 28775155094906029937728516920548140974136451
def c305 : Nat := 28775155094906029938517506934781067900783747
def c306 : Nat := 28775155094923777046131709682210890098253443
def c307 : Nat := 34529248372612352376515627677710068760130187
def c308 : Nat := 34530185198801999777475964326028565966324363
def c309 : Nat := 34530186112950483023660656439119676579070347
def c310 : Nat := 34530186112950483023660656655292458692854155
def c311 : Nat := 34530186113024006758473638588466012532491531
def c312 : Nat := 34530186113049359770478203897071871521370763
def c313 : Nat := 34530186113049359770478203897071894302765707
def c314 : Nat := 34530186113883473863503173805537697503504139
def c315 : Nat := 34530186113883473865426472055203270580735755
def c316 : Nat := 34530186113883473865428402550205140708069131
def c317 : Nat := 34530186145559527063931374407280381531400459
def c318 : Nat := 34530186145559527063931375127856321910700683
def c319 : Nat := 34530186145919539834396189467635218141757835
def c320 : Nat := 34530227344112763664300793289103049280805259
def c321 : Nat := 40285217131900774693342728608503634338185875
def c322 : Nat := 40285217132843906739913289833509618784509459
def c323 : Nat := 40285217132851512643513876592389753096826387
def c324 : Nat := 40285217149652953698963449646500342537585299
def c325 : Nat := 40285217156587002482212061550207002803923603
def c326 : Nat := 40285217157038286095868262700415553493326995
def c327 : Nat := 40285217157038286095893324043391567896183827
def c328 : Nat := 46039406012733176141646659226458406191987867
def c329 : Nat := 46040247200376787516700968680179269676123035
def c330 : Nat := 46040248150909378290636045558800297226501275
def c331 : Nat := 46040248151837298530002133028239076033481115
def c332 : Nat := 51794341574086949064400080071760223411312163
def c333 : Nat := 51795278295414003513280318036927915516962595
def c334 : Nat := 51795279169885022972321175447807667900746787
def c335 : Nat := 51795279169885022972577834221477225747156003
def c336 : Nat := 51795279169950940803533549509226018895521315
def c337 : Nat := 51795279170790125500884908237512824967049891
def c338 : Nat := 51795279188509345590899705110903408040578851
def c339 : Nat := 51795279189629948721476582017484899054259747
def c340 : Nat := 69060372194720850477190955811984414352820939
def c341 : Nat := 69060372227715260299931323500392344105325771
def c342 : Nat := 74815403141240122151031907341187667213485875
def c343 : Nat := 74815403218990204065432339242822822748030003
def c344 : Nat := 74815403219056121896644209045198096300842803
def c345 : Nat := 74815403245562695947414275103509076696171571
def c346 : Nat := 74815403246657946066012023680698428170076723
def c347 : Nat := 74815403246690904981587950629194534062667827
def c348 : Nat := 74815409928510177700221037643315672874026035
def c349 : Nat := 80570434264705670508330428827554225658601923
def c350 : Nat := 80570434264705670508330429043727007772385731
def c351 : Nat := 83447949765993674495621190738962218761004843
def c352 : Nat := 83447949775113152913663093301513426278986283

set_option maxRecDepth 32000 in
set_option maxHeartbeats 8000000 in
def treeData : List ℕ := [
  0,
  0,
  0,
  0,
  0,
  c26,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  c315,
  c29,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  c315,
  c29,
  c26,
  0,
  c26,
  c76,
  0,
  0,
  c24,
  c20,
  0,
  c11,
  c245,
  c264,
  c11,
  c24,
  0,
  c122,
  c20,
  c152,
  c20,
  0,
  c122,
  c20,
  c84,
  c20,
  0,
  c24,
  c20,
  0,
  c294,
  0,
  c119,
  290556748466689,
  c14,
  290556748466689,
  c264,
  c294,
  c24,
  c76,
  0,
  c26,
  0,
  c233,
  0,
  c242,
  c58,
  c189,
  c58,
  c316,
  c233,
  0,
  c233,
  0,
  c242,
  c6,
  c138,
  c6,
  c316,
  c233,
  c26,
  0,
  c26,
  c76,
  0,
  c29,
  0,
  c8,
  c6,
  c0,
  c8,
  0,
  c8,
  c6,
  c84,
  c8,
  c29,
  c76,
  0,
  c150,
  c69,
  c97,
  c69,
  0,
  0,
  0,
  0,
  c16,
  0,
  c11,
  0,
  0,
  c111,
  c210,
  c131,
  c111,
  c49,
  0,
  c182,
  c210,
  c247,
  c182,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  0,
  c11,
  0,
  0,
  180,
  c86,
  c131,
  c86,
  c49,
  0,
  c108,
  c86,
  c247,
  c108,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  c16,
  0,
  c90,
  c10,
  c0,
  c90,
  c40,
  c40,
  c37,
  0,
  0,
  c16,
  0,
  c11,
  0,
  0,
  c111,
  c144,
  c136,
  c111,
  c49,
  0,
  c182,
  c144,
  34530218951327728683122963588519954038815371,
  c144,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  0,
  c11,
  0,
  0,
  c252,
  c128,
  c128,
  c136,
  c49,
  0,
  c108,
  c299,
  46040283062851163875824760733867151773236379,
  c108,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  c16,
  0,
  c90,
  c10,
  c0,
  c90,
  0,
  c90,
  0,
  c224,
  c15,
  0,
  c85,
  4648874290158473,
  c61,
  4648874290158473,
  c15,
  c21,
  c90,
  0,
  c16,
  c10,
  c0,
  c16,
  c37,
  c70,
  0,
  0,
  0,
  c154,
  c100,
  c73,
  c154,
  0,
  c242,
  0,
  c124,
  0,
  0,
  c191,
  5229987708377241,
  c131,
  c131,
  c127,
  c137,
  c127,
  c196,
  c124,
  c45,
  c45,
  c40,
  c40,
  c37,
  0,
  0,
  0,
  c11,
  c35,
  c347,
  c35,
  c6,
  c73,
  c6,
  0,
  c242,
  c6,
  c138,
  c6,
  0,
  46040248150975296121846912535639344930408219,
  c6,
  c21,
  c6,
  0,
  0,
  c91,
  c15,
  c347,
  c15,
  c6,
  c73,
  c6,
  c37,
  c70,
  0,
  c150,
  0,
  c26,
  c76,
  0,
  0,
  c24,
  c20,
  0,
  c11,
  c245,
  c264,
  c11,
  c24,
  0,
  c4,
  c20,
  c152,
  c4,
  0,
  c4,
  c20,
  c84,
  c4,
  0,
  c24,
  c20,
  0,
  c294,
  c15,
  c264,
  c15,
  c24,
  c76,
  c97,
  0,
  c26,
  c76,
  0,
  c29,
  0,
  c8,
  c6,
  c0,
  c8,
  0,
  c8,
  c6,
  c84,
  c8,
  c29,
  c76,
  0,
  0,
  0,
  c27,
  0,
  0,
  c130,
  c318,
  34530218580725005103999182333106617655051019,
  c130,
  0,
  c317,
  c318,
  c0,
  c317,
  c125,
  c125,
  c63,
  c27,
  0,
  c27,
  c77,
  c63,
  c77,
  0,
  c27,
  0,
  0,
  0,
  0,
  0,
  c74,
  76,
  c257,
  c74,
  0,
  c74,
  68,
  c257,
  c74,
  0,
  c74,
  60,
  c257,
  c74,
  0,
  c74,
  84,
  c257,
  c74,
  c35,
  c57,
  c35,
  c87,
  c87,
  c58,
  0,
  c88,
  c58,
  c189,
  c88,
  c125,
  c125,
  c63,
  c27,
  0,
  c27,
  c77,
  c63,
  c77,
  0,
  c150,
  0,
  c255,
  0,
  0,
  c143,
  c98,
  0,
  46040248151829692627425924015788847018367387,
  c286,
  c57,
  c286,
  c143,
  0,
  c4,
  c98,
  c330,
  c4,
  0,
  c4,
  c98,
  c243,
  c4,
  0,
  c143,
  c98,
  0,
  c221,
  0,
  3977919630235001,
  0,
  2905553035711577,
  c177,
  c126,
  2905553035711577,
  c14,
  c14,
  c57,
  c221,
  c143,
  c155,
  0,
  0,
  c143,
  c98,
  c3,
  c3,
  0,
  c4,
  c98,
  c330,
  c4,
  0,
  c4,
  c98,
  c243,
  c4,
  0,
  c143,
  c98,
  c3,
  c3,
  c97,
  0,
  c255,
  0,
  0,
  0,
  c285,
  c35,
  c57,
  c35,
  c87,
  c87,
  0,
  c285,
  c35,
  c57,
  c35,
  0,
  c88,
  c10,
  c0,
  c88,
  0,
  c88,
  0,
  c221,
  0,
  c13,
  0,
  c132,
  5229988497184665,
  c126,
  c132,
  3970831009420665,
  c13,
  c57,
  c221,
  c243,
  c88,
  0,
  0,
  c91,
  0,
  c175,
  0,
  c74,
  c83,
  c126,
  c74,
  c174,
  0,
  c167,
  c83,
  1670689995108938,
  c167,
  c57,
  c91,
  c87,
  c87,
  0,
  c91,
  0,
  c13,
  0,
  c132,
  c177,
  c126,
  c132,
  c14,
  c13,
  c57,
  c91,
  c155,
  0,
  0,
  0,
  c285,
  c35,
  c57,
  c35,
  c6,
  c3,
  c3,
  0,
  c88,
  c6,
  c0,
  c6,
  0,
  c88,
  c6,
  c243,
  c6,
  0,
  0,
  c91,
  0,
  c175,
  0,
  c74,
  c178,
  1452774282496554,
  c178,
  c174,
  0,
  c167,
  c178,
  44,
  c167,
  c57,
  c91,
  c6,
  c3,
  c3,
  0,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c150,
  0,
  c27,
  c77,
  c155,
  c77,
  c97,
  0,
  c27,
  c77,
  c155,
  c77,
  0,
  0,
  0,
  0,
  0,
  c130,
  0,
  0,
  0,
  c81,
  308,
  c112,
  c81,
  c19,
  0,
  c218,
  c250,
  c269,
  c187,
  c19,
  0,
  0,
  c81,
  316,
  c112,
  c81,
  c19,
  0,
  c218,
  c250,
  c269,
  c187,
  c19,
  0,
  0,
  c81,
  300,
  c112,
  c81,
  c19,
  0,
  c218,
  c250,
  c269,
  c187,
  c19,
  0,
  0,
  c81,
  324,
  c112,
  c81,
  c19,
  0,
  c218,
  c250,
  c269,
  c187,
  c19,
  0,
  c123,
  0,
  0,
  c211,
  c162,
  c112,
  c112,
  c19,
  0,
  c108,
  c162,
  c314,
  c108,
  c19,
  0,
  0,
  c211,
  c162,
  c112,
  c112,
  c19,
  0,
  c324,
  c162,
  c314,
  c162,
  c19,
  c123,
  c130,
  0,
  c90,
  c10,
  c0,
  c90,
  c28,
  c28,
  80677897,
  0,
  0,
  c130,
  0,
  c56,
  0,
  0,
  c81,
  c144,
  c168,
  c81,
  c19,
  0,
  c187,
  c144,
  c319,
  c144,
  c19,
  0,
  0,
  c81,
  c144,
  c168,
  c81,
  c19,
  0,
  c187,
  c144,
  c141,
  c144,
  c19,
  c56,
  0,
  c123,
  0,
  0,
  c211,
  c234,
  c168,
  c168,
  c19,
  0,
  c108,
  c234,
  c319,
  c108,
  c19,
  0,
  0,
  c211,
  c234,
  c168,
  c168,
  c19,
  0,
  c324,
  c234,
  c141,
  c141,
  c19,
  c123,
  c130,
  0,
  c90,
  c10,
  c0,
  c90,
  c194,
  c194,
  80677897,
  c80,
  0,
  0,
  0,
  c232,
  c312,
  c55,
  c232,
  0,
  c232,
  c312,
  0,
  0,
  0,
  c211,
  c305,
  c112,
  c112,
  c306,
  0,
  c92,
  34530186113883473865428402550205156911164683,
  34530186113883473865428402550205156911605515,
  c92,
  c306,
  0,
  0,
  2905551140167001,
  c305,
  c112,
  c112,
  28775155142161509013036450099584038343384451,
  c14,
  c14,
  c196,
  c196,
  c232,
  c28,
  c28,
  2581692937,
  0,
  0,
  51795279169925587791528984200620137732747811,
  c6,
  c55,
  c6,
  0,
  c287,
  c6,
  c138,
  c6,
  c194,
  c194,
  2581692937,
  c80,
  0,
  c93,
  0,
  0,
  0,
  c4,
  0,
  c195,
  0,
  c42,
  c96,
  c33,
  c96,
  0,
  0,
  c47,
  c180,
  c113,
  c113,
  c50,
  0,
  c212,
  c180,
  c181,
  c181,
  c50,
  c195,
  0,
  c123,
  0,
  c42,
  c96,
  c33,
  c96,
  0,
  0,
  c135,
  c162,
  c113,
  c113,
  c50,
  0,
  51795279170790125500884661224080457005388451,
  c162,
  c181,
  c162,
  c50,
  c123,
  c4,
  0,
  c4,
  0,
  c195,
  0,
  c42,
  c89,
  c33,
  c89,
  0,
  0,
  c47,
  c180,
  c113,
  c113,
  c50,
  0,
  c212,
  c180,
  c181,
  c181,
  c50,
  c195,
  0,
  c262,
  0,
  c42,
  c89,
  c14,
  c14,
  0,
  0,
  c135,
  c180,
  c113,
  c113,
  c50,
  0,
  c164,
  c180,
  c181,
  c164,
  c50,
  c262,
  c4,
  c28,
  c28,
  c166,
  0,
  0,
  c4,
  0,
  c56,
  0,
  c42,
  c96,
  c33,
  c96,
  0,
  0,
  c47,
  c114,
  284,
  c47,
  c50,
  0,
  c212,
  c114,
  c141,
  c114,
  c50,
  c56,
  0,
  c123,
  0,
  c42,
  c96,
  c33,
  c96,
  0,
  0,
  c273,
  c268,
  c254,
  c135,
  c50,
  0,
  83447948986429120174466931391070220908694699,
  c298,
  c141,
  c141,
  c50,
  c123,
  c4,
  0,
  c4,
  0,
  c56,
  0,
  c42,
  c89,
  c33,
  c89,
  0,
  0,
  c47,
  c114,
  276,
  c47,
  c50,
  0,
  c212,
  c114,
  c141,
  c114,
  c50,
  c56,
  0,
  c56,
  0,
  c42,
  3980750176597625,
  c14,
  c14,
  0,
  0,
  c273,
  c268,
  c254,
  c135,
  c50,
  0,
  c164,
  c298,
  c141,
  c141,
  c50,
  c56,
  c4,
  0,
  c4,
  0,
  c56,
  0,
  c42,
  c96,
  c33,
  c96,
  0,
  0,
  c47,
  c114,
  236,
  c47,
  c50,
  c266,
  c50,
  c56,
  0,
  c52,
  0,
  c42,
  c96,
  c33,
  c96,
  0,
  0,
  c273,
  c268,
  c254,
  c135,
  c50,
  c266,
  c50,
  c52,
  c4,
  0,
  c4,
  0,
  c56,
  0,
  c42,
  c89,
  c33,
  c89,
  0,
  0,
  c47,
  c114,
  292,
  c47,
  c50,
  c266,
  c50,
  c56,
  0,
  c56,
  0,
  c42,
  3980750176597625,
  c14,
  c14,
  0,
  0,
  c273,
  c268,
  c254,
  c135,
  c50,
  c266,
  c50,
  c56,
  c4,
  c166,
  c97,
  c93,
  0,
  c94,
  0,
  0,
  c104,
  0,
  c122,
  0,
  c195,
  0,
  c38,
  c120,
  c352,
  c38,
  0,
  c38,
  c348,
  c217,
  c38,
  c195,
  0,
  c262,
  0,
  c38,
  c120,
  c14,
  c14,
  0,
  c38,
  c348,
  c217,
  c38,
  c262,
  c122,
  c28,
  c28,
  c166,
  0,
  c104,
  0,
  c122,
  0,
  c56,
  0,
  c95,
  c120,
  0,
  581113285321753,
  c114,
  28775155094819829696912994871318514437793155,
  c114,
  c120,
  0,
  c95,
  c230,
  c61,
  c95,
  c56,
  0,
  c56,
  0,
  c95,
  c120,
  c14,
  c14,
  0,
  c95,
  c230,
  c61,
  c95,
  c56,
  c122,
  0,
  c122,
  0,
  c56,
  0,
  c95,
  c17,
  0,
  c212,
  c114,
  c302,
  c114,
  c17,
  0,
  c95,
  c230,
  c61,
  c95,
  c56,
  0,
  c52,
  0,
  c95,
  c17,
  0,
  c117,
  28775155094819829696912994871288190076923395,
  c302,
  c117,
  c17,
  0,
  c95,
  c230,
  c61,
  c95,
  c52,
  c122,
  c104,
  c166,
  0,
  0,
  c104,
  0,
  c340,
  69060372194746203489195520400014348416928459,
  0,
  0,
  c38,
  c54,
  0,
  c92,
  c325,
  c176,
  c176,
  c38,
  0,
  c38,
  c280,
  c14,
  c14,
  c196,
  c196,
  c340,
  c28,
  c28,
  0,
  c48,
  0,
  0,
  c91,
  c206,
  c57,
  c206,
  c238,
  c189,
  0,
  c91,
  c206,
  c57,
  c206,
  c338,
  c48,
  0,
  c104,
  0,
  c287,
  c6,
  c138,
  c6,
  0,
  c287,
  c6,
  0,
  c52,
  0,
  69060372227677230781924475537483532446902859,
  c17,
  0,
  c117,
  581112503845913,
  46040283062851163901775462530677257418407067,
  581112503845913,
  c17,
  c196,
  c52,
  c6,
  c104,
  0,
  c48,
  0,
  0,
  c91,
  c206,
  c57,
  c206,
  c6,
  c138,
  c6,
  c28,
  c48,
  c94,
  0,
  c150,
  c80,
  c97,
  c80,
  0,
  0,
  0,
  c106,
  80677897,
  c63,
  80677897,
  c80,
  0,
  c106,
  2581692937,
  c63,
  2581692937,
  c80,
  0,
  c93,
  c69,
  c97,
  c69,
  0,
  c94,
  c70,
  0,
  c106,
  0,
  0,
  0,
  c11,
  c35,
  c57,
  c35,
  c87,
  c87,
  0,
  c11,
  c35,
  c57,
  c35,
  0,
  c88,
  c238,
  c189,
  c88,
  0,
  c88,
  0,
  c221,
  c15,
  c57,
  c15,
  c21,
  c88,
  0,
  0,
  c91,
  c15,
  c57,
  c15,
  c87,
  c87,
  0,
  c91,
  c15,
  c57,
  c15,
  c63,
  0,
  0,
  0,
  c11,
  c35,
  c57,
  c35,
  c6,
  c3,
  c3,
  0,
  c88,
  c6,
  c138,
  c6,
  0,
  c88,
  c6,
  c21,
  c6,
  0,
  0,
  c91,
  c15,
  c57,
  c15,
  c6,
  c3,
  c3,
  c70,
  0,
  c150,
  c80,
  c97,
  c80,
  0,
  0,
  0,
  c71,
  0,
  c26,
  0,
  c105,
  0,
  0,
  c209,
  c310,
  46040248150876419375242181200897865020674075,
  c209,
  c20,
  c152,
  c20,
  0,
  0,
  0,
  c119,
  0,
  260,
  252,
  244,
  268,
  c173,
  c119,
  c204,
  c204,
  c153,
  c20,
  c84,
  c20,
  c105,
  c157,
  c26,
  c72,
  0,
  c26,
  c75,
  c157,
  c26,
  0,
  0,
  0,
  0,
  c16,
  c1,
  0,
  c11,
  0,
  c25,
  c183,
  c33,
  c25,
  0,
  c25,
  c134,
  0,
  c278,
  c86,
  34530227344112763638170488659729348634433931,
  c86,
  c134,
  c11,
  c16,
  0,
  0,
  c115,
  0,
  c175,
  0,
  340,
  c83,
  c126,
  c83,
  c174,
  c25,
  0,
  c25,
  c134,
  c236,
  c134,
  c115,
  c1,
  c0,
  c1,
  c40,
  c40,
  0,
  c105,
  0,
  0,
  c115,
  0,
  c175,
  0,
  348,
  c83,
  c126,
  c83,
  c174,
  c25,
  c197,
  c115,
  c1,
  c0,
  c1,
  0,
  0,
  c147,
  c179,
  c197,
  c147,
  c1,
  c21,
  c1,
  c105,
  0,
  0,
  c16,
  c1,
  0,
  c11,
  0,
  c25,
  c183,
  c33,
  c25,
  0,
  c25,
  c134,
  0,
  c278,
  28775155094049098131738586201197135660063107,
  c110,
  c110,
  c134,
  c11,
  c16,
  0,
  0,
  c115,
  0,
  c175,
  0,
  332,
  c83,
  c126,
  c83,
  c174,
  c25,
  0,
  c25,
  c134,
  c236,
  c134,
  c115,
  c1,
  c0,
  c1,
  0,
  0,
  c147,
  c179,
  c32,
  c147,
  c1,
  c21,
  c1,
  0,
  c16,
  c1,
  c0,
  c16,
  0,
  c105,
  0,
  0,
  c115,
  0,
  c175,
  0,
  356,
  c83,
  c126,
  c83,
  c174,
  c25,
  c197,
  c115,
  c1,
  c0,
  c1,
  c40,
  c105,
  c69,
  0,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c2,
  0,
  c7,
  0,
  c25,
  c186,
  c137,
  c25,
  0,
  c25,
  c51,
  0,
  c249,
  c129,
  c129,
  c149,
  c51,
  c7,
  c45,
  c2,
  c40,
  c40,
  c75,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c2,
  0,
  c7,
  0,
  c25,
  c186,
  c137,
  c25,
  0,
  c25,
  c51,
  0,
  108,
  c46,
  c110,
  c46,
  c51,
  c7,
  c45,
  c2,
  0,
  c5,
  0,
  c62,
  c31,
  c32,
  c62,
  c21,
  c5,
  0,
  c2,
  c82,
  c55,
  c2,
  c75,
  c69,
  0,
  0,
  0,
  0,
  c16,
  c1,
  0,
  c11,
  0,
  0,
  188,
  c86,
  c131,
  c86,
  c49,
  c265,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  c16,
  0,
  0,
  c115,
  0,
  c228,
  c127,
  c301,
  c127,
  0,
  c228,
  c30,
  c236,
  c30,
  c115,
  c1,
  c0,
  c1,
  c40,
  c40,
  c37,
  0,
  0,
  c16,
  c1,
  0,
  c11,
  0,
  0,
  c252,
  c128,
  c128,
  c136,
  c49,
  c265,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  c16,
  0,
  0,
  c115,
  0,
  c228,
  c127,
  c301,
  c127,
  0,
  c228,
  c30,
  c236,
  c30,
  c115,
  c1,
  c0,
  c1,
  0,
  0,
  c224,
  c15,
  c32,
  c15,
  c1,
  c21,
  c1,
  0,
  c16,
  c1,
  c0,
  c16,
  c37,
  c70,
  0,
  0,
  0,
  c154,
  c100,
  c73,
  c154,
  0,
  c2,
  0,
  c7,
  0,
  0,
  c191,
  40285217132851512643513646440434395933228691,
  c131,
  c131,
  c127,
  c137,
  c127,
  0,
  c85,
  c99,
  c61,
  c99,
  c7,
  c45,
  c2,
  c40,
  c40,
  c37,
  0,
  0,
  c261,
  c100,
  c73,
  c261,
  0,
  c2,
  0,
  c7,
  0,
  0,
  c191,
  c46,
  46040248151837298530239371703854659976358299,
  c46,
  c127,
  c137,
  c127,
  0,
  c85,
  c99,
  c61,
  c99,
  c7,
  c45,
  c2,
  0,
  c244,
  0,
  c346,
  c15,
  c32,
  c15,
  c21,
  c21,
  0,
  c2,
  c100,
  c73,
  c2,
  c37,
  c70,
  0,
  c71,
  0,
  c26,
  c37,
  c157,
  c37,
  c72,
  0,
  c26,
  c37,
  c157,
  c37,
  0,
  0,
  c71,
  0,
  c27,
  0,
  51795279169852064056715241483368753617381155,
  0,
  c60,
  c20,
  0,
  c246,
  c9,
  c197,
  c9,
  c20,
  c334,
  c334,
  c67,
  c27,
  c72,
  0,
  c27,
  c75,
  c67,
  c27,
  0,
  0,
  0,
  0,
  c151,
  c1,
  c3,
  c3,
  0,
  c101,
  c1,
  c0,
  c1,
  0,
  c102,
  c1,
  0,
  c235,
  c31,
  c32,
  c235,
  c1,
  0,
  c151,
  c1,
  c3,
  c3,
  0,
  0,
  c151,
  c1,
  c239,
  c1,
  0,
  c101,
  c1,
  c0,
  c1,
  0,
  c102,
  c1,
  0,
  c274,
  c31,
  c197,
  c274,
  c1,
  0,
  c151,
  c1,
  c239,
  c1,
  0,
  0,
  c151,
  c1,
  0,
  c123,
  c170,
  0,
  40285217131999651440160275562052670993378067,
  c134,
  0,
  34530227343511897253662307923419911315085579,
  c177,
  c110,
  c110,
  c134,
  c123,
  c1,
  0,
  c101,
  c1,
  c0,
  c1,
  0,
  c102,
  c1,
  0,
  c235,
  c31,
  c32,
  c235,
  c1,
  0,
  c151,
  c1,
  c0,
  c1,
  0,
  0,
  c151,
  c1,
  c3,
  c3,
  0,
  c101,
  c1,
  c0,
  c1,
  0,
  c102,
  c1,
  0,
  c274,
  c31,
  c197,
  c274,
  c1,
  0,
  c151,
  c1,
  c3,
  c3,
  0,
  0,
  0,
  c4,
  c59,
  c3,
  c3,
  0,
  c4,
  c59,
  0,
  c246,
  c9,
  c34,
  c34,
  c4,
  0,
  c4,
  c59,
  0,
  c52,
  c31,
  c34,
  c34,
  c4,
  0,
  c4,
  c59,
  c3,
  c3,
  0,
  74815403245562695947414274166760354203109171,
  0,
  c4,
  c59,
  0,
  c246,
  c9,
  c34,
  c34,
  c4,
  c345,
  c345,
  c67,
  c67,
  0,
  0,
  0,
  c5,
  c188,
  c3,
  c3,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  0,
  c47,
  c149,
  c313,
  c47,
  c51,
  0,
  c249,
  c129,
  c129,
  c149,
  c51,
  c7,
  0,
  c7,
  c9,
  0,
  0,
  c279,
  c39,
  c213,
  c39,
  c51,
  0,
  c164,
  c39,
  c320,
  c39,
  c51,
  c7,
  c2,
  0,
  c5,
  0,
  c62,
  c31,
  c32,
  c62,
  0,
  c62,
  c31,
  c32,
  c62,
  c5,
  0,
  c2,
  c188,
  c3,
  c3,
  c75,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  0,
  c47,
  c46,
  c213,
  c47,
  c51,
  0,
  36,
  c46,
  c110,
  c46,
  c51,
  c7,
  0,
  c7,
  c9,
  0,
  0,
  c279,
  c241,
  c213,
  c279,
  c51,
  0,
  c164,
  c241,
  c110,
  c110,
  c51,
  c7,
  c2,
  0,
  c5,
  0,
  c62,
  c31,
  c32,
  c62,
  0,
  c62,
  c31,
  c32,
  c62,
  c5,
  0,
  c2,
  c82,
  c55,
  c2,
  c75,
  0,
  0,
  0,
  0,
  c64,
  c35,
  c34,
  c64,
  c169,
  c3,
  c3,
  0,
  c2,
  c10,
  c0,
  c2,
  0,
  c102,
  0,
  0,
  c13,
  4648879689653385,
  c173,
  c13,
  c31,
  c34,
  c34,
  0,
  c52,
  c31,
  c34,
  c34,
  c102,
  0,
  c2,
  c169,
  c3,
  c3,
  c75,
  c67,
  c75,
  0,
  0,
  0,
  c36,
  0,
  c60,
  c1,
  c0,
  c1,
  0,
  c53,
  c1,
  0,
  c52,
  c31,
  c32,
  c52,
  c1,
  c36,
  c12,
  0,
  c36,
  0,
  c60,
  c1,
  c0,
  c1,
  0,
  c53,
  c1,
  0,
  c52,
  c31,
  c32,
  c52,
  c1,
  c36,
  c12,
  0,
  0,
  c36,
  0,
  c60,
  c59,
  0,
  c246,
  c9,
  0,
  c65,
  290557992716545,
  c61,
  290557992716545,
  c9,
  c59,
  0,
  c53,
  c59,
  0,
  c52,
  c31,
  c32,
  c52,
  c59,
  c36,
  c12,
  c67,
  c12,
  0,
  0,
  c36,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  c85,
  c99,
  c61,
  c99,
  c7,
  0,
  c7,
  c9,
  0,
  c85,
  c190,
  c61,
  c190,
  c7,
  c2,
  0,
  c53,
  0,
  c193,
  c31,
  c32,
  c193,
  0,
  c52,
  c31,
  c32,
  c52,
  c53,
  c36,
  c12,
  0,
  c36,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  c85,
  c99,
  c61,
  c99,
  c7,
  0,
  c7,
  c9,
  0,
  c85,
  c190,
  c61,
  c190,
  c7,
  c2,
  0,
  c53,
  0,
  c193,
  c31,
  c32,
  c193,
  0,
  c52,
  c31,
  c32,
  c52,
  c53,
  c36,
  c12,
  0,
  0,
  c36,
  0,
  c2,
  c10,
  c0,
  c2,
  0,
  c53,
  0,
  c193,
  c31,
  c32,
  c193,
  0,
  c52,
  c31,
  c32,
  c52,
  c53,
  c36,
  c12,
  c67,
  c12,
  0,
  c71,
  0,
  c27,
  c12,
  c67,
  c12,
  c72,
  0,
  c27,
  c12,
  c67,
  c12,
  0,
  0,
  c71,
  0,
  0,
  c333,
  0,
  c185,
  c121,
  0,
  c297,
  c349,
  80570434138802612893662684670901663300657603,
  c297,
  c185,
  c28,
  c28,
  c23,
  c67,
  c23,
  c72,
  0,
  0,
  c333,
  0,
  c2,
  c10,
  c0,
  c2,
  c28,
  c28,
  c23,
  c67,
  c23,
  0,
  c93,
  0,
  0,
  0,
  c4,
  c59,
  0,
  c223,
  0,
  c42,
  4648880478460809,
  c33,
  4648880478460809,
  c34,
  c34,
  c4,
  0,
  c4,
  c59,
  0,
  c223,
  c350,
  c34,
  c34,
  c4,
  c28,
  c28,
  0,
  c48,
  0,
  c4,
  c59,
  0,
  c223,
  c350,
  c34,
  c34,
  c4,
  0,
  c4,
  c59,
  0,
  c223,
  c31,
  c34,
  c34,
  c4,
  c48,
  c67,
  c67,
  0,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c2,
  0,
  c7,
  0,
  c42,
  c89,
  c137,
  c89,
  0,
  0,
  c47,
  28775155094906029938517504340707021685435139,
  c113,
  c113,
  c51,
  0,
  c249,
  c129,
  c129,
  c149,
  c51,
  c7,
  0,
  c7,
  0,
  c42,
  c89,
  c14,
  c14,
  0,
  0,
  c135,
  28775155094906029938517506934780407050841219,
  c113,
  c113,
  c51,
  0,
  c164,
  c325,
  c320,
  c164,
  c51,
  c7,
  c2,
  c28,
  c28,
  c75,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c2,
  0,
  c7,
  0,
  c42,
  c89,
  c137,
  c89,
  0,
  0,
  c47,
  c46,
  c213,
  c47,
  c51,
  0,
  100,
  c46,
  c110,
  c46,
  c51,
  c7,
  0,
  c7,
  0,
  c42,
  c89,
  c14,
  c14,
  0,
  0,
  c135,
  c241,
  c213,
  c135,
  c51,
  0,
  c164,
  c241,
  c110,
  c110,
  c51,
  c7,
  c2,
  0,
  c5,
  0,
  c62,
  c31,
  c32,
  c62,
  0,
  c62,
  c31,
  c32,
  c62,
  c5,
  0,
  c2,
  c82,
  c55,
  c2,
  c75,
  c93,
  0,
  c94,
  0,
  0,
  c104,
  0,
  0,
  c209,
  0,
  c38,
  c120,
  c352,
  c38,
  c118,
  c209,
  c59,
  0,
  c227,
  0,
  c38,
  c120,
  c14,
  c14,
  c118,
  c118,
  c59,
  c28,
  c28,
  0,
  c48,
  0,
  0,
  c209,
  0,
  c65,
  c120,
  83447949775113152913663093301513426278992555,
  c120,
  c118,
  c209,
  c59,
  0,
  c227,
  0,
  c65,
  c120,
  c14,
  c14,
  c118,
  c118,
  c59,
  0,
  0,
  c227,
  c153,
  c118,
  c118,
  c59,
  0,
  c227,
  c31,
  c118,
  c118,
  c59,
  c48,
  c67,
  c67,
  0,
  0,
  c104,
  0,
  c2,
  0,
  c7,
  0,
  c38,
  c281,
  c137,
  c38,
  0,
  c38,
  c275,
  c217,
  c275,
  c7,
  0,
  c7,
  0,
  c38,
  c280,
  c14,
  c14,
  0,
  c38,
  40285217132025004452164840870682172606034963,
  c217,
  c38,
  c7,
  c2,
  c28,
  c28,
  c75,
  0,
  c104,
  0,
  c2,
  0,
  c7,
  0,
  0,
  c191,
  c46,
  c207,
  c46,
  c281,
  c137,
  c281,
  0,
  c85,
  c99,
  c61,
  c99,
  c7,
  0,
  c7,
  0,
  83447949739413576710035654814928352465077035,
  c280,
  c14,
  c14,
  0,
  c85,
  c190,
  c61,
  c190,
  c7,
  c2,
  0,
  0,
  c267,
  c153,
  c32,
  c267,
  0,
  c336,
  c31,
  c32,
  c336,
  0,
  c52,
  c31,
  c32,
  c52,
  0,
  c267,
  c153,
  c32,
  c267,
  c104,
  c75,
  c94,
  0,
  c71,
  0,
  0,
  c104,
  0,
  c4,
  c121,
  0,
  c297,
  c349,
  c34,
  c34,
  c4,
  c28,
  c28,
  c23,
  c67,
  c23,
  c72,
  0,
  0,
  c104,
  0,
  c2,
  c10,
  c0,
  c2,
  c28,
  c28,
  c23,
  c67,
  c23,
  0,
  0,
  c71,
  0,
  0,
  0,
  c24,
  c121,
  c3,
  c24,
  0,
  c185,
  c121,
  c152,
  c185,
  0,
  c185,
  c121,
  c84,
  c185,
  0,
  c24,
  c121,
  c3,
  c24,
  c23,
  c157,
  c23,
  c72,
  0,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  0,
  c8,
  0,
  0,
  c119,
  c19,
  c173,
  c119,
  c204,
  c204,
  0,
  c119,
  c208,
  0,
  c218,
  c129,
  c129,
  92,
  c208,
  c84,
  c8,
  c29,
  c23,
  c157,
  c23,
  0,
  c93,
  c69,
  0,
  0,
  0,
  c5,
  c188,
  c3,
  c3,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  c25,
  c51,
  0,
  c249,
  c129,
  c129,
  c149,
  c51,
  c7,
  c45,
  c2,
  0,
  c5,
  0,
  c62,
  c31,
  c32,
  c62,
  c21,
  c5,
  0,
  c2,
  c188,
  c3,
  c3,
  c75,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  c25,
  c51,
  0,
  116,
  c46,
  c110,
  c46,
  c51,
  c7,
  c45,
  c2,
  0,
  c5,
  0,
  c62,
  c31,
  c32,
  c62,
  c21,
  c5,
  0,
  c2,
  c82,
  c55,
  c2,
  c75,
  c69,
  0,
  c94,
  c70,
  0,
  0,
  0,
  0,
  c64,
  c35,
  0,
  c38,
  0,
  c74,
  581110472830489,
  c176,
  581110472830489,
  5891845567436457,
  c38,
  c64,
  c100,
  c3,
  c3,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  c38,
  c275,
  c217,
  c275,
  c7,
  c45,
  c2,
  0,
  c244,
  0,
  0,
  3970839051851129,
  c277,
  c173,
  3970839051851129,
  c15,
  c32,
  c15,
  c21,
  c21,
  0,
  c2,
  c100,
  c3,
  c3,
  c75,
  0,
  0,
  c261,
  c100,
  c73,
  c261,
  0,
  c2,
  0,
  c7,
  c9,
  0,
  c85,
  c99,
  c61,
  c99,
  c7,
  c45,
  c2,
  0,
  c244,
  0,
  c346,
  c15,
  c32,
  c15,
  c21,
  c21,
  0,
  c2,
  c100,
  c73,
  c2,
  c75,
  c70,
  0,
  c71,
  0,
  0,
  0,
  c24,
  c121,
  c3,
  c24,
  0,
  c4,
  c121,
  c152,
  c4,
  0,
  c4,
  c121,
  c84,
  c4,
  0,
  c24,
  c121,
  c3,
  c24,
  c23,
  c157,
  c23,
  c72,
  0,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  0,
  c8,
  0,
  0,
  c13,
  c277,
  c173,
  c13,
  c15,
  c34,
  c15,
  c84,
  c8,
  c29,
  c23,
  c157,
  c23,
  0,
  0,
  0,
  0,
  c26,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  0,
  c8,
  51795279170797731404485476693764073670736547,
  c21,
  c8,
  c29,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  0,
  c8,
  0,
  c296,
  80570433295604533742253414504429745707945539,
  80570434265567672916486792730056150552677955,
  c296,
  c21,
  c8,
  c29,
  c26,
  0,
  c26,
  0,
  c105,
  0,
  0,
  c309,
  c310,
  c339,
  c309,
  c20,
  c152,
  c20,
  0,
  0,
  c203,
  c153,
  c339,
  c203,
  c20,
  c84,
  c20,
  c105,
  c158,
  c26,
  0,
  c26,
  c41,
  0,
  0,
  c24,
  c58,
  c55,
  c24,
  0,
  c263,
  c58,
  c45,
  c58,
  0,
  0,
  c311,
  c153,
  c22,
  c311,
  c58,
  c21,
  c58,
  0,
  c24,
  c58,
  c55,
  c24,
  c26,
  0,
  c26,
  c41,
  c158,
  c26,
  0,
  0,
  0,
  0,
  c16,
  0,
  c11,
  0,
  c13,
  c237,
  c33,
  c13,
  0,
  c13,
  c184,
  c292,
  c13,
  c11,
  0,
  c11,
  0,
  c25,
  c183,
  c33,
  c25,
  0,
  c25,
  c183,
  0,
  c278,
  c86,
  5229987765647513,
  c86,
  c25,
  c11,
  c16,
  0,
  0,
  c145,
  c198,
  c201,
  c145,
  c10,
  c0,
  c45,
  c40,
  c40,
  0,
  c105,
  0,
  0,
  c145,
  c198,
  c201,
  c145,
  c10,
  c0,
  c45,
  0,
  0,
  c203,
  c179,
  0,
  c25,
  c184,
  83447949775138505925667658610119300706609835,
  c25,
  c203,
  0,
  c203,
  c179,
  0,
  c13,
  c184,
  c292,
  c13,
  c203,
  c21,
  c21,
  c105,
  0,
  0,
  c16,
  0,
  c11,
  0,
  c13,
  c237,
  c33,
  c13,
  0,
  c13,
  c184,
  c44,
  c13,
  c11,
  0,
  c11,
  0,
  c25,
  c183,
  c33,
  c25,
  0,
  c25,
  c183,
  c44,
  c44,
  c11,
  c16,
  0,
  0,
  c145,
  c198,
  c201,
  c145,
  c10,
  c0,
  c45,
  0,
  0,
  c147,
  c179,
  0,
  c25,
  c184,
  c44,
  c44,
  c147,
  0,
  c147,
  c179,
  0,
  c13,
  c184,
  c44,
  c13,
  c147,
  c21,
  c21,
  0,
  c16,
  c10,
  c0,
  c16,
  0,
  c105,
  0,
  0,
  c145,
  c198,
  c201,
  c145,
  c10,
  c0,
  c45,
  c40,
  c105,
  c69,
  0,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c5,
  0,
  c124,
  c171,
  c22,
  c124,
  c45,
  c5,
  c40,
  c40,
  c41,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c5,
  0,
  c124,
  c171,
  c22,
  c124,
  c45,
  c5,
  0,
  c5,
  0,
  c344,
  0,
  c25,
  290557737879809,
  c33,
  290557737879809,
  c22,
  c22,
  c21,
  c5,
  0,
  c5,
  c82,
  c55,
  c5,
  c41,
  c69,
  0,
  0,
  0,
  0,
  c16,
  0,
  c11,
  0,
  0,
  c111,
  c210,
  c131,
  c111,
  c49,
  0,
  c182,
  c210,
  c247,
  c182,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  0,
  c11,
  0,
  0,
  172,
  c86,
  c131,
  c86,
  c49,
  0,
  c108,
  c86,
  c247,
  c108,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  c16,
  0,
  0,
  c226,
  c198,
  c201,
  c226,
  c10,
  c0,
  c45,
  c40,
  c40,
  c37,
  0,
  0,
  c16,
  0,
  c11,
  0,
  0,
  c111,
  c304,
  c136,
  c111,
  c49,
  0,
  c182,
  c210,
  c165,
  c165,
  c49,
  0,
  c107,
  c30,
  c44,
  c44,
  c11,
  0,
  c11,
  0,
  0,
  c252,
  c128,
  c128,
  c136,
  c49,
  0,
  c108,
  c299,
  c165,
  c108,
  c49,
  0,
  c107,
  c276,
  c44,
  c276,
  c11,
  c16,
  0,
  0,
  c226,
  c198,
  c201,
  c226,
  c10,
  c0,
  c45,
  0,
  0,
  c224,
  c15,
  c290,
  c15,
  0,
  c224,
  c15,
  c290,
  c15,
  c21,
  c21,
  0,
  c16,
  c10,
  c0,
  c16,
  c37,
  c70,
  0,
  0,
  0,
  c154,
  c100,
  c73,
  c154,
  0,
  0,
  3486655034120553,
  c171,
  c22,
  3486655034120553,
  0,
  c124,
  c171,
  c22,
  c124,
  c45,
  c45,
  c40,
  c40,
  c37,
  0,
  0,
  c288,
  c100,
  c73,
  c288,
  0,
  c263,
  0,
  c124,
  c171,
  c22,
  c124,
  c45,
  c45,
  0,
  0,
  46040248178511202460029643914656874506818715,
  c15,
  c22,
  c15,
  0,
  c344,
  c15,
  c22,
  c15,
  c21,
  c21,
  0,
  c263,
  c100,
  c73,
  c263,
  c37,
  c70,
  0,
  0,
  c26,
  c37,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  0,
  c8,
  0,
  c296,
  c15,
  c290,
  c15,
  c21,
  c8,
  c29,
  c37,
  0,
  c26,
  c37,
  c158,
  c37,
  0,
  c26,
  c37,
  0,
  0,
  c24,
  c58,
  c73,
  c24,
  0,
  c5,
  c58,
  c45,
  c5,
  0,
  c5,
  c58,
  c21,
  c5,
  0,
  c24,
  c58,
  c73,
  c24,
  c37,
  0,
  c26,
  c37,
  c158,
  c37,
  0,
  0,
  0,
  c27,
  0,
  0,
  c130,
  c321,
  c239,
  c130,
  0,
  c329,
  c10,
  c0,
  c329,
  c43,
  c43,
  0,
  0,
  c130,
  0,
  0,
  0,
  c81,
  c303,
  c168,
  c81,
  c19,
  0,
  40285217132843906739912276343449475334709267,
  c326,
  c142,
  c142,
  c19,
  c170,
  0,
  0,
  c81,
  c303,
  2905551204212057,
  c81,
  c19,
  c44,
  c44,
  c170,
  c259,
  c130,
  0,
  c60,
  c10,
  c0,
  c60,
  c125,
  c125,
  c27,
  0,
  c27,
  0,
  c342,
  0,
  c283,
  c20,
  c192,
  c20,
  c43,
  c43,
  c68,
  c27,
  0,
  c27,
  c41,
  0,
  0,
  c288,
  c58,
  c55,
  c58,
  0,
  c60,
  c58,
  0,
  0,
  0,
  c219,
  c253,
  c270,
  c139,
  c54,
  0,
  c92,
  52,
  c142,
  c92,
  c54,
  c9,
  c22,
  c9,
  c58,
  c125,
  c125,
  c27,
  0,
  c27,
  c41,
  c68,
  c27,
  0,
  0,
  0,
  0,
  c258,
  c169,
  c3,
  c3,
  0,
  c101,
  c10,
  c0,
  c101,
  0,
  c102,
  0,
  c18,
  0,
  c13,
  3967131513149049,
  c33,
  c13,
  0,
  c13,
  c216,
  c292,
  c13,
  c18,
  0,
  c18,
  0,
  c42,
  c103,
  c33,
  c103,
  0,
  0,
  581109441217561,
  c39,
  c328,
  581109441217561,
  c216,
  c291,
  c216,
  c18,
  c102,
  0,
  c258,
  c169,
  c3,
  c3,
  0,
  0,
  0,
  c161,
  c35,
  c295,
  c161,
  c321,
  c239,
  0,
  c161,
  c35,
  c295,
  c161,
  0,
  c283,
  c10,
  c0,
  c192,
  c43,
  c43,
  0,
  0,
  c341,
  0,
  0,
  c13,
  c237,
  0,
  c132,
  c326,
  c142,
  c132,
  c13,
  c170,
  0,
  c13,
  c237,
  c44,
  c13,
  c170,
  c259,
  c259,
  0,
  c101,
  c10,
  c0,
  c101,
  0,
  c102,
  0,
  c79,
  0,
  c13,
  80570434265613308338095008988510031890371907,
  c33,
  c13,
  0,
  c13,
  c216,
  c44,
  c13,
  c79,
  0,
  c79,
  0,
  c42,
  c103,
  c33,
  c103,
  0,
  83447949767015400879405121298714409793423915,
  c216,
  c44,
  c44,
  c79,
  c102,
  0,
  c341,
  c10,
  c0,
  c259,
  0,
  0,
  0,
  c161,
  c35,
  c295,
  c161,
  c169,
  c3,
  c3,
  0,
  c283,
  c10,
  c0,
  c192,
  c43,
  c43,
  0,
  0,
  0,
  c4,
  0,
  c289,
  c170,
  0,
  0,
  c47,
  581113291007001,
  c307,
  c47,
  c133,
  69060372235813012334189239874728763344499275,
  c133,
  c170,
  c3,
  c3,
  0,
  c4,
  0,
  c289,
  c9,
  c172,
  c9,
  0,
  c343,
  c9,
  c172,
  c9,
  c4,
  0,
  c4,
  0,
  c18,
  0,
  c42,
  c308,
  c33,
  c308,
  0,
  0,
  c47,
  34530186112958088927262776943888908159113611,
  c307,
  c47,
  c133,
  c291,
  c133,
  c18,
  0,
  c18,
  0,
  c42,
  c103,
  c33,
  c103,
  0,
  0,
  c284,
  c39,
  c328,
  c39,
  c133,
  c291,
  c133,
  c18,
  c4,
  0,
  c4,
  0,
  c18,
  c171,
  c172,
  c18,
  c3,
  c3,
  0,
  c342,
  0,
  c4,
  0,
  1162222946641449,
  c9,
  c172,
  1162222946641449,
  c192,
  c4,
  c43,
  c43,
  c68,
  c68,
  0,
  0,
  0,
  c5,
  c188,
  c3,
  c3,
  0,
  c5,
  0,
  0,
  0,
  c47,
  c149,
  c313,
  c47,
  c54,
  0,
  c240,
  c149,
  c214,
  c149,
  c54,
  c9,
  c22,
  c9,
  0,
  0,
  0,
  c139,
  c39,
  c214,
  c39,
  c54,
  0,
  c92,
  c39,
  c214,
  c39,
  c54,
  c9,
  c22,
  c9,
  c5,
  0,
  c5,
  0,
  c18,
  0,
  c42,
  c186,
  c33,
  c186,
  c22,
  c18,
  0,
  c18,
  0,
  c42,
  c103,
  c33,
  c103,
  c22,
  c18,
  c5,
  0,
  c5,
  c188,
  c3,
  c3,
  c41,
  0,
  0,
  c5,
  c82,
  c55,
  c5,
  0,
  c5,
  0,
  0,
  0,
  c47,
  c46,
  34530186113049359770478203897071894303136779,
  c47,
  c54,
  0,
  c240,
  c46,
  c142,
  c46,
  c54,
  c9,
  c22,
  c9,
  0,
  0,
  0,
  c219,
  c253,
  c270,
  c139,
  c54,
  0,
  c92,
  28,
  c142,
  c92,
  c54,
  c9,
  c22,
  c9,
  c5,
  0,
  c5,
  0,
  c79,
  0,
  c42,
  c186,
  c33,
  c186,
  c22,
  c79,
  0,
  c79,
  0,
  c42,
  c103,
  c33,
  c103,
  c22,
  c79,
  c5,
  0,
  c5,
  c82,
  c55,
  c5,
  c41,
  0,
  0,
  0,
  c258,
  c169,
  c3,
  c3,
  0,
  c101,
  c10,
  c0,
  c101,
  0,
  c102,
  0,
  c18,
  0,
  c13,
  3967131513149049,
  c33,
  c13,
  c22,
  c18,
  0,
  c18,
  0,
  c42,
  c103,
  c33,
  c103,
  c22,
  c18,
  c102,
  0,
  c258,
  c169,
  c3,
  c3,
  c41,
  c68,
  c41,
  0,
  0,
  0,
  c36,
  0,
  c60,
  c10,
  c0,
  c60,
  0,
  c53,
  0,
  c18,
  0,
  0,
  c111,
  28775155094906029937728516920548140973765123,
  c163,
  c111,
  c17,
  0,
  c272,
  c271,
  c251,
  c215,
  c17,
  0,
  c85,
  c30,
  c61,
  c30,
  c18,
  0,
  c18,
  0,
  0,
  c284,
  c39,
  c163,
  c39,
  c17,
  0,
  c117,
  c39,
  132,
  c39,
  c17,
  0,
  c85,
  c30,
  c61,
  c30,
  c18,
  c53,
  c36,
  c12,
  0,
  c36,
  0,
  c60,
  c10,
  c0,
  c60,
  0,
  c53,
  0,
  c79,
  0,
  0,
  c111,
  c304,
  c136,
  c111,
  c17,
  0,
  c332,
  63305341208113396221732444880399746894598203,
  c165,
  c165,
  c17,
  0,
  c85,
  c30,
  c44,
  c44,
  c79,
  0,
  c79,
  0,
  0,
  c284,
  c327,
  c136,
  c136,
  c17,
  0,
  c117,
  c327,
  c165,
  c117,
  c17,
  0,
  c85,
  c30,
  c44,
  c44,
  c79,
  c53,
  c36,
  c12,
  0,
  0,
  c36,
  0,
  c60,
  0,
  c289,
  c9,
  c172,
  c9,
  0,
  c343,
  c9,
  c172,
  c9,
  c60,
  0,
  c53,
  0,
  c18,
  0,
  c65,
  c17,
  0,
  c272,
  c271,
  c251,
  c215,
  c17,
  0,
  c65,
  c337,
  c61,
  c65,
  c18,
  0,
  c18,
  0,
  c65,
  c17,
  0,
  c117,
  c39,
  124,
  c39,
  c17,
  0,
  c65,
  c337,
  c61,
  c65,
  c18,
  c53,
  c36,
  c12,
  c68,
  c12,
  0,
  0,
  c36,
  0,
  c60,
  0,
  0,
  0,
  c191,
  c282,
  c163,
  c163,
  c54,
  0,
  c240,
  c282,
  c214,
  c282,
  c54,
  c9,
  c22,
  c9,
  0,
  0,
  0,
  c139,
  c39,
  c163,
  c39,
  c54,
  0,
  c92,
  c39,
  c214,
  c39,
  c54,
  c9,
  c22,
  c9,
  c60,
  0,
  c53,
  0,
  c18,
  0,
  0,
  51795279170790125501140076499849708274102947,
  c215,
  c163,
  c163,
  c17,
  0,
  c272,
  c271,
  c251,
  c215,
  c17,
  c22,
  c18,
  0,
  c18,
  0,
  0,
  c139,
  c39,
  c163,
  c39,
  c17,
  0,
  c117,
  c39,
  4,
  c39,
  c17,
  c22,
  c18,
  c53,
  c36,
  c12,
  0,
  c36,
  0,
  c60,
  0,
  0,
  0,
  c191,
  c46,
  40285217131933733609986487563456523874298131,
  c46,
  c54,
  0,
  c240,
  c46,
  c142,
  c46,
  c54,
  c9,
  c22,
  c9,
  0,
  0,
  0,
  c219,
  c253,
  c270,
  c139,
  c54,
  0,
  c92,
  12,
  c142,
  c92,
  c54,
  c9,
  c22,
  c9,
  c60,
  0,
  c53,
  0,
  c79,
  0,
  0,
  51795279169885022972321930827565967499300643,
  c46,
  c335,
  c46,
  c17,
  0,
  c332,
  c46,
  c165,
  c46,
  c17,
  c22,
  c79,
  0,
  c79,
  0,
  0,
  c139,
  c331,
  c335,
  c139,
  c17,
  0,
  c117,
  c331,
  c165,
  c117,
  c17,
  c22,
  c79,
  c53,
  c36,
  c12,
  0,
  0,
  c36,
  0,
  c60,
  c10,
  c0,
  c60,
  0,
  c53,
  0,
  c18,
  0,
  c65,
  c17,
  0,
  c272,
  c271,
  c251,
  c215,
  c17,
  c22,
  c18,
  0,
  c18,
  0,
  c65,
  c17,
  0,
  c117,
  c39,
  140,
  c39,
  c17,
  c22,
  c18,
  c53,
  c36,
  c12,
  c68,
  c12,
  0,
  0,
  c27,
  c12,
  0,
  c36,
  0,
  c101,
  c10,
  c0,
  c101,
  c125,
  c36,
  c12,
  0,
  c27,
  c12,
  c68,
  c12,
  0,
  c27,
  c12,
  0,
  c36,
  0,
  c5,
  c58,
  0,
  0,
  0,
  c219,
  c253,
  c270,
  c139,
  c54,
  0,
  c92,
  148,
  c142,
  c92,
  c54,
  c9,
  c22,
  c9,
  c5,
  c125,
  c36,
  c12,
  0,
  c27,
  c12,
  c68,
  c12,
  0,
  0,
  0,
  c156,
  0,
  c48,
  0,
  0,
  0,
  c148,
  c19,
  c159,
  c19,
  c78,
  c78,
  0,
  c148,
  c222,
  0,
  581110559313433,
  c83,
  5229988613101465,
  581110559313433,
  c222,
  c10,
  c0,
  0,
  0,
  c148,
  c19,
  c159,
  c19,
  c78,
  c78,
  0,
  c148,
  c222,
  c14,
  c14,
  c194,
  c48,
  c260,
  0,
  c48,
  0,
  0,
  0,
  c148,
  c19,
  c159,
  c19,
  c78,
  c78,
  0,
  c148,
  c222,
  c44,
  c44,
  c10,
  c0,
  0,
  0,
  c148,
  c19,
  c159,
  c19,
  c78,
  c78,
  0,
  c148,
  c222,
  c14,
  c14,
  c28,
  c48,
  0,
  c66,
  c23,
  c68,
  c23,
  0,
  c66,
  c41,
  c116,
  c41,
  0,
  c156,
  c23,
  c68,
  c23,
  0,
  c93,
  0,
  c66,
  0,
  c48,
  0,
  c4,
  0,
  c225,
  c200,
  c199,
  c225,
  0,
  c225,
  c200,
  c199,
  c225,
  c4,
  0,
  c4,
  0,
  c109,
  0,
  c229,
  c231,
  c248,
  c231,
  0,
  c229,
  c133,
  c300,
  c133,
  c109,
  0,
  c109,
  0,
  c229,
  c231,
  c248,
  c231,
  0,
  c229,
  c133,
  c300,
  c133,
  c109,
  c4,
  c48,
  c68,
  c68,
  0,
  c66,
  c41,
  c116,
  c41,
  c93,
  0,
  c94,
  0,
  c66,
  0,
  c48,
  0,
  0,
  c146,
  c200,
  c199,
  c146,
  0,
  c146,
  c200,
  c199,
  c146,
  0,
  c146,
  c200,
  c199,
  c146,
  0,
  c146,
  c200,
  c199,
  c146,
  0,
  0,
  c109,
  c153,
  0,
  c205,
  0,
  c160,
  c256,
  220,
  c160,
  c202,
  c65,
  c109,
  0,
  c109,
  0,
  c65,
  c17,
  c248,
  c17,
  0,
  c205,
  0,
  c160,
  c256,
  212,
  c160,
  c202,
  c65,
  c109,
  0,
  c109,
  0,
  c65,
  c17,
  c248,
  c17,
  0,
  c205,
  0,
  c160,
  c256,
  156,
  c160,
  c202,
  c65,
  c109,
  0,
  c109,
  c153,
  0,
  c205,
  0,
  c160,
  c256,
  228,
  c160,
  c202,
  c65,
  c109,
  c48,
  c68,
  c68,
  0,
  c66,
  c41,
  c116,
  c41,
  c94,
  0,
  0,
  c156,
  0,
  c48,
  0,
  0,
  0,
  0,
  c167,
  c83,
  c207,
  c167,
  c220,
  c159,
  c220,
  c78,
  c78,
  0,
  c175,
  0,
  c322,
  c83,
  c126,
  c83,
  c174,
  0,
  c167,
  c83,
  c207,
  c167,
  c10,
  c0,
  0,
  0,
  c13,
  c220,
  c159,
  c13,
  c78,
  c78,
  0,
  c13,
  0,
  c132,
  1670689536887370,
  c126,
  c132,
  c14,
  c13,
  c194,
  c48,
  c260,
  0,
  c48,
  0,
  0,
  0,
  c38,
  c220,
  c159,
  c38,
  c78,
  c78,
  0,
  c38,
  0,
  c322,
  1016942465451026,
  c176,
  c176,
  c44,
  c38,
  c10,
  c0,
  0,
  0,
  c13,
  c220,
  c159,
  c13,
  c78,
  c78,
  0,
  c13,
  0,
  c132,
  204,
  c176,
  c132,
  c14,
  c13,
  c28,
  c48,
  0,
  c66,
  c23,
  c68,
  c23,
  0,
  c66,
  c41,
  c116,
  c41,
  0,
  c156,
  c23,
  c68,
  c23,
  0,
  0,
  0,
  c156,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  c43,
  c29,
  c260,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  c43,
  c29,
  0,
  c66,
  c23,
  c158,
  c23,
  0,
  c66,
  c41,
  c116,
  c41,
  0,
  c156,
  c23,
  c158,
  c23,
  0,
  c93,
  c69,
  0,
  c66,
  c41,
  c116,
  c41,
  c69,
  0,
  c94,
  c70,
  0,
  c66,
  c41,
  c116,
  c41,
  c70,
  0,
  0,
  c156,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  c43,
  c29,
  c260,
  0,
  c29,
  0,
  c8,
  c10,
  c0,
  c8,
  c43,
  c29,
  0,
  c66,
  c23,
  c158,
  c23,
  0,
  c66,
  c41,
  c116,
  c41,
  0,
  c156,
  c23,
  c158,
  c23,
  0,
  0,
  0,
  c71,
  0,
  c26,
  c76,
  0,
  0,
  c24,
  c20,
  0,
  c293,
  c245,
  0,
  c119,
  c208,
  3977827287274873,
  c208,
  c293,
  c24,
  0,
  c122,
  c20,
  c152,
  c20,
  0,
  c122,
  c20,
  c84,
  c20,
  0,
  c24,
  c20,
  0,
  0,
  c119,
  28775155094923777046131478809679592605463683,
  c173,
  c119,
  c204,
  c204,
  0,
  c119,
  c208,
  c14,
  c208,
  c24,
  c76,
  c72,
  0,
  c26,
  c76,
  0,
  c29,
  0,
  c8,
  c6,
  c0,
  c8,
  0,
  c8,
  c6,
  c84,
  c8,
  c29,
  c76,
  0,
  c150,
  c69,
  c97,
  c69,
  0,
  0,
  0,
  0,
  c16,
  c1,
  0,
  c11,
  0,
  0,
  196,
  c86,
  c131,
  c86,
  c49,
  c265,
  c49,
  0,
  c107,
  c30,
  c140,
  c30,
  c11,
  c16,
  0,
  c90,
  c1,
  c0,
  c1,
  c40,
  c40,
  c37,
  0,
  0,
  c16,
  c1,
  0,
  c11,
  0,
  0,
  c252,
  c128,
  c128,
  c136,
  c49,
  c265,
  c49,
  0,
  c107,
  c276,
  c44,
  c276,
  c11,
  c16,
  0,
  c90,
  c1,
  c0,
  c1,
  0,
  c90,
  c1,
  c21,
  c1,
  0,
  c16,
  c1,
  c0,
  c16,
  c37,
  c70,
  0,
  0,
  0,
  c154,
  c100,
  c73,
  c154,
  0,
  c2,
  0,
  c7,
  c171,
  c172,
  c7,
  c45,
  c2,
  c40,
  c40,
  c37,
  0,
  0,
  0,
  c64,
  c35,
  0,
  5728516812781225,
  0,
  c74,
  c178,
  2905553124914265,
  c178,
  c44,
  c44,
  c64,
  c6,
  c73,
  c6,
  0,
  c2,
  c6,
  c138,
  c6,
  0,
  c244,
  c6,
  c21,
  c6,
  0,
  c2,
  c6,
  c73,
  c6,
  c37,
  c70,
  0,
  c71,
  0,
  c26,
  c76,
  0,
  0,
  c24,
  c20,
  0,
  c293,
  c245,
  c34,
  c34,
  c24,
  0,
  c4,
  c20,
  c152,
  c4,
  0,
  c4,
  c20,
  c84,
  c4,
  0,
  c24,
  c20,
  0,
  0,
  0,
  c219,
  c128,
  c128,
  164,
  c277,
  c173,
  c277,
  c15,
  c34,
  c15,
  c24,
  c76,
  c72,
  0,
  c26,
  c76,
  0,
  c29,
  0,
  c8,
  c6,
  c0,
  c8,
  0,
  c8,
  c6,
  c84,
  c8,
  c29,
  c76,
  0,
  0,
  c71,
  0,
  c27,
  c77,
  c63,
  c77,
  c72,
  0,
  c27,
  c77,
  c63,
  c77,
  0,
  c150,
  0,
  c255,
  0,
  0,
  c143,
  c98,
  0,
  c161,
  c286,
  c34,
  c161,
  c143,
  0,
  c4,
  c98,
  c192,
  c4,
  c43,
  c43,
  c155,
  0,
  0,
  c143,
  c98,
  c3,
  c3,
  0,
  c4,
  c98,
  c192,
  c4,
  c43,
  c43,
  c97,
  0,
  c255,
  0,
  0,
  0,
  c64,
  c35,
  c34,
  c64,
  c87,
  c87,
  0,
  c64,
  c35,
  c34,
  c64,
  0,
  c2,
  c10,
  c0,
  c2,
  c43,
  c43,
  c155,
  0,
  0,
  0,
  c64,
  c35,
  c34,
  c64,
  c6,
  c3,
  c3,
  0,
  c2,
  c6,
  c0,
  c6,
  c43,
  c43,
  0,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c106,
  c12,
  c63,
  c12,
  0,
  c71,
  0,
  c27,
  c77,
  c155,
  c77,
  c72,
  0,
  c27,
  c77,
  c155,
  c77,
  0,
  0,
  c71,
  c80,
  c72,
  c80,
  0,
  c93,
  0,
  c66,
  c166,
  c116,
  c166,
  c97,
  c93,
  0,
  c94,
  0,
  c66,
  c166,
  c116,
  c166,
  0,
  c66,
  0,
  c48,
  0,
  c2,
  c238,
  c189,
  c2,
  c338,
  c48,
  c116,
  0,
  c48,
  0,
  c2,
  c6,
  c138,
  c6,
  c28,
  c48,
  c94,
  0,
  c71,
  c80,
  c72,
  c80,
  0,
  0,
  c71,
  c80,
  c72,
  c80,
  0,
  c93,
  c69,
  c97,
  c69,
  0,
  c94,
  c70,
  0,
  c106,
  0,
  0,
  0,
  c64,
  c35,
  0,
  c205,
  0,
  c74,
  c323,
  c351,
  c74,
  c202,
  0,
  1016942286236690,
  c323,
  c207,
  c207,
  c64,
  c87,
  c87,
  0,
  c64,
  c35,
  0,
  c205,
  0,
  1452773636260394,
  c177,
  c351,
  c177,
  c202,
  0,
  20,
  c177,
  c207,
  c177,
  c64,
  0,
  c2,
  c238,
  c189,
  c2,
  c43,
  c43,
  c63,
  0,
  0,
  0,
  c64,
  c35,
  0,
  c38,
  0,
  c74,
  c178,
  c176,
  c178,
  c44,
  c38,
  c64,
  c6,
  c3,
  c3,
  0,
  c2,
  c6,
  c138,
  c6,
  c43,
  c43,
  c70,
  0,
  c71,
  c80,
  c72,
  c80
]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 16000000 in
lemma tree_checked : check code order (fun _ => none) treeData = some [] := by
  decide +kernel

lemma classified (q : V → Fin 4) (hq : CodeConditions q) : ∃ i, q = SlotTables.code i := by
  exact check_sound code order (fun _ => none) treeData [] q tree_checked
    (by intro v c h; cases h) hq

lemma conditions_classified (t : H → Slot) (ht : Conditions t) :
    ∃ i, localCode t = SlotTables.code i :=
  classified (localCode t) (code_conditions t ht)

end SlotTree

namespace FiniteSlots

def joined (f : H → Fin 30) (a b h k : H) : Prop :=
  (f h = f a ∨ f h = f b) ∧ (f k = f a ∨ f k = f b)
def mergeRel (f : H → Fin 30) (a b h k : H) : Prop :=
  f h = f k ∨ joined f a b h k ∨ joined f (barH a) (barH b) h k

lemma joined_sound (t : H → Slot) (f : H → Fin 30)
    (hf : ∀ h k, f h = f k → t h = t k) (a b h k : H)
    (hab : t a = t b) (hr : joined f a b h k) : t h = t k := by
  obtain ⟨hh, hk⟩ := hr
  rcases hh with hh | hh <;> rcases hk with hk | hk
  · exact (hf h a hh).trans (hf k a hk).symm
  · exact (hf h a hh).trans (hab.trans (hf k b hk).symm)
  · exact (hf h b hh).trans (hab.symm.trans (hf k a hk).symm)
  · exact (hf h b hh).trans (hf k b hk).symm

lemma mergeRel_sound (t : H → Slot) (f : H → Fin 30)
    (hf : ∀ h k, f h = f k → t h = t k)
    (hb : ∀ h, t (barH h) = bar (t h)) (a b h k : H)
    (hab : t a = t b) (hr : mergeRel f a b h k) : t h = t k := by
  rcases hr with hr | hr | hr
  · exact hf h k hr
  · exact joined_sound t f hf a b h k hab hr
  · apply joined_sound t f hf (barH a) (barH b) h k ?_ hr
    rw [hb, hb, hab]

def mergeRows : Fin 15 → Finset V := ![{1,4,5}, {0,2,6}, {3,5,6}, {2,4,5,6},
  {1,3,7}, {0,3,6,7}, {4,6,7}, {2,4,8}, {0,7,8}, {1,4,7,8},
  {0,3,9}, {2,5,9}, {1,3,5,9}, {1,8,9}, {0,2,8,9}]
lemma mergeRows_independent : ∀ r, independent (mergeRows r) := by
  unfold independent
  decide +kernel

def mergeHalf (n : ℕ) : H := (⟨(n / 2) % 15, Nat.mod_lt _ (by decide)⟩, n.testBit 0)
def mergeVertex (z : ℕ) : V := ⟨(z / 3) % 10, Nat.mod_lt _ (by decide)⟩
def mergeFirst (z : ℕ) : ℕ := (z / 30) % 30
def mergeSecond (z : ℕ) : ℕ := (z / 900) % 30
def mergeThird (z : ℕ) : ℕ := (z / 27000) % 30
def mergeRow (z : ℕ) : Fin 15 := ⟨(z / 810000) % 15, Nat.mod_lt _ (by decide)⟩
def mergeWitness (z : ℕ) : Fin 3 → H :=
  ![mergeHalf (mergeFirst z), mergeHalf (mergeSecond z), mergeHalf (mergeThird z)]

def MergeCheck (q : V → Fin 4) (f : H → Fin 30) (a b : H) (z : ℕ) : Prop :=
  let v := mergeVertex z
  if z % 3 = 0 then
    let i : Fin 3 := ⟨mergeFirst z % 3, Nat.mod_lt _ (by decide)⟩
    let j : Fin 3 := ⟨mergeSecond z % 3, Nat.mod_lt _ (by decide)⟩
    block (q v) i ≠ block (q v) j ∧ mergeRel f a b (around v i) (around v j)
  else if z % 3 = 1 then
    let h := mergeHalf (mergeFirst z)
    let k := mergeHalf (mergeSecond z)
    endpoint k = endpoint h ∧ mergeRel f a b k (barH h)
  else
    q v ≠ 3 ∧ touches v (mergeRows (mergeRow z)) ∧
      ∀ i : Fin 3, endpoint (mergeWitness z i) ∈ mergeRows (mergeRow z) ∧
        mergeRel f a b (mergeWitness z i) (around v i)

lemma mergeCheck_false (t : H → Slot) (ht : Conditions t) (q : V → Fin 4)
    (hq : localCode t = q) (f : H → Fin 30)
    (hf : ∀ h k, f h = f k → t h = t k) (a b : H) (hab : t a = t b)
    (z : ℕ) (hz : MergeCheck q f a b z) : False := by
  have hs := mergeRel_sound t f hf ht.1 a b
  unfold MergeCheck at hz
  dsimp only at hz
  split_ifs at hz with hzero hone
  · apply hz.1
    rw [← hq]
    exact (localCode_exact t _ (ht.2.2.1 _) _ _).mp (hs _ _ hab hz.2)
  · apply ht.2.1 (mergeHalf (mergeFirst z))
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, mergeHalf (mergeSecond z), hz.1, hs _ _ hab hz.2⟩
  · obtain ⟨hn, htouch, hhits⟩ := hz
    have hc : (selected t (mergeVertex z)).card = 2 :=
      card_two_of_code_ne_three t _ (ht.2.2.1 _) (by rw [hq]; exact hn)
    obtain ⟨h, hv, hdis⟩ := ht.2.2.2 _ _ (mergeRows_independent _) htouch hc
    obtain ⟨i, hi⟩ := around_complete _ h hv
    obtain ⟨hmem, hrel⟩ := hhits i
    have hEq := hs _ _ hab hrel
    rw [hi] at hEq
    have hlower : endpoint (mergeWitness z i) ∈ lower t h := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, mergeWitness z i, rfl, hEq⟩
    exact Finset.disjoint_left.mp hdis hlower hmem

def canonicalLabel (f : H → Fin 30) (h : H) : Finset V :=
  Finset.univ.filter fun v => ∃ k : H, endpoint k = v ∧ f k = f h

lemma lower_eq_canonicalLabel (t : H → Slot) (f : H → Fin 30)
    (he : ∀ h k, t h = t k ↔ f h = f k) (h : H) :
    lower t h = canonicalLabel f h := by
  ext v
  simp only [lower, canonicalLabel, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk, heq⟩
    exact ⟨k, hk, (he k h).mp heq⟩
  · rintro ⟨k, hk, heq⟩
    exact ⟨k, hk, (he k h).mpr heq⟩

end FiniteSlots

namespace NonlocalMerge
open PEqualNP.Outside.L_meta_2590.FiniteSlots
open PEqualNP.Outside.L_meta_2590.SlotTables

def repData : Fin 45 → ℕ := ![
  0x31f192906242420,
  0x216b431c6242420,
  0xbd8438c020,
  0x216b431c6208109,
  0xbd84331c8508109,
  0x837a7b909,
  0x216b431c625a820,
  0x73c438c2b45a820,
  0x73c438c14bad020,
  0x73c438c39d52c20,
  0x1cf10e3052c20,
  0x7192916a,
  0xbd8434a08539820,
  0xbd8439c8e621420,
  0x2f610cc721420,
  0x31f192900118909,
  0x31f19291ac00509,
  0xc7c64a400509,
  0x85ad0c718820,
  0xa5528398a400462,
  0x839d9c862,
  0x9cb19292306b001,
  0x9c98dde8a48c001,
  0x9cb19634a48c001,
  0x272634a48c001,
  0x6b4399ac,
  0xa55283984329001,
  0xa5528399ee10c01,
  0x2954a0e610c01,
  0x837a4a0e610ca4,
  0xa56720814b7b843,
  0x73e720814bad043,
  0xbda72081ee52c43,
  0x1cf9c82052c43,
  0x837a4a08539843,
  0x837a4a23021443,
  0x20de92821443,
  0x77a6354b8c085,
  0x6306379d52c85,
  0x58ddea3052c85,
  0x18c18d52c85,
  0xbd98d005ee9c8e6,
  0x9cb19634017b8e6,
  0xbda72634017b8e6,
  0x272634017b8e6]

def certData : Fin 45 → ℕ := ![
  0x15cd00072300039c00039c00072300573100038d000399235e4a2d9ad900039900038d2d9ad9235e4a000e894fb2f970185500596b000396000e6b00038a7018554fb2f900039600596b00038a000e6b0007450003930003906a427046cd9041a2ba1d688246a3603a20a400039000039346cd906a42701d688241a2ba3a20a446a360001d116fab5962e24dad094e4675b83dcddeb51f9f000727000387000384001fa562e24d6fab594675b8ad094eb51f9f3dcdde000387000727001fa5000384000001,
  0xe890007200003990003990007200048a900039f00038d50a2092faa3100038d00039f2faa3150a2090015cd00038a0003966a1fba9e1dc4856400767a2600039600038a9e1dc46a1fba767a268564000007451d688241a2ba00479b000393001cf3000390767a446a1e5241a2ba1d688200039300479b000390001cf36a1e52767a44001d11ad4bb73dcdde9664496faa8d756fe916abc1000727000387000384001fa53dcddead4bb76faa8d96644916abc1756fe9000387000727001fa5000384000001,
  0x4fed00000000000000000000000000039f00071d00000000000000000000000000071d00039f000745000000000000000000000000536f3991b38900039c00071100000000000000000000000091b389536f3900071100039c003a21000000000000000000000000324cce900e180003870003841adaee620504000000000000000000000000900e18324cce0003840003876205041adaee000001,
  0xe890007200003990003990007200048a900039f00038d50a2092faa3100038d00039f2faa3150a2090015cd00038a000396213d1f9e1dc42810631b475700039600038a9e1dc4213d1f1b47572810630007451d68823dcdde00479b0003932f8a8d16abc10007270003873dcdde1d688200039300479b16abc12f8a8d0003870007270000014d91ce41a2ba2f800d72a49f001cf3000390767a44287d5f000384001fa541a2ba4d91ce72a49f2f800d000390001cf3287d5f767a44001fa5000384001d11,
  0x4fed00039600071d00071d00039600074500039f0053171b475728106300531700039f2810631b47570015cd9ce15c1e6caa00039c00038a0015af00038d1e6caa9ce15c00038a00039c00038d0015af000e89b88a2b4431ad000387000393442fcd508bfb620381442faf4431adb88a2b000393000387508bfb442fcd442faf620381000001ae655a085bec287d5f72c50c001cf3000390085be043489a000384001fa5085becae655a72c50c287d5f000390001cf343489a085be0001fa5000384001d11,
  0x100000000000000000000000000071a00039c00000000000000000000000000039c00071a005e7500000000000000000000000000070e000399239d926e003000000000000000000000000000039900070e6e0030239d920032dd0000000000000000000000000003840003901e702858202026822c3a4e4c0000000000000000000000000003900003845820201e70283a4e4c26822c001d11,
  0xe890007200003990003990007200048a900039f00038d50a2092faa3100038d00039f2faa3150a2090015cd00038a0003962d98d5531a01281009767a2600039600038a531a012d98d5767a262810090007451d6882420fb600479b0003932f8a8d16cee99e1cb629c3f9420fb61d688200039300479b16cee92f8a8d29c3f99e1cb60024554d91ce3dcdde2f800d16abcd001cf30003900007270003870007080023293dcdde4d91ce16abcd2f800d000390001cf3000387000727002329000708000001,
  0x32dd00039f00070e00070e00039f0007457656fe1f7ee200071a0007111f7ee27656fe00071100071a003a21004b97000399531a012d98d500072000646f000399004b972d98d5531a0100646f0007200048a904a19e421a4229c3f99df286b16ca1048f7700479b000393421a4204a19e9df28629c3f9048f77b16ca100039300479b0024557dbc433fef03000387000390b521971adaf13fefb71adb690007080023293fef037dbc430003900003871adaf1b521971adb693fefb7002329000708000001,
  0x32dd00039f00070e00070e00039f0007457656fe1f7ee200071a0007111f7ee27656fe00071100071a003a21421a4204a19e6270f529c3f900072000646f04a19e421a4229c3f96270f500646f000720002455004b97000399531a012d98d50844af77eab700039300479b000399004b972d98d5531a0177eab70844af00479b0003930048a97afc3062406e000387000390b52197624b540023290007083fefb77b11fc62406e7afc30000390000387624b54b521970007080023297b11fc3fefb7000001,
  0x32dd00039f00070e00070e00039f0007457656fe1f7ee200071a0007111f7ee27656fe00071100071a003a217adf260c0c0e6270f5316db100072000646f0c0c0e7adf26316db16270f500646f0007200065b9004b97000399531a0129c3f9048f7777eab700071700673f000399004b9729c3f9531a0177eab7048f7700673f0007170024553a4d983fef030003870003903a513a78212cb522e17849220023290007083fef033a4d9800039000038778212c3a513a784922b522e1000708002329000001,
  0x32dd00000000000000039f00070e00000000000000070e00039f0007450000000000007656fe1f7ee200071a0007110000000000001f7ee27656fe00071100071a003a21000000000000004b97000399531a0129c3f900072000646f000000000000000399004b9729c3f9531a0100646f0007200024550000000000003a4d9862406e0003870003903a513a624b5400232900070800000000000062406e3a4d98000390000387624b543a513a000708002329000001,
  0x100000000000000000000000000072300039600000000000000000000000000039600072300573100000000000000000000000000038d00038a1b89907bed0800000000000000000000000000038a00038d7bed081b8990000e89000000000000000000000000000393000708231aa691e2d826c4f81add4600000000000000000000000000070800039391e2d8231aa61add4626c4f8002455,
  0x4fed00039600071d00071d00039600074500039f005317900cb3287d5f00531700039f287d5f900cb3001d119ce15c1e6caa00039c00038a43489a085be01e6caa9ce15c00038a00039c085be043489a000e899ca5a40858682810631b4757001cf300039000038d0015af0858689ca5a41b4757281063000390001cf30015af00038d0015cdb88a2b91b3f8000387000393001fa500038496a37c89ddd6970d12442fcd91b3f8b88a2b000393000387000384001fa589ddd696a37c442fcd970d12000001,
  0x4fed00039600071d00071d00039600074500039f005317900cb32cbf3700531700039f2cbf37900cb30041659ca5a40858682810631b475700401b0007140858689ca5a41b475728106300071400401b0015cd9ce15c1e6caa00039c00038a9cd34c087f0800038d0015af1e6caa9ce15c00038a00039c087f089cd34c0015af00038d000e89231ce09de254000387000393b889b39c3bfc000384001fa51add28442faf9de254231ce00003930003879c3bfcb889b3001fa5000384442faf1add28000001,
  0x4fed00000000000000039600071d00000000000000071d00039600074500000000000000039f0053171b475728106300000000000000531700039f2810631b47570015cd0000000000009ce15c1e6caa00039c00038a0015af00038d0000000000001e6caa9ce15c00038a00039c00038d0015af000e89000000000000231ce091b3f8000387000393001fa50003841add2889ddd600000000000091b3f8231ce0000393000387000384001fa589ddd61add28000001,
  0x15cd00072300039c00039c00072300573100038d000399900e3f2d9ad900039900038d2d9ad9900e3f000e894fb2f96fab5900596b0003962d99710883d96fab594fb2f900039600596b0883d92d9971000001954aa67018552801f0ae4fe8000e6b00038a000387000727701855954aa6ae4fe82801f000038a000e6b000727000387000745000393000390235e4446cd9026c9a81ada94001fa5000384b41670265cac00039000039346cd90235e441ada9426c9a8000384001fa5265cacb41670001d11,
  0x15cd00072300039c00039c00072300573100038d0003994870f46e5f1c00039900038d6e5f1c4870f4000e894fb2f9745a2d00596b0003962d9971435524745a2d4fb2f900039600596b4355242d9971002b9962e24d6fab592801f002e6b8000e6b00038a00070b002a4f6fab5962e24d02e6b82801f000038a000e6b002a4f00070b0000010003930003902fb92862036026c87cb520ad46a3602a9d58001fa50003840003900003936203602fb928b520ad26c87c2a9d5846a360000384001fa5001d11,
  0x15cd00000000000000072300039c00000000000000039c00072300573100000000000000038d000399235e4a6e5f1c00000000000000039900038d6e5f1c235e4a000e890000000000004fb2f96fab5900596b000396000e6b00038a0000000000006fab594fb2f900039600596b00038a000e6b000001000000000000000393000390235e4462036026c87c1ada94001fa5000384000000000000000390000393620360235e441ada9426c87c000384001fa5001d11,
  0xe890000000000000007200003990000000000000003990007200048a900000000000000039f00038d50a2092faa3100000000000000038d00039f2faa3150a2090015cd00000000000000038a000396213d1f531a012810091b475700000000000000039600038a531a01213d1f1b47572810090007450000000000001d68823dcdde00479b000393001cf30003900007270003870000000000003dcdde1d688200039300479b000390001cf3000387000727000001,
  0x48a900039f00039300039300039f001d11531ad948737000039c000390487370531ad900039000039c0015cd004b970003991ada9426c9a80015af00038d000399004b9726c9a81ada9400038d0015af000e89900dbe7abd9c0003840003966203d89c682a7abce862037e7abd9c900dbe0003960003849c682a6203d862037e7abce800000116b653729059265cacae51e070185598ffde000e6b00038a00038700072772905916b653ae51e0265cac98ffde70185500038a000e6b000727000387000745,
  0x10000000000000000000000000007200007170000000000000000000000000007170007200065b900000000000000000000000000039f00071424d2bc6ea77000000000000000000000000000071400039f6ea77024d2bc00416500000000000000000000000000038a0003871da78b588d3d26f9d58557eb00000000000000000000000000038700038a588d3d1da78b8557eb26f9d5000745,
  0x416500072300569b00569b00072300573100071400071d6203602fb92800071d0007142fb928620360000e8951c959b4fd8500039c0060eb000717000711b4fd8551c9590060eb00039c000711000717003a21996a6411c5be00596b0003962a9d584355247464b911d7e511c5be996a6400039600596b4355242a9d5811d7e57464b9002b999673e83393c275a2801adbfc00038400038a75a1541adaee00070b002a4f3393c29673e81adbfc75a28000038a0003841adaee75a154002a4f00070b000001,
  0x416500072300569b00569b000723002b991720d6b8371e00071a005cefb8371e1720d6005cef00071a005e7500071400071d922cac2a9d5862036030262400071d0007142a9d58922cac302624620360000e8951c959b4fd8511d7e57464b900039c0060eb000717000711b4fd8551c9597464b911d7e50060eb00039c000711000717003a219673e83393c2002a4f00070b75a2801adc1a00038400038a75a1541adaee3393c29673e800070b002a4f1adc1a75a28000038a0003841adaee75a154000001,
  0x416500072300569b00569b00072300573111c5be996a6400039600596b996a6411c5be00596b000396002b9900071400071d922cac2fb9286203602a9d5800071d0007142fb928922cac2a9d58620360000e8951c959b4fd8516c985b70cdd00039c0060eb000717000711b4fd8551c959b70cdd16c9850060eb00039c000711000717003a219673e83393c296747e1adbfc002a4f00070b00038400038a75a1541adaee3393c29673e81adbfc96747e00070b002a4f00038a0003841adaee75a154000001,
  0x416500000000000000072300569b00000000000000569b000723002b9900000000000000071400071d6203602a9d5800000000000000071d0007142a9d58620360000e8900000000000051c959b4fd8500039c0060eb000717000711000000000000b4fd8551c9590060eb00039c000711000717003a210000000000009673e83393c2002a4f00070b00038400038a75a1541adaee0000000000003393c29673e800070b002a4f00038a0003841adaee75a154000001,
  0x10000000000000000000000000003930003990000000000000000000000000003990003930048a900000000000000000000000000038d00039000aff14dbeef00000000000000000000000000039000038d4dbeef00aff10015cd00000000000000000000000000070b0003962107af4685571b431f28138d00000000000000000000000000039600070b4685572107af28138d1b431f002b99,
  0x48a900039f00039300039300039f001d111d695a48737000039c0003904873701d695a00039000039c0015cd004b97000399508cac265cac4872bc170114000399004b97265cac508cac1701144872bc000745482d9b16b9d71ada9426c9a80015af00038d00038a000e6b16b9d7482d9b26c9a81ada9400038d0015af000e6b00038a000e89900dbe7abd9c0003840003966203d89c682a0007270003879c680c62037e7abd9c900dbe0003960003849c682a6203d800038700072762037e9c680c000001,
  0x48a900039f00039300039300039f001d11782d830883f700039c0003900883f7782d8300039000039c0015cd004b97000399508cac2b0b804872bc759f9b000399004b972b0b80508cac759f9b4872bc0032dd482d9b16b6531ada94265cac0015af00038d00070e00319316b653482d9b265cac1ada9400038d0015af00319300070e000745900dbe7abd9c0003840003966203d89c682a7abce86204aa0007270003877abd9c900dbe0003960003849c682a6203d86204aa7abce8000387000727000001,
  0x48a900000000000000039f00039300000000000000039300039f001d11000000000000531ad90883f700039c0003900000000000000883f7531ad900039000039c0015cd000000000000004b970003991ada94265cac0015af00038d000000000000000399004b97265cac1ada9400038d0015af000745000000000000900dbe7abd9c0003840003966203d89c682a0007270003870000000000007abd9c900dbe0003960003849c682a6203d8000387000727000001,
  0x100071a00071700071700071a005e7500039f0003847844cc1e702800038400039f1e70287844cc001d11970d12a7f29400039c0060eb001cf3000390a7f294970d120060eb00039c000390001cf30015cd000387000399b6e44b1d9cff3a20982a7b5c29b6431d56af0003990003871d9cffb6e44b2a7b5c3a20981d56af29b64300074589ddd696a37caf025f33834b1e26542a7ee00015af00038d00038a000e6b96a37c89ddd633834baf025f2a7ee01e265400038d0015af000e6b00038a000e89,
  0x48a900039f00531700531700039f0041657b11fcac8980000396000714ac89807b11fc00071400039600000100479b0003939c3a76231aa600072000070800039300479b231aa69c3a76000708000720002455004b97000399b30b4037a1f862406e7afc3037b4162b07fc000399004b9737a1f8b30b407afc3062406e2b07fc37b4160032dd283d9f4d5553b44ea728369700038700038d1add46267fd400070e0031934d5553283d9f283697b44ea700038d000387267fd41add4600319300070e000745,
  0x32dd00039f00531700531700039f0041657afc3062406e00039600071462406e7afc300007140003960000012b07fc37b4169c3a76231aa600072000070837b4162b07fc231aa69c3a76000708000720002455004b970003999c91d03a1ac84687377b11fc00039300479b000399004b973a1ac89c91d07b11fc46873700479b0003930048a900319300070eb44ea728369700038700038d1add46267fd44d5553283d9f00070e003193283697b44ea700038d000387267fd41add46283d9f4d5553000745,
  0x4fed00039f00531700531700039f0041657b159eac8980000396000714ac89807b159e000714000396000001004f1b00071d9c91d037a1f862406e7afc3000071d004f1b37a1f89c91d07afc3062406e0032dd9de0563a965e9c3a76231aa600072000070800039300479b3a965e9de056231aa69c3a7600070800072000479b000393002455b45cb74d58d7b44ea728369700038700038d00070e0031931add46267fd44d58d7b45cb7283697b44ea700038d00038700319300070e267fd41add46000745,
  0x32dd00000000000000039f00531700000000000000531700039f0041650000000000007afc3062406e00039600071400000000000062406e7afc3000071400039600000100000000000000479b0003939c3a76231aa600072000070800000000000000039300479b231aa69c3a7600070800072000245500000000000000319300070eb44ea728369700038700038d1add46267fd400000000000000070e003193283697b44ea700038d000387267fd41add46000745,
  0x100071a00071700071700071a005e7500039f0003847844cc1e702800038400039f1e70287844cc001d1196a37c89ddd600039c0060eb2a7ee01e265489ddd696a37c0060eb00039c1e26542a7ee0000e89970d12407a9533ecc372228b001cf300039000038d0015af407a95970d1272228b33ecc3000390001cf30015af00038d0015cd000387000399b6e44b1d9cff3a20982a7b5c000e6b00038a29b6431d56af0003990003871d9cffb6e44b2a7b5c3a209800038a000e6b1d56af29b643000745,
  0x100071a00071700071700071a005e7500039f0003847844cc1e702800038400039f1e70287844cc001d119b2ceea7f29400039c0060eb7821a41e4d00a7f2949b2cee0060eb00039c1e4d007821a4003a2196a37c89ddd633834b72228b001cf30003900007110038d789ddd696a37c72228b33834b000390001cf30038d7000711000e89000387000399b6e44b1d9cff3a20982a7b5cb6c1231d79d7000e6b00038a0003990003871d9cffb6e44b2a7b5c3a20981d79d7b6c12300038a000e6b000745,
  0x100000000000000071a00071700000000000000071700071a005e7500000000000000039f0003847844cc1e702800000000000000038400039f1e70287844cc001d1100000000000096a37c89ddd600039c0060eb001cf300039000000000000089ddd696a37c0060eb00039c000390001cf3000e89000000000000000387000399b6e44b1d9cff3a20982a7b5c000e6b00038a0000000000000003990003871d9cffb6e44b2a7b5c3a209800038a000e6b000745,
  0x1784580532dae532dae784580005e7500072300070b00071a005cef00070b000723005cef00071a002b9900070800039900071700673f91e2d82a7a3000039900070800673f0007172a7a3091e2d800245578212c3a513a00039c0060eb5da27d449a535d90509b2d483a513a78212c0060eb00039c449a535da27d9b2d485d9050003a2100038a000390633f743e27c026d72540122b26c4f896a5200007110038d700039000038a3e27c0633f7440122b26d72596a52026c4f80038d7000711000e89,
  0x178212c3a513a3a513a78212c003a2100072300070b00071a005cef00070b000723005cef00071a002b99784922b751dd00072000646f622aa53123ddb751dd78492200646f0007203123dd622aa50065b90007080003995d90502fd54891e2d82a7a3000071700673f0003990007082fd5485d90502a7a3091e2d800673f00071700245500038a0003900007110038d726d72540122b6342f89c8cde26c4f896a52000039000038a0038d700071140122b26d7259c8cde6342f896a52026c4f8000e89,
  0x100072300070b00070b000723002b99784580532dae00071a005cef532dae784580005cef00071a005e7578212c3a513a5da27d3123dd00039c0060eb3a513a78212c3123dd5da27d0060eb00039c003a2100070800039991e2d82a7a3061af002fd54800071700673f0003990007082a7a3091e2d82fd54861af0000673f00071700245500038a00039026d72540122b633f743e27c00007110038d726c4f896a52000039000038a40122b26d7253e27c0633f740038d700071196a52026c4f8000e89,
  0x100000000000078212c3a513a0000000000003a513a78212c003a2100000000000000072300070b00071a005cef00000000000000070b000723005cef00071a002b9900000000000000070800039900071700673f91e2d82a7a3000000000000000039900070800673f0007172a7a3091e2d800245500000000000000038a0003900007110038d726d72540122b26c4f896a52000000000000000039000038a0038d700071140122b26d72596a52026c4f8000e89,
  0x4fed00039600596b00596b000396002b999de254231ce000039c00070b231ce09de25400070b00039c000001004f1b00071d440c872107af00039300070e00071d004f1b2107af440c8700070e0003930032dd00039f005317837eb72ca69b9c3bfcb86d9376e4ca836c9000531700039f2ca69b837eb7b86d939c3bfc836c9076e4ca00416526a8d8898250267ea858202000038d00038426822c76744400401b00071489825026a8d8582020267ea800038400038d76744426822c00071400401b0015cd,
  0x416500072300569b00569b000723005731837eb72ca69b00039600596b2ca69b837eb700596b000396002b999c3bfc3a983e9e4bea231ce000039c00070b3a983e9c3bfc231ce09e4bea00070b00039c000001004f1b00071d481910857be8440c872107af00039300070e00071d004f1b857be84819102107af440c8700070e0003930032dd00401b00071426a8d88985d4267ea858202000038d00038426822c76744400071400401b8985d426a8d8582020267ea800038400038d76744426822c0015cd,
  0x4fed00039f00531700531700039f00416585249746eecf00039600596b46eecf85249700596b000396002b999de2543a983e9c3bfc231ce000039c00070b3a983e9de254231ce09c3bfc00070b00039c000001004f1b00071d481910836c90440c872107af00039300070e00071d004f1b836c904819102107af440c8700070e0003930032dd768ce089825000401b000714267ea858202000038d00038426822c767444898250768ce000071400401b582020267ea800038400038d76744426822c0015cd,
  0x416500000000000000039600596b00000000000000596b000396002b990000000000009c3bfc231ce000039c00070b000000000000231ce09c3bfc00070b00039c000001000000000000004f1b00071d440c872107af00039300070e00000000000000071d004f1b2107af440c8700070e0003930032dd00000000000000401b000714267ea858202000038d00038426822c76744400000000000000071400401b582020267ea800038400038d76744426822c0015cd]

def mergeRep (p : Fin 45) (a : Fin 30) : H :=
  mergeHalf ((Nat.shiftRight (repData p) (5 * a.val)) % 32)

def certificate (p : Fin 45) (a b : Fin 30) : ℕ :=
  (Nat.shiftRight (certData p) (24 * (a.val * (23 - a.val) / 2 + b.val - a.val - 1))) % 16777216

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_0 : ∀ h, slot 0 (mergeRep 0 (slot 0 h)) = slot 0 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_1 : ∀ h, slot 1 (mergeRep 1 (slot 1 h)) = slot 1 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_2 : ∀ h, slot 2 (mergeRep 2 (slot 2 h)) = slot 2 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_3 : ∀ h, slot 3 (mergeRep 3 (slot 3 h)) = slot 3 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_4 : ∀ h, slot 4 (mergeRep 4 (slot 4 h)) = slot 4 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_5 : ∀ h, slot 5 (mergeRep 5 (slot 5 h)) = slot 5 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_6 : ∀ h, slot 6 (mergeRep 6 (slot 6 h)) = slot 6 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_7 : ∀ h, slot 7 (mergeRep 7 (slot 7 h)) = slot 7 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_8 : ∀ h, slot 8 (mergeRep 8 (slot 8 h)) = slot 8 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_9 : ∀ h, slot 9 (mergeRep 9 (slot 9 h)) = slot 9 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_10 : ∀ h, slot 10 (mergeRep 10 (slot 10 h)) = slot 10 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_11 : ∀ h, slot 11 (mergeRep 11 (slot 11 h)) = slot 11 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_12 : ∀ h, slot 12 (mergeRep 12 (slot 12 h)) = slot 12 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_13 : ∀ h, slot 13 (mergeRep 13 (slot 13 h)) = slot 13 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_14 : ∀ h, slot 14 (mergeRep 14 (slot 14 h)) = slot 14 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_15 : ∀ h, slot 15 (mergeRep 15 (slot 15 h)) = slot 15 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_16 : ∀ h, slot 16 (mergeRep 16 (slot 16 h)) = slot 16 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_17 : ∀ h, slot 17 (mergeRep 17 (slot 17 h)) = slot 17 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_18 : ∀ h, slot 18 (mergeRep 18 (slot 18 h)) = slot 18 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_19 : ∀ h, slot 19 (mergeRep 19 (slot 19 h)) = slot 19 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_20 : ∀ h, slot 20 (mergeRep 20 (slot 20 h)) = slot 20 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_21 : ∀ h, slot 21 (mergeRep 21 (slot 21 h)) = slot 21 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_22 : ∀ h, slot 22 (mergeRep 22 (slot 22 h)) = slot 22 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_23 : ∀ h, slot 23 (mergeRep 23 (slot 23 h)) = slot 23 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_24 : ∀ h, slot 24 (mergeRep 24 (slot 24 h)) = slot 24 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_25 : ∀ h, slot 25 (mergeRep 25 (slot 25 h)) = slot 25 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_26 : ∀ h, slot 26 (mergeRep 26 (slot 26 h)) = slot 26 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_27 : ∀ h, slot 27 (mergeRep 27 (slot 27 h)) = slot 27 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_28 : ∀ h, slot 28 (mergeRep 28 (slot 28 h)) = slot 28 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_29 : ∀ h, slot 29 (mergeRep 29 (slot 29 h)) = slot 29 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_30 : ∀ h, slot 30 (mergeRep 30 (slot 30 h)) = slot 30 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_31 : ∀ h, slot 31 (mergeRep 31 (slot 31 h)) = slot 31 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_32 : ∀ h, slot 32 (mergeRep 32 (slot 32 h)) = slot 32 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_33 : ∀ h, slot 33 (mergeRep 33 (slot 33 h)) = slot 33 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_34 : ∀ h, slot 34 (mergeRep 34 (slot 34 h)) = slot 34 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_35 : ∀ h, slot 35 (mergeRep 35 (slot 35 h)) = slot 35 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_36 : ∀ h, slot 36 (mergeRep 36 (slot 36 h)) = slot 36 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_37 : ∀ h, slot 37 (mergeRep 37 (slot 37 h)) = slot 37 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_38 : ∀ h, slot 38 (mergeRep 38 (slot 38 h)) = slot 38 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_39 : ∀ h, slot 39 (mergeRep 39 (slot 39 h)) = slot 39 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_40 : ∀ h, slot 40 (mergeRep 40 (slot 40 h)) = slot 40 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_41 : ∀ h, slot 41 (mergeRep 41 (slot 41 h)) = slot 41 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_42 : ∀ h, slot 42 (mergeRep 42 (slot 42 h)) = slot 42 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_43 : ∀ h, slot 43 (mergeRep 43 (slot 43 h)) = slot 43 h := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
lemma rep_slot_44 : ∀ h, slot 44 (mergeRep 44 (slot 44 h)) = slot 44 h := by
  decide +kernel

lemma rep_slot : ∀ p h, slot p (mergeRep p (slot p h)) = slot p h := by
  intro p
  fin_cases p
  · exact rep_slot_0
  · exact rep_slot_1
  · exact rep_slot_2
  · exact rep_slot_3
  · exact rep_slot_4
  · exact rep_slot_5
  · exact rep_slot_6
  · exact rep_slot_7
  · exact rep_slot_8
  · exact rep_slot_9
  · exact rep_slot_10
  · exact rep_slot_11
  · exact rep_slot_12
  · exact rep_slot_13
  · exact rep_slot_14
  · exact rep_slot_15
  · exact rep_slot_16
  · exact rep_slot_17
  · exact rep_slot_18
  · exact rep_slot_19
  · exact rep_slot_20
  · exact rep_slot_21
  · exact rep_slot_22
  · exact rep_slot_23
  · exact rep_slot_24
  · exact rep_slot_25
  · exact rep_slot_26
  · exact rep_slot_27
  · exact rep_slot_28
  · exact rep_slot_29
  · exact rep_slot_30
  · exact rep_slot_31
  · exact rep_slot_32
  · exact rep_slot_33
  · exact rep_slot_34
  · exact rep_slot_35
  · exact rep_slot_36
  · exact rep_slot_37
  · exact rep_slot_38
  · exact rep_slot_39
  · exact rep_slot_40
  · exact rep_slot_41
  · exact rep_slot_42
  · exact rep_slot_43
  · exact rep_slot_44

def ChecksFor (p : Fin 45) : Prop := ∀ a b : Fin 30, a < b →
  slot p (mergeRep p a) = a → slot p (mergeRep p b) = b →
  MergeCheck (code p) (slot p) (mergeRep p a) (mergeRep p b) (certificate p a b)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_0 : ChecksFor 0 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_1 : ChecksFor 1 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_2 : ChecksFor 2 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_3 : ChecksFor 3 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_4 : ChecksFor 4 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_5 : ChecksFor 5 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_6 : ChecksFor 6 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_7 : ChecksFor 7 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_8 : ChecksFor 8 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_9 : ChecksFor 9 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_10 : ChecksFor 10 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_11 : ChecksFor 11 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_12 : ChecksFor 12 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_13 : ChecksFor 13 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_14 : ChecksFor 14 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_15 : ChecksFor 15 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_16 : ChecksFor 16 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_17 : ChecksFor 17 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_18 : ChecksFor 18 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_19 : ChecksFor 19 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_20 : ChecksFor 20 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_21 : ChecksFor 21 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_22 : ChecksFor 22 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_23 : ChecksFor 23 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_24 : ChecksFor 24 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_25 : ChecksFor 25 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_26 : ChecksFor 26 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_27 : ChecksFor 27 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_28 : ChecksFor 28 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_29 : ChecksFor 29 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_30 : ChecksFor 30 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_31 : ChecksFor 31 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_32 : ChecksFor 32 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_33 : ChecksFor 33 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_34 : ChecksFor 34 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_35 : ChecksFor 35 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_36 : ChecksFor 36 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_37 : ChecksFor 37 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_38 : ChecksFor 38 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_39 : ChecksFor 39 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_40 : ChecksFor 40 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_41 : ChecksFor 41 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_42 : ChecksFor 42 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_43 : ChecksFor 43 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
lemma checks_44 : ChecksFor 44 := by
  unfold ChecksFor MergeCheck mergeRel joined touches
  decide +kernel

lemma all_checks : ∀ p, ChecksFor p := by
  intro p
  fin_cases p
  · exact checks_0
  · exact checks_1
  · exact checks_2
  · exact checks_3
  · exact checks_4
  · exact checks_5
  · exact checks_6
  · exact checks_7
  · exact checks_8
  · exact checks_9
  · exact checks_10
  · exact checks_11
  · exact checks_12
  · exact checks_13
  · exact checks_14
  · exact checks_15
  · exact checks_16
  · exact checks_17
  · exact checks_18
  · exact checks_19
  · exact checks_20
  · exact checks_21
  · exact checks_22
  · exact checks_23
  · exact checks_24
  · exact checks_25
  · exact checks_26
  · exact checks_27
  · exact checks_28
  · exact checks_29
  · exact checks_30
  · exact checks_31
  · exact checks_32
  · exact checks_33
  · exact checks_34
  · exact checks_35
  · exact checks_36
  · exact checks_37
  · exact checks_38
  · exact checks_39
  · exact checks_40
  · exact checks_41
  · exact checks_42
  · exact checks_43
  · exact checks_44

lemma actual_eq_iff_slot (t : H → Slot) (ht : Conditions t) (p : Fin 45)
    (hclosed : ∀ h k, closed (code p) h k ↔ slot p h = slot p k)
    (hq : localCode t = code p) (h k : H) : t h = t k ↔ slot p h = slot p k := by
  have hf (a b : H) (hab : slot p a = slot p b) : t a = t b := by
    apply closed_sound t ht.1 ht.2.2.1
    rw [hq]
    exact (hclosed a b).mpr hab
  constructor
  · intro heq
    by_contra hne
    have hrep (a : H) : t (mergeRep p (slot p a)) = t a := hf _ _ (rep_slot p a)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact mergeCheck_false t ht (code p) hq (slot p) hf _ _
        ((hrep h).trans (heq.trans (hrep k).symm)) _
        (all_checks p (slot p h) (slot p k) hlt (rep_slot p h) (rep_slot p k))
    · exact mergeCheck_false t ht (code p) hq (slot p) hf _ _
        ((hrep k).trans (heq.symm.trans (hrep h).symm)) _
        (all_checks p (slot p k) (slot p h) hgt (rep_slot p k) (rep_slot p h))
  · exact hf h k

def classLabel (p : Fin 45) (h : H) : Finset V := canonicalLabel (slot p) h

lemma lower_eq_label (t : H → Slot) (ht : Conditions t) (p : Fin 45)
    (hclosed : ∀ h k, closed (code p) h k ↔ slot p h = slot p k)
    (hq : localCode t = code p) (h : H) : lower t h = classLabel p h :=
  lower_eq_canonicalLabel t (slot p) (actual_eq_iff_slot t ht p hclosed hq) h

end NonlocalMerge

namespace SlotLabels

open FiniteSlots

def maskWord : Fin 45 → ℕ := ![717044977533379493273861595016988673, 1002367299225542016166459398851397633, 604611505078938005145601, 1002367299225542016166459383819026433, 664857864774063428997499861655896065, 654588766363988812382209, 1002367299225542016166459381671544833, 669969200334374568157590724444964865, 669969200334374568014601539387672577, 669969200334374568013475640554571777, 638932419142126625212399110145, 733611447441494013673473, 664857864774055164856154820456777729, 664857864774053983989815887280506881, 634057869695725068654175356929, 717044977533379493270483848052916225, 717044977533379493269357949219815425, 683827378781680577540385718273, 955931948876897827307185555457, 706315584149176803395142971679576066, 970678337718248364052482, 664797490394374026405337395353359362, 664797175957744552022702309626614786, 664797173481866834635183194650973186, 634000294561628441787813073922, 912885697341100285558786, 706315584149176803388387511037395970, 706315584149176803386135713371194370, 673595031880547336003680011266, 708993494785160617563682203657838596, 706315265959903517084148165983086596, 669969187950159723684434691707906052, 664776891091624895910667643955193860, 678546488588751167977026496516, 708993494785160617550171282373478404, 708993494785160617545667687041075204, 676148886475716226165948680196, 671289762982573626245841535656546312, 671289762953559406718079587292565512, 671290082332113543151137181845704712, 640191805832142861178167644168, 664857706273911327560303846415679497, 664797173481866834774783650540044297, 664776891091605996218193770084057097, 634077061351313571196295987209]

def mask (i : Fin 45) (s : Fin 30) : ℕ := (maskWord i / (2 ^ (10 * s.val))) % 1024

def maskSet (m : ℕ) : Finset V := Finset.univ.filter fun v => m.testBit v.val

def label (i : Fin 45) (s : Fin 30) : Finset V :=
  Finset.univ.filter fun v => ∃ h : H, endpoint h = v ∧ SlotTables.slot i h = s

abbrev LabelMatches (i : Fin 45) : Prop := ∀ (s : Fin 30) (v : V),
    (∃ h : H, endpoint h = v ∧ SlotTables.slot i h = s) ↔
      (mask i s).testBit v.val = true

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma labels_checked0 : ∀ j : Fin 9, LabelMatches ⟨0 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma labels_checked1 : ∀ j : Fin 9, LabelMatches ⟨9 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma labels_checked2 : ∀ j : Fin 9, LabelMatches ⟨18 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma labels_checked3 : ∀ j : Fin 9, LabelMatches ⟨27 + j.val, by omega⟩ := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma labels_checked4 : ∀ j : Fin 9, LabelMatches ⟨36 + j.val, by omega⟩ := by
  decide +kernel

lemma labels_checked (i : Fin 45) : LabelMatches i := by
  fin_cases i
  · exact labels_checked0 0
  · exact labels_checked0 1
  · exact labels_checked0 2
  · exact labels_checked0 3
  · exact labels_checked0 4
  · exact labels_checked0 5
  · exact labels_checked0 6
  · exact labels_checked0 7
  · exact labels_checked0 8
  · exact labels_checked1 0
  · exact labels_checked1 1
  · exact labels_checked1 2
  · exact labels_checked1 3
  · exact labels_checked1 4
  · exact labels_checked1 5
  · exact labels_checked1 6
  · exact labels_checked1 7
  · exact labels_checked1 8
  · exact labels_checked2 0
  · exact labels_checked2 1
  · exact labels_checked2 2
  · exact labels_checked2 3
  · exact labels_checked2 4
  · exact labels_checked2 5
  · exact labels_checked2 6
  · exact labels_checked2 7
  · exact labels_checked2 8
  · exact labels_checked3 0
  · exact labels_checked3 1
  · exact labels_checked3 2
  · exact labels_checked3 3
  · exact labels_checked3 4
  · exact labels_checked3 5
  · exact labels_checked3 6
  · exact labels_checked3 7
  · exact labels_checked3 8
  · exact labels_checked4 0
  · exact labels_checked4 1
  · exact labels_checked4 2
  · exact labels_checked4 3
  · exact labels_checked4 4
  · exact labels_checked4 5
  · exact labels_checked4 6
  · exact labels_checked4 7
  · exact labels_checked4 8

lemma label_eq_mask (i : Fin 45) (s : Fin 30) : label i s = maskSet (mask i s) := by
  ext v
  simp only [label, maskSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact labels_checked i s v

end SlotLabels

namespace SlotLabels

end SlotLabels

namespace SlotOrbits

open FiniteSlots

def word : Fin 45 → ℕ := ![105043959308623874, 104969483439309342, 1016437415936, 105043376338371210, 58393590189269218, 596667025024, 104819952128796798, 85978298829530330, 28557403578642670, 85977711937907906, 186024800087141, 725516043896, 58393586762330342, 20112277620452554, 78272031943793, 105043375186701410, 104819948213824694, 334977050895389, 335267972259841, 85978427682988230, 723247694432, 58170165482775806, 58168577991586042, 19706175202210034, 77108366715049, 593246998148, 85977843561065694, 28557821711281386, 186027585070177, 104936499226878074, 47515898312942722, 47515894890442886, 641515830438946, 35490131143697, 104935623047196814, 104786962864991258, 334555003284485, 104861733572600838, 104861730154540134, 104818782273334450, 334262958842905, 39179399506970226, 38879166909584042, 9160243775196690, 2925682675233]

def canonical (i : Fin 45) : Fin 45 :=
  if word i % 4 = 0 then 2 else if word i % 4 = 1 then 18 else 0

def vertexPerm (i : Fin 45) : Fin 120 := ⟨((word i / 4) % 128) % 120, by omega⟩

def rename (i : Fin 45) (s : Fin 30) : Fin 30 :=
  if s.val < 2 * (4 + word i % 4) then
    ⟨((word i / 512) / (2 ^ (4 * s.val))) % 16, by omega⟩
  else s

def flip (s : Fin 30) : Fin 30 := ⟨2 * (s.val / 2) + (1 - s.val % 2), by omega⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma rename_injective : ∀ i : Fin 45, Function.Injective (rename i) := by
  unfold Function.Injective
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma rename_flip : ∀ (i : Fin 45) (s : Fin 30), rename i (flip s) = flip (rename i s) := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma masks_permuted : ∀ (i : Fin 45) (s : Fin 30) (v : V),
    (SlotLabels.mask i s).testBit v.val =
      (SlotLabels.mask (canonical i) (rename i s)).testBit (Petersen.permV (vertexPerm i) v).val := by
  decide +kernel

lemma maskSet_image (i : Fin 45) (s : Fin 30) :
    (SlotLabels.maskSet (SlotLabels.mask i s)).image (Petersen.permEquiv (vertexPerm i)) =
      SlotLabels.maskSet (SlotLabels.mask (canonical i) (rename i s)) := by
  ext u
  obtain ⟨v, rfl⟩ := (Petersen.permEquiv (vertexPerm i)).surjective u
  have hh : Petersen.permEquiv (vertexPerm i) v ∈
      (SlotLabels.maskSet (SlotLabels.mask i s)).image (Petersen.permEquiv (vertexPerm i)) ↔
      v ∈ SlotLabels.maskSet (SlotLabels.mask i s) := by simp
  rw [hh]
  simpa [SlotLabels.maskSet, Petersen.permEquiv] using
    congrArg (· = true) (masks_permuted i s v)

end SlotOrbits

namespace FiniteSlots

lemma classified_selected (t : H → Slot) (ht : Conditions t) :
    ∃ i : Fin 45, localCode t = SlotTables.code i ∧
      (∀ h k, t h = t k ↔ SlotTables.slot i h = SlotTables.slot i k) ∧
      ∀ h, lower t h = SlotLabels.label i (SlotTables.slot i h) := by
  obtain ⟨i, hi⟩ := SlotTree.conditions_classified t ht
  refine ⟨i, hi, ?_, ?_⟩
  · exact NonlocalMerge.actual_eq_iff_slot t ht i (SlotTables.closed_iff_slot i) hi
  · intro h
    exact NonlocalMerge.lower_eq_label t ht i (SlotTables.closed_iff_slot i) hi h

end FiniteSlots


namespace TopFormFinite

abbrev V := Fin 10
abbrev I := Fin 15
def ends : I → V × V := ![(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
abbrev independent (X : Finset V) : Prop :=
  ∀ i : I, ¬ ((ends i).1 ∈ X ∧ (ends i).2 ∈ X)

end TopFormFinite

namespace DagTools
lemma h9_all_eligible_budget {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hall : eligSet n D = Finset.univ) (hlen : D.length + 1 ≤ 2 * n) :
    Bplus n D = n ∧ Bzero n D = 0 ∧ D.length + 1 = 2 * n := by
  obtain ⟨b, hb⟩ := sem_exists_pureBranch hG h.1 hC
  have hlo := elig_le_Bplus h.1 b hb
  rw [hall, Finset.card_univ, Fintype.card_fin] at hlo
  have hs := surplus_identity h
  have hsplit := totalSurplus_split n D
  omega
end DagTools

namespace DagTools.I0Selected

open FiniteSlots FourGroupGeometry

set_option maxRecDepth 12000 in
lemma edge_adj : ∀ e : Fin 15, adj (FiniteSlots.edges e).1 (FiniteSlots.edges e).2 := by
  unfold adj
  decide +kernel

set_option maxRecDepth 12000 in
lemma adj_edge : ∀ u v : Fin 10, adj u v ↔
    ∃ e : Fin 15, ((FiniteSlots.edges e).1 = u ∧ (FiniteSlots.edges e).2 = v) ∨
      ((FiniteSlots.edges e).1 = v ∧ (FiniteSlots.edges e).2 = u) := by
  unfold adj
  decide +kernel

set_option maxRecDepth 12000 in
lemma port_adj : ∀ h : H, adj (endpoint h) (endpoint (barH h)) := by
  unfold adj
  decide +kernel

lemma selected_exists {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hBp : Bplus 10 D = (eligSet 10 D).card) :
    ∃ t : H → Slot, Conditions t ∧
      (∀ p, t (barH p) = bar (t p)) ∧
      (∀ p, t p ∈ sem_W 10 D (endpoint p)) := by
  classical
  have hex : ∀ e : Fin 15, ∃ p : Slot,
      p ∈ sem_W 10 D (FiniteSlots.edges e).1 ∧
      bar p ∈ sem_W 10 D (FiniteSlots.edges e).2 ∧
      (FiniteSlots.edges e).1 ∉ supp 10 D (src D (bar p)) ∧
      (FiniteSlots.edges e).2 ∉ supp 10 D (src D p) := by
    intro e
    obtain ⟨j, hj, _, _, hu, hv, s, hus, hvs, hvs', hus'⟩ :=
      sem_joint_meeting FourCase.graph h.1 hC (edge_adj e)
    exact ⟨(j,s), sem_mem_W.mpr ⟨hj, hus, hu⟩,
      sem_mem_W.mpr ⟨hj, hvs', hv⟩, hus', hvs⟩
  choose p hp using hex
  let t : H → Slot := fun q => if q.2 then bar (p q.1) else p q.1
  have hb : ∀ q, t (barH q) = bar (t q) := by
    rintro ⟨e, b⟩
    cases b <;> simp [t, barH, bar]
  have hw : ∀ q, t q ∈ sem_W 10 D (endpoint q) := by
    rintro ⟨e, b⟩
    cases b
    · exact (hp e).1
    · exact (hp e).2.1
  refine ⟨t, ?_, hb, hw⟩
  apply conditions_of_exits t (fun s => supp 10 D (src D s)) (sem_W 10 D)
    hb hw
  · intro v s hs
    exact (sem_mem_W.mp hs).2.1
  · rintro ⟨e,b⟩
    cases b
    · exact (hp e).2.2.1
    · simpa [t, barH, bar, endpoint] using (hp e).2.2.2
  · intro v
    have hbudget := h9_exit_budget_tight FourCase.graph h hC hBp v
    omega
  · intro v A hA hv
    have hind : ∀ a ∈ A, ∀ b ∈ A, ¬ adj a b := by
      intro a ha b hb' hab
      obtain ⟨e, he | he⟩ := (adj_edge a b).mp hab
      · exact hA e ⟨he.1.symm ▸ ha, he.2.symm ▸ hb'⟩
      · exact hA e ⟨he.1.symm ▸ hb', he.2.symm ▸ ha⟩
    have hnb : ∃ a ∈ A, adj v a := by
      obtain ⟨q, hq, ha⟩ := hv
      exact ⟨endpoint (barH q), ha, hq ▸ port_adj q⟩
    obtain ⟨j, s, hj, _, hs, hg, hd⟩ :=
      sem_exposure FourCase.graph h.1 hC A hind v hnb
    exact ⟨(j,s), sem_mem_W.mpr ⟨hj, hs, hg⟩, hd⟩

lemma classified_exists {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hBp : Bplus 10 D = (eligSet 10 D).card) :
    ∃ (t : H → Slot) (i : Fin 45),
      (∀ p, t (barH p) = bar (t p)) ∧
      (∀ p, t p ∈ sem_W 10 D (endpoint p)) ∧
      (∀ p q, t p = t q ↔ SlotTables.slot i p = SlotTables.slot i q) := by
  obtain ⟨t, ht, hb, hw⟩ := selected_exists h hC hBp
  obtain ⟨i, _, heq, _⟩ := classified_selected t ht
  exact ⟨t, i, hb, hw, heq⟩

end DagTools.I0Selected

namespace SlotGateIds
open FiniteSlots
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma slot_bar : ∀ (p : Fin 45) (h : H),
    SlotTables.slot p (barH h) = SlotOrbits.flip (SlotTables.slot p h) := by
  decide +kernel
end SlotGateIds

namespace SlotPackages
open FiniteSlots

def index {m : ℕ} (hm : m ≤ 15) (j : Fin m) (s : Bool) : Fin 30 :=
  ⟨2 * j.val + if s then 1 else 0, by cases s <;> simp only [Bool.false_eq_true,
    if_false, if_true] <;> omega⟩

lemma index_flip {m : ℕ} (hm : m ≤ 15) (j : Fin m) :
    SlotOrbits.flip (index hm j false) = index hm j true := by
  apply Fin.ext
  dsimp [SlotOrbits.flip, index]
  omega

lemma index_inj {m : ℕ} (hm : m ≤ 15) {j k : Fin m}
    (h : index hm j false = index hm k false) : j = k := by
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [index] at hv
  omega

lemma index_even_ne_odd {m : ℕ} (hm : m ≤ 15) (j k : Fin m) :
    index hm j false ≠ index hm k true := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [index] at hv
  omega

lemma canonical_packages {m : ℕ} (hm : m ≤ 15) (i : Fin 45)
    (S : Fin m → Bool → Finset V)
    (hmask : ∀ j s, S j s = SlotLabels.maskSet
      (SlotLabels.mask (SlotOrbits.canonical i) (index hm j s)))
    (hne : ∀ j, (S j false).Nonempty)
    (t : H → Slot) (W : V → Finset Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (heq : ∀ h k, t h = t k ↔ SlotTables.slot i h = SlotTables.slot i k)
    (hw : ∀ h, t h ∈ W (endpoint h)) :
    ∃ P : Fin m → Slot, Function.Injective (fun j => (P j).1) ∧
      ∀ j s v, v ∈ S j s → (if s then bar (P j) else P j) ∈
        W ((Petersen.permEquiv (SlotOrbits.vertexPerm i)).symm v) := by
  classical
  let σ := Petersen.permEquiv (SlotOrbits.vertexPerm i)
  let τ : Equiv.Perm (Fin 30) := Equiv.ofBijective (SlotOrbits.rename i)
    (Finite.injective_iff_bijective.mp (SlotOrbits.rename_injective i))
  have horbit (s : Fin 30) : (SlotLabels.label i s).image σ =
      SlotLabels.maskSet (SlotLabels.mask (SlotOrbits.canonical i) (SlotOrbits.rename i s)) := by
    rw [SlotLabels.label_eq_mask]
    exact SlotOrbits.maskSet_image i s
  have hpre (s : Fin 30) (v : V)
      (hv : v ∈ SlotLabels.maskSet (SlotLabels.mask (SlotOrbits.canonical i) s)) :
      ∃ h : H, σ (endpoint h) = v ∧ SlotOrbits.rename i (SlotTables.slot i h) = s := by
    have hτ : SlotOrbits.rename i (τ.symm s) = s := τ.apply_symm_apply s
    have hmemb : v ∈ (SlotLabels.label i (τ.symm s)).image σ := by
      rw [horbit, hτ]
      exact hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hmemb
    obtain ⟨h, he, hs⟩ := (Finset.mem_filter.mp hw).2
    refine ⟨h, ?_, ?_⟩
    · simpa only [he] using hwv
    · rw [hs]
      exact hτ
  have hex : ∀ j : Fin m, ∃ h : H,
      SlotOrbits.rename i (SlotTables.slot i h) = index hm j false := by
    intro j
    obtain ⟨v, hv⟩ := hne j
    rw [hmask] at hv
    obtain ⟨h, _, hh⟩ := hpre (index hm j false) v hv
    exact ⟨h, hh⟩
  choose pick hpick using hex
  have hbar (j : Fin m) :
      SlotOrbits.rename i (SlotTables.slot i (barH (pick j))) = index hm j true := by
    rw [SlotGateIds.slot_bar, SlotOrbits.rename_flip, hpick, index_flip]
  refine ⟨fun j => t (pick j), ?_, ?_⟩
  · intro j k hgate
    by_cases hbit : (t (pick j)).2 = (t (pick k)).2
    · have ht : t (pick j) = t (pick k) := Prod.ext hgate hbit
      have hc := congrArg (SlotOrbits.rename i) ((heq _ _).mp ht)
      rw [hpick, hpick] at hc
      exact index_inj hm hc
    · have ht : t (pick j) = bar (t (pick k)) := by
        apply Prod.ext
        · exact hgate
        · cases hj : (t (pick j)).2 <;> cases hk : (t (pick k)).2 <;>
            simp_all [bar]
      have hc := congrArg (SlotOrbits.rename i)
        ((heq (pick j) (barH (pick k))).mp (ht.trans (hb (pick k)).symm))
      rw [hpick, hbar] at hc
      exact False.elim (index_even_ne_odd hm j k hc)
  · intro j s v hv
    rw [hmask] at hv
    obtain ⟨h, hvh, hcode⟩ := hpre (index hm j s) v hv
    have hend : endpoint h = σ.symm v := by
      apply σ.injective
      simpa only [Equiv.apply_symm_apply] using hvh
    have hmem := hw h
    rw [hend] at hmem
    cases s
    · have hs : t h = t (pick j) := (heq _ _).mpr
        (SlotOrbits.rename_injective i (hcode.trans (hpick j).symm))
      simpa only [hs, Bool.false_eq_true, if_false] using hmem
    · have hs : t h = bar (t (pick j)) :=
        ((heq _ _).mpr (SlotOrbits.rename_injective i
          (hcode.trans (hbar j).symm))).trans (hb (pick j))
      simpa only [hs, if_true] using hmem

lemma six_masks : ∀ (j : Fin 6) (s : Bool),
    SixCase.side j s = SlotLabels.maskSet (SlotLabels.mask 0 (index (by decide) j s)) := by
  decide +kernel

lemma five_masks : ∀ (j : Fin 5) (s : Bool),
    FiveGroupGeometry.sides j s =
      SlotLabels.maskSet (SlotLabels.mask 18 (index (by decide) j s)) := by
  decide +kernel

def fourSide (j : Fin 4) (s : Bool) : Finset V :=
  if s then ![{1}, {8}, DagTools.FourCase.R, {9}] j
  else ![{0}, {3}, DagTools.FourCase.Q, {7}] j

lemma four_masks : ∀ (j : Fin 4) (s : Bool),
    fourSide j s = SlotLabels.maskSet (SlotLabels.mask 2 (index (by decide) j s)) := by
  decide +kernel

lemma six_packages (i : Fin 45) (hi : SlotOrbits.canonical i = 0)
    (t : H → Slot) (W : V → Finset Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (heq : ∀ h k, t h = t k ↔ SlotTables.slot i h = SlotTables.slot i k)
    (hw : ∀ h, t h ∈ W (endpoint h)) :
    ∃ P : Fin 6 → Slot, Function.Injective (fun j => (P j).1) ∧
      ∀ j s v, v ∈ SixCase.side j s → (if s then bar (P j) else P j) ∈
        W ((Petersen.permEquiv (SlotOrbits.vertexPerm i)).symm v) := by
  apply canonical_packages (by decide) i SixCase.side ?_ ?_ t W hb heq hw
  · intro j s
    rw [hi]
    exact six_masks j s
  · decide +kernel

lemma five_packages (i : Fin 45) (hi : SlotOrbits.canonical i = 18)
    (t : H → Slot) (W : V → Finset Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (heq : ∀ h k, t h = t k ↔ SlotTables.slot i h = SlotTables.slot i k)
    (hw : ∀ h, t h ∈ W (endpoint h)) :
    ∃ P : Fin 5 → Slot, Function.Injective (fun j => (P j).1) ∧
      ∀ j s v, v ∈ FiveGroupGeometry.sides j s → (if s then bar (P j) else P j) ∈
        W ((Petersen.permEquiv (SlotOrbits.vertexPerm i)).symm v) := by
  apply canonical_packages (by decide) i FiveGroupGeometry.sides ?_ ?_ t W hb heq hw
  · intro j s
    rw [hi]
    exact five_masks j s
  · decide +kernel

lemma four_packages (i : Fin 45) (hi : SlotOrbits.canonical i = 2)
    (t : H → Slot) (W : V → Finset Slot)
    (hb : ∀ h, t (barH h) = bar (t h))
    (heq : ∀ h k, t h = t k ↔ SlotTables.slot i h = SlotTables.slot i k)
    (hw : ∀ h, t h ∈ W (endpoint h)) :
    ∃ P : Fin 4 → Slot, Function.Injective (fun j => (P j).1) ∧
      ∀ j s v, v ∈ fourSide j s → (if s then bar (P j) else P j) ∈
        W ((Petersen.permEquiv (SlotOrbits.vertexPerm i)).symm v) := by
  apply canonical_packages (by decide) i fourSide ?_ ?_ t W hb heq hw
  · intro j s
    rw [hi]
    exact four_masks j s
  · decide +kernel

end SlotPackages

namespace DagTools.I0Case

open FourGroupGeometry

set_option maxRecDepth 12000 in
lemma related_eq_adj : ∀ u v : Fin 10, Petersen.related u v = true ↔ adj u v := by
  unfold adj
  decide +kernel

lemma permutation_adj (k : Fin 120) (u v : Fin 10) :
    adj (Petersen.permEquiv k u) (Petersen.permEquiv k v) ↔ adj u v := by
  rw [← related_eq_adj, ← related_eq_adj]
  change Petersen.related (Petersen.permV k u) (Petersen.permV k v) = true ↔ _
  rw [Petersen.permVgood k u v]

lemma canonical_cases (i : Fin 45) : SlotOrbits.canonical i = 0 ∨
    SlotOrbits.canonical i = 18 ∨ SlotOrbits.canonical i = 2 := by
  unfold SlotOrbits.canonical
  split
  · exact Or.inr (Or.inr rfl)
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl

lemma tight_impossible {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hBp : Bplus 10 D = (eligSet 10 D).card) (hB0 : Bzero 10 D = 0) : False := by
  classical
  obtain ⟨t, i, hb, hw, heq⟩ := I0Selected.classified_exists h hC hBp
  let σ := Petersen.permEquiv (SlotOrbits.vertexPerm i)
  let E := relabel σ D
  have hE : StrictLive 10 E := relabel_strictLive σ h
  have hEC : sem_Comp 10 adj E := relabel_comp σ h hC
    (permutation_adj (SlotOrbits.vertexPerm i))
  have hEBp : Bplus 10 E = (eligSet 10 E).card := relabel_tight_budget σ h.1 h.2.2 hBp
  have hEB0 : Bzero 10 E = 0 := (relabel_Bzero σ h.1 h.2.2).trans hB0
  have hW (v : Fin 10) : sem_W 10 E v = sem_W 10 D (σ.symm v) :=
    relabel_W_preimage σ h.1 v
  rcases canonical_cases i with hi | hi | hi
  · obtain ⟨P, hP, hs⟩ := SlotPackages.six_packages i hi t (sem_W 10 D) hb heq hw
    apply SixCase.canonical_six_impossible FourCase.graph hE hEC hEBp hEB0 P hP
    · intro j s v hv
      rw [hW]
      exact hs j s v hv
    · unfold adj
      decide +kernel
    · unfold adj
      decide +kernel
  · obtain ⟨P, hP, hs⟩ := SlotPackages.five_packages i hi t (sem_W 10 D) hb heq hw
    apply FiveCase.canonical_five_tight_impossible hE hEC hEBp hEB0 P hP
    intro j s v hv
    rw [hW]
    exact hs j s v hv
  · obtain ⟨P, hP, hs⟩ := SlotPackages.four_packages i hi t (sem_W 10 D) hb heq hw
    have hslots (j : Fin 4) (s : Bool) (v : Fin 10) (hv : v ∈ SlotPackages.fourSide j s) :
        (if s then FiniteSlots.bar (P j) else P j) ∈ sem_W 10 E v := by
      rw [hW]
      exact hs j s v hv
    apply FourCase.canonical_four_tight_impossible hE hEC hEBp hEB0
      (P 2) (P 0) (P 1) (P 3)
    · exact fun he => (by decide : (0 : Fin 4) ≠ 1) (hP he)
    · exact fun he => (by decide : (0 : Fin 4) ≠ 3) (hP he)
    · exact fun he => (by decide : (1 : Fin 4) ≠ 3) (hP he)
    · exact fun he => (by decide : (0 : Fin 4) ≠ 2) (hP he)
    · exact fun he => (by decide : (1 : Fin 4) ≠ 2) (hP he)
    · exact fun he => (by decide : (3 : Fin 4) ≠ 2) (hP he)
    · intro v hv
      exact hslots 2 false v hv
    · intro v hv
      exact hslots 2 true v hv
    · exact hslots 0 false 0 (by decide +kernel)
    · exact hslots 0 true 1 (by decide +kernel)
    · exact hslots 1 false 3 (by decide +kernel)
    · exact hslots 1 true 8 (by decide +kernel)
    · exact hslots 3 false 7 (by decide +kernel)
    · exact hslots 3 true 9 (by decide +kernel)

lemma all_eligible_impossible {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hall : eligSet 10 D = Finset.univ) (hlen : D.length ≤ 19) : False := by
  obtain ⟨hBp, hB0, _⟩ := h9_all_eligible_budget FourCase.graph h hC hall (by omega)
  have he : Bplus 10 D = (eligSet 10 D).card := by
    rw [hall, Finset.card_univ, Fintype.card_fin]
    exact hBp
  exact tight_impossible h hC he hB0

lemma zero_ineligible_impossible {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 adj D) (hi : (ineligSet 10 D).card = 0)
    (hlen : D.length ≤ 19) : False := by
  have hnone : ineligSet 10 D = ∅ := Finset.card_eq_zero.mp hi
  have hall : eligSet 10 D = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    by_contra hv
    have hm : v ∈ ineligSet 10 D := sem_mem_inelig.mpr hv
    rw [hnone] at hm
    exact Finset.notMem_empty v hm
  exact all_eligible_impossible h hC hall hlen

end DagTools.I0Case


namespace DagTools.I0Selected
open FiniteSlots FourGroupGeometry

lemma selected_exists_of_exit_cap {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hcap : ∀ v : Fin 10, (sem_W 10 D v).card ≤ 2) :
    ∃ t : H → Slot, Conditions t ∧
      (∀ p, t (barH p) = bar (t p)) ∧
      (∀ p, t p ∈ sem_W 10 D (endpoint p)) := by
  classical
  have hex : ∀ e : Fin 15, ∃ p : Slot,
      p ∈ sem_W 10 D (FiniteSlots.edges e).1 ∧
      bar p ∈ sem_W 10 D (FiniteSlots.edges e).2 ∧
      (FiniteSlots.edges e).1 ∉ supp 10 D (src D (bar p)) ∧
      (FiniteSlots.edges e).2 ∉ supp 10 D (src D p) := by
    intro e
    obtain ⟨j, hj, _, _, hu, hv, s, hus, hvs, hvs', hus'⟩ :=
      sem_joint_meeting FourCase.graph h.1 hC (edge_adj e)
    exact ⟨(j,s), sem_mem_W.mpr ⟨hj, hus, hu⟩,
      sem_mem_W.mpr ⟨hj, hvs', hv⟩, hus', hvs⟩
  choose p hp using hex
  let t : H → Slot := fun q => if q.2 then bar (p q.1) else p q.1
  have hb : ∀ q, t (barH q) = bar (t q) := by
    rintro ⟨e, b⟩
    cases b <;> simp [t, barH, bar]
  have hw : ∀ q, t q ∈ sem_W 10 D (endpoint q) := by
    rintro ⟨e, b⟩
    cases b
    · exact (hp e).1
    · exact (hp e).2.1
  refine ⟨t, ?_, hb, hw⟩
  apply conditions_of_exits t (fun s => supp 10 D (src D s)) (sem_W 10 D)
    hb hw
  · intro v s hs
    exact (sem_mem_W.mp hs).2.1
  · rintro ⟨e,b⟩
    cases b
    · exact (hp e).2.2.1
    · simpa [t, barH, bar, endpoint] using (hp e).2.2.2
  · intro v
    exact hcap v
  · intro v A hA hv
    have hind : ∀ a ∈ A, ∀ b ∈ A, ¬ adj a b := by
      intro a ha b hb' hab
      obtain ⟨e, he | he⟩ := (adj_edge a b).mp hab
      · exact hA e ⟨he.1.symm ▸ ha, he.2.symm ▸ hb'⟩
      · exact hA e ⟨he.1.symm ▸ hb', he.2.symm ▸ ha⟩
    have hnb : ∃ a ∈ A, adj v a := by
      obtain ⟨q, hq, ha⟩ := hv
      exact ⟨endpoint (barH q), ha, hq ▸ port_adj q⟩
    obtain ⟨j, s, hj, _, hs, hg, hd⟩ :=
      sem_exposure FourCase.graph h.1 hC A hind v hnb
    exact ⟨(j,s), sem_mem_W.mpr ⟨hj, hs, hg⟩, hd⟩

lemma classified_exists_of_exit_cap {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hcap : ∀ v : Fin 10, (sem_W 10 D v).card ≤ 2) :
    ∃ (t : H → Slot) (i : Fin 45),
      (∀ p, t (barH p) = bar (t p)) ∧
      (∀ p, t p ∈ sem_W 10 D (endpoint p)) ∧
      (∀ p q, t p = t q ↔ SlotTables.slot i p = SlotTables.slot i q) := by
  obtain ⟨t, ht, hb, hw⟩ := selected_exists_of_exit_cap h hC hcap
  obtain ⟨i, _, heq, _⟩ := classified_selected t ht
  exact ⟨t, i, hb, hw, heq⟩

end DagTools.I0Selected

namespace DagTools.ExitCapCanonical

lemma slot_ne_of_gate_injective {m : ℕ} (P : Fin m → ℕ × Bool)
    (hP : Function.Injective (fun i => (P i).1)) {j k : Fin m}
    (hne : j ≠ k) (s t : Bool) :
    (if s then FiniteSlots.bar (P j) else P j) ≠
      (if t then FiniteSlots.bar (P k) else P k) := by
  intro he
  apply hne
  apply hP
  have hg := congrArg Prod.fst he
  cases s <;> cases t <;> simpa only [FiniteSlots.bar, Bool.false_eq_true,
    if_false, if_true] using hg

lemma canonical_six_all_eligible {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 FourGroupGeometry.adj D)
    (P : Fin 6 → ℕ × Bool) (hP : Function.Injective (fun i => (P i).1))
    (hslots : ∀ (i : Fin 6) (s : Bool) (v : Fin 10), v ∈ SixCase.side i s →
      (if s then FiniteSlots.bar (P i) else P i) ∈ sem_W 10 D v) :
    eligSet 10 D = Finset.univ := by
  classical
  apply Finset.eq_univ_iff_forall.mpr
  intro v
  apply h9_two_exits_implies_eligible FourCase.graph h hC v
  obtain ⟨i,s,j,t,hij,hi,hj⟩ := SixCase.two_positions v
  exact Nat.succ_le_of_lt (Finset.one_lt_card.mpr
    ⟨_, hslots i s v hi, _, hslots j t v hj,
      slot_ne_of_gate_injective P hP hij s t⟩)

lemma canonical_five_nonzero_eligible {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 FourGroupGeometry.adj D)
    (P : Fin 5 → ℕ × Bool) (hP : Function.Injective (fun i => (P i).1))
    (hslots : ∀ (i : Fin 5) (s : Bool) (v : Fin 10), v ∈ FiveGroupGeometry.sides i s →
      (if s then FiniteSlots.bar (P i) else P i) ∈ sem_W 10 D v)
    (v : Fin 10) (hv : v ≠ 0) : v ∈ eligSet 10 D := by
  have hslots' : ∀ (i : Fin 5) (s : Bool) (v : Fin 10),
      v ∈ FiveGroupGeometry.sides i s →
      FiveGroupGeometry.flip s (P i) ∈ sem_W 10 D v := by
    intro i s v hi
    exact hslots i s v hi
  apply h9_two_exits_implies_eligible FourCase.graph h hC v
  have hc := Finset.card_le_card (FiveCase.known_subset P hslots' v)
  rwa [FiveCase.known_card P hP v hv] at hc

lemma canonical_five_ineligible_center {D : Dag} (h : StrictLive 10 D)
    (hC : sem_Comp 10 FourGroupGeometry.adj D)
    (P : Fin 5 → ℕ × Bool) (hP : Function.Injective (fun i => (P i).1))
    (hslots : ∀ (i : Fin 5) (s : Bool) (v : Fin 10), v ∈ FiveGroupGeometry.sides i s →
      (if s then FiniteSlots.bar (P i) else P i) ∈ sem_W 10 D v)
    (v : Fin 10) (hin : v ∈ ineligSet 10 D) : v = 0 := by
  by_contra hv
  exact (sem_mem_inelig.mp hin)
    (canonical_five_nonzero_eligible h hC P hP hslots v hv)

end DagTools.ExitCapCanonical

namespace DagTools.ExitCapCanonical
open FiniteSlots FourGroupGeometry

lemma four_R_second_side : ∀ v : Fin 10, v ∈ FourCase.R →
    ∃ j : Fin 4, ∃ s : Bool, j ≠ 2 ∧ v ∈ SlotPackages.fourSide j s := by
  decide +kernel

lemma four_all_eligible {D : Dag} (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hcap : ∀ v : Fin 10, (sem_W 10 D v).card ≤ 2)
    (P : Fin 4 → Slot) (hP : Function.Injective (fun j => (P j).1))
    (hs : ∀ j s v, v ∈ SlotPackages.fourSide j s →
      (if s then bar (P j) else P j) ∈ sem_W 10 D v) :
    eligSet 10 D = Finset.univ := by
  have hQ : ∀ v ∈ FourCase.Q, P 2 ∈ sem_W 10 D v := fun v hv => hs 2 false v hv
  have hextra := FourCase.pure_extra h.1 hC hcap (P 2) hQ
  apply Finset.eq_univ_of_forall
  intro v
  apply h9_two_exits_implies_eligible FourCase.graph h hC v
  apply Nat.succ_le_of_lt
  rcases FourCase.partition v with hv | hv
  · obtain ⟨e,he,hne,_⟩ := hextra v hv
    exact Finset.one_lt_card.mpr ⟨P 2,hQ v hv,e,he,Ne.symm hne⟩
  · obtain ⟨j,s,hj,hvs⟩ := four_R_second_side v hv
    exact Finset.one_lt_card.mpr
      ⟨(if s then bar (P j) else P j),hs j s v hvs,
       bar (P 2),hs 2 true v hv,slot_ne_of_gate_injective P hP hj s true⟩

end DagTools.ExitCapCanonical

namespace DagTools.ExitCapCase
open FiniteSlots FourGroupGeometry

lemma relabel_ineligible {D : Dag} (σ : Equiv.Perm (Fin 10))
    (hS : Strict 10 D) {v : Fin 10} (hv : v ∈ ineligSet 10 D) :
    σ v ∈ ineligSet 10 (relabel σ D) := by
  apply sem_mem_inelig.mpr
  intro he
  rw [relabel_eligSet σ hS] at he
  exact (sem_mem_inelig.mp hv) ((relabel_mem_image σ (eligSet 10 D) v).mp he)

lemma canonical_five_of_ineligible {D : Dag}
    (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hcap : ∀ v : Fin 10, (sem_W 10 D v).card ≤ 2)
    (t : H → Slot) (i : Fin 45)
    (hb : ∀ p, t (barH p) = bar (t p))
    (hw : ∀ p, t p ∈ sem_W 10 D (endpoint p))
    (heq : ∀ p q, t p = t q ↔ SlotTables.slot i p = SlotTables.slot i q)
    (hin : (ineligSet 10 D).Nonempty) : SlotOrbits.canonical i = 18 := by
  let σ := Petersen.permEquiv (SlotOrbits.vertexPerm i)
  let E := relabel σ D
  have hE : StrictLive 10 E := relabel_strictLive σ h
  have hEC : sem_Comp 10 adj E := relabel_comp σ h hC
    (I0Case.permutation_adj (SlotOrbits.vertexPerm i))
  have hEcap (v : Fin 10) : (sem_W 10 E v).card ≤ 2 := by
    rw [relabel_W_preimage σ h.1]
    exact hcap (σ.symm v)
  have hW (v : Fin 10) : sem_W 10 E v = sem_W 10 D (σ.symm v) :=
    relabel_W_preimage σ h.1 v
  obtain ⟨v,hv⟩ := hin
  have hvin : σ v ∈ ineligSet 10 E := relabel_ineligible σ h.1 hv
  have not_all : eligSet 10 E ≠ Finset.univ := by
    intro hall
    exact (sem_mem_inelig.mp hvin) (by rw [hall]; exact Finset.mem_univ _)
  rcases I0Case.canonical_cases i with hi | hi | hi
  · obtain ⟨P,hP,hs⟩ := SlotPackages.six_packages i hi t (sem_W 10 D) hb heq hw
    exfalso
    apply not_all
    apply ExitCapCanonical.canonical_six_all_eligible hE hEC P hP
    intro j s v hv
    rw [hW]
    exact hs j s v hv
  · exact hi
  · obtain ⟨P,hP,hs⟩ := SlotPackages.four_packages i hi t (sem_W 10 D) hb heq hw
    exfalso
    apply not_all
    apply ExitCapCanonical.four_all_eligible hE hEC hEcap P hP
    intro j s v hv
    rw [hW]
    exact hs j s v hv

lemma classified_five_exists_of_exit_cap {D : Dag}
    (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hcap : ∀ v : Fin 10, (sem_W 10 D v).card ≤ 2)
    (hin : (ineligSet 10 D).Nonempty) :
    ∃ (t : H → Slot) (i : Fin 45),
      (∀ p, t (barH p) = bar (t p)) ∧
      (∀ p, t p ∈ sem_W 10 D (endpoint p)) ∧
      (∀ p q, t p = t q ↔ SlotTables.slot i p = SlotTables.slot i q) ∧
      SlotOrbits.canonical i = 18 := by
  obtain ⟨t,i,hb,hw,heq⟩ := I0Selected.classified_exists_of_exit_cap h hC hcap
  exact ⟨t,i,hb,hw,heq,canonical_five_of_ineligible h hC hcap t i hb hw heq hin⟩

lemma ineligible_maps_zero {D : Dag}
    (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hcap : ∀ v : Fin 10, (sem_W 10 D v).card ≤ 2)
    (t : H → Slot) (i : Fin 45)
    (hb : ∀ p, t (barH p) = bar (t p))
    (hw : ∀ p, t p ∈ sem_W 10 D (endpoint p))
    (heq : ∀ p q, t p = t q ↔ SlotTables.slot i p = SlotTables.slot i q)
    (v : Fin 10) (hv : v ∈ ineligSet 10 D) :
    Petersen.permEquiv (SlotOrbits.vertexPerm i) v = 0 := by
  let σ := Petersen.permEquiv (SlotOrbits.vertexPerm i)
  let E := relabel σ D
  have hE : StrictLive 10 E := relabel_strictLive σ h
  have hEC : sem_Comp 10 adj E := relabel_comp σ h hC
    (I0Case.permutation_adj (SlotOrbits.vertexPerm i))
  have hi := canonical_five_of_ineligible h hC hcap t i hb hw heq ⟨v,hv⟩
  obtain ⟨P,hP,hs⟩ := SlotPackages.five_packages i hi t (sem_W 10 D) hb heq hw
  apply ExitCapCanonical.canonical_five_ineligible_center hE hEC P hP ?_ (σ v)
    (relabel_ineligible σ h.1 hv)
  intro j s w hw
  rw [relabel_W_preimage σ h.1]
  exact hs j s w hw

lemma ineligible_card_le_one_of_exit_cap {D : Dag}
    (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (hcap : ∀ v : Fin 10, (sem_W 10 D v).card ≤ 2) :
    (ineligSet 10 D).card ≤ 1 := by
  obtain ⟨t,i,hb,hw,heq⟩ := I0Selected.classified_exists_of_exit_cap h hC hcap
  apply Finset.card_le_one.mpr
  intro v hv w hw'
  apply (Petersen.permEquiv (SlotOrbits.vertexPerm i)).injective
  exact (ineligible_maps_zero h hC hcap t i hb hw heq v hv).trans
    (ineligible_maps_zero h hC hcap t i hb hw heq w hw').symm

end DagTools.ExitCapCase

namespace DagTools.ExitCapCase
open FiniteSlots FourGroupGeometry

lemma nonzero_two_exits_of_exit_cap {D : Dag}
    (h : StrictLive 10 D) (hC : sem_Comp 10 adj D)
    (h0 : (0 : Fin 10) ∈ ineligSet 10 D)
    (hcap : ∀ v : Fin 10, (sem_W 10 D v).card ≤ 2) :
    ∀ v : Fin 10, v ≠ 0 → (sem_W 10 D v).card = 2 := by
  obtain ⟨t,i,hb,hw,heq⟩ := I0Selected.classified_exists_of_exit_cap h hC hcap
  have hi := canonical_five_of_ineligible h hC hcap t i hb hw heq ⟨0,h0⟩
  let σ := Petersen.permEquiv (SlotOrbits.vertexPerm i)
  let E := relabel σ D
  have hσ0 : σ 0 = 0 := ineligible_maps_zero h hC hcap t i hb hw heq 0 h0
  obtain ⟨P,hP,hs⟩ := SlotPackages.five_packages i hi t (sem_W 10 D) hb heq hw
  have hslots : ∀ j s w, w ∈ FiveGroupGeometry.sides j s →
      FiveGroupGeometry.flip s (P j) ∈ sem_W 10 E w := by
    intro j s w hw'
    rw [relabel_W_preimage σ h.1]
    exact hs j s w hw'
  intro v hv
  have hσv : σ v ≠ 0 := fun he => hv (σ.injective (he.trans hσ0.symm))
  have hc := Finset.card_le_card (FiveCase.known_subset P hslots (σ v))
  rw [FiveCase.known_card P hP (σ v) hσv] at hc
  have hlo : 2 ≤ (sem_W 10 D v).card := by
    simpa only [E, relabel_W σ h.1] using hc
  exact Nat.le_antisymm (hcap v) hlo

end DagTools.ExitCapCase

namespace N0BirthsGeneral
open DagTools

abbrev V := Fin 10
def pair (i : Fin 3) : Finset V := ![{2, 6}, {3, 9}, {7, 8}] i
def triple (i : Fin 3) : Finset V := insert 0 (pair i)
def Occ (D : Dag) (S : Finset V) : Prop := ∃ w, supp 10 D w = S
def Good (S : Finset V) : Prop :=
  2 ≤ S.card ∧ ((0 : V) ∈ S ∨ ∃ i : Fin 3, S = pair i)
def Birth (D : Dag) (j : ℕ) (S : Finset V) : Prop :=
  j < D.length ∧ supp 10 D (10 + j) = S ∧
    ∀ w, w < 10 + j → supp 10 D w ≠ S

lemma geometry : (∀ i, (triple i).card = 3 ∧ (0 : V) ∈ triple i ∧ (pair i).card = 2) ∧
    ∀ i j, i ≠ j → triple i ∩ triple j = {0} := by decide +kernel

lemma triple_injective : Function.Injective triple := by decide +kernel

lemma good_subtriple {S : Finset V} {i : Fin 3}
    (hcard : 2 ≤ S.card) (hsub : S ⊆ triple i) : Good S := by
  refine ⟨hcard, ?_⟩
  by_cases hz : (0 : V) ∈ S
  · exact Or.inl hz
  · right
    refine ⟨i, Finset.eq_of_subset_of_card_le ?_ ?_⟩
    · intro v hv
      have hv' := hsub hv
      rw [triple, Finset.mem_insert] at hv'
      exact hv'.resolve_left (fun he => hz (he ▸ hv))
    · rw [(geometry.1 i).2.2]
      exact hcard

lemma good_supertriple {S : Finset V} {i : Fin 3}
    (hsub : triple i ⊆ S) : Good S := by
  have hc := Finset.card_le_card hsub
  rw [(geometry.1 i).1] at hc
  exact ⟨by omega, Or.inl (hsub (geometry.1 i).2.1)⟩

lemma birth_exists {D : Dag} (hS : Strict 10 D) {S : Finset V}
    (hcard : 2 ≤ S.card) (hocc : Occ D S) : ∃ j, Birth D j S := by
  obtain ⟨w, hw⟩ := hocc
  obtain ⟨j,hj,_,hs,_,hfirst,_⟩ :=
    sem_first_mask hS Finset.univ S hcard w (by simpa using hw)
  simp only [Finset.inter_univ] at hs hfirst
  exact ⟨j,hj,hs,hfirst⟩

lemma support_split {D : Dag} (hS : Strict 10 D) {S : Finset V}
    (hcard : S.card = 3) (hocc : Occ D S) :
    (∃ A B : Finset V, Occ D A ∧ Occ D B ∧ S ⊂ A ∧ S ⊂ B ∧ A ∩ B = S) ∨
    (∃ C : Finset V, Occ D C ∧ 2 ≤ C.card ∧ C ⊂ S) := by
  obtain ⟨w, hw⟩ := hocc
  obtain ⟨j,hj,_,hs,_,_,hcases⟩ :=
    sem_first_mask hS Finset.univ S (by omega) w (by simpa using hw)
  simp only [Finset.inter_univ] at hs hcases
  rcases hcases with ⟨ht,ha,hb⟩ | ⟨_,ha,hb,hu,_,_⟩
  · exact Or.inl ⟨_,_,⟨opA D j,rfl⟩,⟨opB D j,rfl⟩,ha,hb,
      (sem_supp_and hS hj ht).symm.trans hs⟩
  · have hc := Finset.card_union_le (supp 10 D (opA D j)) (supp 10 D (opB D j))
    rw [hu,hcard] at hc
    by_cases hca : 2 ≤ (supp 10 D (opA D j)).card
    · exact Or.inr ⟨_,⟨opA D j,rfl⟩,hca,ha⟩
    · exact Or.inr ⟨_,⟨opB D j,rfl⟩,by omega,hb⟩

lemma birth_unique {D : Dag} {j k : ℕ} {S : Finset V}
    (hj : Birth D j S) (hk : Birth D k S) : j = k := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hk.2.2 (10+j) (by omega) hj.2.1
  · exact hj.2.2 (10+k) (by omega) hk.2.1

lemma collect_six {D : Dag} (hS : Strict 10 D)
    (hocc : ∀ i, Occ D (triple i))
    (U : Fin 3 → Finset V) (hu : ∀ i, Occ D (U i) ∧ Good (U i))
    (hinj : Function.Injective U) (hsep : ∀ i j, triple i ≠ U j) :
    ∃ F : Finset ℕ, F.card = 6 ∧
      (∀ j ∈ F, Birth D j (supp 10 D (10+j)) ∧ Good (supp 10 D (10+j))) ∧
      ∀ j ∈ F, ∀ k ∈ F, ∀ i : Fin 3,
        supp 10 D (10+j) = pair i → supp 10 D (10+k) = pair i → j = k := by
  classical
  let S : Fin 3 × Bool → Finset V := fun p => if p.2 then triple p.1 else U p.1
  have hs : ∀ p, Occ D (S p) ∧ Good (S p) := by
    rintro ⟨i,s⟩
    cases s
    · exact hu i
    · exact ⟨hocc i,good_supertriple (Finset.Subset.refl _)⟩
  have hsi : Function.Injective S := by
    rintro ⟨i,s⟩ ⟨j,t⟩ he
    cases s <;> cases t
    · exact Prod.ext (hinj he) rfl
    · exact False.elim (hsep j i he.symm)
    · exact False.elim (hsep i j he)
    · exact Prod.ext (triple_injective he) rfl
  have hbe (p : Fin 3 × Bool) : ∃ j, Birth D j (S p) :=
    birth_exists hS (hs p).2.1 (hs p).1
  choose gate hb using hbe
  have hgi : Function.Injective gate := by
    intro p q he
    apply hsi
    exact (hb p).2.1.symm.trans ((congrArg (fun j => supp 10 D (10+j)) he).trans (hb q).2.1)
  let F := Finset.univ.image gate
  have hf : ∀ j ∈ F, Birth D j (supp 10 D (10+j)) ∧ Good (supp 10 D (10+j)) := by
    intro j hj
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hj
    simpa only [(hb p).2.1] using And.intro (hb p) (hs p).2
  refine ⟨F,?_,hf,?_⟩
  · rw [Finset.card_image_of_injective _ hgi]
    decide
  · intro j hj k hk i he hf'
    apply birth_unique (S := pair i)
    · simpa only [he] using (hf j hj).1
    · simpa only [hf'] using (hf k hk).1

lemma six_of_small_helpers {D : Dag} (hS : Strict 10 D)
    (hocc : ∀ i, Occ D (triple i))
    (hsmall : ∀ i, ∃ C : Finset V, Occ D C ∧ 2 ≤ C.card ∧ C ⊂ triple i) :
    ∃ U : Fin 3 → Finset V, (∀ i, Occ D (U i) ∧ Good (U i)) ∧
      Function.Injective U ∧ (∀ i j, triple i ≠ U j) := by
  classical
  choose U hu hc hs using hsmall
  have hcard (i : Fin 3) : (U i).card = 2 := by
    have hh := Finset.card_lt_card (hs i)
    rw [(geometry.1 i).1] at hh
    have := hc i
    omega
  refine ⟨U,fun i => ⟨hu i,good_subtriple (hc i) (hs i).le⟩,?_,?_⟩
  · intro i j he
    by_contra hne
    have hsub : U i ⊆ triple i ∩ triple j := by
      intro v hv
      exact Finset.mem_inter.mpr ⟨(hs i).le hv,(hs j).le (he ▸ hv)⟩
    have hh := Finset.card_le_card hsub
    rw [geometry.2 i j hne,Finset.card_singleton,hcard] at hh
    omega
  · intro i j he
    have hh := congrArg Finset.card he
    rw [(geometry.1 i).1,hcard] at hh
    omega

lemma other_parent {i j : Fin 3} (hij : i ≠ j) {A B X Y : Finset V}
    (hAB : A ∩ B = triple i) (hX : triple j ⊂ X)
    (hXY : X ∩ Y = triple j) :
    (X ≠ A ∧ X ≠ B) ∨ (Y ≠ A ∧ Y ≠ B) := by
  have hne : X ≠ Y := by
    intro he
    have hc := Finset.card_lt_card hX
    have hh : X = triple j := by simpa only [← he,Finset.inter_self] using hXY
    rw [hh] at hc
    omega
  by_cases hx : X ≠ A ∧ X ≠ B
  · exact Or.inl hx
  by_cases hy : Y ≠ A ∧ Y ≠ B
  · exact Or.inr hy
  have hx' : X = A ∨ X = B := by tauto
  have hy' : Y = A ∨ Y = B := by tauto
  exfalso
  rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy'
  · exact hne (hx'.trans hy'.symm)
  · apply hij
    apply triple_injective
    calc triple i = A ∩ B := hAB.symm
         _ = X ∩ Y := by rw [hx',hy']
         _ = triple j := hXY
  · apply hij
    apply triple_injective
    calc triple i = A ∩ B := hAB.symm
         _ = X ∩ Y := by rw [hx',hy',Finset.inter_comm]
         _ = triple j := hXY
  · exact hne (hx'.trans hy'.symm)

lemma helpers_of_and {D : Dag} (hS : Strict 10 D)
    (hocc : ∀ i, Occ D (triple i)) (i : Fin 3) (A B : Finset V)
    (hOA : Occ D A) (hOB : Occ D B)
    (hA : triple i ⊂ A) (hB : triple i ⊂ B) (hAB : A ∩ B = triple i) :
    ∃ U : Fin 3 → Finset V, (∀ k, Occ D (U k) ∧ Good (U k)) ∧
      Function.Injective U ∧ (∀ k l, triple k ≠ U l) := by
  classical
  have hAc : 4 ≤ A.card := by
    have hh := Finset.card_lt_card hA
    rw [(geometry.1 i).1] at hh
    omega
  have hBc : 4 ≤ B.card := by
    have hh := Finset.card_lt_card hB
    rw [(geometry.1 i).1] at hh
    omega
  have hABne : A ≠ B := by
    intro he
    have hh : A = triple i := by simpa only [← he,Finset.inter_self] using hAB
    rw [hh,(geometry.1 i).1] at hAc
    omega
  have hje : ∃ j : Fin 3, j ≠ i := by fin_cases i <;> decide +kernel
  obtain ⟨j,hji⟩ := hje
  have hCe : ∃ C : Finset V, Occ D C ∧ Good C ∧ C ≠ A ∧ C ≠ B ∧
      (∀ k, triple k ≠ C) := by
    rcases support_split hS (geometry.1 j).1 (hocc j) with
      ⟨X,Y,hOX,hOY,hX,hY,hXY⟩ | ⟨C,hOC,hC,hCT⟩
    · have pick := other_parent (Ne.symm hji) hAB hX hXY
      have build (Z : Finset V) (hOZ : Occ D Z) (hZ : triple j ⊂ Z)
          (hneA : Z ≠ A) (hneB : Z ≠ B) :
          Occ D Z ∧ Good Z ∧ Z ≠ A ∧ Z ≠ B ∧ (∀ k, triple k ≠ Z) := by
        refine ⟨hOZ,good_supertriple hZ.le,hneA,hneB,?_⟩
        intro k he
        have hc := Finset.card_lt_card hZ
        rw [← he,(geometry.1 j).1,(geometry.1 k).1] at hc
        omega
      rcases pick with hx | hy
      · exact ⟨X,build X hOX hX hx.1 hx.2⟩
      · exact ⟨Y,build Y hOY hY hy.1 hy.2⟩
    · have hCc : C.card = 2 := by
        have hc := Finset.card_lt_card hCT
        rw [(geometry.1 j).1] at hc
        omega
      refine ⟨C,hOC,good_subtriple hC hCT.le,?_,?_,?_⟩
      · intro he
        rw [← he,hCc] at hAc
        omega
      · intro he
        rw [← he,hCc] at hBc
        omega
      · intro k he
        have hc := congrArg Finset.card he
        rw [(geometry.1 k).1,hCc] at hc
        omega
  obtain ⟨C,hOC,hGC,hCA,hCB,hCT⟩ := hCe
  let U : Fin 3 → Finset V := ![A,B,C]
  refine ⟨U,?_,?_,?_⟩
  · intro k
    fin_cases k
    · exact ⟨hOA,good_supertriple hA.le⟩
    · exact ⟨hOB,good_supertriple hB.le⟩
    · exact ⟨hOC,hGC⟩
  · intro k l he
    fin_cases k <;> fin_cases l <;> simp_all [U]
  · intro k l he
    fin_cases l
    · have hc := congrArg Finset.card he
      change (triple k).card = A.card at hc
      rw [(geometry.1 k).1] at hc
      omega
    · have hc := congrArg Finset.card he
      change (triple k).card = B.card at hc
      rw [(geometry.1 k).1] at hc
      omega
    · exact hCT k he

lemma six_births {D : Dag} (hS : Strict 10 D)
    (hocc : ∀ i, Occ D (triple i)) :
    ∃ F : Finset ℕ, F.card = 6 ∧
      (∀ j ∈ F, Birth D j (supp 10 D (10+j)) ∧
        2 ≤ (supp 10 D (10+j)).card ∧
        ((0 : V) ∈ supp 10 D (10+j) ∨ ∃ i, supp 10 D (10+j) = pair i)) ∧
      ∀ j ∈ F, ∀ k ∈ F, ∀ i : Fin 3,
        supp 10 D (10+j) = pair i → supp 10 D (10+k) = pair i → j = k := by
  classical
  by_cases ha : ∃ i : Fin 3, ∃ A B : Finset V,
      Occ D A ∧ Occ D B ∧ triple i ⊂ A ∧ triple i ⊂ B ∧ A ∩ B = triple i
  · obtain ⟨i,A,B,hOA,hOB,hA,hB,hAB⟩ := ha
    obtain ⟨U,hu,hi,hs⟩ := helpers_of_and hS hocc i A B hOA hOB hA hB hAB
    exact collect_six hS hocc U hu hi hs
  · have hsmall : ∀ i, ∃ C : Finset V, Occ D C ∧ 2 ≤ C.card ∧ C ⊂ triple i := by
      intro i
      rcases support_split hS (geometry.1 i).1 (hocc i) with hh | hh
      · exact False.elim (ha ⟨i,hh⟩)
      · exact hh
    obtain ⟨U,hu,hi,hs⟩ := six_of_small_helpers hS hocc hsmall
    exact collect_six hS hocc U hu hi hs

end N0BirthsGeneral

namespace AnnotatedPruning
open DagTools

def keep {m : ℕ} (S : Finset (Fin m)) (g : Fin m → ℕ) (q : ℕ) : Finset (Fin m) :=
  S.filter (fun i => g i ≠ q)

def shift {m : ℕ} (g : Fin m → ℕ) (q : ℕ) (i : Fin m) : ℕ := na_sh q (g i)

lemma keep_subset {m : ℕ} (S : Finset (Fin m)) (g : Fin m → ℕ) (q : ℕ) :
    keep S g q ⊆ S := Finset.filter_subset _ _

lemma keep_card_loss {m : ℕ} (S : Finset (Fin m)) (g : Fin m → ℕ) (q : ℕ)
    (hinj : Set.InjOn g S) : S.card ≤ (keep S g q).card + 1 := by
  have heq (i : Fin m) (hi : i ∈ S \ keep S g q) : g i = q := by
    obtain ⟨his, hin⟩ := Finset.mem_sdiff.mp hi
    by_contra hne
    exact hin (Finset.mem_filter.mpr ⟨his, hne⟩)
  have hlost : (S \ keep S g q).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact hinj (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hb).1
      ((heq a ha).trans (heq b hb).symm)
  have hsplit := Finset.card_sdiff_add_card_eq_card (keep_subset S g q)
  omega

lemma shift_inverse {m : ℕ} (g : Fin m → ℕ) (q : ℕ) (i : Fin m)
    (hne : g i ≠ q) : na_up q (shift g q i) = g i := by
  unfold shift na_up na_sh
  split_ifs <;> omega

lemma delete_support {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ)
    (hj : j < D.length) (hf : fanout D (n + j) = 0) (w : ℕ)
    (hw : w < n + (D.length - 1)) :
    supp n (na_del n j D) w = supp n D (na_up (n + j) w) := by
  ext v
  simp only [mem_supp]
  rw [na_del_val hS j hj hf (single v) w hw]

lemma delete_annotations {m n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ)
    (hj : j < D.length) (hf : fanout D (n + j) = 0)
    (S : Finset (Fin m)) (g : Fin m → ℕ) (P : Fin m → Finset (Fin n))
    (hinj : Set.InjOn g S)
    (hbounds : ∀ i ∈ S, n ≤ g i ∧ g i < n + D.length)
    (hjoint : ∀ i ∈ S, P i ⊆ supp n D (g i)) :
    keep S g (n + j) ⊆ S ∧
    S.card ≤ (keep S g (n + j)).card + 1 ∧
    Set.InjOn (shift g (n + j)) (keep S g (n + j)) ∧
    (∀ i ∈ keep S g (n + j),
      n ≤ shift g (n + j) i ∧ shift g (n + j) i < n + (na_del n j D).length) ∧
    (∀ i ∈ keep S g (n + j), P i ⊆ supp n (na_del n j D) (shift g (n + j) i)) := by
  have hb (i : Fin m) (hi : i ∈ keep S g (n + j)) :
      n ≤ shift g (n + j) i ∧ shift g (n + j) i < n + (na_del n j D).length := by
    obtain ⟨his, hne⟩ := Finset.mem_filter.mp hi
    have hbi := hbounds i his
    rw [na_del_length n j D hj]
    constructor <;> unfold shift na_sh <;> split_ifs <;> omega
  refine ⟨keep_subset S g (n + j), keep_card_loss S g (n + j) hinj, ?_, hb, ?_⟩
  · intro a ha b hb' he
    have hga := shift_inverse g (n + j) a (Finset.mem_filter.mp ha).2
    have hgb := shift_inverse g (n + j) b (Finset.mem_filter.mp hb').2
    apply hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb').1
    exact hga.symm.trans ((congrArg (na_up (n + j)) he).trans hgb)
  · intro i hi
    have hbound := (hb i hi).2
    rw [na_del_length n j D hj] at hbound
    rw [delete_support hS j hj hf _ hbound,
      shift_inverse g (n + j) i (Finset.mem_filter.mp hi).2]
    exact hjoint i (Finset.mem_filter.mp hi).1

end AnnotatedPruning

namespace AnnotatedPruning
open DagTools

lemma prune_aux {m n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (P : Fin m → Finset (Fin n)) :
    ∀ (s : ℕ) (D : Dag), D.length = s → Strict n D → D ≠ [] →
      (∀ x : Fin n → Bool, val D x (outW n D) = F x) →
      ∀ (S : Finset (Fin m)) (g : Fin m → ℕ), Set.InjOn g S →
      (∀ i ∈ S, n ≤ g i ∧ g i < n + D.length) →
      (∀ i ∈ S, P i ⊆ supp n D (g i)) →
      ∃ (D' : Dag) (S' : Finset (Fin m)) (g' : Fin m → ℕ),
        StrictLive n D' ∧ S' ⊆ S ∧ Set.InjOn g' S' ∧
        (∀ i ∈ S', n ≤ g' i ∧ g' i < n + D'.length) ∧
        (∀ i ∈ S', P i ⊆ supp n D' (g' i)) ∧
        D'.length ≤ s ∧ D'.length + S.card ≤ s + S'.card ∧
        ∀ x : Fin n → Bool, val D' x (outW n D') = F x := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro D hlen hS hne hD S g hinj hbounds hjoint
    have hpos : 0 < D.length := List.length_pos_iff.mpr hne
    by_cases hL : Live n D
    · exact ⟨D,S,g,⟨hS,hL,hne⟩,Finset.Subset.refl S,hinj,hbounds,hjoint,
        hlen.le,by omega,hD⟩
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
        have hne' : na_del n j D ≠ [] := by
          intro he
          rw [he] at hl
          simp at hl
          omega
        have hD' : ∀ x : Fin n → Bool,
            val (na_del n j D) x (outW n (na_del n j D)) = F x := by
          intro x
          have ho : outW n (na_del n j D) = n + (D.length - 1) - 1 := by
            unfold outW
            rw [hl]
          have hu : na_up (n + j) (n + (D.length - 1) - 1) = outW n D := by
            unfold na_up outW
            split_ifs <;> omega
          rw [ho, na_del_val hS j hj hf0 x _ (by omega), hu]
          exact hD x
        obtain ⟨hkeep,hdrop,hginj,hgb,hgj⟩ :=
          delete_annotations hS j hj hf0 S g P hinj hbounds hjoint
        obtain ⟨D',S',g',h1,hsub,hginj',hgb',hgj',h2,h3,h4⟩ :=
          ih (D.length - 1) (by omega) (na_del n j D) hl
            (na_del_strict hS j hj hf0) hne' hD'
            (keep S g (n+j)) (shift g (n+j)) hginj hgb hgj
        exact ⟨D',S',g',h1,Finset.Subset.trans hsub hkeep,hginj',hgb',hgj',
          by omega,by omega,h4⟩

lemma exists_live_preserving_annotations {m n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (P : Fin m → Finset (Fin n)) (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x : Fin n → Bool, val D x (outW n D) = F x)
    (S : Finset (Fin m)) (g : Fin m → ℕ) (hinj : Set.InjOn g S)
    (hbounds : ∀ i ∈ S, n ≤ g i ∧ g i < n + D.length)
    (hjoint : ∀ i ∈ S, P i ⊆ supp n D (g i)) :
    ∃ (D' : Dag) (S' : Finset (Fin m)) (g' : Fin m → ℕ),
      StrictLive n D' ∧ S' ⊆ S ∧ Set.InjOn g' S' ∧
      (∀ i ∈ S', n ≤ g' i ∧ g' i < n + D'.length) ∧
      (∀ i ∈ S', P i ⊆ supp n D' (g' i)) ∧
      D'.length ≤ D.length ∧ D'.length + S.card ≤ D.length + S'.card ∧
      ∀ x : Fin n → Bool, val D' x (outW n D') = F x :=
  prune_aux F hess P D.length D rfl hS hne hD S g hinj hbounds hjoint

lemma lift_live_bound {m n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (P : Fin m → Finset (Fin n)) (b : ℕ)
    (hlive : ∀ (D : Dag) (S : Finset (Fin m)) (g : Fin m → ℕ),
      StrictLive n D → (∀ x : Fin n → Bool, val D x (outW n D) = F x) →
      Set.InjOn g S → (∀ i ∈ S, n ≤ g i ∧ g i < n + D.length) →
      (∀ i ∈ S, P i ⊆ supp n D (g i)) → b + S.card ≤ D.length)
    (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x : Fin n → Bool, val D x (outW n D) = F x)
    (S : Finset (Fin m)) (g : Fin m → ℕ) (hinj : Set.InjOn g S)
    (hbounds : ∀ i ∈ S, n ≤ g i ∧ g i < n + D.length)
    (hjoint : ∀ i ∈ S, P i ⊆ supp n D (g i)) : b + S.card ≤ D.length := by
  obtain ⟨D',S',g',h1,_,h2,h3,h4,_,h5,h6⟩ :=
    exists_live_preserving_annotations F hess P D hS hne hD S g hinj hbounds hjoint
  have h7 := hlive D' S' g' h1 h6 h2 h3 h4
  omega

end AnnotatedPruning

end PEqualNP.Outside.L_meta_2590
