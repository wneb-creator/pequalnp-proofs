import PEqualNP.Defs
import Mathlib.Tactic.IntervalCases

namespace PEqualNP.Outside.L_meta_24717

namespace Reflect

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

section Live

variable {α : Type} [DecidableEq α] (bop : α → α → Finset α) (uop : α → Finset α) (goal : α)

def build : ℕ → Finset α → Prop
  | 0, av => goal ∈ av
  | k + 1, av => build k av ∨
      (∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ z ∈ bop a b, build k (insert z av)) ∨
      (∃ a ∈ av, ∃ z ∈ uop a, build k (insert z av))

def live : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live k s ∨
      (∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ bop a b, z ∉ s ∧
        ∃ rest : Finset α, s = insert a (insert b rest) ∧ live k (insert z rest)) ∨
      (∃ a ∈ s, ∃ z ∈ uop a, z ∉ s ∧
        ∃ rest : Finset α, s = insert a rest ∧ live k (insert z rest))

variable {bop uop goal}

lemma compress {k : ℕ} {av : Finset α} (h : build bop uop goal k av) :
    ∃ s ⊆ av, live bop uop goal k s := by
  induction k generalizing av with
  | zero => exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩ | ⟨a, ha, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ av
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ av := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ av := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ av := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr (Or.inl ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩)⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ av
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ av := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ av := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a rest
        have hs : s ⊆ av := Finset.insert_subset ha hrest
        refine ⟨s, hs, Or.inr (Or.inr ⟨a, by simp [s], z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩)⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

lemma live_card {k : ℕ} {s : Finset α} (h : live bop uop goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩ |
        ⟨a, ha, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a rest
      omega

lemma live_separates (D : α → Prop) (hd : D goal)
    (hops : ∀ a b, ∀ z ∈ bop a b, D z → D a ∨ D b) (hun : ∀ a, ∀ z ∈ uop a, D z → D a)
    {k : ℕ} {s : Finset α} (h : live bop uop goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩ |
        ⟨a, ha, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact ⟨a, ha, hun a w hz hD⟩
      · exact ⟨w, by simp [hw], hD⟩

lemma live_tight (D : α → Prop) (hd : D goal)
    (hops : ∀ a b, ∀ z ∈ bop a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live bop uop goal k s) (hc : s.card = k + 1) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩ |
        ⟨a, ha, z, hz, hout, rest, rfl, tail⟩
    · have := live_card skip
      omega
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := live_card tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      have hc' : (insert z rest).card = k + 1 := by
        rw [Finset.card_insert_of_notMem hzrest]; omega
      obtain ⟨w, hw, hD⟩ := ih tail hc'
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := live_card tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a rest
      omega

lemma build_mono {k : ℕ} {av : Finset α} (h : build bop uop goal k av) :
    ∀ j, k ≤ j → build bop uop goal j av := by
  intro j hj
  induction hj with
  | refl => exact h
  | step _ ih => exact Or.inl ih

end Live

section Lists

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

lemma pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

lemma pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def keepChoices (a b : ℕ) (r : List ℕ) : List (List ℕ) := [r, a :: r, b :: r, a :: b :: r]

lemma recover_kept {ws r : List ℕ} {a b : ℕ} {needed : Finset ℕ}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

lemma recover_kept1 {ws r : List ℕ} {a : ℕ} {needed : Finset ℕ}
    (hp : ws.Perm (a :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a needed) :
    ∃ kept ∈ [r, a :: r], kept.Nodup ∧ kept.toFinset = needed := by
  have har := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a r.toFinset := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a := by
    intro v
    have he : (v ∈ insert a r.toFinset) ↔ v ∈ insert a needed := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons] at har
    grind
  by_cases ha : a ∈ needed
  · refine ⟨a :: r, by simp, har, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp, (List.nodup_cons.mp har).2, ?_⟩
    ext v; simp [henne]; grind

lemma singleton_list {ws : List ℕ} {goal : ℕ} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) :
    ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

lemma all_of_chunks {β : Type} (L : List β) (f : β → Bool) (B n : ℕ) (hlen : L.length ≤ B * n)
    (h : ∀ i < n, ((L.drop (B * i)).take B).all f = true) : L.all f = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · subst h0; rw [Nat.zero_mul] at hlen; omega
    · exact h0
  have hi : j / B < n := by
    rw [Nat.div_lt_iff_lt_mul hB]; rw [Nat.mul_comm] at hlen; omega
  have hmod := Nat.mod_lt j hB
  have hdm := Nat.div_add_mod j B
  have hc := List.all_eq_true.mp (h (j / B) hi)
  apply hc
  rw [List.mem_iff_getElem]
  refine ⟨j % B, ?_, ?_⟩
  · simp only [List.length_take, List.length_drop]
    omega
  · simp only [List.getElem_take, List.getElem_drop]
    congr 1
    all_goals omega

end Lists

section Search

def enc : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * enc l

lemma testBit_enc (l : List Bool) (i : ℕ) : (enc l).testBit i = l.getD i false := by
  induction l generalizing i with
  | nil => simp [enc]
  | cons b l ih =>
    cases i with
    | zero =>
      simp only [enc, Nat.testBit_zero, List.getD_cons_zero]
      cases b <;> simp <;> omega
    | succ i =>
      rw [Nat.testBit_add_one, List.getD_cons_succ, ← ih i]
      congr 1
      simp only [enc]
      cases b <;> simp <;> omega

def maskN (N : ℕ) : ℕ := enc (List.replicate N true)

lemma maskN_testBit (N r : ℕ) : (maskN N).testBit r = decide (r < N) := by
  rw [maskN, testBit_enc]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  by_cases h : r < N <;> simp [h]

variable (goal mask : ℕ) (prs : List (ℕ × ℕ)) (N J : ℕ)

def prsOf : List (ℕ × ℕ) := (List.range J).map (fun j => (N + j, N + J + j))

def sepF (ws : List ℕ) : Bool :=
  (ws.foldr (fun w acc => acc ||| ((w >>> N) ^^^ (w >>> (N + J)))) 0 &&& maskN J) == maskN J

def monF (ws : List ℕ) : Bool :=
  (ws.foldr (fun w acc => acc ||| ((w >>> N) &&& (maskN J ^^^ (w >>> (N + J))))) 0 &&& maskN J)
    == maskN J

lemma foldr_or_testBit (f : ℕ → ℕ) (ws : List ℕ) (i : ℕ) :
    (ws.foldr (fun w acc => acc ||| f w) 0).testBit i = ws.any (fun w => (f w).testBit i) := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    simp only [List.foldr_cons, Nat.testBit_or, ih, List.any_cons]
    exact Bool.or_comm _ _

def bop (a b : ℕ) : Finset ℕ := {a &&& b, a ||| b}
def uop (a : ℕ) : Finset ℕ := {mask ^^^ a}

def sepOK (ws : List ℕ) : Bool :=
  prs.all (fun pq => ws.any (fun w => w.testBit pq.1 != w.testBit pq.2))

def monOK (ws : List ℕ) : Bool :=
  prs.all (fun pq => ws.any (fun w => w.testBit pq.1 && !w.testBit pq.2))

lemma sepF_of {ws : List ℕ} (h : sepOK (prsOf N J) ws = true) : sepF N J ws = true := by
  simp only [sepOK, prsOf, List.all_map, List.all_eq_true, List.mem_range, Function.comp_def,
    List.any_eq_true, bne_iff_ne] at h
  simp only [sepF, beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, maskN_testBit, foldr_or_testBit]
  by_cases hi : i < J
  · obtain ⟨w, hw, hd⟩ := h i hi
    simp only [hi, decide_true, Bool.and_true, List.any_eq_true]
    refine ⟨w, hw, ?_⟩
    rw [Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_shiftRight]
    revert hd
    cases w.testBit (N + i) <;> cases w.testBit (N + J + i) <;> simp
  · simp [hi]

lemma monF_of {ws : List ℕ} (h : monOK (prsOf N J) ws = true) : monF N J ws = true := by
  simp only [monOK, prsOf, List.all_map, List.all_eq_true, List.mem_range, Function.comp_def,
    List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  simp only [monF, beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, maskN_testBit, foldr_or_testBit]
  by_cases hi : i < J
  · obtain ⟨w, hw, hd1, hd2⟩ := h i hi
    simp only [hi, decide_true, Bool.and_true, List.any_eq_true]
    refine ⟨w, hw, ?_⟩
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
      maskN_testBit, hd1, hd2]
    simp [hi]
  · simp [hi]

variable (nt : Bool)

def uopN (a : ℕ) : Finset ℕ := if nt then {mask ^^^ a} else ∅

def chk (k : ℕ) (ws : List ℕ) : Bool :=
  decide (ws.length ≤ k + 2) && sepF N J ws && ((nt && ws.length != k + 2) || monF N J ws)

def LS : ℕ → List ℕ → Bool
  | 0, ws => ws == [goal]
  | k + 1, ws => ws == [goal] ||
      (chk N J nt k ws &&
        ((pairs ws).any (fun t => [t.1 &&& t.2.1, t.1 ||| t.2.1].any (fun z =>
            !ws.contains z && (keepChoices t.1 t.2.1 t.2.2).any (fun kept => LS k (z :: kept)))) ||
         (nt && (singles ws).any (fun t => !ws.contains (mask ^^^ t.1) &&
            [t.2, t.1 :: t.2].any (fun kept => LS k ((mask ^^^ t.1) :: kept))))))

lemma chk_mono {k : ℕ} {ws : List ℕ} (h : chk N J nt k ws = true) : chk N J nt (k + 1) ws = true := by
  simp only [chk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨by omega, h2⟩, ?_⟩
  rcases h3 with ⟨hn, hl⟩ | h
  · exact Or.inl ⟨hn, by omega⟩
  · exact Or.inr h

lemma LS_mono : ∀ k ws, LS goal mask N J nt k ws = true → LS goal mask N J nt (k + 1) ws = true := by
  intro k
  induction k with
  | zero =>
    intro ws h
    simp only [LS] at h ⊢
    simp [h]
  | succ k ih =>
    intro ws h
    rw [LS] at h
    rw [LS]
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true] at h ⊢
    rcases h with h | ⟨hc, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨chk_mono N J nt hc, ?_⟩
      rcases h with ⟨t, ht, z, hz, hc, kept, hk, hr⟩ | ⟨hnt, t, ht, hc, kept, hk, hr⟩
      · exact Or.inl ⟨t, ht, z, hz, hc, kept, hk, ih _ hr⟩
      · exact Or.inr ⟨hnt, t, ht, hc, kept, hk, ih _ hr⟩

lemma bop_comm (a b : ℕ) : bop a b = bop b a := by
  simp [bop, Nat.land_comm, Nat.lor_comm, Finset.pair_comm]

def Dpq (pq : ℕ × ℕ) (w : ℕ) : Prop := w.testBit pq.1 ≠ w.testBit pq.2

lemma bop_D (pq : ℕ × ℕ) (a b z : ℕ) (hz : z ∈ bop a b) (hdz : Dpq pq z) : Dpq pq a ∨ Dpq pq b := by
  simp only [bop, Finset.mem_insert, Finset.mem_singleton] at hz
  unfold Dpq at hdz ⊢
  rcases hz with rfl | rfl <;> revert hdz <;>
    simp only [Nat.testBit_and, Nat.testBit_or] <;>
    cases a.testBit pq.1 <;> cases a.testBit pq.2 <;>
    cases b.testBit pq.1 <;> cases b.testBit pq.2 <;> simp

lemma bop_O (pq : ℕ × ℕ) (a b z : ℕ) (hz : z ∈ bop a b)
    (hdz : z.testBit pq.1 = true ∧ z.testBit pq.2 = false) :
    (a.testBit pq.1 = true ∧ a.testBit pq.2 = false) ∨
      (b.testBit pq.1 = true ∧ b.testBit pq.2 = false) := by
  simp only [bop, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl <;> revert hdz <;>
    simp only [Nat.testBit_and, Nat.testBit_or] <;>
    cases a.testBit pq.1 <;> cases a.testBit pq.2 <;>
    cases b.testBit pq.1 <;> cases b.testBit pq.2 <;> simp

lemma sep_of_live (hD : ∀ pq ∈ prs, Dpq pq goal)
    (hM : ∀ pq ∈ prs, mask.testBit pq.1 = mask.testBit pq.2)
    {k : ℕ} {ws : List ℕ} (h : live bop (uopN mask nt) goal k ws.toFinset) :
    sepOK prs ws = true := by
  simp only [sepOK, List.all_eq_true, List.any_eq_true, bne_iff_ne]
  intro pq hpq
  obtain ⟨w, hw, hd⟩ := live_separates (Dpq pq) (hD pq hpq) (bop_D pq)
    (by
      intro a z hz hdz
      unfold uopN at hz
      split at hz
      · simp only [Finset.mem_singleton] at hz
        subst hz
        unfold Dpq at hdz ⊢
        have hm := hM pq hpq
        revert hdz
        simp only [Nat.testBit_xor, hm]
        cases mask.testBit pq.2 <;> cases a.testBit pq.1 <;> cases a.testBit pq.2 <;> simp
      · simp at hz) h
  exact ⟨w, List.mem_toFinset.mp hw, hd⟩

lemma mon_of_live (hO : ∀ pq ∈ prs, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false)
    {k : ℕ} {ws : List ℕ} (hn : ws.Nodup) (h : live bop (uopN mask nt) goal k ws.toFinset)
    (hc : nt = false ∨ ws.length = k + 1) : monOK prs ws = true := by
  simp only [monOK, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true']
  intro pq hpq
  rcases hc with hnt | hc
  · obtain ⟨w, hw, hd⟩ := live_separates (fun w => w.testBit pq.1 = true ∧ w.testBit pq.2 = false)
      (hO pq hpq) (bop_O pq) (by intro a z hz; simp [uopN, hnt] at hz) h
    exact ⟨w, List.mem_toFinset.mp hw, hd⟩
  · obtain ⟨w, hw, hd⟩ := live_tight (fun w => w.testBit pq.1 = true ∧ w.testBit pq.2 = false)
      (hO pq hpq) (bop_O pq) h (by rw [List.toFinset_card_of_nodup hn, hc])
    exact ⟨w, List.mem_toFinset.mp hw, hd⟩

lemma chk_of_live (hD : ∀ pq ∈ prsOf N J, Dpq pq goal)
    (hM : ∀ pq ∈ prsOf N J, mask.testBit pq.1 = mask.testBit pq.2)
    (hO : ∀ pq ∈ prsOf N J, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false)
    {k : ℕ} {ws : List ℕ} (hn : ws.Nodup)
    (h : live bop (uopN mask nt) goal (k + 1) ws.toFinset) : chk N J nt k ws = true := by
  have hcard := live_card h
  rw [List.toFinset_card_of_nodup hn] at hcard
  have hsep := sepF_of N J (sep_of_live goal mask (prsOf N J) nt hD hM h)
  simp only [chk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne]
  refine ⟨⟨hcard, hsep⟩, ?_⟩
  by_cases hnt : nt = true
  · by_cases hl : ws.length = k + 2
    · exact Or.inr (monF_of N J (mon_of_live goal mask (prsOf N J) nt hO hn h (Or.inr hl)))
    · exact Or.inl ⟨hnt, hl⟩
  · exact Or.inr (monF_of N J (mon_of_live goal mask (prsOf N J) nt hO hn h
      (Or.inl (by simpa using hnt))))

lemma LS_complete (hD : ∀ pq ∈ prsOf N J, Dpq pq goal)
    (hM : ∀ pq ∈ prsOf N J, mask.testBit pq.1 = mask.testBit pq.2)
    (hO : ∀ pq ∈ prsOf N J, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false) :
    ∀ k (ws : List ℕ), ws.Nodup → live bop (uopN mask nt) goal k ws.toFinset →
      LS goal mask N J nt k ws = true := by
  intro k
  induction k with
  | zero =>
    intro ws hn h
    simp [LS, singleton_list hn h]
  | succ k ih =>
    intro ws hn h
    have hchk := chk_of_live goal mask N J nt hD hM hO hn h
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩ |
        ⟨a, ha, z, hz, hout, needed, hs, tail⟩
    · exact LS_mono goal mask N J nt k ws (ih ws hn skip)
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have hzc : ws.contains z = false := by
        simpa using fun hh => hout (List.mem_toFinset.mpr hh)
      have go {a b : ℕ} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ bop a b) :
          [a &&& b, a ||| b].any (fun z =>
            !ws.contains z && (keepChoices a b r).any (fun kept => LS goal mask N J nt k (z :: kept)))
            = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live bop (uopN mask nt) goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hrec := ih _ hnd hl
        simp only [List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true']
        refine ⟨z, ?_, hzc, kept, hk, hrec⟩
        simp only [bop, Finset.mem_insert, Finset.mem_singleton] at hop
        rcases hop with rfl | rfl <;> simp
      simp only [LS, Bool.or_eq_true, Bool.and_eq_true]
      right
      refine ⟨hchk, Or.inl ?_⟩
      simp only [List.any_eq_true]
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, by simpa using go hp hs hz⟩
      · exact ⟨(b, a, r), swap, by
          simpa using go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm])
            (bop_comm a b ▸ hz)⟩
    · obtain ⟨r, hm, hp⟩ := pick_one (List.mem_toFinset.mp ha)
      by_cases hnt : nt = true
      · simp only [uopN, hnt, if_true, Finset.mem_singleton] at hz
        subst hz
        have hzc : ws.contains (mask ^^^ a) = false := by
          simpa using fun hh => hout (List.mem_toFinset.mpr hh)
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept1 hp hn hs
        have hznew : (mask ^^^ a) ∉ kept := by
          intro hu
          apply hout
          rw [hs]
          exact Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu))
        have hnd : ((mask ^^^ a) :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live bop (uopN mask nt) goal k ((mask ^^^ a) :: kept).toFinset := by
          simpa [hfin] using tail
        have hrec := ih _ hnd hl
        simp only [LS, Bool.or_eq_true, Bool.and_eq_true]
        right
        refine ⟨hchk, Or.inr ⟨hnt, ?_⟩⟩
        simp only [List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true']
        exact ⟨(a, r), hm, hzc, kept, hk, hrec⟩
      · simp [uopN, hnt] at hz

def kidsN (ws : List ℕ) : List (List ℕ) :=
  (pairs ws).flatMap (fun t => [t.1 &&& t.2.1, t.1 ||| t.2.1].flatMap (fun z =>
      if ws.contains z then [] else (keepChoices t.1 t.2.1 t.2.2).map (fun kept => z :: kept))) ++
  (if nt then (singles ws).flatMap (fun t =>
      if ws.contains (mask ^^^ t.1) then [] else
        [t.2, t.1 :: t.2].map (fun kept => (mask ^^^ t.1) :: kept)) else [])

def expand (k : ℕ) (L : List (List ℕ)) : List (List ℕ) :=
  L.flatMap (fun ws => if chk N J nt k ws then kidsN mask nt ws else [])

lemma LS_split {k : ℕ} {ws : List ℕ} (h : LS goal mask N J nt (k + 1) ws = true) :
    ws = [goal] ∨ ∃ c ∈ kidsN mask nt ws, chk N J nt k ws = true ∧ LS goal mask N J nt k c = true := by
  rw [LS] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at h
  rcases h with h | ⟨hc, ⟨t, ht, z, hz, hzc, kept, hk, hr⟩ | ⟨hnt, t, ht, hzc, kept, hk, hr⟩⟩
  · exact Or.inl h
  · right
    refine ⟨z :: kept, ?_, hc, hr⟩
    unfold kidsN
    apply List.mem_append_left
    rw [List.mem_flatMap]
    refine ⟨t, ht, ?_⟩
    rw [List.mem_flatMap]
    refine ⟨z, hz, ?_⟩
    rw [hzc]
    exact List.mem_map.mpr ⟨kept, hk, rfl⟩
  · right
    refine ⟨(mask ^^^ t.1) :: kept, ?_, hc, hr⟩
    unfold kidsN
    apply List.mem_append_right
    rw [hnt, if_pos rfl, List.mem_flatMap]
    refine ⟨t, ht, ?_⟩
    rw [hzc]
    exact List.mem_map.mpr ⟨kept, hk, rfl⟩

lemma split_all (k : ℕ) (L : List (List ℕ)) (h1 : L.all (fun ws => !(ws == [goal])) = true)
    (h2 : (expand mask N J nt k L).all (fun c => !LS goal mask N J nt k c) = true) :
    L.all (fun ws => !LS goal mask N J nt (k + 1) ws) = true := by
  rw [List.all_eq_true]
  intro ws hws
  cases e : LS goal mask N J nt (k + 1) ws
  · rfl
  · exfalso
    rcases LS_split goal mask N J nt e with hg | ⟨c, hc, hck, hl⟩
    · have := List.all_eq_true.mp h1 ws hws
      simp [hg] at this
    · have hmem : c ∈ expand mask N J nt k L := by
        unfold expand
        rw [List.mem_flatMap]
        exact ⟨ws, hws, by rw [hck, if_pos rfl]; exact hc⟩
      have := List.all_eq_true.mp h2 c hmem
      simp [hl] at this

end Search

section Circ

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def beh (W : List (List Bool)) (i : ℕ) : ℕ := enc (W.map fun w => w.getD i false)

lemma getD_map_row (W : List (List Bool)) (i r : ℕ) :
    (W.map fun w => w.getD i false).getD r false = (W.getD r []).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[r]? <;> simp

lemma beh_testBit (W : List (List Bool)) (i r : ℕ) :
    (beh W i).testBit r = (W.getD r []).getD i false := by
  rw [beh, testBit_enc, getD_map_row]

lemma row_of_lt {W : List (List Bool)} {r : ℕ} (h : r < W.length) :
    W.getD r [] ∈ W := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

lemma row_of_ge {W : List (List Bool)} {r : ℕ} (h : W.length ≤ r) : W.getD r [] = [] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma getD_step_ne {w : List Bool} {g : Gate} {i : ℕ} (hi : i ≠ w.length) :
    (step w g).getD i false = w.getD i false := by
  simp only [step, List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma getD_step_eq {w : List Bool} {g : Gate} :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [step, List.getD_eq_getElem?_getD]

lemma mapstep_row (W : List (List Bool)) (g : Gate) (r : ℕ) :
    (W.map (fun w => step w g)).getD r [] =
      if r < W.length then step (W.getD r []) g else [] := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : r < W.length
  · simp [h, List.getElem?_eq_getElem h]
  · simp [h, List.getElem?_eq_none (Nat.le_of_not_lt h)]

lemma beh_old {W : List (List Bool)} {L : ℕ} (hl : ∀ w ∈ W, w.length = L) (g : Gate) {i : ℕ}
    (hi : i ≠ L) : beh (W.map (fun w => step w g)) i = beh W i := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [beh_testBit, beh_testBit, mapstep_row]
  by_cases h : r < W.length
  · simp only [h, ↓reduceIte]
    rw [getD_step_ne (by rw [hl _ (row_of_lt h)]; exact hi)]
  · simp only [h, ↓reduceIte]
    rw [row_of_ge (Nat.le_of_not_lt h)]

lemma beh_beyond {W : List (List Bool)} {L : ℕ} (hl : ∀ w ∈ W, w.length = L) {i : ℕ}
    (hi : L ≤ i) : beh W i = 0 := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [beh_testBit, Nat.zero_testBit]
  by_cases h : r < W.length
  · have h2 : (W.getD r []).length ≤ i := by rw [hl _ (row_of_lt h)]; exact hi
    exact List.getD_eq_default _ _ h2
  · rw [row_of_ge (Nat.le_of_not_lt h)]
    rfl

def okGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma beh_new {W : List (List Bool)} {L N : ℕ} (hl : ∀ w ∈ W, w.length = L)
    (hN : W.length = N) (g : Gate) (z : ℕ)
    (hz : ∀ r, (r < N → z.testBit r =
        g.op.eval (g.inputs.map fun i => (W.getD r []).getD i false)) ∧
      (N ≤ r → z.testBit r = false)) :
    beh (W.map (fun w => step w g)) L = z := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [beh_testBit, mapstep_row]
  by_cases h : r < W.length
  · simp only [h, ↓reduceIte]
    have hm := row_of_lt h
    have := getD_step_eq (w := W.getD r []) (g := g)
    rw [hl _ hm] at this
    rw [this, (hz r).1 (hN ▸ h)]
  · simp only [h, ↓reduceIte]
    rw [(hz r).2 (by omega)]
    rfl

lemma gate_step {W : List (List Bool)} {L N : ℕ} (hl : ∀ w ∈ W, w.length = L)
    (hN : W.length = N) (av : Finset ℕ) (hmask : maskN N ∈ av) (hinv : ∀ i, beh W i ∈ av)
    (g : Gate) (hg : okGate g) :
    ∃ z, (z ∈ av ∨ (∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ z ∈ bop a b) ∨
        (g.op = GateOp.not ∧ ∃ a ∈ av, z ∈ uop (maskN N) a)) ∧
      beh (W.map (fun w => step w g)) L = z := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  have hbeyond := beh_beyond hl (le_refl L)
  have hi : ∀ i r, N ≤ r → (beh W i).testBit r = false := by
    intro i r hr
    rw [beh_testBit, row_of_ge (by omega)]
    rfl
  have hmk : ∀ r, N ≤ r → (maskN N).testBit r = false := by
    intro r hr
    rw [maskN_testBit]
    simp; omega
  have hmk' : ∀ r, r < N → (maskN N).testBit r = true := by
    intro r hr
    rw [maskN_testBit]
    simp; omega
  match inputs, hlen with
  | [], _ =>
    rcases hop with rfl | rfl | rfl
    · refine ⟨maskN N, Or.inl hmask, beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun hr => by simp [hmk' r hr, GateOp.eval], fun hr => hmk r hr⟩
    · refine ⟨0, Or.inl (hbeyond ▸ hinv L), beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun _ => by simp [GateOp.eval], fun _ => by simp⟩
    · refine ⟨maskN N, Or.inl hmask, beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun hr => by simp [hmk' r hr, GateOp.eval], fun hr => hmk r hr⟩
  | [i], _ =>
    rcases hop with rfl | rfl | rfl
    · refine ⟨beh W i, Or.inl (hinv i), beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun _ => by simp [beh_testBit, GateOp.eval], fun hr => hi i r hr⟩
    · refine ⟨beh W i, Or.inl (hinv i), beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun _ => by simp [beh_testBit, GateOp.eval], fun hr => hi i r hr⟩
    · refine ⟨maskN N ^^^ beh W i, Or.inr (Or.inr ⟨rfl, beh W i, hinv i, by simp [uop]⟩),
        beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun hr => by simp [Nat.testBit_xor, hmk' r hr, beh_testBit, GateOp.eval],
        fun hr => by simp [Nat.testBit_xor, hmk r hr, hi i r hr]⟩
  | [i, j], _ =>
    rcases hop with rfl | rfl | rfl
    · refine ⟨beh W i &&& beh W j, ?_, beh_new hl hN _ _ ?_⟩
      · by_cases e : beh W i = beh W j
        · left; rw [e, Nat.and_self]; exact hinv j
        · right; left; exact ⟨_, hinv i, _, hinv j, e, by simp [bop]⟩
      · intro r
        exact ⟨fun _ => by simp [Nat.testBit_and, beh_testBit, GateOp.eval],
          fun hr => by simp [Nat.testBit_and, hi i r hr]⟩
    · refine ⟨beh W i ||| beh W j, ?_, beh_new hl hN _ _ ?_⟩
      · by_cases e : beh W i = beh W j
        · left; rw [e, Nat.or_self]; exact hinv j
        · right; left; exact ⟨_, hinv i, _, hinv j, e, by simp [bop]⟩
      · intro r
        exact ⟨fun _ => by simp [Nat.testBit_or, beh_testBit, GateOp.eval],
          fun hr => by simp [Nat.testBit_or, hi i r hr, hi j r hr]⟩
    · refine ⟨maskN N ^^^ beh W i, Or.inr (Or.inr ⟨rfl, beh W i, hinv i, by simp [uop]⟩),
        beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun hr => by simp [Nat.testBit_xor, hmk' r hr, beh_testBit, GateOp.eval],
        fun hr => by simp [Nat.testBit_xor, hmk r hr, hi i r hr]⟩
  | _ :: _ :: _ :: _, h => simp at h

def stepAll (gs : List Gate) (W : List (List Bool)) : List (List Bool) :=
  gs.foldl (fun W g => W.map (fun w => step w g)) W

lemma stepAll_eq (gs : List Gate) :
    ∀ W, stepAll gs W = W.map (fun w => gs.foldl step w) := by
  induction gs with
  | nil => intro W; simp [stepAll]
  | cons g gs ih =>
    intro W
    show stepAll gs (W.map (fun w => step w g)) = _
    rw [ih, List.map_map]
    rfl

def okN (nt : Bool) (g : Gate) : Prop := okGate g ∧ (nt = false → g.op ≠ GateOp.not)

lemma to_buildN (nt : Bool) (N goal : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, okN nt g) :
    ∀ (L : ℕ) (W : List (List Bool)) (av : Finset ℕ), (∀ w ∈ W, w.length = L) → W.length = N →
      maskN N ∈ av → (∀ i, beh W i ∈ av) → ∀ o, beh (stepAll gs W) o = goal →
      build bop (uopN (maskN N) nt) goal gs.length av := by
  induction gs with
  | nil =>
    intro L W av _ _ _ hinv o ho
    exact ho ▸ hinv o
  | cons g gs ih =>
    intro L W av hl hN hm hinv o ho
    obtain ⟨z, hz, hbz⟩ := gate_step hl hN av hm hinv g (hg g (by simp)).1
    have hl' : ∀ w ∈ W.map (fun w => step w g), w.length = L + 1 := by
      intro w hw
      obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
      simp [step, hl w0 hw0]
    have hN' : (W.map (fun w => step w g)).length = N := by simp [hN]
    have hinv' : ∀ i, beh (W.map (fun w => step w g)) i ∈ insert z av := by
      intro i
      by_cases hi : i = L
      · subst hi; rw [hbz]; exact Finset.mem_insert_self _ _
      · rw [beh_old hl g hi]; exact Finset.mem_insert_of_mem (hinv i)
    have hrec := ih (fun g hg' => hg g (List.mem_cons_of_mem _ hg')) (L + 1) _ (insert z av)
      hl' hN' (Finset.mem_insert_of_mem hm) hinv' o ho
    rw [List.length_cons]
    rcases hz with hz | ⟨a, ha, b, hb, hab, hz⟩ | ⟨hop, a, ha, hz⟩
    · rw [Finset.insert_eq_of_mem hz] at hrec; exact Or.inl hrec
    · exact Or.inr (Or.inl ⟨a, ha, b, hb, hab, z, hz, hrec⟩)
    · by_cases hnt : nt = true
      · refine Or.inr (Or.inr ⟨a, ha, z, ?_, hrec⟩)
        simp only [uop, Finset.mem_singleton] at hz
        simp [uopN, hnt, hz]
      · exact absurd hop ((hg g (by simp)).2 (by simpa using hnt))

def rowsOf (n m : ℕ) (ex : List (Fin n × Fin m)) : List (List Bool) :=
  ((List.finRange n).flatMap fun u => (List.finRange m).map fun v => oneEach u v) ++
    ex.map (fun p => oneEach p.1 p.2)

def goalOf {n m : ℕ} (A : Fin n → Fin m → Bool) (ex : List (Fin n × Fin m)) : List Bool :=
  ((List.finRange n).flatMap fun u => (List.finRange m).map fun v => A u v) ++
    ex.map (fun p => A p.1 p.2)

lemma rows_len (n m : ℕ) (ex : List (Fin n × Fin m)) :
    ∀ w ∈ rowsOf n m ex, w.length = n + m := by
  intro w hw
  simp only [rowsOf, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_finRange,
    true_and] at hw
  rcases hw with ⟨u, v, rfl⟩ | ⟨p, _, rfl⟩ <;> simp [oneEach]

lemma core (X : List (List Bool)) (L : ℕ) (hX : ∀ x ∈ X, x.length = L) (tl : List Bool)
    (nt : Bool) (K Nb J Nt goal mask : ℕ) (init : List ℕ)
    (hN : X.length = Nt) (hgoal : enc tl = goal) (hmask : maskN Nt = mask)
    (hinit : ((List.range L).all (fun i => init.contains (beh X i)) &&
      init.contains 0 && init.contains mask) = true)
    (hnd : init.Nodup)
    (hprs : (List.range J).all (fun j => (goal.testBit (Nb + j) && !goal.testBit (Nb + J + j)) &&
      (mask.testBit (Nb + j) == mask.testBit (Nb + J + j))) = true)
    (hsearch : init.sublists.all (fun l => !LS goal mask Nb J nt K l) = true)
    (C : Circuit) (hF : ∀ g ∈ C.gates, okN nt g) (hs : C.size ≤ K)
    (hev : X.map (fun x => C.eval x) = tl) : False := by
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, List.mem_range] at hinit
  obtain ⟨⟨hinp, h0⟩, hm⟩ := hinit
  have hinv : ∀ i, beh X i ∈ init.toFinset := by
    intro i
    rw [List.mem_toFinset]
    by_cases h : i < L
    · exact hinp i h
    · rw [beh_beyond hX (Nat.le_of_not_lt h)]; exact h0
  have hfin : beh (stepAll C.gates X) C.output = goal := by
    rw [← hgoal, ← hev, beh, stepAll_eq, List.map_map]
    rfl
  have hb := to_buildN nt Nt goal C.gates hF L X init.toFinset hX hN
    (by rw [hmask]; exact List.mem_toFinset.mpr hm) hinv C.output hfin
  rw [hmask] at hb
  have hb' := build_mono hb K hs
  obtain ⟨S, hS, hlive⟩ := compress hb'
  have hall : ∀ pq ∈ prsOf Nb J, (goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false) ∧
      mask.testBit pq.1 = mask.testBit pq.2 := by
    intro pq hpq
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hpq
    have := List.all_eq_true.mp hprs j hj
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at this
    exact this
  have hO : ∀ pq ∈ prsOf Nb J, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false :=
    fun pq hpq => (hall pq hpq).1
  have hD : ∀ pq ∈ prsOf Nb J, Dpq pq goal := by
    intro pq hpq
    have := hO pq hpq
    unfold Dpq
    rw [this.1, this.2]
    simp
  have hM : ∀ pq ∈ prsOf Nb J, mask.testBit pq.1 = mask.testBit pq.2 :=
    fun pq hpq => (hall pq hpq).2
  let l := init.filter (fun x => decide (x ∈ S))
  have hl_sub : l ∈ init.sublists := List.mem_sublists.mpr List.filter_sublist
  have hl_nd : l.Nodup := hnd.filter _
  have hl_fs : l.toFinset = S := by
    ext x
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hS h), h⟩⟩
  have hc := LS_complete goal mask Nb J nt hD hM hO K l hl_nd (hl_fs ▸ hlive)
  have hf := List.all_eq_true.mp hsearch l hl_sub
  rw [hc] at hf
  exact Bool.noConfusion hf

lemma rows_eval {n m : ℕ} (A : Fin n → Fin m → Bool) (ex : List (Fin n × Fin m)) (C : Circuit)
    (hr : Represents A C) : (rowsOf n m ex).map (fun x => C.eval x) = goalOf A ex := by
  simp only [rowsOf, goalOf, List.map_append, List.map_flatMap, List.map_map]
  congr 1
  · congr 1
    funext u
    apply List.map_congr_left
    intro v _
    exact hr u v
  · apply List.map_congr_left
    intro p _
    exact hr p.1 p.2

lemma refuteM {n m : ℕ} (A : Fin n → Fin m → Bool) (K Nb J Nt goal mask : ℕ) (init : List ℕ)
    (ex : List (Fin n × Fin m))
    (hN : (rowsOf n m ex).length = Nt) (hgoal : enc (goalOf A ex) = goal) (hmask : maskN Nt = mask)
    (hinit : ((List.range (n + m)).all (fun i => init.contains (beh (rowsOf n m ex) i)) &&
      init.contains 0 && init.contains mask) = true)
    (hnd : init.Nodup)
    (hprs : (List.range J).all (fun j => (goal.testBit (Nb + j) && !goal.testBit (Nb + J + j)) &&
      (mask.testBit (Nb + j) == mask.testBit (Nb + J + j))) = true)
    (hsearch : init.sublists.all (fun l => !LS goal mask Nb J false K l) = true) :
    ¬ PEqualNP.Represents.RepSizeAtMost A K := by
  rintro ⟨C, hC, hs, hr⟩
  refine core (rowsOf n m ex) (n + m) (rows_len n m ex) (goalOf A ex) false K Nb J Nt goal mask
    init hN hgoal hmask hinit hnd hprs hsearch C ?_ hs (rows_eval A ex C hr)
  intro g hg
  obtain ⟨hop, hl⟩ := hC g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  refine ⟨⟨by rcases hop with h | h <;> simp [h], hl⟩, fun _ => ?_⟩
  rcases hop with h | h <;> rw [h] <;> simp

lemma refuteF {n m : ℕ} (A : Fin n → Fin m → Bool) (K Nb J Nt goal mask : ℕ) (init : List ℕ)
    (ex : List (Fin n × Fin m))
    (hN : (rowsOf n m ex).length = Nt) (hgoal : enc (goalOf A ex) = goal) (hmask : maskN Nt = mask)
    (hinit : ((List.range (n + m)).all (fun i => init.contains (beh (rowsOf n m ex) i)) &&
      init.contains 0 && init.contains mask) = true)
    (hnd : init.Nodup)
    (hprs : (List.range J).all (fun j => (goal.testBit (Nb + j) && !goal.testBit (Nb + J + j)) &&
      (mask.testBit (Nb + j) == mask.testBit (Nb + J + j))) = true)
    (hsearch : init.sublists.all (fun l => !LS goal mask Nb J true K l) = true) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ K ∧ Represents A C := by
  rintro ⟨C, hC, hs, hr⟩
  exact core (rowsOf n m ex) (n + m) (rows_len n m ex) (goalOf A ex) true K Nb J Nt goal mask
    init hN hgoal hmask hinit hnd hprs hsearch C (fun g hg => ⟨hC g hg, by simp⟩) hs
    (rows_eval A ex C hr)

def twoRow5 (p : Fin 5 × Fin 5) : List Bool := List.ofFn fun k : Fin 5 => decide (k = p.1 ∨ k = p.2)

def twoGoal5 (M : ℕ) (p : Fin 5 × Fin 5) : Bool :=
  M.testBit (5 * min p.1.val p.2.val + max p.1.val p.2.val)

lemma refuteT5 (M K Nb J Nt goal mask : ℕ) (init : List ℕ) (ex : List (Fin 5 × Fin 5))
    (hN : (ex.map twoRow5).length = Nt) (hgoal : enc (ex.map (twoGoal5 M)) = goal)
    (hmask : maskN Nt = mask)
    (hinit : ((List.range 5).all (fun i => init.contains (beh (ex.map twoRow5) i)) &&
      init.contains 0 && init.contains mask) = true)
    (hnd : init.Nodup)
    (hprs : (List.range J).all (fun j => (goal.testBit (Nb + j) && !goal.testBit (Nb + J + j)) &&
      (mask.testBit (Nb + j) == mask.testBit (Nb + J + j))) = true)
    (hsearch : init.sublists.all (fun l => !LS goal mask Nb J true K l) = true) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ K ∧ ∀ i j : Fin 5,
      C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
        M.testBit (5 * min i.val j.val + max i.val j.val) := by
  rintro ⟨C, hC, hs, hr⟩
  refine core (ex.map twoRow5) 5 ?_ (ex.map (twoGoal5 M)) true K Nb J Nt goal mask
    init hN hgoal hmask hinit hnd hprs hsearch C (fun g hg => ⟨hC g hg, by simp⟩) hs ?_
  · intro x hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    simp [twoRow5]
  · rw [List.map_map]
    apply List.map_congr_left
    intro p _
    exact hr p.1 p.2

end Circ

section PermReview

lemma singles_perm_review {α : Type} {ws : List α} {a : α} {r : List α}
    (h : (a, r) ∈ singles ws) : ws.Perm (a :: r) := by
  induction ws generalizing a r with
  | nil => simp [singles] at h
  | cons x xs ih =>
    simp only [singles, List.mem_cons, List.mem_map] at h
    rcases h with h | ⟨⟨b, bs⟩, hb, he⟩
    · cases h
      exact List.Perm.refl _
    · cases he
      exact ((ih hb).cons x).trans (.swap _ _ _)

lemma pairs_perm_review {α : Type} {ws : List α} {a b : α} {r : List α}
    (h : (a, b, r) ∈ pairs ws) : ws.Perm (a :: b :: r) := by
  induction ws generalizing a b r with
  | nil => simp [pairs] at h
  | cons x xs ih =>
    simp only [pairs, List.mem_append, List.mem_map] at h
    rcases h with ⟨⟨c, cs⟩, hc, he⟩ | ⟨⟨c, d, cs⟩, hc, he⟩
    · cases he
      exact (singles_perm_review hc).cons x
    · cases he
      exact ((ih hc).cons x).trans
        ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _))

lemma kept_props_review {ws r kept : List ℕ} {a b : ℕ}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hk : kept ∈ keepChoices a b r) :
    kept.Nodup ∧ kept.toFinset ⊆ ws.toFinset ∧
      ws.toFinset = insert a (insert b kept.toFinset) := by
  have hnd := hp.nodup_iff.mp hn
  have hfs : ws.toFinset = insert a (insert b r.toFinset) := by
    ext x
    simp [hp.mem_iff]
  simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp_all [List.nodup_cons, Finset.insert_comm, Finset.insert_subset_iff]
  all_goals
    intro x hx
    simp [hx]

lemma kept1_props_review {ws r kept : List ℕ} {a : ℕ}
    (hp : ws.Perm (a :: r)) (hn : ws.Nodup)
    (hk : kept ∈ [r, a :: r]) :
    kept.Nodup ∧ kept.toFinset ⊆ ws.toFinset ∧
      ws.toFinset = insert a kept.toFinset := by
  have hnd := hp.nodup_iff.mp hn
  have hfs : ws.toFinset = insert a r.toFinset := by
    ext x
    simp [hp.mem_iff]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl <;> simp_all [List.nodup_cons, Finset.insert_subset_iff]

lemma live_singleton_review (bop : ℕ → ℕ → Finset ℕ) (uop : ℕ → Finset ℕ)
    (goal k : ℕ) : live bop uop goal k {goal} := by
  induction k with
  | zero => rfl
  | succ k ih => exact Or.inl ih

lemma LS_sound_review (goal mask N J : ℕ) (nt : Bool) :
    ∀ k (ws : List ℕ), ws.Nodup → LS goal mask N J nt k ws = true →
      live bop (uopN mask nt) goal k ws.toFinset := by
  intro k
  induction k with
  | zero =>
    intro ws hn h
    simp only [LS, beq_iff_eq] at h
    subst ws
    exact rfl
  | succ k ih =>
    intro ws hn h
    rw [LS] at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true,
      beq_iff_eq, Bool.not_eq_true'] at h
    rcases h with hg | ⟨hc, h⟩
    · subst ws
      exact live_singleton_review bop (uopN mask nt) goal (k + 1)
    · rcases h with ⟨⟨a, b, r⟩, ht, z, hz, hzc, kept, hk, hr⟩ |
        ⟨hnt, ⟨a, r⟩, ht, hzc, kept, hk, hr⟩
      · have hp := pairs_perm_review ht
        obtain ⟨hkn, hks, hfs⟩ := kept_props_review hp hn hk
        have hzout : z ∉ ws.toFinset := by
          simpa using hzc
        have hzk : z ∉ kept := fun hz => hzout (hks (List.mem_toFinset.mpr hz))
        have htail := ih _ (List.nodup_cons.mpr ⟨hzk, hkn⟩) hr
        have hnd := hp.nodup_iff.mp hn
        have hab : a ≠ b := by
          simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
          exact hnd.1.1
        refine Or.inr (Or.inl ⟨a, ?_, b, ?_, hab, z, ?_, hzout,
          kept.toFinset, hfs, ?_⟩)
        · rw [hfs]; simp
        · rw [hfs]; simp
        · simpa [bop] using hz
        · simpa using htail
      · have hp := singles_perm_review ht
        obtain ⟨hkn, hks, hfs⟩ := kept1_props_review hp hn hk
        have hzout : mask ^^^ a ∉ ws.toFinset := by
          simpa using hzc
        have hzk : mask ^^^ a ∉ kept := fun hz => hzout (hks (List.mem_toFinset.mpr hz))
        have htail := ih _ (List.nodup_cons.mpr ⟨hzk, hkn⟩) hr
        refine Or.inr (Or.inr ⟨a, ?_, mask ^^^ a, ?_, hzout, kept.toFinset, hfs, ?_⟩)
        · rw [hfs]; simp
        · simp [uopN, hnt]
        · simpa using htail

lemma LS_perm_review (goal mask N J : ℕ) (nt : Bool)
    (hD : ∀ pq ∈ prsOf N J, Dpq pq goal)
    (hM : ∀ pq ∈ prsOf N J, mask.testBit pq.1 = mask.testBit pq.2)
    (hO : ∀ pq ∈ prsOf N J, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false)
    {k : ℕ} {ws vs : List ℕ} (hn : ws.Nodup) (hp : ws.Perm vs) :
    LS goal mask N J nt k ws = LS goal mask N J nt k vs := by
  have hfs : ws.toFinset = vs.toFinset := by
    ext x
    simp only [List.mem_toFinset, hp.mem_iff]
  have hvn := hp.nodup_iff.mp hn
  have forward : LS goal mask N J nt k ws = true → LS goal mask N J nt k vs = true := by
    intro h
    apply LS_complete goal mask N J nt hD hM hO k vs hvn
    rw [← hfs]
    exact LS_sound_review goal mask N J nt k ws hn h
  have backward : LS goal mask N J nt k vs = true → LS goal mask N J nt k ws = true := by
    intro h
    apply LS_complete goal mask N J nt hD hM hO k ws hn
    rw [hfs]
    exact LS_sound_review goal mask N J nt k vs hvn h
  cases hw : LS goal mask N J nt k ws <;>
    cases hv : LS goal mask N J nt k vs <;> simp_all


def canon_review (ws : List ℕ) : List ℕ :=
  ws.insertionSort (fun a b => a ≤ b)

lemma LS_canon_review (goal mask N J : ℕ) (nt : Bool)
    (hD : ∀ pq ∈ prsOf N J, Dpq pq goal)
    (hM : ∀ pq ∈ prsOf N J, mask.testBit pq.1 = mask.testBit pq.2)
    (hO : ∀ pq ∈ prsOf N J, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false)
    (k : ℕ) (ws : List ℕ) (hn : ws.Nodup) :
    LS goal mask N J nt k ws = LS goal mask N J nt k (canon_review ws) := by
  exact LS_perm_review goal mask N J nt hD hM hO hn
    (List.perm_insertionSort (fun a b => a ≤ b) ws).symm

lemma all_canon_review (goal mask N J : ℕ) (nt : Bool)
    (hD : ∀ pq ∈ prsOf N J, Dpq pq goal)
    (hM : ∀ pq ∈ prsOf N J, mask.testBit pq.1 = mask.testBit pq.2)
    (hO : ∀ pq ∈ prsOf N J, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false)
    (k : ℕ) (L : List (List ℕ)) (hn : ∀ ws ∈ L, ws.Nodup)
    (h : (L.map canon_review).eraseDups.all (fun ws => !LS goal mask N J nt k ws) = true) :
    L.all (fun ws => !LS goal mask N J nt k ws) = true := by
  rw [List.all_eq_true] at h ⊢
  intro ws hws
  have hc := h (canon_review ws)
    (List.mem_eraseDups.mpr (List.mem_map.mpr ⟨ws, hws, rfl⟩))
  rw [LS_canon_review goal mask N J nt hD hM hO k ws (hn ws hws)]
  exact hc

lemma split_all_canon_review (goal mask N J : ℕ) (nt : Bool)
    (hD : ∀ pq ∈ prsOf N J, Dpq pq goal)
    (hM : ∀ pq ∈ prsOf N J, mask.testBit pq.1 = mask.testBit pq.2)
    (hO : ∀ pq ∈ prsOf N J, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false)
    (k : ℕ) (L : List (List ℕ))
    (hn : ∀ ws ∈ expand mask N J nt k L, ws.Nodup)
    (h1 : L.all (fun ws => !(ws == [goal])) = true)
    (h2 : ((expand mask N J nt k L).map canon_review).eraseDups.all
      (fun ws => !LS goal mask N J nt k ws) = true) :
    L.all (fun ws => !LS goal mask N J nt (k + 1) ws) = true := by
  exact split_all goal mask N J nt k L h1
    (all_canon_review goal mask N J nt hD hM hO k (expand mask N J nt k L) hn h2)


def quickFail_review (goal N J : ℕ) (nt : Bool) (k : ℕ) (ws : List ℕ) : Bool :=
  !(ws == [goal]) && match k with
    | 0 => true
    | j + 1 => !chk N J nt j ws

lemma quickFail_sound_review (goal mask N J : ℕ) (nt : Bool) (k : ℕ) (ws : List ℕ)
    (h : quickFail_review goal N J nt k ws = true) :
    LS goal mask N J nt k ws = false := by
  cases k with
  | zero =>
    simp only [quickFail_review, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1
  | succ k =>
    simp only [quickFail_review, Bool.and_eq_true, Bool.not_eq_true'] at h
    rw [LS, h.1, h.2]
    rfl

lemma canon_perm_review {ws vs : List ℕ} (h : canon_review ws = canon_review vs) :
    ws.Perm vs := by
  have hw := List.perm_insertionSort (fun a b => a ≤ b) ws
  have hv := List.perm_insertionSort (fun a b => a ≤ b) vs
  change (canon_review ws).Perm ws at hw
  change (canon_review vs).Perm vs at hv
  rw [← h] at hv
  exact hw.symm.trans hv

def tableHit_review {n : ℕ} (T : Fin n → ℕ × List ℕ)
    (lookup : ℕ → List ℕ → Fin n) (k : ℕ) (ws : List ℕ) : Bool :=
  ((T (lookup k ws)).1 == k) &&
    (canon_review (T (lookup k ws)).2 == canon_review ws)

def failRow_review {n : ℕ} (goal mask N J : ℕ) (nt : Bool)
    (T : Fin n → ℕ × List ℕ) (lookup : ℕ → List ℕ → Fin n)
    (k : ℕ) (ws : List ℕ) : Bool :=
  decide ws.Nodup && !(ws == [goal]) && match k with
    | 0 => true
    | j + 1 => !chk N J nt j ws ||
        (kidsN mask nt ws).all (fun c => quickFail_review goal N J nt j c || tableHit_review T lookup j c)

def failTable_review {n : ℕ} (goal mask N J : ℕ) (nt : Bool)
    (T : Fin n → ℕ × List ℕ) (lookup : ℕ → List ℕ → Fin n) : Bool :=
  (List.finRange n).all (fun r => failRow_review goal mask N J nt T lookup (T r).1 (T r).2)

lemma failRow_nodup_review {n : ℕ} (goal mask N J : ℕ) (nt : Bool)
    (T : Fin n → ℕ × List ℕ) (lookup : ℕ → List ℕ → Fin n) (k : ℕ) (ws : List ℕ)
    (h : failRow_review goal mask N J nt T lookup k ws = true) : ws.Nodup := by
  simp only [failRow_review, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

lemma failTable_sound_review {n : ℕ} (goal mask N J : ℕ) (nt : Bool)
    (hD : ∀ pq ∈ prsOf N J, Dpq pq goal)
    (hM : ∀ pq ∈ prsOf N J, mask.testBit pq.1 = mask.testBit pq.2)
    (hO : ∀ pq ∈ prsOf N J, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false)
    (T : Fin n → ℕ × List ℕ) (lookup : ℕ → List ℕ → Fin n)
    (h : failTable_review goal mask N J nt T lookup = true) :
    ∀ r, LS goal mask N J nt (T r).1 (T r).2 = false := by
  have rows : ∀ r, failRow_review goal mask N J nt T lookup (T r).1 (T r).2 = true := by
    intro r
    exact List.all_eq_true.mp h r (List.mem_finRange r)
  have main : ∀ k r, (T r).1 = k → LS goal mask N J nt k (T r).2 = false := by
    intro k
    induction k with
    | zero =>
      intro r he
      have hr := rows r
      rw [he] at hr
      simp only [failRow_review, Bool.and_eq_true, Bool.not_eq_true'] at hr
      exact hr.1.2
    | succ k ih =>
      intro r he
      have hr := rows r
      rw [he] at hr
      simp only [failRow_review, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hr
      have hg := hr.1.2
      rcases hr.2 with hp | hc
      · rw [LS, hg, hp]
        rfl
      · cases hl : LS goal mask N J nt (k + 1) (T r).2 with
        | false => rfl
        | true =>
          exfalso
          rcases LS_split goal mask N J nt hl with hgoal | ⟨c, hmem, hck, hls⟩
          · simp [hgoal] at hg
          · have hchild := List.all_eq_true.mp hc c hmem
            simp only [Bool.or_eq_true] at hchild
            rcases hchild with hquick | hhit
            · have hf := quickFail_sound_review goal mask N J nt k c hquick
              rw [hf] at hls
              contradiction
            · simp only [tableHit_review, Bool.and_eq_true, beq_iff_eq] at hhit
              have hp : (T (lookup k c)).2.Perm c := canon_perm_review hhit.2
              have hn := failRow_nodup_review goal mask N J nt T lookup
                (T (lookup k c)).1 (T (lookup k c)).2 (rows (lookup k c))
              have hv := LS_perm_review goal mask N J nt hD hM hO hn hp (k := k)
              have hf := ih (lookup k c) hhit.1
              rw [hf, hls] at hv
              contradiction
  intro r
  exact main (T r).1 r rfl



lemma failTable_lookup_review {n : ℕ} (goal mask N J : ℕ) (nt : Bool)
    (hD : ∀ pq ∈ prsOf N J, Dpq pq goal)
    (hM : ∀ pq ∈ prsOf N J, mask.testBit pq.1 = mask.testBit pq.2)
    (hO : ∀ pq ∈ prsOf N J, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false)
    (T : Fin n → ℕ × List ℕ) (lookup : ℕ → List ℕ → Fin n)
    (h : failTable_review goal mask N J nt T lookup = true)
    (k : ℕ) (ws : List ℕ) (hit : tableHit_review T lookup k ws = true) :
    LS goal mask N J nt k ws = false := by
  simp only [tableHit_review, Bool.and_eq_true, beq_iff_eq] at hit
  have hr := List.all_eq_true.mp h (lookup k ws) (List.mem_finRange (lookup k ws))
  have hn := failRow_nodup_review goal mask N J nt T lookup
    (T (lookup k ws)).1 (T (lookup k ws)).2 hr
  have hp : (T (lookup k ws)).2.Perm ws := canon_perm_review hit.2
  have hv := LS_perm_review goal mask N J nt hD hM hO hn hp (k := k)
  have hf := failTable_sound_review goal mask N J nt hD hM hO T lookup h (lookup k ws)
  rw [hit.1] at hf
  rw [← hv]
  exact hf

lemma failTable_frontier_review {n : ℕ} (goal mask N J : ℕ) (nt : Bool)
    (hD : ∀ pq ∈ prsOf N J, Dpq pq goal)
    (hM : ∀ pq ∈ prsOf N J, mask.testBit pq.1 = mask.testBit pq.2)
    (hO : ∀ pq ∈ prsOf N J, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false)
    (T : Fin n → ℕ × List ℕ) (lookup : ℕ → List ℕ → Fin n)
    (h : failTable_review goal mask N J nt T lookup = true)
    (k : ℕ) (L : List (List ℕ))
    (hc : L.all (fun ws => quickFail_review goal N J nt k ws || tableHit_review T lookup k ws) = true) :
    L.all (fun ws => !LS goal mask N J nt k ws) = true := by
  rw [List.all_eq_true] at hc ⊢
  intro ws hws
  have hh := hc ws hws
  simp only [Bool.or_eq_true] at hh
  have hf : LS goal mask N J nt k ws = false := by
    rcases hh with hquick | hhit
    · exact quickFail_sound_review goal mask N J nt k ws hquick
    · exact failTable_lookup_review goal mask N J nt hD hM hO T lookup h k ws hhit
  rw [hf]
  rfl

end PermReview

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def memoRawBlocks : Array (Array (Array (ℕ × List ℕ))) := #[
#[
#[
(2, [204, 32136]),
(2, [220, 32152]),
(2, [255, 580]),
(2, [255, 32187]),
(2, [511, 836]),
(2, [1279, 1604]),
(2, [3327, 3652]),
(2, [3583, 3908]),
(3, [16, 204, 32152]),
(3, [24, 204, 32152]),
(3, [28, 192, 32152]),
(3, [31, 68, 32016]),
(3, [31, 68, 32024]),
(3, [31, 196, 32152]),
(3, [31, 204, 615]),
(3, [31, 204, 32152])
],
#[
(3, [31, 226, 580]),
(3, [31, 226, 32187]),
(3, [31, 482, 836]),
(3, [31, 580, 32541]),
(3, [31, 1250, 1604]),
(3, [31, 3298, 3652]),
(3, [31, 3554, 3908]),
(3, [31, 3652, 32088]),
(3, [31, 4070, 27988]),
(3, [31, 4070, 27994]),
(3, [31, 4267, 28146]),
(3, [31, 4621, 28500]),
(3, [31, 5291, 27122]),
(3, [31, 5645, 27476]),
(3, [31, 13380, 26896]),
(3, [31, 18930, 19284])
],
#[
(3, [31, 27122, 27476]),
(3, [31, 28146, 28500]),
(3, [31, 28154, 28500]),
(3, [31, 28154, 28508]),
(3, [31, 32152, 32563]),
(3, [31, 32187, 32541]),
(3, [31, 32250, 32604]),
(3, [68, 159, 32152]),
(3, [68, 159, 32159]),
(3, [68, 223, 32152]),
(3, [68, 255, 32152]),
(3, [95, 3652, 32024]),
(3, [159, 3652, 32216]),
(3, [159, 32250, 32732]),
(3, [204, 223, 32152]),
(3, [204, 5887, 13448])
],
#[
(3, [204, 13448, 26880]),
(3, [204, 32152, 32736]),
(3, [220, 13448, 26896]),
(3, [220, 13464, 26896]),
(3, [223, 615, 3652]),
(3, [223, 615, 16076]),
(3, [223, 3652, 32152]),
(3, [223, 3652, 32159]),
(3, [223, 3652, 32216]),
(3, [223, 3652, 32223]),
(3, [223, 3780, 32152]),
(3, [223, 16076, 32152]),
(3, [223, 16691, 32152]),
(3, [223, 28500, 32152]),
(3, [223, 29115, 32152]),
(3, [223, 32152, 32732])
],
#[
(3, [226, 1055, 1604]),
(3, [226, 3103, 3652]),
(3, [255, 615, 3652]),
(3, [255, 1024, 1604]),
(3, [255, 1604, 5256]),
(3, [255, 1604, 13448]),
(3, [255, 1604, 13471]),
(3, [255, 1604, 13546]),
(3, [255, 1604, 13567]),
(3, [255, 1604, 13802]),
(3, [255, 1604, 19319]),
(3, [255, 1604, 32152]),
(3, [255, 2628, 5871]),
(3, [255, 2628, 26896]),
(3, [255, 3072, 3652]),
(3, [255, 3652, 4847])
],
#[
(3, [255, 3652, 15496]),
(3, [255, 3652, 27920]),
(3, [255, 3652, 32152]),
(3, [255, 3652, 32159]),
(3, [255, 3652, 32250]),
(3, [255, 3652, 32255]),
(3, [255, 5836, 13448]),
(3, [255, 5871, 30139]),
(3, [255, 13448, 14028]),
(3, [255, 13448, 31163]),
(3, [255, 16076, 32152]),
(3, [255, 26896, 30139]),
(3, [255, 28500, 32152]),
(3, [255, 29115, 32152]),
(3, [255, 32152, 32732]),
(3, [256, 476, 32152])
],
#[
(3, [256, 511, 580]),
(3, [256, 511, 32187]),
(3, [256, 3583, 3652]),
(3, [324, 511, 32152]),
(3, [476, 13471, 32152]),
(3, [482, 3103, 3908]),
(3, [482, 3359, 3908]),
(3, [511, 615, 3908]),
(3, [511, 999, 28500]),
(3, [511, 1860, 13448]),
(3, [511, 2304, 2628]),
(3, [511, 2304, 30139]),
(3, [511, 2628, 5887]),
(3, [511, 2628, 26880]),
(3, [511, 2644, 26896]),
(3, [511, 2884, 26896])
],
#[
(3, [511, 3072, 3908]),
(3, [511, 3328, 3652]),
(3, [511, 3328, 3908]),
(3, [511, 3652, 4863]),
(3, [511, 3652, 27904]),
(3, [511, 3668, 27920]),
(3, [511, 3908, 15496]),
(3, [511, 3908, 15752]),
(3, [511, 3908, 27920]),
(3, [511, 3908, 32152]),
(3, [511, 3908, 32159]),
(3, [511, 3908, 32250]),
(3, [511, 3908, 32255]),
(3, [511, 4070, 27988]),
(3, [511, 5887, 30139]),
(3, [511, 12100, 32152])
],
#[
(3, [511, 12100, 32250]),
(3, [511, 13448, 26948]),
(3, [511, 13464, 26964]),
(3, [511, 13806, 26964]),
(3, [511, 15752, 16076]),
(3, [511, 16076, 32136]),
(3, [511, 16092, 32152]),
(3, [511, 26880, 30139]),
(3, [511, 26896, 29883]),
(3, [511, 26896, 30123]),
(3, [511, 28484, 32136]),
(3, [511, 28484, 32152]),
(3, [511, 28500, 31768]),
(3, [511, 28500, 31896]),
(3, [511, 28859, 32152]),
(3, [1055, 4267, 27122])
],
#[
(3, [1055, 5645, 28500]),
(3, [1055, 27122, 28500]),
(3, [1183, 27122, 28500]),
(3, [1279, 3652, 5871]),
(3, [1279, 3652, 26896]),
(3, [1535, 2304, 3652]),
(3, [1535, 3652, 5887]),
(3, [1535, 3652, 26880]),
(3, [1535, 3668, 26896]),
(3, [1535, 3908, 26896]),
(3, [1604, 13448, 32512]),
(3, [2303, 3652, 13448]),
(3, [2304, 3583, 3652]),
(3, [2559, 3908, 13448]),
(3, [3103, 3652, 32541]),
(3, [3652, 32152, 32512])
],
#[
(3, [3652, 32152, 32544]),
(3, [3908, 32152, 32256]),
(3, [13448, 27135, 28484]),
(3, [16076, 32152, 32544]),
(3, [27122, 27476, 32736]),
(3, [27122, 28500, 31712]),
(3, [28146, 28500, 32736]),
(4, [0, 31, 204, 32152]),
(4, [0, 31, 27122, 27476]),
(4, [0, 31, 28146, 28500]),
(4, [0, 223, 3652, 32152]),
(4, [0, 223, 16076, 32152]),
(4, [0, 255, 1604, 13448]),
(4, [0, 255, 3652, 32152]),
(4, [0, 511, 3908, 32152]),
(4, [0, 1055, 27122, 28500])
],
#[
(4, [4, 31, 192, 32152]),
(4, [12, 31, 192, 32152]),
(4, [16, 204, 13448, 26896]),
(4, [16, 511, 2628, 26896]),
(4, [16, 511, 3652, 27920]),
(4, [16, 511, 13448, 26964]),
(4, [16, 511, 16076, 32152]),
(4, [16, 511, 26896, 30139]),
(4, [16, 511, 28500, 32152]),
(4, [16, 1535, 3652, 26896]),
(4, [16, 13448, 27135, 28500]),
(4, [18, 13448, 27135, 28500]),
(4, [20, 511, 28500, 32152]),
(4, [23, 511, 2628, 26896]),
(4, [24, 511, 16076, 32152]),
(4, [24, 511, 28500, 32152])
],
#[
(4, [27, 482, 26896, 30143]),
(4, [27, 482, 26911, 30139]),
(4, [27, 511, 26896, 30139]),
(4, [28, 192, 13448, 26896]),
(4, [28, 448, 13448, 26896]),
(4, [28, 448, 13448, 32152]),
(4, [28, 448, 26896, 32152]),
(4, [28, 482, 16076, 32152]),
(4, [28, 482, 28500, 32152]),
(4, [28, 13448, 27122, 28500]),
(4, [29, 482, 2628, 26896]),
(4, [29, 482, 3652, 27920]),
(4, [29, 482, 3652, 32024]),
(4, [29, 482, 16076, 32152]),
(4, [29, 482, 26896, 30139]),
(4, [29, 482, 28500, 32152])
],
#[
(4, [29, 1506, 3652, 26896]),
(4, [29, 2628, 26896, 32285]),
(4, [29, 3652, 26896, 31261]),
(4, [29, 3652, 27920, 32285]),
(4, [29, 3652, 32024, 32285]),
(4, [29, 3652, 32152, 32541]),
(4, [29, 13448, 27122, 28500]),
(4, [29, 16076, 32152, 32285]),
(4, [29, 26896, 30139, 32285]),
(4, [29, 28500, 32152, 32285]),
(4, [31, 64, 3652, 32024]),
(4, [31, 68, 128, 32152]),
(4, [31, 68, 136, 32152]),
(4, [31, 68, 13312, 26896]),
(4, [31, 68, 13320, 26896]),
(4, [31, 68, 19447, 26896])
],
#[
(4, [31, 68, 19455, 26896]),
(4, [31, 128, 3652, 32216]),
(4, [31, 128, 32250, 32732]),
(4, [31, 136, 13516, 26896]),
(4, [31, 192, 615, 3652]),
(4, [31, 192, 615, 16076]),
(4, [31, 192, 3652, 32152]),
(4, [31, 192, 3652, 32159]),
(4, [31, 192, 3652, 32216]),
(4, [31, 192, 3780, 32152]),
(4, [31, 192, 16076, 32152]),
(4, [31, 192, 16691, 32152]),
(4, [31, 192, 28500, 32152]),
(4, [31, 192, 29115, 32152]),
(4, [31, 192, 32152, 32732]),
(4, [31, 194, 3652, 32152])
],
#[
(4, [31, 194, 3652, 32159]),
(4, [31, 194, 16076, 32152]),
(4, [31, 196, 13448, 26896]),
(4, [31, 204, 482, 32152]),
(4, [31, 204, 511, 32152]),
(4, [31, 204, 3652, 32152]),
(4, [31, 204, 5871, 13448]),
(4, [31, 204, 13448, 26896]),
(4, [31, 204, 13448, 26911]),
(4, [31, 204, 13448, 27100]),
(4, [31, 204, 13448, 32152]),
(4, [31, 204, 16076, 32152]),
(4, [31, 204, 19319, 26896]),
(4, [31, 204, 26896, 32152]),
(4, [31, 204, 32152]),
(4, [31, 204, 32152, 32767])
]
],
#[
#[
(4, [31, 223, 3652, 32152]),
(4, [31, 223, 16076, 32152]),
(4, [31, 224, 3652, 32152]),
(4, [31, 224, 3652, 32159]),
(4, [31, 226, 615, 3652]),
(4, [31, 226, 1024, 1604]),
(4, [31, 226, 1604, 5256]),
(4, [31, 226, 1604, 13448]),
(4, [31, 226, 1604, 13471]),
(4, [31, 226, 1604, 13546]),
(4, [31, 226, 1604, 13802]),
(4, [31, 226, 1604, 19319]),
(4, [31, 226, 1604, 32152]),
(4, [31, 226, 2628, 5871]),
(4, [31, 226, 2628, 26896]),
(4, [31, 226, 3072, 3652])
],
#[
(4, [31, 226, 3652, 4847]),
(4, [31, 226, 3652, 15496]),
(4, [31, 226, 3652, 27920]),
(4, [31, 226, 3652, 32152]),
(4, [31, 226, 3652, 32159]),
(4, [31, 226, 3652, 32250]),
(4, [31, 226, 5836, 13448]),
(4, [31, 226, 5871, 30139]),
(4, [31, 226, 13448, 14028]),
(4, [31, 226, 13448, 31163]),
(4, [31, 226, 16076, 32152]),
(4, [31, 226, 26896, 30139]),
(4, [31, 226, 28500, 32152]),
(4, [31, 226, 29115, 32152]),
(4, [31, 226, 32152, 32732]),
(4, [31, 239, 1604, 13448])
],
#[
(4, [31, 239, 3652, 32152]),
(4, [31, 255, 1604, 13448]),
(4, [31, 255, 3652, 32152]),
(4, [31, 256, 482, 580]),
(4, [31, 256, 482, 32187]),
(4, [31, 256, 3554, 3652]),
(4, [31, 340, 482, 32152]),
(4, [31, 340, 511, 32152]),
(4, [31, 418, 26896, 30203]),
(4, [31, 443, 13802, 26896]),
(4, [31, 443, 13823, 26896]),
(4, [31, 448, 16076, 32152]),
(4, [31, 448, 28500, 32152]),
(4, [31, 476, 13448, 26896]),
(4, [31, 476, 13448, 32152]),
(4, [31, 476, 26896, 32152])
],
#[
(4, [31, 480, 2628, 26896]),
(4, [31, 480, 3652, 27920]),
(4, [31, 480, 16076, 32152]),
(4, [31, 480, 26896, 30139]),
(4, [31, 480, 28500, 32152]),
(4, [31, 482, 517, 28500]),
(4, [31, 482, 580, 4847]),
(4, [31, 482, 580, 5871]),
(4, [31, 482, 580, 14063]),
(4, [31, 482, 580, 26896]),
(4, [31, 482, 580, 26911]),
(4, [31, 482, 580, 27476]),
(4, [31, 482, 580, 27920]),
(4, [31, 482, 580, 28500]),
(4, [31, 482, 615, 3780]),
(4, [31, 482, 615, 3908])
],
#[
(4, [31, 482, 615, 4267]),
(4, [31, 482, 615, 14028]),
(4, [31, 482, 615, 16076]),
(4, [31, 482, 615, 16691]),
(4, [31, 482, 615, 27476]),
(4, [31, 482, 615, 28500]),
(4, [31, 482, 743, 3652]),
(4, [31, 482, 999, 28500]),
(4, [31, 482, 1604, 5354]),
(4, [31, 482, 1604, 13546]),
(4, [31, 482, 1604, 27920]),
(4, [31, 482, 1860, 13448]),
(4, [31, 482, 2304, 2628]),
(4, [31, 482, 2304, 30139]),
(4, [31, 482, 2628, 5856]),
(4, [31, 482, 2628, 5871])
],
#[
(4, [31, 482, 2628, 5887]),
(4, [31, 482, 2628, 14063]),
(4, [31, 482, 2628, 18704]),
(4, [31, 482, 2628, 18711]),
(4, [31, 482, 2628, 18719]),
(4, [31, 482, 2628, 26880]),
(4, [31, 482, 2628, 26896]),
(4, [31, 482, 2628, 26898]),
(4, [31, 482, 2628, 26900]),
(4, [31, 482, 2628, 26903]),
(4, [31, 482, 2628, 26904]),
(4, [31, 482, 2628, 26911]),
(4, [31, 482, 2628, 26960]),
(4, [31, 482, 2628, 27920]),
(4, [31, 482, 2630, 26896]),
(4, [31, 482, 2644, 26896])
],
#[
(4, [31, 482, 2884, 26896]),
(4, [31, 482, 3072, 3908]),
(4, [31, 482, 3328, 3652]),
(4, [31, 482, 3328, 3908]),
(4, [31, 482, 3652, 4783]),
(4, [31, 482, 3652, 4832]),
(4, [31, 482, 3652, 4839]),
(4, [31, 482, 3652, 4843]),
(4, [31, 482, 3652, 4847]),
(4, [31, 482, 3652, 4863]),
(4, [31, 482, 3652, 19728]),
(4, [31, 482, 3652, 27904]),
(4, [31, 482, 3652, 27920]),
(4, [31, 482, 3652, 27922]),
(4, [31, 482, 3652, 27924]),
(4, [31, 482, 3652, 27928])
],
#[
(4, [31, 482, 3652, 27935]),
(4, [31, 482, 3652, 27984]),
(4, [31, 482, 3652, 27988]),
(4, [31, 482, 3652, 27994]),
(4, [31, 482, 3652, 27999]),
(4, [31, 482, 3652, 32016]),
(4, [31, 482, 3652, 32024]),
(4, [31, 482, 3652, 32029]),
(4, [31, 482, 3652, 32031]),
(4, [31, 482, 3654, 27920]),
(4, [31, 482, 3660, 27928]),
(4, [31, 482, 3668, 27920]),
(4, [31, 482, 3780, 28048]),
(4, [31, 482, 3780, 32152]),
(4, [31, 482, 3780, 32159]),
(4, [31, 482, 3782, 32152])
],
#[
(4, [31, 482, 3782, 32159]),
(4, [31, 482, 3788, 32152]),
(4, [31, 482, 3908, 15496]),
(4, [31, 482, 3908, 15752]),
(4, [31, 482, 3908, 27920]),
(4, [31, 482, 3908, 32152]),
(4, [31, 482, 3908, 32159]),
(4, [31, 482, 3908, 32250]),
(4, [31, 482, 3910, 32152]),
(4, [31, 482, 3910, 32159]),
(4, [31, 482, 3924, 32152]),
(4, [31, 482, 4070, 27984]),
(4, [31, 482, 4267, 27920]),
(4, [31, 482, 4267, 32152]),
(4, [31, 482, 4267, 32187]),
(4, [31, 482, 4267, 32250])
],
#[
(4, [31, 482, 4847, 28500]),
(4, [31, 482, 4847, 29115]),
(4, [31, 482, 5291, 5871]),
(4, [31, 482, 5291, 26896]),
(4, [31, 482, 5836, 32152]),
(4, [31, 482, 5856, 30139]),
(4, [31, 482, 5871, 13483]),
(4, [31, 482, 5871, 19284]),
(4, [31, 482, 5871, 27476]),
(4, [31, 482, 5871, 30139]),
(4, [31, 482, 5871, 32187]),
(4, [31, 482, 5887, 30139]),
(4, [31, 482, 7884, 32152]),
(4, [31, 482, 10820, 26896]),
(4, [31, 482, 11844, 27920]),
(4, [31, 482, 11972, 32152])
],
#[
(4, [31, 482, 12100, 32152]),
(4, [31, 482, 12100, 32250]),
(4, [31, 482, 13483, 26896]),
(4, [31, 482, 13483, 27122]),
(4, [31, 482, 13483, 31163]),
(4, [31, 482, 13483, 32152]),
(4, [31, 482, 13483, 32187]),
(4, [31, 482, 13516, 26964]),
(4, [31, 482, 13516, 32152]),
(4, [31, 482, 13755, 26896]),
(4, [31, 482, 14028, 32152]),
(4, [31, 482, 14063, 30139]),
(4, [31, 482, 15752, 16076]),
(4, [31, 482, 15948, 32024]),
(4, [31, 482, 16068, 32144]),
(4, [31, 482, 16068, 32152])
],
#[
(4, [31, 482, 16076, 32136]),
(4, [31, 482, 16076, 32152]),
(4, [31, 482, 16076, 32154]),
(4, [31, 482, 16078, 32152]),
(4, [31, 482, 16078, 32154]),
(4, [31, 482, 16092, 32152]),
(4, [31, 482, 16691, 32152]),
(4, [31, 482, 18704, 19284]),
(4, [31, 482, 18704, 30139]),
(4, [31, 482, 19284, 26896]),
(4, [31, 482, 19284, 27122]),
(4, [31, 482, 19284, 32152]),
(4, [31, 482, 20308, 32152]),
(4, [31, 482, 24848, 32187]),
(4, [31, 482, 26880, 30139]),
(4, [31, 482, 26896, 27476])
],
#[
(4, [31, 482, 26896, 29883]),
(4, [31, 482, 26896, 30123]),
(4, [31, 482, 26896, 30137]),
(4, [31, 482, 26896, 30139]),
(4, [31, 482, 26896, 32187]),
(4, [31, 482, 26898, 30139]),
(4, [31, 482, 26900, 30139]),
(4, [31, 482, 26904, 30139]),
(4, [31, 482, 26907, 30139]),
(4, [31, 482, 26911, 30139]),
(4, [31, 482, 26911, 32187]),
(4, [31, 482, 26931, 32152]),
(4, [31, 482, 26960, 30139]),
(4, [31, 482, 26964, 32152]),
(4, [31, 482, 27122, 27476]),
(4, [31, 482, 27476, 32152])
],
#[
(4, [31, 482, 27920, 28500]),
(4, [31, 482, 27920, 29115]),
(4, [31, 482, 27920, 30139]),
(4, [31, 482, 27920, 31163]),
(4, [31, 482, 27920, 32187]),
(4, [31, 482, 27924, 29115]),
(4, [31, 482, 27928, 28500]),
(4, [31, 482, 27928, 28508]),
(4, [31, 482, 27928, 29115]),
(4, [31, 482, 27935, 29115]),
(4, [31, 482, 27984, 28500]),
(4, [31, 482, 27984, 29115]),
(4, [31, 482, 28048, 28500]),
(4, [31, 482, 28146, 28500]),
(4, [31, 482, 28484, 32136]),
(4, [31, 482, 28484, 32152])
],
#[
(4, [31, 482, 28500, 31768]),
(4, [31, 482, 28500, 31896]),
(4, [31, 482, 28500, 32024]),
(4, [31, 482, 28500, 32144]),
(4, [31, 482, 28500, 32152]),
(4, [31, 482, 28500, 32154]),
(4, [31, 482, 28500, 32187]),
(4, [31, 482, 28500, 32216]),
(4, [31, 482, 28500, 32250]),
(4, [31, 482, 28502, 32152]),
(4, [31, 482, 28502, 32154]),
(4, [31, 482, 28508, 32152]),
(4, [31, 482, 28859, 32152]),
(4, [31, 482, 28987, 32152]),
(4, [31, 482, 29115, 32024]),
(4, [31, 482, 32024, 32604])
],
#[
(4, [31, 486, 2628, 26896]),
(4, [31, 486, 3652, 27920]),
(4, [31, 486, 13448, 26964]),
(4, [31, 486, 16076, 32152]),
(4, [31, 486, 26896, 30139]),
(4, [31, 486, 28500, 32152]),
(4, [31, 490, 2628, 26896]),
(4, [31, 490, 3652, 27920]),
(4, [31, 490, 16076, 32152]),
(4, [31, 490, 26896, 30139]),
(4, [31, 490, 28500, 32152]),
(4, [31, 494, 16076, 32152]),
(4, [31, 498, 2628, 26896]),
(4, [31, 498, 3652, 27920]),
(4, [31, 498, 16076, 32152]),
(4, [31, 498, 26896, 30139])
]
],
#[
#[
(4, [31, 498, 28500, 32152]),
(4, [31, 502, 28500, 32152]),
(4, [31, 503, 2628, 26896]),
(4, [31, 506, 16076, 32152]),
(4, [31, 506, 28500, 32152]),
(4, [31, 507, 26896, 30139]),
(4, [31, 511, 580, 26896]),
(4, [31, 511, 615, 16076]),
(4, [31, 511, 615, 28500]),
(4, [31, 511, 2628, 5871]),
(4, [31, 511, 2628, 18704]),
(4, [31, 511, 2628, 26896]),
(4, [31, 511, 2628, 26911]),
(4, [31, 511, 3652, 4847]),
(4, [31, 511, 3652, 27920]),
(4, [31, 511, 3652, 27924])
],
#[
(4, [31, 511, 3652, 27928]),
(4, [31, 511, 3652, 27935]),
(4, [31, 511, 3652, 27984]),
(4, [31, 511, 3652, 27988]),
(4, [31, 511, 3652, 32016]),
(4, [31, 511, 3652, 32024]),
(4, [31, 511, 3780, 32152]),
(4, [31, 511, 3788, 32152]),
(4, [31, 511, 3908, 32152]),
(4, [31, 511, 3924, 32152]),
(4, [31, 511, 4267, 32152]),
(4, [31, 511, 5871, 30139]),
(4, [31, 511, 13483, 26896]),
(4, [31, 511, 13516, 26964]),
(4, [31, 511, 13516, 32152]),
(4, [31, 511, 13755, 26896])
],
#[
(4, [31, 511, 16691, 32152]),
(4, [31, 511, 19284, 26896]),
(4, [31, 511, 26896, 27476]),
(4, [31, 511, 26896, 30139]),
(4, [31, 511, 26896, 32187]),
(4, [31, 511, 26911, 30139]),
(4, [31, 511, 26964, 32152]),
(4, [31, 511, 27920, 28500]),
(4, [31, 511, 27920, 29115]),
(4, [31, 511, 28500, 32250]),
(4, [31, 517, 27122, 28500]),
(4, [31, 580, 26896, 27122]),
(4, [31, 580, 26896, 32285]),
(4, [31, 615, 3652, 32541]),
(4, [31, 615, 16076, 32285]),
(4, [31, 615, 27122, 28500])
],
#[
(4, [31, 615, 28500, 32285]),
(4, [31, 743, 3652, 32285]),
(4, [31, 1024, 4267, 27122]),
(4, [31, 1024, 5645, 28500]),
(4, [31, 1024, 27122, 28500]),
(4, [31, 1024, 28146, 28500]),
(4, [31, 1028, 27122, 28500]),
(4, [31, 1032, 27122, 28500]),
(4, [31, 1055, 27122, 28500]),
(4, [31, 1088, 27122, 28500]),
(4, [31, 1092, 4070, 26896]),
(4, [31, 1092, 4095, 26896]),
(4, [31, 1098, 4070, 26896]),
(4, [31, 1152, 27122, 28500]),
(4, [31, 1250, 3652, 5871]),
(4, [31, 1250, 3652, 26896])
],
#[
(4, [31, 1504, 3652, 26896]),
(4, [31, 1506, 1604, 5871]),
(4, [31, 1506, 1604, 26896]),
(4, [31, 1506, 2304, 3652]),
(4, [31, 1506, 3652, 4847]),
(4, [31, 1506, 3652, 5856]),
(4, [31, 1506, 3652, 5871]),
(4, [31, 1506, 3652, 5887]),
(4, [31, 1506, 3652, 14063]),
(4, [31, 1506, 3652, 18704]),
(4, [31, 1506, 3652, 26880]),
(4, [31, 1506, 3652, 26896]),
(4, [31, 1506, 3652, 26898]),
(4, [31, 1506, 3652, 26900]),
(4, [31, 1506, 3652, 26904]),
(4, [31, 1506, 3652, 26911])
],
#[
(4, [31, 1506, 3652, 26960]),
(4, [31, 1506, 3652, 27920]),
(4, [31, 1506, 3652, 27935]),
(4, [31, 1506, 3652, 27984]),
(4, [31, 1506, 3654, 26896]),
(4, [31, 1506, 3668, 26896]),
(4, [31, 1506, 3908, 26896]),
(4, [31, 1506, 4267, 26896]),
(4, [31, 1506, 5871, 28500]),
(4, [31, 1506, 5871, 29115]),
(4, [31, 1506, 11844, 26896]),
(4, [31, 1506, 26896, 28500]),
(4, [31, 1506, 26896, 29115]),
(4, [31, 1506, 26896, 31163]),
(4, [31, 1506, 26911, 29115]),
(4, [31, 1506, 27122, 28500])
],
#[
(4, [31, 1506, 27920, 28500]),
(4, [31, 1506, 27920, 29115]),
(4, [31, 1506, 28146, 28500]),
(4, [31, 1506, 28500, 32152]),
(4, [31, 1510, 3652, 5871]),
(4, [31, 1510, 3652, 26896]),
(4, [31, 1510, 3652, 26911]),
(4, [31, 1510, 3652, 27924]),
(4, [31, 1510, 26896, 28500]),
(4, [31, 1510, 26896, 29115]),
(4, [31, 1514, 3652, 5871]),
(4, [31, 1514, 3652, 26896]),
(4, [31, 1514, 3652, 26911]),
(4, [31, 1514, 3652, 27928]),
(4, [31, 1514, 3660, 26896]),
(4, [31, 1514, 26896, 28500])
],
#[
(4, [31, 1514, 26896, 29115]),
(4, [31, 1522, 3652, 26896]),
(4, [31, 1535, 3652, 5871]),
(4, [31, 1535, 3652, 26896]),
(4, [31, 1535, 3652, 26911]),
(4, [31, 1535, 3652, 27920]),
(4, [31, 1535, 3652, 27935]),
(4, [31, 1535, 26896, 28500]),
(4, [31, 1535, 26896, 29115]),
(4, [31, 1604, 13448, 32541]),
(4, [31, 1766, 3652, 13802]),
(4, [31, 2274, 3652, 13448]),
(4, [31, 2304, 3554, 3652]),
(4, [31, 2530, 2628, 26896]),
(4, [31, 2530, 3652, 27920]),
(4, [31, 2530, 3908, 13448])
],
#[
(4, [31, 2530, 26896, 30139]),
(4, [31, 2530, 28500, 32152]),
(4, [31, 2628, 5645, 26896]),
(4, [31, 2628, 5871, 27122]),
(4, [31, 2628, 5871, 32285]),
(4, [31, 2628, 8674, 26896]),
(4, [31, 2628, 18704, 18930]),
(4, [31, 2628, 18704, 32285]),
(4, [31, 2628, 18930, 26896]),
(4, [31, 2628, 26896, 27122]),
(4, [31, 2628, 26896, 27135]),
(4, [31, 2628, 26896, 32256]),
(4, [31, 2628, 26896, 32285]),
(4, [31, 2628, 26896, 32287]),
(4, [31, 2628, 26896, 32541]),
(4, [31, 2628, 26911, 27122])
],
#[
(4, [31, 2628, 26911, 27135]),
(4, [31, 2628, 26911, 32285]),
(4, [31, 2628, 27122, 27476]),
(4, [31, 2628, 27122, 28500]),
(4, [31, 3072, 3652, 32541]),
(4, [31, 3072, 27122, 28500]),
(4, [31, 3136, 27122, 28500]),
(4, [31, 3554, 3652, 5871]),
(4, [31, 3554, 3652, 26896]),
(4, [31, 3554, 3652, 26911]),
(4, [31, 3554, 3652, 27920]),
(4, [31, 3554, 3652, 28500]),
(4, [31, 3554, 26896, 28500]),
(4, [31, 3554, 26896, 29115]),
(4, [31, 3554, 28500, 32152]),
(4, [31, 3558, 3652, 26896])
],
#[
(4, [31, 3558, 3652, 26911]),
(4, [31, 3578, 3652, 26896]),
(4, [31, 3583, 3652, 26896]),
(4, [31, 3588, 3652, 32024]),
(4, [31, 3652, 4070, 27984]),
(4, [31, 3652, 4621, 26896]),
(4, [31, 3652, 4621, 27920]),
(4, [31, 3652, 4847, 27122]),
(4, [31, 3652, 4847, 28146]),
(4, [31, 3652, 4847, 32285]),
(4, [31, 3652, 5354, 27122]),
(4, [31, 3652, 5645, 27920]),
(4, [31, 3652, 5645, 32024]),
(4, [31, 3652, 5871, 9698]),
(4, [31, 3652, 5871, 28146]),
(4, [31, 3652, 5871, 31261])
],
#[
(4, [31, 3652, 8674, 27920]),
(4, [31, 3652, 9698, 26896]),
(4, [31, 3652, 9698, 26911]),
(4, [31, 3652, 9698, 27920]),
(4, [31, 3652, 9706, 26896]),
(4, [31, 3652, 9706, 26911]),
(4, [31, 3652, 9718, 26896]),
(4, [31, 3652, 9727, 26896]),
(4, [31, 3652, 13320, 26960]),
(4, [31, 3652, 13384, 26896]),
(4, [31, 3652, 13802, 31001]),
(4, [31, 3652, 13802, 32024]),
(4, [31, 3652, 15496, 32541]),
(4, [31, 3652, 19447, 26960]),
(4, [31, 3652, 23069, 26896]),
(4, [31, 3652, 26896, 28146])
],
#[
(4, [31, 3652, 26896, 28150]),
(4, [31, 3652, 26896, 28154]),
(4, [31, 3652, 26896, 28159]),
(4, [31, 3652, 26896, 29213]),
(4, [31, 3652, 26896, 31232]),
(4, [31, 3652, 26896, 31253]),
(4, [31, 3652, 26896, 31257]),
(4, [31, 3652, 26896, 31261]),
(4, [31, 3652, 26896, 31263]),
(4, [31, 3652, 26896, 31517]),
(4, [31, 3652, 26911, 28146]),
(4, [31, 3652, 26911, 28159]),
(4, [31, 3652, 26911, 31261]),
(4, [31, 3652, 27122, 27413]),
(4, [31, 3652, 27122, 27476]),
(4, [31, 3652, 27122, 27920])
],
#[
(4, [31, 3652, 27122, 27924]),
(4, [31, 3652, 27122, 27928]),
(4, [31, 3652, 27122, 27935]),
(4, [31, 3652, 27122, 27984]),
(4, [31, 3652, 27122, 32024]),
(4, [31, 3652, 27135, 27920]),
(4, [31, 3652, 27135, 27935]),
(4, [31, 3652, 27920, 28146]),
(4, [31, 3652, 27920, 28159]),
(4, [31, 3652, 27920, 31261]),
(4, [31, 3652, 27920, 32256]),
(4, [31, 3652, 27920, 32285]),
(4, [31, 3652, 27920, 32287]),
(4, [31, 3652, 27920, 32541]),
(4, [31, 3652, 27924, 28150]),
(4, [31, 3652, 27924, 32285])
],
#[
(4, [31, 3652, 27928, 28154]),
(4, [31, 3652, 27928, 32285]),
(4, [31, 3652, 27935, 28146]),
(4, [31, 3652, 27935, 28159]),
(4, [31, 3652, 27935, 32285]),
(4, [31, 3652, 27984, 28146]),
(4, [31, 3652, 27984, 32285]),
(4, [31, 3652, 28146, 28500]),
(4, [31, 3652, 31768, 32541]),
(4, [31, 3652, 31896, 32541]),
(4, [31, 3652, 32016, 32256]),
(4, [31, 3652, 32024, 32250]),
(4, [31, 3652, 32024, 32285]),
(4, [31, 3652, 32024, 32287]),
(4, [31, 3652, 32024, 32413]),
(4, [31, 3652, 32024, 32541])
],
#[
(4, [31, 3652, 32029, 32285]),
(4, [31, 3652, 32031, 32285]),
(4, [31, 3652, 32152, 32528]),
(4, [31, 3652, 32152, 32541]),
(4, [31, 3652, 32152, 32543]),
(4, [31, 3652, 32152, 32575]),
(4, [31, 3652, 32159, 32541]),
(4, [31, 3652, 32159, 32543]),
(4, [31, 3652, 32250, 32541]),
(4, [31, 3780, 13448, 27088]),
(4, [31, 3780, 32152, 32285]),
(4, [31, 3908, 32152, 32285]),
(4, [31, 4070, 13802, 27984]),
(4, [31, 4070, 28500, 32250]),
(4, [31, 4267, 5645, 13448]),
(4, [31, 4267, 9216, 27122])
]
],
#[
#[
(4, [31, 4267, 9698, 26896]),
(4, [31, 4267, 13448, 27122]),
(4, [31, 4267, 13471, 27122]),
(4, [31, 4267, 13483, 27122]),
(4, [31, 4267, 13802, 27122]),
(4, [31, 4267, 19319, 27122]),
(4, [31, 4267, 27122, 32152]),
(4, [31, 4267, 27122, 32250]),
(4, [31, 4267, 32152, 32285]),
(4, [31, 5128, 5645, 28500]),
(4, [31, 5128, 27122, 28500]),
(4, [31, 5256, 27122, 28500]),
(4, [31, 5645, 9216, 28500]),
(4, [31, 5645, 13448, 28500]),
(4, [31, 5645, 13471, 28500]),
(4, [31, 5645, 13802, 28500])
],
#[
(4, [31, 5645, 19319, 28500]),
(4, [31, 5645, 26896, 30139]),
(4, [31, 5645, 28500, 32152]),
(4, [31, 5645, 28500, 32250]),
(4, [31, 5871, 9698, 28500]),
(4, [31, 5871, 27122, 30139]),
(4, [31, 5871, 30139, 32285]),
(4, [31, 8674, 26896, 30139]),
(4, [31, 8674, 28500, 32152]),
(4, [31, 9216, 27122, 28500]),
(4, [31, 9216, 28146, 28500]),
(4, [31, 9224, 27122, 28500]),
(4, [31, 9236, 27122, 28500]),
(4, [31, 9247, 27122, 28500]),
(4, [31, 9344, 27122, 28500]),
(4, [31, 9536, 27122, 28500])
],
#[
(4, [31, 9698, 11844, 26896]),
(4, [31, 9698, 26896, 28500]),
(4, [31, 9698, 26896, 29115]),
(4, [31, 9698, 27122, 28500]),
(4, [31, 9698, 27920, 28500]),
(4, [31, 9698, 28146, 28500]),
(4, [31, 9698, 28500, 32152]),
(4, [31, 9706, 26896, 28500]),
(4, [31, 9718, 26896, 28500]),
(4, [31, 9727, 26896, 28500]),
(4, [31, 10444, 13448, 26896]),
(4, [31, 10444, 13448, 26911]),
(4, [31, 12100, 13802, 27122]),
(4, [31, 13320, 27122, 28500]),
(4, [31, 13440, 27122, 28500]),
(4, [31, 13448, 18930, 20308])
],
#[
(4, [31, 13448, 18930, 28500]),
(4, [31, 13448, 26896, 27100]),
(4, [31, 13448, 26896, 32563]),
(4, [31, 13448, 26964, 27122]),
(4, [31, 13448, 27088, 28500]),
(4, [31, 13448, 27106, 28484]),
(4, [31, 13448, 27120, 28500]),
(4, [31, 13448, 27122, 27476]),
(4, [31, 13448, 27122, 28484]),
(4, [31, 13448, 27122, 28500]),
(4, [31, 13448, 27122, 28502]),
(4, [31, 13448, 27122, 28508]),
(4, [31, 13448, 27130, 28500]),
(4, [31, 13448, 27130, 28508]),
(4, [31, 13448, 28146, 28500]),
(4, [31, 13448, 31163, 32541])
],
#[
(4, [31, 13450, 27122, 28500]),
(4, [31, 13452, 27122, 28500]),
(4, [31, 13464, 27122, 28500]),
(4, [31, 13466, 27122, 28500]),
(4, [31, 13468, 27122, 28500]),
(4, [31, 13483, 26896, 27122]),
(4, [31, 13483, 26896, 32285]),
(4, [31, 13483, 27122, 28500]),
(4, [31, 13512, 27122, 28500]),
(4, [31, 13704, 27122, 28500]),
(4, [31, 13768, 27122, 28500]),
(4, [31, 13802, 15948, 26896]),
(4, [31, 13802, 26896, 32324]),
(4, [31, 13823, 26896, 32324]),
(4, [31, 13823, 27122, 28500]),
(4, [31, 15496, 27122, 28500])
],
#[
(4, [31, 15560, 27122, 28500]),
(4, [31, 15884, 16076, 32152]),
(4, [31, 15948, 32024, 32285]),
(4, [31, 16076, 16883, 32152]),
(4, [31, 16076, 32152, 32256]),
(4, [31, 16076, 32152, 32287]),
(4, [31, 16076, 32152, 32541]),
(4, [31, 16076, 32152, 32575]),
(4, [31, 16691, 16883, 32152]),
(4, [31, 16691, 32152, 32285]),
(4, [31, 16883, 26896, 30139]),
(4, [31, 18930, 19319, 20308]),
(4, [31, 18930, 19319, 28500]),
(4, [31, 18965, 27122, 28500]),
(4, [31, 19284, 26896, 27122]),
(4, [31, 19284, 26896, 32285])
],
#[
(4, [31, 19284, 27122, 28500]),
(4, [31, 19296, 27122, 28500]),
(4, [31, 19319, 27122, 27476]),
(4, [31, 19327, 27122, 28500]),
(4, [31, 19447, 27122, 28500]),
(4, [31, 23069, 26896, 28500]),
(4, [31, 23551, 27122, 28500]),
(4, [31, 24848, 27122, 30139]),
(4, [31, 25074, 26896, 30139]),
(4, [31, 26896, 27122, 27476]),
(4, [31, 26896, 27122, 30139]),
(4, [31, 26896, 27122, 32187]),
(4, [31, 26896, 27135, 30139]),
(4, [31, 26896, 27476, 32285]),
(4, [31, 26896, 28146, 28500]),
(4, [31, 26896, 28146, 29115])
],
#[
(4, [31, 26896, 28500, 31261]),
(4, [31, 26896, 29115, 31261]),
(4, [31, 26896, 30139, 32256]),
(4, [31, 26896, 30139, 32285]),
(4, [31, 26896, 30139, 32287]),
(4, [31, 26896, 30139, 32541]),
(4, [31, 26896, 32187, 32285]),
(4, [31, 26911, 27122, 30139]),
(4, [31, 26911, 27135, 30139]),
(4, [31, 26911, 30139, 32285]),
(4, [31, 27122, 27476]),
(4, [31, 27122, 27476, 32767]),
(4, [31, 27122, 27511, 28500]),
(4, [31, 27122, 27639, 28500]),
(4, [31, 27122, 27920, 28500]),
(4, [31, 27122, 27920, 29115])
],
#[
(4, [31, 27122, 27984, 28500]),
(4, [31, 27122, 28146, 28500]),
(4, [31, 27122, 28500, 30139]),
(4, [31, 27122, 28500, 31743]),
(4, [31, 27122, 28500, 32159]),
(4, [31, 27122, 28500, 32216]),
(4, [31, 27122, 28500, 32250]),
(4, [31, 27122, 28500, 32255]),
(4, [31, 27135, 28500, 32152]),
(4, [31, 27135, 28500, 32250]),
(4, [31, 27920, 28146, 28500]),
(4, [31, 27920, 28146, 29115]),
(4, [31, 27920, 28500, 32285]),
(4, [31, 27920, 29115, 32285]),
(4, [31, 28146, 28500]),
(4, [31, 28146, 28500, 32152])
],
#[
(4, [31, 28146, 28500, 32767]),
(4, [31, 28500, 28662, 32250]),
(4, [31, 28500, 31768, 32285]),
(4, [31, 28500, 31896, 32285]),
(4, [31, 28500, 32024, 32285]),
(4, [31, 28500, 32152, 32256]),
(4, [31, 28500, 32152, 32287]),
(4, [31, 28500, 32152, 32541]),
(4, [31, 28500, 32250, 32285]),
(4, [31, 29115, 32024, 32285]),
(4, [31, 29115, 32152, 32541]),
(4, [31, 32024, 32285, 32604]),
(4, [31, 32152, 32541, 32732]),
(4, [64, 159, 3652, 32152]),
(4, [68, 159, 13448, 26896]),
(4, [68, 159, 13471, 26896])
],
#[
(4, [68, 223, 13448, 26896]),
(4, [68, 255, 5871, 13448]),
(4, [68, 255, 13448, 26896]),
(4, [68, 256, 511, 32152]),
(4, [68, 511, 5871, 13471]),
(4, [68, 511, 5871, 13802]),
(4, [68, 511, 5887, 13448]),
(4, [68, 511, 13448, 26880]),
(4, [68, 511, 13464, 26896]),
(4, [68, 511, 13471, 26896]),
(4, [68, 511, 13471, 26911]),
(4, [68, 511, 13471, 26964]),
(4, [68, 511, 13471, 32152]),
(4, [68, 511, 13471, 32159]),
(4, [68, 511, 13535, 26896]),
(4, [68, 511, 13704, 26896])
],
#[
(4, [68, 511, 13802, 26896]),
(4, [68, 511, 13802, 26964]),
(4, [68, 511, 13806, 26896]),
(4, [68, 511, 18965, 26896]),
(4, [68, 511, 19296, 26896]),
(4, [68, 13471, 26896, 32256]),
(4, [68, 13802, 26896, 32256]),
(4, [84, 511, 13448, 26896]),
(4, [95, 128, 3652, 32152]),
(4, [95, 482, 2628, 26896]),
(4, [95, 482, 3652, 27920]),
(4, [95, 482, 16076, 32152]),
(4, [95, 482, 26896, 30139]),
(4, [95, 482, 28500, 32152]),
(4, [95, 1506, 3652, 26896]),
(4, [95, 3652, 13320, 26896])
],
#[
(4, [95, 3652, 19447, 26896]),
(4, [159, 482, 615, 3652]),
(4, [159, 482, 2628, 26896]),
(4, [159, 482, 3652, 27920]),
(4, [159, 482, 3652, 32152]),
(4, [159, 482, 3652, 32159]),
(4, [159, 482, 3780, 32152]),
(4, [159, 482, 16076, 32152]),
(4, [159, 482, 26896, 30139]),
(4, [159, 482, 28500, 32152]),
(4, [159, 482, 29115, 32152]),
(4, [159, 482, 32152, 32732]),
(4, [159, 511, 3652, 32152]),
(4, [159, 511, 3652, 32159]),
(4, [159, 1506, 3652, 26896]),
(4, [159, 3652, 13448, 26960])
],
#[
(4, [159, 3652, 13512, 26896]),
(4, [159, 3652, 13802, 32152]),
(4, [159, 3652, 27122, 32152]),
(4, [159, 3652, 32152, 32250]),
(4, [159, 3652, 32152, 32285]),
(4, [159, 13448, 27122, 28500]),
(4, [159, 13802, 16076, 26896]),
(4, [192, 223, 3652, 32152]),
(4, [192, 223, 16076, 32152]),
(4, [192, 3652, 32152, 32736]),
(4, [192, 16076, 32152, 32736]),
(4, [204, 223, 13448, 26896]),
(4, [204, 482, 511, 32152]),
(4, [204, 13448, 13471, 26896]),
(4, [204, 13448, 26896, 32736]),
(4, [223, 482, 3652, 32152])
],
#[
(4, [223, 482, 16076, 32152]),
(4, [223, 3652, 5871, 13448]),
(4, [223, 3652, 13448, 26896]),
(4, [223, 3652, 13448, 26911]),
(4, [223, 3652, 13448, 27088]),
(4, [223, 3652, 13448, 27103]),
(4, [223, 3652, 13448, 32152]),
(4, [223, 3652, 13471, 26896]),
(4, [223, 3652, 13512, 26896]),
(4, [223, 3652, 13535, 26896]),
(4, [223, 3652, 16076, 32152]),
(4, [223, 3652, 19319, 26896]),
(4, [223, 3652, 26896, 32152]),
(4, [223, 3652, 32152]),
(4, [223, 3652, 32152, 32767]),
(4, [223, 3780, 13448, 26896])
],
#[
(4, [223, 5871, 13448, 16076]),
(4, [223, 13448, 16076, 26896]),
(4, [223, 13448, 16076, 26911]),
(4, [223, 13448, 16076, 27088]),
(4, [223, 13448, 16076, 27103]),
(4, [223, 13448, 16076, 32152]),
(4, [223, 13448, 16691, 26896]),
(4, [223, 13448, 26896, 28500]),
(4, [223, 13448, 26896, 29115]),
(4, [223, 13448, 26896, 32732]),
(4, [223, 16076, 19319, 26896]),
(4, [223, 16076, 26896, 32152]),
(4, [223, 16076, 32152]),
(4, [223, 16076, 32152, 32767]),
(4, [226, 255, 1604, 13448]),
(4, [226, 255, 3652, 32152])
]
],
#[
#[
(4, [226, 1055, 3652, 5871]),
(4, [226, 1055, 3652, 26896]),
(4, [226, 1604, 13448, 32736]),
(4, [226, 2079, 3652, 13448]),
(4, [226, 3652, 32152, 32736]),
(4, [239, 3652, 5887, 13448]),
(4, [255, 482, 1604, 13448]),
(4, [255, 482, 3652, 32152]),
(4, [255, 1024, 3652, 5871]),
(4, [255, 1024, 3652, 26896]),
(4, [255, 1604, 3652, 13448]),
(4, [255, 1604, 5871, 13448]),
(4, [255, 1604, 13448]),
(4, [255, 1604, 13448, 26896]),
(4, [255, 1604, 13448, 32767]),
(4, [255, 2048, 3652, 13448])
],
#[
(4, [255, 3652, 5256, 5871]),
(4, [255, 3652, 5256, 26896]),
(4, [255, 3652, 5856, 13448]),
(4, [255, 3652, 5871, 13448]),
(4, [255, 3652, 5871, 13471]),
(4, [255, 3652, 5871, 13546]),
(4, [255, 3652, 5871, 13567]),
(4, [255, 3652, 5871, 13802]),
(4, [255, 3652, 5871, 19319]),
(4, [255, 3652, 5871, 32152]),
(4, [255, 3652, 5887, 13448]),
(4, [255, 3652, 6127, 13448]),
(4, [255, 3652, 13448, 14063]),
(4, [255, 3652, 13448, 26896]),
(4, [255, 3652, 13448, 26911]),
(4, [255, 3652, 13448, 27122])
],
#[
(4, [255, 3652, 13448, 27135]),
(4, [255, 3652, 13448, 32152]),
(4, [255, 3652, 13471, 26896]),
(4, [255, 3652, 13546, 26896]),
(4, [255, 3652, 13567, 26896]),
(4, [255, 3652, 13802, 26896]),
(4, [255, 3652, 19319, 26896]),
(4, [255, 3652, 26896, 32152]),
(4, [255, 3652, 32152]),
(4, [255, 3652, 32152, 32767]),
(4, [255, 5871, 13448, 16076]),
(4, [255, 5871, 13448, 28500]),
(4, [255, 5871, 13448, 29115]),
(4, [255, 13448, 16076, 26896]),
(4, [255, 13448, 26896, 28500]),
(4, [255, 13448, 26896, 29115])
],
#[
(4, [256, 482, 3103, 3652]),
(4, [256, 511, 615, 3652]),
(4, [256, 511, 1604, 13448]),
(4, [256, 511, 2628, 26896]),
(4, [256, 511, 3072, 3652]),
(4, [256, 511, 3652, 15496]),
(4, [256, 511, 3652, 27920]),
(4, [256, 511, 3652, 32152]),
(4, [256, 511, 3652, 32159]),
(4, [256, 511, 3652, 32250]),
(4, [256, 511, 3652, 32255]),
(4, [256, 511, 3908, 32152]),
(4, [256, 511, 13448, 31163]),
(4, [256, 511, 16076, 32152]),
(4, [256, 511, 26896, 30139]),
(4, [256, 511, 28500, 32152])
],
#[
(4, [256, 511, 29115, 32152]),
(4, [256, 511, 32152, 32732]),
(4, [256, 1535, 3652, 26896]),
(4, [256, 2559, 3652, 13448]),
(4, [256, 3652, 32152, 32256]),
(4, [258, 511, 3652, 32152]),
(4, [287, 482, 615, 3652]),
(4, [287, 482, 2628, 26896]),
(4, [287, 482, 3652, 27920]),
(4, [287, 482, 3652, 32152]),
(4, [287, 482, 3908, 32152]),
(4, [287, 482, 16076, 32152]),
(4, [287, 482, 26896, 30139]),
(4, [287, 482, 28500, 32152]),
(4, [287, 482, 29115, 32152]),
(4, [287, 482, 32152, 32732])
],
#[
(4, [287, 1506, 3652, 26896]),
(4, [287, 3652, 32152, 32285]),
(4, [320, 511, 3652, 32152]),
(4, [320, 511, 28500, 32152]),
(4, [324, 511, 13448, 26896]),
(4, [340, 482, 511, 32152]),
(4, [340, 511, 13471, 26896]),
(4, [340, 511, 13802, 26896]),
(4, [351, 482, 3652, 32152]),
(4, [351, 482, 28500, 32152]),
(4, [354, 511, 2628, 26896]),
(4, [354, 511, 3652, 32152]),
(4, [383, 482, 2628, 26896]),
(4, [383, 482, 3652, 32152]),
(4, [384, 511, 16076, 32152]),
(4, [384, 511, 28500, 32152])
],
#[
(4, [415, 482, 16076, 32152]),
(4, [415, 482, 28500, 32152]),
(4, [418, 511, 26896, 30139]),
(4, [443, 482, 13471, 26896]),
(4, [443, 482, 13823, 26896]),
(4, [443, 511, 13471, 26896]),
(4, [443, 511, 13802, 26896]),
(4, [447, 482, 26896, 30139]),
(4, [447, 3652, 13802, 26896]),
(4, [447, 13802, 26896, 29115]),
(4, [476, 482, 13448, 26896]),
(4, [476, 482, 13448, 32152]),
(4, [476, 482, 26896, 32152]),
(4, [480, 1055, 3652, 26896]),
(4, [480, 2628, 26896, 32736]),
(4, [480, 3652, 26896, 31712])
],
#[
(4, [480, 3652, 27920, 32736]),
(4, [480, 16076, 32152, 32736]),
(4, [480, 26896, 30139, 32736]),
(4, [480, 28500, 32152, 32736]),
(4, [482, 511, 580, 26896]),
(4, [482, 511, 615, 16076]),
(4, [482, 511, 615, 28500]),
(4, [482, 511, 2628, 5871]),
(4, [482, 511, 2628, 18704]),
(4, [482, 511, 2628, 26896]),
(4, [482, 511, 3652, 4847]),
(4, [482, 511, 3652, 27920]),
(4, [482, 511, 3652, 27924]),
(4, [482, 511, 3652, 27928]),
(4, [482, 511, 3652, 27984]),
(4, [482, 511, 3652, 27988])
],
#[
(4, [482, 511, 3652, 32016]),
(4, [482, 511, 3652, 32024]),
(4, [482, 511, 3780, 32152]),
(4, [482, 511, 3788, 32152]),
(4, [482, 511, 3908, 32152]),
(4, [482, 511, 3924, 32152]),
(4, [482, 511, 4267, 32152]),
(4, [482, 511, 5871, 30139]),
(4, [482, 511, 13483, 26896]),
(4, [482, 511, 13516, 26964]),
(4, [482, 511, 13516, 32152]),
(4, [482, 511, 13755, 26896]),
(4, [482, 511, 16691, 32152]),
(4, [482, 511, 19284, 26896]),
(4, [482, 511, 26896, 27476]),
(4, [482, 511, 26896, 30139])
],
#[
(4, [482, 511, 26896, 32187]),
(4, [482, 511, 26964, 32152]),
(4, [482, 511, 27920, 28500]),
(4, [482, 511, 27920, 29115]),
(4, [482, 511, 28500, 32250]),
(4, [482, 580, 26896, 32736]),
(4, [482, 615, 16076, 32736]),
(4, [482, 615, 28500, 32736]),
(4, [482, 639, 3652, 13471]),
(4, [482, 639, 3652, 26911]),
(4, [482, 1053, 3652, 26896]),
(4, [482, 1055, 1604, 5871]),
(4, [482, 1055, 1604, 26896]),
(4, [482, 1055, 2304, 3652]),
(4, [482, 1055, 3652, 4832]),
(4, [482, 1055, 3652, 4847])
],
#[
(4, [482, 1055, 3652, 5856]),
(4, [482, 1055, 3652, 5871]),
(4, [482, 1055, 3652, 5887]),
(4, [482, 1055, 3652, 14063]),
(4, [482, 1055, 3652, 18704]),
(4, [482, 1055, 3652, 26880]),
(4, [482, 1055, 3652, 26896]),
(4, [482, 1055, 3652, 26898]),
(4, [482, 1055, 3652, 26900]),
(4, [482, 1055, 3652, 26904]),
(4, [482, 1055, 3652, 26911]),
(4, [482, 1055, 3652, 26960]),
(4, [482, 1055, 3652, 27920]),
(4, [482, 1055, 3652, 27924]),
(4, [482, 1055, 3652, 27928]),
(4, [482, 1055, 3652, 27935])
],
#[
(4, [482, 1055, 3654, 26896]),
(4, [482, 1055, 3668, 26896]),
(4, [482, 1055, 3908, 26896]),
(4, [482, 1055, 4267, 26896]),
(4, [482, 1055, 5871, 28500]),
(4, [482, 1055, 5871, 29115]),
(4, [482, 1055, 11844, 26896]),
(4, [482, 1055, 26896, 28500]),
(4, [482, 1055, 26896, 29115]),
(4, [482, 1055, 26896, 31163]),
(4, [482, 1055, 26911, 29115]),
(4, [482, 1055, 27122, 28500]),
(4, [482, 1055, 27920, 29115]),
(4, [482, 1055, 27935, 29115]),
(4, [482, 1119, 3652, 5871]),
(4, [482, 1119, 3652, 26896])
],
#[
(4, [482, 1119, 3652, 26911]),
(4, [482, 1119, 3652, 27984]),
(4, [482, 1119, 3652, 27999]),
(4, [482, 1119, 26896, 28500]),
(4, [482, 1119, 26896, 29115]),
(4, [482, 1183, 2304, 3652]),
(4, [482, 1183, 3652, 5871]),
(4, [482, 1183, 3652, 26896]),
(4, [482, 1183, 3652, 26911]),
(4, [482, 1183, 3652, 28048]),
(4, [482, 1183, 3652, 28063]),
(4, [482, 1183, 3652, 32152]),
(4, [482, 1183, 3780, 26896]),
(4, [482, 1183, 26896, 28500]),
(4, [482, 1183, 26896, 29115]),
(4, [482, 1311, 3652, 26896])
],
#[
(4, [482, 1535, 3652, 5871]),
(4, [482, 1535, 3652, 26896]),
(4, [482, 1535, 3652, 27920]),
(4, [482, 1535, 26896, 28500]),
(4, [482, 1535, 26896, 29115]),
(4, [482, 2079, 2628, 26896]),
(4, [482, 2079, 3652, 27920]),
(4, [482, 2079, 3908, 13448]),
(4, [482, 2079, 26896, 30139]),
(4, [482, 2335, 3652, 13471]),
(4, [482, 2335, 3652, 15752]),
(4, [482, 2335, 3652, 32152]),
(4, [482, 2335, 3908, 13448]),
(4, [482, 2628, 2655, 26911]),
(4, [482, 2628, 3679, 26911]),
(4, [482, 2628, 5871, 32736])
],
#[
(4, [482, 2628, 18704, 32736]),
(4, [482, 2628, 26880, 32736]),
(4, [482, 2628, 26896, 32256]),
(4, [482, 2628, 26896, 32736]),
(4, [482, 2628, 26896, 32738]),
(4, [482, 2628, 26911, 32736]),
(4, [482, 2655, 3652, 26911]),
(4, [482, 3076, 3679, 26911]),
(4, [482, 3103, 3652, 5871]),
(4, [482, 3103, 3652, 26896]),
(4, [482, 3103, 3652, 26911]),
(4, [482, 3103, 3652, 27920]),
(4, [482, 3103, 3652, 27935]),
(4, [482, 3103, 3652, 28500]),
(4, [482, 3103, 26896, 29115]),
(4, [482, 3167, 3652, 26896])
],
#[
(4, [482, 3487, 3652, 26896]),
(4, [482, 3583, 3652, 26896]),
(4, [482, 3652, 3679, 27924]),
(4, [482, 3652, 3679, 27935]),
(4, [482, 3652, 4847, 32736]),
(4, [482, 3652, 5279, 5856]),
(4, [482, 3652, 5279, 26911]),
(4, [482, 3652, 5871, 31712]),
(4, [482, 3652, 13471, 18719]),
(4, [482, 3652, 13471, 32128]),
(4, [482, 3652, 18719, 19296]),
(4, [482, 3652, 26880, 31712]),
(4, [482, 3652, 26896, 29664]),
(4, [482, 3652, 26896, 31232]),
(4, [482, 3652, 26896, 31584]),
(4, [482, 3652, 26896, 31648])
]
],
#[
#[
(4, [482, 3652, 26896, 31712]),
(4, [482, 3652, 26896, 31714]),
(4, [482, 3652, 26911, 31712]),
(4, [482, 3652, 26911, 32128]),
(4, [482, 3652, 27904, 32736]),
(4, [482, 3652, 27920, 31712]),
(4, [482, 3652, 27920, 32256]),
(4, [482, 3652, 27920, 32736]),
(4, [482, 3652, 27920, 32738]),
(4, [482, 3652, 27924, 32736]),
(4, [482, 3652, 27928, 32736]),
(4, [482, 3652, 27935, 31712]),
(4, [482, 3652, 27935, 32736]),
(4, [482, 3652, 27984, 32736]),
(4, [482, 3652, 32016, 32256]),
(4, [482, 3652, 32024, 32736])
],
#[
(4, [482, 3652, 32152, 32480]),
(4, [482, 3652, 32152, 32608]),
(4, [482, 3679, 26911, 30139]),
(4, [482, 3780, 32152, 32736]),
(4, [482, 3908, 32152, 32736]),
(4, [482, 4267, 32152, 32736]),
(4, [482, 5871, 30139, 32736]),
(4, [482, 9247, 11844, 26896]),
(4, [482, 11844, 13471, 26911]),
(4, [482, 13448, 26911, 28484]),
(4, [482, 13471, 16068, 26896]),
(4, [482, 13471, 26896, 32324]),
(4, [482, 13483, 26896, 32736]),
(4, [482, 13823, 26896, 32324]),
(4, [482, 16068, 32144, 32736]),
(4, [482, 16068, 32152, 32736])
],
#[
(4, [482, 16076, 32136, 32736]),
(4, [482, 16076, 32152, 32256]),
(4, [482, 16076, 32152, 32738]),
(4, [482, 16691, 32152, 32736]),
(4, [482, 19284, 26896, 32736]),
(4, [482, 26880, 30139, 32736]),
(4, [482, 26896, 27476, 32736]),
(4, [482, 26896, 28500, 31712]),
(4, [482, 26896, 29115, 31712]),
(4, [482, 26896, 30139, 32256]),
(4, [482, 26896, 30139, 32736]),
(4, [482, 26896, 30139, 32738]),
(4, [482, 26896, 32187, 32736]),
(4, [482, 26911, 30139, 32736]),
(4, [482, 27920, 28500, 32736]),
(4, [482, 27920, 29115, 32736])
],
#[
(4, [482, 28484, 32136, 32736]),
(4, [482, 28484, 32152, 32736]),
(4, [482, 28500, 32144, 32736]),
(4, [482, 28500, 32152, 32256]),
(4, [482, 28500, 32152, 32738]),
(4, [482, 28500, 32250, 32736]),
(4, [486, 511, 13448, 26964]),
(4, [486, 1055, 3652, 26896]),
(4, [490, 1055, 3652, 26896]),
(4, [490, 13471, 16076, 26896]),
(4, [495, 3652, 5887, 13448]),
(4, [498, 1055, 3652, 26896]),
(4, [506, 3652, 13471, 32152]),
(4, [507, 3652, 13471, 26896]),
(4, [507, 13471, 26896, 29115]),
(4, [511, 608, 3652, 13471])
],
#[
(4, [511, 615, 3652, 13471]),
(4, [511, 639, 3652, 13448]),
(4, [511, 639, 3652, 26896]),
(4, [511, 999, 3652, 26896]),
(4, [511, 1024, 2304, 3652]),
(4, [511, 1024, 3652, 5887]),
(4, [511, 1024, 3652, 26880]),
(4, [511, 1024, 3668, 26896]),
(4, [511, 1024, 3908, 26896]),
(4, [511, 1040, 3652, 26896]),
(4, [511, 1055, 3652, 5871]),
(4, [511, 1055, 3652, 26896]),
(4, [511, 1055, 3652, 26911]),
(4, [511, 1055, 3652, 27920]),
(4, [511, 1055, 3652, 27935]),
(4, [511, 1055, 26896, 28500])
],
#[
(4, [511, 1055, 26896, 29115]),
(4, [511, 1092, 3679, 26896]),
(4, [511, 1092, 4070, 26896]),
(4, [511, 1092, 13471, 26896]),
(4, [511, 1092, 13802, 26896]),
(4, [511, 1119, 3652, 26896]),
(4, [511, 1152, 2304, 3652]),
(4, [511, 1183, 3652, 26896]),
(4, [511, 1280, 3652, 26896]),
(4, [511, 1506, 3652, 5871]),
(4, [511, 1506, 3652, 26896]),
(4, [511, 1506, 3652, 27920]),
(4, [511, 1506, 26896, 28500]),
(4, [511, 1506, 26896, 29115]),
(4, [511, 1510, 3652, 26896]),
(4, [511, 1514, 3652, 26896])
],
#[
(4, [511, 1604, 5871, 13471]),
(4, [511, 1604, 5871, 13802]),
(4, [511, 1604, 5887, 13448]),
(4, [511, 1604, 13471, 26896]),
(4, [511, 1604, 13802, 26896]),
(4, [511, 2048, 3908, 13448]),
(4, [511, 2116, 13471, 26896]),
(4, [511, 2116, 13802, 26896]),
(4, [511, 2304, 3652, 13448]),
(4, [511, 2304, 3652, 13471]),
(4, [511, 2304, 3652, 13802]),
(4, [511, 2304, 3652, 13823]),
(4, [511, 2304, 3652, 15752]),
(4, [511, 2304, 3652, 19319]),
(4, [511, 2304, 3652, 32152]),
(4, [511, 2304, 3908, 13448])
],
#[
(4, [511, 2304, 13448, 16076]),
(4, [511, 2304, 13448, 29115]),
(4, [511, 2320, 3652, 13471]),
(4, [511, 2320, 3652, 13802]),
(4, [511, 2628, 2655, 26896]),
(4, [511, 2628, 3046, 26896]),
(4, [511, 2628, 3679, 26896]),
(4, [511, 2628, 4070, 26896]),
(4, [511, 2628, 13471, 26896]),
(4, [511, 2628, 13802, 26896]),
(4, [511, 2628, 26896, 32285]),
(4, [511, 2628, 26896, 32736]),
(4, [511, 2647, 3652, 26896]),
(4, [511, 2655, 3652, 26896]),
(4, [511, 2918, 3652, 26896]),
(4, [511, 3046, 3652, 26896])
],
#[
(4, [511, 3096, 3652, 26896]),
(4, [511, 3103, 3652, 26896]),
(4, [511, 3456, 3652, 13448]),
(4, [511, 3456, 3652, 26896]),
(4, [511, 3554, 3652, 26896]),
(4, [511, 3652, 3679, 27920]),
(4, [511, 3652, 3679, 27928]),
(4, [511, 3652, 3908, 32152]),
(4, [511, 3652, 4070, 27920]),
(4, [511, 3652, 5256, 5887]),
(4, [511, 3652, 5279, 5871]),
(4, [511, 3652, 5279, 26896]),
(4, [511, 3652, 5610, 5871]),
(4, [511, 3652, 5610, 26896]),
(4, [511, 3652, 5856, 13471]),
(4, [511, 3652, 5871, 13464])
],
#[
(4, [511, 3652, 5871, 13704]),
(4, [511, 3652, 5871, 18965]),
(4, [511, 3652, 5871, 19296]),
(4, [511, 3652, 5887, 13448]),
(4, [511, 3652, 5887, 13471]),
(4, [511, 3652, 5887, 13802]),
(4, [511, 3652, 5887, 13823]),
(4, [511, 3652, 5887, 19319]),
(4, [511, 3652, 5887, 32152]),
(4, [511, 3652, 8448, 32152]),
(4, [511, 3652, 8448, 32250]),
(4, [511, 3652, 9236, 26896]),
(4, [511, 3652, 9247, 26896]),
(4, [511, 3652, 9536, 26896]),
(4, [511, 3652, 9698, 26896]),
(4, [511, 3652, 10496, 13448])
],
#[
(4, [511, 3652, 10496, 13802]),
(4, [511, 3652, 13341, 26896]),
(4, [511, 3652, 13343, 26896]),
(4, [511, 3652, 13440, 26880]),
(4, [511, 3652, 13448, 14079]),
(4, [511, 3652, 13448, 15752]),
(4, [511, 3652, 13448, 18688]),
(4, [511, 3652, 13448, 26880]),
(4, [511, 3652, 13448, 30463]),
(4, [511, 3652, 13448, 32128]),
(4, [511, 3652, 13448, 32136]),
(4, [511, 3652, 13464, 26896]),
(4, [511, 3652, 13464, 32152]),
(4, [511, 3652, 13466, 26896]),
(4, [511, 3652, 13467, 26896]),
(4, [511, 3652, 13468, 26896])
],
#[
(4, [511, 3652, 13469, 26896]),
(4, [511, 3652, 13471, 14063]),
(4, [511, 3652, 13471, 14079]),
(4, [511, 3652, 13471, 18688]),
(4, [511, 3652, 13471, 18704]),
(4, [511, 3652, 13471, 26880]),
(4, [511, 3652, 13471, 26896]),
(4, [511, 3652, 13471, 26898]),
(4, [511, 3652, 13471, 26900]),
(4, [511, 3652, 13471, 26904]),
(4, [511, 3652, 13471, 26960]),
(4, [511, 3652, 13471, 26964]),
(4, [511, 3652, 13471, 27024]),
(4, [511, 3652, 13471, 27026]),
(4, [511, 3652, 13471, 27032]),
(4, [511, 3652, 13471, 27039])
],
#[
(4, [511, 3652, 13471, 27920]),
(4, [511, 3652, 13471, 27924]),
(4, [511, 3652, 13471, 32159]),
(4, [511, 3652, 13535, 26896]),
(4, [511, 3652, 13704, 26896]),
(4, [511, 3652, 13706, 26896]),
(4, [511, 3652, 13738, 26896]),
(4, [511, 3652, 13768, 26896]),
(4, [511, 3652, 13792, 26896]),
(4, [511, 3652, 13794, 26896]),
(4, [511, 3652, 13800, 26896]),
(4, [511, 3652, 13802, 14063]),
(4, [511, 3652, 13802, 18704]),
(4, [511, 3652, 13802, 26880]),
(4, [511, 3652, 13802, 26896]),
(4, [511, 3652, 13802, 26900])
],
#[
(4, [511, 3652, 13802, 26960]),
(4, [511, 3652, 13802, 26964]),
(4, [511, 3652, 13802, 27920]),
(4, [511, 3652, 13802, 27984]),
(4, [511, 3652, 13806, 26896]),
(4, [511, 3652, 13823, 26880]),
(4, [511, 3652, 15512, 26896]),
(4, [511, 3652, 15519, 26896]),
(4, [511, 3652, 15752, 26896]),
(4, [511, 3652, 15850, 26896]),
(4, [511, 3652, 16095, 32152]),
(4, [511, 3652, 16095, 32159]),
(4, [511, 3652, 18688, 19296]),
(4, [511, 3652, 18965, 26896]),
(4, [511, 3652, 18975, 26896]),
(4, [511, 3652, 19063, 26896])
],
#[
(4, [511, 3652, 19296, 26896]),
(4, [511, 3652, 19296, 26911]),
(4, [511, 3652, 19296, 32152]),
(4, [511, 3652, 19296, 32159]),
(4, [511, 3652, 19303, 26896]),
(4, [511, 3652, 19319, 26880]),
(4, [511, 3652, 19426, 26896]),
(4, [511, 3652, 26880, 32136]),
(4, [511, 3652, 26880, 32152]),
(4, [511, 3652, 26896, 29849]),
(4, [511, 3652, 26896, 30120]),
(4, [511, 3652, 26896, 31261]),
(4, [511, 3652, 26896, 31712]),
(4, [511, 3652, 26896, 31768]),
(4, [511, 3652, 26896, 31896]),
(4, [511, 3652, 26896, 32128])
],
#[
(4, [511, 3652, 26896, 32136]),
(4, [511, 3652, 27920, 32285]),
(4, [511, 3652, 27920, 32736]),
(4, [511, 3652, 32024, 32285]),
(4, [511, 3652, 32152, 32413]),
(4, [511, 3652, 32152, 32511]),
(4, [511, 3668, 5871, 13448]),
(4, [511, 3668, 13448, 26896]),
(4, [511, 3668, 13448, 32152]),
(4, [511, 3668, 13464, 26896]),
(4, [511, 3668, 13471, 26896]),
(4, [511, 3668, 13802, 26896]),
(4, [511, 3668, 13823, 26896]),
(4, [511, 3668, 19319, 26896]),
(4, [511, 3668, 26896, 32152]),
(4, [511, 3676, 13448, 26896])
]
],
#[
#[
(4, [511, 3676, 13448, 32152]),
(4, [511, 3676, 26896, 32152]),
(4, [511, 3679, 16076, 32152]),
(4, [511, 3679, 26896, 30139]),
(4, [511, 3679, 28500, 32152]),
(4, [511, 3908, 5871, 13448]),
(4, [511, 3908, 13448, 26896]),
(4, [511, 3908, 13448, 26911]),
(4, [511, 3908, 13448, 27122]),
(4, [511, 3908, 13448, 27135]),
(4, [511, 3908, 13448, 32152]),
(4, [511, 3908, 13471, 26896]),
(4, [511, 3908, 13704, 26896]),
(4, [511, 3908, 13802, 26896]),
(4, [511, 3908, 13823, 26896]),
(4, [511, 3908, 19319, 26896])
],
#[
(4, [511, 3908, 26896, 32152]),
(4, [511, 3908, 32152]),
(4, [511, 3908, 32152, 32767]),
(4, [511, 3924, 13471, 26896]),
(4, [511, 3924, 13802, 26896]),
(4, [511, 4036, 13448, 26896]),
(4, [511, 4036, 13448, 32152]),
(4, [511, 4036, 26896, 32152]),
(4, [511, 4070, 13448, 26964]),
(4, [511, 4070, 16076, 32152]),
(4, [511, 4070, 26896, 30139]),
(4, [511, 4070, 28500, 32152]),
(4, [511, 4267, 13471, 26896]),
(4, [511, 4267, 13802, 26896]),
(4, [511, 5871, 13471, 28500]),
(4, [511, 5871, 13471, 29115])
],
#[
(4, [511, 5871, 13802, 28500]),
(4, [511, 5871, 13802, 29115]),
(4, [511, 5887, 13448, 16076]),
(4, [511, 5887, 13448, 29115]),
(4, [511, 6127, 13448, 28500]),
(4, [511, 9236, 26896, 28500]),
(4, [511, 9247, 26896, 28500]),
(4, [511, 9536, 26896, 28500]),
(4, [511, 9698, 26896, 28500]),
(4, [511, 10496, 13448, 16076]),
(4, [511, 11844, 13471, 26896]),
(4, [511, 11844, 13802, 26896]),
(4, [511, 11860, 13448, 26896]),
(4, [511, 11860, 13471, 26896]),
(4, [511, 12100, 13448, 26896]),
(4, [511, 12100, 13802, 26896])
],
#[
(4, [511, 13448, 16076, 26880]),
(4, [511, 13448, 16092, 26896]),
(4, [511, 13448, 16332, 26896]),
(4, [511, 13448, 26640, 28500]),
(4, [511, 13448, 26880, 28484]),
(4, [511, 13448, 26880, 29115]),
(4, [511, 13448, 26896, 28244]),
(4, [511, 13448, 26896, 28484]),
(4, [511, 13448, 26896, 28859]),
(4, [511, 13448, 26896, 29099]),
(4, [511, 13464, 16076, 26896]),
(4, [511, 13464, 16092, 26896]),
(4, [511, 13464, 26896, 28500]),
(4, [511, 13464, 26896, 29115]),
(4, [511, 13467, 26896, 29115]),
(4, [511, 13468, 26896, 28500])
],
#[
(4, [511, 13471, 16076, 32152]),
(4, [511, 13471, 26896, 26964]),
(4, [511, 13471, 26896, 30139]),
(4, [511, 13471, 26896, 31163]),
(4, [511, 13471, 26896, 32324]),
(4, [511, 13471, 26896, 32699]),
(4, [511, 13471, 26911, 29115]),
(4, [511, 13471, 27122, 28500]),
(4, [511, 13471, 28500, 32152]),
(4, [511, 13471, 29115, 32152]),
(4, [511, 13471, 29115, 32159]),
(4, [511, 13471, 32152, 32732]),
(4, [511, 13704, 16076, 26896]),
(4, [511, 13704, 16332, 26896]),
(4, [511, 13704, 26896, 28500]),
(4, [511, 13704, 26896, 29115])
],
#[
(4, [511, 13738, 26896, 29115]),
(4, [511, 13768, 26896, 28500]),
(4, [511, 13802, 16076, 32152]),
(4, [511, 13802, 26896, 26964]),
(4, [511, 13802, 26896, 30139]),
(4, [511, 13802, 26896, 31163]),
(4, [511, 13802, 26896, 32324]),
(4, [511, 13802, 26896, 32699]),
(4, [511, 13802, 27122, 28500]),
(4, [511, 13802, 28500, 32152]),
(4, [511, 13802, 28500, 32250]),
(4, [511, 16076, 16095, 32152]),
(4, [511, 16076, 16366, 32152]),
(4, [511, 16076, 32152, 32285]),
(4, [511, 16076, 32152, 32736]),
(4, [511, 18965, 26896, 28500])
],
#[
(4, [511, 18965, 26896, 29115]),
(4, [511, 19296, 26896, 28500]),
(4, [511, 19296, 26896, 29115]),
(4, [511, 26896, 30139, 32285]),
(4, [511, 26896, 30139, 32736]),
(4, [511, 28500, 32152, 32285]),
(4, [511, 28500, 32152, 32736]),
(4, [1024, 1055, 27122, 28500]),
(4, [1024, 27122, 28500, 32736]),
(4, [1053, 3652, 26896, 32285]),
(4, [1055, 1506, 3652, 5871]),
(4, [1055, 1506, 3652, 26896]),
(4, [1055, 1506, 3652, 26911]),
(4, [1055, 1506, 3652, 27920]),
(4, [1055, 1506, 3652, 27935]),
(4, [1055, 1506, 26896, 28500])
],
#[
(4, [1055, 1506, 26896, 29115]),
(4, [1055, 1510, 3652, 26896]),
(4, [1055, 1514, 3652, 26896]),
(4, [1055, 1535, 3652, 5871]),
(4, [1055, 1535, 3652, 26896]),
(4, [1055, 1535, 3652, 26911]),
(4, [1055, 1535, 3652, 27920]),
(4, [1055, 1535, 3652, 27935]),
(4, [1055, 1535, 26896, 28500]),
(4, [1055, 1535, 26896, 29115]),
(4, [1055, 2530, 3652, 26896]),
(4, [1055, 3652, 5645, 26896]),
(4, [1055, 3652, 5871, 27122]),
(4, [1055, 3652, 5871, 32285]),
(4, [1055, 3652, 8674, 26896]),
(4, [1055, 3652, 26896, 27122])
],
#[
(4, [1055, 3652, 26896, 27135]),
(4, [1055, 3652, 26896, 28146]),
(4, [1055, 3652, 26896, 28159]),
(4, [1055, 3652, 26896, 31232]),
(4, [1055, 3652, 26896, 31261]),
(4, [1055, 3652, 26896, 32256]),
(4, [1055, 3652, 26896, 32285]),
(4, [1055, 3652, 26896, 32287]),
(4, [1055, 3652, 26896, 32541]),
(4, [1055, 3652, 26911, 27122]),
(4, [1055, 3652, 26911, 27135]),
(4, [1055, 3652, 26911, 32285]),
(4, [1055, 3652, 27122, 27920]),
(4, [1055, 3652, 27122, 27935]),
(4, [1055, 3652, 27122, 28500]),
(4, [1055, 3652, 27920, 28146])
],
#[
(4, [1055, 3652, 27920, 32285]),
(4, [1055, 3652, 27935, 28159]),
(4, [1055, 3652, 27935, 32285]),
(4, [1055, 13448, 27122, 28500]),
(4, [1055, 26896, 27122, 28500]),
(4, [1055, 26896, 27122, 29115]),
(4, [1055, 26896, 28500, 32285]),
(4, [1055, 26896, 29115, 32285]),
(4, [1055, 27122, 28500]),
(4, [1055, 27122, 28500, 32767]),
(4, [1119, 1506, 3652, 26896]),
(4, [1119, 1535, 3652, 26896]),
(4, [1119, 3652, 4070, 26896]),
(4, [1119, 3652, 26896, 27122]),
(4, [1119, 3652, 26896, 32285]),
(4, [1183, 1506, 3652, 26896])
],
#[
(4, [1183, 1535, 3652, 26896]),
(4, [1183, 3652, 26896, 27122]),
(4, [1183, 3652, 26896, 32285]),
(4, [1504, 3652, 26896, 32736]),
(4, [1506, 1535, 3652, 5871]),
(4, [1506, 1535, 3652, 26896]),
(4, [1506, 1535, 3652, 27920]),
(4, [1506, 1535, 26896, 28500]),
(4, [1506, 1535, 26896, 29115]),
(4, [1506, 2079, 3652, 26896]),
(4, [1506, 3652, 3679, 26911]),
(4, [1506, 3652, 5871, 32736]),
(4, [1506, 3652, 26880, 32736]),
(4, [1506, 3652, 26896, 31232]),
(4, [1506, 3652, 26896, 31712]),
(4, [1506, 3652, 26896, 32256])
],
#[
(4, [1506, 3652, 26896, 32736]),
(4, [1506, 3652, 26896, 32738]),
(4, [1506, 3652, 26911, 32736]),
(4, [1506, 3652, 27920, 32736]),
(4, [1506, 26896, 28500, 32736]),
(4, [1506, 26896, 29115, 32736]),
(4, [1510, 1535, 3652, 26896]),
(4, [1510, 3652, 3679, 26896]),
(4, [1510, 3652, 26896, 32736]),
(4, [1514, 1535, 3652, 26896]),
(4, [1514, 3652, 3679, 26911]),
(4, [1514, 3652, 26896, 32736]),
(4, [1535, 3652, 3679, 26896]),
(4, [1535, 3652, 4070, 26896]),
(4, [1535, 3652, 13471, 26896]),
(4, [1535, 3652, 13802, 26896])
],
#[
(4, [1535, 3652, 26896, 31261]),
(4, [1535, 3652, 26896, 31712]),
(4, [1535, 3652, 26896, 32285]),
(4, [1535, 3652, 26896, 32736]),
(4, [2079, 3652, 13448, 32541]),
(4, [2304, 2559, 3652, 13448]),
(4, [2304, 3652, 13448, 32256]),
(4, [2559, 3652, 13471, 26896]),
(4, [2559, 3652, 13802, 26896]),
(4, [2559, 3652, 15519, 26896]),
(4, [2559, 3652, 15850, 26896]),
(4, [2628, 26896, 27122, 32736]),
(4, [2628, 26896, 32285, 32736]),
(4, [3103, 3554, 3652, 26896]),
(4, [3103, 3583, 3652, 26896]),
(4, [3103, 3652, 26896, 27122])
],
#[
(4, [3103, 3652, 26896, 32285]),
(4, [3167, 3652, 26896, 27122]),
(4, [3554, 3583, 3652, 26896]),
(4, [3554, 3652, 26896, 32736]),
(4, [3652, 5663, 13448, 26911]),
(4, [3652, 5871, 13448, 32512]),
(4, [3652, 5871, 13471, 32256]),
(4, [3652, 5871, 13802, 32256]),
(4, [3652, 5887, 13448, 27135]),
(4, [3652, 5887, 13448, 32256]),
(4, [3652, 8703, 13802, 26896]),
(4, [3652, 9247, 9698, 26896]),
(4, [3652, 9698, 9727, 26896]),
(4, [3652, 9698, 26896, 32736]),
(4, [3652, 10463, 13448, 26896]),
(4, [3652, 13343, 26896, 32256])
],
#[
(4, [3652, 13448, 26880, 27135]),
(4, [3652, 13448, 26880, 32256]),
(4, [3652, 13448, 26896, 32512]),
(4, [3652, 13448, 26896, 32544]),
(4, [3652, 13448, 26911, 27104]),
(4, [3652, 13464, 26896, 32256]),
(4, [3652, 13471, 26896, 32256]),
(4, [3652, 13471, 26911, 32256]),
(4, [3652, 13471, 32152, 32256]),
(4, [3652, 13471, 32159, 32256]),
(4, [3652, 13704, 26896, 32256]),
(4, [3652, 13794, 26896, 32256]),
(4, [3652, 13802, 26896, 32256]),
(4, [3652, 18965, 26896, 32256]),
(4, [3652, 19296, 26896, 32256]),
(4, [3652, 26896, 27122, 31712])
],
#[
(4, [3652, 26896, 28146, 32736]),
(4, [3652, 26896, 31261, 32736]),
(4, [3652, 26896, 31712, 32285]),
(4, [3652, 27122, 27920, 32736]),
(4, [3652, 27920, 28146, 32736]),
(4, [3652, 27920, 32285, 32736]),
(4, [3652, 32024, 32285, 32736]),
(4, [3652, 32152, 32541, 32736]),
(4, [3668, 13448, 26896, 32256]),
(4, [3679, 4070, 13802, 26911]),
(4, [3679, 13471, 27122, 28500]),
(4, [3908, 13448, 26896, 32256]),
(4, [4267, 13448, 27122, 32736]),
(4, [5645, 13448, 28500, 32736]),
(4, [8223, 13448, 27122, 28500]),
(4, [8351, 13448, 27122, 28500])
]
],
#[
#[
(4, [9216, 9247, 27122, 28500]),
(4, [9216, 27122, 28500, 32736]),
(4, [9247, 9698, 26896, 28500]),
(4, [9247, 13448, 27122, 28500]),
(4, [9698, 9727, 26896, 28500]),
(4, [9698, 26896, 28500, 32736]),
(4, [10463, 13448, 16076, 26896]),
(4, [13440, 27122, 28500, 32736]),
(4, [13448, 16076, 26896, 32544]),
(4, [13448, 27106, 28484, 32736]),
(4, [13448, 27120, 28500, 32736]),
(4, [13448, 27122, 28484, 32736]),
(4, [13448, 27122, 28500, 32738]),
(4, [13471, 26896, 28500, 32256]),
(4, [13471, 26896, 29115, 32256]),
(4, [13471, 26896, 32256, 32324])
],
#[
(4, [13471, 27122, 28500, 32736]),
(4, [13802, 26896, 28500, 32256]),
(4, [13802, 26896, 29115, 32256]),
(4, [13802, 26896, 32256, 32324]),
(4, [13802, 27122, 28500, 32736]),
(4, [16076, 32152, 32285, 32736]),
(4, [19319, 27122, 28500, 32736]),
(4, [26896, 27122, 30139, 32736]),
(4, [26896, 30139, 32285, 32736]),
(4, [27122, 28500, 32152, 32736]),
(4, [27122, 28500, 32250, 32736]),
(4, [28500, 32152, 32285, 32736]),
(5, [0, 31, 192, 3652, 32152]),
(5, [0, 31, 192, 16076, 32152]),
(5, [0, 31, 204, 13448, 26896]),
(5, [0, 31, 226, 1604, 13448])
],
#[
(5, [0, 31, 226, 3652, 32152]),
(5, [0, 31, 482, 580, 26896]),
(5, [0, 31, 482, 615, 16076]),
(5, [0, 31, 482, 615, 28500]),
(5, [0, 31, 482, 2628, 5871]),
(5, [0, 31, 482, 2628, 18704]),
(5, [0, 31, 482, 2628, 26896]),
(5, [0, 31, 482, 2628, 26911]),
(5, [0, 31, 482, 3652, 4847]),
(5, [0, 31, 482, 3652, 27920]),
(5, [0, 31, 482, 3652, 27924]),
(5, [0, 31, 482, 3652, 27928]),
(5, [0, 31, 482, 3652, 27935]),
(5, [0, 31, 482, 3652, 27984]),
(5, [0, 31, 482, 3652, 32024]),
(5, [0, 31, 482, 3780, 32152])
],
#[
(5, [0, 31, 482, 3908, 32152]),
(5, [0, 31, 482, 4267, 32152]),
(5, [0, 31, 482, 5871, 30139]),
(5, [0, 31, 482, 13483, 26896]),
(5, [0, 31, 482, 16076, 32152]),
(5, [0, 31, 482, 16691, 32152]),
(5, [0, 31, 482, 19284, 26896]),
(5, [0, 31, 482, 26896, 27476]),
(5, [0, 31, 482, 26896, 30139]),
(5, [0, 31, 482, 26896, 32187]),
(5, [0, 31, 482, 26911, 30139]),
(5, [0, 31, 482, 27920, 28500]),
(5, [0, 31, 482, 27920, 29115]),
(5, [0, 31, 482, 28500, 32152]),
(5, [0, 31, 482, 28500, 32250]),
(5, [0, 31, 511, 2628, 26896])
],
#[
(5, [0, 31, 511, 3652, 27920]),
(5, [0, 31, 511, 16076, 32152]),
(5, [0, 31, 511, 26896, 30139]),
(5, [0, 31, 511, 28500, 32152]),
(5, [0, 31, 1024, 27122, 28500]),
(5, [0, 31, 1506, 3652, 5871]),
(5, [0, 31, 1506, 3652, 26896]),
(5, [0, 31, 1506, 3652, 26911]),
(5, [0, 31, 1506, 3652, 27920]),
(5, [0, 31, 1506, 26896, 28500]),
(5, [0, 31, 1506, 26896, 29115]),
(5, [0, 31, 1510, 3652, 26896]),
(5, [0, 31, 1514, 3652, 26896]),
(5, [0, 31, 1535, 3652, 26896]),
(5, [0, 31, 2628, 26896, 27122]),
(5, [0, 31, 2628, 26896, 32285])
],
#[
(5, [0, 31, 3554, 3652, 26896]),
(5, [0, 31, 3652, 9698, 26896]),
(5, [0, 31, 3652, 26896, 28146]),
(5, [0, 31, 3652, 26896, 31261]),
(5, [0, 31, 3652, 27122, 27920]),
(5, [0, 31, 3652, 27920, 28146]),
(5, [0, 31, 3652, 27920, 32285]),
(5, [0, 31, 3652, 32024, 32285]),
(5, [0, 31, 3652, 32152, 32541]),
(5, [0, 31, 4267, 13448, 27122]),
(5, [0, 31, 5645, 13448, 28500]),
(5, [0, 31, 9216, 27122, 28500]),
(5, [0, 31, 9698, 26896, 28500]),
(5, [0, 31, 13448, 27122, 28500]),
(5, [0, 31, 13471, 27122, 28500]),
(5, [0, 31, 13802, 27122, 28500])
],
#[
(5, [0, 31, 16076, 32152, 32285]),
(5, [0, 31, 19319, 27122, 28500]),
(5, [0, 31, 26896, 27122, 30139]),
(5, [0, 31, 26896, 30139, 32285]),
(5, [0, 31, 27122, 28500, 32152]),
(5, [0, 31, 27122, 28500, 32250]),
(5, [0, 31, 28500, 32152, 32285]),
(5, [0, 68, 511, 13471, 26896]),
(5, [0, 68, 511, 13802, 26896]),
(5, [0, 159, 482, 3652, 32152]),
(5, [0, 223, 3652, 13448, 26896]),
(5, [0, 223, 13448, 16076, 26896]),
(5, [0, 255, 3652, 5871, 13448]),
(5, [0, 255, 3652, 13448, 26896]),
(5, [0, 256, 511, 3652, 32152]),
(5, [0, 287, 482, 3652, 32152])
],
#[
(5, [0, 482, 511, 2628, 26896]),
(5, [0, 482, 511, 3652, 27920]),
(5, [0, 482, 511, 16076, 32152]),
(5, [0, 482, 511, 26896, 30139]),
(5, [0, 482, 511, 28500, 32152]),
(5, [0, 482, 1055, 3652, 5871]),
(5, [0, 482, 1055, 3652, 26896]),
(5, [0, 482, 1055, 3652, 26911]),
(5, [0, 482, 1055, 3652, 27920]),
(5, [0, 482, 1055, 3652, 27935]),
(5, [0, 482, 1055, 26896, 28500]),
(5, [0, 482, 1055, 26896, 29115]),
(5, [0, 482, 1119, 3652, 26896]),
(5, [0, 482, 1183, 3652, 26896]),
(5, [0, 482, 1535, 3652, 26896]),
(5, [0, 482, 2628, 26896, 32736])
],
#[
(5, [0, 482, 3103, 3652, 26896]),
(5, [0, 482, 3652, 26896, 31712]),
(5, [0, 482, 3652, 27920, 32736]),
(5, [0, 482, 16076, 32152, 32736]),
(5, [0, 482, 26896, 30139, 32736]),
(5, [0, 482, 28500, 32152, 32736]),
(5, [0, 511, 1055, 3652, 26896]),
(5, [0, 511, 1506, 3652, 26896]),
(5, [0, 511, 2304, 3652, 13448]),
(5, [0, 511, 3652, 5871, 13471]),
(5, [0, 511, 3652, 5871, 13802]),
(5, [0, 511, 3652, 5887, 13448]),
(5, [0, 511, 3652, 13448, 26880]),
(5, [0, 511, 3652, 13464, 26896]),
(5, [0, 511, 3652, 13471, 26896]),
(5, [0, 511, 3652, 13471, 26911])
],
#[
(5, [0, 511, 3652, 13471, 32152]),
(5, [0, 511, 3652, 13471, 32159]),
(5, [0, 511, 3652, 13704, 26896]),
(5, [0, 511, 3652, 13802, 26896]),
(5, [0, 511, 3652, 18965, 26896]),
(5, [0, 511, 3652, 19296, 26896]),
(5, [0, 511, 3668, 13448, 26896]),
(5, [0, 511, 3908, 13448, 26896]),
(5, [0, 511, 13471, 26896, 28500]),
(5, [0, 511, 13471, 26896, 29115]),
(5, [0, 511, 13802, 26896, 28500]),
(5, [0, 511, 13802, 26896, 29115]),
(5, [0, 1055, 1506, 3652, 26896]),
(5, [0, 1055, 1535, 3652, 26896]),
(5, [0, 1055, 3652, 26896, 27122]),
(5, [0, 1055, 3652, 26896, 32285])
],
#[
(5, [0, 1506, 1535, 3652, 26896]),
(5, [0, 1506, 3652, 26896, 32736]),
(5, [0, 3652, 13471, 26896, 32256]),
(5, [0, 3652, 13802, 26896, 32256]),
(5, [0, 13448, 27122, 28500, 32736]),
(5, [2, 31, 482, 2628, 26896]),
(5, [2, 31, 482, 3652, 27920]),
(5, [2, 31, 482, 16076, 32152]),
(5, [2, 31, 482, 26896, 30139]),
(5, [2, 31, 482, 28500, 32152]),
(5, [2, 31, 1506, 3652, 26896]),
(5, [2, 31, 13448, 27122, 28500]),
(5, [2, 482, 1055, 3652, 26896]),
(5, [2, 511, 3652, 13471, 26896]),
(5, [2, 511, 3652, 13802, 26896]),
(5, [4, 31, 192, 13448, 26896])
],
#[
(5, [4, 31, 482, 2628, 26896]),
(5, [4, 31, 482, 3652, 27920]),
(5, [4, 31, 482, 13448, 26960]),
(5, [4, 31, 482, 16076, 32152]),
(5, [4, 31, 482, 26896, 30139]),
(5, [4, 31, 482, 28500, 32152]),
(5, [4, 31, 1506, 3652, 26896]),
(5, [4, 31, 13448, 27122, 28500]),
(5, [4, 482, 1055, 3652, 26896]),
(5, [4, 511, 3652, 13471, 26896]),
(5, [4, 511, 3652, 13802, 26896]),
(5, [8, 31, 482, 2628, 26896]),
(5, [8, 31, 482, 3652, 27920]),
(5, [8, 31, 482, 16076, 32152]),
(5, [8, 31, 482, 26896, 30139]),
(5, [8, 31, 482, 28500, 32152])
],
#[
(5, [8, 31, 1506, 3652, 26896]),
(5, [8, 31, 13448, 27122, 28500]),
(5, [8, 482, 1055, 3652, 26896]),
(5, [8, 482, 13471, 16076, 26896]),
(5, [8, 511, 3652, 13471, 26896]),
(5, [8, 511, 3652, 13802, 26896]),
(5, [10, 511, 3652, 13802, 26896]),
(5, [12, 31, 192, 13448, 26896]),
(5, [12, 31, 482, 16076, 32152]),
(5, [15, 482, 3652, 5887, 13448]),
(5, [16, 31, 482, 2628, 26896]),
(5, [16, 31, 482, 3652, 27920]),
(5, [16, 31, 482, 16076, 32152]),
(5, [16, 31, 482, 26896, 30139]),
(5, [16, 31, 482, 28500, 32152]),
(5, [16, 31, 1506, 3652, 26896])
],
#[
(5, [16, 31, 13448, 27122, 28500]),
(5, [16, 68, 511, 13448, 26896]),
(5, [16, 482, 1055, 3652, 26896]),
(5, [16, 482, 13448, 26911, 28500]),
(5, [16, 511, 1024, 3652, 26896]),
(5, [16, 511, 3652, 5871, 13448]),
(5, [16, 511, 3652, 13448, 26896]),
(5, [16, 511, 3652, 13448, 32152]),
(5, [16, 511, 3652, 13464, 26896]),
(5, [16, 511, 3652, 13471, 26896]),
(5, [16, 511, 3652, 13802, 26896]),
(5, [16, 511, 3652, 13823, 26896]),
(5, [16, 511, 3652, 19319, 26896]),
(5, [16, 511, 3652, 26896, 32152]),
(5, [16, 511, 3668, 13448, 26896]),
(5, [16, 511, 13448, 16076, 26896])
],
#[
(5, [16, 511, 13448, 26896, 28500]),
(5, [16, 511, 13448, 26896, 29115]),
(5, [16, 3652, 13448, 26896, 27135]),
(5, [16, 3652, 13448, 26896, 32256]),
(5, [18, 31, 13448, 27122, 28500]),
(5, [18, 511, 3652, 13448, 26896]),
(5, [18, 3652, 13448, 26896, 27135]),
(5, [18, 3652, 13448, 26911, 27122]),
(5, [20, 31, 482, 28500, 32152]),
(5, [20, 31, 13448, 27122, 28500]),
(5, [20, 511, 3652, 13448, 26896]),
(5, [20, 511, 13448, 26896, 28500]),
(5, [23, 31, 482, 2628, 26896]),
(5, [23, 482, 3652, 19327, 26896]),
(5, [23, 511, 3652, 13448, 26896]),
(5, [23, 511, 3652, 19319, 26896])
],
#[
(5, [24, 31, 482, 16076, 32152]),
(5, [24, 31, 482, 28500, 32152]),
(5, [24, 482, 3652, 13471, 32152]),
(5, [24, 482, 3652, 26911, 32152]),
(5, [24, 511, 3652, 13448, 26896]),
(5, [24, 511, 3652, 13448, 32152]),
(5, [24, 511, 3652, 26896, 32152]),
(5, [27, 31, 482, 26896, 30139]),
(5, [27, 482, 3652, 13448, 26911]),
(5, [27, 482, 3652, 13471, 26896]),
(5, [27, 482, 13448, 26896, 29119]),
(5, [27, 482, 13448, 26911, 29115]),
(5, [27, 482, 13471, 26896, 29115]),
(5, [27, 511, 3652, 13448, 26896]),
(5, [27, 511, 13448, 26896, 29115]),
(5, [28, 482, 3652, 13448, 26896])
]
],
#[
#[
(5, [28, 482, 3652, 13448, 32152]),
(5, [28, 482, 3652, 26896, 32152]),
(5, [28, 482, 13448, 16076, 26896]),
(5, [28, 482, 13448, 26896, 28500]),
(5, [28, 482, 13448, 26896, 32732]),
(5, [28, 482, 13448, 32152, 32732]),
(5, [28, 482, 26896, 32152, 32732]),
(5, [29, 482, 1024, 3652, 26896]),
(5, [29, 482, 3652, 5871, 13448]),
(5, [29, 482, 3652, 13320, 26896]),
(5, [29, 482, 3652, 13448, 26896]),
(5, [29, 482, 3652, 13448, 26909]),
(5, [29, 482, 3652, 13448, 32152]),
(5, [29, 482, 3652, 13469, 26896]),
(5, [29, 482, 3652, 13471, 26896]),
(5, [29, 482, 3652, 13802, 26896])
],
#[
(5, [29, 482, 3652, 19319, 26896]),
(5, [29, 482, 3652, 26896, 32152]),
(5, [29, 482, 13448, 16076, 26896]),
(5, [29, 482, 13448, 26896, 28500]),
(5, [29, 482, 13448, 26896, 29115]),
(5, [29, 511, 3652, 13448, 26896]),
(5, [29, 1024, 3652, 26896, 32285]),
(5, [29, 3652, 5871, 13448, 32285]),
(5, [29, 3652, 13320, 26896, 32285]),
(5, [29, 3652, 13448, 26896, 27122]),
(5, [29, 3652, 13448, 26896, 32285]),
(5, [29, 3652, 13448, 26896, 32287]),
(5, [29, 3652, 13448, 26896, 32541]),
(5, [29, 3652, 13448, 26909, 32285]),
(5, [29, 3652, 13448, 32152, 32285]),
(5, [29, 3652, 13469, 26896, 32285])
],
#[
(5, [29, 3652, 13471, 26896, 32285]),
(5, [29, 3652, 13802, 26896, 32285]),
(5, [29, 3652, 19319, 26896, 32285]),
(5, [29, 3652, 26896, 32152, 32285]),
(5, [29, 13448, 16076, 26896, 32285]),
(5, [29, 13448, 26896, 28500, 32285]),
(5, [29, 13448, 26896, 29115, 32285]),
(5, [31, 35, 482, 13448, 26896]),
(5, [31, 35, 482, 13448, 32152]),
(5, [31, 35, 482, 26896, 32152]),
(5, [31, 64, 128, 3652, 32152]),
(5, [31, 64, 482, 2628, 26896]),
(5, [31, 64, 482, 3652, 27920]),
(5, [31, 64, 482, 16076, 32152]),
(5, [31, 64, 482, 26896, 30139]),
(5, [31, 64, 482, 28500, 32152])
],
#[
(5, [31, 64, 1506, 3652, 26896]),
(5, [31, 64, 3652, 13320, 26896]),
(5, [31, 64, 3652, 19447, 26896]),
(5, [31, 64, 13448, 27122, 28500]),
(5, [31, 68, 128, 13448, 26896]),
(5, [31, 68, 136, 13448, 26896]),
(5, [31, 68, 482, 5871, 13448]),
(5, [31, 68, 482, 13448, 26896]),
(5, [31, 68, 482, 13448, 26911]),
(5, [31, 68, 482, 13448, 26964]),
(5, [31, 68, 482, 13448, 32152]),
(5, [31, 68, 482, 13471, 26896]),
(5, [31, 68, 482, 13516, 26896]),
(5, [31, 68, 482, 13802, 26896]),
(5, [31, 68, 482, 13823, 26896]),
(5, [31, 68, 482, 19319, 26896])
],
#[
(5, [31, 68, 482, 26896, 32152]),
(5, [31, 68, 486, 13448, 26896]),
(5, [31, 68, 511, 5871, 13448]),
(5, [31, 68, 511, 13448, 26896]),
(5, [31, 68, 511, 13448, 26911]),
(5, [31, 68, 511, 13448, 26964]),
(5, [31, 68, 511, 13448, 32152]),
(5, [31, 68, 511, 13471, 26896]),
(5, [31, 68, 511, 13516, 26896]),
(5, [31, 68, 511, 13802, 26896]),
(5, [31, 68, 511, 13823, 26896]),
(5, [31, 68, 511, 19319, 26896]),
(5, [31, 68, 511, 26896, 32152]),
(5, [31, 68, 13448, 26896, 27122]),
(5, [31, 68, 13448, 26896, 27135]),
(5, [31, 68, 13448, 26896, 32256])
],
#[
(5, [31, 68, 13448, 26896, 32285]),
(5, [31, 128, 482, 615, 3652]),
(5, [31, 128, 482, 2628, 26896]),
(5, [31, 128, 482, 3652, 27920]),
(5, [31, 128, 482, 3652, 32152]),
(5, [31, 128, 482, 3652, 32159]),
(5, [31, 128, 482, 3780, 32152]),
(5, [31, 128, 482, 16076, 32152]),
(5, [31, 128, 482, 26896, 30139]),
(5, [31, 128, 482, 28500, 32152]),
(5, [31, 128, 482, 29115, 32152]),
(5, [31, 128, 482, 32152, 32732]),
(5, [31, 128, 511, 3652, 32152]),
(5, [31, 128, 1506, 3652, 26896]),
(5, [31, 128, 3652, 13448, 26960]),
(5, [31, 128, 3652, 13512, 26896])
],
#[
(5, [31, 128, 3652, 13802, 32152]),
(5, [31, 128, 3652, 27122, 32152]),
(5, [31, 128, 3652, 32152, 32250]),
(5, [31, 128, 3652, 32152, 32285]),
(5, [31, 128, 13448, 27122, 28500]),
(5, [31, 128, 13802, 16076, 26896]),
(5, [31, 130, 482, 3652, 32152]),
(5, [31, 130, 482, 3652, 32159]),
(5, [31, 136, 482, 3652, 32152]),
(5, [31, 136, 511, 3652, 32152]),
(5, [31, 159, 482, 3652, 32152]),
(5, [31, 192, 482, 3652, 32152]),
(5, [31, 192, 482, 16076, 32152]),
(5, [31, 192, 3652, 5871, 13448]),
(5, [31, 192, 3652, 13448, 26896]),
(5, [31, 192, 3652, 13448, 26911])
],
#[
(5, [31, 192, 3652, 13448, 27088]),
(5, [31, 192, 3652, 13448, 32152]),
(5, [31, 192, 3652, 13471, 26896]),
(5, [31, 192, 3652, 13512, 26896]),
(5, [31, 192, 3652, 16076, 32152]),
(5, [31, 192, 3652, 19319, 26896]),
(5, [31, 192, 3652, 26896, 32152]),
(5, [31, 192, 3652, 32152]),
(5, [31, 192, 3652, 32152, 32767]),
(5, [31, 192, 3780, 13448, 26896]),
(5, [31, 192, 5871, 13448, 16076]),
(5, [31, 192, 13448, 16076, 26896]),
(5, [31, 192, 13448, 16076, 26911]),
(5, [31, 192, 13448, 16076, 27088]),
(5, [31, 192, 13448, 16076, 32152]),
(5, [31, 192, 13448, 16691, 26896])
],
#[
(5, [31, 192, 13448, 26896, 28500]),
(5, [31, 192, 13448, 26896, 29115]),
(5, [31, 192, 13448, 26896, 32732]),
(5, [31, 192, 16076, 19319, 26896]),
(5, [31, 192, 16076, 26896, 32152]),
(5, [31, 192, 16076, 32152]),
(5, [31, 192, 16076, 32152, 32767]),
(5, [31, 194, 3652, 13448, 26896]),
(5, [31, 194, 3652, 13471, 26896]),
(5, [31, 194, 13448, 16076, 26896]),
(5, [31, 204, 482, 13448, 26896]),
(5, [31, 204, 511, 13448, 26896]),
(5, [31, 204, 3652, 13448, 26896]),
(5, [31, 204, 13448, 16076, 26896]),
(5, [31, 204, 13448, 26896]),
(5, [31, 204, 13448, 26896, 32767])
],
#[
(5, [31, 223, 3652, 13448, 26896]),
(5, [31, 223, 13448, 16076, 26896]),
(5, [31, 224, 3652, 5856, 13448]),
(5, [31, 224, 3652, 13448, 26896]),
(5, [31, 224, 3652, 13448, 26911]),
(5, [31, 226, 482, 1604, 13448]),
(5, [31, 226, 482, 3652, 32152]),
(5, [31, 226, 1024, 3652, 5871]),
(5, [31, 226, 1024, 3652, 26896]),
(5, [31, 226, 1604, 3652, 13448]),
(5, [31, 226, 1604, 5871, 13448]),
(5, [31, 226, 1604, 13448]),
(5, [31, 226, 1604, 13448, 26896]),
(5, [31, 226, 1604, 13448, 32767]),
(5, [31, 226, 2048, 3652, 13448]),
(5, [31, 226, 3652, 5256, 5871])
],
#[
(5, [31, 226, 3652, 5256, 26896]),
(5, [31, 226, 3652, 5871, 13448]),
(5, [31, 226, 3652, 5871, 13471]),
(5, [31, 226, 3652, 5871, 13546]),
(5, [31, 226, 3652, 5871, 13802]),
(5, [31, 226, 3652, 5871, 19319]),
(5, [31, 226, 3652, 5871, 32152]),
(5, [31, 226, 3652, 5887, 13448]),
(5, [31, 226, 3652, 6127, 13448]),
(5, [31, 226, 3652, 13448, 14063]),
(5, [31, 226, 3652, 13448, 26896]),
(5, [31, 226, 3652, 13448, 26911]),
(5, [31, 226, 3652, 13448, 27122]),
(5, [31, 226, 3652, 13448, 32152]),
(5, [31, 226, 3652, 13471, 26896]),
(5, [31, 226, 3652, 13546, 26896])
],
#[
(5, [31, 226, 3652, 13802, 26896]),
(5, [31, 226, 3652, 19319, 26896]),
(5, [31, 226, 3652, 26896, 32152]),
(5, [31, 226, 3652, 32152]),
(5, [31, 226, 3652, 32152, 32767]),
(5, [31, 226, 5871, 13448, 16076]),
(5, [31, 226, 5871, 13448, 28500]),
(5, [31, 226, 5871, 13448, 29115]),
(5, [31, 226, 13448, 16076, 26896]),
(5, [31, 226, 13448, 26896, 28500]),
(5, [31, 226, 13448, 26896, 29115]),
(5, [31, 239, 3652, 5871, 13448]),
(5, [31, 239, 3652, 13448, 26896]),
(5, [31, 255, 3652, 5871, 13448]),
(5, [31, 255, 3652, 13448, 26896]),
(5, [31, 256, 482, 615, 3652])
],
#[
(5, [31, 256, 482, 1604, 13448]),
(5, [31, 256, 482, 2628, 26896]),
(5, [31, 256, 482, 3072, 3652]),
(5, [31, 256, 482, 3652, 15496]),
(5, [31, 256, 482, 3652, 27920]),
(5, [31, 256, 482, 3652, 32152]),
(5, [31, 256, 482, 3652, 32159]),
(5, [31, 256, 482, 3652, 32250]),
(5, [31, 256, 482, 3908, 32152]),
(5, [31, 256, 482, 13448, 31163]),
(5, [31, 256, 482, 16076, 32152]),
(5, [31, 256, 482, 26896, 30139]),
(5, [31, 256, 482, 28500, 32152]),
(5, [31, 256, 482, 29115, 32152]),
(5, [31, 256, 482, 32152, 32732]),
(5, [31, 256, 511, 3652, 32152])
],
#[
(5, [31, 256, 1506, 3652, 26896]),
(5, [31, 256, 2530, 3652, 13448]),
(5, [31, 256, 3652, 32152, 32285]),
(5, [31, 256, 13448, 27122, 28500]),
(5, [31, 258, 482, 3652, 32152]),
(5, [31, 258, 482, 3652, 32159]),
(5, [31, 272, 482, 3652, 32152]),
(5, [31, 272, 511, 3652, 32152]),
(5, [31, 287, 482, 3652, 32152]),
(5, [31, 320, 482, 3652, 32152]),
(5, [31, 320, 482, 28500, 32152]),
(5, [31, 320, 13448, 27122, 28500]),
(5, [31, 340, 482, 13448, 26896]),
(5, [31, 340, 511, 13448, 26896]),
(5, [31, 354, 482, 2628, 26896]),
(5, [31, 354, 482, 3652, 32152])
],
#[
(5, [31, 354, 3652, 19447, 26896]),
(5, [31, 384, 482, 16076, 32152]),
(5, [31, 384, 482, 28500, 32152]),
(5, [31, 418, 482, 26896, 30139]),
(5, [31, 418, 3652, 13802, 26896]),
(5, [31, 418, 13448, 26896, 29179]),
(5, [31, 418, 13802, 26896, 29115]),
(5, [31, 443, 482, 13448, 26896]),
(5, [31, 443, 511, 13448, 26896]),
(5, [31, 448, 3652, 13448, 26896]),
(5, [31, 448, 3652, 13448, 32152]),
(5, [31, 448, 3652, 26896, 32152]),
(5, [31, 448, 13448, 16076, 26896]),
(5, [31, 448, 13448, 26896, 28500]),
(5, [31, 448, 13448, 26896, 32732]),
(5, [31, 448, 13448, 32152, 32732])
],
#[
(5, [31, 448, 26896, 32152, 32732]),
(5, [31, 480, 1024, 3652, 26896]),
(5, [31, 480, 3652, 5871, 13448]),
(5, [31, 480, 3652, 13440, 26896]),
(5, [31, 480, 3652, 13448, 26880]),
(5, [31, 480, 3652, 13448, 26896]),
(5, [31, 480, 3652, 13448, 26911]),
(5, [31, 480, 3652, 13448, 32152]),
(5, [31, 480, 3652, 13471, 26896]),
(5, [31, 480, 3652, 13800, 26896]),
(5, [31, 480, 3652, 13802, 26896]),
(5, [31, 480, 3652, 19319, 26896]),
(5, [31, 480, 3652, 26896, 32152]),
(5, [31, 480, 13448, 16076, 26896]),
(5, [31, 480, 13448, 26896, 28500]),
(5, [31, 480, 13448, 26896, 29115])
]
],
#[
#[
(5, [31, 482, 511, 2628, 26896]),
(5, [31, 482, 511, 3652, 27920]),
(5, [31, 482, 511, 16076, 32152]),
(5, [31, 482, 511, 26896, 30139]),
(5, [31, 482, 511, 28500, 32152]),
(5, [31, 482, 517, 3652, 26896]),
(5, [31, 482, 580, 615, 13448]),
(5, [31, 482, 580, 615, 26896]),
(5, [31, 482, 580, 3652, 26896]),
(5, [31, 482, 580, 13448, 26896]),
(5, [31, 482, 580, 13448, 32152]),
(5, [31, 482, 580, 26896]),
(5, [31, 482, 580, 26896, 32152]),
(5, [31, 482, 580, 26896, 32767]),
(5, [31, 482, 608, 3652, 13448]),
(5, [31, 482, 608, 3652, 13471])
],
#[
(5, [31, 482, 608, 3652, 26896]),
(5, [31, 482, 608, 3652, 26911]),
(5, [31, 482, 615, 3652, 5871]),
(5, [31, 482, 615, 3652, 13448]),
(5, [31, 482, 615, 3652, 13471]),
(5, [31, 482, 615, 3652, 14063]),
(5, [31, 482, 615, 3652, 16076]),
(5, [31, 482, 615, 3652, 19319]),
(5, [31, 482, 615, 3652, 26896]),
(5, [31, 482, 615, 3652, 26911]),
(5, [31, 482, 615, 3652, 27511]),
(5, [31, 482, 615, 3652, 28500]),
(5, [31, 482, 615, 13448, 16076]),
(5, [31, 482, 615, 13448, 28500]),
(5, [31, 482, 615, 13448, 29115]),
(5, [31, 482, 615, 13448, 32732])
],
#[
(5, [31, 482, 615, 16076]),
(5, [31, 482, 615, 16076, 26896]),
(5, [31, 482, 615, 16076, 32152]),
(5, [31, 482, 615, 16076, 32767]),
(5, [31, 482, 615, 26896, 28500]),
(5, [31, 482, 615, 26896, 29115]),
(5, [31, 482, 615, 26896, 32732]),
(5, [31, 482, 615, 28500]),
(5, [31, 482, 615, 28500, 32152]),
(5, [31, 482, 615, 28500, 32767]),
(5, [31, 482, 639, 3652, 13448]),
(5, [31, 482, 639, 3652, 26896]),
(5, [31, 482, 999, 3652, 26896]),
(5, [31, 482, 1024, 1604, 5871]),
(5, [31, 482, 1024, 1604, 26896]),
(5, [31, 482, 1024, 2304, 3652])
],
#[
(5, [31, 482, 1024, 2628, 26896]),
(5, [31, 482, 1024, 3652, 4847]),
(5, [31, 482, 1024, 3652, 5856]),
(5, [31, 482, 1024, 3652, 5871]),
(5, [31, 482, 1024, 3652, 5887]),
(5, [31, 482, 1024, 3652, 14063]),
(5, [31, 482, 1024, 3652, 18704]),
(5, [31, 482, 1024, 3652, 26880]),
(5, [31, 482, 1024, 3652, 26896]),
(5, [31, 482, 1024, 3652, 26898]),
(5, [31, 482, 1024, 3652, 26900]),
(5, [31, 482, 1024, 3652, 26904]),
(5, [31, 482, 1024, 3652, 26960]),
(5, [31, 482, 1024, 3652, 27920]),
(5, [31, 482, 1024, 3652, 27935]),
(5, [31, 482, 1024, 3654, 26896])
],
#[
(5, [31, 482, 1024, 3668, 26896]),
(5, [31, 482, 1024, 3908, 26896]),
(5, [31, 482, 1024, 4267, 26896]),
(5, [31, 482, 1024, 5871, 28500]),
(5, [31, 482, 1024, 5871, 29115]),
(5, [31, 482, 1024, 11844, 26896]),
(5, [31, 482, 1024, 16076, 32152]),
(5, [31, 482, 1024, 26896, 28500]),
(5, [31, 482, 1024, 26896, 29115]),
(5, [31, 482, 1024, 26896, 30139]),
(5, [31, 482, 1024, 26896, 31163]),
(5, [31, 482, 1024, 26911, 29115]),
(5, [31, 482, 1024, 27122, 28500]),
(5, [31, 482, 1024, 27920, 28500]),
(5, [31, 482, 1024, 27920, 29115]),
(5, [31, 482, 1024, 28500, 32152])
],
#[
(5, [31, 482, 1026, 3652, 26896]),
(5, [31, 482, 1028, 3652, 5871]),
(5, [31, 482, 1028, 3652, 26896]),
(5, [31, 482, 1028, 3652, 26911]),
(5, [31, 482, 1028, 3652, 27924]),
(5, [31, 482, 1028, 3679, 26896]),
(5, [31, 482, 1028, 26896, 28500]),
(5, [31, 482, 1028, 26896, 29115]),
(5, [31, 482, 1032, 3652, 5871]),
(5, [31, 482, 1032, 3652, 26896]),
(5, [31, 482, 1032, 3652, 26911]),
(5, [31, 482, 1032, 3652, 27928]),
(5, [31, 482, 1032, 3660, 26896]),
(5, [31, 482, 1032, 26896, 28500]),
(5, [31, 482, 1032, 26896, 29115]),
(5, [31, 482, 1040, 3652, 26896])
],
#[
(5, [31, 482, 1055, 3652, 5871]),
(5, [31, 482, 1055, 3652, 26896]),
(5, [31, 482, 1055, 3652, 26911]),
(5, [31, 482, 1055, 3652, 27920]),
(5, [31, 482, 1055, 3652, 27935]),
(5, [31, 482, 1055, 26896, 28500]),
(5, [31, 482, 1055, 26896, 29115]),
(5, [31, 482, 1088, 3652, 5871]),
(5, [31, 482, 1088, 3652, 26896]),
(5, [31, 482, 1088, 3652, 26911]),
(5, [31, 482, 1088, 3652, 27984]),
(5, [31, 482, 1088, 4070, 26896]),
(5, [31, 482, 1088, 26896, 28500]),
(5, [31, 482, 1088, 26896, 29115]),
(5, [31, 482, 1092, 3652, 26896]),
(5, [31, 482, 1092, 13448, 26896])
],
#[
(5, [31, 482, 1092, 13471, 26896]),
(5, [31, 482, 1092, 13802, 26896]),
(5, [31, 482, 1092, 13823, 26896]),
(5, [31, 482, 1098, 3652, 26896]),
(5, [31, 482, 1119, 3652, 26896]),
(5, [31, 482, 1152, 2304, 3652]),
(5, [31, 482, 1152, 3652, 5871]),
(5, [31, 482, 1152, 3652, 26896]),
(5, [31, 482, 1152, 3652, 26911]),
(5, [31, 482, 1152, 3652, 28048]),
(5, [31, 482, 1152, 3652, 32152]),
(5, [31, 482, 1152, 3780, 26896]),
(5, [31, 482, 1152, 26896, 28500]),
(5, [31, 482, 1152, 26896, 29115]),
(5, [31, 482, 1158, 3652, 26896]),
(5, [31, 482, 1160, 3652, 26896])
],
#[
(5, [31, 482, 1183, 3652, 26896]),
(5, [31, 482, 1280, 3652, 26896]),
(5, [31, 482, 1506, 3652, 5871]),
(5, [31, 482, 1506, 3652, 26896]),
(5, [31, 482, 1506, 3652, 26911]),
(5, [31, 482, 1506, 3652, 27920]),
(5, [31, 482, 1506, 26896, 28500]),
(5, [31, 482, 1506, 26896, 29115]),
(5, [31, 482, 1510, 3652, 26896]),
(5, [31, 482, 1514, 3652, 26896]),
(5, [31, 482, 1535, 3652, 26896]),
(5, [31, 482, 1604, 5256, 5871]),
(5, [31, 482, 1604, 5256, 26896]),
(5, [31, 482, 1604, 5871, 13448]),
(5, [31, 482, 1604, 5871, 13471]),
(5, [31, 482, 1604, 5871, 13802])
],
#[
(5, [31, 482, 1604, 5871, 19319]),
(5, [31, 482, 1604, 5871, 32152]),
(5, [31, 482, 1604, 5887, 13448]),
(5, [31, 482, 1604, 7919, 13448]),
(5, [31, 482, 1604, 13448, 14063]),
(5, [31, 482, 1604, 13448, 26896]),
(5, [31, 482, 1604, 13448, 26911]),
(5, [31, 482, 1604, 13448, 28500]),
(5, [31, 482, 1604, 13448, 32152]),
(5, [31, 482, 1604, 13471, 26896]),
(5, [31, 482, 1604, 13802, 26896]),
(5, [31, 482, 1604, 19319, 26896]),
(5, [31, 482, 1604, 26896, 32152]),
(5, [31, 482, 1766, 3652, 13448]),
(5, [31, 482, 2048, 2628, 26896]),
(5, [31, 482, 2048, 3652, 27920])
],
#[
(5, [31, 482, 2048, 3908, 13448]),
(5, [31, 482, 2048, 16076, 32152]),
(5, [31, 482, 2048, 26896, 30139]),
(5, [31, 482, 2048, 28500, 32152]),
(5, [31, 482, 2116, 13448, 26896]),
(5, [31, 482, 2116, 13448, 26911]),
(5, [31, 482, 2304, 3652, 13448]),
(5, [31, 482, 2304, 3652, 13471]),
(5, [31, 482, 2304, 3652, 13802]),
(5, [31, 482, 2304, 3652, 15752]),
(5, [31, 482, 2304, 3652, 19319]),
(5, [31, 482, 2304, 3652, 32152]),
(5, [31, 482, 2304, 3908, 13448]),
(5, [31, 482, 2304, 13448, 16076]),
(5, [31, 482, 2304, 13448, 29115]),
(5, [31, 482, 2310, 3652, 13448])
],
#[
(5, [31, 482, 2320, 3652, 13448]),
(5, [31, 482, 2335, 3652, 13448]),
(5, [31, 482, 2564, 3652, 26896]),
(5, [31, 482, 2624, 3652, 26896]),
(5, [31, 482, 2628, 2655, 26896]),
(5, [31, 482, 2628, 3046, 26896]),
(5, [31, 482, 2628, 3652, 5871]),
(5, [31, 482, 2628, 3652, 18704]),
(5, [31, 482, 2628, 3652, 26896]),
(5, [31, 482, 2628, 3652, 26911]),
(5, [31, 482, 2628, 3679, 26896]),
(5, [31, 482, 2628, 4070, 26896]),
(5, [31, 482, 2628, 5871]),
(5, [31, 482, 2628, 5871, 13448]),
(5, [31, 482, 2628, 5871, 19319]),
(5, [31, 482, 2628, 5871, 26896])
],
#[
(5, [31, 482, 2628, 5871, 32767]),
(5, [31, 482, 2628, 8192, 26896]),
(5, [31, 482, 2628, 13448, 18704]),
(5, [31, 482, 2628, 13448, 26896]),
(5, [31, 482, 2628, 13448, 26911]),
(5, [31, 482, 2628, 13448, 32152]),
(5, [31, 482, 2628, 13471, 26896]),
(5, [31, 482, 2628, 13802, 26896]),
(5, [31, 482, 2628, 16076, 26896]),
(5, [31, 482, 2628, 18704]),
(5, [31, 482, 2628, 18704, 19319]),
(5, [31, 482, 2628, 18704, 26896]),
(5, [31, 482, 2628, 18704, 32767]),
(5, [31, 482, 2628, 19319, 26896]),
(5, [31, 482, 2628, 19319, 26911]),
(5, [31, 482, 2628, 19319, 32152])
],
#[
(5, [31, 482, 2628, 19327, 26896]),
(5, [31, 482, 2628, 19447, 26896]),
(5, [31, 482, 2628, 20343, 26896]),
(5, [31, 482, 2628, 26896]),
(5, [31, 482, 2628, 26896, 26911]),
(5, [31, 482, 2628, 26896, 27122]),
(5, [31, 482, 2628, 26896, 27476]),
(5, [31, 482, 2628, 26896, 27511]),
(5, [31, 482, 2628, 26896, 28500]),
(5, [31, 482, 2628, 26896, 29115]),
(5, [31, 482, 2628, 26896, 30139]),
(5, [31, 482, 2628, 26896, 31743]),
(5, [31, 482, 2628, 26896, 32152]),
(5, [31, 482, 2628, 26896, 32285]),
(5, [31, 482, 2628, 26896, 32736]),
(5, [31, 482, 2628, 26896, 32767])
],
#[
(5, [31, 482, 2628, 26911]),
(5, [31, 482, 2628, 26911, 32767]),
(5, [31, 482, 2647, 3652, 26896]),
(5, [31, 482, 2655, 3652, 26896]),
(5, [31, 482, 2918, 3652, 26896]),
(5, [31, 482, 3046, 3652, 26896]),
(5, [31, 482, 3072, 3652, 5871]),
(5, [31, 482, 3072, 3652, 26896]),
(5, [31, 482, 3072, 3652, 26911]),
(5, [31, 482, 3072, 3652, 27920]),
(5, [31, 482, 3072, 3652, 28500]),
(5, [31, 482, 3072, 16076, 32152]),
(5, [31, 482, 3072, 26896, 28500]),
(5, [31, 482, 3072, 26896, 29115]),
(5, [31, 482, 3072, 28500, 32152]),
(5, [31, 482, 3076, 3652, 26896])
],
#[
(5, [31, 482, 3076, 3652, 26911]),
(5, [31, 482, 3096, 3652, 26896]),
(5, [31, 482, 3103, 3652, 26896]),
(5, [31, 482, 3136, 3652, 26896]),
(5, [31, 482, 3456, 3652, 13448]),
(5, [31, 482, 3456, 3652, 26896]),
(5, [31, 482, 3554, 3652, 26896]),
(5, [31, 482, 3652, 3679, 27920]),
(5, [31, 482, 3652, 3679, 27928]),
(5, [31, 482, 3652, 3780, 32152]),
(5, [31, 482, 3652, 3908, 32152]),
(5, [31, 482, 3652, 4070, 27920]),
(5, [31, 482, 3652, 4267, 32152]),
(5, [31, 482, 3652, 4847]),
(5, [31, 482, 3652, 4847, 13448]),
(5, [31, 482, 3652, 4847, 26896])
]
],
#[
#[
(5, [31, 482, 3652, 4847, 27920]),
(5, [31, 482, 3652, 4847, 32767]),
(5, [31, 482, 3652, 5128, 26896]),
(5, [31, 482, 3652, 5248, 5856]),
(5, [31, 482, 3652, 5248, 26896]),
(5, [31, 482, 3652, 5248, 26911]),
(5, [31, 482, 3652, 5256, 5871]),
(5, [31, 482, 3652, 5256, 5887]),
(5, [31, 482, 3652, 5256, 14063]),
(5, [31, 482, 3652, 5256, 26896]),
(5, [31, 482, 3652, 5256, 26911]),
(5, [31, 482, 3652, 5256, 32152]),
(5, [31, 482, 3652, 5263, 5871]),
(5, [31, 482, 3652, 5263, 26896]),
(5, [31, 482, 3652, 5279, 5871]),
(5, [31, 482, 3652, 5279, 26896])
],
#[
(5, [31, 482, 3652, 5354, 5871]),
(5, [31, 482, 3652, 5354, 26896]),
(5, [31, 482, 3652, 5610, 5871]),
(5, [31, 482, 3652, 5610, 26896]),
(5, [31, 482, 3652, 5743, 13448]),
(5, [31, 482, 3652, 5807, 13448]),
(5, [31, 482, 3652, 5856, 13448]),
(5, [31, 482, 3652, 5856, 13471]),
(5, [31, 482, 3652, 5856, 13802]),
(5, [31, 482, 3652, 5856, 19319]),
(5, [31, 482, 3652, 5856, 32152]),
(5, [31, 482, 3652, 5856, 32159]),
(5, [31, 482, 3652, 5863, 13448]),
(5, [31, 482, 3652, 5867, 13448]),
(5, [31, 482, 3652, 5869, 13448]),
(5, [31, 482, 3652, 5871, 9216])
],
#[
(5, [31, 482, 3652, 5871, 13320]),
(5, [31, 482, 3652, 5871, 13440]),
(5, [31, 482, 3652, 5871, 13448]),
(5, [31, 482, 3652, 5871, 13450]),
(5, [31, 482, 3652, 5871, 13452]),
(5, [31, 482, 3652, 5871, 13455]),
(5, [31, 482, 3652, 5871, 13464]),
(5, [31, 482, 3652, 5871, 13512]),
(5, [31, 482, 3652, 5871, 13546]),
(5, [31, 482, 3652, 5871, 13704]),
(5, [31, 482, 3652, 5871, 13823]),
(5, [31, 482, 3652, 5871, 15496]),
(5, [31, 482, 3652, 5871, 18965]),
(5, [31, 482, 3652, 5871, 19296]),
(5, [31, 482, 3652, 5871, 19327]),
(5, [31, 482, 3652, 5871, 19447])
],
#[
(5, [31, 482, 3652, 5871, 27511]),
(5, [31, 482, 3652, 5871, 27920]),
(5, [31, 482, 3652, 5871, 30139]),
(5, [31, 482, 3652, 5871, 31743]),
(5, [31, 482, 3652, 5871, 32152]),
(5, [31, 482, 3652, 5871, 32159]),
(5, [31, 482, 3652, 5871, 32250]),
(5, [31, 482, 3652, 5887, 13448]),
(5, [31, 482, 3652, 5887, 13471]),
(5, [31, 482, 3652, 5887, 13802]),
(5, [31, 482, 3652, 5887, 19319]),
(5, [31, 482, 3652, 5887, 32152]),
(5, [31, 482, 3652, 7919, 32152]),
(5, [31, 482, 3652, 8192, 27920]),
(5, [31, 482, 3652, 8320, 32152]),
(5, [31, 482, 3652, 8448, 32152])
],
#[
(5, [31, 482, 3652, 8448, 32250]),
(5, [31, 482, 3652, 9216, 26896]),
(5, [31, 482, 3652, 9216, 26911]),
(5, [31, 482, 3652, 9216, 27920]),
(5, [31, 482, 3652, 9224, 26896]),
(5, [31, 482, 3652, 9224, 26911]),
(5, [31, 482, 3652, 9236, 26896]),
(5, [31, 482, 3652, 9247, 26896]),
(5, [31, 482, 3652, 9344, 26896]),
(5, [31, 482, 3652, 9536, 26896]),
(5, [31, 482, 3652, 9698, 26896]),
(5, [31, 482, 3652, 10496, 13448]),
(5, [31, 482, 3652, 10496, 13802]),
(5, [31, 482, 3652, 12424, 32152]),
(5, [31, 482, 3652, 13312, 26896]),
(5, [31, 482, 3652, 13320, 26896])
],
#[
(5, [31, 482, 3652, 13320, 26911]),
(5, [31, 482, 3652, 13320, 32024]),
(5, [31, 482, 3652, 13341, 26896]),
(5, [31, 482, 3652, 13343, 26896]),
(5, [31, 482, 3652, 13440, 26880]),
(5, [31, 482, 3652, 13440, 26896]),
(5, [31, 482, 3652, 13440, 26911]),
(5, [31, 482, 3652, 13440, 32144]),
(5, [31, 482, 3652, 13440, 32152]),
(5, [31, 482, 3652, 13448, 14056]),
(5, [31, 482, 3652, 13448, 14063]),
(5, [31, 482, 3652, 13448, 14079]),
(5, [31, 482, 3652, 13448, 15752]),
(5, [31, 482, 3652, 13448, 18688]),
(5, [31, 482, 3652, 13448, 18704]),
(5, [31, 482, 3652, 13448, 18711])
],
#[
(5, [31, 482, 3652, 13448, 18719]),
(5, [31, 482, 3652, 13448, 26880]),
(5, [31, 482, 3652, 13448, 26898]),
(5, [31, 482, 3652, 13448, 26900]),
(5, [31, 482, 3652, 13448, 26902]),
(5, [31, 482, 3652, 13448, 26903]),
(5, [31, 482, 3652, 13448, 26904]),
(5, [31, 482, 3652, 13448, 26906]),
(5, [31, 482, 3652, 13448, 26907]),
(5, [31, 482, 3652, 13448, 26908]),
(5, [31, 482, 3652, 13448, 26909]),
(5, [31, 482, 3652, 13448, 26911]),
(5, [31, 482, 3652, 13448, 26960]),
(5, [31, 482, 3652, 13448, 26962]),
(5, [31, 482, 3652, 13448, 26964]),
(5, [31, 482, 3652, 13448, 26975])
],
#[
(5, [31, 482, 3652, 13448, 27024]),
(5, [31, 482, 3652, 13448, 27026]),
(5, [31, 482, 3652, 13448, 27032]),
(5, [31, 482, 3652, 13448, 27039]),
(5, [31, 482, 3652, 13448, 27088]),
(5, [31, 482, 3652, 13448, 27920]),
(5, [31, 482, 3652, 13448, 27924]),
(5, [31, 482, 3652, 13448, 27928]),
(5, [31, 482, 3652, 13448, 27935]),
(5, [31, 482, 3652, 13448, 27984]),
(5, [31, 482, 3652, 13448, 28048]),
(5, [31, 482, 3652, 13448, 30463]),
(5, [31, 482, 3652, 13448, 31001]),
(5, [31, 482, 3652, 13448, 31128]),
(5, [31, 482, 3652, 13448, 32024]),
(5, [31, 482, 3652, 13448, 32128])
],
#[
(5, [31, 482, 3652, 13448, 32136]),
(5, [31, 482, 3652, 13448, 32144]),
(5, [31, 482, 3652, 13448, 32152]),
(5, [31, 482, 3652, 13448, 32154]),
(5, [31, 482, 3652, 13448, 32156]),
(5, [31, 482, 3652, 13448, 32159]),
(5, [31, 482, 3652, 13448, 32216]),
(5, [31, 482, 3652, 13450, 26896]),
(5, [31, 482, 3652, 13450, 26898]),
(5, [31, 482, 3652, 13450, 26911]),
(5, [31, 482, 3652, 13450, 32152]),
(5, [31, 482, 3652, 13450, 32154]),
(5, [31, 482, 3652, 13452, 26896]),
(5, [31, 482, 3652, 13452, 26900]),
(5, [31, 482, 3652, 13452, 26911]),
(5, [31, 482, 3652, 13452, 32152])
],
#[
(5, [31, 482, 3652, 13452, 32156]),
(5, [31, 482, 3652, 13454, 26896]),
(5, [31, 482, 3652, 13455, 26896]),
(5, [31, 482, 3652, 13464, 26896]),
(5, [31, 482, 3652, 13464, 26911]),
(5, [31, 482, 3652, 13464, 32152]),
(5, [31, 482, 3652, 13466, 26896]),
(5, [31, 482, 3652, 13467, 26896]),
(5, [31, 482, 3652, 13468, 26896]),
(5, [31, 482, 3652, 13469, 26896]),
(5, [31, 482, 3652, 13471, 14063]),
(5, [31, 482, 3652, 13471, 14079]),
(5, [31, 482, 3652, 13471, 18688]),
(5, [31, 482, 3652, 13471, 18704]),
(5, [31, 482, 3652, 13471, 26880]),
(5, [31, 482, 3652, 13471, 26896])
],
#[
(5, [31, 482, 3652, 13471, 26898]),
(5, [31, 482, 3652, 13471, 26900]),
(5, [31, 482, 3652, 13471, 26904]),
(5, [31, 482, 3652, 13471, 26960]),
(5, [31, 482, 3652, 13471, 27024]),
(5, [31, 482, 3652, 13471, 27026]),
(5, [31, 482, 3652, 13471, 27920]),
(5, [31, 482, 3652, 13471, 27924]),
(5, [31, 482, 3652, 13471, 32159]),
(5, [31, 482, 3652, 13483, 26896]),
(5, [31, 482, 3652, 13512, 26896]),
(5, [31, 482, 3652, 13512, 26911]),
(5, [31, 482, 3652, 13512, 26960]),
(5, [31, 482, 3652, 13512, 32152]),
(5, [31, 482, 3652, 13512, 32216]),
(5, [31, 482, 3652, 13514, 26896])
],
#[
(5, [31, 482, 3652, 13516, 26896]),
(5, [31, 482, 3652, 13535, 26896]),
(5, [31, 482, 3652, 13546, 26896]),
(5, [31, 482, 3652, 13704, 26896]),
(5, [31, 482, 3652, 13704, 26911]),
(5, [31, 482, 3652, 13706, 26896]),
(5, [31, 482, 3652, 13706, 26911]),
(5, [31, 482, 3652, 13720, 26896]),
(5, [31, 482, 3652, 13727, 26896]),
(5, [31, 482, 3652, 13738, 26896]),
(5, [31, 482, 3652, 13768, 26896]),
(5, [31, 482, 3652, 13792, 26896]),
(5, [31, 482, 3652, 13794, 26896]),
(5, [31, 482, 3652, 13800, 26896]),
(5, [31, 482, 3652, 13802, 14063]),
(5, [31, 482, 3652, 13802, 18704])
],
#[
(5, [31, 482, 3652, 13802, 26880]),
(5, [31, 482, 3652, 13802, 26896]),
(5, [31, 482, 3652, 13802, 26898]),
(5, [31, 482, 3652, 13802, 26900]),
(5, [31, 482, 3652, 13802, 26904]),
(5, [31, 482, 3652, 13802, 26906]),
(5, [31, 482, 3652, 13802, 26960]),
(5, [31, 482, 3652, 13802, 27920]),
(5, [31, 482, 3652, 13802, 27984]),
(5, [31, 482, 3652, 13806, 26896]),
(5, [31, 482, 3652, 13818, 26896]),
(5, [31, 482, 3652, 13823, 26896]),
(5, [31, 482, 3652, 13823, 26911]),
(5, [31, 482, 3652, 14063, 19319]),
(5, [31, 482, 3652, 14063, 32152]),
(5, [31, 482, 3652, 15496, 26896])
],
#[
(5, [31, 482, 3652, 15496, 26911]),
(5, [31, 482, 3652, 15496, 28500]),
(5, [31, 482, 3652, 15496, 32152]),
(5, [31, 482, 3652, 15500, 26896]),
(5, [31, 482, 3652, 15500, 26911]),
(5, [31, 482, 3652, 15512, 26896]),
(5, [31, 482, 3652, 15519, 26896]),
(5, [31, 482, 3652, 15560, 26896]),
(5, [31, 482, 3652, 15752, 26896]),
(5, [31, 482, 3652, 15850, 26896]),
(5, [31, 482, 3652, 16076, 27920]),
(5, [31, 482, 3652, 16076, 32159]),
(5, [31, 482, 3652, 16095, 32152]),
(5, [31, 482, 3652, 16095, 32159]),
(5, [31, 482, 3652, 16691, 32152]),
(5, [31, 482, 3652, 17271, 26896])
],
#[
(5, [31, 482, 3652, 18688, 19296]),
(5, [31, 482, 3652, 18704, 19319]),
(5, [31, 482, 3652, 18704, 19327]),
(5, [31, 482, 3652, 18704, 19447]),
(5, [31, 482, 3652, 18704, 27511]),
(5, [31, 482, 3652, 18704, 32152]),
(5, [31, 482, 3652, 18711, 19319]),
(5, [31, 482, 3652, 18719, 19319]),
(5, [31, 482, 3652, 18944, 26896]),
(5, [31, 482, 3652, 18965, 26896]),
(5, [31, 482, 3652, 18965, 26911]),
(5, [31, 482, 3652, 18975, 26896]),
(5, [31, 482, 3652, 19063, 26896]),
(5, [31, 482, 3652, 19255, 26896]),
(5, [31, 482, 3652, 19284, 26896]),
(5, [31, 482, 3652, 19296, 26896])
],
#[
(5, [31, 482, 3652, 19296, 26911]),
(5, [31, 482, 3652, 19296, 32152]),
(5, [31, 482, 3652, 19296, 32159]),
(5, [31, 482, 3652, 19303, 26896]),
(5, [31, 482, 3652, 19315, 26896]),
(5, [31, 482, 3652, 19317, 26896]),
(5, [31, 482, 3652, 19319, 26880]),
(5, [31, 482, 3652, 19319, 26896]),
(5, [31, 482, 3652, 19319, 26898]),
(5, [31, 482, 3652, 19319, 26900]),
(5, [31, 482, 3652, 19319, 26903]),
(5, [31, 482, 3652, 19319, 26904]),
(5, [31, 482, 3652, 19319, 26960]),
(5, [31, 482, 3652, 19319, 27024]),
(5, [31, 482, 3652, 19319, 27920]),
(5, [31, 482, 3652, 19319, 32152])
]
],
#[
#[
(5, [31, 482, 3652, 19319, 32159]),
(5, [31, 482, 3652, 19327, 26896]),
(5, [31, 482, 3652, 19327, 26911]),
(5, [31, 482, 3652, 19327, 32152]),
(5, [31, 482, 3652, 19426, 26896]),
(5, [31, 482, 3652, 19447, 26896]),
(5, [31, 482, 3652, 19447, 26911]),
(5, [31, 482, 3652, 19455, 26896]),
(5, [31, 482, 3652, 20343, 32152]),
(5, [31, 482, 3652, 23551, 26896]),
(5, [31, 482, 3652, 24848, 32152]),
(5, [31, 482, 3652, 26880, 32136]),
(5, [31, 482, 3652, 26880, 32152]),
(5, [31, 482, 3652, 26896, 27413]),
(5, [31, 482, 3652, 26896, 27476]),
(5, [31, 482, 3652, 26896, 27504])
],
#[
(5, [31, 482, 3652, 26896, 27511]),
(5, [31, 482, 3652, 26896, 27519]),
(5, [31, 482, 3652, 26896, 27639]),
(5, [31, 482, 3652, 26896, 27920]),
(5, [31, 482, 3652, 26896, 27924]),
(5, [31, 482, 3652, 26896, 27928]),
(5, [31, 482, 3652, 26896, 27935]),
(5, [31, 482, 3652, 26896, 27984]),
(5, [31, 482, 3652, 26896, 28048]),
(5, [31, 482, 3652, 26896, 28146]),
(5, [31, 482, 3652, 26896, 29695]),
(5, [31, 482, 3652, 26896, 29849]),
(5, [31, 482, 3652, 26896, 30104]),
(5, [31, 482, 3652, 26896, 30120]),
(5, [31, 482, 3652, 26896, 30139]),
(5, [31, 482, 3652, 26896, 30143])
],
#[
(5, [31, 482, 3652, 26896, 30203]),
(5, [31, 482, 3652, 26896, 31261]),
(5, [31, 482, 3652, 26896, 31615]),
(5, [31, 482, 3652, 26896, 31679]),
(5, [31, 482, 3652, 26896, 31712]),
(5, [31, 482, 3652, 26896, 31735]),
(5, [31, 482, 3652, 26896, 31739]),
(5, [31, 482, 3652, 26896, 31743]),
(5, [31, 482, 3652, 26896, 31768]),
(5, [31, 482, 3652, 26896, 31896]),
(5, [31, 482, 3652, 26896, 32024]),
(5, [31, 482, 3652, 26896, 32128]),
(5, [31, 482, 3652, 26896, 32136]),
(5, [31, 482, 3652, 26896, 32144]),
(5, [31, 482, 3652, 26896, 32152]),
(5, [31, 482, 3652, 26896, 32154])
],
#[
(5, [31, 482, 3652, 26896, 32156]),
(5, [31, 482, 3652, 26896, 32159]),
(5, [31, 482, 3652, 26896, 32187]),
(5, [31, 482, 3652, 26896, 32216]),
(5, [31, 482, 3652, 26896, 32250]),
(5, [31, 482, 3652, 26896, 32255]),
(5, [31, 482, 3652, 26898, 32152]),
(5, [31, 482, 3652, 26898, 32154]),
(5, [31, 482, 3652, 26900, 32152]),
(5, [31, 482, 3652, 26900, 32156]),
(5, [31, 482, 3652, 26904, 32152]),
(5, [31, 482, 3652, 26911, 27511]),
(5, [31, 482, 3652, 26911, 27519]),
(5, [31, 482, 3652, 26911, 27920]),
(5, [31, 482, 3652, 26911, 27935]),
(5, [31, 482, 3652, 26911, 30139])
],
#[
(5, [31, 482, 3652, 26911, 31743]),
(5, [31, 482, 3652, 26911, 32159]),
(5, [31, 482, 3652, 26911, 32250]),
(5, [31, 482, 3652, 26911, 32255]),
(5, [31, 482, 3652, 26960, 32152]),
(5, [31, 482, 3652, 26960, 32216]),
(5, [31, 482, 3652, 27122, 27920]),
(5, [31, 482, 3652, 27511, 32152]),
(5, [31, 482, 3652, 27920]),
(5, [31, 482, 3652, 27920, 27935]),
(5, [31, 482, 3652, 27920, 28146]),
(5, [31, 482, 3652, 27920, 28500]),
(5, [31, 482, 3652, 27920, 29115]),
(5, [31, 482, 3652, 27920, 31743]),
(5, [31, 482, 3652, 27920, 32152]),
(5, [31, 482, 3652, 27920, 32285])
],
#[
(5, [31, 482, 3652, 27920, 32736]),
(5, [31, 482, 3652, 27920, 32767]),
(5, [31, 482, 3652, 27924]),
(5, [31, 482, 3652, 27924, 32767]),
(5, [31, 482, 3652, 27928]),
(5, [31, 482, 3652, 27928, 32767]),
(5, [31, 482, 3652, 27935]),
(5, [31, 482, 3652, 27935, 32767]),
(5, [31, 482, 3652, 27984]),
(5, [31, 482, 3652, 27984, 32767]),
(5, [31, 482, 3652, 28500, 32159]),
(5, [31, 482, 3652, 28500, 32250]),
(5, [31, 482, 3652, 28511, 32152]),
(5, [31, 482, 3652, 28511, 32159]),
(5, [31, 482, 3652, 32024]),
(5, [31, 482, 3652, 32024, 32285])
],
#[
(5, [31, 482, 3652, 32024, 32767]),
(5, [31, 482, 3652, 32152, 32413]),
(5, [31, 482, 3652, 32152, 32511]),
(5, [31, 482, 3652, 32152, 32541]),
(5, [31, 482, 3652, 32152, 32639]),
(5, [31, 482, 3654, 5871, 13448]),
(5, [31, 482, 3654, 13448, 26896]),
(5, [31, 482, 3654, 13448, 26898]),
(5, [31, 482, 3654, 13448, 26911]),
(5, [31, 482, 3654, 13448, 32152]),
(5, [31, 482, 3654, 13450, 26896]),
(5, [31, 482, 3654, 13471, 26896]),
(5, [31, 482, 3654, 13802, 26896]),
(5, [31, 482, 3654, 19319, 26896]),
(5, [31, 482, 3654, 26896, 32152]),
(5, [31, 482, 3660, 5871, 13448])
],
#[
(5, [31, 482, 3660, 13448, 26896]),
(5, [31, 482, 3660, 13448, 26904]),
(5, [31, 482, 3660, 13448, 26911]),
(5, [31, 482, 3660, 13448, 32152]),
(5, [31, 482, 3660, 13802, 26896]),
(5, [31, 482, 3660, 19319, 26896]),
(5, [31, 482, 3660, 26896, 32152]),
(5, [31, 482, 3662, 13448, 26896]),
(5, [31, 482, 3662, 13802, 26896]),
(5, [31, 482, 3668, 5871, 13448]),
(5, [31, 482, 3668, 13448, 26896]),
(5, [31, 482, 3668, 13448, 32152]),
(5, [31, 482, 3668, 13464, 26896]),
(5, [31, 482, 3668, 13471, 26896]),
(5, [31, 482, 3668, 13802, 26896]),
(5, [31, 482, 3668, 19319, 26896])
],
#[
(5, [31, 482, 3668, 26896, 32152]),
(5, [31, 482, 3670, 13448, 26896]),
(5, [31, 482, 3676, 13448, 26896]),
(5, [31, 482, 3676, 13448, 32152]),
(5, [31, 482, 3676, 26896, 32152]),
(5, [31, 482, 3679, 16076, 32152]),
(5, [31, 482, 3679, 26896, 30139]),
(5, [31, 482, 3679, 28500, 32152]),
(5, [31, 482, 3780, 5871, 13448]),
(5, [31, 482, 3780, 13448, 26896]),
(5, [31, 482, 3780, 13448, 26911]),
(5, [31, 482, 3780, 13448, 27024]),
(5, [31, 482, 3780, 13448, 32152]),
(5, [31, 482, 3780, 13471, 26896]),
(5, [31, 482, 3780, 19319, 26896]),
(5, [31, 482, 3780, 26896, 32152])
],
#[
(5, [31, 482, 3780, 32152]),
(5, [31, 482, 3780, 32152, 32767]),
(5, [31, 482, 3782, 13448, 26896]),
(5, [31, 482, 3782, 13471, 26896]),
(5, [31, 482, 3788, 13448, 26896]),
(5, [31, 482, 3908, 5871, 13448]),
(5, [31, 482, 3908, 13448, 26896]),
(5, [31, 482, 3908, 13448, 26911]),
(5, [31, 482, 3908, 13448, 27122]),
(5, [31, 482, 3908, 13448, 32152]),
(5, [31, 482, 3908, 13471, 26896]),
(5, [31, 482, 3908, 13704, 26896]),
(5, [31, 482, 3908, 13802, 26896]),
(5, [31, 482, 3908, 19319, 26896]),
(5, [31, 482, 3908, 26896, 32152]),
(5, [31, 482, 3908, 32152])
],
#[
(5, [31, 482, 3908, 32152, 32767]),
(5, [31, 482, 3910, 13448, 26896]),
(5, [31, 482, 3910, 13448, 26911]),
(5, [31, 482, 3924, 13448, 26896]),
(5, [31, 482, 4036, 13448, 26896]),
(5, [31, 482, 4036, 13448, 32152]),
(5, [31, 482, 4036, 26896, 32152]),
(5, [31, 482, 4070, 13448, 26960]),
(5, [31, 482, 4070, 16076, 32152]),
(5, [31, 482, 4070, 26896, 30139]),
(5, [31, 482, 4070, 28500, 32152]),
(5, [31, 482, 4267, 5871, 13448]),
(5, [31, 482, 4267, 9216, 26896]),
(5, [31, 482, 4267, 13448, 26896]),
(5, [31, 482, 4267, 13448, 27122]),
(5, [31, 482, 4267, 13448, 31163])
],
#[
(5, [31, 482, 4267, 13448, 32152]),
(5, [31, 482, 4267, 13471, 26896]),
(5, [31, 482, 4267, 13483, 26896]),
(5, [31, 482, 4267, 13802, 26896]),
(5, [31, 482, 4267, 19319, 26896]),
(5, [31, 482, 4267, 26896, 32152]),
(5, [31, 482, 4267, 28500, 32152]),
(5, [31, 482, 4267, 32152]),
(5, [31, 482, 4267, 32152, 32767]),
(5, [31, 482, 5256, 5871, 7884]),
(5, [31, 482, 5256, 5871, 16076]),
(5, [31, 482, 5256, 5871, 28500]),
(5, [31, 482, 5256, 5871, 29115]),
(5, [31, 482, 5256, 7884, 26896]),
(5, [31, 482, 5256, 16076, 26896]),
(5, [31, 482, 5256, 26896, 28500])
],
#[
(5, [31, 482, 5256, 26896, 29115]),
(5, [31, 482, 5645, 13448, 28500]),
(5, [31, 482, 5836, 5871, 13448]),
(5, [31, 482, 5836, 13448, 26896]),
(5, [31, 482, 5856, 13448, 16076]),
(5, [31, 482, 5856, 13448, 29115]),
(5, [31, 482, 5871, 7884, 13448]),
(5, [31, 482, 5871, 9216, 28500]),
(5, [31, 482, 5871, 11844, 13448]),
(5, [31, 482, 5871, 13448, 14028]),
(5, [31, 482, 5871, 13448, 16691]),
(5, [31, 482, 5871, 13448, 28500]),
(5, [31, 482, 5871, 13448, 30139]),
(5, [31, 482, 5871, 13448, 31163]),
(5, [31, 482, 5871, 13448, 32732]),
(5, [31, 482, 5871, 13471, 28500])
],
#[
(5, [31, 482, 5871, 13471, 29115]),
(5, [31, 482, 5871, 13802, 28500]),
(5, [31, 482, 5871, 13802, 29115]),
(5, [31, 482, 5871, 16076, 19319]),
(5, [31, 482, 5871, 16076, 32152]),
(5, [31, 482, 5871, 19319, 28500]),
(5, [31, 482, 5871, 19319, 29115]),
(5, [31, 482, 5871, 26896, 30139]),
(5, [31, 482, 5871, 28500, 32152]),
(5, [31, 482, 5871, 29115, 30139]),
(5, [31, 482, 5871, 29115, 32152]),
(5, [31, 482, 5871, 30139]),
(5, [31, 482, 5871, 30139, 32767]),
(5, [31, 482, 5871, 32152, 32732]),
(5, [31, 482, 5887, 13448, 16076]),
(5, [31, 482, 5887, 13448, 29115])
],
#[
(5, [31, 482, 6127, 13448, 28500]),
(5, [31, 482, 7884, 13448, 26896]),
(5, [31, 482, 8192, 16076, 32152]),
(5, [31, 482, 8192, 26896, 30139]),
(5, [31, 482, 8192, 28500, 32152]),
(5, [31, 482, 9216, 11844, 26896]),
(5, [31, 482, 9216, 26896, 28500]),
(5, [31, 482, 9216, 26896, 29115]),
(5, [31, 482, 9216, 27122, 28500]),
(5, [31, 482, 9216, 27920, 28500]),
(5, [31, 482, 9216, 28500, 32152]),
(5, [31, 482, 9224, 26896, 28500]),
(5, [31, 482, 9236, 26896, 28500]),
(5, [31, 482, 9247, 26896, 28500]),
(5, [31, 482, 9344, 26896, 28500]),
(5, [31, 482, 9536, 26896, 28500])
],
#[
(5, [31, 482, 9698, 26896, 28500]),
(5, [31, 482, 10240, 16076, 32152]),
(5, [31, 482, 10496, 13448, 16076]),
(5, [31, 482, 11844, 13448, 26896]),
(5, [31, 482, 11844, 13448, 26911]),
(5, [31, 482, 11844, 13448, 32152]),
(5, [31, 482, 11844, 13471, 26896]),
(5, [31, 482, 11844, 13802, 26896]),
(5, [31, 482, 11844, 19319, 26896]),
(5, [31, 482, 11844, 26896, 32152]),
(5, [31, 482, 11852, 13448, 26896]),
(5, [31, 482, 11852, 13448, 26911]),
(5, [31, 482, 11860, 13448, 26896]),
(5, [31, 482, 11860, 13471, 26896]),
(5, [31, 482, 11972, 13448, 26896]),
(5, [31, 482, 12100, 13448, 26896])
]
],
#[
#[
(5, [31, 482, 12100, 13802, 26896]),
(5, [31, 482, 12424, 26896, 30139]),
(5, [31, 482, 12424, 29115, 32152]),
(5, [31, 482, 13320, 15948, 26896]),
(5, [31, 482, 13320, 26896, 28500]),
(5, [31, 482, 13320, 26896, 29115]),
(5, [31, 482, 13440, 16068, 26896]),
(5, [31, 482, 13440, 26896, 28500]),
(5, [31, 482, 13440, 26896, 29115]),
(5, [31, 482, 13448, 13483, 26896]),
(5, [31, 482, 13448, 13516, 26896]),
(5, [31, 482, 13448, 14028, 26896]),
(5, [31, 482, 13448, 14063, 16076]),
(5, [31, 482, 13448, 14063, 28500]),
(5, [31, 482, 13448, 14063, 29115]),
(5, [31, 482, 13448, 15948, 26896])
],
#[
(5, [31, 482, 13448, 16068, 26896]),
(5, [31, 482, 13448, 16076, 18704]),
(5, [31, 482, 13448, 16076, 26880]),
(5, [31, 482, 13448, 16076, 26896]),
(5, [31, 482, 13448, 16076, 26898]),
(5, [31, 482, 13448, 16076, 26900]),
(5, [31, 482, 13448, 16076, 26904]),
(5, [31, 482, 13448, 16076, 26908]),
(5, [31, 482, 13448, 16076, 26960]),
(5, [31, 482, 13448, 16076, 27024]),
(5, [31, 482, 13448, 16076, 27088]),
(5, [31, 482, 13448, 16076, 27920]),
(5, [31, 482, 13448, 16076, 32159]),
(5, [31, 482, 13448, 16078, 26896]),
(5, [31, 482, 13448, 16092, 26896]),
(5, [31, 482, 13448, 16332, 26896])
],
#[
(5, [31, 482, 13448, 16691, 26896]),
(5, [31, 482, 13448, 16691, 26911]),
(5, [31, 482, 13448, 16691, 32152]),
(5, [31, 482, 13448, 18704, 20308]),
(5, [31, 482, 13448, 18704, 28500]),
(5, [31, 482, 13448, 18704, 29115]),
(5, [31, 482, 13448, 19284, 26896]),
(5, [31, 482, 13448, 20308, 26896]),
(5, [31, 482, 13448, 20923, 26896]),
(5, [31, 482, 13448, 24848, 31163]),
(5, [31, 482, 13448, 26640, 28500]),
(5, [31, 482, 13448, 26880, 28484]),
(5, [31, 482, 13448, 26880, 29115]),
(5, [31, 482, 13448, 26896, 26931]),
(5, [31, 482, 13448, 26896, 26964]),
(5, [31, 482, 13448, 26896, 27476])
],
#[
(5, [31, 482, 13448, 26896, 28244]),
(5, [31, 482, 13448, 26896, 28484]),
(5, [31, 482, 13448, 26896, 28500]),
(5, [31, 482, 13448, 26896, 28502]),
(5, [31, 482, 13448, 26896, 28508]),
(5, [31, 482, 13448, 26896, 28628]),
(5, [31, 482, 13448, 26896, 28859]),
(5, [31, 482, 13448, 26896, 28987]),
(5, [31, 482, 13448, 26896, 29099]),
(5, [31, 482, 13448, 26896, 29107]),
(5, [31, 482, 13448, 26896, 29113]),
(5, [31, 482, 13448, 26896, 29115]),
(5, [31, 482, 13448, 26896, 30139]),
(5, [31, 482, 13448, 26896, 31163]),
(5, [31, 482, 13448, 26896, 32187]),
(5, [31, 482, 13448, 26896, 32324])
],
#[
(5, [31, 482, 13448, 26896, 32699]),
(5, [31, 482, 13448, 26896, 32732]),
(5, [31, 482, 13448, 26898, 28500]),
(5, [31, 482, 13448, 26898, 28502]),
(5, [31, 482, 13448, 26898, 29115]),
(5, [31, 482, 13448, 26900, 29115]),
(5, [31, 482, 13448, 26904, 28500]),
(5, [31, 482, 13448, 26904, 28508]),
(5, [31, 482, 13448, 26904, 29115]),
(5, [31, 482, 13448, 26907, 29115]),
(5, [31, 482, 13448, 26911, 30139]),
(5, [31, 482, 13448, 26911, 31163]),
(5, [31, 482, 13448, 26960, 28500]),
(5, [31, 482, 13448, 26960, 29115]),
(5, [31, 482, 13448, 27024, 28500]),
(5, [31, 482, 13448, 27024, 28628])
],
#[
(5, [31, 482, 13448, 27024, 29115]),
(5, [31, 482, 13448, 27122, 32732]),
(5, [31, 482, 13448, 27920, 28500]),
(5, [31, 482, 13448, 27920, 29115]),
(5, [31, 482, 13448, 28500, 31163]),
(5, [31, 482, 13448, 28500, 32250]),
(5, [31, 482, 13448, 29115, 31128]),
(5, [31, 482, 13448, 29115, 32159]),
(5, [31, 482, 13448, 30139, 32152]),
(5, [31, 482, 13448, 31163, 32152]),
(5, [31, 482, 13448, 32152, 32187]),
(5, [31, 482, 13448, 32152, 32732]),
(5, [31, 482, 13448, 32250, 32732]),
(5, [31, 482, 13450, 16076, 26896]),
(5, [31, 482, 13450, 16078, 26896]),
(5, [31, 482, 13450, 26896, 28500])
],
#[
(5, [31, 482, 13450, 26896, 29115]),
(5, [31, 482, 13452, 26896, 28500]),
(5, [31, 482, 13452, 26896, 29115]),
(5, [31, 482, 13464, 16076, 26896]),
(5, [31, 482, 13464, 16092, 26896]),
(5, [31, 482, 13464, 26896, 28500]),
(5, [31, 482, 13464, 26896, 29115]),
(5, [31, 482, 13467, 26896, 29115]),
(5, [31, 482, 13468, 26896, 28500]),
(5, [31, 482, 13471, 16076, 32152]),
(5, [31, 482, 13471, 26896, 30139]),
(5, [31, 482, 13471, 26896, 31163]),
(5, [31, 482, 13471, 26911, 29115]),
(5, [31, 482, 13471, 27122, 28500]),
(5, [31, 482, 13471, 28500, 32152]),
(5, [31, 482, 13471, 29115, 32152])
],
#[
(5, [31, 482, 13471, 29115, 32159]),
(5, [31, 482, 13471, 32152, 32732]),
(5, [31, 482, 13483, 26896]),
(5, [31, 482, 13483, 26896, 28500]),
(5, [31, 482, 13483, 26896, 32767]),
(5, [31, 482, 13512, 26896, 28500]),
(5, [31, 482, 13512, 26896, 29115]),
(5, [31, 482, 13704, 16076, 26896]),
(5, [31, 482, 13704, 16332, 26896]),
(5, [31, 482, 13704, 26896, 28500]),
(5, [31, 482, 13704, 26896, 29115]),
(5, [31, 482, 13738, 26896, 29115]),
(5, [31, 482, 13768, 26896, 28500]),
(5, [31, 482, 13802, 16076, 32152]),
(5, [31, 482, 13802, 26896, 30139]),
(5, [31, 482, 13802, 26896, 31163])
],
#[
(5, [31, 482, 13802, 26911, 29115]),
(5, [31, 482, 13802, 27122, 28500]),
(5, [31, 482, 13802, 28500, 32152]),
(5, [31, 482, 13802, 28500, 32250]),
(5, [31, 482, 13823, 26896, 28500]),
(5, [31, 482, 13823, 26896, 29115]),
(5, [31, 482, 15496, 16076, 26896]),
(5, [31, 482, 15496, 16076, 32152]),
(5, [31, 482, 15496, 26896, 28500]),
(5, [31, 482, 15496, 26896, 29115]),
(5, [31, 482, 16076, 16095, 32152]),
(5, [31, 482, 16076, 16366, 32152]),
(5, [31, 482, 16076, 16691, 32152]),
(5, [31, 482, 16076, 18704, 19319]),
(5, [31, 482, 16076, 19319, 26896]),
(5, [31, 482, 16076, 19319, 26911])
],
#[
(5, [31, 482, 16076, 19319, 32152]),
(5, [31, 482, 16076, 26896, 27511]),
(5, [31, 482, 16076, 26896, 30139]),
(5, [31, 482, 16076, 26911, 32152]),
(5, [31, 482, 16076, 27122, 32152]),
(5, [31, 482, 16076, 28500, 32152]),
(5, [31, 482, 16076, 29115, 32152]),
(5, [31, 482, 16076, 32152, 32159]),
(5, [31, 482, 16076, 32152, 32250]),
(5, [31, 482, 16076, 32152, 32285]),
(5, [31, 482, 16076, 32152, 32732]),
(5, [31, 482, 16076, 32152, 32736]),
(5, [31, 482, 16076, 32152, 32767]),
(5, [31, 482, 16691, 19319, 26896]),
(5, [31, 482, 16691, 26896, 30139]),
(5, [31, 482, 16691, 26896, 32152])
],
#[
(5, [31, 482, 16691, 32152]),
(5, [31, 482, 16691, 32152, 32767]),
(5, [31, 482, 18704, 19319, 20308]),
(5, [31, 482, 18704, 19319, 28500]),
(5, [31, 482, 18704, 19319, 29115]),
(5, [31, 482, 18965, 26896, 28500]),
(5, [31, 482, 18965, 26896, 29115]),
(5, [31, 482, 19284, 19319, 26896]),
(5, [31, 482, 19284, 26896]),
(5, [31, 482, 19284, 26896, 28500]),
(5, [31, 482, 19284, 26896, 32767]),
(5, [31, 482, 19296, 26896, 28500]),
(5, [31, 482, 19296, 26896, 29115]),
(5, [31, 482, 19319, 20308, 26896]),
(5, [31, 482, 19319, 26896, 27476]),
(5, [31, 482, 19319, 26896, 30139])
],
#[
(5, [31, 482, 19319, 26896, 31163]),
(5, [31, 482, 19319, 26896, 32732]),
(5, [31, 482, 19319, 26911, 29115]),
(5, [31, 482, 19319, 27122, 28500]),
(5, [31, 482, 19319, 28500, 32152]),
(5, [31, 482, 19319, 29115, 32152]),
(5, [31, 482, 19319, 32152, 32732]),
(5, [31, 482, 19327, 26896, 28500]),
(5, [31, 482, 19327, 26896, 29115]),
(5, [31, 482, 19447, 26896, 28500]),
(5, [31, 482, 19447, 26896, 29115]),
(5, [31, 482, 23551, 26896, 28500]),
(5, [31, 482, 24848, 26896, 30139]),
(5, [31, 482, 24848, 29115, 32152]),
(5, [31, 482, 26896, 26911, 30139]),
(5, [31, 482, 26896, 27122, 30139])
],
#[
(5, [31, 482, 26896, 27476]),
(5, [31, 482, 26896, 27476, 32767]),
(5, [31, 482, 26896, 27511, 28500]),
(5, [31, 482, 26896, 27511, 29115]),
(5, [31, 482, 26896, 27920, 28500]),
(5, [31, 482, 26896, 27920, 29115]),
(5, [31, 482, 26896, 28500, 30139]),
(5, [31, 482, 26896, 28500, 31743]),
(5, [31, 482, 26896, 28500, 32159]),
(5, [31, 482, 26896, 28500, 32250]),
(5, [31, 482, 26896, 29115, 30104]),
(5, [31, 482, 26896, 29115, 30139]),
(5, [31, 482, 26896, 29115, 30143]),
(5, [31, 482, 26896, 29115, 30203]),
(5, [31, 482, 26896, 29115, 31743]),
(5, [31, 482, 26896, 29115, 32159])
],
#[
(5, [31, 482, 26896, 29115, 32187]),
(5, [31, 482, 26896, 29115, 32250]),
(5, [31, 482, 26896, 29119, 30139]),
(5, [31, 482, 26896, 29179, 30139]),
(5, [31, 482, 26896, 30139]),
(5, [31, 482, 26896, 30139, 30143]),
(5, [31, 482, 26896, 30139, 30203]),
(5, [31, 482, 26896, 30139, 31163]),
(5, [31, 482, 26896, 30139, 32152]),
(5, [31, 482, 26896, 30139, 32187]),
(5, [31, 482, 26896, 30139, 32285]),
(5, [31, 482, 26896, 30139, 32736]),
(5, [31, 482, 26896, 30139, 32767]),
(5, [31, 482, 26896, 31163, 32152]),
(5, [31, 482, 26896, 31163, 32187]),
(5, [31, 482, 26896, 32152, 32187])
],
#[
(5, [31, 482, 26896, 32152, 32732]),
(5, [31, 482, 26896, 32187]),
(5, [31, 482, 26896, 32187, 32767]),
(5, [31, 482, 26911, 28500, 32152]),
(5, [31, 482, 26911, 29115, 30139]),
(5, [31, 482, 26911, 29115, 32152]),
(5, [31, 482, 26911, 29115, 32159]),
(5, [31, 482, 26911, 30139]),
(5, [31, 482, 26911, 30139, 32767]),
(5, [31, 482, 26911, 32152, 32732]),
(5, [31, 482, 27122, 28500, 32152]),
(5, [31, 482, 27122, 28500, 32250]),
(5, [31, 482, 27920, 28500]),
(5, [31, 482, 27920, 28500, 32152]),
(5, [31, 482, 27920, 28500, 32767]),
(5, [31, 482, 27920, 29115])
],
#[
(5, [31, 482, 27920, 29115, 32767]),
(5, [31, 482, 28500, 28511, 32152]),
(5, [31, 482, 28500, 28662, 32152]),
(5, [31, 482, 28500, 29115, 32152]),
(5, [31, 482, 28500, 32152, 32159]),
(5, [31, 482, 28500, 32152, 32250]),
(5, [31, 482, 28500, 32152, 32285]),
(5, [31, 482, 28500, 32152, 32732]),
(5, [31, 482, 28500, 32152, 32736]),
(5, [31, 482, 28500, 32152, 32767]),
(5, [31, 482, 28500, 32250]),
(5, [31, 482, 28500, 32250, 32767]),
(5, [31, 486, 1024, 3652, 26896]),
(5, [31, 486, 3652, 5871, 13448]),
(5, [31, 486, 3652, 13448, 26896]),
(5, [31, 486, 3652, 13448, 26900])
]
],
#[
#[
(5, [31, 486, 3652, 13448, 26911]),
(5, [31, 486, 3652, 13448, 32152]),
(5, [31, 486, 3652, 13452, 26896]),
(5, [31, 486, 3652, 13471, 26896]),
(5, [31, 486, 3652, 13802, 26896]),
(5, [31, 486, 3652, 13806, 26896]),
(5, [31, 486, 3652, 19319, 26896]),
(5, [31, 486, 3652, 26896, 32152]),
(5, [31, 486, 13448, 16076, 26896]),
(5, [31, 486, 13448, 26896, 28500]),
(5, [31, 486, 13448, 26896, 29115]),
(5, [31, 490, 1024, 3652, 26896]),
(5, [31, 490, 3652, 5871, 13448]),
(5, [31, 490, 3652, 13448, 26896]),
(5, [31, 490, 3652, 13448, 26904]),
(5, [31, 490, 3652, 13448, 26911])
],
#[
(5, [31, 490, 3652, 13448, 32152]),
(5, [31, 490, 3652, 13471, 26896]),
(5, [31, 490, 3652, 13802, 26896]),
(5, [31, 490, 3652, 19319, 26896]),
(5, [31, 490, 3652, 26896, 32152]),
(5, [31, 490, 3660, 13448, 26896]),
(5, [31, 490, 13448, 16076, 26896]),
(5, [31, 490, 13448, 26896, 28500]),
(5, [31, 490, 13448, 26896, 29115]),
(5, [31, 494, 3652, 13448, 26896]),
(5, [31, 494, 13448, 16076, 26896]),
(5, [31, 495, 3652, 5871, 13448]),
(5, [31, 495, 3652, 13448, 26896]),
(5, [31, 498, 1024, 3652, 26896]),
(5, [31, 498, 3652, 5871, 13448]),
(5, [31, 498, 3652, 13448, 26896])
],
#[
(5, [31, 498, 3652, 13448, 26911]),
(5, [31, 498, 3652, 13448, 32152]),
(5, [31, 498, 3652, 13464, 26896]),
(5, [31, 498, 3652, 13471, 26896]),
(5, [31, 498, 3652, 13802, 26896]),
(5, [31, 498, 3652, 13818, 26896]),
(5, [31, 498, 3652, 19319, 26896]),
(5, [31, 498, 3652, 26896, 32152]),
(5, [31, 498, 3668, 13448, 26896]),
(5, [31, 498, 13448, 16076, 26896]),
(5, [31, 498, 13448, 26896, 28500]),
(5, [31, 498, 13448, 26896, 29115]),
(5, [31, 502, 3652, 13448, 26896]),
(5, [31, 502, 13448, 26896, 28500]),
(5, [31, 503, 3652, 13448, 26896]),
(5, [31, 503, 3652, 19319, 26896])
],
#[
(5, [31, 506, 3652, 13448, 26896]),
(5, [31, 506, 3652, 13448, 32152]),
(5, [31, 506, 3652, 26896, 32152]),
(5, [31, 507, 3652, 13448, 26896]),
(5, [31, 507, 13448, 26896, 29115]),
(5, [31, 511, 615, 3652, 13448]),
(5, [31, 511, 615, 3652, 26896]),
(5, [31, 511, 1024, 3652, 5871]),
(5, [31, 511, 1024, 3652, 26911]),
(5, [31, 511, 1024, 3652, 27920]),
(5, [31, 511, 1024, 26896, 28500]),
(5, [31, 511, 1024, 26896, 29115]),
(5, [31, 511, 1028, 3652, 26896]),
(5, [31, 511, 1032, 3652, 26896]),
(5, [31, 511, 1055, 3652, 26896]),
(5, [31, 511, 1088, 3652, 26896])
],
#[
(5, [31, 511, 1092, 3652, 26896]),
(5, [31, 511, 1092, 13448, 26896]),
(5, [31, 511, 1092, 13823, 26896]),
(5, [31, 511, 1152, 3652, 26896]),
(5, [31, 511, 1160, 3652, 26896]),
(5, [31, 511, 1506, 3652, 26896]),
(5, [31, 511, 1535, 3652, 26896]),
(5, [31, 511, 1604, 5871, 13448]),
(5, [31, 511, 1604, 13448, 26896]),
(5, [31, 511, 2116, 13448, 26896]),
(5, [31, 511, 2304, 3652, 13448]),
(5, [31, 511, 2320, 3652, 13448]),
(5, [31, 511, 2628, 3652, 26896]),
(5, [31, 511, 2628, 13448, 26896]),
(5, [31, 511, 2628, 19319, 26896]),
(5, [31, 511, 2628, 26896])
],
#[
(5, [31, 511, 2628, 26896, 32767]),
(5, [31, 511, 3072, 3652, 26896]),
(5, [31, 511, 3652, 5256, 5871]),
(5, [31, 511, 3652, 5256, 26896]),
(5, [31, 511, 3652, 5856, 13448]),
(5, [31, 511, 3652, 5871, 13471]),
(5, [31, 511, 3652, 5871, 13802]),
(5, [31, 511, 3652, 5871, 13823]),
(5, [31, 511, 3652, 5871, 19319]),
(5, [31, 511, 3652, 5871, 32152]),
(5, [31, 511, 3652, 5887, 13448]),
(5, [31, 511, 3652, 9216, 26896]),
(5, [31, 511, 3652, 13312, 26896]),
(5, [31, 511, 3652, 13320, 26896]),
(5, [31, 511, 3652, 13440, 26896]),
(5, [31, 511, 3652, 13448, 14063])
],
#[
(5, [31, 511, 3652, 13448, 18704]),
(5, [31, 511, 3652, 13448, 26880]),
(5, [31, 511, 3652, 13448, 26896]),
(5, [31, 511, 3652, 13448, 26898]),
(5, [31, 511, 3652, 13448, 26900]),
(5, [31, 511, 3652, 13448, 26904]),
(5, [31, 511, 3652, 13448, 26960]),
(5, [31, 511, 3652, 13448, 26964]),
(5, [31, 511, 3652, 13448, 27024]),
(5, [31, 511, 3652, 13448, 27032]),
(5, [31, 511, 3652, 13448, 27920]),
(5, [31, 511, 3652, 13448, 32159]),
(5, [31, 511, 3652, 13450, 26896]),
(5, [31, 511, 3652, 13452, 26896]),
(5, [31, 511, 3652, 13464, 26896]),
(5, [31, 511, 3652, 13471, 26911])
],
#[
(5, [31, 511, 3652, 13471, 32152]),
(5, [31, 511, 3652, 13471, 32159]),
(5, [31, 511, 3652, 13512, 26896]),
(5, [31, 511, 3652, 13516, 26896]),
(5, [31, 511, 3652, 13704, 26896]),
(5, [31, 511, 3652, 13720, 26896]),
(5, [31, 511, 3652, 13802, 26911]),
(5, [31, 511, 3652, 13823, 26896]),
(5, [31, 511, 3652, 13823, 26911]),
(5, [31, 511, 3652, 15496, 26896]),
(5, [31, 511, 3652, 16076, 32152]),
(5, [31, 511, 3652, 18704, 19319]),
(5, [31, 511, 3652, 18944, 26896]),
(5, [31, 511, 3652, 18965, 26896]),
(5, [31, 511, 3652, 19296, 26896]),
(5, [31, 511, 3652, 19319, 26911])
],
#[
(5, [31, 511, 3652, 19319, 32152]),
(5, [31, 511, 3652, 19327, 26896]),
(5, [31, 511, 3652, 19447, 26896]),
(5, [31, 511, 3652, 19455, 26896]),
(5, [31, 511, 3652, 26896, 27511]),
(5, [31, 511, 3652, 26896, 27920]),
(5, [31, 511, 3652, 26896, 30139]),
(5, [31, 511, 3652, 26896, 31743]),
(5, [31, 511, 3652, 26896, 32159]),
(5, [31, 511, 3652, 26896, 32250]),
(5, [31, 511, 3652, 26896, 32255]),
(5, [31, 511, 3652, 26911, 32152]),
(5, [31, 511, 3652, 26911, 32159]),
(5, [31, 511, 3652, 27920]),
(5, [31, 511, 3652, 27920, 32767]),
(5, [31, 511, 3652, 28500, 32152])
],
#[
(5, [31, 511, 3660, 13448, 26896]),
(5, [31, 511, 3668, 13448, 26896]),
(5, [31, 511, 3780, 13448, 26896]),
(5, [31, 511, 3788, 13448, 26896]),
(5, [31, 511, 3908, 13448, 26896]),
(5, [31, 511, 3924, 13448, 26896]),
(5, [31, 511, 4267, 13448, 26896]),
(5, [31, 511, 5871, 13448, 16076]),
(5, [31, 511, 5871, 13448, 28500]),
(5, [31, 511, 5871, 13448, 29115]),
(5, [31, 511, 9216, 26896, 28500]),
(5, [31, 511, 11844, 13448, 26896]),
(5, [31, 511, 13448, 13516, 26896]),
(5, [31, 511, 13448, 16076, 26911]),
(5, [31, 511, 13448, 16076, 32152]),
(5, [31, 511, 13448, 16691, 26896])
],
#[
(5, [31, 511, 13448, 26896, 26964]),
(5, [31, 511, 13448, 26896, 30139]),
(5, [31, 511, 13448, 26896, 31163]),
(5, [31, 511, 13448, 26896, 32324]),
(5, [31, 511, 13448, 26896, 32699]),
(5, [31, 511, 13448, 26896, 32732]),
(5, [31, 511, 13448, 26911, 29115]),
(5, [31, 511, 13448, 27122, 28500]),
(5, [31, 511, 13448, 28500, 32152]),
(5, [31, 511, 13448, 29115, 32152]),
(5, [31, 511, 13448, 32152, 32732]),
(5, [31, 511, 13471, 26896, 28500]),
(5, [31, 511, 13471, 26896, 29115]),
(5, [31, 511, 13802, 26896, 28500]),
(5, [31, 511, 13802, 26896, 29115]),
(5, [31, 511, 13823, 26896, 28500])
],
#[
(5, [31, 511, 13823, 26896, 29115]),
(5, [31, 511, 16076, 19319, 26896]),
(5, [31, 511, 16076, 26896, 32152]),
(5, [31, 511, 16076, 32152]),
(5, [31, 511, 16076, 32152, 32767]),
(5, [31, 511, 19319, 26896, 28500]),
(5, [31, 511, 19319, 26896, 29115]),
(5, [31, 511, 26896, 28500, 32152]),
(5, [31, 511, 26896, 29115, 30139]),
(5, [31, 511, 26896, 29115, 32152]),
(5, [31, 511, 26896, 30139]),
(5, [31, 511, 26896, 30139, 32767]),
(5, [31, 511, 26896, 32152, 32732]),
(5, [31, 511, 28500, 32152]),
(5, [31, 511, 28500, 32152, 32767]),
(5, [31, 517, 3652, 26896, 27122])
],
#[
(5, [31, 615, 3652, 13448, 32285]),
(5, [31, 615, 3652, 26896, 27122]),
(5, [31, 615, 3652, 26896, 32285]),
(5, [31, 1024, 1506, 3652, 5871]),
(5, [31, 1024, 1506, 3652, 26896]),
(5, [31, 1024, 1506, 3652, 26911]),
(5, [31, 1024, 1506, 3652, 27920]),
(5, [31, 1024, 1506, 26896, 28500]),
(5, [31, 1024, 1506, 26896, 29115]),
(5, [31, 1024, 1535, 3652, 26896]),
(5, [31, 1024, 2530, 3652, 26896]),
(5, [31, 1024, 3652, 5645, 26896]),
(5, [31, 1024, 3652, 5871, 27122]),
(5, [31, 1024, 3652, 5871, 32285]),
(5, [31, 1024, 3652, 8674, 26896]),
(5, [31, 1024, 3652, 26896, 27135])
],
#[
(5, [31, 1024, 3652, 26896, 28146]),
(5, [31, 1024, 3652, 26896, 31261]),
(5, [31, 1024, 3652, 26896, 32256]),
(5, [31, 1024, 3652, 26896, 32285]),
(5, [31, 1024, 3652, 26896, 32287]),
(5, [31, 1024, 3652, 26896, 32541]),
(5, [31, 1024, 3652, 26911, 27122]),
(5, [31, 1024, 3652, 26911, 27135]),
(5, [31, 1024, 3652, 26911, 32285]),
(5, [31, 1024, 3652, 27122, 27920]),
(5, [31, 1024, 3652, 27122, 28500]),
(5, [31, 1024, 3652, 27920, 28146]),
(5, [31, 1024, 3652, 27920, 32285]),
(5, [31, 1024, 13448, 27122, 28500]),
(5, [31, 1024, 26896, 27122, 28500]),
(5, [31, 1024, 26896, 27122, 29115])
],
#[
(5, [31, 1024, 26896, 28500, 32285]),
(5, [31, 1024, 26896, 29115, 32285]),
(5, [31, 1024, 27122, 28500]),
(5, [31, 1024, 27122, 28500, 32767]),
(5, [31, 1028, 1510, 3652, 26896]),
(5, [31, 1028, 3652, 26896, 27122]),
(5, [31, 1028, 3652, 26896, 32285]),
(5, [31, 1032, 1514, 3652, 26896]),
(5, [31, 1032, 3652, 26896, 27122]),
(5, [31, 1032, 3652, 26896, 32285]),
(5, [31, 1055, 1506, 3652, 26896]),
(5, [31, 1055, 1535, 3652, 26896]),
(5, [31, 1055, 3652, 26896, 27122]),
(5, [31, 1055, 3652, 26896, 32285]),
(5, [31, 1088, 1506, 3652, 26896]),
(5, [31, 1088, 3652, 4070, 26896])
],
#[
(5, [31, 1088, 3652, 26896, 27122]),
(5, [31, 1088, 3652, 26896, 32285]),
(5, [31, 1088, 4070, 13802, 26896]),
(5, [31, 1152, 1506, 3652, 26896]),
(5, [31, 1152, 3652, 26896, 27122]),
(5, [31, 1152, 3652, 26896, 32285]),
(5, [31, 1506, 1535, 3652, 26896]),
(5, [31, 1506, 2048, 3652, 26896]),
(5, [31, 1506, 3652, 3679, 26896]),
(5, [31, 1506, 3652, 4070, 26896]),
(5, [31, 1506, 3652, 5871]),
(5, [31, 1506, 3652, 5871, 13448]),
(5, [31, 1506, 3652, 5871, 26896]),
(5, [31, 1506, 3652, 5871, 32767]),
(5, [31, 1506, 3652, 8192, 26896]),
(5, [31, 1506, 3652, 13448, 26896])
]
],
#[
#[
(5, [31, 1506, 3652, 13448, 26911]),
(5, [31, 1506, 3652, 13448, 27920]),
(5, [31, 1506, 3652, 13448, 32152]),
(5, [31, 1506, 3652, 13471, 26896]),
(5, [31, 1506, 3652, 13802, 26896]),
(5, [31, 1506, 3652, 16076, 26896]),
(5, [31, 1506, 3652, 19319, 26896]),
(5, [31, 1506, 3652, 26896]),
(5, [31, 1506, 3652, 26896, 26911]),
(5, [31, 1506, 3652, 26896, 27122]),
(5, [31, 1506, 3652, 26896, 27920]),
(5, [31, 1506, 3652, 26896, 28146]),
(5, [31, 1506, 3652, 26896, 28500]),
(5, [31, 1506, 3652, 26896, 29115]),
(5, [31, 1506, 3652, 26896, 31261]),
(5, [31, 1506, 3652, 26896, 31743])
],
#[
(5, [31, 1506, 3652, 26896, 32152]),
(5, [31, 1506, 3652, 26896, 32285]),
(5, [31, 1506, 3652, 26896, 32736]),
(5, [31, 1506, 3652, 26896, 32767]),
(5, [31, 1506, 3652, 26911]),
(5, [31, 1506, 3652, 26911, 32767]),
(5, [31, 1506, 3652, 27920]),
(5, [31, 1506, 3652, 27920, 32767]),
(5, [31, 1506, 13448, 26896, 28500]),
(5, [31, 1506, 13448, 26896, 29115]),
(5, [31, 1506, 26896, 28500]),
(5, [31, 1506, 26896, 28500, 32767]),
(5, [31, 1506, 26896, 29115]),
(5, [31, 1506, 26896, 29115, 32767]),
(5, [31, 1510, 3652, 13448, 26896]),
(5, [31, 1510, 3652, 13471, 26896])
],
#[
(5, [31, 1510, 3652, 26896]),
(5, [31, 1510, 3652, 26896, 32767]),
(5, [31, 1514, 3652, 3679, 26896]),
(5, [31, 1514, 3652, 13448, 26896]),
(5, [31, 1514, 3652, 26896]),
(5, [31, 1514, 3652, 26896, 32767]),
(5, [31, 1535, 3652, 13448, 26896]),
(5, [31, 1535, 3652, 26896]),
(5, [31, 1535, 3652, 26896, 32767]),
(5, [31, 1604, 5871, 13448, 27122]),
(5, [31, 1604, 5871, 13448, 32285]),
(5, [31, 1604, 13448, 26896, 27122]),
(5, [31, 1604, 13448, 26896, 32285]),
(5, [31, 2048, 3652, 13448, 32541]),
(5, [31, 2048, 13448, 27122, 28500]),
(5, [31, 2112, 13448, 27122, 28500])
],
#[
(5, [31, 2116, 13448, 26896, 27122]),
(5, [31, 2116, 13448, 26896, 27135]),
(5, [31, 2116, 13448, 26911, 27135]),
(5, [31, 2304, 2530, 3652, 13448]),
(5, [31, 2304, 3652, 4070, 13802]),
(5, [31, 2304, 3652, 13448, 32285]),
(5, [31, 2530, 3652, 5871, 13448]),
(5, [31, 2530, 3652, 13448, 26896]),
(5, [31, 2530, 3652, 13448, 26911]),
(5, [31, 2530, 3652, 13448, 28500]),
(5, [31, 2530, 3652, 13448, 32152]),
(5, [31, 2530, 3652, 13471, 26896]),
(5, [31, 2530, 3652, 13802, 26896]),
(5, [31, 2530, 3652, 15496, 26896]),
(5, [31, 2530, 3652, 15850, 26896]),
(5, [31, 2530, 3652, 19319, 26896])
],
#[
(5, [31, 2530, 3652, 26896, 32152]),
(5, [31, 2530, 13448, 16076, 26896]),
(5, [31, 2530, 13448, 26896, 28500]),
(5, [31, 2530, 13448, 26896, 29115]),
(5, [31, 2534, 3652, 13448, 26896]),
(5, [31, 2534, 3652, 13448, 26911]),
(5, [31, 2546, 3652, 13448, 26896]),
(5, [31, 2559, 3652, 13448, 26896]),
(5, [31, 2628, 3652, 26896, 27122]),
(5, [31, 2628, 3652, 26896, 32285]),
(5, [31, 2628, 13448, 26896, 27122]),
(5, [31, 2628, 13448, 26896, 32285]),
(5, [31, 2628, 19319, 26896, 27122]),
(5, [31, 2628, 19319, 26896, 32285]),
(5, [31, 2628, 26896, 27122]),
(5, [31, 2628, 26896, 27122, 32767])
],
#[
(5, [31, 2628, 26896, 32285]),
(5, [31, 2628, 26896, 32285, 32767]),
(5, [31, 3072, 3554, 3652, 26896]),
(5, [31, 3072, 3652, 26896, 27122]),
(5, [31, 3072, 3652, 26896, 32285]),
(5, [31, 3136, 3652, 26896, 27122]),
(5, [31, 3554, 3652, 13448, 26896]),
(5, [31, 3554, 3652, 13448, 32152]),
(5, [31, 3554, 3652, 26896]),
(5, [31, 3554, 3652, 26896, 32152]),
(5, [31, 3554, 3652, 26896, 32767]),
(5, [31, 3588, 3652, 13320, 26896]),
(5, [31, 3588, 13448, 26896, 32349]),
(5, [31, 3652, 4070, 5871, 13802]),
(5, [31, 3652, 4070, 13448, 26960]),
(5, [31, 3652, 4070, 13512, 26896])
],
#[
(5, [31, 3652, 4070, 13802, 26911]),
(5, [31, 3652, 4070, 13823, 26896]),
(5, [31, 3652, 4070, 18965, 26896]),
(5, [31, 3652, 4070, 26896, 32250]),
(5, [31, 3652, 4095, 13802, 26896]),
(5, [31, 3652, 4095, 13823, 26896]),
(5, [31, 3652, 4267, 13448, 27122]),
(5, [31, 3652, 5128, 5645, 26896]),
(5, [31, 3652, 5128, 26896, 27122]),
(5, [31, 3652, 5256, 5871, 27122]),
(5, [31, 3652, 5256, 5871, 32285]),
(5, [31, 3652, 5256, 26896, 27122]),
(5, [31, 3652, 5256, 26896, 32285]),
(5, [31, 3652, 5632, 13448, 26896]),
(5, [31, 3652, 5632, 13448, 26911]),
(5, [31, 3652, 5645, 5871, 13448])
],
#[
(5, [31, 3652, 5645, 13448, 26896]),
(5, [31, 3652, 5645, 13448, 26911]),
(5, [31, 3652, 5645, 13448, 28500]),
(5, [31, 3652, 5645, 13448, 32541]),
(5, [31, 3652, 5645, 13471, 26896]),
(5, [31, 3652, 5645, 13802, 26896]),
(5, [31, 3652, 5645, 19319, 26896]),
(5, [31, 3652, 5645, 26896, 32152]),
(5, [31, 3652, 5645, 26896, 32250]),
(5, [31, 3652, 5663, 13448, 26896]),
(5, [31, 3652, 5856, 13448, 27122]),
(5, [31, 3652, 5856, 13448, 27135]),
(5, [31, 3652, 5856, 13448, 32285]),
(5, [31, 3652, 5871, 8674, 13448]),
(5, [31, 3652, 5871, 13320, 32285]),
(5, [31, 3652, 5871, 13448, 27122])
],
#[
(5, [31, 3652, 5871, 13448, 27135]),
(5, [31, 3652, 5871, 13448, 32256]),
(5, [31, 3652, 5871, 13448, 32287]),
(5, [31, 3652, 5871, 13448, 32541]),
(5, [31, 3652, 5871, 13471, 27122]),
(5, [31, 3652, 5871, 13471, 32285]),
(5, [31, 3652, 5871, 13802, 27122]),
(5, [31, 3652, 5871, 13802, 32285]),
(5, [31, 3652, 5871, 19319, 27122]),
(5, [31, 3652, 5871, 19319, 32285]),
(5, [31, 3652, 5871, 27122, 32152]),
(5, [31, 3652, 5871, 27122, 32250]),
(5, [31, 3652, 5871, 32152, 32285]),
(5, [31, 3652, 5887, 13448, 27122]),
(5, [31, 3652, 5887, 13448, 32285]),
(5, [31, 3652, 7919, 13448, 27122])
],
#[
(5, [31, 3652, 8448, 13802, 27122]),
(5, [31, 3652, 8674, 13448, 26896]),
(5, [31, 3652, 8674, 13448, 26911]),
(5, [31, 3652, 8674, 13471, 26896]),
(5, [31, 3652, 8674, 13802, 26896]),
(5, [31, 3652, 8674, 19319, 26896]),
(5, [31, 3652, 8674, 26896, 32152]),
(5, [31, 3652, 8682, 13448, 26896]),
(5, [31, 3652, 8682, 13448, 26911]),
(5, [31, 3652, 8690, 13448, 26896]),
(5, [31, 3652, 8690, 13471, 26896]),
(5, [31, 3652, 8703, 13448, 26896]),
(5, [31, 3652, 9216, 9698, 26896]),
(5, [31, 3652, 9216, 26896, 27122]),
(5, [31, 3652, 9216, 26896, 32285]),
(5, [31, 3652, 9216, 27122, 28500])
],
#[
(5, [31, 3652, 9344, 26896, 27122]),
(5, [31, 3652, 9698, 13448, 26896]),
(5, [31, 3652, 9698, 26896]),
(5, [31, 3652, 9698, 26896, 28500]),
(5, [31, 3652, 9698, 26896, 32767]),
(5, [31, 3652, 10432, 13448, 26896]),
(5, [31, 3652, 10722, 13448, 26896]),
(5, [31, 3652, 13312, 26896, 32256]),
(5, [31, 3652, 13320, 13802, 26896]),
(5, [31, 3652, 13320, 26896, 27122]),
(5, [31, 3652, 13320, 26896, 32285]),
(5, [31, 3652, 13320, 26896, 32287]),
(5, [31, 3652, 13320, 26896, 32413]),
(5, [31, 3652, 13320, 26896, 32541]),
(5, [31, 3652, 13320, 26911, 32285]),
(5, [31, 3652, 13320, 32024, 32285])
],
#[
(5, [31, 3652, 13341, 26896, 32285]),
(5, [31, 3652, 13343, 26896, 32285]),
(5, [31, 3652, 13440, 26896, 27122]),
(5, [31, 3652, 13440, 26896, 32285]),
(5, [31, 3652, 13448, 14063, 32285]),
(5, [31, 3652, 13448, 15884, 26896]),
(5, [31, 3652, 13448, 16883, 26896]),
(5, [31, 3652, 13448, 18704, 18930]),
(5, [31, 3652, 13448, 18704, 32285]),
(5, [31, 3652, 13448, 18930, 26896]),
(5, [31, 3652, 13448, 24093, 26896]),
(5, [31, 3652, 13448, 24848, 27122]),
(5, [31, 3652, 13448, 25074, 26896]),
(5, [31, 3652, 13448, 26640, 32541]),
(5, [31, 3652, 13448, 26880, 27106]),
(5, [31, 3652, 13448, 26880, 27122])
],
#[
(5, [31, 3652, 13448, 26880, 32285]),
(5, [31, 3652, 13448, 26896, 27088]),
(5, [31, 3652, 13448, 26896, 27104]),
(5, [31, 3652, 13448, 26896, 27106]),
(5, [31, 3652, 13448, 26896, 27120]),
(5, [31, 3652, 13448, 26896, 27122]),
(5, [31, 3652, 13448, 26896, 27126]),
(5, [31, 3652, 13448, 26896, 27130]),
(5, [31, 3652, 13448, 26896, 27135]),
(5, [31, 3652, 13448, 26896, 28146]),
(5, [31, 3652, 13448, 26896, 30237]),
(5, [31, 3652, 13448, 26896, 31261]),
(5, [31, 3652, 13448, 26896, 32256]),
(5, [31, 3652, 13448, 26896, 32269]),
(5, [31, 3652, 13448, 26896, 32277]),
(5, [31, 3652, 13448, 26896, 32281])
],
#[
(5, [31, 3652, 13448, 26896, 32285]),
(5, [31, 3652, 13448, 26896, 32287]),
(5, [31, 3652, 13448, 26896, 32528]),
(5, [31, 3652, 13448, 26896, 32541]),
(5, [31, 3652, 13448, 26896, 32543]),
(5, [31, 3652, 13448, 26896, 32575]),
(5, [31, 3652, 13448, 26898, 27122]),
(5, [31, 3652, 13448, 26898, 32285]),
(5, [31, 3652, 13448, 26900, 27122]),
(5, [31, 3652, 13448, 26900, 27126]),
(5, [31, 3652, 13448, 26900, 32285]),
(5, [31, 3652, 13448, 26904, 27122]),
(5, [31, 3652, 13448, 26904, 27130]),
(5, [31, 3652, 13448, 26904, 32285]),
(5, [31, 3652, 13448, 26909, 32285]),
(5, [31, 3652, 13448, 26911, 27135])
],
#[
(5, [31, 3652, 13448, 26911, 32256]),
(5, [31, 3652, 13448, 26911, 32287]),
(5, [31, 3652, 13448, 26911, 32541]),
(5, [31, 3652, 13448, 26911, 32543]),
(5, [31, 3652, 13448, 26960, 27122]),
(5, [31, 3652, 13448, 26960, 32285]),
(5, [31, 3652, 13448, 27024, 32285]),
(5, [31, 3652, 13448, 27122, 27920]),
(5, [31, 3652, 13448, 27122, 28511]),
(5, [31, 3652, 13448, 27122, 32541]),
(5, [31, 3652, 13448, 27135, 28500]),
(5, [31, 3652, 13448, 27135, 28511]),
(5, [31, 3652, 13448, 27920, 28146]),
(5, [31, 3652, 13448, 27920, 32285]),
(5, [31, 3652, 13448, 32024, 32285]),
(5, [31, 3652, 13448, 32152, 32256])
],
#[
(5, [31, 3652, 13448, 32152, 32287]),
(5, [31, 3652, 13448, 32152, 32541]),
(5, [31, 3652, 13448, 32159, 32285]),
(5, [31, 3652, 13450, 26896, 27122]),
(5, [31, 3652, 13450, 26896, 32285]),
(5, [31, 3652, 13452, 26896, 27122]),
(5, [31, 3652, 13452, 26896, 32285]),
(5, [31, 3652, 13464, 26896, 27122]),
(5, [31, 3652, 13464, 26896, 32285]),
(5, [31, 3652, 13466, 26896, 27122]),
(5, [31, 3652, 13469, 26896, 32285]),
(5, [31, 3652, 13471, 26896, 27135]),
(5, [31, 3652, 13471, 26896, 32256]),
(5, [31, 3652, 13471, 26896, 32287]),
(5, [31, 3652, 13471, 26896, 32541]),
(5, [31, 3652, 13471, 26911, 27122])
]
],
#[
#[
(5, [31, 3652, 13471, 26911, 27135]),
(5, [31, 3652, 13471, 26911, 32285]),
(5, [31, 3652, 13471, 27122, 28500]),
(5, [31, 3652, 13471, 32152, 32285]),
(5, [31, 3652, 13471, 32159, 32285]),
(5, [31, 3652, 13512, 26896, 27122]),
(5, [31, 3652, 13512, 26896, 32285]),
(5, [31, 3652, 13704, 26896, 27122]),
(5, [31, 3652, 13704, 26896, 32285]),
(5, [31, 3652, 13802, 19447, 26896]),
(5, [31, 3652, 13802, 26896, 27135]),
(5, [31, 3652, 13802, 26896, 28662]),
(5, [31, 3652, 13802, 26896, 28697]),
(5, [31, 3652, 13802, 26896, 32256]),
(5, [31, 3652, 13802, 26896, 32285]),
(5, [31, 3652, 13802, 26896, 32287])
],
#[
(5, [31, 3652, 13802, 26896, 32349]),
(5, [31, 3652, 13802, 26896, 32541]),
(5, [31, 3652, 13802, 26911, 27122]),
(5, [31, 3652, 13802, 26911, 27135]),
(5, [31, 3652, 13802, 26911, 32285]),
(5, [31, 3652, 13802, 27122, 28500]),
(5, [31, 3652, 13823, 26896, 27122]),
(5, [31, 3652, 13823, 26896, 27135]),
(5, [31, 3652, 13823, 26896, 32256]),
(5, [31, 3652, 13823, 26896, 32285]),
(5, [31, 3652, 15496, 26896, 27122]),
(5, [31, 3652, 15496, 26896, 32285]),
(5, [31, 3652, 15560, 26896, 27122]),
(5, [31, 3652, 16076, 32152, 32285]),
(5, [31, 3652, 18704, 18930, 19319]),
(5, [31, 3652, 18704, 19319, 32285])
],
#[
(5, [31, 3652, 18930, 19319, 26896]),
(5, [31, 3652, 18965, 19447, 26896]),
(5, [31, 3652, 18965, 26896, 27122]),
(5, [31, 3652, 18965, 26896, 32285]),
(5, [31, 3652, 19296, 26896, 27122]),
(5, [31, 3652, 19296, 26896, 32285]),
(5, [31, 3652, 19319, 26896, 27135]),
(5, [31, 3652, 19319, 26896, 32256]),
(5, [31, 3652, 19319, 26896, 32287]),
(5, [31, 3652, 19319, 26896, 32541]),
(5, [31, 3652, 19319, 26911, 27122]),
(5, [31, 3652, 19319, 26911, 27135]),
(5, [31, 3652, 19319, 26911, 32285]),
(5, [31, 3652, 19319, 27122, 28500]),
(5, [31, 3652, 19319, 32152, 32285]),
(5, [31, 3652, 19327, 26896, 27122])
],
#[
(5, [31, 3652, 19327, 26896, 32285]),
(5, [31, 3652, 19447, 26896, 27122]),
(5, [31, 3652, 19447, 26896, 32285]),
(5, [31, 3652, 26896, 27122, 27511]),
(5, [31, 3652, 26896, 27122, 27639]),
(5, [31, 3652, 26896, 27122, 27920]),
(5, [31, 3652, 26896, 27122, 28146]),
(5, [31, 3652, 26896, 27122, 30139]),
(5, [31, 3652, 26896, 27122, 31743]),
(5, [31, 3652, 26896, 27122, 32159]),
(5, [31, 3652, 26896, 27122, 32250]),
(5, [31, 3652, 26896, 27122, 32255]),
(5, [31, 3652, 26896, 27135, 32152]),
(5, [31, 3652, 26896, 27135, 32159]),
(5, [31, 3652, 26896, 27135, 32250]),
(5, [31, 3652, 26896, 27135, 32255])
],
#[
(5, [31, 3652, 26896, 27511, 32285]),
(5, [31, 3652, 26896, 27920, 28146]),
(5, [31, 3652, 26896, 27920, 32285]),
(5, [31, 3652, 26896, 28146]),
(5, [31, 3652, 26896, 28146, 32767]),
(5, [31, 3652, 26896, 28662, 32250]),
(5, [31, 3652, 26896, 30139, 32285]),
(5, [31, 3652, 26896, 31261]),
(5, [31, 3652, 26896, 31261, 32767]),
(5, [31, 3652, 26896, 31743, 32285]),
(5, [31, 3652, 26896, 31768, 32285]),
(5, [31, 3652, 26896, 31896, 32285]),
(5, [31, 3652, 26896, 32024, 32285]),
(5, [31, 3652, 26896, 32152, 32256]),
(5, [31, 3652, 26896, 32152, 32287]),
(5, [31, 3652, 26896, 32152, 32541])
],
#[
(5, [31, 3652, 26896, 32159, 32285]),
(5, [31, 3652, 26896, 32250, 32285]),
(5, [31, 3652, 26911, 27122, 32152]),
(5, [31, 3652, 26911, 27122, 32159]),
(5, [31, 3652, 26911, 27122, 32250]),
(5, [31, 3652, 26911, 27135, 32152]),
(5, [31, 3652, 26911, 27135, 32159]),
(5, [31, 3652, 26911, 27135, 32255]),
(5, [31, 3652, 26911, 32152, 32285]),
(5, [31, 3652, 26911, 32159, 32285]),
(5, [31, 3652, 27122, 27920]),
(5, [31, 3652, 27122, 27920, 32767]),
(5, [31, 3652, 27122, 28500, 32152]),
(5, [31, 3652, 27122, 28500, 32250]),
(5, [31, 3652, 27920, 28146]),
(5, [31, 3652, 27920, 28146, 32767])
],
#[
(5, [31, 3652, 27920, 32285]),
(5, [31, 3652, 27920, 32285, 32767]),
(5, [31, 3652, 28500, 32152, 32285]),
(5, [31, 3652, 32024, 32285]),
(5, [31, 3652, 32024, 32285, 32767]),
(5, [31, 3652, 32152, 32285, 32413]),
(5, [31, 3652, 32152, 32285, 32541]),
(5, [31, 3652, 32152, 32541]),
(5, [31, 3652, 32152, 32541, 32767]),
(5, [31, 3654, 13448, 26896, 27122]),
(5, [31, 3654, 13448, 26896, 32285]),
(5, [31, 3660, 13448, 26896, 27122]),
(5, [31, 3660, 13448, 26896, 32285]),
(5, [31, 3668, 13448, 26896, 27122]),
(5, [31, 3668, 13448, 26896, 32285]),
(5, [31, 3670, 13448, 26896, 27122])
],
#[
(5, [31, 3679, 4070, 13802, 26896]),
(5, [31, 3679, 13448, 27122, 28500]),
(5, [31, 3780, 13448, 26896, 27122]),
(5, [31, 3780, 13448, 26896, 32285]),
(5, [31, 3908, 13448, 26896, 27122]),
(5, [31, 3908, 13448, 26896, 32285]),
(5, [31, 4070, 13448, 27122, 28500]),
(5, [31, 4070, 13802, 26896, 28500]),
(5, [31, 4070, 13802, 26896, 29115]),
(5, [31, 4267, 13448, 26896, 27122]),
(5, [31, 4267, 13448, 26896, 32285]),
(5, [31, 4267, 13448, 27122]),
(5, [31, 4267, 13448, 27122, 28500]),
(5, [31, 4267, 13448, 27122, 32767]),
(5, [31, 5645, 13448, 16076, 26896]),
(5, [31, 5645, 13448, 26896, 28500])
],
#[
(5, [31, 5645, 13448, 26896, 29115]),
(5, [31, 5645, 13448, 27122, 28500]),
(5, [31, 5645, 13448, 28500]),
(5, [31, 5645, 13448, 28500, 32767]),
(5, [31, 5871, 13448, 16076, 27122]),
(5, [31, 5871, 13448, 16076, 32285]),
(5, [31, 5871, 13448, 27122, 28500]),
(5, [31, 5871, 13448, 27122, 29115]),
(5, [31, 5871, 13448, 28500, 32285]),
(5, [31, 5871, 13448, 29115, 32285]),
(5, [31, 8192, 13448, 27122, 28500]),
(5, [31, 8320, 13448, 27122, 28500]),
(5, [31, 8674, 11844, 13448, 26896]),
(5, [31, 8674, 13448, 16076, 26896]),
(5, [31, 8674, 13448, 26896, 28500]),
(5, [31, 8674, 13448, 26896, 29115])
],
#[
(5, [31, 9216, 9698, 26896, 28500]),
(5, [31, 9216, 13448, 27122, 28500]),
(5, [31, 9216, 26896, 27122, 28500]),
(5, [31, 9216, 26896, 28500, 32285]),
(5, [31, 9216, 27122, 28500]),
(5, [31, 9216, 27122, 28500, 32767]),
(5, [31, 9698, 13448, 26896, 28500]),
(5, [31, 9698, 26896, 28500]),
(5, [31, 9698, 26896, 28500, 32767]),
(5, [31, 10432, 13448, 16076, 26896]),
(5, [31, 10722, 13448, 16076, 26896]),
(5, [31, 11844, 13448, 26896, 27122]),
(5, [31, 11844, 13448, 26896, 32285]),
(5, [31, 11972, 13448, 26896, 27122]),
(5, [31, 13320, 15948, 26896, 32285]),
(5, [31, 13320, 26896, 28500, 32285])
],
#[
(5, [31, 13320, 26896, 29115, 32285]),
(5, [31, 13448, 13471, 27122, 28500]),
(5, [31, 13448, 13802, 27122, 28500]),
(5, [31, 13448, 15884, 16076, 26896]),
(5, [31, 13448, 15948, 26896, 32285]),
(5, [31, 13448, 16076, 16883, 26896]),
(5, [31, 13448, 16076, 26896, 27088]),
(5, [31, 13448, 16076, 26896, 27135]),
(5, [31, 13448, 16076, 26896, 32256]),
(5, [31, 13448, 16076, 26896, 32287]),
(5, [31, 13448, 16076, 26896, 32541]),
(5, [31, 13448, 16076, 26896, 32575]),
(5, [31, 13448, 16076, 26911, 27122]),
(5, [31, 13448, 16076, 26911, 27135]),
(5, [31, 13448, 16076, 26911, 32285]),
(5, [31, 13448, 16076, 27122, 28500])
],
#[
(5, [31, 13448, 16076, 32152, 32285]),
(5, [31, 13448, 16691, 16883, 26896]),
(5, [31, 13448, 16691, 26896, 27122]),
(5, [31, 13448, 16691, 26896, 32285]),
(5, [31, 13448, 19319, 27122, 28500]),
(5, [31, 13448, 24848, 27122, 29115]),
(5, [31, 13448, 25074, 26896, 29115]),
(5, [31, 13448, 26640, 28500, 32285]),
(5, [31, 13448, 26896, 27122, 30139]),
(5, [31, 13448, 26896, 27122, 31163]),
(5, [31, 13448, 26896, 27122, 32732]),
(5, [31, 13448, 26896, 27135, 28500]),
(5, [31, 13448, 26896, 27135, 29115]),
(5, [31, 13448, 26896, 28244, 32285]),
(5, [31, 13448, 26896, 28500, 32256]),
(5, [31, 13448, 26896, 28500, 32287])
],
#[
(5, [31, 13448, 26896, 28500, 32541]),
(5, [31, 13448, 26896, 29115, 32256]),
(5, [31, 13448, 26896, 29115, 32287]),
(5, [31, 13448, 26896, 29115, 32541]),
(5, [31, 13448, 26896, 30139, 32285]),
(5, [31, 13448, 26896, 31163, 32285]),
(5, [31, 13448, 26896, 32256, 32324]),
(5, [31, 13448, 26896, 32285, 32732]),
(5, [31, 13448, 26911, 27122, 28500]),
(5, [31, 13448, 26911, 27122, 29115]),
(5, [31, 13448, 26911, 27135, 29115]),
(5, [31, 13448, 26911, 29115, 32285]),
(5, [31, 13448, 26960, 27122, 28500]),
(5, [31, 13448, 27122, 27135, 28500]),
(5, [31, 13448, 27122, 28500, 28511]),
(5, [31, 13448, 27122, 28500, 28662])
],
#[
(5, [31, 13448, 27122, 28500, 29115]),
(5, [31, 13448, 27122, 28500, 32152]),
(5, [31, 13448, 27122, 28500, 32250]),
(5, [31, 13448, 27122, 28500, 32285]),
(5, [31, 13448, 27122, 28500, 32732]),
(5, [31, 13448, 27122, 28500, 32736]),
(5, [31, 13448, 27122, 28500, 32767]),
(5, [31, 13448, 28500, 32152, 32285]),
(5, [31, 13448, 29115, 32152, 32285]),
(5, [31, 13448, 32152, 32285, 32732]),
(5, [31, 13471, 26896, 27122, 28500]),
(5, [31, 13471, 26896, 27122, 29115]),
(5, [31, 13471, 26896, 28500, 32285]),
(5, [31, 13471, 26896, 29115, 32285]),
(5, [31, 13471, 27122, 28500]),
(5, [31, 13471, 27122, 28500, 32767])
],
#[
(5, [31, 13802, 26896, 27122, 28500]),
(5, [31, 13802, 26896, 27122, 29115]),
(5, [31, 13802, 26896, 28500, 28662]),
(5, [31, 13802, 26896, 28500, 32285]),
(5, [31, 13802, 26896, 29115, 32285]),
(5, [31, 13802, 27122, 28500]),
(5, [31, 13802, 27122, 28500, 32767]),
(5, [31, 16076, 19319, 26896, 27122]),
(5, [31, 16076, 19319, 26896, 32285]),
(5, [31, 16076, 26896, 27122, 32152]),
(5, [31, 16076, 26896, 32152, 32285]),
(5, [31, 16076, 32152, 32285]),
(5, [31, 16076, 32152, 32285, 32767]),
(5, [31, 19319, 26896, 27122, 28500]),
(5, [31, 19319, 26896, 27122, 29115]),
(5, [31, 19319, 26896, 28500, 32285])
],
#[
(5, [31, 19319, 26896, 29115, 32285]),
(5, [31, 19319, 27122, 28500]),
(5, [31, 19319, 27122, 28500, 32767]),
(5, [31, 26896, 27122, 28500, 32152]),
(5, [31, 26896, 27122, 28500, 32250]),
(5, [31, 26896, 27122, 29115, 30139]),
(5, [31, 26896, 27122, 29115, 32152]),
(5, [31, 26896, 27122, 29115, 32250]),
(5, [31, 26896, 27122, 30139]),
(5, [31, 26896, 27122, 30139, 32767]),
(5, [31, 26896, 27122, 32152, 32732]),
(5, [31, 26896, 28500, 32152, 32285]),
(5, [31, 26896, 29115, 30139, 32285]),
(5, [31, 26896, 29115, 32152, 32285]),
(5, [31, 26896, 30139, 32285]),
(5, [31, 26896, 30139, 32285, 32767])
]
],
#[
#[
(5, [31, 26896, 32152, 32285, 32732]),
(5, [31, 27122, 28500, 32152]),
(5, [31, 27122, 28500, 32152, 32767]),
(5, [31, 27122, 28500, 32250]),
(5, [31, 27122, 28500, 32250, 32767]),
(5, [31, 28500, 32152, 32285]),
(5, [31, 28500, 32152, 32285, 32767]),
(5, [64, 159, 3652, 13448, 26896]),
(5, [64, 482, 1055, 3652, 26896]),
(5, [64, 511, 3652, 13471, 26896]),
(5, [64, 511, 3652, 13802, 26896]),
(5, [68, 95, 482, 13448, 26896]),
(5, [68, 95, 511, 13448, 26896]),
(5, [68, 256, 511, 13448, 26896]),
(5, [68, 482, 511, 5871, 13448]),
(5, [68, 482, 511, 13448, 26896])
],
#[
(5, [68, 482, 511, 13448, 26964]),
(5, [68, 482, 511, 13448, 32152]),
(5, [68, 482, 511, 13471, 26896]),
(5, [68, 482, 511, 13516, 26896]),
(5, [68, 482, 511, 13802, 26896]),
(5, [68, 482, 511, 13823, 26896]),
(5, [68, 482, 511, 19319, 26896]),
(5, [68, 482, 511, 26896, 32152]),
(5, [68, 482, 13448, 26896, 32256]),
(5, [68, 482, 13448, 26896, 32736]),
(5, [68, 486, 511, 13448, 26896]),
(5, [68, 511, 3652, 13471, 26896]),
(5, [68, 511, 3652, 13802, 26896]),
(5, [68, 511, 3679, 13448, 26896]),
(5, [68, 511, 4070, 13448, 26896]),
(5, [68, 511, 13448, 13471, 26896])
],
#[
(5, [68, 511, 13448, 13802, 26896]),
(5, [68, 511, 13448, 26896, 32285]),
(5, [68, 511, 13448, 26896, 32736]),
(5, [68, 511, 13471, 26896]),
(5, [68, 511, 13471, 26896, 32767]),
(5, [68, 511, 13802, 26896]),
(5, [68, 511, 13802, 26896, 32767]),
(5, [95, 128, 3652, 13448, 26896]),
(5, [95, 482, 1024, 3652, 26896]),
(5, [95, 482, 3652, 5871, 13448]),
(5, [95, 482, 3652, 13448, 26896]),
(5, [95, 482, 3652, 13448, 26911]),
(5, [95, 482, 3652, 13448, 26960]),
(5, [95, 482, 3652, 13448, 26975]),
(5, [95, 482, 3652, 13448, 32152]),
(5, [95, 482, 3652, 13471, 26896])
],
#[
(5, [95, 482, 3652, 13512, 26896]),
(5, [95, 482, 3652, 13535, 26896]),
(5, [95, 482, 3652, 13802, 26896]),
(5, [95, 482, 3652, 19319, 26896]),
(5, [95, 482, 3652, 26896, 32152]),
(5, [95, 482, 13448, 16076, 26896]),
(5, [95, 482, 13448, 26896, 28500]),
(5, [95, 482, 13448, 26896, 29115]),
(5, [95, 511, 3652, 13448, 26896]),
(5, [95, 3652, 4070, 13448, 26896]),
(5, [95, 3652, 13448, 26896, 27122]),
(5, [95, 3652, 13448, 26896, 32285]),
(5, [128, 159, 482, 3652, 32152]),
(5, [128, 482, 511, 3652, 32152]),
(5, [128, 482, 1055, 3652, 26896]),
(5, [128, 482, 3652, 32152, 32736])
],
#[
(5, [128, 511, 3652, 13471, 26896]),
(5, [128, 511, 3652, 13802, 26896]),
(5, [130, 511, 3652, 13471, 26896]),
(5, [136, 482, 511, 3652, 32152]),
(5, [136, 511, 3652, 13471, 26896]),
(5, [136, 511, 3652, 13802, 26896]),
(5, [159, 482, 1024, 3652, 26896]),
(5, [159, 482, 3652, 5871, 13448]),
(5, [159, 482, 3652, 13448, 26896]),
(5, [159, 482, 3652, 13448, 26911]),
(5, [159, 482, 3652, 13448, 27024]),
(5, [159, 482, 3652, 13448, 27039]),
(5, [159, 482, 3652, 13448, 32152]),
(5, [159, 482, 3652, 13471, 26896]),
(5, [159, 482, 3652, 13802, 26896]),
(5, [159, 482, 3652, 19319, 26896])
],
#[
(5, [159, 482, 3652, 26896, 32152]),
(5, [159, 482, 3652, 32152]),
(5, [159, 482, 3652, 32152, 32767]),
(5, [159, 482, 3780, 13448, 26896]),
(5, [159, 482, 13448, 16076, 26896]),
(5, [159, 482, 13448, 26896, 28500]),
(5, [159, 482, 13448, 26896, 29115]),
(5, [159, 511, 3652, 13448, 26896]),
(5, [159, 511, 3652, 13471, 26896]),
(5, [159, 3652, 13448, 13802, 26896]),
(5, [159, 3652, 13448, 26896, 27122]),
(5, [159, 3652, 13448, 26896, 32285]),
(5, [192, 223, 3652, 13448, 26896]),
(5, [192, 223, 13448, 16076, 26896]),
(5, [192, 3652, 13448, 26896, 32736]),
(5, [192, 13448, 16076, 26896, 32736])
],
#[
(5, [204, 482, 511, 13448, 26896]),
(5, [223, 482, 3652, 13448, 26896]),
(5, [223, 482, 13448, 16076, 26896]),
(5, [223, 3652, 13448, 16076, 26896]),
(5, [223, 3652, 13448, 26896]),
(5, [223, 3652, 13448, 26896, 32767]),
(5, [223, 13448, 16076, 26896]),
(5, [223, 13448, 16076, 26896, 32767]),
(5, [226, 255, 3652, 5871, 13448]),
(5, [226, 255, 3652, 13448, 26896]),
(5, [226, 3652, 5871, 13448, 32736]),
(5, [226, 3652, 13448, 26896, 32736]),
(5, [255, 482, 3652, 5871, 13448]),
(5, [255, 482, 3652, 13448, 26896]),
(5, [255, 3652, 5871, 13448]),
(5, [255, 3652, 5871, 13448, 26896])
],
#[
(5, [255, 3652, 5871, 13448, 32767]),
(5, [255, 3652, 13448, 26896]),
(5, [255, 3652, 13448, 26896, 32767]),
(5, [256, 287, 482, 3652, 32152]),
(5, [256, 482, 511, 3652, 32152]),
(5, [256, 482, 1055, 3652, 26896]),
(5, [256, 482, 2079, 3652, 13448]),
(5, [256, 482, 3652, 32152, 32736]),
(5, [256, 511, 1024, 3652, 26896]),
(5, [256, 511, 2048, 3652, 13448]),
(5, [256, 511, 3652, 5871, 13448]),
(5, [256, 511, 3652, 13448, 26896]),
(5, [256, 511, 3652, 13448, 26911]),
(5, [256, 511, 3652, 13448, 27122]),
(5, [256, 511, 3652, 13448, 27135]),
(5, [256, 511, 3652, 13448, 32152])
],
#[
(5, [256, 511, 3652, 13471, 26896]),
(5, [256, 511, 3652, 13704, 26896]),
(5, [256, 511, 3652, 13802, 26896]),
(5, [256, 511, 3652, 13823, 26896]),
(5, [256, 511, 3652, 19319, 26896]),
(5, [256, 511, 3652, 26896, 32152]),
(5, [256, 511, 3652, 32152]),
(5, [256, 511, 3652, 32152, 32767]),
(5, [256, 511, 3908, 13448, 26896]),
(5, [256, 511, 13448, 16076, 26896]),
(5, [256, 511, 13448, 26896, 28500]),
(5, [256, 511, 13448, 26896, 29115]),
(5, [256, 3652, 13448, 26896, 32256]),
(5, [258, 511, 3652, 13448, 26896]),
(5, [272, 482, 511, 3652, 32152]),
(5, [272, 511, 3652, 13471, 26896])
],
#[
(5, [272, 511, 3652, 13802, 26896]),
(5, [287, 482, 1024, 3652, 26896]),
(5, [287, 482, 3652, 5871, 13448]),
(5, [287, 482, 3652, 13448, 26896]),
(5, [287, 482, 3652, 13448, 32152]),
(5, [287, 482, 3652, 13471, 26896]),
(5, [287, 482, 3652, 13704, 26896]),
(5, [287, 482, 3652, 13727, 26896]),
(5, [287, 482, 3652, 13802, 26896]),
(5, [287, 482, 3652, 19319, 26896]),
(5, [287, 482, 3652, 26896, 32152]),
(5, [287, 482, 3652, 32152]),
(5, [287, 482, 3652, 32152, 32767]),
(5, [287, 482, 3908, 13448, 26896]),
(5, [287, 482, 13448, 16076, 26896]),
(5, [287, 482, 13448, 26896, 28500])
],
#[
(5, [287, 482, 13448, 26896, 29115]),
(5, [287, 3652, 13448, 26896, 32285]),
(5, [320, 511, 3652, 13448, 26896]),
(5, [320, 511, 13448, 26896, 28500]),
(5, [340, 482, 511, 13448, 26896]),
(5, [351, 482, 3652, 13448, 26896]),
(5, [351, 482, 13448, 26896, 28500]),
(5, [354, 511, 3652, 13448, 26896]),
(5, [354, 511, 3652, 19319, 26896]),
(5, [383, 482, 3652, 13448, 26896]),
(5, [383, 482, 3652, 19319, 26896]),
(5, [384, 511, 3652, 13448, 26896]),
(5, [384, 511, 3652, 13448, 32152]),
(5, [384, 511, 3652, 26896, 32152]),
(5, [415, 482, 3652, 13448, 26896]),
(5, [415, 482, 3652, 13448, 32152])
],
#[
(5, [415, 482, 3652, 26896, 32152]),
(5, [418, 511, 3652, 13448, 26896]),
(5, [418, 511, 13448, 26896, 29115]),
(5, [443, 482, 511, 13448, 26896]),
(5, [447, 482, 3652, 13448, 26896]),
(5, [447, 482, 13448, 26896, 29115]),
(5, [480, 511, 3652, 13448, 26896]),
(5, [480, 1024, 3652, 26896, 32736]),
(5, [480, 3652, 5871, 13448, 32736]),
(5, [480, 3652, 13440, 26896, 32736]),
(5, [480, 3652, 13448, 26880, 32736]),
(5, [480, 3652, 13448, 26896, 32736]),
(5, [480, 3652, 13448, 26896, 32738]),
(5, [480, 3652, 13448, 26911, 32736]),
(5, [480, 3652, 13448, 32152, 32736]),
(5, [480, 3652, 13471, 26896, 32736])
],
#[
(5, [480, 3652, 13800, 26896, 32736]),
(5, [480, 3652, 13802, 26896, 32736]),
(5, [480, 3652, 19319, 26896, 32736]),
(5, [480, 3652, 26896, 32152, 32736]),
(5, [480, 13448, 16076, 26896, 32736]),
(5, [480, 13448, 26896, 28500, 32736]),
(5, [480, 13448, 26896, 29115, 32736]),
(5, [482, 511, 615, 3652, 13448]),
(5, [482, 511, 615, 3652, 26896]),
(5, [482, 511, 1024, 3652, 5871]),
(5, [482, 511, 1024, 3652, 27920]),
(5, [482, 511, 1024, 26896, 28500]),
(5, [482, 511, 1024, 26896, 29115]),
(5, [482, 511, 1028, 3652, 26896]),
(5, [482, 511, 1032, 3652, 26896]),
(5, [482, 511, 1055, 3652, 26896])
],
#[
(5, [482, 511, 1088, 3652, 26896]),
(5, [482, 511, 1092, 3652, 26896]),
(5, [482, 511, 1092, 13448, 26896]),
(5, [482, 511, 1092, 13823, 26896]),
(5, [482, 511, 1152, 3652, 26896]),
(5, [482, 511, 1160, 3652, 26896]),
(5, [482, 511, 1506, 3652, 26896]),
(5, [482, 511, 1535, 3652, 26896]),
(5, [482, 511, 1604, 5871, 13448]),
(5, [482, 511, 1604, 13448, 26896]),
(5, [482, 511, 2116, 13448, 26896]),
(5, [482, 511, 2304, 3652, 13448]),
(5, [482, 511, 2320, 3652, 13448]),
(5, [482, 511, 2628, 3652, 26896]),
(5, [482, 511, 2628, 13448, 26896]),
(5, [482, 511, 2628, 19319, 26896])
],
#[
(5, [482, 511, 2628, 26896]),
(5, [482, 511, 2628, 26896, 32767]),
(5, [482, 511, 3072, 3652, 26896]),
(5, [482, 511, 3652, 5256, 5871]),
(5, [482, 511, 3652, 5256, 26896]),
(5, [482, 511, 3652, 5871, 13471]),
(5, [482, 511, 3652, 5871, 13802]),
(5, [482, 511, 3652, 5871, 13823]),
(5, [482, 511, 3652, 5871, 19319]),
(5, [482, 511, 3652, 5871, 32152]),
(5, [482, 511, 3652, 5887, 13448]),
(5, [482, 511, 3652, 9216, 26896]),
(5, [482, 511, 3652, 13312, 26896]),
(5, [482, 511, 3652, 13320, 26896]),
(5, [482, 511, 3652, 13440, 26896]),
(5, [482, 511, 3652, 13448, 14063])
],
#[
(5, [482, 511, 3652, 13448, 18704]),
(5, [482, 511, 3652, 13448, 26880]),
(5, [482, 511, 3652, 13448, 26896]),
(5, [482, 511, 3652, 13448, 26900]),
(5, [482, 511, 3652, 13448, 26904]),
(5, [482, 511, 3652, 13448, 26960]),
(5, [482, 511, 3652, 13448, 26964]),
(5, [482, 511, 3652, 13448, 27024]),
(5, [482, 511, 3652, 13448, 27032]),
(5, [482, 511, 3652, 13448, 27920]),
(5, [482, 511, 3652, 13450, 26896]),
(5, [482, 511, 3652, 13452, 26896]),
(5, [482, 511, 3652, 13464, 26896]),
(5, [482, 511, 3652, 13471, 26911]),
(5, [482, 511, 3652, 13471, 32152]),
(5, [482, 511, 3652, 13471, 32159])
]
],
#[
#[
(5, [482, 511, 3652, 13512, 26896]),
(5, [482, 511, 3652, 13516, 26896]),
(5, [482, 511, 3652, 13704, 26896]),
(5, [482, 511, 3652, 13720, 26896]),
(5, [482, 511, 3652, 13823, 26896]),
(5, [482, 511, 3652, 15496, 26896]),
(5, [482, 511, 3652, 16076, 32152]),
(5, [482, 511, 3652, 18704, 19319]),
(5, [482, 511, 3652, 18944, 26896]),
(5, [482, 511, 3652, 18965, 26896]),
(5, [482, 511, 3652, 19296, 26896]),
(5, [482, 511, 3652, 19319, 32152]),
(5, [482, 511, 3652, 19327, 26896]),
(5, [482, 511, 3652, 19447, 26896]),
(5, [482, 511, 3652, 19455, 26896]),
(5, [482, 511, 3652, 26896, 27511])
],
#[
(5, [482, 511, 3652, 26896, 27920]),
(5, [482, 511, 3652, 26896, 30139]),
(5, [482, 511, 3652, 26896, 31743]),
(5, [482, 511, 3652, 26896, 32159]),
(5, [482, 511, 3652, 26896, 32250]),
(5, [482, 511, 3652, 26896, 32255]),
(5, [482, 511, 3652, 26911, 32152]),
(5, [482, 511, 3652, 27920]),
(5, [482, 511, 3652, 27920, 32767]),
(5, [482, 511, 3652, 28500, 32152]),
(5, [482, 511, 3660, 13448, 26896]),
(5, [482, 511, 3668, 13448, 26896]),
(5, [482, 511, 3780, 13448, 26896]),
(5, [482, 511, 3788, 13448, 26896]),
(5, [482, 511, 3908, 13448, 26896]),
(5, [482, 511, 3924, 13448, 26896])
],
#[
(5, [482, 511, 4267, 13448, 26896]),
(5, [482, 511, 5871, 13448, 16076]),
(5, [482, 511, 5871, 13448, 28500]),
(5, [482, 511, 5871, 13448, 29115]),
(5, [482, 511, 9216, 26896, 28500]),
(5, [482, 511, 11844, 13448, 26896]),
(5, [482, 511, 13448, 13516, 26896]),
(5, [482, 511, 13448, 16076, 32152]),
(5, [482, 511, 13448, 16691, 26896]),
(5, [482, 511, 13448, 26896, 26964]),
(5, [482, 511, 13448, 26896, 30139]),
(5, [482, 511, 13448, 26896, 31163]),
(5, [482, 511, 13448, 26896, 32324]),
(5, [482, 511, 13448, 26896, 32699]),
(5, [482, 511, 13448, 26896, 32732]),
(5, [482, 511, 13448, 27122, 28500])
],
#[
(5, [482, 511, 13448, 28500, 32152]),
(5, [482, 511, 13448, 29115, 32152]),
(5, [482, 511, 13448, 32152, 32732]),
(5, [482, 511, 13471, 26896, 28500]),
(5, [482, 511, 13471, 26896, 29115]),
(5, [482, 511, 13802, 26896, 28500]),
(5, [482, 511, 13802, 26896, 29115]),
(5, [482, 511, 13823, 26896, 28500]),
(5, [482, 511, 13823, 26896, 29115]),
(5, [482, 511, 16076, 19319, 26896]),
(5, [482, 511, 16076, 26896, 32152]),
(5, [482, 511, 16076, 32152]),
(5, [482, 511, 16076, 32152, 32767]),
(5, [482, 511, 19319, 26896, 28500]),
(5, [482, 511, 19319, 26896, 29115]),
(5, [482, 511, 26896, 28500, 32152])
],
#[
(5, [482, 511, 26896, 29115, 30139]),
(5, [482, 511, 26896, 29115, 32152]),
(5, [482, 511, 26896, 30139]),
(5, [482, 511, 26896, 30139, 32767]),
(5, [482, 511, 26896, 32152, 32732]),
(5, [482, 511, 28500, 32152]),
(5, [482, 511, 28500, 32152, 32767]),
(5, [482, 615, 3652, 13448, 32736]),
(5, [482, 615, 3652, 26896, 32736]),
(5, [482, 1024, 1055, 3652, 5871]),
(5, [482, 1024, 1055, 3652, 26896]),
(5, [482, 1024, 1055, 3652, 26911]),
(5, [482, 1024, 1055, 3652, 27920]),
(5, [482, 1024, 1055, 3652, 27935]),
(5, [482, 1024, 1055, 26896, 28500]),
(5, [482, 1024, 1055, 26896, 29115])
],
#[
(5, [482, 1024, 1535, 3652, 26896]),
(5, [482, 1024, 2079, 3652, 26896]),
(5, [482, 1024, 3652, 3679, 26911]),
(5, [482, 1024, 3652, 5871, 32736]),
(5, [482, 1024, 3652, 26880, 32736]),
(5, [482, 1024, 3652, 26896, 31712]),
(5, [482, 1024, 3652, 26896, 32256]),
(5, [482, 1024, 3652, 26896, 32736]),
(5, [482, 1024, 3652, 26896, 32738]),
(5, [482, 1024, 3652, 26911, 32736]),
(5, [482, 1024, 3652, 27920, 32736]),
(5, [482, 1024, 26896, 28500, 32736]),
(5, [482, 1024, 26896, 29115, 32736]),
(5, [482, 1028, 1055, 3652, 26896]),
(5, [482, 1028, 3652, 3679, 26896]),
(5, [482, 1028, 3652, 26896, 32736])
],
#[
(5, [482, 1028, 3679, 13471, 26896]),
(5, [482, 1032, 1055, 3652, 26896]),
(5, [482, 1032, 3652, 3679, 26911]),
(5, [482, 1032, 3652, 26896, 32736]),
(5, [482, 1055, 1506, 3652, 26896]),
(5, [482, 1055, 1535, 3652, 26896]),
(5, [482, 1055, 2048, 3652, 26896]),
(5, [482, 1055, 3652, 3679, 26896]),
(5, [482, 1055, 3652, 4070, 26896]),
(5, [482, 1055, 3652, 5871]),
(5, [482, 1055, 3652, 5871, 13448]),
(5, [482, 1055, 3652, 5871, 26896]),
(5, [482, 1055, 3652, 5871, 32767]),
(5, [482, 1055, 3652, 8192, 26896]),
(5, [482, 1055, 3652, 13448, 26896]),
(5, [482, 1055, 3652, 13448, 26911])
],
#[
(5, [482, 1055, 3652, 13448, 27920]),
(5, [482, 1055, 3652, 13448, 27935]),
(5, [482, 1055, 3652, 13448, 32152]),
(5, [482, 1055, 3652, 13471, 26896]),
(5, [482, 1055, 3652, 13802, 26896]),
(5, [482, 1055, 3652, 16076, 26896]),
(5, [482, 1055, 3652, 19319, 26896]),
(5, [482, 1055, 3652, 26896]),
(5, [482, 1055, 3652, 26896, 26911]),
(5, [482, 1055, 3652, 26896, 27122]),
(5, [482, 1055, 3652, 26896, 27920]),
(5, [482, 1055, 3652, 26896, 27935]),
(5, [482, 1055, 3652, 26896, 28500]),
(5, [482, 1055, 3652, 26896, 29115]),
(5, [482, 1055, 3652, 26896, 31712]),
(5, [482, 1055, 3652, 26896, 31743])
],
#[
(5, [482, 1055, 3652, 26896, 32152]),
(5, [482, 1055, 3652, 26896, 32285]),
(5, [482, 1055, 3652, 26896, 32736]),
(5, [482, 1055, 3652, 26896, 32767]),
(5, [482, 1055, 3652, 26911]),
(5, [482, 1055, 3652, 26911, 32767]),
(5, [482, 1055, 3652, 27920]),
(5, [482, 1055, 3652, 27920, 32767]),
(5, [482, 1055, 3652, 27935]),
(5, [482, 1055, 3652, 27935, 32767]),
(5, [482, 1055, 13448, 26896, 28500]),
(5, [482, 1055, 13448, 26896, 29115]),
(5, [482, 1055, 26896, 28500]),
(5, [482, 1055, 26896, 28500, 32767]),
(5, [482, 1055, 26896, 29115]),
(5, [482, 1055, 26896, 29115, 32767])
],
#[
(5, [482, 1088, 1119, 3652, 26896]),
(5, [482, 1088, 3652, 26896, 32736]),
(5, [482, 1119, 3652, 13448, 26896]),
(5, [482, 1119, 3652, 13802, 26896]),
(5, [482, 1119, 3652, 26896]),
(5, [482, 1119, 3652, 26896, 32767]),
(5, [482, 1152, 1183, 3652, 26896]),
(5, [482, 1152, 3652, 26896, 32736]),
(5, [482, 1183, 3652, 4070, 26896]),
(5, [482, 1183, 3652, 13448, 26896]),
(5, [482, 1183, 3652, 26896]),
(5, [482, 1183, 3652, 26896, 32767]),
(5, [482, 1506, 1535, 3652, 26896]),
(5, [482, 1506, 3652, 26896, 32736]),
(5, [482, 1535, 3652, 13448, 26896]),
(5, [482, 1535, 3652, 26896])
],
#[
(5, [482, 1535, 3652, 26896, 32767]),
(5, [482, 1604, 5871, 13448, 32736]),
(5, [482, 1604, 13448, 26896, 32736]),
(5, [482, 2052, 3679, 13448, 26911]),
(5, [482, 2079, 3652, 5871, 13448]),
(5, [482, 2079, 3652, 13448, 26896]),
(5, [482, 2079, 3652, 13448, 26911]),
(5, [482, 2079, 3652, 13448, 28500]),
(5, [482, 2079, 3652, 13448, 32152]),
(5, [482, 2079, 3652, 13471, 26896]),
(5, [482, 2079, 3652, 13802, 26896]),
(5, [482, 2079, 3652, 15496, 26896]),
(5, [482, 2079, 3652, 15519, 26896]),
(5, [482, 2079, 3652, 19319, 26896]),
(5, [482, 2079, 3652, 26896, 32152]),
(5, [482, 2079, 13448, 16076, 26896])
],
#[
(5, [482, 2079, 13448, 26896, 29115]),
(5, [482, 2143, 3652, 13448, 26896]),
(5, [482, 2304, 2335, 3652, 13448]),
(5, [482, 2304, 3652, 13448, 32736]),
(5, [482, 2335, 3652, 13448, 26896]),
(5, [482, 2559, 3652, 13448, 26896]),
(5, [482, 2628, 3652, 26896, 32736]),
(5, [482, 2628, 13448, 26896, 32736]),
(5, [482, 2628, 19319, 26896, 32736]),
(5, [482, 2628, 26896, 32736]),
(5, [482, 2628, 26896, 32736, 32767]),
(5, [482, 3072, 3103, 3652, 26896]),
(5, [482, 3072, 3652, 26896, 32736]),
(5, [482, 3103, 3652, 13448, 26896]),
(5, [482, 3103, 3652, 13448, 32152]),
(5, [482, 3103, 3652, 26896])
],
#[
(5, [482, 3103, 3652, 26896, 32152]),
(5, [482, 3103, 3652, 26896, 32767]),
(5, [482, 3648, 13448, 26896, 32740]),
(5, [482, 3652, 3679, 5856, 13448]),
(5, [482, 3652, 3679, 5871, 13471]),
(5, [482, 3652, 3679, 13448, 26900]),
(5, [482, 3652, 3679, 13448, 32159]),
(5, [482, 3652, 3679, 13452, 26896]),
(5, [482, 3652, 3679, 13471, 26911]),
(5, [482, 3652, 3679, 13471, 32152]),
(5, [482, 3652, 3679, 13471, 32159]),
(5, [482, 3652, 3679, 13802, 26911]),
(5, [482, 3652, 3679, 13823, 26896]),
(5, [482, 3652, 3679, 19296, 26896]),
(5, [482, 3652, 3679, 19319, 26911]),
(5, [482, 3652, 3679, 26896, 32159])
],
#[
(5, [482, 3652, 3679, 26911, 32152]),
(5, [482, 3652, 3679, 26911, 32159]),
(5, [482, 3652, 4095, 13471, 26896]),
(5, [482, 3652, 4095, 13823, 26896]),
(5, [482, 3652, 5256, 5871, 32736]),
(5, [482, 3652, 5256, 26896, 32736]),
(5, [482, 3652, 5856, 5887, 13448]),
(5, [482, 3652, 5856, 13448, 32736]),
(5, [482, 3652, 5871, 8223, 13448]),
(5, [482, 3652, 5871, 13440, 32736]),
(5, [482, 3652, 5871, 13448, 32256]),
(5, [482, 3652, 5871, 13448, 32738]),
(5, [482, 3652, 5871, 13471, 32736]),
(5, [482, 3652, 5871, 13802, 32736]),
(5, [482, 3652, 5871, 19319, 32736]),
(5, [482, 3652, 5871, 32152, 32736])
],
#[
(5, [482, 3652, 5887, 13448, 26911]),
(5, [482, 3652, 5887, 13448, 32736]),
(5, [482, 3652, 8192, 13471, 26911]),
(5, [482, 3652, 8223, 13448, 26896]),
(5, [482, 3652, 8223, 13802, 26896]),
(5, [482, 3652, 8223, 19319, 26896]),
(5, [482, 3652, 8351, 13448, 26896]),
(5, [482, 3652, 8479, 13448, 26896]),
(5, [482, 3652, 8479, 13802, 26896]),
(5, [482, 3652, 8703, 13448, 26896]),
(5, [482, 3652, 9216, 9247, 26896]),
(5, [482, 3652, 9216, 26896, 32736]),
(5, [482, 3652, 9247, 13448, 26896]),
(5, [482, 3652, 10271, 13448, 26896]),
(5, [482, 3652, 13312, 26896, 32256]),
(5, [482, 3652, 13320, 26896, 32736])
],
#[
(5, [482, 3652, 13440, 13471, 26896]),
(5, [482, 3652, 13440, 26880, 32736]),
(5, [482, 3652, 13440, 26896, 32736]),
(5, [482, 3652, 13440, 26896, 32738]),
(5, [482, 3652, 13440, 26896, 32744]),
(5, [482, 3652, 13440, 26911, 32736]),
(5, [482, 3652, 13440, 32144, 32736]),
(5, [482, 3652, 13440, 32152, 32736]),
(5, [482, 3652, 13448, 14063, 32736]),
(5, [482, 3652, 13448, 18704, 32736]),
(5, [482, 3652, 13448, 24544, 26896]),
(5, [482, 3652, 13448, 26880, 26911]),
(5, [482, 3652, 13448, 26880, 32736]),
(5, [482, 3652, 13448, 26880, 32738]),
(5, [482, 3652, 13448, 26880, 32752]),
(5, [482, 3652, 13448, 26896, 30688])
]
],
#[
#[
(5, [482, 3652, 13448, 26896, 31712]),
(5, [482, 3652, 13448, 26896, 32256]),
(5, [482, 3652, 13448, 26896, 32480]),
(5, [482, 3652, 13448, 26896, 32608]),
(5, [482, 3652, 13448, 26896, 32672]),
(5, [482, 3652, 13448, 26896, 32736]),
(5, [482, 3652, 13448, 26896, 32738]),
(5, [482, 3652, 13448, 26898, 32736]),
(5, [482, 3652, 13448, 26900, 32736]),
(5, [482, 3652, 13448, 26904, 32736]),
(5, [482, 3652, 13448, 26911, 29088]),
(5, [482, 3652, 13448, 26911, 32736]),
(5, [482, 3652, 13448, 26911, 32740]),
(5, [482, 3652, 13448, 26960, 32736]),
(5, [482, 3652, 13448, 27024, 32736]),
(5, [482, 3652, 13448, 27920, 32736])
],
#[
(5, [482, 3652, 13448, 32128, 32736]),
(5, [482, 3652, 13448, 32136, 32736]),
(5, [482, 3652, 13448, 32144, 32736]),
(5, [482, 3652, 13448, 32152, 32256]),
(5, [482, 3652, 13448, 32152, 32738]),
(5, [482, 3652, 13448, 32159, 32736]),
(5, [482, 3652, 13450, 26896, 32736]),
(5, [482, 3652, 13452, 26896, 32736]),
(5, [482, 3652, 13464, 26896, 32736]),
(5, [482, 3652, 13471, 19327, 26896]),
(5, [482, 3652, 13471, 26880, 32736]),
(5, [482, 3652, 13471, 26896, 29088]),
(5, [482, 3652, 13471, 26896, 32256]),
(5, [482, 3652, 13471, 26896, 32736]),
(5, [482, 3652, 13471, 26896, 32738]),
(5, [482, 3652, 13471, 26896, 32740])
],
#[
(5, [482, 3652, 13471, 26911, 32736]),
(5, [482, 3652, 13471, 32152, 32736]),
(5, [482, 3652, 13471, 32159, 32736]),
(5, [482, 3652, 13512, 26896, 32736]),
(5, [482, 3652, 13704, 26896, 32736]),
(5, [482, 3652, 13792, 26896, 32736]),
(5, [482, 3652, 13794, 26896, 32736]),
(5, [482, 3652, 13800, 26896, 32736]),
(5, [482, 3652, 13802, 26880, 32736]),
(5, [482, 3652, 13802, 26896, 32256]),
(5, [482, 3652, 13802, 26896, 32738]),
(5, [482, 3652, 13802, 26911, 32736]),
(5, [482, 3652, 13823, 26896, 32256]),
(5, [482, 3652, 13823, 26896, 32736]),
(5, [482, 3652, 15496, 26896, 32736]),
(5, [482, 3652, 16076, 32152, 32736])
],
#[
(5, [482, 3652, 18704, 19319, 32736]),
(5, [482, 3652, 18965, 26896, 32736]),
(5, [482, 3652, 19296, 19327, 26896]),
(5, [482, 3652, 19296, 26896, 32736]),
(5, [482, 3652, 19319, 26880, 32736]),
(5, [482, 3652, 19319, 26896, 32256]),
(5, [482, 3652, 19319, 26896, 32738]),
(5, [482, 3652, 19319, 26911, 32736]),
(5, [482, 3652, 19319, 32152, 32736]),
(5, [482, 3652, 19327, 26896, 32736]),
(5, [482, 3652, 19447, 26896, 32736]),
(5, [482, 3652, 26880, 32136, 32736]),
(5, [482, 3652, 26880, 32152, 32736]),
(5, [482, 3652, 26896, 27511, 32736]),
(5, [482, 3652, 26896, 27920, 32736]),
(5, [482, 3652, 26896, 30139, 32736])
],
#[
(5, [482, 3652, 26896, 31712]),
(5, [482, 3652, 26896, 31712, 32767]),
(5, [482, 3652, 26896, 31743, 32736]),
(5, [482, 3652, 26896, 32128, 32736]),
(5, [482, 3652, 26896, 32136, 32736]),
(5, [482, 3652, 26896, 32144, 32736]),
(5, [482, 3652, 26896, 32152, 32256]),
(5, [482, 3652, 26896, 32152, 32738]),
(5, [482, 3652, 26896, 32159, 32736]),
(5, [482, 3652, 26896, 32250, 32736]),
(5, [482, 3652, 26911, 32152, 32736]),
(5, [482, 3652, 26911, 32159, 32736]),
(5, [482, 3652, 27920, 32736]),
(5, [482, 3652, 27920, 32736, 32767]),
(5, [482, 3652, 28500, 32152, 32736]),
(5, [482, 3654, 13448, 26896, 32736])
],
#[
(5, [482, 3660, 13448, 26896, 32736]),
(5, [482, 3668, 13448, 26896, 32736]),
(5, [482, 3679, 4070, 13448, 26911]),
(5, [482, 3679, 4070, 13471, 26896]),
(5, [482, 3679, 13448, 16076, 26911]),
(5, [482, 3679, 13448, 26911, 29115]),
(5, [482, 3679, 13471, 26896, 28500]),
(5, [482, 3679, 13471, 26896, 29115]),
(5, [482, 3780, 13448, 26896, 32736]),
(5, [482, 3908, 13448, 26896, 32736]),
(5, [482, 4267, 13448, 26896, 32736]),
(5, [482, 5871, 13448, 16076, 32736]),
(5, [482, 5871, 13448, 28500, 32736]),
(5, [482, 5871, 13448, 29115, 32736]),
(5, [482, 8223, 11844, 13448, 26896]),
(5, [482, 8223, 13448, 16076, 26896])
],
#[
(5, [482, 8223, 13448, 26896, 28500]),
(5, [482, 8223, 13448, 26896, 29115]),
(5, [482, 9216, 9247, 26896, 28500]),
(5, [482, 9216, 26896, 28500, 32736]),
(5, [482, 9247, 13448, 26896, 28500]),
(5, [482, 10271, 13448, 16076, 26896]),
(5, [482, 11844, 13448, 26896, 32736]),
(5, [482, 13440, 16068, 26896, 32736]),
(5, [482, 13440, 26896, 28500, 32736]),
(5, [482, 13440, 26896, 29115, 32736]),
(5, [482, 13448, 16068, 26896, 32736]),
(5, [482, 13448, 16076, 26880, 32736]),
(5, [482, 13448, 16076, 26896, 32256]),
(5, [482, 13448, 16076, 26896, 32738]),
(5, [482, 13448, 16076, 26911, 32736]),
(5, [482, 13448, 16076, 32152, 32736])
],
#[
(5, [482, 13448, 16691, 26896, 32736]),
(5, [482, 13448, 26880, 28484, 32736]),
(5, [482, 13448, 26880, 29115, 32736]),
(5, [482, 13448, 26896, 28484, 32736]),
(5, [482, 13448, 26896, 28500, 32256]),
(5, [482, 13448, 26896, 28500, 32738]),
(5, [482, 13448, 26896, 29115, 32256]),
(5, [482, 13448, 26896, 29115, 32738]),
(5, [482, 13448, 26896, 30139, 32736]),
(5, [482, 13448, 26896, 31163, 32736]),
(5, [482, 13448, 26896, 32256, 32324]),
(5, [482, 13448, 26896, 32732, 32736]),
(5, [482, 13448, 26911, 29115, 32736]),
(5, [482, 13448, 27122, 28500, 32736]),
(5, [482, 13448, 28500, 32152, 32736]),
(5, [482, 13448, 29115, 32152, 32736])
],
#[
(5, [482, 13448, 32152, 32732, 32736]),
(5, [482, 13471, 26896, 28500, 32736]),
(5, [482, 13471, 26896, 29115, 32736]),
(5, [482, 13802, 26896, 28500, 32736]),
(5, [482, 13802, 26896, 29115, 32736]),
(5, [482, 16076, 19319, 26896, 32736]),
(5, [482, 16076, 26896, 32152, 32736]),
(5, [482, 16076, 32152, 32736]),
(5, [482, 16076, 32152, 32736, 32767]),
(5, [482, 19319, 26896, 28500, 32736]),
(5, [482, 19319, 26896, 29115, 32736]),
(5, [482, 26896, 28500, 32152, 32736]),
(5, [482, 26896, 29115, 30139, 32736]),
(5, [482, 26896, 29115, 32152, 32736]),
(5, [482, 26896, 30139, 32736]),
(5, [482, 26896, 30139, 32736, 32767])
],
#[
(5, [482, 26896, 32152, 32732, 32736]),
(5, [482, 28500, 32152, 32736]),
(5, [482, 28500, 32152, 32736, 32767]),
(5, [486, 511, 3652, 13448, 26896]),
(5, [486, 3652, 3679, 13448, 26896]),
(5, [486, 3652, 13448, 26896, 32736]),
(5, [490, 511, 3652, 13448, 26896]),
(5, [490, 511, 3652, 13802, 26896]),
(5, [490, 3652, 13448, 13471, 26896]),
(5, [490, 3652, 13448, 26896, 32736]),
(5, [498, 3652, 13448, 26896, 32736]),
(5, [511, 1024, 1055, 3652, 26896]),
(5, [511, 1024, 1506, 3652, 26896]),
(5, [511, 1024, 3652, 3679, 26896]),
(5, [511, 1024, 3652, 4070, 26896]),
(5, [511, 1024, 3652, 13471, 26896])
],
#[
(5, [511, 1024, 3652, 13802, 26896]),
(5, [511, 1024, 3652, 26896, 32285]),
(5, [511, 1024, 3652, 26896, 32736]),
(5, [511, 1028, 3652, 13471, 26896]),
(5, [511, 1032, 3652, 3679, 26896]),
(5, [511, 1055, 3652, 13448, 26896]),
(5, [511, 1055, 3652, 26896]),
(5, [511, 1055, 3652, 26896, 32767]),
(5, [511, 1088, 3652, 13802, 26896]),
(5, [511, 1152, 3652, 4070, 26896]),
(5, [511, 1506, 3652, 13448, 26896]),
(5, [511, 1506, 3652, 26896]),
(5, [511, 1506, 3652, 26896, 32767]),
(5, [511, 2048, 3652, 13471, 26896]),
(5, [511, 2048, 3652, 13802, 26896]),
(5, [511, 2064, 3652, 13448, 26896])
],
#[
(5, [511, 2079, 3652, 13448, 26896]),
(5, [511, 2304, 3652, 4070, 13448]),
(5, [511, 2304, 3652, 13448]),
(5, [511, 2304, 3652, 13448, 26896]),
(5, [511, 2304, 3652, 13448, 32767]),
(5, [511, 2530, 3652, 13448, 26896]),
(5, [511, 3652, 3668, 13448, 26896]),
(5, [511, 3652, 3679, 5871, 13448]),
(5, [511, 3652, 3679, 13448, 26911]),
(5, [511, 3652, 3679, 13448, 32152]),
(5, [511, 3652, 3679, 13471, 26896]),
(5, [511, 3652, 3679, 13802, 26896]),
(5, [511, 3652, 3679, 13823, 26896]),
(5, [511, 3652, 3679, 19319, 26896]),
(5, [511, 3652, 3679, 26896, 32152]),
(5, [511, 3652, 3908, 13448, 26896])
],
#[
(5, [511, 3652, 4070, 5871, 13448]),
(5, [511, 3652, 4070, 13448, 32152]),
(5, [511, 3652, 4070, 13471, 26896]),
(5, [511, 3652, 4070, 13802, 26896]),
(5, [511, 3652, 4070, 13823, 26896]),
(5, [511, 3652, 4070, 19319, 26896]),
(5, [511, 3652, 4070, 26896, 32152]),
(5, [511, 3652, 4095, 13471, 26896]),
(5, [511, 3652, 4095, 13802, 26896]),
(5, [511, 3652, 5871, 5887, 13448]),
(5, [511, 3652, 5871, 6127, 13448]),
(5, [511, 3652, 5871, 13448, 13471]),
(5, [511, 3652, 5871, 13448, 13802]),
(5, [511, 3652, 5871, 13448, 32285]),
(5, [511, 3652, 5871, 13448, 32736]),
(5, [511, 3652, 5871, 13471])
],
#[
(5, [511, 3652, 5871, 13471, 26896]),
(5, [511, 3652, 5871, 13471, 32767]),
(5, [511, 3652, 5871, 13802]),
(5, [511, 3652, 5871, 13802, 26896]),
(5, [511, 3652, 5871, 13802, 32767]),
(5, [511, 3652, 5887, 13448]),
(5, [511, 3652, 5887, 13448, 26896]),
(5, [511, 3652, 5887, 13448, 32767]),
(5, [511, 3652, 6127, 13448, 26896]),
(5, [511, 3652, 8192, 13471, 26896]),
(5, [511, 3652, 8192, 13802, 26896]),
(5, [511, 3652, 8208, 13448, 26896]),
(5, [511, 3652, 8208, 13471, 26896]),
(5, [511, 3652, 8223, 13448, 26896]),
(5, [511, 3652, 8448, 13448, 26896]),
(5, [511, 3652, 8448, 13802, 26896])
],
#[
(5, [511, 3652, 8674, 13448, 26896]),
(5, [511, 3652, 13320, 26896, 32285]),
(5, [511, 3652, 13440, 26896, 32736]),
(5, [511, 3652, 13448, 13464, 26896]),
(5, [511, 3652, 13448, 13471, 26911]),
(5, [511, 3652, 13448, 13471, 32152]),
(5, [511, 3652, 13448, 13471, 32159]),
(5, [511, 3652, 13448, 13704, 26896]),
(5, [511, 3652, 13448, 13802, 32152]),
(5, [511, 3652, 13448, 16095, 26896]),
(5, [511, 3652, 13448, 16366, 26896]),
(5, [511, 3652, 13448, 18965, 26896]),
(5, [511, 3652, 13448, 19296, 26896]),
(5, [511, 3652, 13448, 26640, 26896]),
(5, [511, 3652, 13448, 26880]),
(5, [511, 3652, 13448, 26880, 26896])
],
#[
(5, [511, 3652, 13448, 26880, 32736]),
(5, [511, 3652, 13448, 26880, 32767]),
(5, [511, 3652, 13448, 26896, 28697]),
(5, [511, 3652, 13448, 26896, 29088]),
(5, [511, 3652, 13448, 26896, 32285]),
(5, [511, 3652, 13448, 26896, 32287]),
(5, [511, 3652, 13448, 26896, 32349]),
(5, [511, 3652, 13448, 26896, 32413]),
(5, [511, 3652, 13448, 26896, 32511]),
(5, [511, 3652, 13448, 26896, 32736]),
(5, [511, 3652, 13448, 26896, 32738]),
(5, [511, 3652, 13448, 26896, 32740]),
(5, [511, 3652, 13448, 26896, 32744]),
(5, [511, 3652, 13448, 26896, 32751]),
(5, [511, 3652, 13448, 26911, 32736]),
(5, [511, 3652, 13448, 32152, 32285])
]
],
#[
#[
(5, [511, 3652, 13448, 32152, 32736]),
(5, [511, 3652, 13464, 26896]),
(5, [511, 3652, 13464, 26896, 32767]),
(5, [511, 3652, 13471, 13802, 26896]),
(5, [511, 3652, 13471, 13823, 26896]),
(5, [511, 3652, 13471, 16076, 26896]),
(5, [511, 3652, 13471, 16095, 26896]),
(5, [511, 3652, 13471, 19296, 26896]),
(5, [511, 3652, 13471, 19319, 26896]),
(5, [511, 3652, 13471, 26896, 26911]),
(5, [511, 3652, 13471, 26896, 27122]),
(5, [511, 3652, 13471, 26896, 27135]),
(5, [511, 3652, 13471, 26896, 28500]),
(5, [511, 3652, 13471, 26896, 29115]),
(5, [511, 3652, 13471, 26896, 32152]),
(5, [511, 3652, 13471, 26896, 32159])
],
#[
(5, [511, 3652, 13471, 26896, 32256]),
(5, [511, 3652, 13471, 26896, 32285]),
(5, [511, 3652, 13471, 26896, 32736]),
(5, [511, 3652, 13471, 26896, 32767]),
(5, [511, 3652, 13471, 26911]),
(5, [511, 3652, 13471, 26911, 32767]),
(5, [511, 3652, 13471, 32152]),
(5, [511, 3652, 13471, 32152, 32767]),
(5, [511, 3652, 13471, 32159]),
(5, [511, 3652, 13471, 32159, 32767]),
(5, [511, 3652, 13704, 26896]),
(5, [511, 3652, 13704, 26896, 32767]),
(5, [511, 3652, 13802, 13823, 26896]),
(5, [511, 3652, 13802, 16076, 26896]),
(5, [511, 3652, 13802, 16366, 26896]),
(5, [511, 3652, 13802, 18965, 26896])
],
#[
(5, [511, 3652, 13802, 19319, 26896]),
(5, [511, 3652, 13802, 26896, 26911]),
(5, [511, 3652, 13802, 26896, 27122]),
(5, [511, 3652, 13802, 26896, 27135]),
(5, [511, 3652, 13802, 26896, 28500]),
(5, [511, 3652, 13802, 26896, 29115]),
(5, [511, 3652, 13802, 26896, 32152]),
(5, [511, 3652, 13802, 26896, 32250]),
(5, [511, 3652, 13802, 26896, 32256]),
(5, [511, 3652, 13802, 26896, 32285]),
(5, [511, 3652, 13802, 26896, 32736]),
(5, [511, 3652, 13802, 26896, 32767]),
(5, [511, 3652, 13823, 26896, 32285]),
(5, [511, 3652, 13823, 26896, 32736]),
(5, [511, 3652, 18965, 26896]),
(5, [511, 3652, 18965, 26896, 32767])
],
#[
(5, [511, 3652, 19296, 26896]),
(5, [511, 3652, 19296, 26896, 32767]),
(5, [511, 3652, 19319, 26896, 32285]),
(5, [511, 3652, 19319, 26896, 32736]),
(5, [511, 3652, 26896, 32152, 32285]),
(5, [511, 3652, 26896, 32152, 32736]),
(5, [511, 3668, 13448, 26896]),
(5, [511, 3668, 13448, 26896, 32767]),
(5, [511, 3679, 13448, 16076, 26896]),
(5, [511, 3679, 13448, 26896, 28500]),
(5, [511, 3679, 13448, 26896, 29115]),
(5, [511, 3908, 13448, 26896]),
(5, [511, 3908, 13448, 26896, 32767]),
(5, [511, 4070, 13448, 16076, 26896]),
(5, [511, 4070, 13448, 26896, 28500]),
(5, [511, 4070, 13448, 26896, 29115])
],
#[
(5, [511, 13448, 13471, 16076, 26896]),
(5, [511, 13448, 13471, 26896, 28500]),
(5, [511, 13448, 13471, 26896, 29115]),
(5, [511, 13448, 13802, 16076, 26896]),
(5, [511, 13448, 13802, 26896, 28500]),
(5, [511, 13448, 13802, 26896, 29115]),
(5, [511, 13448, 16076, 16095, 26896]),
(5, [511, 13448, 16076, 16366, 26896]),
(5, [511, 13448, 16076, 26896, 32285]),
(5, [511, 13448, 16076, 26896, 32736]),
(5, [511, 13448, 26896, 28500, 32285]),
(5, [511, 13448, 26896, 28500, 32736]),
(5, [511, 13448, 26896, 29115, 32285]),
(5, [511, 13448, 26896, 29115, 32736]),
(5, [511, 13471, 26896, 28500]),
(5, [511, 13471, 26896, 28500, 32767])
],
#[
(5, [511, 13471, 26896, 29115]),
(5, [511, 13471, 26896, 29115, 32767]),
(5, [511, 13802, 26896, 28500]),
(5, [511, 13802, 26896, 28500, 32767]),
(5, [511, 13802, 26896, 29115]),
(5, [511, 13802, 26896, 29115, 32767]),
(5, [1024, 1055, 1506, 3652, 26896]),
(5, [1024, 1055, 1535, 3652, 26896]),
(5, [1024, 1055, 3652, 26896, 27122]),
(5, [1024, 1055, 3652, 26896, 32285]),
(5, [1024, 1506, 1535, 3652, 26896]),
(5, [1024, 1506, 3652, 26896, 32736]),
(5, [1024, 3652, 26896, 27122, 32736]),
(5, [1024, 3652, 26896, 32285, 32736]),
(5, [1055, 1506, 3652, 13448, 26896]),
(5, [1055, 1506, 3652, 26896])
],
#[
(5, [1055, 1506, 3652, 26896, 32767]),
(5, [1055, 1535, 3652, 13448, 26896]),
(5, [1055, 1535, 3652, 26896]),
(5, [1055, 1535, 3652, 26896, 32767]),
(5, [1055, 3652, 13448, 26896, 27122]),
(5, [1055, 3652, 13448, 26896, 32285]),
(5, [1055, 3652, 26896, 27122]),
(5, [1055, 3652, 26896, 27122, 32767]),
(5, [1055, 3652, 26896, 32285]),
(5, [1055, 3652, 26896, 32285, 32767]),
(5, [1506, 1535, 3652, 13448, 26896]),
(5, [1506, 1535, 3652, 26896]),
(5, [1506, 1535, 3652, 26896, 32767]),
(5, [1506, 3652, 13448, 26896, 32736]),
(5, [1506, 3652, 26896, 32736]),
(5, [1506, 3652, 26896, 32736, 32767])
],
#[
(5, [2079, 2530, 3652, 13448, 26896]),
(5, [2079, 2559, 3652, 13448, 26896]),
(5, [2079, 3652, 13448, 26896, 27122]),
(5, [2079, 3652, 13448, 26896, 32285]),
(5, [2143, 3652, 13448, 26896, 27122]),
(5, [2530, 2559, 3652, 13448, 26896]),
(5, [2530, 3652, 13448, 26896, 32736]),
(5, [3652, 3679, 13448, 26896, 27135]),
(5, [3652, 3679, 13448, 26896, 32256]),
(5, [3652, 3679, 13448, 26911, 27122]),
(5, [3652, 3679, 13448, 26911, 27135]),
(5, [3652, 3679, 13448, 26911, 32285]),
(5, [3652, 3679, 13471, 26896, 27122]),
(5, [3652, 3679, 13471, 26896, 32285]),
(5, [3652, 4070, 13448, 26896, 32256]),
(5, [3652, 4070, 13802, 26896, 32736])
],
#[
(5, [3652, 5645, 13448, 26896, 32736]),
(5, [3652, 5871, 13448, 27122, 32736]),
(5, [3652, 5871, 13448, 32285, 32736]),
(5, [3652, 8223, 8674, 13448, 26896]),
(5, [3652, 8223, 8703, 13448, 26896]),
(5, [3652, 8223, 13448, 26896, 27122]),
(5, [3652, 8223, 13448, 26896, 32285]),
(5, [3652, 8351, 13448, 26896, 27122]),
(5, [3652, 8674, 8703, 13448, 26896]),
(5, [3652, 8674, 13448, 26896, 32736]),
(5, [3652, 13320, 26896, 32285, 32736]),
(5, [3652, 13440, 26896, 27122, 32736]),
(5, [3652, 13440, 26896, 32285, 32736]),
(5, [3652, 13448, 13471, 26896, 27135]),
(5, [3652, 13448, 13471, 26896, 32256]),
(5, [3652, 13448, 13471, 26911, 27122])
],
#[
(5, [3652, 13448, 13802, 26896, 32256]),
(5, [3652, 13448, 26880, 27106, 32736]),
(5, [3652, 13448, 26880, 27122, 32736]),
(5, [3652, 13448, 26880, 32285, 32736]),
(5, [3652, 13448, 26896, 27104, 32736]),
(5, [3652, 13448, 26896, 27106, 32736]),
(5, [3652, 13448, 26896, 27120, 32736]),
(5, [3652, 13448, 26896, 27122, 32738]),
(5, [3652, 13448, 26896, 27135, 32736]),
(5, [3652, 13448, 26896, 32256, 32285]),
(5, [3652, 13448, 26896, 32256, 32287]),
(5, [3652, 13448, 26896, 32256, 32736]),
(5, [3652, 13448, 26896, 32256, 32738]),
(5, [3652, 13448, 26896, 32285, 32738]),
(5, [3652, 13448, 26896, 32287, 32736]),
(5, [3652, 13448, 26896, 32541, 32736])
],
#[
(5, [3652, 13448, 26911, 27122, 32736]),
(5, [3652, 13448, 26911, 27135, 32736]),
(5, [3652, 13448, 26911, 32285, 32736]),
(5, [3652, 13448, 27122, 28500, 32736]),
(5, [3652, 13448, 32152, 32285, 32736]),
(5, [3652, 13471, 26896, 27122, 32736]),
(5, [3652, 13471, 26896, 32256]),
(5, [3652, 13471, 26896, 32256, 32767]),
(5, [3652, 13471, 26896, 32285, 32736]),
(5, [3652, 13802, 26896, 27122, 32736]),
(5, [3652, 13802, 26896, 32256]),
(5, [3652, 13802, 26896, 32256, 32767]),
(5, [3652, 13802, 26896, 32285, 32736]),
(5, [3652, 19319, 26896, 27122, 32736]),
(5, [3652, 19319, 26896, 32285, 32736]),
(5, [3652, 26896, 27122, 32152, 32736])
],
#[
(5, [3652, 26896, 27122, 32250, 32736]),
(5, [3652, 26896, 32152, 32285, 32736]),
(5, [13448, 16076, 26896, 27122, 32736]),
(5, [13448, 16076, 26896, 32285, 32736]),
(5, [13448, 26896, 27122, 28500, 32736]),
(5, [13448, 26896, 27122, 29115, 32736]),
(5, [13448, 26896, 28500, 32285, 32736]),
(5, [13448, 26896, 29115, 32285, 32736]),
(5, [13448, 27122, 28500, 32736]),
(5, [13448, 27122, 28500, 32736, 32767]),
(6, [0, 16, 511, 3652, 13448, 26896]),
(6, [0, 29, 482, 3652, 13448, 26896]),
(6, [0, 29, 3652, 13448, 26896, 32285]),
(6, [0, 31, 68, 482, 13448, 26896]),
(6, [0, 31, 68, 511, 13448, 26896]),
(6, [0, 31, 128, 482, 3652, 32152])
],
#[
(6, [0, 31, 192, 3652, 13448, 26896]),
(6, [0, 31, 192, 13448, 16076, 26896]),
(6, [0, 31, 226, 3652, 5871, 13448]),
(6, [0, 31, 226, 3652, 13448, 26896]),
(6, [0, 31, 256, 482, 3652, 32152]),
(6, [0, 31, 480, 3652, 13448, 26896]),
(6, [0, 31, 482, 615, 3652, 13448]),
(6, [0, 31, 482, 615, 3652, 26896]),
(6, [0, 31, 482, 1024, 3652, 5871]),
(6, [0, 31, 482, 1024, 3652, 26896]),
(6, [0, 31, 482, 1024, 3652, 26911]),
(6, [0, 31, 482, 1024, 3652, 27920]),
(6, [0, 31, 482, 1024, 26896, 28500]),
(6, [0, 31, 482, 1024, 26896, 29115]),
(6, [0, 31, 482, 1028, 3652, 26896]),
(6, [0, 31, 482, 1032, 3652, 26896])
],
#[
(6, [0, 31, 482, 1055, 3652, 26896]),
(6, [0, 31, 482, 1088, 3652, 26896]),
(6, [0, 31, 482, 1152, 3652, 26896]),
(6, [0, 31, 482, 1506, 3652, 26896]),
(6, [0, 31, 482, 1604, 5871, 13448]),
(6, [0, 31, 482, 1604, 13448, 26896]),
(6, [0, 31, 482, 2304, 3652, 13448]),
(6, [0, 31, 482, 2628, 3652, 26896]),
(6, [0, 31, 482, 2628, 13448, 26896]),
(6, [0, 31, 482, 2628, 19319, 26896]),
(6, [0, 31, 482, 2628, 26896]),
(6, [0, 31, 482, 2628, 26896, 32767]),
(6, [0, 31, 482, 3072, 3652, 26896]),
(6, [0, 31, 482, 3652, 5256, 5871]),
(6, [0, 31, 482, 3652, 5256, 26896]),
(6, [0, 31, 482, 3652, 5856, 13448])
],
#[
(6, [0, 31, 482, 3652, 5871, 13448]),
(6, [0, 31, 482, 3652, 5871, 13471]),
(6, [0, 31, 482, 3652, 5871, 13802]),
(6, [0, 31, 482, 3652, 5871, 19319]),
(6, [0, 31, 482, 3652, 5871, 32152]),
(6, [0, 31, 482, 3652, 5887, 13448]),
(6, [0, 31, 482, 3652, 9216, 26896]),
(6, [0, 31, 482, 3652, 13320, 26896]),
(6, [0, 31, 482, 3652, 13440, 26896]),
(6, [0, 31, 482, 3652, 13448, 14063]),
(6, [0, 31, 482, 3652, 13448, 18704]),
(6, [0, 31, 482, 3652, 13448, 26880]),
(6, [0, 31, 482, 3652, 13448, 26896]),
(6, [0, 31, 482, 3652, 13448, 26898]),
(6, [0, 31, 482, 3652, 13448, 26900]),
(6, [0, 31, 482, 3652, 13448, 26904])
],
#[
(6, [0, 31, 482, 3652, 13448, 26911]),
(6, [0, 31, 482, 3652, 13448, 26960]),
(6, [0, 31, 482, 3652, 13448, 27024]),
(6, [0, 31, 482, 3652, 13448, 27920]),
(6, [0, 31, 482, 3652, 13448, 32152]),
(6, [0, 31, 482, 3652, 13448, 32159]),
(6, [0, 31, 482, 3652, 13450, 26896]),
(6, [0, 31, 482, 3652, 13452, 26896]),
(6, [0, 31, 482, 3652, 13464, 26896]),
(6, [0, 31, 482, 3652, 13471, 26896]),
(6, [0, 31, 482, 3652, 13471, 26911]),
(6, [0, 31, 482, 3652, 13471, 32152]),
(6, [0, 31, 482, 3652, 13471, 32159]),
(6, [0, 31, 482, 3652, 13512, 26896]),
(6, [0, 31, 482, 3652, 13704, 26896]),
(6, [0, 31, 482, 3652, 13802, 26896])
]
],
#[
#[
(6, [0, 31, 482, 3652, 13802, 26911]),
(6, [0, 31, 482, 3652, 13823, 26896]),
(6, [0, 31, 482, 3652, 15496, 26896]),
(6, [0, 31, 482, 3652, 16076, 32152]),
(6, [0, 31, 482, 3652, 18704, 19319]),
(6, [0, 31, 482, 3652, 18965, 26896]),
(6, [0, 31, 482, 3652, 19296, 26896]),
(6, [0, 31, 482, 3652, 19319, 26896]),
(6, [0, 31, 482, 3652, 19319, 26911]),
(6, [0, 31, 482, 3652, 19319, 32152]),
(6, [0, 31, 482, 3652, 19327, 26896]),
(6, [0, 31, 482, 3652, 19447, 26896]),
(6, [0, 31, 482, 3652, 26896, 27511]),
(6, [0, 31, 482, 3652, 26896, 27920]),
(6, [0, 31, 482, 3652, 26896, 30139]),
(6, [0, 31, 482, 3652, 26896, 31743])
],
#[
(6, [0, 31, 482, 3652, 26896, 32152]),
(6, [0, 31, 482, 3652, 26896, 32159]),
(6, [0, 31, 482, 3652, 26896, 32250]),
(6, [0, 31, 482, 3652, 26911, 32152]),
(6, [0, 31, 482, 3652, 26911, 32159]),
(6, [0, 31, 482, 3652, 27920]),
(6, [0, 31, 482, 3652, 27920, 32767]),
(6, [0, 31, 482, 3652, 28500, 32152]),
(6, [0, 31, 482, 3654, 13448, 26896]),
(6, [0, 31, 482, 3660, 13448, 26896]),
(6, [0, 31, 482, 3668, 13448, 26896]),
(6, [0, 31, 482, 3780, 13448, 26896]),
(6, [0, 31, 482, 3908, 13448, 26896]),
(6, [0, 31, 482, 4267, 13448, 26896]),
(6, [0, 31, 482, 5871, 13448, 16076]),
(6, [0, 31, 482, 5871, 13448, 28500])
],
#[
(6, [0, 31, 482, 5871, 13448, 29115]),
(6, [0, 31, 482, 9216, 26896, 28500]),
(6, [0, 31, 482, 11844, 13448, 26896]),
(6, [0, 31, 482, 13448, 16076, 26896]),
(6, [0, 31, 482, 13448, 16076, 26911]),
(6, [0, 31, 482, 13448, 16076, 32152]),
(6, [0, 31, 482, 13448, 16691, 26896]),
(6, [0, 31, 482, 13448, 26896, 28500]),
(6, [0, 31, 482, 13448, 26896, 29115]),
(6, [0, 31, 482, 13448, 26896, 30139]),
(6, [0, 31, 482, 13448, 26896, 31163]),
(6, [0, 31, 482, 13448, 26896, 32732]),
(6, [0, 31, 482, 13448, 26911, 29115]),
(6, [0, 31, 482, 13448, 27122, 28500]),
(6, [0, 31, 482, 13448, 28500, 32152]),
(6, [0, 31, 482, 13448, 29115, 32152])
],
#[
(6, [0, 31, 482, 13448, 32152, 32732]),
(6, [0, 31, 482, 13471, 26896, 28500]),
(6, [0, 31, 482, 13471, 26896, 29115]),
(6, [0, 31, 482, 13802, 26896, 28500]),
(6, [0, 31, 482, 13802, 26896, 29115]),
(6, [0, 31, 482, 16076, 19319, 26896]),
(6, [0, 31, 482, 16076, 26896, 32152]),
(6, [0, 31, 482, 16076, 32152]),
(6, [0, 31, 482, 16076, 32152, 32767]),
(6, [0, 31, 482, 19319, 26896, 28500]),
(6, [0, 31, 482, 19319, 26896, 29115]),
(6, [0, 31, 482, 26896, 28500, 32152]),
(6, [0, 31, 482, 26896, 29115, 30139]),
(6, [0, 31, 482, 26896, 29115, 32152]),
(6, [0, 31, 482, 26896, 30139]),
(6, [0, 31, 482, 26896, 30139, 32767])
],
#[
(6, [0, 31, 482, 26896, 32152, 32732]),
(6, [0, 31, 482, 28500, 32152]),
(6, [0, 31, 482, 28500, 32152, 32767]),
(6, [0, 31, 486, 3652, 13448, 26896]),
(6, [0, 31, 490, 3652, 13448, 26896]),
(6, [0, 31, 498, 3652, 13448, 26896]),
(6, [0, 31, 511, 1024, 3652, 26896]),
(6, [0, 31, 511, 3652, 5871, 13448]),
(6, [0, 31, 511, 3652, 13448, 26896]),
(6, [0, 31, 511, 3652, 13448, 26911]),
(6, [0, 31, 511, 3652, 13448, 32152]),
(6, [0, 31, 511, 3652, 13471, 26896]),
(6, [0, 31, 511, 3652, 13802, 26896]),
(6, [0, 31, 511, 3652, 13823, 26896]),
(6, [0, 31, 511, 3652, 19319, 26896]),
(6, [0, 31, 511, 3652, 26896, 32152])
],
#[
(6, [0, 31, 511, 13448, 16076, 26896]),
(6, [0, 31, 511, 13448, 26896, 28500]),
(6, [0, 31, 511, 13448, 26896, 29115]),
(6, [0, 31, 1024, 1506, 3652, 26896]),
(6, [0, 31, 1024, 3652, 26896, 27122]),
(6, [0, 31, 1024, 3652, 26896, 32285]),
(6, [0, 31, 1506, 3652, 13448, 26896]),
(6, [0, 31, 1506, 3652, 26896]),
(6, [0, 31, 1506, 3652, 26896, 32767]),
(6, [0, 31, 2530, 3652, 13448, 26896]),
(6, [0, 31, 3652, 4070, 13802, 26896]),
(6, [0, 31, 3652, 5645, 13448, 26896]),
(6, [0, 31, 3652, 5871, 13448, 27122]),
(6, [0, 31, 3652, 5871, 13448, 32285]),
(6, [0, 31, 3652, 8674, 13448, 26896]),
(6, [0, 31, 3652, 13320, 26896, 32285])
],
#[
(6, [0, 31, 3652, 13448, 26896, 27122]),
(6, [0, 31, 3652, 13448, 26896, 27135]),
(6, [0, 31, 3652, 13448, 26896, 32256]),
(6, [0, 31, 3652, 13448, 26896, 32285]),
(6, [0, 31, 3652, 13448, 26896, 32287]),
(6, [0, 31, 3652, 13448, 26896, 32541]),
(6, [0, 31, 3652, 13448, 26911, 27122]),
(6, [0, 31, 3652, 13448, 26911, 27135]),
(6, [0, 31, 3652, 13448, 26911, 32285]),
(6, [0, 31, 3652, 13448, 27122, 28500]),
(6, [0, 31, 3652, 13448, 32152, 32285]),
(6, [0, 31, 3652, 13471, 26896, 27122]),
(6, [0, 31, 3652, 13471, 26896, 32285]),
(6, [0, 31, 3652, 13802, 26896, 27122]),
(6, [0, 31, 3652, 13802, 26896, 32285]),
(6, [0, 31, 3652, 19319, 26896, 27122])
],
#[
(6, [0, 31, 3652, 19319, 26896, 32285]),
(6, [0, 31, 3652, 26896, 27122, 32152]),
(6, [0, 31, 3652, 26896, 27122, 32250]),
(6, [0, 31, 3652, 26896, 32152, 32285]),
(6, [0, 31, 13448, 16076, 26896, 27122]),
(6, [0, 31, 13448, 16076, 26896, 32285]),
(6, [0, 31, 13448, 26896, 27122, 28500]),
(6, [0, 31, 13448, 26896, 27122, 29115]),
(6, [0, 31, 13448, 26896, 28500, 32285]),
(6, [0, 31, 13448, 26896, 29115, 32285]),
(6, [0, 31, 13448, 27122, 28500]),
(6, [0, 31, 13448, 27122, 28500, 32767]),
(6, [0, 68, 482, 511, 13448, 26896]),
(6, [0, 95, 482, 3652, 13448, 26896]),
(6, [0, 159, 482, 3652, 13448, 26896]),
(6, [0, 256, 511, 3652, 13448, 26896])
],
#[
(6, [0, 287, 482, 3652, 13448, 26896]),
(6, [0, 480, 3652, 13448, 26896, 32736]),
(6, [0, 482, 511, 1024, 3652, 26896]),
(6, [0, 482, 511, 3652, 5871, 13448]),
(6, [0, 482, 511, 3652, 13448, 26896]),
(6, [0, 482, 511, 3652, 13448, 32152]),
(6, [0, 482, 511, 3652, 13471, 26896]),
(6, [0, 482, 511, 3652, 13802, 26896]),
(6, [0, 482, 511, 3652, 13823, 26896]),
(6, [0, 482, 511, 3652, 19319, 26896]),
(6, [0, 482, 511, 3652, 26896, 32152]),
(6, [0, 482, 511, 13448, 16076, 26896]),
(6, [0, 482, 511, 13448, 26896, 28500]),
(6, [0, 482, 511, 13448, 26896, 29115]),
(6, [0, 482, 1024, 1055, 3652, 26896]),
(6, [0, 482, 1024, 3652, 26896, 32736])
],
#[
(6, [0, 482, 1055, 3652, 13448, 26896]),
(6, [0, 482, 1055, 3652, 26896]),
(6, [0, 482, 1055, 3652, 26896, 32767]),
(6, [0, 482, 2079, 3652, 13448, 26896]),
(6, [0, 482, 3652, 3679, 13448, 26911]),
(6, [0, 482, 3652, 3679, 13471, 26896]),
(6, [0, 482, 3652, 5871, 13448, 32736]),
(6, [0, 482, 3652, 8223, 13448, 26896]),
(6, [0, 482, 3652, 13440, 26896, 32736]),
(6, [0, 482, 3652, 13448, 26880, 32736]),
(6, [0, 482, 3652, 13448, 26896, 32256]),
(6, [0, 482, 3652, 13448, 26896, 32736]),
(6, [0, 482, 3652, 13448, 26896, 32738]),
(6, [0, 482, 3652, 13448, 26911, 32736]),
(6, [0, 482, 3652, 13448, 32152, 32736]),
(6, [0, 482, 3652, 13471, 26896, 32736])
],
#[
(6, [0, 482, 3652, 13802, 26896, 32736]),
(6, [0, 482, 3652, 19319, 26896, 32736]),
(6, [0, 482, 3652, 26896, 32152, 32736]),
(6, [0, 482, 13448, 16076, 26896, 32736]),
(6, [0, 482, 13448, 26896, 28500, 32736]),
(6, [0, 482, 13448, 26896, 29115, 32736]),
(6, [0, 511, 3652, 3679, 13448, 26896]),
(6, [0, 511, 3652, 4070, 13448, 26896]),
(6, [0, 511, 3652, 13448, 13471, 26896]),
(6, [0, 511, 3652, 13448, 13802, 26896]),
(6, [0, 511, 3652, 13448, 26896, 32285]),
(6, [0, 511, 3652, 13448, 26896, 32736]),
(6, [0, 511, 3652, 13471, 26896]),
(6, [0, 511, 3652, 13471, 26896, 32767]),
(6, [0, 511, 3652, 13802, 26896]),
(6, [0, 511, 3652, 13802, 26896, 32767])
],
#[
(6, [0, 3652, 13448, 26896, 27122, 32736]),
(6, [0, 3652, 13448, 26896, 32285, 32736]),
(6, [2, 31, 482, 1024, 3652, 26896]),
(6, [2, 31, 482, 3652, 5871, 13448]),
(6, [2, 31, 482, 3652, 13448, 26898]),
(6, [2, 31, 482, 3652, 13448, 26911]),
(6, [2, 31, 482, 3652, 13448, 32152]),
(6, [2, 31, 482, 3652, 13450, 26896]),
(6, [2, 31, 482, 3652, 13471, 26896]),
(6, [2, 31, 482, 3652, 13802, 26896]),
(6, [2, 31, 482, 3652, 19319, 26896]),
(6, [2, 31, 482, 3652, 26896, 32152]),
(6, [2, 31, 482, 3654, 13448, 26896]),
(6, [2, 31, 482, 13448, 16076, 26896]),
(6, [2, 31, 482, 13448, 26896, 28500]),
(6, [2, 31, 482, 13448, 26896, 29115])
],
#[
(6, [2, 31, 511, 3652, 13448, 26896]),
(6, [2, 31, 3652, 13448, 26896, 27122]),
(6, [2, 31, 3652, 13448, 26896, 32285]),
(6, [2, 482, 511, 3652, 13448, 26896]),
(6, [2, 482, 3652, 13448, 26896, 32736]),
(6, [4, 31, 64, 482, 13448, 26896]),
(6, [4, 31, 482, 1024, 3652, 26896]),
(6, [4, 31, 482, 3652, 5871, 13448]),
(6, [4, 31, 482, 3652, 13448, 26900]),
(6, [4, 31, 482, 3652, 13448, 26911]),
(6, [4, 31, 482, 3652, 13448, 32152]),
(6, [4, 31, 482, 3652, 13452, 26896]),
(6, [4, 31, 482, 3652, 13471, 26896]),
(6, [4, 31, 482, 3652, 13802, 26896]),
(6, [4, 31, 482, 3652, 19319, 26896]),
(6, [4, 31, 482, 3652, 26896, 32152])
],
#[
(6, [4, 31, 482, 3679, 13448, 26896]),
(6, [4, 31, 482, 13448, 16076, 26896]),
(6, [4, 31, 482, 13448, 26896, 28500]),
(6, [4, 31, 482, 13448, 26896, 29115]),
(6, [4, 31, 486, 3652, 13448, 26896]),
(6, [4, 31, 511, 3652, 13448, 26896]),
(6, [4, 31, 3652, 13448, 26896, 27122]),
(6, [4, 31, 3652, 13448, 26896, 32285]),
(6, [4, 482, 511, 3652, 13448, 26896]),
(6, [4, 482, 3652, 3679, 13448, 26896]),
(6, [4, 482, 3652, 13448, 26896, 32736]),
(6, [6, 31, 482, 3652, 13448, 26896]),
(6, [8, 31, 482, 1024, 3652, 26896]),
(6, [8, 31, 482, 3652, 5871, 13448]),
(6, [8, 31, 482, 3652, 13448, 26904]),
(6, [8, 31, 482, 3652, 13448, 26911])
],
#[
(6, [8, 31, 482, 3652, 13448, 32152]),
(6, [8, 31, 482, 3652, 13471, 26896]),
(6, [8, 31, 482, 3652, 13802, 26896]),
(6, [8, 31, 482, 3652, 19319, 26896]),
(6, [8, 31, 482, 3652, 26896, 32152]),
(6, [8, 31, 482, 3660, 13448, 26896]),
(6, [8, 31, 482, 13448, 16076, 26896]),
(6, [8, 31, 482, 13448, 26896, 28500]),
(6, [8, 31, 482, 13448, 26896, 29115]),
(6, [8, 31, 490, 3652, 13448, 26896]),
(6, [8, 31, 511, 3652, 13448, 26896]),
(6, [8, 31, 3652, 13448, 26896, 27122]),
(6, [8, 31, 3652, 13448, 26896, 32285]),
(6, [8, 482, 511, 3652, 13448, 26896]),
(6, [8, 482, 3652, 13448, 13471, 26896]),
(6, [8, 482, 3652, 13448, 26896, 32736])
],
#[
(6, [10, 31, 482, 3652, 13448, 26896]),
(6, [10, 31, 482, 3652, 13802, 26896]),
(6, [12, 31, 482, 3652, 13448, 26896]),
(6, [12, 31, 482, 13448, 16076, 26896]),
(6, [15, 31, 482, 3652, 5871, 13448]),
(6, [15, 31, 482, 3652, 13448, 26896]),
(6, [16, 31, 482, 1024, 3652, 26896]),
(6, [16, 31, 482, 3652, 5871, 13448]),
(6, [16, 31, 482, 3652, 13448, 26911]),
(6, [16, 31, 482, 3652, 13448, 32152]),
(6, [16, 31, 482, 3652, 13464, 26896]),
(6, [16, 31, 482, 3652, 13471, 26896]),
(6, [16, 31, 482, 3652, 13802, 26896]),
(6, [16, 31, 482, 3652, 19319, 26896]),
(6, [16, 31, 482, 3652, 26896, 32152]),
(6, [16, 31, 482, 3668, 13448, 26896])
]
],
#[
#[
(6, [16, 31, 482, 13448, 16076, 26896]),
(6, [16, 31, 482, 13448, 26896, 28500]),
(6, [16, 31, 482, 13448, 26896, 29115]),
(6, [16, 31, 498, 3652, 13448, 26896]),
(6, [16, 31, 511, 3652, 13448, 26896]),
(6, [16, 31, 3652, 13448, 26896, 27122]),
(6, [16, 31, 3652, 13448, 26896, 32285]),
(6, [16, 482, 511, 3652, 13448, 26896]),
(6, [16, 482, 3652, 13448, 26896, 26911]),
(6, [16, 482, 3652, 13448, 26896, 32736]),
(6, [16, 511, 3652, 13448, 26896]),
(6, [16, 511, 3652, 13448, 26896, 32767]),
(6, [18, 31, 482, 3652, 13448, 26896]),
(6, [18, 31, 3652, 13448, 26896, 27122]),
(6, [20, 31, 482, 3652, 13448, 26896]),
(6, [20, 31, 482, 13448, 26896, 28500])
],
#[
(6, [23, 31, 482, 3652, 13448, 26896]),
(6, [23, 31, 482, 3652, 19319, 26896]),
(6, [24, 31, 482, 3652, 13448, 26896]),
(6, [24, 31, 482, 3652, 13448, 32152]),
(6, [24, 31, 482, 3652, 26896, 32152]),
(6, [27, 31, 482, 3652, 13448, 26896]),
(6, [27, 31, 482, 13448, 26896, 29115]),
(6, [29, 31, 482, 3652, 13448, 26896]),
(6, [29, 31, 3652, 13448, 26896, 32285]),
(6, [29, 482, 3652, 13448, 26896]),
(6, [29, 482, 3652, 13448, 26896, 32285]),
(6, [29, 482, 3652, 13448, 26896, 32767]),
(6, [29, 3652, 13448, 26896, 32285]),
(6, [29, 3652, 13448, 26896, 32285, 32767]),
(6, [31, 64, 128, 3652, 13448, 26896]),
(6, [31, 64, 482, 1024, 3652, 26896])
],
#[
(6, [31, 64, 482, 3652, 5871, 13448]),
(6, [31, 64, 482, 3652, 13448, 26911]),
(6, [31, 64, 482, 3652, 13448, 26960]),
(6, [31, 64, 482, 3652, 13448, 32152]),
(6, [31, 64, 482, 3652, 13471, 26896]),
(6, [31, 64, 482, 3652, 13512, 26896]),
(6, [31, 64, 482, 3652, 13802, 26896]),
(6, [31, 64, 482, 3652, 19319, 26896]),
(6, [31, 64, 482, 3652, 26896, 32152]),
(6, [31, 64, 482, 4070, 13448, 26896]),
(6, [31, 64, 482, 13448, 16076, 26896]),
(6, [31, 64, 482, 13448, 26896, 28500]),
(6, [31, 64, 482, 13448, 26896, 29115]),
(6, [31, 64, 511, 3652, 13448, 26896]),
(6, [31, 64, 3652, 4070, 13448, 26896]),
(6, [31, 64, 3652, 13448, 26896, 27122])
],
#[
(6, [31, 64, 3652, 13448, 26896, 32285]),
(6, [31, 66, 482, 3652, 13448, 26896]),
(6, [31, 68, 482, 511, 13448, 26896]),
(6, [31, 68, 482, 3652, 13448, 26896]),
(6, [31, 68, 482, 13448, 26896]),
(6, [31, 68, 482, 13448, 26896, 32767]),
(6, [31, 68, 511, 3652, 13448, 26896]),
(6, [31, 68, 511, 13448, 26896]),
(6, [31, 68, 511, 13448, 26896, 32767]),
(6, [31, 95, 482, 3652, 13448, 26896]),
(6, [31, 128, 482, 1024, 3652, 26896]),
(6, [31, 128, 482, 3652, 5871, 13448]),
(6, [31, 128, 482, 3652, 13448, 26911]),
(6, [31, 128, 482, 3652, 13448, 27024]),
(6, [31, 128, 482, 3652, 13448, 32152]),
(6, [31, 128, 482, 3652, 13471, 26896])
],
#[
(6, [31, 128, 482, 3652, 13802, 26896]),
(6, [31, 128, 482, 3652, 19319, 26896]),
(6, [31, 128, 482, 3652, 26896, 32152]),
(6, [31, 128, 482, 3652, 32152]),
(6, [31, 128, 482, 3652, 32152, 32767]),
(6, [31, 128, 482, 3780, 13448, 26896]),
(6, [31, 128, 482, 13448, 16076, 26896]),
(6, [31, 128, 482, 13448, 26896, 28500]),
(6, [31, 128, 482, 13448, 26896, 29115]),
(6, [31, 128, 511, 3652, 13448, 26896]),
(6, [31, 128, 3652, 13448, 13802, 26896]),
(6, [31, 128, 3652, 13448, 26896, 27122]),
(6, [31, 128, 3652, 13448, 26896, 32285]),
(6, [31, 130, 482, 3652, 13448, 26896]),
(6, [31, 130, 482, 3652, 13471, 26896]),
(6, [31, 136, 482, 3652, 13448, 26896])
],
#[
(6, [31, 136, 511, 3652, 13448, 26896]),
(6, [31, 159, 482, 3652, 13448, 26896]),
(6, [31, 192, 482, 3652, 13448, 26896]),
(6, [31, 192, 482, 13448, 16076, 26896]),
(6, [31, 192, 3652, 13448, 16076, 26896]),
(6, [31, 192, 3652, 13448, 26896]),
(6, [31, 192, 3652, 13448, 26896, 32767]),
(6, [31, 192, 13448, 16076, 26896]),
(6, [31, 192, 13448, 16076, 26896, 32767]),
(6, [31, 226, 482, 3652, 5871, 13448]),
(6, [31, 226, 482, 3652, 13448, 26896]),
(6, [31, 226, 3652, 5871, 13448]),
(6, [31, 226, 3652, 5871, 13448, 26896]),
(6, [31, 226, 3652, 5871, 13448, 32767]),
(6, [31, 226, 3652, 13448, 26896]),
(6, [31, 226, 3652, 13448, 26896, 32767])
],
#[
(6, [31, 256, 482, 1024, 3652, 26896]),
(6, [31, 256, 482, 2048, 3652, 13448]),
(6, [31, 256, 482, 3652, 5871, 13448]),
(6, [31, 256, 482, 3652, 13448, 26911]),
(6, [31, 256, 482, 3652, 13448, 27122]),
(6, [31, 256, 482, 3652, 13448, 32152]),
(6, [31, 256, 482, 3652, 13471, 26896]),
(6, [31, 256, 482, 3652, 13704, 26896]),
(6, [31, 256, 482, 3652, 13802, 26896]),
(6, [31, 256, 482, 3652, 19319, 26896]),
(6, [31, 256, 482, 3652, 26896, 32152]),
(6, [31, 256, 482, 3652, 32152]),
(6, [31, 256, 482, 3652, 32152, 32767]),
(6, [31, 256, 482, 3908, 13448, 26896]),
(6, [31, 256, 482, 13448, 16076, 26896]),
(6, [31, 256, 482, 13448, 26896, 28500])
],
#[
(6, [31, 256, 482, 13448, 26896, 29115]),
(6, [31, 256, 511, 3652, 13448, 26896]),
(6, [31, 256, 3652, 13448, 26896, 27122]),
(6, [31, 256, 3652, 13448, 26896, 32285]),
(6, [31, 258, 482, 3652, 13448, 26896]),
(6, [31, 258, 482, 3652, 13448, 26911]),
(6, [31, 272, 482, 3652, 13448, 26896]),
(6, [31, 272, 511, 3652, 13448, 26896]),
(6, [31, 287, 482, 3652, 13448, 26896]),
(6, [31, 320, 482, 3652, 13448, 26896]),
(6, [31, 320, 482, 13448, 26896, 28500]),
(6, [31, 354, 482, 3652, 13448, 26896]),
(6, [31, 354, 482, 3652, 19319, 26896]),
(6, [31, 384, 482, 3652, 13448, 26896]),
(6, [31, 384, 482, 3652, 13448, 32152]),
(6, [31, 384, 482, 3652, 26896, 32152])
],
#[
(6, [31, 418, 482, 3652, 13448, 26896]),
(6, [31, 418, 482, 13448, 26896, 29115]),
(6, [31, 480, 482, 3652, 13448, 26896]),
(6, [31, 480, 3652, 13448, 26896]),
(6, [31, 480, 3652, 13448, 26896, 32736]),
(6, [31, 480, 3652, 13448, 26896, 32767]),
(6, [31, 482, 486, 3652, 13448, 26896]),
(6, [31, 482, 490, 3652, 13448, 26896]),
(6, [31, 482, 498, 3652, 13448, 26896]),
(6, [31, 482, 511, 1024, 3652, 26896]),
(6, [31, 482, 511, 3652, 5871, 13448]),
(6, [31, 482, 511, 3652, 13448, 26911]),
(6, [31, 482, 511, 3652, 13448, 32152]),
(6, [31, 482, 511, 3652, 13471, 26896]),
(6, [31, 482, 511, 3652, 13802, 26896]),
(6, [31, 482, 511, 3652, 13823, 26896])
],
#[
(6, [31, 482, 511, 3652, 19319, 26896]),
(6, [31, 482, 511, 3652, 26896, 32152]),
(6, [31, 482, 511, 13448, 16076, 26896]),
(6, [31, 482, 511, 13448, 26896, 28500]),
(6, [31, 482, 511, 13448, 26896, 29115]),
(6, [31, 482, 615, 3652, 13448]),
(6, [31, 482, 615, 3652, 13448, 26896]),
(6, [31, 482, 615, 3652, 13448, 32152]),
(6, [31, 482, 615, 3652, 13448, 32767]),
(6, [31, 482, 615, 3652, 26896]),
(6, [31, 482, 615, 3652, 26896, 32152]),
(6, [31, 482, 615, 3652, 26896, 32767]),
(6, [31, 482, 1024, 1055, 3652, 26896]),
(6, [31, 482, 1024, 1506, 3652, 26896]),
(6, [31, 482, 1024, 2048, 3652, 26896]),
(6, [31, 482, 1024, 3652, 3679, 26896])
],
#[
(6, [31, 482, 1024, 3652, 4070, 26896]),
(6, [31, 482, 1024, 3652, 5871]),
(6, [31, 482, 1024, 3652, 5871, 13448]),
(6, [31, 482, 1024, 3652, 5871, 26896]),
(6, [31, 482, 1024, 3652, 5871, 32767]),
(6, [31, 482, 1024, 3652, 8192, 26896]),
(6, [31, 482, 1024, 3652, 13448, 26911]),
(6, [31, 482, 1024, 3652, 13448, 27920]),
(6, [31, 482, 1024, 3652, 13448, 32152]),
(6, [31, 482, 1024, 3652, 13471, 26896]),
(6, [31, 482, 1024, 3652, 13802, 26896]),
(6, [31, 482, 1024, 3652, 16076, 26896]),
(6, [31, 482, 1024, 3652, 19319, 26896]),
(6, [31, 482, 1024, 3652, 26896, 26911]),
(6, [31, 482, 1024, 3652, 26896, 27122]),
(6, [31, 482, 1024, 3652, 26896, 27920])
],
#[
(6, [31, 482, 1024, 3652, 26896, 28500]),
(6, [31, 482, 1024, 3652, 26896, 29115]),
(6, [31, 482, 1024, 3652, 26896, 31743]),
(6, [31, 482, 1024, 3652, 26896, 32152]),
(6, [31, 482, 1024, 3652, 26896, 32285]),
(6, [31, 482, 1024, 3652, 26896, 32736]),
(6, [31, 482, 1024, 3652, 26896, 32767]),
(6, [31, 482, 1024, 3652, 26911]),
(6, [31, 482, 1024, 3652, 26911, 32767]),
(6, [31, 482, 1024, 3652, 27920]),
(6, [31, 482, 1024, 3652, 27920, 32767]),
(6, [31, 482, 1024, 13448, 16076, 26896]),
(6, [31, 482, 1024, 13448, 26896, 28500]),
(6, [31, 482, 1024, 13448, 26896, 29115]),
(6, [31, 482, 1024, 26896, 28500]),
(6, [31, 482, 1024, 26896, 28500, 32767])
],
#[
(6, [31, 482, 1024, 26896, 29115]),
(6, [31, 482, 1024, 26896, 29115, 32767]),
(6, [31, 482, 1028, 3652, 13448, 26896]),
(6, [31, 482, 1028, 3652, 13471, 26896]),
(6, [31, 482, 1028, 3652, 26896]),
(6, [31, 482, 1028, 3652, 26896, 32767]),
(6, [31, 482, 1032, 3652, 3679, 26896]),
(6, [31, 482, 1032, 3652, 13448, 26896]),
(6, [31, 482, 1032, 3652, 26896]),
(6, [31, 482, 1032, 3652, 26896, 32767]),
(6, [31, 482, 1055, 3652, 13448, 26896]),
(6, [31, 482, 1055, 3652, 26896]),
(6, [31, 482, 1055, 3652, 26896, 32767]),
(6, [31, 482, 1088, 3652, 13448, 26896]),
(6, [31, 482, 1088, 3652, 13802, 26896]),
(6, [31, 482, 1088, 3652, 26896])
],
#[
(6, [31, 482, 1088, 3652, 26896, 32767]),
(6, [31, 482, 1152, 3652, 4070, 26896]),
(6, [31, 482, 1152, 3652, 13448, 26896]),
(6, [31, 482, 1152, 3652, 26896]),
(6, [31, 482, 1152, 3652, 26896, 32767]),
(6, [31, 482, 1506, 3652, 13448, 26896]),
(6, [31, 482, 1506, 3652, 26896]),
(6, [31, 482, 1506, 3652, 26896, 32767]),
(6, [31, 482, 1604, 3652, 5871, 13448]),
(6, [31, 482, 1604, 3652, 13448, 26896]),
(6, [31, 482, 1604, 5871, 13448]),
(6, [31, 482, 1604, 5871, 13448, 26896]),
(6, [31, 482, 1604, 5871, 13448, 32767]),
(6, [31, 482, 1604, 13448, 26896]),
(6, [31, 482, 1604, 13448, 26896, 32767]),
(6, [31, 482, 2048, 3652, 5871, 13448])
],
#[
(6, [31, 482, 2048, 3652, 13448, 26911]),
(6, [31, 482, 2048, 3652, 13448, 28500]),
(6, [31, 482, 2048, 3652, 13448, 32152]),
(6, [31, 482, 2048, 3652, 13471, 26896]),
(6, [31, 482, 2048, 3652, 13802, 26896]),
(6, [31, 482, 2048, 3652, 15496, 26896]),
(6, [31, 482, 2048, 3652, 19319, 26896]),
(6, [31, 482, 2048, 3652, 26896, 32152]),
(6, [31, 482, 2048, 13448, 16076, 26896]),
(6, [31, 482, 2048, 13448, 26896, 28500]),
(6, [31, 482, 2048, 13448, 26896, 29115]),
(6, [31, 482, 2052, 3652, 13448, 26896]),
(6, [31, 482, 2052, 3652, 13448, 26911]),
(6, [31, 482, 2064, 3652, 13448, 26896]),
(6, [31, 482, 2079, 3652, 13448, 26896]),
(6, [31, 482, 2112, 3652, 13448, 26896])
],
#[
(6, [31, 482, 2304, 3652, 4070, 13448]),
(6, [31, 482, 2304, 3652, 13448]),
(6, [31, 482, 2304, 3652, 13448, 26896]),
(6, [31, 482, 2304, 3652, 13448, 32767]),
(6, [31, 482, 2530, 3652, 13448, 26896]),
(6, [31, 482, 2628, 3652, 13448, 26896]),
(6, [31, 482, 2628, 3652, 19319, 26896]),
(6, [31, 482, 2628, 3652, 26896]),
(6, [31, 482, 2628, 3652, 26896, 32767]),
(6, [31, 482, 2628, 13448, 19319, 26896]),
(6, [31, 482, 2628, 13448, 26896]),
(6, [31, 482, 2628, 13448, 26896, 32767]),
(6, [31, 482, 2628, 19319, 26896]),
(6, [31, 482, 2628, 19319, 26896, 32767]),
(6, [31, 482, 2628, 26896]),
(6, [31, 482, 2628, 26896, 32767])
]
],
#[
#[
(6, [31, 482, 3072, 3652, 13448, 26896]),
(6, [31, 482, 3072, 3652, 13448, 32152]),
(6, [31, 482, 3072, 3652, 26896]),
(6, [31, 482, 3072, 3652, 26896, 32152]),
(6, [31, 482, 3072, 3652, 26896, 32767]),
(6, [31, 482, 3588, 3652, 13448, 26896]),
(6, [31, 482, 3648, 3652, 13448, 26896]),
(6, [31, 482, 3652, 3654, 13448, 26896]),
(6, [31, 482, 3652, 3660, 13448, 26896]),
(6, [31, 482, 3652, 3668, 13448, 26896]),
(6, [31, 482, 3652, 3679, 5871, 13448]),
(6, [31, 482, 3652, 3679, 13448, 26911]),
(6, [31, 482, 3652, 3679, 13448, 32152]),
(6, [31, 482, 3652, 3679, 13471, 26896]),
(6, [31, 482, 3652, 3679, 13802, 26896]),
(6, [31, 482, 3652, 3679, 19319, 26896])
],
#[
(6, [31, 482, 3652, 3679, 26896, 32152]),
(6, [31, 482, 3652, 3780, 13448, 26896]),
(6, [31, 482, 3652, 3908, 13448, 26896]),
(6, [31, 482, 3652, 4070, 5871, 13448]),
(6, [31, 482, 3652, 4070, 13448, 26911]),
(6, [31, 482, 3652, 4070, 13448, 32152]),
(6, [31, 482, 3652, 4070, 13471, 26896]),
(6, [31, 482, 3652, 4070, 13802, 26896]),
(6, [31, 482, 3652, 4070, 19319, 26896]),
(6, [31, 482, 3652, 4070, 26896, 32152]),
(6, [31, 482, 3652, 4095, 13448, 26896]),
(6, [31, 482, 3652, 4267, 13448, 26896]),
(6, [31, 482, 3652, 5256, 5871]),
(6, [31, 482, 3652, 5256, 5871, 13448]),
(6, [31, 482, 3652, 5256, 5871, 26896]),
(6, [31, 482, 3652, 5256, 5871, 32767])
],
#[
(6, [31, 482, 3652, 5256, 13448, 26896]),
(6, [31, 482, 3652, 5256, 26896]),
(6, [31, 482, 3652, 5256, 26896, 32767]),
(6, [31, 482, 3652, 5645, 13448, 26896]),
(6, [31, 482, 3652, 5856, 13448]),
(6, [31, 482, 3652, 5856, 13448, 26896]),
(6, [31, 482, 3652, 5856, 13448, 26911]),
(6, [31, 482, 3652, 5856, 13448, 32767]),
(6, [31, 482, 3652, 5871, 5887, 13448]),
(6, [31, 482, 3652, 5871, 6127, 13448]),
(6, [31, 482, 3652, 5871, 7919, 13448]),
(6, [31, 482, 3652, 5871, 8192, 13448]),
(6, [31, 482, 3652, 5871, 13448, 13471]),
(6, [31, 482, 3652, 5871, 13448, 13802]),
(6, [31, 482, 3652, 5871, 13448, 14063]),
(6, [31, 482, 3652, 5871, 13448, 16076])
],
#[
(6, [31, 482, 3652, 5871, 13448, 19319]),
(6, [31, 482, 3652, 5871, 13448, 26896]),
(6, [31, 482, 3652, 5871, 13448, 26911]),
(6, [31, 482, 3652, 5871, 13448, 27122]),
(6, [31, 482, 3652, 5871, 13448, 28500]),
(6, [31, 482, 3652, 5871, 13448, 29115]),
(6, [31, 482, 3652, 5871, 13448, 32152]),
(6, [31, 482, 3652, 5871, 13448, 32285]),
(6, [31, 482, 3652, 5871, 13448, 32736]),
(6, [31, 482, 3652, 5871, 13448, 32767]),
(6, [31, 482, 3652, 5871, 13471]),
(6, [31, 482, 3652, 5871, 13471, 26896]),
(6, [31, 482, 3652, 5871, 13471, 32767]),
(6, [31, 482, 3652, 5871, 13802]),
(6, [31, 482, 3652, 5871, 13802, 26896]),
(6, [31, 482, 3652, 5871, 13802, 32767])
],
#[
(6, [31, 482, 3652, 5871, 19319]),
(6, [31, 482, 3652, 5871, 19319, 26896]),
(6, [31, 482, 3652, 5871, 19319, 32767]),
(6, [31, 482, 3652, 5871, 26896, 32152]),
(6, [31, 482, 3652, 5871, 32152]),
(6, [31, 482, 3652, 5871, 32152, 32767]),
(6, [31, 482, 3652, 5887, 13448]),
(6, [31, 482, 3652, 5887, 13448, 26896]),
(6, [31, 482, 3652, 5887, 13448, 32767]),
(6, [31, 482, 3652, 6127, 13448, 26896]),
(6, [31, 482, 3652, 7919, 13448, 26896]),
(6, [31, 482, 3652, 8192, 13448, 26911]),
(6, [31, 482, 3652, 8192, 13448, 32152]),
(6, [31, 482, 3652, 8192, 13471, 26896]),
(6, [31, 482, 3652, 8192, 13802, 26896]),
(6, [31, 482, 3652, 8192, 19319, 26896])
],
#[
(6, [31, 482, 3652, 8192, 26896, 32152]),
(6, [31, 482, 3652, 8200, 13448, 26896]),
(6, [31, 482, 3652, 8200, 13448, 26911]),
(6, [31, 482, 3652, 8208, 13448, 26896]),
(6, [31, 482, 3652, 8208, 13471, 26896]),
(6, [31, 482, 3652, 8223, 13448, 26896]),
(6, [31, 482, 3652, 8320, 13448, 26896]),
(6, [31, 482, 3652, 8448, 13448, 26896]),
(6, [31, 482, 3652, 8448, 13802, 26896]),
(6, [31, 482, 3652, 8674, 13448, 26896]),
(6, [31, 482, 3652, 9216, 13448, 26896]),
(6, [31, 482, 3652, 9216, 26896]),
(6, [31, 482, 3652, 9216, 26896, 28500]),
(6, [31, 482, 3652, 9216, 26896, 32767]),
(6, [31, 482, 3652, 10240, 13448, 26896]),
(6, [31, 482, 3652, 11844, 13448, 26896])
],
#[
(6, [31, 482, 3652, 12424, 13448, 26896]),
(6, [31, 482, 3652, 13320, 13448, 26896]),
(6, [31, 482, 3652, 13320, 26896]),
(6, [31, 482, 3652, 13320, 26896, 32285]),
(6, [31, 482, 3652, 13320, 26896, 32767]),
(6, [31, 482, 3652, 13440, 13448, 26896]),
(6, [31, 482, 3652, 13440, 26896]),
(6, [31, 482, 3652, 13440, 26896, 32736]),
(6, [31, 482, 3652, 13440, 26896, 32767]),
(6, [31, 482, 3652, 13448, 13450, 26896]),
(6, [31, 482, 3652, 13448, 13452, 26896]),
(6, [31, 482, 3652, 13448, 13464, 26896]),
(6, [31, 482, 3652, 13448, 13471, 26911]),
(6, [31, 482, 3652, 13448, 13471, 32152]),
(6, [31, 482, 3652, 13448, 13471, 32159]),
(6, [31, 482, 3652, 13448, 13512, 26896])
],
#[
(6, [31, 482, 3652, 13448, 13704, 26896]),
(6, [31, 482, 3652, 13448, 13802, 26911]),
(6, [31, 482, 3652, 13448, 13802, 32152]),
(6, [31, 482, 3652, 13448, 13823, 26896]),
(6, [31, 482, 3652, 13448, 14063]),
(6, [31, 482, 3652, 13448, 14063, 26896]),
(6, [31, 482, 3652, 13448, 14063, 32767]),
(6, [31, 482, 3652, 13448, 15496, 26896]),
(6, [31, 482, 3652, 13448, 16076, 26911]),
(6, [31, 482, 3652, 13448, 16076, 32152]),
(6, [31, 482, 3652, 13448, 16095, 26896]),
(6, [31, 482, 3652, 13448, 16366, 26896]),
(6, [31, 482, 3652, 13448, 16691, 26896]),
(6, [31, 482, 3652, 13448, 18704]),
(6, [31, 482, 3652, 13448, 18704, 19319]),
(6, [31, 482, 3652, 13448, 18704, 26896])
],
#[
(6, [31, 482, 3652, 13448, 18704, 32767]),
(6, [31, 482, 3652, 13448, 18965, 26896]),
(6, [31, 482, 3652, 13448, 19296, 26896]),
(6, [31, 482, 3652, 13448, 19319, 26896]),
(6, [31, 482, 3652, 13448, 19319, 26911]),
(6, [31, 482, 3652, 13448, 19319, 32152]),
(6, [31, 482, 3652, 13448, 19327, 26896]),
(6, [31, 482, 3652, 13448, 19447, 26896]),
(6, [31, 482, 3652, 13448, 20343, 26896]),
(6, [31, 482, 3652, 13448, 24575, 26896]),
(6, [31, 482, 3652, 13448, 24848, 26896]),
(6, [31, 482, 3652, 13448, 26640, 26896]),
(6, [31, 482, 3652, 13448, 26880]),
(6, [31, 482, 3652, 13448, 26880, 26896]),
(6, [31, 482, 3652, 13448, 26880, 32736]),
(6, [31, 482, 3652, 13448, 26880, 32767])
],
#[
(6, [31, 482, 3652, 13448, 26896]),
(6, [31, 482, 3652, 13448, 26896, 26898]),
(6, [31, 482, 3652, 13448, 26896, 26900]),
(6, [31, 482, 3652, 13448, 26896, 26904]),
(6, [31, 482, 3652, 13448, 26896, 26960]),
(6, [31, 482, 3652, 13448, 26896, 27024]),
(6, [31, 482, 3652, 13448, 26896, 27135]),
(6, [31, 482, 3652, 13448, 26896, 27511]),
(6, [31, 482, 3652, 13448, 26896, 27920]),
(6, [31, 482, 3652, 13448, 26896, 28511]),
(6, [31, 482, 3652, 13448, 26896, 28662]),
(6, [31, 482, 3652, 13448, 26896, 28697]),
(6, [31, 482, 3652, 13448, 26896, 29088]),
(6, [31, 482, 3652, 13448, 26896, 29115]),
(6, [31, 482, 3652, 13448, 26896, 29119]),
(6, [31, 482, 3652, 13448, 26896, 29179])
],
#[
(6, [31, 482, 3652, 13448, 26896, 30139]),
(6, [31, 482, 3652, 13448, 26896, 30719]),
(6, [31, 482, 3652, 13448, 26896, 31163]),
(6, [31, 482, 3652, 13448, 26896, 31743]),
(6, [31, 482, 3652, 13448, 26896, 32159]),
(6, [31, 482, 3652, 13448, 26896, 32250]),
(6, [31, 482, 3652, 13448, 26896, 32256]),
(6, [31, 482, 3652, 13448, 26896, 32285]),
(6, [31, 482, 3652, 13448, 26896, 32287]),
(6, [31, 482, 3652, 13448, 26896, 32349]),
(6, [31, 482, 3652, 13448, 26896, 32413]),
(6, [31, 482, 3652, 13448, 26896, 32511]),
(6, [31, 482, 3652, 13448, 26896, 32541]),
(6, [31, 482, 3652, 13448, 26896, 32639]),
(6, [31, 482, 3652, 13448, 26896, 32703]),
(6, [31, 482, 3652, 13448, 26896, 32732])
],
#[
(6, [31, 482, 3652, 13448, 26896, 32736]),
(6, [31, 482, 3652, 13448, 26896, 32738]),
(6, [31, 482, 3652, 13448, 26896, 32740]),
(6, [31, 482, 3652, 13448, 26896, 32744]),
(6, [31, 482, 3652, 13448, 26896, 32751]),
(6, [31, 482, 3652, 13448, 26896, 32752]),
(6, [31, 482, 3652, 13448, 26896, 32759]),
(6, [31, 482, 3652, 13448, 26896, 32763]),
(6, [31, 482, 3652, 13448, 26896, 32765]),
(6, [31, 482, 3652, 13448, 26896, 32767]),
(6, [31, 482, 3652, 13448, 26898]),
(6, [31, 482, 3652, 13448, 26898, 32767]),
(6, [31, 482, 3652, 13448, 26900]),
(6, [31, 482, 3652, 13448, 26900, 32767]),
(6, [31, 482, 3652, 13448, 26904]),
(6, [31, 482, 3652, 13448, 26904, 32767])
],
#[
(6, [31, 482, 3652, 13448, 26911, 27122]),
(6, [31, 482, 3652, 13448, 26911, 27135]),
(6, [31, 482, 3652, 13448, 26911, 28500]),
(6, [31, 482, 3652, 13448, 26911, 28511]),
(6, [31, 482, 3652, 13448, 26911, 29115]),
(6, [31, 482, 3652, 13448, 26911, 32152]),
(6, [31, 482, 3652, 13448, 26911, 32159]),
(6, [31, 482, 3652, 13448, 26911, 32285]),
(6, [31, 482, 3652, 13448, 26911, 32736]),
(6, [31, 482, 3652, 13448, 26911, 32767]),
(6, [31, 482, 3652, 13448, 26960]),
(6, [31, 482, 3652, 13448, 26960, 32767]),
(6, [31, 482, 3652, 13448, 27024]),
(6, [31, 482, 3652, 13448, 27024, 32767]),
(6, [31, 482, 3652, 13448, 27122, 28500]),
(6, [31, 482, 3652, 13448, 27122, 32152])
],
#[
(6, [31, 482, 3652, 13448, 27920]),
(6, [31, 482, 3652, 13448, 27920, 32767]),
(6, [31, 482, 3652, 13448, 28500, 32152]),
(6, [31, 482, 3652, 13448, 29115, 32152]),
(6, [31, 482, 3652, 13448, 32152, 32159]),
(6, [31, 482, 3652, 13448, 32152, 32250]),
(6, [31, 482, 3652, 13448, 32152, 32285]),
(6, [31, 482, 3652, 13448, 32152, 32732]),
(6, [31, 482, 3652, 13448, 32152, 32736]),
(6, [31, 482, 3652, 13448, 32152, 32767]),
(6, [31, 482, 3652, 13448, 32159]),
(6, [31, 482, 3652, 13448, 32159, 32767]),
(6, [31, 482, 3652, 13450, 26896]),
(6, [31, 482, 3652, 13450, 26896, 32767]),
(6, [31, 482, 3652, 13452, 26896]),
(6, [31, 482, 3652, 13452, 26896, 32767])
],
#[
(6, [31, 482, 3652, 13464, 26896]),
(6, [31, 482, 3652, 13464, 26896, 32767]),
(6, [31, 482, 3652, 13471, 13802, 26896]),
(6, [31, 482, 3652, 13471, 13823, 26896]),
(6, [31, 482, 3652, 13471, 16076, 26896]),
(6, [31, 482, 3652, 13471, 16095, 26896]),
(6, [31, 482, 3652, 13471, 19296, 26896]),
(6, [31, 482, 3652, 13471, 19319, 26896]),
(6, [31, 482, 3652, 13471, 26896, 26911]),
(6, [31, 482, 3652, 13471, 26896, 27122]),
(6, [31, 482, 3652, 13471, 26896, 28500]),
(6, [31, 482, 3652, 13471, 26896, 29115]),
(6, [31, 482, 3652, 13471, 26896, 32152]),
(6, [31, 482, 3652, 13471, 26896, 32159]),
(6, [31, 482, 3652, 13471, 26896, 32285]),
(6, [31, 482, 3652, 13471, 26896, 32736])
],
#[
(6, [31, 482, 3652, 13471, 26896, 32767]),
(6, [31, 482, 3652, 13471, 26911]),
(6, [31, 482, 3652, 13471, 26911, 32767]),
(6, [31, 482, 3652, 13471, 32152]),
(6, [31, 482, 3652, 13471, 32152, 32767]),
(6, [31, 482, 3652, 13471, 32159]),
(6, [31, 482, 3652, 13471, 32159, 32767]),
(6, [31, 482, 3652, 13512, 26896]),
(6, [31, 482, 3652, 13512, 26896, 32767]),
(6, [31, 482, 3652, 13704, 26896]),
(6, [31, 482, 3652, 13704, 26896, 32767]),
(6, [31, 482, 3652, 13802, 13823, 26896]),
(6, [31, 482, 3652, 13802, 16076, 26896]),
(6, [31, 482, 3652, 13802, 16366, 26896]),
(6, [31, 482, 3652, 13802, 18965, 26896]),
(6, [31, 482, 3652, 13802, 19319, 26896])
]
],
#[
#[
(6, [31, 482, 3652, 13802, 26896, 26911]),
(6, [31, 482, 3652, 13802, 26896, 27122]),
(6, [31, 482, 3652, 13802, 26896, 28500]),
(6, [31, 482, 3652, 13802, 26896, 29115]),
(6, [31, 482, 3652, 13802, 26896, 32152]),
(6, [31, 482, 3652, 13802, 26896, 32250]),
(6, [31, 482, 3652, 13802, 26896, 32285]),
(6, [31, 482, 3652, 13802, 26896, 32736]),
(6, [31, 482, 3652, 13802, 26896, 32767]),
(6, [31, 482, 3652, 13802, 26911]),
(6, [31, 482, 3652, 13802, 26911, 32767]),
(6, [31, 482, 3652, 13823, 26896]),
(6, [31, 482, 3652, 13823, 26896, 32767]),
(6, [31, 482, 3652, 15496, 26896]),
(6, [31, 482, 3652, 15496, 26896, 32767]),
(6, [31, 482, 3652, 16076, 19319, 26896])
],
#[
(6, [31, 482, 3652, 16076, 26896, 32152]),
(6, [31, 482, 3652, 16076, 32152]),
(6, [31, 482, 3652, 16076, 32152, 32767]),
(6, [31, 482, 3652, 18704, 19319]),
(6, [31, 482, 3652, 18704, 19319, 26896]),
(6, [31, 482, 3652, 18704, 19319, 32767]),
(6, [31, 482, 3652, 18965, 26896]),
(6, [31, 482, 3652, 18965, 26896, 32767]),
(6, [31, 482, 3652, 19296, 26896]),
(6, [31, 482, 3652, 19296, 26896, 32767]),
(6, [31, 482, 3652, 19319, 19327, 26896]),
(6, [31, 482, 3652, 19319, 19447, 26896]),
(6, [31, 482, 3652, 19319, 20343, 26896]),
(6, [31, 482, 3652, 19319, 26896, 26911]),
(6, [31, 482, 3652, 19319, 26896, 27122]),
(6, [31, 482, 3652, 19319, 26896, 27511])
],
#[
(6, [31, 482, 3652, 19319, 26896, 28500]),
(6, [31, 482, 3652, 19319, 26896, 29115]),
(6, [31, 482, 3652, 19319, 26896, 32152]),
(6, [31, 482, 3652, 19319, 26896, 32285]),
(6, [31, 482, 3652, 19319, 26896, 32736]),
(6, [31, 482, 3652, 19319, 26896, 32767]),
(6, [31, 482, 3652, 19319, 26911]),
(6, [31, 482, 3652, 19319, 26911, 32767]),
(6, [31, 482, 3652, 19319, 32152]),
(6, [31, 482, 3652, 19319, 32152, 32767]),
(6, [31, 482, 3652, 19327, 26896]),
(6, [31, 482, 3652, 19327, 26896, 32767]),
(6, [31, 482, 3652, 19447, 26896]),
(6, [31, 482, 3652, 19447, 26896, 32767]),
(6, [31, 482, 3652, 26896, 26911, 32152]),
(6, [31, 482, 3652, 26896, 26911, 32159])
],
#[
(6, [31, 482, 3652, 26896, 27122, 32152]),
(6, [31, 482, 3652, 26896, 27122, 32250]),
(6, [31, 482, 3652, 26896, 27511]),
(6, [31, 482, 3652, 26896, 27511, 32767]),
(6, [31, 482, 3652, 26896, 27920]),
(6, [31, 482, 3652, 26896, 27920, 32767]),
(6, [31, 482, 3652, 26896, 28500, 32152]),
(6, [31, 482, 3652, 26896, 29115, 30139]),
(6, [31, 482, 3652, 26896, 29115, 32152]),
(6, [31, 482, 3652, 26896, 30139]),
(6, [31, 482, 3652, 26896, 30139, 32767]),
(6, [31, 482, 3652, 26896, 31743]),
(6, [31, 482, 3652, 26896, 31743, 32767]),
(6, [31, 482, 3652, 26896, 32152, 32159]),
(6, [31, 482, 3652, 26896, 32152, 32250]),
(6, [31, 482, 3652, 26896, 32152, 32285])
],
#[
(6, [31, 482, 3652, 26896, 32152, 32732]),
(6, [31, 482, 3652, 26896, 32152, 32736]),
(6, [31, 482, 3652, 26896, 32152, 32767]),
(6, [31, 482, 3652, 26896, 32159]),
(6, [31, 482, 3652, 26896, 32159, 32767]),
(6, [31, 482, 3652, 26896, 32250]),
(6, [31, 482, 3652, 26896, 32250, 32767]),
(6, [31, 482, 3652, 26911, 32152]),
(6, [31, 482, 3652, 26911, 32152, 32767]),
(6, [31, 482, 3652, 26911, 32159]),
(6, [31, 482, 3652, 26911, 32159, 32767]),
(6, [31, 482, 3652, 27920]),
(6, [31, 482, 3652, 27920, 32767]),
(6, [31, 482, 3652, 28500, 32152]),
(6, [31, 482, 3652, 28500, 32152, 32767]),
(6, [31, 482, 3654, 13448, 26896])
],
#[
(6, [31, 482, 3654, 13448, 26896, 32767]),
(6, [31, 482, 3660, 13448, 26896]),
(6, [31, 482, 3660, 13448, 26896, 32767]),
(6, [31, 482, 3668, 13448, 26896]),
(6, [31, 482, 3668, 13448, 26896, 32767]),
(6, [31, 482, 3679, 4070, 13448, 26896]),
(6, [31, 482, 3679, 13448, 16076, 26896]),
(6, [31, 482, 3679, 13448, 26896, 28500]),
(6, [31, 482, 3679, 13448, 26896, 29115]),
(6, [31, 482, 3780, 13448, 26896]),
(6, [31, 482, 3780, 13448, 26896, 32767]),
(6, [31, 482, 3908, 13448, 26896]),
(6, [31, 482, 3908, 13448, 26896, 32767]),
(6, [31, 482, 4070, 13448, 16076, 26896]),
(6, [31, 482, 4070, 13448, 26896, 28500]),
(6, [31, 482, 4070, 13448, 26896, 29115])
],
#[
(6, [31, 482, 4267, 13448, 26896]),
(6, [31, 482, 4267, 13448, 26896, 28500]),
(6, [31, 482, 4267, 13448, 26896, 32767]),
(6, [31, 482, 5871, 13448, 16076]),
(6, [31, 482, 5871, 13448, 16076, 26896]),
(6, [31, 482, 5871, 13448, 16076, 32767]),
(6, [31, 482, 5871, 13448, 26896, 28500]),
(6, [31, 482, 5871, 13448, 26896, 29115]),
(6, [31, 482, 5871, 13448, 28500]),
(6, [31, 482, 5871, 13448, 28500, 32767]),
(6, [31, 482, 5871, 13448, 29115]),
(6, [31, 482, 5871, 13448, 29115, 32767]),
(6, [31, 482, 8192, 11844, 13448, 26896]),
(6, [31, 482, 8192, 13448, 16076, 26896]),
(6, [31, 482, 8192, 13448, 26896, 28500]),
(6, [31, 482, 8192, 13448, 26896, 29115])
],
#[
(6, [31, 482, 9216, 13448, 26896, 28500]),
(6, [31, 482, 9216, 26896, 28500]),
(6, [31, 482, 9216, 26896, 28500, 32767]),
(6, [31, 482, 10240, 13448, 16076, 26896]),
(6, [31, 482, 11844, 13448, 26896]),
(6, [31, 482, 11844, 13448, 26896, 32767]),
(6, [31, 482, 12424, 13448, 26896, 29115]),
(6, [31, 482, 13448, 13471, 16076, 26896]),
(6, [31, 482, 13448, 13471, 26896, 28500]),
(6, [31, 482, 13448, 13471, 26896, 29115]),
(6, [31, 482, 13448, 13802, 16076, 26896]),
(6, [31, 482, 13448, 13802, 26896, 28500]),
(6, [31, 482, 13448, 13802, 26896, 29115]),
(6, [31, 482, 13448, 16076, 16095, 26896]),
(6, [31, 482, 13448, 16076, 16366, 26896]),
(6, [31, 482, 13448, 16076, 16691, 26896])
],
#[
(6, [31, 482, 13448, 16076, 19319, 26896]),
(6, [31, 482, 13448, 16076, 26896, 26911]),
(6, [31, 482, 13448, 16076, 26896, 27122]),
(6, [31, 482, 13448, 16076, 26896, 28500]),
(6, [31, 482, 13448, 16076, 26896, 29115]),
(6, [31, 482, 13448, 16076, 26896, 32152]),
(6, [31, 482, 13448, 16076, 26896, 32285]),
(6, [31, 482, 13448, 16076, 26896, 32732]),
(6, [31, 482, 13448, 16076, 26896, 32736]),
(6, [31, 482, 13448, 16076, 26896, 32767]),
(6, [31, 482, 13448, 16076, 26911]),
(6, [31, 482, 13448, 16076, 26911, 32767]),
(6, [31, 482, 13448, 16076, 32152]),
(6, [31, 482, 13448, 16076, 32152, 32767]),
(6, [31, 482, 13448, 16691, 26896]),
(6, [31, 482, 13448, 16691, 26896, 32767])
],
#[
(6, [31, 482, 13448, 19319, 26896, 28500]),
(6, [31, 482, 13448, 19319, 26896, 29115]),
(6, [31, 482, 13448, 24848, 26896, 29115]),
(6, [31, 482, 13448, 26896, 26911, 28500]),
(6, [31, 482, 13448, 26896, 26911, 29115]),
(6, [31, 482, 13448, 26896, 27122, 28500]),
(6, [31, 482, 13448, 26896, 27122, 29115]),
(6, [31, 482, 13448, 26896, 28500, 28511]),
(6, [31, 482, 13448, 26896, 28500, 28662]),
(6, [31, 482, 13448, 26896, 28500, 29115]),
(6, [31, 482, 13448, 26896, 28500, 32152]),
(6, [31, 482, 13448, 26896, 28500, 32285]),
(6, [31, 482, 13448, 26896, 28500, 32732]),
(6, [31, 482, 13448, 26896, 28500, 32736]),
(6, [31, 482, 13448, 26896, 28500, 32767]),
(6, [31, 482, 13448, 26896, 29115, 29119])
],
#[
(6, [31, 482, 13448, 26896, 29115, 29179]),
(6, [31, 482, 13448, 26896, 29115, 30139]),
(6, [31, 482, 13448, 26896, 29115, 31163]),
(6, [31, 482, 13448, 26896, 29115, 32152]),
(6, [31, 482, 13448, 26896, 29115, 32285]),
(6, [31, 482, 13448, 26896, 29115, 32736]),
(6, [31, 482, 13448, 26896, 29115, 32767]),
(6, [31, 482, 13448, 26896, 30139]),
(6, [31, 482, 13448, 26896, 30139, 32767]),
(6, [31, 482, 13448, 26896, 31163]),
(6, [31, 482, 13448, 26896, 31163, 32767]),
(6, [31, 482, 13448, 26896, 32152, 32732]),
(6, [31, 482, 13448, 26896, 32732]),
(6, [31, 482, 13448, 26896, 32732, 32767]),
(6, [31, 482, 13448, 26911, 29115]),
(6, [31, 482, 13448, 26911, 29115, 32767])
],
#[
(6, [31, 482, 13448, 27122, 28500]),
(6, [31, 482, 13448, 27122, 28500, 32767]),
(6, [31, 482, 13448, 28500, 32152]),
(6, [31, 482, 13448, 28500, 32152, 32767]),
(6, [31, 482, 13448, 29115, 32152]),
(6, [31, 482, 13448, 29115, 32152, 32767]),
(6, [31, 482, 13448, 32152, 32732]),
(6, [31, 482, 13448, 32152, 32732, 32767]),
(6, [31, 482, 13471, 26896, 28500]),
(6, [31, 482, 13471, 26896, 28500, 32767]),
(6, [31, 482, 13471, 26896, 29115]),
(6, [31, 482, 13471, 26896, 29115, 32767]),
(6, [31, 482, 13802, 26896, 28500]),
(6, [31, 482, 13802, 26896, 28500, 32767]),
(6, [31, 482, 13802, 26896, 29115]),
(6, [31, 482, 13802, 26896, 29115, 32767])
],
#[
(6, [31, 482, 16076, 19319, 26896]),
(6, [31, 482, 16076, 19319, 26896, 32767]),
(6, [31, 482, 16076, 26896, 32152]),
(6, [31, 482, 16076, 26896, 32152, 32767]),
(6, [31, 482, 16076, 32152]),
(6, [31, 482, 16076, 32152, 32767]),
(6, [31, 482, 19319, 26896, 28500]),
(6, [31, 482, 19319, 26896, 28500, 32767]),
(6, [31, 482, 19319, 26896, 29115]),
(6, [31, 482, 19319, 26896, 29115, 32767]),
(6, [31, 482, 26896, 28500, 32152]),
(6, [31, 482, 26896, 28500, 32152, 32767]),
(6, [31, 482, 26896, 29115, 30139]),
(6, [31, 482, 26896, 29115, 30139, 32767]),
(6, [31, 482, 26896, 29115, 32152]),
(6, [31, 482, 26896, 29115, 32152, 32767])
],
#[
(6, [31, 482, 26896, 30139]),
(6, [31, 482, 26896, 30139, 32767]),
(6, [31, 482, 26896, 32152, 32732]),
(6, [31, 482, 26896, 32152, 32732, 32767]),
(6, [31, 482, 28500, 32152]),
(6, [31, 482, 28500, 32152, 32767]),
(6, [31, 486, 3652, 13448, 26896]),
(6, [31, 486, 3652, 13448, 26896, 32767]),
(6, [31, 490, 3652, 13448, 26896]),
(6, [31, 490, 3652, 13448, 26896, 32767]),
(6, [31, 498, 3652, 13448, 26896]),
(6, [31, 498, 3652, 13448, 26896, 32767]),
(6, [31, 511, 1024, 3652, 13448, 26896]),
(6, [31, 511, 1024, 3652, 26896]),
(6, [31, 511, 1024, 3652, 26896, 32767]),
(6, [31, 511, 2048, 3652, 13448, 26896])
],
#[
(6, [31, 511, 3652, 3679, 13448, 26896]),
(6, [31, 511, 3652, 4070, 13448, 26896]),
(6, [31, 511, 3652, 4095, 13448, 26896]),
(6, [31, 511, 3652, 5871, 13448]),
(6, [31, 511, 3652, 5871, 13448, 26896]),
(6, [31, 511, 3652, 5871, 13448, 32767]),
(6, [31, 511, 3652, 8192, 13448, 26896]),
(6, [31, 511, 3652, 13448, 13471, 26896]),
(6, [31, 511, 3652, 13448, 13802, 26896]),
(6, [31, 511, 3652, 13448, 13823, 26896]),
(6, [31, 511, 3652, 13448, 16076, 26896]),
(6, [31, 511, 3652, 13448, 19319, 26896]),
(6, [31, 511, 3652, 13448, 26896, 26911]),
(6, [31, 511, 3652, 13448, 26896, 27122]),
(6, [31, 511, 3652, 13448, 26896, 27135]),
(6, [31, 511, 3652, 13448, 26896, 28500])
],
#[
(6, [31, 511, 3652, 13448, 26896, 29115]),
(6, [31, 511, 3652, 13448, 26896, 32152]),
(6, [31, 511, 3652, 13448, 26896, 32256]),
(6, [31, 511, 3652, 13448, 26896, 32285]),
(6, [31, 511, 3652, 13448, 26896, 32736]),
(6, [31, 511, 3652, 13448, 26896, 32767]),
(6, [31, 511, 3652, 13448, 26911]),
(6, [31, 511, 3652, 13448, 26911, 32767]),
(6, [31, 511, 3652, 13448, 32152]),
(6, [31, 511, 3652, 13448, 32152, 32767]),
(6, [31, 511, 3652, 13471, 26896]),
(6, [31, 511, 3652, 13471, 26896, 32767]),
(6, [31, 511, 3652, 13802, 26896]),
(6, [31, 511, 3652, 13802, 26896, 32767]),
(6, [31, 511, 3652, 13823, 26896]),
(6, [31, 511, 3652, 13823, 26896, 32767])
]
],
#[
#[
(6, [31, 511, 3652, 19319, 26896]),
(6, [31, 511, 3652, 19319, 26896, 32767]),
(6, [31, 511, 3652, 26896, 32152]),
(6, [31, 511, 3652, 26896, 32152, 32767]),
(6, [31, 511, 13448, 16076, 26896]),
(6, [31, 511, 13448, 16076, 26896, 32767]),
(6, [31, 511, 13448, 26896, 28500]),
(6, [31, 511, 13448, 26896, 28500, 32767]),
(6, [31, 511, 13448, 26896, 29115]),
(6, [31, 511, 13448, 26896, 29115, 32767]),
(6, [31, 1024, 1506, 3652, 13448, 26896]),
(6, [31, 1024, 1506, 3652, 26896]),
(6, [31, 1024, 1506, 3652, 26896, 32767]),
(6, [31, 1024, 3652, 13448, 26896, 27122]),
(6, [31, 1024, 3652, 13448, 26896, 32285]),
(6, [31, 1024, 3652, 26896, 27122])
],
#[
(6, [31, 1024, 3652, 26896, 27122, 32767]),
(6, [31, 1024, 3652, 26896, 32285]),
(6, [31, 1024, 3652, 26896, 32285, 32767]),
(6, [31, 1506, 3652, 13448, 26896]),
(6, [31, 1506, 3652, 13448, 26896, 32767]),
(6, [31, 1506, 3652, 26896]),
(6, [31, 1506, 3652, 26896, 32767]),
(6, [31, 2048, 2530, 3652, 13448, 26896]),
(6, [31, 2048, 3652, 13448, 26896, 27122]),
(6, [31, 2048, 3652, 13448, 26896, 32285]),
(6, [31, 2112, 3652, 13448, 26896, 27122]),
(6, [31, 2530, 3652, 13448, 26896]),
(6, [31, 2530, 3652, 13448, 26896, 32767]),
(6, [31, 3588, 3652, 13448, 26896, 32285]),
(6, [31, 3652, 3679, 13448, 26896, 27122]),
(6, [31, 3652, 3679, 13448, 26896, 32285])
],
#[
(6, [31, 3652, 4070, 13448, 13802, 26896]),
(6, [31, 3652, 4070, 13448, 26896, 27122]),
(6, [31, 3652, 4070, 13448, 26896, 32285]),
(6, [31, 3652, 4070, 13802, 26896]),
(6, [31, 3652, 4070, 13802, 26896, 32767]),
(6, [31, 3652, 5645, 13448, 26896]),
(6, [31, 3652, 5645, 13448, 26896, 27122]),
(6, [31, 3652, 5645, 13448, 26896, 32767]),
(6, [31, 3652, 5871, 13448, 26896, 27122]),
(6, [31, 3652, 5871, 13448, 26896, 32285]),
(6, [31, 3652, 5871, 13448, 27122]),
(6, [31, 3652, 5871, 13448, 27122, 32767]),
(6, [31, 3652, 5871, 13448, 32285]),
(6, [31, 3652, 5871, 13448, 32285, 32767]),
(6, [31, 3652, 8192, 8674, 13448, 26896]),
(6, [31, 3652, 8192, 13448, 26896, 27122])
],
#[
(6, [31, 3652, 8192, 13448, 26896, 32285]),
(6, [31, 3652, 8320, 13448, 26896, 27122]),
(6, [31, 3652, 8674, 13448, 26896]),
(6, [31, 3652, 8674, 13448, 26896, 32767]),
(6, [31, 3652, 13320, 13448, 26896, 32285]),
(6, [31, 3652, 13320, 26896, 32285]),
(6, [31, 3652, 13320, 26896, 32285, 32767]),
(6, [31, 3652, 13448, 13471, 26896, 27122]),
(6, [31, 3652, 13448, 13471, 26896, 32285]),
(6, [31, 3652, 13448, 13802, 26896, 27122]),
(6, [31, 3652, 13448, 13802, 26896, 32285]),
(6, [31, 3652, 13448, 16076, 26896, 27122]),
(6, [31, 3652, 13448, 16076, 26896, 32285]),
(6, [31, 3652, 13448, 19319, 26896, 27122]),
(6, [31, 3652, 13448, 19319, 26896, 32285]),
(6, [31, 3652, 13448, 26640, 26896, 32285])
],
#[
(6, [31, 3652, 13448, 26896, 26911, 27122]),
(6, [31, 3652, 13448, 26896, 26911, 27135]),
(6, [31, 3652, 13448, 26896, 26911, 32285]),
(6, [31, 3652, 13448, 26896, 27122, 27135]),
(6, [31, 3652, 13448, 26896, 27122, 28500]),
(6, [31, 3652, 13448, 26896, 27122, 28662]),
(6, [31, 3652, 13448, 26896, 27122, 29115]),
(6, [31, 3652, 13448, 26896, 27122, 32152]),
(6, [31, 3652, 13448, 26896, 27122, 32250]),
(6, [31, 3652, 13448, 26896, 27122, 32285]),
(6, [31, 3652, 13448, 26896, 27122, 32736]),
(6, [31, 3652, 13448, 26896, 27122, 32767]),
(6, [31, 3652, 13448, 26896, 27135]),
(6, [31, 3652, 13448, 26896, 27135, 32767]),
(6, [31, 3652, 13448, 26896, 28500, 32285]),
(6, [31, 3652, 13448, 26896, 29115, 32285])
],
#[
(6, [31, 3652, 13448, 26896, 32152, 32285]),
(6, [31, 3652, 13448, 26896, 32256]),
(6, [31, 3652, 13448, 26896, 32256, 32767]),
(6, [31, 3652, 13448, 26896, 32285, 32287]),
(6, [31, 3652, 13448, 26896, 32285, 32349]),
(6, [31, 3652, 13448, 26896, 32285, 32413]),
(6, [31, 3652, 13448, 26896, 32285, 32541]),
(6, [31, 3652, 13448, 26896, 32285, 32736]),
(6, [31, 3652, 13448, 26896, 32285, 32767]),
(6, [31, 3652, 13448, 26896, 32287]),
(6, [31, 3652, 13448, 26896, 32287, 32767]),
(6, [31, 3652, 13448, 26896, 32541]),
(6, [31, 3652, 13448, 26896, 32541, 32767]),
(6, [31, 3652, 13448, 26911, 27122]),
(6, [31, 3652, 13448, 26911, 27122, 32767]),
(6, [31, 3652, 13448, 26911, 27135])
],
#[
(6, [31, 3652, 13448, 26911, 27135, 32767]),
(6, [31, 3652, 13448, 26911, 32285]),
(6, [31, 3652, 13448, 26911, 32285, 32767]),
(6, [31, 3652, 13448, 27122, 28500]),
(6, [31, 3652, 13448, 27122, 28500, 32767]),
(6, [31, 3652, 13448, 32152, 32285]),
(6, [31, 3652, 13448, 32152, 32285, 32767]),
(6, [31, 3652, 13471, 26896, 27122]),
(6, [31, 3652, 13471, 26896, 27122, 32767]),
(6, [31, 3652, 13471, 26896, 32285]),
(6, [31, 3652, 13471, 26896, 32285, 32767]),
(6, [31, 3652, 13802, 26896, 27122]),
(6, [31, 3652, 13802, 26896, 27122, 32767]),
(6, [31, 3652, 13802, 26896, 32285]),
(6, [31, 3652, 13802, 26896, 32285, 32767]),
(6, [31, 3652, 19319, 26896, 27122])
],
#[
(6, [31, 3652, 19319, 26896, 27122, 32767]),
(6, [31, 3652, 19319, 26896, 32285]),
(6, [31, 3652, 19319, 26896, 32285, 32767]),
(6, [31, 3652, 26896, 27122, 32152]),
(6, [31, 3652, 26896, 27122, 32152, 32767]),
(6, [31, 3652, 26896, 27122, 32250]),
(6, [31, 3652, 26896, 27122, 32250, 32767]),
(6, [31, 3652, 26896, 32152, 32285]),
(6, [31, 3652, 26896, 32152, 32285, 32767]),
(6, [31, 13448, 16076, 26896, 27122]),
(6, [31, 13448, 16076, 26896, 27122, 32767]),
(6, [31, 13448, 16076, 26896, 32285]),
(6, [31, 13448, 16076, 26896, 32285, 32767]),
(6, [31, 13448, 26896, 27122, 28500]),
(6, [31, 13448, 26896, 27122, 28500, 32767]),
(6, [31, 13448, 26896, 27122, 29115])
],
#[
(6, [31, 13448, 26896, 27122, 29115, 32767]),
(6, [31, 13448, 26896, 28500, 32285]),
(6, [31, 13448, 26896, 28500, 32285, 32767]),
(6, [31, 13448, 26896, 29115, 32285]),
(6, [31, 13448, 26896, 29115, 32285, 32767]),
(6, [31, 13448, 27122, 28500]),
(6, [31, 13448, 27122, 28500, 32767]),
(6, [64, 95, 482, 3652, 13448, 26896]),
(6, [64, 482, 511, 3652, 13448, 26896]),
(6, [64, 482, 3652, 13448, 26896, 32736]),
(6, [68, 482, 511, 3652, 13448, 26896]),
(6, [68, 482, 511, 13448, 26896]),
(6, [68, 482, 511, 13448, 26896, 32767]),
(6, [95, 482, 3652, 13448, 26896]),
(6, [95, 482, 3652, 13448, 26896, 32767]),
(6, [128, 159, 482, 3652, 13448, 26896])
],
#[
(6, [128, 482, 511, 3652, 13448, 26896]),
(6, [128, 482, 3652, 13448, 26896, 32736]),
(6, [136, 482, 511, 3652, 13448, 26896]),
(6, [159, 482, 3652, 13448, 26896]),
(6, [159, 482, 3652, 13448, 26896, 32767]),
(6, [256, 287, 482, 3652, 13448, 26896]),
(6, [256, 482, 511, 3652, 13448, 26896]),
(6, [256, 482, 3652, 13448, 26896, 32736]),
(6, [256, 511, 3652, 13448, 26896]),
(6, [256, 511, 3652, 13448, 26896, 32767]),
(6, [272, 482, 511, 3652, 13448, 26896]),
(6, [287, 482, 3652, 13448, 26896]),
(6, [287, 482, 3652, 13448, 26896, 32767]),
(6, [480, 482, 3652, 13448, 26896, 32736]),
(6, [480, 3652, 13448, 26896, 32736]),
(6, [480, 3652, 13448, 26896, 32736, 32767])
],
#[
(6, [482, 511, 1024, 3652, 13448, 26896]),
(6, [482, 511, 1024, 3652, 26896]),
(6, [482, 511, 1024, 3652, 26896, 32767]),
(6, [482, 511, 2048, 3652, 13448, 26896]),
(6, [482, 511, 3652, 3679, 13448, 26896]),
(6, [482, 511, 3652, 4070, 13448, 26896]),
(6, [482, 511, 3652, 4095, 13448, 26896]),
(6, [482, 511, 3652, 5871, 13448]),
(6, [482, 511, 3652, 5871, 13448, 26896]),
(6, [482, 511, 3652, 5871, 13448, 32767]),
(6, [482, 511, 3652, 8192, 13448, 26896]),
(6, [482, 511, 3652, 13448, 13471, 26896]),
(6, [482, 511, 3652, 13448, 13802, 26896]),
(6, [482, 511, 3652, 13448, 13823, 26896]),
(6, [482, 511, 3652, 13448, 16076, 26896]),
(6, [482, 511, 3652, 13448, 19319, 26896])
],
#[
(6, [482, 511, 3652, 13448, 26896, 26911]),
(6, [482, 511, 3652, 13448, 26896, 27122]),
(6, [482, 511, 3652, 13448, 26896, 27135]),
(6, [482, 511, 3652, 13448, 26896, 28500]),
(6, [482, 511, 3652, 13448, 26896, 29115]),
(6, [482, 511, 3652, 13448, 26896, 32152]),
(6, [482, 511, 3652, 13448, 26896, 32256]),
(6, [482, 511, 3652, 13448, 26896, 32285]),
(6, [482, 511, 3652, 13448, 26896, 32736]),
(6, [482, 511, 3652, 13448, 26896, 32767]),
(6, [482, 511, 3652, 13448, 32152]),
(6, [482, 511, 3652, 13448, 32152, 32767]),
(6, [482, 511, 3652, 13471, 26896]),
(6, [482, 511, 3652, 13471, 26896, 32767]),
(6, [482, 511, 3652, 13802, 26896]),
(6, [482, 511, 3652, 13802, 26896, 32767])
],
#[
(6, [482, 511, 3652, 13823, 26896]),
(6, [482, 511, 3652, 13823, 26896, 32767]),
(6, [482, 511, 3652, 19319, 26896]),
(6, [482, 511, 3652, 19319, 26896, 32767]),
(6, [482, 511, 3652, 26896, 32152]),
(6, [482, 511, 3652, 26896, 32152, 32767]),
(6, [482, 511, 13448, 16076, 26896]),
(6, [482, 511, 13448, 16076, 26896, 32767]),
(6, [482, 511, 13448, 26896, 28500]),
(6, [482, 511, 13448, 26896, 28500, 32767]),
(6, [482, 511, 13448, 26896, 29115]),
(6, [482, 511, 13448, 26896, 29115, 32767]),
(6, [482, 1024, 1055, 3652, 13448, 26896]),
(6, [482, 1024, 1055, 3652, 26896]),
(6, [482, 1024, 1055, 3652, 26896, 32767]),
(6, [482, 1024, 3652, 13448, 26896, 32736])
],
#[
(6, [482, 1024, 3652, 26896, 32736]),
(6, [482, 1024, 3652, 26896, 32736, 32767]),
(6, [482, 1055, 3652, 13448, 26896]),
(6, [482, 1055, 3652, 13448, 26896, 32767]),
(6, [482, 1055, 3652, 26896]),
(6, [482, 1055, 3652, 26896, 32767]),
(6, [482, 2048, 2079, 3652, 13448, 26896]),
(6, [482, 2048, 3652, 13448, 26896, 32736]),
(6, [482, 2079, 3652, 13448, 26896]),
(6, [482, 2079, 3652, 13448, 26896, 32767]),
(6, [482, 3648, 3652, 13448, 26896, 32736]),
(6, [482, 3652, 3679, 13448, 13471, 26896]),
(6, [482, 3652, 3679, 13448, 26896, 26911]),
(6, [482, 3652, 3679, 13448, 26896, 32736]),
(6, [482, 3652, 3679, 13448, 26911]),
(6, [482, 3652, 3679, 13448, 26911, 32767])
],
#[
(6, [482, 3652, 3679, 13471, 26896]),
(6, [482, 3652, 3679, 13471, 26896, 32767]),
(6, [482, 3652, 4070, 13448, 26896, 32736]),
(6, [482, 3652, 5871, 13448, 26896, 32736]),
(6, [482, 3652, 5871, 13448, 32736]),
(6, [482, 3652, 5871, 13448, 32736, 32767]),
(6, [482, 3652, 8192, 8223, 13448, 26896]),
(6, [482, 3652, 8192, 13448, 26896, 32736]),
(6, [482, 3652, 8223, 13448, 26896]),
(6, [482, 3652, 8223, 13448, 26896, 32767]),
(6, [482, 3652, 13440, 13448, 26896, 32736]),
(6, [482, 3652, 13440, 26896, 32736]),
(6, [482, 3652, 13440, 26896, 32736, 32767]),
(6, [482, 3652, 13448, 13471, 26896, 26911]),
(6, [482, 3652, 13448, 13471, 26896, 32736]),
(6, [482, 3652, 13448, 13802, 26896, 32736])
],
#[
(6, [482, 3652, 13448, 16076, 26896, 32736]),
(6, [482, 3652, 13448, 19319, 26896, 32736]),
(6, [482, 3652, 13448, 26880, 26896, 32736]),
(6, [482, 3652, 13448, 26880, 32736]),
(6, [482, 3652, 13448, 26880, 32736, 32767]),
(6, [482, 3652, 13448, 26896, 26911, 32736]),
(6, [482, 3652, 13448, 26896, 27122, 32736]),
(6, [482, 3652, 13448, 26896, 28500, 32736]),
(6, [482, 3652, 13448, 26896, 29115, 32736]),
(6, [482, 3652, 13448, 26896, 32152, 32736]),
(6, [482, 3652, 13448, 26896, 32256]),
(6, [482, 3652, 13448, 26896, 32256, 32767]),
(6, [482, 3652, 13448, 26896, 32285, 32736]),
(6, [482, 3652, 13448, 26896, 32736, 32738]),
(6, [482, 3652, 13448, 26896, 32736, 32740]),
(6, [482, 3652, 13448, 26896, 32736, 32744])
]
],
#[
#[
(6, [482, 3652, 13448, 26896, 32736, 32752]),
(6, [482, 3652, 13448, 26896, 32736, 32767]),
(6, [482, 3652, 13448, 26896, 32738]),
(6, [482, 3652, 13448, 26896, 32738, 32767]),
(6, [482, 3652, 13448, 26911, 32736]),
(6, [482, 3652, 13448, 26911, 32736, 32767]),
(6, [482, 3652, 13448, 32152, 32736]),
(6, [482, 3652, 13448, 32152, 32736, 32767]),
(6, [482, 3652, 13471, 26896, 32736]),
(6, [482, 3652, 13471, 26896, 32736, 32767]),
(6, [482, 3652, 13802, 26896, 32736]),
(6, [482, 3652, 13802, 26896, 32736, 32767]),
(6, [482, 3652, 19319, 26896, 32736]),
(6, [482, 3652, 19319, 26896, 32736, 32767]),
(6, [482, 3652, 26896, 32152, 32736]),
(6, [482, 3652, 26896, 32152, 32736, 32767])
],
#[
(6, [482, 13448, 16076, 26896, 32736]),
(6, [482, 13448, 16076, 26896, 32736, 32767]),
(6, [482, 13448, 26896, 28500, 32736]),
(6, [482, 13448, 26896, 28500, 32736, 32767]),
(6, [482, 13448, 26896, 29115, 32736]),
(6, [482, 13448, 26896, 29115, 32736, 32767]),
(6, [511, 3652, 3679, 13448, 26896]),
(6, [511, 3652, 3679, 13448, 26896, 32767]),
(6, [511, 3652, 4070, 13448, 26896]),
(6, [511, 3652, 4070, 13448, 26896, 32767]),
(6, [511, 3652, 13448, 13471, 26896]),
(6, [511, 3652, 13448, 13471, 26896, 32767]),
(6, [511, 3652, 13448, 13802, 26896]),
(6, [511, 3652, 13448, 13802, 26896, 32767]),
(6, [511, 3652, 13448, 26896, 32285]),
(6, [511, 3652, 13448, 26896, 32285, 32767])
],
#[
(6, [511, 3652, 13448, 26896, 32736]),
(6, [511, 3652, 13448, 26896, 32736, 32767]),
(6, [511, 3652, 13471, 26896]),
(6, [511, 3652, 13471, 26896, 32767]),
(6, [511, 3652, 13802, 26896]),
(6, [511, 3652, 13802, 26896, 32767]),
(6, [3652, 13448, 26896, 27122, 32736]),
(6, [3652, 13448, 26896, 27122, 32736, 32767]),
(6, [3652, 13448, 26896, 32285, 32736]),
(6, [3652, 13448, 26896, 32285, 32736, 32767]),
(7, [0, 2, 31, 482, 3652, 13448, 26896]),
(7, [0, 4, 31, 482, 3652, 13448, 26896]),
(7, [0, 8, 31, 482, 3652, 13448, 26896]),
(7, [0, 16, 31, 482, 3652, 13448, 26896]),
(7, [0, 31, 64, 482, 3652, 13448, 26896]),
(7, [0, 31, 128, 482, 3652, 13448, 26896])
],
#[
(7, [0, 31, 256, 482, 3652, 13448, 26896]),
(7, [0, 31, 482, 511, 3652, 13448, 26896]),
(7, [0, 31, 482, 1024, 3652, 13448, 26896]),
(7, [0, 31, 482, 1024, 3652, 26896]),
(7, [0, 31, 482, 1024, 3652, 26896, 32767]),
(7, [0, 31, 482, 2048, 3652, 13448, 26896]),
(7, [0, 31, 482, 3652, 3679, 13448, 26896]),
(7, [0, 31, 482, 3652, 4070, 13448, 26896]),
(7, [0, 31, 482, 3652, 5871, 13448]),
(7, [0, 31, 482, 3652, 5871, 13448, 26896]),
(7, [0, 31, 482, 3652, 5871, 13448, 32767]),
(7, [0, 31, 482, 3652, 8192, 13448, 26896]),
(7, [0, 31, 482, 3652, 13448, 13471, 26896]),
(7, [0, 31, 482, 3652, 13448, 13802, 26896]),
(7, [0, 31, 482, 3652, 13448, 16076, 26896]),
(7, [0, 31, 482, 3652, 13448, 19319, 26896])
],
#[
(7, [0, 31, 482, 3652, 13448, 26896]),
(7, [0, 31, 482, 3652, 13448, 26896, 26911]),
(7, [0, 31, 482, 3652, 13448, 26896, 27122]),
(7, [0, 31, 482, 3652, 13448, 26896, 28500]),
(7, [0, 31, 482, 3652, 13448, 26896, 29115]),
(7, [0, 31, 482, 3652, 13448, 26896, 32152]),
(7, [0, 31, 482, 3652, 13448, 26896, 32285]),
(7, [0, 31, 482, 3652, 13448, 26896, 32736]),
(7, [0, 31, 482, 3652, 13448, 26896, 32767]),
(7, [0, 31, 482, 3652, 13448, 26911]),
(7, [0, 31, 482, 3652, 13448, 26911, 32767]),
(7, [0, 31, 482, 3652, 13448, 32152]),
(7, [0, 31, 482, 3652, 13448, 32152, 32767]),
(7, [0, 31, 482, 3652, 13471, 26896]),
(7, [0, 31, 482, 3652, 13471, 26896, 32767]),
(7, [0, 31, 482, 3652, 13802, 26896])
],
#[
(7, [0, 31, 482, 3652, 13802, 26896, 32767]),
(7, [0, 31, 482, 3652, 19319, 26896]),
(7, [0, 31, 482, 3652, 19319, 26896, 32767]),
(7, [0, 31, 482, 3652, 26896, 32152]),
(7, [0, 31, 482, 3652, 26896, 32152, 32767]),
(7, [0, 31, 482, 13448, 16076, 26896]),
(7, [0, 31, 482, 13448, 16076, 26896, 32767]),
(7, [0, 31, 482, 13448, 26896, 28500]),
(7, [0, 31, 482, 13448, 26896, 28500, 32767]),
(7, [0, 31, 482, 13448, 26896, 29115]),
(7, [0, 31, 482, 13448, 26896, 29115, 32767]),
(7, [0, 31, 511, 3652, 13448, 26896]),
(7, [0, 31, 511, 3652, 13448, 26896, 32767]),
(7, [0, 31, 3652, 13448, 26896, 27122]),
(7, [0, 31, 3652, 13448, 26896, 27122, 32767]),
(7, [0, 31, 3652, 13448, 26896, 32285])
],
#[
(7, [0, 31, 3652, 13448, 26896, 32285, 32767]),
(7, [0, 482, 511, 3652, 13448, 26896]),
(7, [0, 482, 511, 3652, 13448, 26896, 32767]),
(7, [0, 482, 3652, 13448, 26896, 32736]),
(7, [0, 482, 3652, 13448, 26896, 32736, 32767]),
(7, [2, 31, 482, 3652, 13448, 26896]),
(7, [2, 31, 482, 3652, 13448, 26896, 32767]),
(7, [4, 31, 482, 3652, 13448, 26896]),
(7, [4, 31, 482, 3652, 13448, 26896, 32767]),
(7, [8, 31, 482, 3652, 13448, 26896]),
(7, [8, 31, 482, 3652, 13448, 26896, 32767]),
(7, [16, 31, 482, 3652, 13448, 26896]),
(7, [16, 31, 482, 3652, 13448, 26896, 32767]),
(7, [31, 64, 482, 3652, 13448, 26896]),
(7, [31, 64, 482, 3652, 13448, 26896, 32767]),
(7, [31, 128, 482, 3652, 13448, 26896])
],
#[
(7, [31, 128, 482, 3652, 13448, 26896, 32767]),
(7, [31, 256, 482, 3652, 13448, 26896]),
(7, [31, 256, 482, 3652, 13448, 26896, 32767]),
(7, [31, 482, 511, 3652, 13448, 26896]),
(7, [31, 482, 511, 3652, 13448, 26896, 32767]),
(7, [31, 482, 1024, 3652, 13448, 26896]),
(7, [31, 482, 1024, 3652, 13448, 26896, 32767]),
(7, [31, 482, 1024, 3652, 26896]),
(7, [31, 482, 1024, 3652, 26896, 32767]),
(7, [31, 482, 2048, 3652, 13448, 26896]),
(7, [31, 482, 2048, 3652, 13448, 26896, 32767]),
(7, [31, 482, 3652, 3679, 13448, 26896]),
(7, [31, 482, 3652, 3679, 13448, 26896, 32767]),
(7, [31, 482, 3652, 4070, 13448, 26896]),
(7, [31, 482, 3652, 4070, 13448, 26896, 32767]),
(7, [31, 482, 3652, 5871, 13448])
],
#[
(7, [31, 482, 3652, 5871, 13448, 26896]),
(7, [31, 482, 3652, 5871, 13448, 26896, 32767]),
(7, [31, 482, 3652, 5871, 13448, 32767]),
(7, [31, 482, 3652, 8192, 13448, 26896]),
(7, [31, 482, 3652, 8192, 13448, 26896, 32767]),
(7, [31, 482, 3652, 13448, 13471, 26896]),
(7, [31, 482, 3652, 13448, 13471, 26896, 32767]),
(7, [31, 482, 3652, 13448, 13802, 26896]),
(7, [31, 482, 3652, 13448, 13802, 26896, 32767]),
(7, [31, 482, 3652, 13448, 16076, 26896]),
(7, [31, 482, 3652, 13448, 16076, 26896, 32767]),
(7, [31, 482, 3652, 13448, 19319, 26896]),
(7, [31, 482, 3652, 13448, 19319, 26896, 32767]),
(7, [31, 482, 3652, 13448, 26896, 26911]),
(7, [31, 482, 3652, 13448, 26896, 26911, 32767]),
(7, [31, 482, 3652, 13448, 26896, 27122])
],
#[
(7, [31, 482, 3652, 13448, 26896, 27122, 32767]),
(7, [31, 482, 3652, 13448, 26896, 28500]),
(7, [31, 482, 3652, 13448, 26896, 28500, 32767]),
(7, [31, 482, 3652, 13448, 26896, 29115]),
(7, [31, 482, 3652, 13448, 26896, 29115, 32767]),
(7, [31, 482, 3652, 13448, 26896, 32152]),
(7, [31, 482, 3652, 13448, 26896, 32152, 32767]),
(7, [31, 482, 3652, 13448, 26896, 32285]),
(7, [31, 482, 3652, 13448, 26896, 32285, 32767]),
(7, [31, 482, 3652, 13448, 26896, 32736]),
(7, [31, 482, 3652, 13448, 26896, 32736, 32767]),
(7, [31, 482, 3652, 13448, 26896, 32767]),
(7, [31, 482, 3652, 13448, 26911]),
(7, [31, 482, 3652, 13448, 26911, 32767]),
(7, [31, 482, 3652, 13448, 32152]),
(7, [31, 482, 3652, 13448, 32152, 32767])
],
#[
(7, [31, 482, 3652, 13471, 26896]),
(7, [31, 482, 3652, 13471, 26896, 32767]),
(7, [31, 482, 3652, 13802, 26896]),
(7, [31, 482, 3652, 13802, 26896, 32767]),
(7, [31, 482, 3652, 19319, 26896]),
(7, [31, 482, 3652, 19319, 26896, 32767]),
(7, [31, 482, 3652, 26896, 32152]),
(7, [31, 482, 3652, 26896, 32152, 32767]),
(7, [31, 482, 13448, 16076, 26896]),
(7, [31, 482, 13448, 16076, 26896, 32767]),
(7, [31, 482, 13448, 26896, 28500]),
(7, [31, 482, 13448, 26896, 28500, 32767]),
(7, [31, 482, 13448, 26896, 29115]),
(7, [31, 482, 13448, 26896, 29115, 32767]),
(7, [31, 511, 3652, 13448, 26896]),
(7, [31, 511, 3652, 13448, 26896, 32767])
],
#[
(7, [31, 3652, 13448, 26896, 27122]),
(7, [31, 3652, 13448, 26896, 27122, 32767]),
(7, [31, 3652, 13448, 26896, 32285]),
(7, [31, 3652, 13448, 26896, 32285, 32767]),
(7, [482, 511, 3652, 13448, 26896]),
(7, [482, 511, 3652, 13448, 26896, 32767]),
(7, [482, 3652, 13448, 26896, 32736]),
(7, [482, 3652, 13448, 26896, 32736, 32767]),
(8, [0, 31, 482, 3652, 13448, 26896]),
(8, [0, 31, 482, 3652, 13448, 26896, 32767]),
(8, [31, 482, 3652, 13448, 26896]),
(8, [31, 482, 3652, 13448, 26896, 32767])
]
]
]

def memoRawTable : Array (ℕ × List ℕ) :=
  (memoRawBlocks.toList.flatMap (fun middle =>
    middle.toList.flatMap (fun leaf => leaf.toList))).toArray

def memoRawGet (i : ℕ) : ℕ × List ℕ :=
  let middle := memoRawBlocks[i / 256]!
  let leaf := middle[(i / 16) % 16]!
  leaf[i % 16]!

def memoExpandedWord (w : ℕ) : ℕ :=
  w +
  (if w.testBit 0 then 8355840 else 0) +
  (if w.testBit 1 then 2139095040 else 0) +
  (if w.testBit 2 then 667220327295957762237270832474750976 else 0) +
  (if w.testBit 3 then 547608330240 else 0) +
  (if w.testBit 4 then 140187732541440 else 0) +
  (if w.testBit 5 then 35888059530608640 else 0) +
  (if w.testBit 6 then 1334440654591915524474541664949501952 else 0) +
  (if w.testBit 7 then 9187343239835811840 else 0) +
  (if w.testBit 8 then 2668881309183831048949083329899003904 else 0) +
  (if w.testBit 9 then 2351959869397967831040 else 0) +
  (if w.testBit 10 then 5337762618367662097898166659798007808 else 0) +
  (if w.testBit 11 then 10675525236735324195796333319596015616 else 0) +
  (if w.testBit 12 then 21351050473470648391592666639192031232 else 0) +
  (if w.testBit 13 then 42702100946941296783185333278384062464 else 0) +
  (if w.testBit 14 then 85404201893882593566370666556768124928 else 0)

def memoTable (r : Fin 6588) : ℕ × List ℕ :=
  let t := memoRawGet r.val
  (t.1, t.2.map memoExpandedWord)

def memoListLT : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a == b then memoListLT as bs else decide (a < b)

def memoKeyLT (a b : ℕ × List ℕ) : Bool :=
  if a.1 == b.1 then memoListLT a.2 b.2 else decide (a.1 < b.1)

def memoSearch (key : ℕ × List ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      let row := memoRawGet mid
      if row == key then mid
      else if memoKeyLT row key then memoSearch key fuel (mid + 1) hi
      else memoSearch key fuel lo mid
    else 0

def memoInsert (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: memoInsert a bs

def memoSort : List ℕ → List ℕ
  | [] => []
  | a :: as => memoInsert a (memoSort as)

def memoLookup (k : ℕ) (ws : List ℕ) : Fin 6588 :=
  let raw := memoSort (ws.map (fun w => w &&& 32767))
  ⟨memoSearch (k, raw) 14 0 6588 % 6588, Nat.mod_lt _ (by decide)⟩

def G : ℕ := 2361183241434822574779
def MK : ℕ := 170141183460469231731687303715884105727
def I : List ℕ := [667220327295957762237411569963073567, 4003321963775746582646856296354021858, 18014948836990861932366181874786111044, 69390914038779607281863510364818257032, 141450709386743045594301556672379775248, 0, 170141183460469231731687303715884105727]
def E : List (Fin 5 × Fin 5) := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 1), (1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (4, 4), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (1, 1), (1, 1), (1, 1), (1, 1), (1, 1), (1, 1), (1, 1), (1, 1), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (2, 2), (2, 2), (2, 2), (2, 2), (2, 2), (2, 2), (2, 2), (2, 2), (0, 2), (1, 2), (1, 4), (2, 3), (2, 4), (3, 3), (3, 4), (4, 4), (0, 2), (1, 2), (1, 4), (2, 3), (2, 4), (3, 3), (3, 4), (4, 4), (0, 2), (1, 2), (1, 4), (2, 3), (2, 4), (3, 3), (3, 4), (4, 4), (0, 2), (1, 2), (1, 4), (2, 3), (2, 4), (3, 3), (3, 4), (4, 4), (0, 2), (1, 2), (1, 4), (2, 3), (2, 4), (3, 3), (3, 4), (4, 4), (0, 2), (1, 2), (1, 4), (2, 3), (2, 4), (3, 3), (3, 4), (4, 4), (0, 2), (1, 2), (1, 4), (2, 3), (2, 4), (3, 3), (3, 4), (4, 4)]

lemma table_search
    (hTable : failTable_review G MK 15 56 true memoTable memoLookup = true)
    (hCover : I.sublists.all (fun ws =>
      quickFail_review G 15 56 true 8 ws || tableHit_review memoTable memoLookup 8 ws) = true) :
    I.sublists.all (fun ws => !LS G MK 15 56 true 8 ws) = true := by
  have hprs : (List.range 56).all (fun j =>
      (G.testBit (15 + j) && !G.testBit (15 + 56 + j)) &&
      (MK.testBit (15 + j) == MK.testBit (15 + 56 + j))) = true := by decide +kernel
  have hall : ∀ pq ∈ prsOf 15 56,
      (G.testBit pq.1 = true ∧ G.testBit pq.2 = false) ∧
      MK.testBit pq.1 = MK.testBit pq.2 := by
    intro pq hpq
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hpq
    have h := List.all_eq_true.mp hprs j hj
    simpa only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] using h
  have hD : ∀ pq ∈ prsOf 15 56, Dpq pq G := by
    intro pq hpq
    have h := (hall pq hpq).1
    simp [Dpq, h.1, h.2]
  exact failTable_frontier_review G MK 15 56 true hD
    (fun pq hpq => (hall pq hpq).2) (fun pq hpq => (hall pq hpq).1)
    memoTable memoLookup hTable 8 I.sublists hCover

lemma five_lower
    (hTable : failTable_review G MK 15 56 true memoTable memoLookup = true)
    (hCover : I.sublists.all (fun ws =>
      quickFail_review G 15 56 true 8 ws || tableHit_review memoTable memoLookup 8 ws) = true) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5,
      C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
        (4443 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  exact refuteT5 4443 8 15 56 127 G MK I E
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (table_search hTable hCover)

def certRows : List (Fin 6588) := List.finRange 6588
def certRowOK (r : Fin 6588) : Bool :=
  failRow_review G MK 15 56 true memoTable memoLookup (memoTable r).1 (memoTable r).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk000 : ((certRows.drop 0).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk001 : ((certRows.drop 16).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk002 : ((certRows.drop 32).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk003 : ((certRows.drop 48).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk004 : ((certRows.drop 64).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk005 : ((certRows.drop 80).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk006 : ((certRows.drop 96).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk007 : ((certRows.drop 112).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk008 : ((certRows.drop 128).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk009 : ((certRows.drop 144).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk010 : ((certRows.drop 160).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk011 : ((certRows.drop 176).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk012 : ((certRows.drop 192).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk013 : ((certRows.drop 208).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk014 : ((certRows.drop 224).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk015 : ((certRows.drop 240).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk016 : ((certRows.drop 256).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk017 : ((certRows.drop 272).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk018 : ((certRows.drop 288).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk019 : ((certRows.drop 304).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk020 : ((certRows.drop 320).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk021 : ((certRows.drop 336).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk022 : ((certRows.drop 352).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk023 : ((certRows.drop 368).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk024 : ((certRows.drop 384).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk025 : ((certRows.drop 400).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk026 : ((certRows.drop 416).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk027 : ((certRows.drop 432).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk028 : ((certRows.drop 448).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk029 : ((certRows.drop 464).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk030 : ((certRows.drop 480).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk031 : ((certRows.drop 496).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk032 : ((certRows.drop 512).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk033 : ((certRows.drop 528).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk034 : ((certRows.drop 544).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk035 : ((certRows.drop 560).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk036 : ((certRows.drop 576).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk037 : ((certRows.drop 592).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk038 : ((certRows.drop 608).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk039 : ((certRows.drop 624).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk040 : ((certRows.drop 640).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk041 : ((certRows.drop 656).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk042 : ((certRows.drop 672).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk043 : ((certRows.drop 688).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk044 : ((certRows.drop 704).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk045 : ((certRows.drop 720).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk046 : ((certRows.drop 736).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk047 : ((certRows.drop 752).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk048 : ((certRows.drop 768).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk049 : ((certRows.drop 784).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk050 : ((certRows.drop 800).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk051 : ((certRows.drop 816).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk052 : ((certRows.drop 832).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk053 : ((certRows.drop 848).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk054 : ((certRows.drop 864).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk055 : ((certRows.drop 880).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk056 : ((certRows.drop 896).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk057 : ((certRows.drop 912).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk058 : ((certRows.drop 928).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk059 : ((certRows.drop 944).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk060 : ((certRows.drop 960).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk061 : ((certRows.drop 976).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk062 : ((certRows.drop 992).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk063 : ((certRows.drop 1008).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk064 : ((certRows.drop 1024).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk065 : ((certRows.drop 1040).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk066 : ((certRows.drop 1056).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk067 : ((certRows.drop 1072).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk068 : ((certRows.drop 1088).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk069 : ((certRows.drop 1104).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk070 : ((certRows.drop 1120).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk071 : ((certRows.drop 1136).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk072 : ((certRows.drop 1152).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk073 : ((certRows.drop 1168).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk074 : ((certRows.drop 1184).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk075 : ((certRows.drop 1200).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk076 : ((certRows.drop 1216).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk077 : ((certRows.drop 1232).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk078 : ((certRows.drop 1248).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk079 : ((certRows.drop 1264).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk080 : ((certRows.drop 1280).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk081 : ((certRows.drop 1296).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk082 : ((certRows.drop 1312).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk083 : ((certRows.drop 1328).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk084 : ((certRows.drop 1344).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk085 : ((certRows.drop 1360).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk086 : ((certRows.drop 1376).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk087 : ((certRows.drop 1392).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk088 : ((certRows.drop 1408).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk089 : ((certRows.drop 1424).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk090 : ((certRows.drop 1440).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk091 : ((certRows.drop 1456).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk092 : ((certRows.drop 1472).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk093 : ((certRows.drop 1488).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk094 : ((certRows.drop 1504).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk095 : ((certRows.drop 1520).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk096 : ((certRows.drop 1536).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk097 : ((certRows.drop 1552).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk098 : ((certRows.drop 1568).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk099 : ((certRows.drop 1584).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk100 : ((certRows.drop 1600).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk101 : ((certRows.drop 1616).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk102 : ((certRows.drop 1632).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk103 : ((certRows.drop 1648).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk104 : ((certRows.drop 1664).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk105 : ((certRows.drop 1680).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk106 : ((certRows.drop 1696).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk107 : ((certRows.drop 1712).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk108 : ((certRows.drop 1728).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk109 : ((certRows.drop 1744).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk110 : ((certRows.drop 1760).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk111 : ((certRows.drop 1776).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk112 : ((certRows.drop 1792).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk113 : ((certRows.drop 1808).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk114 : ((certRows.drop 1824).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk115 : ((certRows.drop 1840).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk116 : ((certRows.drop 1856).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk117 : ((certRows.drop 1872).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk118 : ((certRows.drop 1888).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk119 : ((certRows.drop 1904).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk120 : ((certRows.drop 1920).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk121 : ((certRows.drop 1936).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk122 : ((certRows.drop 1952).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk123 : ((certRows.drop 1968).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk124 : ((certRows.drop 1984).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk125 : ((certRows.drop 2000).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk126 : ((certRows.drop 2016).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk127 : ((certRows.drop 2032).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk128 : ((certRows.drop 2048).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk129 : ((certRows.drop 2064).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk130 : ((certRows.drop 2080).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk131 : ((certRows.drop 2096).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk132 : ((certRows.drop 2112).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk133 : ((certRows.drop 2128).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk134 : ((certRows.drop 2144).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk135 : ((certRows.drop 2160).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk136 : ((certRows.drop 2176).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk137 : ((certRows.drop 2192).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk138 : ((certRows.drop 2208).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk139 : ((certRows.drop 2224).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk140 : ((certRows.drop 2240).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk141 : ((certRows.drop 2256).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk142 : ((certRows.drop 2272).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk143 : ((certRows.drop 2288).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk144 : ((certRows.drop 2304).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk145 : ((certRows.drop 2320).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk146 : ((certRows.drop 2336).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk147 : ((certRows.drop 2352).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk148 : ((certRows.drop 2368).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk149 : ((certRows.drop 2384).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk150 : ((certRows.drop 2400).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk151 : ((certRows.drop 2416).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk152 : ((certRows.drop 2432).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk153 : ((certRows.drop 2448).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk154 : ((certRows.drop 2464).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk155 : ((certRows.drop 2480).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk156 : ((certRows.drop 2496).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk157 : ((certRows.drop 2512).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk158 : ((certRows.drop 2528).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk159 : ((certRows.drop 2544).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk160 : ((certRows.drop 2560).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk161 : ((certRows.drop 2576).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk162 : ((certRows.drop 2592).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk163 : ((certRows.drop 2608).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk164 : ((certRows.drop 2624).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk165 : ((certRows.drop 2640).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk166 : ((certRows.drop 2656).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk167 : ((certRows.drop 2672).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk168 : ((certRows.drop 2688).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk169 : ((certRows.drop 2704).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk170 : ((certRows.drop 2720).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk171 : ((certRows.drop 2736).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk172 : ((certRows.drop 2752).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk173 : ((certRows.drop 2768).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk174 : ((certRows.drop 2784).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk175 : ((certRows.drop 2800).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk176 : ((certRows.drop 2816).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk177 : ((certRows.drop 2832).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk178 : ((certRows.drop 2848).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk179 : ((certRows.drop 2864).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk180 : ((certRows.drop 2880).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk181 : ((certRows.drop 2896).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk182 : ((certRows.drop 2912).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk183 : ((certRows.drop 2928).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk184 : ((certRows.drop 2944).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk185 : ((certRows.drop 2960).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk186 : ((certRows.drop 2976).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk187 : ((certRows.drop 2992).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk188 : ((certRows.drop 3008).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk189 : ((certRows.drop 3024).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk190 : ((certRows.drop 3040).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk191 : ((certRows.drop 3056).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk192 : ((certRows.drop 3072).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk193 : ((certRows.drop 3088).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk194 : ((certRows.drop 3104).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk195 : ((certRows.drop 3120).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk196 : ((certRows.drop 3136).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk197 : ((certRows.drop 3152).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk198 : ((certRows.drop 3168).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk199 : ((certRows.drop 3184).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk200 : ((certRows.drop 3200).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk201 : ((certRows.drop 3216).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk202 : ((certRows.drop 3232).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk203 : ((certRows.drop 3248).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk204 : ((certRows.drop 3264).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk205 : ((certRows.drop 3280).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk206 : ((certRows.drop 3296).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk207 : ((certRows.drop 3312).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk208 : ((certRows.drop 3328).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk209 : ((certRows.drop 3344).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk210 : ((certRows.drop 3360).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk211 : ((certRows.drop 3376).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk212 : ((certRows.drop 3392).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk213 : ((certRows.drop 3408).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk214 : ((certRows.drop 3424).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk215 : ((certRows.drop 3440).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk216 : ((certRows.drop 3456).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk217 : ((certRows.drop 3472).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk218 : ((certRows.drop 3488).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk219 : ((certRows.drop 3504).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk220 : ((certRows.drop 3520).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk221 : ((certRows.drop 3536).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk222 : ((certRows.drop 3552).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk223 : ((certRows.drop 3568).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk224 : ((certRows.drop 3584).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk225 : ((certRows.drop 3600).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk226 : ((certRows.drop 3616).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk227 : ((certRows.drop 3632).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk228 : ((certRows.drop 3648).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk229 : ((certRows.drop 3664).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk230 : ((certRows.drop 3680).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk231 : ((certRows.drop 3696).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk232 : ((certRows.drop 3712).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk233 : ((certRows.drop 3728).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk234 : ((certRows.drop 3744).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk235 : ((certRows.drop 3760).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk236 : ((certRows.drop 3776).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk237 : ((certRows.drop 3792).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk238 : ((certRows.drop 3808).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk239 : ((certRows.drop 3824).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk240 : ((certRows.drop 3840).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk241 : ((certRows.drop 3856).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk242 : ((certRows.drop 3872).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk243 : ((certRows.drop 3888).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk244 : ((certRows.drop 3904).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk245 : ((certRows.drop 3920).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk246 : ((certRows.drop 3936).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk247 : ((certRows.drop 3952).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk248 : ((certRows.drop 3968).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk249 : ((certRows.drop 3984).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk250 : ((certRows.drop 4000).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk251 : ((certRows.drop 4016).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk252 : ((certRows.drop 4032).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk253 : ((certRows.drop 4048).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk254 : ((certRows.drop 4064).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk255 : ((certRows.drop 4080).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk256 : ((certRows.drop 4096).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk257 : ((certRows.drop 4112).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk258 : ((certRows.drop 4128).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk259 : ((certRows.drop 4144).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk260 : ((certRows.drop 4160).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk261 : ((certRows.drop 4176).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk262 : ((certRows.drop 4192).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk263 : ((certRows.drop 4208).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk264 : ((certRows.drop 4224).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk265 : ((certRows.drop 4240).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk266 : ((certRows.drop 4256).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk267 : ((certRows.drop 4272).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk268 : ((certRows.drop 4288).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk269 : ((certRows.drop 4304).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk270 : ((certRows.drop 4320).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk271 : ((certRows.drop 4336).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk272 : ((certRows.drop 4352).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk273 : ((certRows.drop 4368).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk274 : ((certRows.drop 4384).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk275 : ((certRows.drop 4400).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk276 : ((certRows.drop 4416).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk277 : ((certRows.drop 4432).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk278 : ((certRows.drop 4448).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk279 : ((certRows.drop 4464).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk280 : ((certRows.drop 4480).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk281 : ((certRows.drop 4496).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk282 : ((certRows.drop 4512).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk283 : ((certRows.drop 4528).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk284 : ((certRows.drop 4544).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk285 : ((certRows.drop 4560).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk286 : ((certRows.drop 4576).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk287 : ((certRows.drop 4592).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk288 : ((certRows.drop 4608).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk289 : ((certRows.drop 4624).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk290 : ((certRows.drop 4640).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk291 : ((certRows.drop 4656).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk292 : ((certRows.drop 4672).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk293 : ((certRows.drop 4688).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk294 : ((certRows.drop 4704).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk295 : ((certRows.drop 4720).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk296 : ((certRows.drop 4736).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk297 : ((certRows.drop 4752).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk298 : ((certRows.drop 4768).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk299 : ((certRows.drop 4784).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk300 : ((certRows.drop 4800).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk301 : ((certRows.drop 4816).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk302 : ((certRows.drop 4832).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk303 : ((certRows.drop 4848).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk304 : ((certRows.drop 4864).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk305 : ((certRows.drop 4880).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk306 : ((certRows.drop 4896).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk307 : ((certRows.drop 4912).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk308 : ((certRows.drop 4928).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk309 : ((certRows.drop 4944).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk310 : ((certRows.drop 4960).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk311 : ((certRows.drop 4976).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk312 : ((certRows.drop 4992).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk313 : ((certRows.drop 5008).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk314 : ((certRows.drop 5024).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk315 : ((certRows.drop 5040).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk316 : ((certRows.drop 5056).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk317 : ((certRows.drop 5072).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk318 : ((certRows.drop 5088).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk319 : ((certRows.drop 5104).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk320 : ((certRows.drop 5120).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk321 : ((certRows.drop 5136).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk322 : ((certRows.drop 5152).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk323 : ((certRows.drop 5168).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk324 : ((certRows.drop 5184).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk325 : ((certRows.drop 5200).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk326 : ((certRows.drop 5216).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk327 : ((certRows.drop 5232).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk328 : ((certRows.drop 5248).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk329 : ((certRows.drop 5264).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk330 : ((certRows.drop 5280).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk331 : ((certRows.drop 5296).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk332 : ((certRows.drop 5312).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk333 : ((certRows.drop 5328).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk334 : ((certRows.drop 5344).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk335 : ((certRows.drop 5360).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk336 : ((certRows.drop 5376).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk337 : ((certRows.drop 5392).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk338 : ((certRows.drop 5408).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk339 : ((certRows.drop 5424).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk340 : ((certRows.drop 5440).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk341 : ((certRows.drop 5456).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk342 : ((certRows.drop 5472).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk343 : ((certRows.drop 5488).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk344 : ((certRows.drop 5504).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk345 : ((certRows.drop 5520).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk346 : ((certRows.drop 5536).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk347 : ((certRows.drop 5552).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk348 : ((certRows.drop 5568).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk349 : ((certRows.drop 5584).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk350 : ((certRows.drop 5600).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk351 : ((certRows.drop 5616).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk352 : ((certRows.drop 5632).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk353 : ((certRows.drop 5648).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk354 : ((certRows.drop 5664).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk355 : ((certRows.drop 5680).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk356 : ((certRows.drop 5696).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk357 : ((certRows.drop 5712).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk358 : ((certRows.drop 5728).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk359 : ((certRows.drop 5744).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk360 : ((certRows.drop 5760).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk361 : ((certRows.drop 5776).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk362 : ((certRows.drop 5792).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk363 : ((certRows.drop 5808).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk364 : ((certRows.drop 5824).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk365 : ((certRows.drop 5840).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk366 : ((certRows.drop 5856).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk367 : ((certRows.drop 5872).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk368 : ((certRows.drop 5888).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk369 : ((certRows.drop 5904).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk370 : ((certRows.drop 5920).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk371 : ((certRows.drop 5936).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk372 : ((certRows.drop 5952).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk373 : ((certRows.drop 5968).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk374 : ((certRows.drop 5984).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk375 : ((certRows.drop 6000).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk376 : ((certRows.drop 6016).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk377 : ((certRows.drop 6032).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk378 : ((certRows.drop 6048).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk379 : ((certRows.drop 6064).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk380 : ((certRows.drop 6080).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk381 : ((certRows.drop 6096).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk382 : ((certRows.drop 6112).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk383 : ((certRows.drop 6128).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk384 : ((certRows.drop 6144).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk385 : ((certRows.drop 6160).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk386 : ((certRows.drop 6176).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk387 : ((certRows.drop 6192).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk388 : ((certRows.drop 6208).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk389 : ((certRows.drop 6224).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk390 : ((certRows.drop 6240).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk391 : ((certRows.drop 6256).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk392 : ((certRows.drop 6272).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk393 : ((certRows.drop 6288).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk394 : ((certRows.drop 6304).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk395 : ((certRows.drop 6320).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk396 : ((certRows.drop 6336).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk397 : ((certRows.drop 6352).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk398 : ((certRows.drop 6368).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk399 : ((certRows.drop 6384).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk400 : ((certRows.drop 6400).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk401 : ((certRows.drop 6416).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk402 : ((certRows.drop 6432).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk403 : ((certRows.drop 6448).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk404 : ((certRows.drop 6464).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk405 : ((certRows.drop 6480).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk406 : ((certRows.drop 6496).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk407 : ((certRows.drop 6512).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk408 : ((certRows.drop 6528).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk409 : ((certRows.drop 6544).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk410 : ((certRows.drop 6560).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def certChunk411 : ((certRows.drop 6576).take 16).all certRowOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def hTable : failTable_review G MK 15 56 true memoTable memoLookup = true := by
  change certRows.all certRowOK = true
  apply all_of_chunks certRows certRowOK 16 412
  · decide +kernel
  · intro i hi
    interval_cases i
    · exact certChunk000
    · exact certChunk001
    · exact certChunk002
    · exact certChunk003
    · exact certChunk004
    · exact certChunk005
    · exact certChunk006
    · exact certChunk007
    · exact certChunk008
    · exact certChunk009
    · exact certChunk010
    · exact certChunk011
    · exact certChunk012
    · exact certChunk013
    · exact certChunk014
    · exact certChunk015
    · exact certChunk016
    · exact certChunk017
    · exact certChunk018
    · exact certChunk019
    · exact certChunk020
    · exact certChunk021
    · exact certChunk022
    · exact certChunk023
    · exact certChunk024
    · exact certChunk025
    · exact certChunk026
    · exact certChunk027
    · exact certChunk028
    · exact certChunk029
    · exact certChunk030
    · exact certChunk031
    · exact certChunk032
    · exact certChunk033
    · exact certChunk034
    · exact certChunk035
    · exact certChunk036
    · exact certChunk037
    · exact certChunk038
    · exact certChunk039
    · exact certChunk040
    · exact certChunk041
    · exact certChunk042
    · exact certChunk043
    · exact certChunk044
    · exact certChunk045
    · exact certChunk046
    · exact certChunk047
    · exact certChunk048
    · exact certChunk049
    · exact certChunk050
    · exact certChunk051
    · exact certChunk052
    · exact certChunk053
    · exact certChunk054
    · exact certChunk055
    · exact certChunk056
    · exact certChunk057
    · exact certChunk058
    · exact certChunk059
    · exact certChunk060
    · exact certChunk061
    · exact certChunk062
    · exact certChunk063
    · exact certChunk064
    · exact certChunk065
    · exact certChunk066
    · exact certChunk067
    · exact certChunk068
    · exact certChunk069
    · exact certChunk070
    · exact certChunk071
    · exact certChunk072
    · exact certChunk073
    · exact certChunk074
    · exact certChunk075
    · exact certChunk076
    · exact certChunk077
    · exact certChunk078
    · exact certChunk079
    · exact certChunk080
    · exact certChunk081
    · exact certChunk082
    · exact certChunk083
    · exact certChunk084
    · exact certChunk085
    · exact certChunk086
    · exact certChunk087
    · exact certChunk088
    · exact certChunk089
    · exact certChunk090
    · exact certChunk091
    · exact certChunk092
    · exact certChunk093
    · exact certChunk094
    · exact certChunk095
    · exact certChunk096
    · exact certChunk097
    · exact certChunk098
    · exact certChunk099
    · exact certChunk100
    · exact certChunk101
    · exact certChunk102
    · exact certChunk103
    · exact certChunk104
    · exact certChunk105
    · exact certChunk106
    · exact certChunk107
    · exact certChunk108
    · exact certChunk109
    · exact certChunk110
    · exact certChunk111
    · exact certChunk112
    · exact certChunk113
    · exact certChunk114
    · exact certChunk115
    · exact certChunk116
    · exact certChunk117
    · exact certChunk118
    · exact certChunk119
    · exact certChunk120
    · exact certChunk121
    · exact certChunk122
    · exact certChunk123
    · exact certChunk124
    · exact certChunk125
    · exact certChunk126
    · exact certChunk127
    · exact certChunk128
    · exact certChunk129
    · exact certChunk130
    · exact certChunk131
    · exact certChunk132
    · exact certChunk133
    · exact certChunk134
    · exact certChunk135
    · exact certChunk136
    · exact certChunk137
    · exact certChunk138
    · exact certChunk139
    · exact certChunk140
    · exact certChunk141
    · exact certChunk142
    · exact certChunk143
    · exact certChunk144
    · exact certChunk145
    · exact certChunk146
    · exact certChunk147
    · exact certChunk148
    · exact certChunk149
    · exact certChunk150
    · exact certChunk151
    · exact certChunk152
    · exact certChunk153
    · exact certChunk154
    · exact certChunk155
    · exact certChunk156
    · exact certChunk157
    · exact certChunk158
    · exact certChunk159
    · exact certChunk160
    · exact certChunk161
    · exact certChunk162
    · exact certChunk163
    · exact certChunk164
    · exact certChunk165
    · exact certChunk166
    · exact certChunk167
    · exact certChunk168
    · exact certChunk169
    · exact certChunk170
    · exact certChunk171
    · exact certChunk172
    · exact certChunk173
    · exact certChunk174
    · exact certChunk175
    · exact certChunk176
    · exact certChunk177
    · exact certChunk178
    · exact certChunk179
    · exact certChunk180
    · exact certChunk181
    · exact certChunk182
    · exact certChunk183
    · exact certChunk184
    · exact certChunk185
    · exact certChunk186
    · exact certChunk187
    · exact certChunk188
    · exact certChunk189
    · exact certChunk190
    · exact certChunk191
    · exact certChunk192
    · exact certChunk193
    · exact certChunk194
    · exact certChunk195
    · exact certChunk196
    · exact certChunk197
    · exact certChunk198
    · exact certChunk199
    · exact certChunk200
    · exact certChunk201
    · exact certChunk202
    · exact certChunk203
    · exact certChunk204
    · exact certChunk205
    · exact certChunk206
    · exact certChunk207
    · exact certChunk208
    · exact certChunk209
    · exact certChunk210
    · exact certChunk211
    · exact certChunk212
    · exact certChunk213
    · exact certChunk214
    · exact certChunk215
    · exact certChunk216
    · exact certChunk217
    · exact certChunk218
    · exact certChunk219
    · exact certChunk220
    · exact certChunk221
    · exact certChunk222
    · exact certChunk223
    · exact certChunk224
    · exact certChunk225
    · exact certChunk226
    · exact certChunk227
    · exact certChunk228
    · exact certChunk229
    · exact certChunk230
    · exact certChunk231
    · exact certChunk232
    · exact certChunk233
    · exact certChunk234
    · exact certChunk235
    · exact certChunk236
    · exact certChunk237
    · exact certChunk238
    · exact certChunk239
    · exact certChunk240
    · exact certChunk241
    · exact certChunk242
    · exact certChunk243
    · exact certChunk244
    · exact certChunk245
    · exact certChunk246
    · exact certChunk247
    · exact certChunk248
    · exact certChunk249
    · exact certChunk250
    · exact certChunk251
    · exact certChunk252
    · exact certChunk253
    · exact certChunk254
    · exact certChunk255
    · exact certChunk256
    · exact certChunk257
    · exact certChunk258
    · exact certChunk259
    · exact certChunk260
    · exact certChunk261
    · exact certChunk262
    · exact certChunk263
    · exact certChunk264
    · exact certChunk265
    · exact certChunk266
    · exact certChunk267
    · exact certChunk268
    · exact certChunk269
    · exact certChunk270
    · exact certChunk271
    · exact certChunk272
    · exact certChunk273
    · exact certChunk274
    · exact certChunk275
    · exact certChunk276
    · exact certChunk277
    · exact certChunk278
    · exact certChunk279
    · exact certChunk280
    · exact certChunk281
    · exact certChunk282
    · exact certChunk283
    · exact certChunk284
    · exact certChunk285
    · exact certChunk286
    · exact certChunk287
    · exact certChunk288
    · exact certChunk289
    · exact certChunk290
    · exact certChunk291
    · exact certChunk292
    · exact certChunk293
    · exact certChunk294
    · exact certChunk295
    · exact certChunk296
    · exact certChunk297
    · exact certChunk298
    · exact certChunk299
    · exact certChunk300
    · exact certChunk301
    · exact certChunk302
    · exact certChunk303
    · exact certChunk304
    · exact certChunk305
    · exact certChunk306
    · exact certChunk307
    · exact certChunk308
    · exact certChunk309
    · exact certChunk310
    · exact certChunk311
    · exact certChunk312
    · exact certChunk313
    · exact certChunk314
    · exact certChunk315
    · exact certChunk316
    · exact certChunk317
    · exact certChunk318
    · exact certChunk319
    · exact certChunk320
    · exact certChunk321
    · exact certChunk322
    · exact certChunk323
    · exact certChunk324
    · exact certChunk325
    · exact certChunk326
    · exact certChunk327
    · exact certChunk328
    · exact certChunk329
    · exact certChunk330
    · exact certChunk331
    · exact certChunk332
    · exact certChunk333
    · exact certChunk334
    · exact certChunk335
    · exact certChunk336
    · exact certChunk337
    · exact certChunk338
    · exact certChunk339
    · exact certChunk340
    · exact certChunk341
    · exact certChunk342
    · exact certChunk343
    · exact certChunk344
    · exact certChunk345
    · exact certChunk346
    · exact certChunk347
    · exact certChunk348
    · exact certChunk349
    · exact certChunk350
    · exact certChunk351
    · exact certChunk352
    · exact certChunk353
    · exact certChunk354
    · exact certChunk355
    · exact certChunk356
    · exact certChunk357
    · exact certChunk358
    · exact certChunk359
    · exact certChunk360
    · exact certChunk361
    · exact certChunk362
    · exact certChunk363
    · exact certChunk364
    · exact certChunk365
    · exact certChunk366
    · exact certChunk367
    · exact certChunk368
    · exact certChunk369
    · exact certChunk370
    · exact certChunk371
    · exact certChunk372
    · exact certChunk373
    · exact certChunk374
    · exact certChunk375
    · exact certChunk376
    · exact certChunk377
    · exact certChunk378
    · exact certChunk379
    · exact certChunk380
    · exact certChunk381
    · exact certChunk382
    · exact certChunk383
    · exact certChunk384
    · exact certChunk385
    · exact certChunk386
    · exact certChunk387
    · exact certChunk388
    · exact certChunk389
    · exact certChunk390
    · exact certChunk391
    · exact certChunk392
    · exact certChunk393
    · exact certChunk394
    · exact certChunk395
    · exact certChunk396
    · exact certChunk397
    · exact certChunk398
    · exact certChunk399
    · exact certChunk400
    · exact certChunk401
    · exact certChunk402
    · exact certChunk403
    · exact certChunk404
    · exact certChunk405
    · exact certChunk406
    · exact certChunk407
    · exact certChunk408
    · exact certChunk409
    · exact certChunk410
    · exact certChunk411

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def hCover : I.sublists.all (fun ws =>
    quickFail_review G 15 56 true 8 ws ||
    tableHit_review memoTable memoLookup 8 ws) = true := by
  decide +kernel

end Reflect

namespace Restrict

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

variable {n : ℕ}

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

lemma mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

lemma mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _


def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L


def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}



def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

lemma agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

lemma agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]


def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

lemma normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

lemma wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]


abbrev Stat := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)



def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]


def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega



lemma elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj



def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2



def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat)) ++ [Sum.inl b]

lemma inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

lemma ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp


lemma supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

lemma inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

lemma inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp




lemma gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Sum.inl false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

lemma helper8_restriction
    (h5 : ¬ ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 8 ∧
      ∀ i j : Fin 5, D.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
        (4443 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 9 ∧
      ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (17051 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  rintro ⟨C, hfan, hsize, heval⟩
  let f : (Fin 6 → Bool) → Bool := fun x => C.eval (List.ofFn x)
  have hdep : ∃ x : Fin 6 → Bool,
      f (Function.update x (Fin.last 5) (!x (Fin.last 5))) ≠ f x := by
    refine ⟨fun k : Fin 6 => decide (k = 0 ∨ k = 0), ?_⟩
    have hx : Function.update (fun k : Fin 6 => decide (k = 0 ∨ k = 0))
        (Fin.last 5) (!(decide (Fin.last 5 = (0 : Fin 6) ∨ Fin.last 5 = (0 : Fin 6)))) =
        (fun k : Fin 6 => decide (k = 0 ∨ k = 5)) := by decide +kernel
    change C.eval (List.ofFn _) ≠ C.eval (List.ofFn _)
    rw [hx, heval 0 5, heval 0 0]
    decide
  have hnc : ∃ y y' : Fin 5 → Bool, f (Fin.snoc y false) ≠ f (Fin.snoc y' false) := by
    refine ⟨fun k : Fin 5 => decide (k = 0 ∨ k = 0),
      fun k : Fin 5 => decide (k = 3 ∨ k = 3), ?_⟩
    have hx0 : (Fin.snoc (fun k : Fin 5 => decide (k = 0 ∨ k = 0)) false : Fin 6 → Bool) =
        (fun k : Fin 6 => decide (k = 0 ∨ k = 0)) := by decide +kernel
    have hx3 : (Fin.snoc (fun k : Fin 5 => decide (k = 3 ∨ k = 3)) false : Fin 6 → Bool) =
        (fun k : Fin 6 => decide (k = 3 ∨ k = 3)) := by decide +kernel
    change C.eval (List.ofFn _) ≠ C.eval (List.ofFn _)
    rw [hx0, hx3, heval 0 0, heval 3 3]
    decide
  have hC : HasCircuitSize 6 f 9 := ⟨C, hfan, hsize, fun _ => rfl⟩
  obtain ⟨D, hDfan, hDsize, hDeval⟩ :=
    gate_elim 5 f false 8 hdep hnc hC
  apply h5
  refine ⟨D, hDfan, hDsize, ?_⟩
  intro i j
  rw [hDeval]
  change C.eval (List.ofFn (Fin.snoc (fun k : Fin 5 => decide (k = i ∨ k = j)) false)) = _
  have hin : ∀ i j : Fin 5,
      (Fin.snoc (fun k : Fin 5 => decide (k = i ∨ k = j)) false : Fin 6 → Bool) =
        (fun k : Fin 6 => decide (k = i.castSucc ∨ k = j.castSucc)) := by decide +kernel
  rw [hin i j, heval]
  have hbits : ∀ i j : Fin 5,
      (17051 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) =
        (4443 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by decide +kernel
  exact hbits i j

end Restrict

lemma memo_conditional
    (hTable : Reflect.failTable_review Reflect.G Reflect.MK 15 56 true
      Reflect.memoTable Reflect.memoLookup = true)
    (hCover : Reflect.I.sublists.all (fun ws =>
      Reflect.quickFail_review Reflect.G 15 56 true 8 ws ||
      Reflect.tableHit_review Reflect.memoTable Reflect.memoLookup 8 ws) = true) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6,
      C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (17051 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact Restrict.helper8_restriction (Reflect.five_lower hTable hCover)

end PEqualNP.Outside.L_meta_24717

theorem PEqualNP.Outside.L_meta_24717 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17051 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact PEqualNP.Outside.L_meta_24717.memo_conditional
    PEqualNP.Outside.L_meta_24717.Reflect.hTable
    PEqualNP.Outside.L_meta_24717.Reflect.hCover
