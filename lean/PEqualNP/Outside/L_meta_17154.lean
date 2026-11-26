import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17154_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

section Cycle

variable {n : ℕ}

def nxt (hn : 3 ≤ n) (a : Fin (2 * n)) : Fin (2 * n) :=
  ⟨(a.val + 1) % (2 * n), Nat.mod_lt _ (by omega)⟩

def prv (hn : 3 ≤ n) (a : Fin (2 * n)) : Fin (2 * n) :=
  ⟨(a.val + 2 * n - 1) % (2 * n), Nat.mod_lt _ (by omega)⟩

lemma nxt_val (hn : 3 ≤ n) (a : Fin (2 * n)) :
    (nxt hn a).val = if a.val + 1 < 2 * n then a.val + 1 else 0 := by
  simp only [nxt]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have : a.val + 1 = 2 * n := by omega
    rw [this, Nat.mod_self]

lemma prv_val (hn : 3 ≤ n) (a : Fin (2 * n)) :
    (prv hn a).val = if a.val = 0 then 2 * n - 1 else a.val - 1 := by
  simp only [prv]
  split_ifs with h
  · rw [h]; simp only [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
  · have h1 : a.val + 2 * n - 1 = (a.val - 1) + 2 * n := by omega
    rw [h1, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

lemma nxt_prv (hn : 3 ≤ n) (a : Fin (2 * n)) : nxt hn (prv hn a) = a := by
  apply Fin.ext
  rw [nxt_val, prv_val]
  split_ifs at * <;> omega

lemma prv_nxt (hn : 3 ≤ n) (a : Fin (2 * n)) : prv hn (nxt hn a) = a := by
  apply Fin.ext
  rw [prv_val, nxt_val]
  split_ifs at * <;> omega

lemma nxt_inj (hn : 3 ≤ n) : Function.Injective (nxt hn) := fun a b h => by
  have := congrArg (prv hn) h
  rwa [prv_nxt, prv_nxt] at this

lemma prv_inj (hn : 3 ≤ n) : Function.Injective (prv hn) := fun a b h => by
  have := congrArg (nxt hn) h
  rwa [nxt_prv, nxt_prv] at this

lemma nxt_ne_self (hn : 3 ≤ n) (a : Fin (2 * n)) : nxt hn a ≠ a := by
  intro h
  have := congrArg Fin.val h
  rw [nxt_val] at this
  split_ifs at this <;> omega

lemma nxt2_ne_self (hn : 3 ≤ n) (a : Fin (2 * n)) : nxt hn (nxt hn a) ≠ a := by
  intro h
  have := congrArg Fin.val h
  rw [nxt_val, nxt_val] at this
  split_ifs at this <;> omega

lemma nxt3_ne_self (hn : 3 ≤ n) (a : Fin (2 * n)) : nxt hn (nxt hn (nxt hn a)) ≠ a := by
  intro h
  have := congrArg Fin.val h
  rw [nxt_val, nxt_val, nxt_val] at this
  split_ifs at this <;> omega

lemma nxt4_ne_self (hn : 3 ≤ n) (a : Fin (2 * n)) :
    nxt hn (nxt hn (nxt hn (nxt hn a))) ≠ a := by
  intro h
  have := congrArg Fin.val h
  rw [nxt_val, nxt_val, nxt_val, nxt_val] at this
  split_ifs at this <;> omega

lemma nxt_ne_prv (hn : 3 ≤ n) (a : Fin (2 * n)) : nxt hn a ≠ prv hn a := by
  intro h
  have h1 := congrArg (nxt hn) h
  rw [nxt_prv] at h1
  exact nxt2_ne_self hn a h1

def rightV (v : Fin n) : Fin (2 * n) := ⟨2 * v.val, by omega⟩
def leftV (u : Fin n) : Fin (2 * n) := ⟨2 * u.val + 1, by omega⟩

def toWire (a : Fin (2 * n)) : ℕ :=
  if a.val % 2 = 1 then a.val / 2 else n + a.val / 2

def fromWire (w : ℕ) (hw : w < 2 * n) : Fin (2 * n) :=
  if h : w < n then leftV ⟨w, h⟩ else rightV ⟨w - n, by omega⟩

lemma toWire_leftV (u : Fin n) : toWire (leftV u) = u.val := by
  simp only [toWire, leftV]
  have h1 : (2 * u.val + 1) % 2 = 1 := by omega
  have h2 : (2 * u.val + 1) / 2 = u.val := by omega
  simp [h1, h2]

lemma toWire_rightV (v : Fin n) : toWire (rightV v) = n + v.val := by
  simp only [toWire, rightV]
  have h1 : (2 * v.val) % 2 ≠ 1 := by omega
  have h2 : (2 * v.val) / 2 = v.val := by omega
  simp [h1, h2]

lemma toWire_lt (a : Fin (2 * n)) : toWire a < 2 * n := by
  simp only [toWire]
  split_ifs <;> omega

lemma toWire_fromWire (w : ℕ) (hw : w < 2 * n) : toWire (fromWire w hw) = w := by
  simp only [fromWire]
  split_ifs with h
  · rw [toWire_leftV]
  · rw [toWire_rightV]; dsimp; omega

lemma fromWire_toWire (a : Fin (2 * n)) : fromWire (toWire a) (toWire_lt a) = a := by
  apply Fin.ext
  simp only [fromWire, toWire]
  split_ifs <;> simp only [leftV, rightV] <;> omega

lemma toWire_inj : Function.Injective (@toWire n) := fun a b h => by
  have h1 : fromWire (toWire a) (toWire_lt a) = fromWire (toWire b) (toWire_lt b) := by
    congr 1
  rwa [fromWire_toWire, fromWire_toWire] at h1

lemma leftV_ne_rightV (u v : Fin n) : leftV u ≠ rightV v := by
  intro h
  have := congrArg Fin.val h
  simp only [leftV, rightV] at this
  omega

def cycAdj (hn : 3 ≤ n) (a b : Fin (2 * n)) : Prop :=
  b = nxt hn a ∨ a = nxt hn b

lemma cycAdj_symm (hn : 3 ≤ n) {a b : Fin (2 * n)} (h : cycAdj hn a b) : cycAdj hn b a :=
  h.symm

lemma cycAdj_parity (hn : 3 ≤ n) {a b : Fin (2 * n)} (h : cycAdj hn a b) :
    a.val % 2 ≠ b.val % 2 := by
  rcases h with rfl | rfl <;> rw [nxt_val] <;> split_ifs <;> omega

lemma cycAdj_left_right (hn : 3 ≤ n) (u v : Fin n) :
    cycAdj hn (leftV u) (rightV v) ↔ (v.val = u.val ∨ v.val = (u.val + 1) % n) := by
  have hlu : (leftV u).val = 2 * u.val + 1 := rfl
  have hrv : (rightV v).val = 2 * v.val := rfl
  unfold cycAdj
  constructor
  · rintro (h | h)
    · have hv := congrArg Fin.val h
      rw [nxt_val] at hv
      split_ifs at hv with hlt
      · simp only [hlu, hrv] at hv hlt
        right; have : u.val + 1 < n := by omega
        rw [Nat.mod_eq_of_lt this]; omega
      · simp only [hlu, hrv] at hv hlt
        right; have : u.val + 1 = n := by omega
        rw [this, Nat.mod_self]; omega
    · have hv := congrArg Fin.val h
      rw [nxt_val] at hv
      split_ifs at hv with hlt
      · simp only [hlu, hrv] at hv hlt; left; omega
      · simp only [hlu, hrv] at hv hlt; omega
  · rintro (h | h)
    · right
      apply Fin.ext
      rw [nxt_val]
      split_ifs with hlt <;> simp only [hlu, hrv] at * <;> omega
    · left
      apply Fin.ext
      rw [nxt_val]
      by_cases hlt : u.val + 1 < n
      · rw [Nat.mod_eq_of_lt hlt] at h
        split_ifs with hlt2 <;> simp only [hlu, hrv] at * <;> omega
      · have heq : u.val + 1 = n := by omega
        rw [heq, Nat.mod_self] at h
        split_ifs with hlt2 <;> simp only [hlu, hrv] at * <;> omega

lemma exists_non_adj_right (hn : 3 ≤ n) (u : Fin n) :
    ∃ v : Fin n, ¬ cycAdj hn (leftV u) (rightV v) := by
  by_cases h0 : u.val = 0
  · refine ⟨⟨2, by omega⟩, ?_⟩
    rw [cycAdj_left_right]; dsimp
    have hmod : (u.val + 1) % n = 1 := by rw [h0]; exact Nat.mod_eq_of_lt (by omega)
    rw [hmod]; omega
  · by_cases h1 : u.val + 1 = n
    · refine ⟨⟨1, by omega⟩, ?_⟩
      rw [cycAdj_left_right]; dsimp
      rw [h1, Nat.mod_self]
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      rw [cycAdj_left_right]; dsimp
      have hmod : (u.val + 1) % n = u.val + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hmod]; omega

lemma exists_non_adj_left (hn : 3 ≤ n) (v : Fin n) :
    ∃ u : Fin n, ¬ cycAdj hn (leftV u) (rightV v) := by
  by_cases h0 : v.val = 0
  · refine ⟨⟨1, by omega⟩, ?_⟩
    rw [cycAdj_left_right]; dsimp
    have hmod : (1 + 1) % n = 2 := Nat.mod_eq_of_lt (by omega)
    rw [hmod]; omega
  · by_cases h1 : v.val = 1
    · refine ⟨⟨2, by omega⟩, ?_⟩
      rw [cycAdj_left_right]; dsimp
      by_cases h2 : 3 = n
      · have hmod : (2 + 1) % n = 0 := by rw [← h2, Nat.mod_self]
        rw [hmod]; omega
      · have hmod : (2 + 1) % n = 3 := Nat.mod_eq_of_lt (by omega)
        rw [hmod]; omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      rw [cycAdj_left_right]; dsimp
      have hmod : (0 + 1) % n = 1 := Nat.mod_eq_of_lt (by omega)
      rw [hmod]; omega

def starts (hn : 3 ≤ n) (S : Finset (Fin (2 * n))) : Finset (Fin (2 * n)) :=
  S.filter fun a => prv hn a ∉ S

def NoShortRun (hn : 3 ≤ n) (S : Finset (Fin (2 * n))) : Prop :=
  ∀ a ∈ S, prv hn a ∉ S →
    nxt hn a ∈ S ∧ nxt hn (nxt hn a) ∈ S ∧ nxt hn (nxt hn (nxt hn a)) ∈ S

def phiZ (hn : 3 ≤ n) (S : Finset (Fin (2 * n))) : ℤ :=
  (S.card : ℤ) - 3 * ((starts hn S).card : ℤ)

def phi (hn : 3 ≤ n) (S : Finset (Fin (2 * n))) : ℕ :=
  S.card - 3 * (starts hn S).card

lemma noShortRun_univ (hn : 3 ≤ n) : NoShortRun hn Finset.univ := by
  intro a _ h; exact (h (Finset.mem_univ _)).elim

lemma starts_univ (hn : 3 ≤ n) : starts hn Finset.univ = ∅ := by
  ext a; simp [starts]

lemma phi_univ (hn : 3 ≤ n) : phi hn Finset.univ = 2 * n := by
  simp [phi, starts_univ]

lemma noShortRun_deg_pos (hn : 3 ≤ n) {S : Finset (Fin (2 * n))}
    (hS : NoShortRun hn S) {a : Fin (2 * n)} (ha : a ∈ S) :
    ∃ b ∈ S, cycAdj hn a b := by
  by_cases hp : prv hn a ∈ S
  · exact ⟨prv hn a, hp, Or.inr (nxt_prv hn a).symm⟩
  · exact ⟨nxt hn a, (hS a ha hp).1, Or.inl rfl⟩

lemma noShortRun_no_isolated_edge (hn : 3 ≤ n) {S : Finset (Fin (2 * n))}
    (hS : NoShortRun hn S) {a b : Fin (2 * n)} (ha : a ∈ S) (hb : b ∈ S)
    (hab : cycAdj hn a b) :
    (∃ c ∈ S, c ≠ b ∧ cycAdj hn a c) ∨ (∃ c ∈ S, c ≠ a ∧ cycAdj hn b c) := by
  rcases hab with rfl | rfl
  · by_cases hp : prv hn a ∈ S
    · exact Or.inl ⟨prv hn a, hp, (nxt_ne_prv hn a).symm, Or.inr (nxt_prv hn a).symm⟩
    · refine Or.inr ⟨nxt hn (nxt hn a), (hS a ha hp).2.1, ?_, Or.inl rfl⟩
      exact nxt2_ne_self hn a
  · by_cases hp : prv hn b ∈ S
    · exact Or.inr ⟨prv hn b, hp, (nxt_ne_prv hn b).symm, Or.inr (nxt_prv hn b).symm⟩
    · refine Or.inl ⟨nxt hn (nxt hn b), (hS b hb hp).2.1, ?_, Or.inl rfl⟩
      exact nxt2_ne_self hn b

lemma noShortRun_no_twin (hn : 3 ≤ n) {S : Finset (Fin (2 * n))}
    (hS : NoShortRun hn S) {a b : Fin (2 * n)} (ha : a ∈ S) (hb : b ∈ S)
    (hne : a ≠ b) :
    ∃ c ∈ S, (cycAdj hn a c ∧ ¬ cycAdj hn b c) ∨ (cycAdj hn b c ∧ ¬ cycAdj hn a c) := by
  by_contra hno
  push_neg at hno
  have hsame : ∀ c ∈ S, cycAdj hn a c ↔ cycAdj hn b c := fun c hc =>
    ⟨(hno c hc).1, (hno c hc).2⟩
  obtain ⟨c, hc, hac⟩ := noShortRun_deg_pos hn hS ha
  have hbc := (hsame c hc).mp hac
  rcases hac with rfl | rfl
  · rcases hbc with h1 | h1
    · exact hne (nxt_inj hn h1)
    ·
      have hpa : prv hn a ∉ S := by
        intro hp
        have hbp := (hsame (prv hn a) hp).mp (Or.inr (nxt_prv hn a).symm)
        rcases hbp with h2 | h2
        · have h3 := congrArg (nxt hn) h2
          rw [nxt_prv, h1] at h3
          exact nxt4_ne_self hn a h3.symm
        · have h3 := congrArg (nxt hn) h2
          rw [nxt_prv] at h3
          rw [h1] at h3
          exact nxt2_ne_self hn a (nxt_inj hn h3)
      have h3 := (hS a ha hpa).2.2
      have hnb : cycAdj hn b (nxt hn (nxt hn (nxt hn a))) := Or.inl (by rw [h1])
      have hanb := (hsame _ h3).mpr hnb
      rcases hanb with h2 | h2
      · exact nxt2_ne_self hn (nxt hn a) h2
      · exact nxt4_ne_self hn a h2.symm
  · rcases hbc with h1 | h1
    ·
      have hpb : prv hn b ∉ S := by
        intro hp
        have hap := (hsame (prv hn b) hp).mpr (Or.inr (nxt_prv hn b).symm)
        rcases hap with h2 | h2
        · have h3 := congrArg (nxt hn) h2
          rw [nxt_prv, h1] at h3
          exact nxt4_ne_self hn b h3.symm
        · have h3 := congrArg (nxt hn) h2
          rw [nxt_prv, h1] at h3
          exact nxt2_ne_self hn b (nxt_inj hn h3)
      have h3 := (hS b hb hpb).2.2
      have hna : cycAdj hn (nxt hn c) (nxt hn (nxt hn (nxt hn b))) := Or.inl (by rw [h1])
      have hbna := (hsame _ h3).mp hna
      rcases hbna with h2 | h2
      · exact nxt2_ne_self hn (nxt hn b) h2
      · exact nxt4_ne_self hn b h2.symm
    · exact hne (by rw [h1])

lemma four_mul_starts_le (hn : 3 ≤ n) {S : Finset (Fin (2 * n))} (hS : NoShortRun hn S) :
    4 * (starts hn S).card ≤ S.card := by
  let f : Fin (2 * n) × Fin 4 → Fin (2 * n) := fun p =>
    match p.2.val with
    | 0 => p.1
    | 1 => nxt hn p.1
    | 2 => nxt hn (nxt hn p.1)
    | _ => nxt hn (nxt hn (nxt hn p.1))
  have hsub : ((starts hn S) ×ˢ (Finset.univ : Finset (Fin 4))).image f ⊆ S := by
    intro y hy
    obtain ⟨⟨a, k⟩, hk, rfl⟩ := Finset.mem_image.mp hy
    have ha := Finset.mem_filter.mp (Finset.mem_product.mp hk).1
    have hrun := hS a ha.1 ha.2
    fin_cases k
    · exact ha.1
    · exact hrun.1
    · exact hrun.2.1
    · exact hrun.2.2
  have hinj : Set.InjOn f ↑((starts hn S) ×ˢ (Finset.univ : Finset (Fin 4))) := by
    rintro ⟨a, i⟩ hi ⟨b, j⟩ hj heq
    have ha := Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_coe.mp hi)).1
    have hb := Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_coe.mp hj)).1
    have hstep1 : ∀ {x y : Fin (2 * n)}, x ∈ S → prv hn x ∉ S → y ∈ S → prv hn y ∉ S →
        nxt hn x ≠ y := by
      intro x y hx _ _ hpy hxy; exact hpy (by rw [← hxy, prv_nxt]; exact hx)
    have hstep2 : ∀ {x y : Fin (2 * n)}, x ∈ S → prv hn x ∉ S → y ∈ S → prv hn y ∉ S →
        nxt hn (nxt hn x) ≠ y := by
      intro x y hx hpx _ hpy hxy; exact hpy (by rw [← hxy, prv_nxt]; exact (hS x hx hpx).1)
    have hstep3 : ∀ {x y : Fin (2 * n)}, x ∈ S → prv hn x ∉ S → y ∈ S → prv hn y ∉ S →
        nxt hn (nxt hn (nxt hn x)) ≠ y := by
      intro x y hx hpx _ hpy hxy; exact hpy (by rw [← hxy, prv_nxt]; exact (hS x hx hpx).2.1)
    fin_cases i <;> fin_cases j <;> simp only [f] at heq
    · exact Prod.ext heq rfl
    · exact (hstep1 hb.1 hb.2 ha.1 ha.2 heq.symm).elim
    · exact (hstep2 hb.1 hb.2 ha.1 ha.2 heq.symm).elim
    · exact (hstep3 hb.1 hb.2 ha.1 ha.2 heq.symm).elim
    · exact (hstep1 ha.1 ha.2 hb.1 hb.2 heq).elim
    · exact Prod.ext (nxt_inj hn heq) rfl
    · exact (hstep1 hb.1 hb.2 ha.1 ha.2 (nxt_inj hn heq).symm).elim
    · exact (hstep2 hb.1 hb.2 ha.1 ha.2 (nxt_inj hn heq).symm).elim
    · exact (hstep2 ha.1 ha.2 hb.1 hb.2 heq).elim
    · exact (hstep1 ha.1 ha.2 hb.1 hb.2 (nxt_inj hn heq)).elim
    · exact Prod.ext (nxt_inj hn (nxt_inj hn heq)) rfl
    · exact (hstep1 hb.1 hb.2 ha.1 ha.2 (nxt_inj hn (nxt_inj hn heq)).symm).elim
    · exact (hstep3 ha.1 ha.2 hb.1 hb.2 heq).elim
    · exact (hstep2 ha.1 ha.2 hb.1 hb.2 (nxt_inj hn heq)).elim
    · exact (hstep1 ha.1 ha.2 hb.1 hb.2 (nxt_inj hn (nxt_inj hn heq))).elim
    · exact Prod.ext (nxt_inj hn (nxt_inj hn (nxt_inj hn heq))) rfl
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_univ, Fintype.card_fin] at hcard
  omega

lemma phiZ_eq_phi (hn : 3 ≤ n) {S : Finset (Fin (2 * n))} (hS : NoShortRun hn S) :
    phiZ hn S = (phi hn S : ℤ) := by
  have h := four_mul_starts_le hn hS
  unfold phiZ phi
  omega

lemma nonempty_of_phi_pos (hn : 3 ≤ n) {S : Finset (Fin (2 * n))} (h : 0 < phi hn S) :
    S.Nonempty := by
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  subst hemp
  simp [phi, starts] at h

lemma card_ge_four_of_nonempty (hn : 3 ≤ n) {S : Finset (Fin (2 * n))}
    (hS : NoShortRun hn S) (hne : S.Nonempty) : 4 ≤ S.card := by
  by_cases hu : S = Finset.univ
  · subst hu; simp; omega
  · have hst : (starts hn S).Nonempty := by
      by_contra h0
      rw [Finset.not_nonempty_iff_eq_empty] at h0
      have hclosed : ∀ a ∈ S, prv hn a ∈ S := by
        intro a ha
        by_contra hp
        have : a ∈ starts hn S := Finset.mem_filter.mpr ⟨ha, hp⟩
        rw [h0] at this; exact Finset.notMem_empty a this
      obtain ⟨a0, ha0⟩ := hne
      have hwalk : ∀ k : ℕ, (prv hn)^[k] a0 ∈ S := by
        intro k
        induction k with
        | zero => exact ha0
        | succ k ih => rw [Function.iterate_succ_apply']; exact hclosed _ ih
      have hval : ∀ k : ℕ, ((prv hn)^[k] a0).val = (a0.val + 2 * n * k - k) % (2 * n) := by
        intro k
        induction k with
        | zero => simp [Nat.mod_eq_of_lt a0.isLt]
        | succ k ih =>
          rw [Function.iterate_succ_apply', prv_val, ih]
          set m := (a0.val + 2 * n * k - k) % (2 * n)
          have hm : m < 2 * n := Nat.mod_lt _ (by omega)
          have hstep : (a0.val + 2 * n * (k + 1) - (k + 1)) = (a0.val + 2 * n * k - k) + (2 * n - 1) := by
            have hmul : 2 * n * (k + 1) = 2 * n * k + 2 * n := Nat.mul_succ _ _
            have : k ≤ 2 * n * k := Nat.le_mul_of_pos_left k (by omega)
            omega
          rw [hstep, Nat.add_mod]
          change _ = (m + (2 * n - 1) % (2 * n)) % (2 * n)
          rw [Nat.mod_eq_of_lt (by omega : 2 * n - 1 < 2 * n)]
          split_ifs with h0m
          · rw [h0m, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
          · have : m + (2 * n - 1) = (m - 1) + 2 * n := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      apply hu
      ext b
      simp only [Finset.mem_univ, iff_true]
      let k := (a0.val + 2 * n - b.val) % (2 * n)
      have hbk : (prv hn)^[k] a0 = b := by
        apply Fin.ext
        rw [hval k]
        have hk : k < 2 * n := Nat.mod_lt _ (by omega)

        by_cases hle : b.val ≤ a0.val
        · have hkval : k = a0.val - b.val := by
            dsimp [k]
            have : a0.val + 2 * n - b.val = (a0.val - b.val) + 2 * n := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          have : a0.val + 2 * n * k - k = b.val + 2 * n * k := by omega
          rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
        · have hkval : k = a0.val + 2 * n - b.val := by
            dsimp [k]; exact Nat.mod_eq_of_lt (by omega)
          have : a0.val + 2 * n * k - k = b.val + 2 * n * (k - 1) := by
            have hkpos : 1 ≤ k := by omega
            have : 2 * n * k = 2 * n * (k - 1) + 2 * n := by
              rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hkpos]
            omega
          rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]
      rw [← hbk]
      exact hwalk k
    have h4 := four_mul_starts_le hn hS
    have hpos := Finset.card_pos.mpr hst
    omega

lemma phiZ_erase_ge (hn : 3 ≤ n) (S : Finset (Fin (2 * n))) {x : Fin (2 * n)} (hx : x ∈ S) :
    phiZ hn S - 4 ≤ phiZ hn (S.erase x) := by
  have hsub : starts hn (S.erase x) ⊆ insert (nxt hn x) (starts hn S) := by
    intro a ha
    rw [starts, Finset.mem_filter] at ha
    have haS : a ∈ S := Finset.mem_of_mem_erase ha.1
    by_cases hax : a = nxt hn x
    · exact hax ▸ Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨haS, ?_⟩)
      intro hpS
      have hne : prv hn a ≠ x := fun h => hax (by rw [← h, nxt_prv])
      exact ha.2 (Finset.mem_erase.mpr ⟨hne, hpS⟩)
  have hcardSt : (starts hn (S.erase x)).card ≤ (starts hn S).card + 1 :=
    (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hcardS : (S.erase x).card + 1 = S.card := Finset.card_erase_add_one hx
  unfold phiZ
  omega

lemma exists_trim_step (hn : 3 ≤ n) (T : Finset (Fin (2 * n))) (hnot : ¬ NoShortRun hn T) :
    ∃ T' : Finset (Fin (2 * n)), T' ⊂ T ∧ phiZ hn T ≤ phiZ hn T' := by
  unfold NoShortRun at hnot
  push_neg at hnot
  obtain ⟨a, haT, hpa, hbad⟩ := hnot
  have haSt : a ∈ starts hn T := Finset.mem_filter.mpr ⟨haT, hpa⟩
  by_cases h1 : nxt hn a ∉ T
  · refine ⟨T.erase a, Finset.erase_ssubset haT, ?_⟩
    have hst : starts hn (T.erase a) ⊆ (starts hn T).erase a := by
      intro b hb
      rw [starts, Finset.mem_filter] at hb
      have hbne : b ≠ a := (Finset.mem_erase.mp hb.1).1
      have hbT : b ∈ T := (Finset.mem_erase.mp hb.1).2
      refine Finset.mem_erase.mpr ⟨hbne, Finset.mem_filter.mpr ⟨hbT, ?_⟩⟩
      intro hpT
      have hpa' : prv hn b ≠ a := fun h => h1 (by rw [← h, nxt_prv]; exact hbT)
      exact hb.2 (Finset.mem_erase.mpr ⟨hpa', hpT⟩)
    have hcs := (Finset.card_le_card hst).trans_eq (Finset.card_erase_of_mem haSt)
    have hct := Finset.card_erase_add_one haT
    have hpos : 1 ≤ (starts hn T).card := Finset.card_pos.mpr ⟨a, haSt⟩
    unfold phiZ; omega
  · push_neg at h1
    by_cases h2 : nxt hn (nxt hn a) ∉ T
    · let R : Finset (Fin (2 * n)) := {a, nxt hn a}
      have hRsub : R ⊆ T := by
        intro b hb; simp only [R, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl <;> assumption
      have hRcard : R.card = 2 := Finset.card_pair (nxt_ne_self hn a).symm
      refine ⟨T \ R, Finset.sdiff_ssubset hRsub ⟨a, by simp [R]⟩, ?_⟩
      have hst : starts hn (T \ R) ⊆ (starts hn T).erase a := by
        intro b hb
        rw [starts, Finset.mem_filter, Finset.mem_sdiff] at hb
        have hbne : b ≠ a := fun h => hb.1.2 (by simp [R, h])
        refine Finset.mem_erase.mpr ⟨hbne, Finset.mem_filter.mpr ⟨hb.1.1, ?_⟩⟩
        intro hpT
        have hpR : prv hn b ∉ R := by
          intro hmem
          simp only [R, Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h | h
          · exact hb.1.2 (by simp [R, ← h, nxt_prv])
          · exact h2 (by rw [← h, nxt_prv]; exact hb.1.1)
        exact hb.2 (Finset.mem_sdiff.mpr ⟨hpT, hpR⟩)
      have hcs := (Finset.card_le_card hst).trans_eq (Finset.card_erase_of_mem haSt)
      have hct : (T \ R).card + R.card = T.card := Finset.card_sdiff_add_card_eq_card hRsub
      have hpos : 1 ≤ (starts hn T).card := Finset.card_pos.mpr ⟨a, haSt⟩
      unfold phiZ; omega
    · push_neg at h2
      have h3 : nxt hn (nxt hn (nxt hn a)) ∉ T := fun h => hbad h1 h2 h
      let R : Finset (Fin (2 * n)) := {a, nxt hn a, nxt hn (nxt hn a)}
      have hRsub : R ⊆ T := by
        intro b hb; simp only [R, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl | rfl <;> assumption
      have hRcard : R.card = 3 := by
        have h12 : a ≠ nxt hn a := (nxt_ne_self hn a).symm
        have h13 : a ≠ nxt hn (nxt hn a) := (nxt2_ne_self hn a).symm
        have h23 : nxt hn a ≠ nxt hn (nxt hn a) := (nxt_ne_self hn (nxt hn a)).symm
        simp [R, h12, h13, h23]
      refine ⟨T \ R, Finset.sdiff_ssubset hRsub ⟨a, by simp [R]⟩, ?_⟩
      have hst : starts hn (T \ R) ⊆ (starts hn T).erase a := by
        intro b hb
        rw [starts, Finset.mem_filter, Finset.mem_sdiff] at hb
        have hbne : b ≠ a := fun h => hb.1.2 (by simp [R, h])
        refine Finset.mem_erase.mpr ⟨hbne, Finset.mem_filter.mpr ⟨hb.1.1, ?_⟩⟩
        intro hpT
        have hpR : prv hn b ∉ R := by
          intro hmem
          simp only [R, Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with h | h | h
          · exact hb.1.2 (by simp [R, ← h, nxt_prv])
          · exact hb.1.2 (by simp [R, ← h, nxt_prv])
          · exact h3 (by rw [← h, nxt_prv]; exact hb.1.1)
        exact hb.2 (Finset.mem_sdiff.mpr ⟨hpT, hpR⟩)
      have hcs := (Finset.card_le_card hst).trans_eq (Finset.card_erase_of_mem haSt)
      have hct : (T \ R).card + R.card = T.card := Finset.card_sdiff_add_card_eq_card hRsub
      have hpos : 1 ≤ (starts hn T).card := Finset.card_pos.mpr ⟨a, haSt⟩
      unfold phiZ; omega

lemma exists_trimmed (hn : 3 ≤ n) (T : Finset (Fin (2 * n))) :
    ∃ T' : Finset (Fin (2 * n)), T' ⊆ T ∧ NoShortRun hn T' ∧ phiZ hn T ≤ phiZ hn T' := by
  induction hk : T.card using Nat.strong_induction_on generalizing T with
  | ind k ih =>
    by_cases hgood : NoShortRun hn T
    · exact ⟨T, Finset.Subset.refl T, hgood, le_rfl⟩
    · obtain ⟨T1, hss, hphi⟩ := exists_trim_step hn T hgood
      have hlt : T1.card < k := hk ▸ Finset.card_lt_card hss
      obtain ⟨T', hsub', hgood', hphi'⟩ := ih T1.card hlt T1 rfl
      exact ⟨T', hsub'.trans hss.subset, hgood', hphi.trans hphi'⟩

lemma trim1_exists (hn : 3 ≤ n) {S : Finset (Fin (2 * n))} (hS : NoShortRun hn S)
    {x : Fin (2 * n)} (hx : x ∈ S) :
    ∃ S' : Finset (Fin (2 * n)), S' ⊆ S ∧ x ∉ S' ∧ NoShortRun hn S' ∧ phi hn S ≤ phi hn S' + 4 := by
  obtain ⟨S', hsub, hgood, hphi⟩ := exists_trimmed hn (S.erase x)
  have h1 := phiZ_erase_ge hn S hx
  have h2 := le_trans h1 hphi
  rw [phiZ_eq_phi hn hS, phiZ_eq_phi hn hgood] at h2
  refine ⟨S', hsub.trans (Finset.erase_subset x S), fun hm => (Finset.mem_erase.mp (hsub hm)).1 rfl, hgood, ?_⟩
  omega

lemma trim_le2_exists (hn : 3 ≤ n) {S : Finset (Fin (2 * n))} (hS : NoShortRun hn S)
    (L : Finset (Fin (2 * n))) (hLsub : L ⊆ S) (hLcard : L.card ≤ 2) :
    ∃ S' : Finset (Fin (2 * n)), S' ⊆ S ∧ Disjoint L S' ∧ NoShortRun hn S' ∧
      phi hn S ≤ phi hn S' + 8 := by
  by_cases h0 : L = ∅
  · subst h0; exact ⟨S, Finset.Subset.refl S, Finset.disjoint_empty_left S, hS, by omega⟩
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr h0
    obtain ⟨S1, hS1sub, hx1, hgood1, hphi1⟩ := trim1_exists hn hS (hLsub hx)
    by_cases h1 : (L.erase x) = ∅
    · refine ⟨S1, hS1sub, Finset.disjoint_left.mpr fun a ha ha1 => ?_, hgood1, by omega⟩
      have : a = x := by
        by_contra hne
        have : a ∈ L.erase x := Finset.mem_erase.mpr ⟨hne, ha⟩
        rw [h1] at this; exact Finset.notMem_empty a this
      exact hx1 (this ▸ ha1)
    · obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr h1
      have hyne : y ≠ x := (Finset.mem_erase.mp hy).1
      have hyL : y ∈ L := (Finset.mem_erase.mp hy).2
      have hLpair : L = {x, y} := by
        have hsub2 : ({x, y} : Finset _) ⊆ L := by
          intro a ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
          rcases ha with rfl | rfl <;> assumption
        have hc2 : ({x, y} : Finset _).card = 2 := Finset.card_pair hyne.symm
        exact (Finset.eq_of_subset_of_card_le hsub2 (by omega)).symm
      by_cases hy1 : y ∈ S1
      · obtain ⟨S2, hS2sub, hy2, hgood2, hphi2⟩ := trim1_exists hn hgood1 hy1
        refine ⟨S2, hS2sub.trans hS1sub, ?_, hgood2, by omega⟩
        rw [hLpair, Finset.disjoint_left]
        intro a ha ha2
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact hx1 (hS2sub ha2)
        · exact hy2 ha2
      · refine ⟨S1, hS1sub, ?_, hgood1, by omega⟩
        rw [hLpair, Finset.disjoint_left]
        intro a ha ha1
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl
        · exact hx1 ha1
        · exact hy1 ha1

end Cycle

section BDag

abbrev BGate := Bool × ℕ × ℕ
abbrev BDag := List BGate

def evalOp (op : Bool) (a b : Bool) : Bool :=
  if op then a && b else a || b

def bstep (w : List Bool) (g : BGate) : List Bool :=
  w ++ [evalOp g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

def evalBDag (D : BDag) (x : List Bool) : List Bool :=
  D.foldl bstep x

lemma bstep_length (w : List Bool) (g : BGate) : (bstep w g).length = w.length + 1 := by
  simp [bstep]

lemma evalBDag_length (D : BDag) (x : List Bool) :
    (evalBDag D x).length = x.length + D.length := by
  induction D generalizing x with
  | nil => simp [evalBDag]
  | cons g gs ih =>
    simp only [evalBDag, List.foldl_cons] at ih ⊢
    rw [ih, bstep_length, List.length_cons]
    omega

lemma evalBDag_getD_lt (D : BDag) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (evalBDag D x).getD i false = x.getD i false := by
  induction D generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [evalBDag, List.foldl_cons] at ih ⊢
    rw [ih (bstep x g) (by rw [bstep_length]; omega)]
    simp only [bstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma evalBDag_append (D1 D2 : BDag) (x : List Bool) :
    evalBDag (D1 ++ D2) x = evalBDag D2 (evalBDag D1 x) := by
  simp [evalBDag, List.foldl_append]

lemma evalBDag_gate (D : BDag) (x : List Bool) (j : ℕ) (hj : j < D.length) :
    (evalBDag D x).getD (x.length + j) false =
      evalOp (D[j]).1 ((evalBDag D x).getD (D[j]).2.1 false)
        ((evalBDag D x).getD (D[j]).2.2 false) → True := fun _ => trivial

def WellFormed (m : ℕ) (D : BDag) : Prop :=
  ∀ j (hj : j < D.length), (D[j]).2.1 < m + j ∧ (D[j]).2.2 < m + j ∧ (D[j]).2.1 ≠ (D[j]).2.2

lemma evalBDag_at_gate {m : ℕ} {D : BDag} (hWF : WellFormed m D) (x : List Bool)
    (hx : x.length = m) (j : ℕ) (hj : j < D.length) :
    (evalBDag D x).getD (m + j) false =
      evalOp (D[j]).1 ((evalBDag D x).getD (D[j]).2.1 false)
        ((evalBDag D x).getD (D[j]).2.2 false) := by
  have hsplit : D = D.take j ++ [D[j]] ++ D.drop (j + 1) := by
    have h2 : D.drop j = D[j] :: D.drop (j + 1) := List.drop_eq_getElem_cons hj
    calc D = D.take j ++ D.drop j := (List.take_append_drop j D).symm
      _ = D.take j ++ (D[j] :: D.drop (j + 1)) := by rw [h2]
      _ = D.take j ++ [D[j]] ++ D.drop (j + 1) := by simp [List.append_assoc]
  have hlen : (evalBDag (D.take j) x).length = m + j := by
    rw [evalBDag_length, hx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hpref : ∀ i < m + j, (evalBDag D x).getD i false = (evalBDag (D.take j) x).getD i false := by
    intro i hi
    conv_lhs => rw [hsplit]
    rw [evalBDag_append, evalBDag_append,
        evalBDag_getD_lt _ _ i (by rw [evalBDag_length, hlen]; simp; omega),
        evalBDag_getD_lt _ _ i (by rw [hlen]; exact hi)]
  obtain ⟨ha, hb, _⟩ := hWF j hj
  rw [hpref _ ha, hpref _ hb]
  conv_lhs => rw [hsplit]
  rw [evalBDag_append, evalBDag_append,
      evalBDag_getD_lt _ _ (m + j) (by rw [evalBDag_length, hlen]; simp)]
  simp only [evalBDag, List.foldl_cons, List.foldl_nil, bstep]
  rw [← hlen]
  simp only [evalBDag, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

lemma evalBDag_mono (D : BDag) (x y : List Bool) (hlen : x.length = y.length)
    (hle : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (evalBDag D x).getD i false = true → (evalBDag D y).getD i false = true := by
  induction D generalizing x y with
  | nil => exact hle
  | cons g gs ih =>
    simp only [evalBDag, List.foldl_cons] at ih ⊢
    apply ih (bstep x g) (bstep y g) (by simp [bstep, hlen])
    intro i hi
    by_cases hlt : i < x.length
    · rw [bstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hi
      rw [bstep, List.getD_eq_getElem?_getD, List.getElem?_append_left (hlen ▸ hlt)]
      exact hle i (by simpa [List.getD_eq_getElem?_getD] using hi)
    · by_cases heq : i = x.length
      · subst heq
        simp only [bstep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hi
        rw [bstep, hlen, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        cases h1 : g.1 <;> simp only [evalOp, h1, Bool.false_eq_true, ite_true, ite_false] at hi ⊢
        · rw [Bool.or_eq_true] at hi ⊢
          exact hi.imp (hle _) (hle _)
        · rw [Bool.and_eq_true] at hi ⊢
          exact ⟨hle _ hi.1, hle _ hi.2⟩
      · have hge : (bstep x g).length ≤ i := by simp [bstep]; omega
        rw [List.getD_eq_default _ _ hge] at hi
        exact Bool.noConfusion hi

inductive WireRef
  | cFalse
  | cTrue
  | wire (idx : ℕ)
  deriving DecidableEq

def evalRef (w : List Bool) : WireRef → Bool
  | .cFalse => false
  | .cTrue => true
  | .wire i => w.getD i false

def refOk (lim : ℕ) : WireRef → Prop
  | .cFalse => True
  | .cTrue => True
  | .wire i => i < lim

def foldBin (m : ℕ) (D : BDag) (op : Bool) (r1 r2 : WireRef) : BDag × WireRef :=
  if op then
    match r1, r2 with
    | .cFalse, _ => (D, .cFalse)
    | _, .cFalse => (D, .cFalse)
    | .cTrue, r => (D, r)
    | r, .cTrue => (D, r)
    | .wire a, .wire b =>
      if a = b then (D, .wire a) else (D ++ [(true, a, b)], .wire (m + D.length))
  else
    match r1, r2 with
    | .cTrue, _ => (D, .cTrue)
    | _, .cTrue => (D, .cTrue)
    | .cFalse, r => (D, r)
    | r, .cFalse => (D, r)
    | .wire a, .wire b =>
      if a = b then (D, .wire a) else (D ++ [(false, a, b)], .wire (m + D.length))

lemma foldBin_spec (m : ℕ) (D : BDag) (hWF : WellFormed m D) (op : Bool) (r1 r2 : WireRef)
    (hr1 : refOk (m + D.length) r1) (hr2 : refOk (m + D.length) r2) :
    let res := foldBin m D op r1 r2
    WellFormed m res.1 ∧
    (D.length ≤ res.1.length ∧ res.1.length ≤ D.length + 1) ∧
    refOk (m + res.1.length) res.2 ∧
    (∀ (x : List Bool), x.length = m →
      (∀ i < m + D.length, (evalBDag res.1 x).getD i false = (evalBDag D x).getD i false) ∧
      evalRef (evalBDag res.1 x) res.2 =
        evalOp op (evalRef (evalBDag D x) r1) (evalRef (evalBDag D x) r2)) := by
  dsimp only
  unfold foldBin
  cases op
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases r1 <;> cases r2 <;> dsimp only
    · exact ⟨hWF, ⟨le_rfl, by omega⟩, trivial, fun x _ => ⟨fun _ _ => rfl, rfl⟩⟩
    · exact ⟨hWF, ⟨le_rfl, by omega⟩, trivial, fun x _ => ⟨fun _ _ => rfl, rfl⟩⟩
    · exact ⟨hWF, ⟨le_rfl, by omega⟩, hr2, fun x _ => ⟨fun _ _ => rfl, by simp [evalRef, evalOp]⟩⟩
    · exact ⟨hWF, ⟨le_rfl, by omega⟩, trivial, fun x _ => ⟨fun _ _ => rfl, rfl⟩⟩
    · exact ⟨hWF, ⟨le_rfl, by omega⟩, trivial, fun x _ => ⟨fun _ _ => rfl, rfl⟩⟩
    · exact ⟨hWF, ⟨le_rfl, by omega⟩, trivial, fun x _ => ⟨fun _ _ => rfl, by simp [evalRef, evalOp]⟩⟩
    · exact ⟨hWF, ⟨le_rfl, by omega⟩, hr1, fun x _ => ⟨fun _ _ => rfl, by simp [evalRef, evalOp]⟩⟩
    · exact ⟨hWF, ⟨le_rfl, by omega⟩, trivial, fun x _ => ⟨fun _ _ => rfl, by simp [evalRef, evalOp]⟩⟩
    · rename_i a b
      split_ifs with hab
      · subst hab; dsimp only
        exact ⟨hWF, ⟨le_rfl, by omega⟩, hr1, fun x _ => ⟨fun _ _ => rfl, by simp [evalRef, evalOp]⟩⟩
      · refine ⟨?_, ⟨by simp, by simp⟩, by simp [refOk], fun x hx => ?_⟩
        · intro j hj
          simp only [List.length_append, List.length_singleton] at hj
          by_cases hlt : j < D.length
          · simpa [List.getElem_append_left hlt] using hWF j hlt
          · have heq : j = D.length := by omega
            subst heq
            simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero]
            exact ⟨hr1, hr2, hab⟩
        · have hlen : (evalBDag D x).length = m + D.length := by rw [evalBDag_length, hx]
          refine ⟨fun i hi => ?_, ?_⟩
          · rw [evalBDag_append, evalBDag_getD_lt _ _ i (by rw [hlen]; exact hi)]
          · rw [evalBDag_append]
            simp only [evalRef, evalBDag, List.foldl_cons, List.foldl_nil, bstep]
            rw [← hlen]
            simp only [evalBDag, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  · simp only [↓reduceIte]
    cases r1 <;> cases r2 <;> dsimp only
    · exact ⟨hWF, ⟨le_rfl, by omega⟩, trivial, fun x _ => ⟨fun _ _ => rfl, rfl⟩⟩
    · exact ⟨hWF, ⟨le_rfl, by omega⟩, trivial, fun x _ => ⟨fun _ _ => rfl, rfl⟩⟩
    · exact ⟨hWF, ⟨le_rfl, by omega⟩, trivial, fun x _ => ⟨fun _ _ => rfl, by simp [evalRef, evalOp]⟩⟩
    · exact ⟨hWF, ⟨le_rfl, by omega⟩, trivial, fun x _ => ⟨fun _ _ => rfl, rfl⟩⟩
    · exact ⟨hWF, ⟨le_rfl, by omega⟩, trivial, fun x _ => ⟨fun _ _ => rfl, rfl⟩⟩
    · exact ⟨hWF, ⟨le_rfl, by omega⟩, hr2, fun x _ => ⟨fun _ _ => rfl, by simp [evalRef, evalOp]⟩⟩
    · exact ⟨hWF, ⟨le_rfl, by omega⟩, trivial, fun x _ => ⟨fun _ _ => rfl, by simp [evalRef, evalOp]⟩⟩
    · exact ⟨hWF, ⟨le_rfl, by omega⟩, hr1, fun x _ => ⟨fun _ _ => rfl, by simp [evalRef, evalOp]⟩⟩
    · rename_i a b
      split_ifs with hab
      · subst hab; dsimp only
        exact ⟨hWF, ⟨le_rfl, by omega⟩, hr1, fun x _ => ⟨fun _ _ => rfl, by simp [evalRef, evalOp]⟩⟩
      · refine ⟨?_, ⟨by simp, by simp⟩, by simp [refOk], fun x hx => ?_⟩
        · intro j hj
          simp only [List.length_append, List.length_singleton] at hj
          by_cases hlt : j < D.length
          · simpa [List.getElem_append_left hlt] using hWF j hlt
          · have heq : j = D.length := by omega
            subst heq
            simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero]
            exact ⟨hr1, hr2, hab⟩
        · have hlen : (evalBDag D x).length = m + D.length := by rw [evalBDag_length, hx]
          refine ⟨fun i hi => ?_, ?_⟩
          · rw [evalBDag_append, evalBDag_getD_lt _ _ i (by rw [hlen]; exact hi)]
          · rw [evalBDag_append]
            simp only [evalRef, evalBDag, List.foldl_cons, List.foldl_nil, bstep]
            rw [← hlen]
            simp only [evalBDag, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl,
              Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

lemma foldBin_ne_cTrue (m : ℕ) (D : BDag) (op : Bool) (r1 r2 : WireRef)
    (hr1 : r1 ≠ .cTrue) (hr2 : r2 ≠ .cTrue) : (foldBin m D op r1 r2).2 ≠ .cTrue := by
  unfold foldBin
  cases op
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases r1 with
    | cTrue => exact (hr1 rfl).elim
    | cFalse => cases r2 with | cTrue => exact (hr2 rfl).elim | _ => simp
    | wire a =>
      cases r2 with
      | cTrue => exact (hr2 rfl).elim
      | cFalse => simp
      | wire b => dsimp only; split_ifs <;> simp
  · simp only [↓reduceIte]
    cases r1 with
    | cTrue => exact (hr1 rfl).elim
    | cFalse => cases r2 <;> simp
    | wire a =>
      cases r2 with
      | cTrue => exact (hr2 rfl).elim
      | cFalse => simp
      | wire b => dsimp only; split_ifs <;> simp

lemma foldBin_eq_cFalse_iff (m : ℕ) (D : BDag) (op : Bool) (r1 r2 : WireRef)
    (hr1 : r1 ≠ .cTrue) (hr2 : r2 ≠ .cTrue) :
    (foldBin m D op r1 r2).2 = .cFalse ↔
      (op = true ∧ (r1 = .cFalse ∨ r2 = .cFalse)) ∨
      (op = false ∧ r1 = .cFalse ∧ r2 = .cFalse) := by
  unfold foldBin
  cases op
  · simp only [Bool.false_eq_true, ↓reduceIte, false_and, true_and, false_or]
    cases r1 with
    | cTrue => exact (hr1 rfl).elim
    | cFalse => cases r2 <;> simp
    | wire a =>
      cases r2 with
      | cTrue => exact (hr2 rfl).elim
      | cFalse => simp
      | wire b => dsimp only; split_ifs <;> simp
  · simp only [↓reduceIte, true_and, Bool.true_eq_false, false_and, or_false]
    cases r1 with
    | cTrue => exact (hr1 rfl).elim
    | cFalse => cases r2 <;> simp
    | wire a =>
      cases r2 with
      | cTrue => exact (hr2 rfl).elim
      | cFalse => simp
      | wire b => dsimp only; split_ifs <;> simp

lemma foldBin_len_of_cFalse (m : ℕ) (D : BDag) (op : Bool) (r1 r2 : WireRef)
    (h : r1 = .cFalse ∨ r2 = .cFalse) : (foldBin m D op r1 r2).1.length = D.length := by
  unfold foldBin
  cases op <;> rcases h with rfl | rfl
  · simp only [Bool.false_eq_true, ↓reduceIte]; cases r2 <;> rfl
  · simp only [Bool.false_eq_true, ↓reduceIte]; cases r1 <;> rfl
  · simp only [↓reduceIte]
  · simp only [↓reduceIte]; cases r1 <;> rfl

lemma refOk_mono {a b : ℕ} (h : a ≤ b) {r : WireRef} (hr : refOk a r) : refOk b r := by
  cases r with
  | cFalse => trivial
  | cTrue => trivial
  | wire i => exact Nat.lt_of_lt_of_le hr h

lemma evalRef_congr {w1 w2 : List Bool} {lim : ℕ} (r : WireRef) (hr : refOk lim r)
    (heq : ∀ i < lim, w1.getD i false = w2.getD i false) :
    evalRef w1 r = evalRef w2 r := by
  cases r with
  | cFalse => rfl
  | cTrue => rfl
  | wire i => exact heq i hr

lemma compile_monotone2 (m : ℕ) (C : Circuit) (hmono : Monotone2 C) :
    ∃ (D : BDag) (r : WireRef),
      WellFormed m D ∧ D.length ≤ C.gates.length ∧ refOk (m + D.length) r ∧
      ∀ x : List Bool, x.length = m → evalRef (evalBDag D x) r = C.eval x := by
  suffices h : ∀ (gs : List Gate), (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      ∃ (D : BDag) (env : List WireRef),
        WellFormed m D ∧ D.length ≤ gs.length ∧ env.length = m + gs.length ∧
        (∀ r ∈ env, refOk (m + D.length) r) ∧
        ∀ x : List Bool, x.length = m → ∀ i,
          evalRef (evalBDag D x) (env.getD i .cFalse) =
            (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) x).getD i false by
    obtain ⟨D, env, hWF, hlen, _, hok, hev⟩ := h C.gates hmono
    refine ⟨D, env.getD C.output .cFalse, hWF, hlen, ?_, fun x hx => hev x hx C.output⟩
    by_cases ho : C.output < env.length
    · rw [List.getD_eq_getElem _ _ ho]; exact hok _ (List.getElem_mem ho)
    · rw [List.getD_eq_default _ _ (by omega)]; trivial
  intro gs hgs
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], List.ofFn (fun i : Fin m => WireRef.wire i.val), fun j hj => by simp at hj,
      le_rfl, by simp, ?_, ?_⟩
    · intro r hr
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
      simpa [refOk] using i.isLt
    · intro x hx i
      by_cases hi : i < m
      · rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]; rfl
      · simp only [List.foldl_nil]
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by rw [hx]; omega)]; rfl
  | append_singleton gs g ih =>
    obtain ⟨D, env, hWF, hlen, helen, hok, hev⟩ :=
      ih (fun g' hg' => hgs g' (List.mem_append_left _ hg'))
    obtain ⟨hgop, hgin⟩ := hgs g (List.mem_append_right _ (List.mem_singleton_self _))
    have hgetOk : ∀ k, refOk (m + D.length) (env.getD k .cFalse) := by
      intro k
      by_cases hk : k < env.length
      · rw [List.getD_eq_getElem _ _ hk]; exact hok _ (List.getElem_mem hk)
      · rw [List.getD_eq_default _ _ (by omega)]; trivial
    have hfoldlen : ∀ x : List Bool, x.length = m →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) x).length = m + gs.length := by
      intro x hx
      have : ∀ (ls : List Gate) (w : List Bool),
          (ls.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) w).length = w.length + ls.length := by
        intro ls
        induction ls with
        | nil => intro w; simp
        | cons a as iha =>
          intro w; rw [List.foldl_cons, iha]; simp; omega
      rw [this, hx]
    have hstepRef : ∀ (op : Bool) (r1 r2 : WireRef),
        refOk (m + D.length) r1 → refOk (m + D.length) r2 →
        (∀ x : List Bool, x.length = m →
          g.op.eval (g.inputs.map fun k =>
            (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) x).getD k false) =
          evalOp op (evalRef (evalBDag D x) r1) (evalRef (evalBDag D x) r2)) →
        ∃ (D' : BDag) (env' : List WireRef),
          WellFormed m D' ∧ D'.length ≤ (gs ++ [g]).length ∧ env'.length = m + (gs ++ [g]).length ∧
          (∀ r ∈ env', refOk (m + D'.length) r) ∧
          ∀ x : List Bool, x.length = m → ∀ i,
            evalRef (evalBDag D' x) (env'.getD i .cFalse) =
              ((gs ++ [g]).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) x).getD i false := by
      intro op r1 r2 hr1 hr2 hgeval
      obtain ⟨hWF', ⟨hDle, hDle1⟩, hrOk', hspec⟩ := foldBin_spec m D hWF op r1 r2 hr1 hr2
      set res := foldBin m D op r1 r2
      refine ⟨res.1, env ++ [res.2], hWF', by simp; omega, by simp [helen]; omega, ?_, ?_⟩
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact refOk_mono (by omega) (hok r hr)
        · rw [List.mem_singleton.mp hr]; exact hrOk'
      · intro x hx i
        obtain ⟨hpref, hval⟩ := hspec x hx
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        set W := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) x
        have hWlen : W.length = m + gs.length := hfoldlen x hx
        by_cases hi : i < m + gs.length
        · rw [List.getD_append _ _ _ _ (by rw [helen]; exact hi),
              List.getD_append _ _ _ _ (by rw [hWlen]; exact hi)]
          rw [evalRef_congr _ (hgetOk i) hpref, hev x hx i]
        · by_cases heq : i = m + gs.length
          · subst heq
            rw [List.getD_append_right _ _ _ _ (by rw [helen]), helen, Nat.sub_self,
                List.getD_cons_zero,
                List.getD_append_right _ _ _ _ (by rw [hWlen]), hWlen, Nat.sub_self,
                List.getD_cons_zero]
            rw [hval, hgeval x hx]
          · rw [List.getD_eq_default _ _ (by simp [helen]; omega),
                List.getD_eq_default _ _ (by simp [hWlen]; omega)]
            rfl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgop
    rcases hgop with hop | hop
    · cases hli : g.inputs with
      | nil =>
        exact hstepRef true .cTrue .cTrue trivial trivial (fun x hx => by simp [hop, hli, GateOp.eval, evalOp, evalRef])
      | cons a rest =>
        cases rest with
        | nil =>
          exact hstepRef true (env.getD a .cFalse) .cTrue (hgetOk a) trivial
            (fun x hx => by
              rw [hop, hli, GateOp.eval]
              simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
                Bool.and_true, evalOp, evalRef, ite_true]
              exact (hev x hx a).symm)
        | cons b rest2 =>
          cases rest2 with
          | nil =>
            exact hstepRef true (env.getD a .cFalse) (env.getD b .cFalse) (hgetOk a) (hgetOk b)
              (fun x hx => by
                rw [hop, hli, GateOp.eval]
                simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
                  Bool.and_true, evalOp, ite_true]
                rw [hev x hx a, hev x hx b])
          | cons _ _ => simp [hli] at hgin
    · cases hli : g.inputs with
      | nil =>
        exact hstepRef false .cFalse .cFalse trivial trivial (fun x hx => by simp [hop, hli, GateOp.eval, evalOp, evalRef])
      | cons a rest =>
        cases rest with
        | nil =>
          exact hstepRef false (env.getD a .cFalse) .cFalse (hgetOk a) trivial
            (fun x hx => by
              rw [hop, hli, GateOp.eval]
              simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                Bool.or_false, evalOp, evalRef, Bool.false_eq_true, ite_false]
              exact (hev x hx a).symm)
        | cons b rest2 =>
          cases rest2 with
          | nil =>
            exact hstepRef false (env.getD a .cFalse) (env.getD b .cFalse) (hgetOk a) (hgetOk b)
              (fun x hx => by
                rw [hop, hli, GateOp.eval]
                simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
                  Bool.or_false, evalOp, Bool.false_eq_true, ite_false]
                rw [hev x hx a, hev x hx b])
          | cons _ _ => simp [hli] at hgin

def zeroStep (m : ℕ) (killGate : ℕ → Bool) (st : BDag × List WireRef × ℕ) (g : BGate) :
    BDag × List WireRef × ℕ :=
  let (D', env, j) := st
  if killGate j then
    (D', env ++ [.cFalse], j + 1)
  else
    let r1 := env.getD g.2.1 .cFalse
    let r2 := env.getD g.2.2 .cFalse
    let (D'', r) := foldBin m D' g.1 r1 r2
    (D'', env ++ [r], j + 1)

def zeroFold (m : ℕ) (killIn : ℕ → Bool) (killGate : ℕ → Bool) (D : BDag) :
    BDag × List WireRef :=
  let initEnv : List WireRef := List.ofFn fun i : Fin m => if killIn i.val then .cFalse else .wire i.val
  let res := D.foldl (zeroStep m killGate) ([], initEnv, 0)
  (res.1, res.2.1)

lemma zeroFold_spec (m : ℕ) (killIn : ℕ → Bool) (killGate : ℕ → Bool) (D : BDag)
    (hWF : WellFormed m D) :
    let res := zeroFold m killIn killGate D
    WellFormed m res.1 ∧
    res.2.length = m + D.length ∧
    (∀ r ∈ res.2, refOk (m + res.1.length) r ∧ r ≠ .cTrue) ∧
    (∀ i < m, res.2.getD i .cFalse = if killIn i then .cFalse else .wire i) ∧
    (∀ j (hj : j < D.length),
      res.2.getD (m + j) .cFalse = .cFalse ↔
        killGate j = true ∨
        ((D[j]).1 = true ∧ (res.2.getD (D[j]).2.1 .cFalse = .cFalse ∨ res.2.getD (D[j]).2.2 .cFalse = .cFalse)) ∨
        ((D[j]).1 = false ∧ res.2.getD (D[j]).2.1 .cFalse = .cFalse ∧ res.2.getD (D[j]).2.2 .cFalse = .cFalse)) ∧
    res.1.length ≤ (Finset.range D.length |>.filter fun j =>
      if hj : j < D.length then
        killGate j = false ∧
        res.2.getD (D[j]).2.1 .cFalse ≠ .cFalse ∧
        res.2.getD (D[j]).2.2 .cFalse ≠ .cFalse
      else false).card ∧
    (∀ (x : List Bool), x.length = m →
      (∀ j < D.length, killGate j = true →
        (evalBDag D (List.ofFn fun i : Fin m => if killIn i.val then false else x.getD i.val false)).getD (m + j) false = false) →
      ∀ k < m + D.length,
        evalRef (evalBDag res.1 x) (res.2.getD k .cFalse) =
          (evalBDag D (List.ofFn fun i : Fin m => if killIn i.val then false else x.getD i.val false)).getD k false) := by
  suffices h : ∀ (D0 : BDag), WellFormed m D0 →
      let st := D0.foldl (zeroStep m killGate)
        ([], List.ofFn (fun i : Fin m => if killIn i.val then .cFalse else .wire i.val), 0)
      st.2.2 = D0.length ∧
      WellFormed m st.1 ∧
      st.2.1.length = m + D0.length ∧
      (∀ r ∈ st.2.1, refOk (m + st.1.length) r ∧ r ≠ .cTrue) ∧
      (∀ i < m, st.2.1.getD i .cFalse = if killIn i then .cFalse else .wire i) ∧
      (∀ j (hj : j < D0.length),
        st.2.1.getD (m + j) .cFalse = .cFalse ↔
          killGate j = true ∨
          ((D0[j]).1 = true ∧ (st.2.1.getD (D0[j]).2.1 .cFalse = .cFalse ∨ st.2.1.getD (D0[j]).2.2 .cFalse = .cFalse)) ∨
          ((D0[j]).1 = false ∧ st.2.1.getD (D0[j]).2.1 .cFalse = .cFalse ∧ st.2.1.getD (D0[j]).2.2 .cFalse = .cFalse)) ∧
      st.1.length ≤ (Finset.range D0.length |>.filter fun j =>
        if hj : j < D0.length then
          killGate j = false ∧
          st.2.1.getD (D0[j]).2.1 .cFalse ≠ .cFalse ∧
          st.2.1.getD (D0[j]).2.2 .cFalse ≠ .cFalse
        else false).card ∧
      (∀ (x : List Bool), x.length = m →
        (∀ j < D0.length, killGate j = true →
          (evalBDag D0 (List.ofFn fun i : Fin m => if killIn i.val then false else x.getD i.val false)).getD (m + j) false = false) →
        ∀ k < m + D0.length,
          evalRef (evalBDag st.1 x) (st.2.1.getD k .cFalse) =
            (evalBDag D0 (List.ofFn fun i : Fin m => if killIn i.val then false else x.getD i.val false)).getD k false) by
    have := h D hWF
    exact ⟨this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2.1, this.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2⟩
  intro D0 hWF0
  induction D0 using List.reverseRecOn with
  | nil =>
    refine ⟨rfl, fun j hj => by simp at hj, by simp, ?_, ?_, fun j hj => by simp at hj, by simp, ?_⟩
    · intro r hr
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
      split_ifs <;> simp [refOk, i.isLt]
    · intro i hi
      simp only [List.foldl_nil]
      rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]
    · intro x hx _ k hk
      simp only [List.length_nil, Nat.add_zero, List.foldl_nil] at hk ⊢
      rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]
      simp only [evalBDag, List.foldl_nil]
      rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]
      split_ifs <;> rfl
  | append_singleton gs g ih =>
    have hWFgs : WellFormed m gs := fun j hj => by
      have h := hWF0 j (by simp; omega)
      simpa [List.getElem_append_left hj] using h
    obtain ⟨hj_eq, hWF', helen, hok, hin, hiff, hcnt, hev⟩ := ih hWFgs
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set st := gs.foldl (zeroStep m killGate)
      ([], List.ofFn (fun i : Fin m => if killIn i.val then .cFalse else .wire i.val), 0)
    set D' := st.1
    set env := st.2.1
    have hst_j : st.2.2 = gs.length := hj_eq
    have hga : g.2.1 < m + gs.length := by
      have h := hWF0 gs.length (by simp)
      simpa using h.1
    have hgb : g.2.2 < m + gs.length := by
      have h := hWF0 gs.length (by simp)
      simpa using h.2.1
    have hgetOk : ∀ k < m + gs.length, refOk (m + D'.length) (env.getD k .cFalse) ∧ env.getD k .cFalse ≠ .cTrue := by
      intro k hk
      rw [List.getD_eq_getElem _ _ (by rw [helen]; exact hk)]
      exact hok _ (List.getElem_mem _)
    have hlen_app : (gs ++ [g]).length = gs.length + 1 := by simp
    have hget_old : ∀ (r : WireRef) (k : ℕ), k < m + gs.length →
        (env ++ [r]).getD k .cFalse = env.getD k .cFalse := fun r k hk =>
      List.getD_append _ _ _ _ (by rw [helen]; exact hk)
    have hget_new : ∀ (r : WireRef), (env ++ [r]).getD (m + gs.length) .cFalse = r := fun r => by
      rw [List.getD_append_right _ _ _ _ (by rw [helen]), helen, Nat.sub_self, List.getD_cons_zero]
    have hfold_alive : ∀ (r : WireRef),
        (Finset.range gs.length |>.filter fun j =>
          if hj : j < gs.length then
            killGate j = false ∧
            env.getD (gs[j]).2.1 .cFalse ≠ .cFalse ∧
            env.getD (gs[j]).2.2 .cFalse ≠ .cFalse
          else false) ⊆
        (Finset.range (gs ++ [g]).length |>.filter fun j =>
          if hj : j < (gs ++ [g]).length then
            killGate j = false ∧
            (env ++ [r]).getD ((gs ++ [g])[j]).2.1 .cFalse ≠ .cFalse ∧
            (env ++ [r]).getD ((gs ++ [g])[j]).2.2 .cFalse ≠ .cFalse
          else false) := by
      intro r j hj
      rw [Finset.mem_filter, Finset.mem_range] at hj ⊢
      have hjlt : j < gs.length := hj.1
      have hj1 : j < (gs ++ [g]).length := by simp; omega
      refine ⟨hj1, ?_⟩
      simp only [hjlt, hj1, ↓reduceDIte] at hj ⊢
      have hga' := (hWFgs j hjlt).1
      have hgb' := (hWFgs j hjlt).2.1
      rw [List.getElem_append_left hjlt, hget_old r _ (by omega : (gs[j]).2.1 < m + gs.length),
        hget_old r _ (by omega : (gs[j]).2.2 < m + gs.length)]
      exact hj.2

    simp only [zeroStep, hst_j]
    split_ifs with hkill
    ·
      refine ⟨by simp [hst_j], hWF', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · change (env ++ [WireRef.cFalse]).length = m + (gs ++ [g]).length
        simp only [List.length_append, List.length_singleton, helen]; omega
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hok r hr
        · rw [List.mem_singleton.mp hr]; exact ⟨trivial, by decide⟩
      · intro i hi; rw [hget_old _ i (by omega)]; exact hin i hi
      · intro j hj
        by_cases hlt : j < gs.length
        · have hga' := (hWFgs j hlt).1; have hgb' := (hWFgs j hlt).2.1
          rw [List.getElem_append_left hlt, hget_old _ (m + j) (by omega),
            hget_old _ _ (by omega : (gs[j]).2.1 < m + gs.length),
            hget_old _ _ (by omega : (gs[j]).2.2 < m + gs.length)]
          exact hiff j hlt
        · have heq : j = gs.length := by simp at hj; omega
          subst heq
          rw [hget_new]
          simp [hkill]
      · refine hcnt.trans (Finset.card_le_card fun j hj => ?_)
        have h1 := hfold_alive .cFalse hj
        rw [Finset.mem_filter, Finset.mem_range] at h1 ⊢
        refine ⟨h1.1, ?_⟩
        dsimp only at h1 ⊢
        simp only [h1.1, ↓reduceDIte] at h1 ⊢
        exact h1.2
      · intro x hx hkillEv k hk
        set x0 := List.ofFn fun i : Fin m => if killIn i.val then false else x.getD i.val false
        have hx0len : x0.length = m := by simp [x0]
        have hkillEv_gs : ∀ j < gs.length, killGate j = true → (evalBDag gs x0).getD (m + j) false = false := by
          intro j hj hkj
          have h1 := hkillEv j (by simp; omega) hkj
          rw [evalBDag_append, evalBDag_getD_lt _ _ (m + j) (by rw [evalBDag_length, hx0len]; omega)] at h1
          exact h1
        by_cases hlt : k < m + gs.length
        · rw [hget_old _ k hlt, evalBDag_append,
              evalBDag_getD_lt _ _ k (by rw [evalBDag_length, hx0len]; exact hlt)]
          exact hev x hx hkillEv_gs k hlt
        · have heq : k = m + gs.length := by simp at hk; omega
          subst heq
          rw [hget_new]
          exact (hkillEv gs.length (by simp) hkill).symm
    ·
      set r1 := env.getD g.2.1 .cFalse
      set r2 := env.getD g.2.2 .cFalse
      obtain ⟨hr1ok, hr1nt⟩ := hgetOk g.2.1 hga
      obtain ⟨hr2ok, hr2nt⟩ := hgetOk g.2.2 hgb
      obtain ⟨hWF'', ⟨hDle, hDle1⟩, hrOk'', hspec⟩ := foldBin_spec m D' hWF' g.1 r1 r2 hr1ok hr2ok
      set res := foldBin m D' g.1 r1 r2
      have hDle' : D'.length ≤ res.1.length := hDle
      have hDle1' : res.1.length ≤ D'.length + 1 := hDle1
      have hres_nt : res.2 ≠ .cTrue := foldBin_ne_cTrue m D' g.1 r1 r2 hr1nt hr2nt
      have hres_cf : res.2 = .cFalse ↔
          (g.1 = true ∧ (r1 = .cFalse ∨ r2 = .cFalse)) ∨
          (g.1 = false ∧ r1 = .cFalse ∧ r2 = .cFalse) :=
        foldBin_eq_cFalse_iff m D' g.1 r1 r2 hr1nt hr2nt
      have hres_len : r1 = .cFalse ∨ r2 = .cFalse → res.1.length = D'.length :=
        foldBin_len_of_cFalse m D' g.1 r1 r2
      refine ⟨by simp [hst_j], hWF'', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · change (env ++ [res.2]).length = m + (gs ++ [g]).length
        simp only [List.length_append, List.length_singleton, helen]; omega
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact ⟨refOk_mono (Nat.add_le_add_left hDle' m) (hok r hr).1, (hok r hr).2⟩
        · rw [List.mem_singleton.mp hr]; exact ⟨hrOk'', hres_nt⟩
      · intro i hi; rw [hget_old _ i (by omega)]; exact hin i hi
      · intro j hj
        by_cases hlt : j < gs.length
        · have hga' := (hWFgs j hlt).1; have hgb' := (hWFgs j hlt).2.1
          rw [List.getElem_append_left hlt, hget_old _ (m + j) (by omega),
            hget_old _ _ (by omega : (gs[j]).2.1 < m + gs.length),
            hget_old _ _ (by omega : (gs[j]).2.2 < m + gs.length)]
          exact hiff j hlt
        · have heq : j = gs.length := by simp at hj; omega
          subst heq
          have hst_env : st.2.1 = env := rfl
          dsimp only
          rw [hst_env]
          simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero,
            hget_new, hget_old _ g.2.1 hga, hget_old _ g.2.2 hgb, Bool.eq_false_iff.mpr hkill,
            Bool.false_eq_true, false_or]
          exact hres_cf
      · change res.1.length ≤ _
        by_cases hzero : r1 = .cFalse ∨ r2 = .cFalse
        · rw [hres_len hzero]
          refine hcnt.trans (Finset.card_le_card fun j hj => ?_)
          have h1 := hfold_alive res.2 hj
          rw [Finset.mem_filter, Finset.mem_range] at h1 ⊢
          refine ⟨h1.1, ?_⟩
          dsimp only at h1 ⊢
          simp only [h1.1, ↓reduceDIte] at h1 ⊢
          exact h1.2
        · push_neg at hzero
          have hmem : gs.length ∈ (Finset.range (gs ++ [g]).length |>.filter fun j =>
              if hj : j < (gs ++ [g]).length then
                killGate j = false ∧
                (env ++ [res.2]).getD ((gs ++ [g])[j]).2.1 .cFalse ≠ .cFalse ∧
                (env ++ [res.2]).getD ((gs ++ [g])[j]).2.2 .cFalse ≠ .cFalse
              else false) := by
            rw [Finset.mem_filter, Finset.mem_range]
            refine ⟨by simp, ?_⟩
            have hj1 : gs.length < (gs ++ [g]).length := by simp
            simp only [hj1, ↓reduceDIte, List.getElem_append_right le_rfl, Nat.sub_self,
              List.getElem_cons_zero, hget_old _ g.2.1 hga, hget_old _ g.2.2 hgb]
            exact ⟨Bool.eq_false_iff.mpr hkill, hzero.1, hzero.2⟩
          have hnotmem : gs.length ∉ (Finset.range gs.length |>.filter fun j =>
              if hj : j < gs.length then
                killGate j = false ∧
                env.getD (gs[j]).2.1 .cFalse ≠ .cFalse ∧
                env.getD (gs[j]).2.2 .cFalse ≠ .cFalse
              else false) := by
            simp
          have hss := Finset.insert_subset_iff.mpr ⟨hmem, hfold_alive res.2⟩
          have hc := Finset.card_le_card hss
          rw [Finset.card_insert_of_notMem hnotmem] at hc
          have hcnt' : D'.length ≤ (Finset.range gs.length |>.filter fun j =>
              if hj : j < gs.length then
                killGate j = false ∧
                env.getD (gs[j]).2.1 .cFalse ≠ .cFalse ∧
                env.getD (gs[j]).2.2 .cFalse ≠ .cFalse
              else false).card := hcnt
          refine (hDle1'.trans (Nat.add_le_add_right hcnt' 1)).trans (hc.trans (Finset.card_le_card fun j hj => ?_))
          rw [Finset.mem_filter, Finset.mem_range] at hj ⊢
          refine ⟨hj.1, ?_⟩
          dsimp only at hj ⊢
          simp only [hj.1, ↓reduceDIte] at hj ⊢
          exact hj.2
      · intro x hx hkillEv k hk
        set x0 := List.ofFn fun i : Fin m => if killIn i.val then false else x.getD i.val false
        have hx0len : x0.length = m := by simp [x0]
        have hkillEv_gs : ∀ j < gs.length, killGate j = true → (evalBDag gs x0).getD (m + j) false = false := by
          intro j hj hkj
          have h1 := hkillEv j (by simp; omega) hkj
          rw [evalBDag_append, evalBDag_getD_lt _ _ (m + j) (by rw [evalBDag_length, hx0len]; omega)] at h1
          exact h1
        obtain ⟨hpref, hval⟩ := hspec x hx
        by_cases hlt : k < m + gs.length
        · rw [hget_old _ k hlt, evalBDag_append,
              evalBDag_getD_lt _ _ k (by rw [evalBDag_length, hx0len]; exact hlt)]
          rw [evalRef_congr _ (hgetOk k hlt).1 hpref]
          exact hev x hx hkillEv_gs k hlt
        · have heq : k = m + gs.length := by simp at hk; omega
          subst heq
          rw [hget_new, hval, hev x hx hkillEv_gs g.2.1 hga, hev x hx hkillEv_gs g.2.2 hgb]
          have hgate := evalBDag_at_gate hWF0 x0 hx0len gs.length (by simp)
          simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero] at hgate
          rw [hgate, evalBDag_append,
              evalBDag_getD_lt [g] (evalBDag gs x0) g.2.1 (by rw [evalBDag_length, hx0len]; exact hga),
              evalBDag_getD_lt [g] (evalBDag gs x0) g.2.2 (by rw [evalBDag_length, hx0len]; exact hgb)]

def fanout (D : BDag) (w : ℕ) : ℕ :=
  ((Finset.range D.length).filter fun j =>
    if hj : j < D.length then (D[j]).2.1 = w ∨ (D[j]).2.2 = w else false).card

lemma sum_card_filter_comm {α β : Type*} (s : Finset α) (t : Finset β)
    (P : α → β → Prop) [∀ a b, Decidable (P a b)] :
    ∑ a ∈ s, (t.filter fun b => P a b).card = ∑ b ∈ t, (s.filter fun a => P a b).card := by
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

lemma sum_fanout (m : ℕ) (D : BDag) (hWF : WellFormed m D) :
    ∑ w ∈ Finset.range (m + D.length), fanout D w = 2 * D.length := by
  unfold fanout
  rw [sum_card_filter_comm]
  have hterm : ∀ j ∈ Finset.range D.length,
      ((Finset.range (m + D.length)).filter fun w =>
        if hj : j < D.length then (D[j]).2.1 = w ∨ (D[j]).2.2 = w else false).card = 2 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    obtain ⟨ha, hb, hab⟩ := hWF j hj'
    have heq : (Finset.range (m + D.length)).filter (fun w =>
        if hj : j < D.length then (D[j]).2.1 = w ∨ (D[j]).2.2 = w else false) =
        {(D[j]).2.1, (D[j]).2.2} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_range, hj', ↓reduceDIte, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨_, rfl | rfl⟩ <;> simp
      · rintro (rfl | rfl)
        · exact ⟨by omega, Or.inl rfl⟩
        · exact ⟨by omega, Or.inr rfl⟩
    rw [heq, Finset.card_pair hab]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]

lemma sum_fanout_zero_bound (m : ℕ) (D : BDag) (hWF : WellFormed m D)
    (env : List WireRef)
    (hiff : ∀ j (hj : j < D.length),
      env.getD (m + j) .cFalse = .cFalse ↔
        ((D[j]).1 = true ∧ (env.getD (D[j]).2.1 .cFalse = .cFalse ∨ env.getD (D[j]).2.2 .cFalse = .cFalse)) ∨
        ((D[j]).1 = false ∧ env.getD (D[j]).2.1 .cFalse = .cFalse ∧ env.getD (D[j]).2.2 .cFalse = .cFalse)) :
    let K := (Finset.range (m + D.length)).filter fun w => env.getD w .cFalse = .cFalse
    let ZG := (Finset.range D.length).filter fun j => env.getD (m + j) .cFalse = .cFalse
    let Alive := (Finset.range D.length).filter fun j =>
      if hj : j < D.length then
        env.getD (D[j]).2.1 .cFalse ≠ .cFalse ∧ env.getD (D[j]).2.2 .cFalse ≠ .cFalse
      else false
    ∑ w ∈ K, fanout D w ≤ 2 * ZG.card + (D.length - ZG.card - Alive.card) := by
  intro K ZG Alive
  unfold fanout
  have hswap : ∑ w ∈ K, ((Finset.range D.length).filter fun j =>
      if hj : j < D.length then (D[j]).2.1 = w ∨ (D[j]).2.2 = w else false).card =
      ∑ j ∈ Finset.range D.length, (K.filter fun w =>
        if hj : j < D.length then (D[j]).2.1 = w ∨ (D[j]).2.2 = w else false).card :=
    sum_card_filter_comm K (Finset.range D.length) (fun w j =>
      if hj : j < D.length then (D[j]).2.1 = w ∨ (D[j]).2.2 = w else false)
  rw [hswap]
  let cnt := fun j => (K.filter fun w =>
    if hj : j < D.length then (D[j]).2.1 = w ∨ (D[j]).2.2 = w else false).card
  have hle_per : ∀ j ∈ Finset.range D.length,
      cnt j ≤ (if j ∈ ZG then 2 else if j ∈ Alive then 0 else 1) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    obtain ⟨ha, hb, hab⟩ := hWF j hj'
    have hKsub : K.filter (fun w => if hj : j < D.length then (D[j]).2.1 = w ∨ (D[j]).2.2 = w else false) ⊆
        {(D[j]).2.1, (D[j]).2.2} := by
      intro w hw
      rw [Finset.mem_filter] at hw
      simp only [hj', ↓reduceDIte] at hw
      rcases hw.2 with rfl | rfl <;> simp
    split_ifs with hZG hAl
    · exact (Finset.card_le_card hKsub).trans (by rw [Finset.card_pair hab])
    · rw [Finset.mem_filter] at hAl
      simp only [hj', ↓reduceDIte] at hAl
      have hemp : K.filter (fun w => if hj : j < D.length then (D[j]).2.1 = w ∨ (D[j]).2.2 = w else false) = ∅ := by
        ext w; simp only [Finset.mem_filter, hj', ↓reduceDIte, Finset.notMem_empty, iff_false, not_and]
        intro hwK hor
        rw [Finset.mem_filter] at hwK
        rcases hor with rfl | rfl
        · exact hAl.2.1 hwK.2
        · exact hAl.2.2 hwK.2
      simp only [cnt, hemp, Finset.card_empty, le_refl]
    ·
      have hnotZG : env.getD (m + j) .cFalse ≠ .cFalse := fun h => hZG (Finset.mem_filter.mpr ⟨hj, h⟩)
      have hnotBoth : ¬ (env.getD (D[j]).2.1 .cFalse = .cFalse ∧ env.getD (D[j]).2.2 .cFalse = .cFalse) := by
        rintro ⟨h1, h2⟩
        apply hnotZG
        rw [hiff j hj']
        cases hop : (D[j]).1 with
        | false => exact Or.inr ⟨rfl, h1, h2⟩
        | true => exact Or.inl ⟨rfl, Or.inl h1⟩
      by_cases h1 : env.getD (D[j]).2.1 .cFalse = .cFalse
      · have h2 : env.getD (D[j]).2.2 .cFalse ≠ .cFalse := fun h => hnotBoth ⟨h1, h⟩
        have hsub1 : K.filter (fun w => if hj : j < D.length then (D[j]).2.1 = w ∨ (D[j]).2.2 = w else false) ⊆
            {(D[j]).2.1} := by
          intro w hw
          rw [Finset.mem_filter] at hw
          simp only [hj', ↓reduceDIte] at hw
          rw [Finset.mem_filter] at hw
          rcases hw.2 with rfl | rfl
          · simp
          · exact (h2 hw.1.2).elim
        exact (Finset.card_le_card hsub1).trans (by simp)
      · have hsub1 : K.filter (fun w => if hj : j < D.length then (D[j]).2.1 = w ∨ (D[j]).2.2 = w else false) ⊆
            {(D[j]).2.2} := by
          intro w hw
          rw [Finset.mem_filter] at hw
          simp only [hj', ↓reduceDIte] at hw
          rw [Finset.mem_filter] at hw
          rcases hw.2 with rfl | rfl
          · exact (h1 hw.1.2).elim
          · simp
        exact (Finset.card_le_card hsub1).trans (by simp)
  have hsum := Finset.sum_le_sum hle_per
  have hdisj : Disjoint ZG Alive := by
    rw [Finset.disjoint_left]
    intro j hZ hA
    rw [Finset.mem_filter] at hZ hA
    have hj' := Finset.mem_range.mp hZ.1
    simp only [hj', ↓reduceDIte] at hA
    have hcf := (hiff j hj').mp hZ.2
    rcases hcf with ⟨_, h1 | h2⟩ | ⟨_, h1, _⟩
    · exact hA.2.1 h1
    · exact hA.2.2 h2
    · exact hA.2.1 h1
  have hZsub : ZG ⊆ Finset.range D.length := Finset.filter_subset _ _
  have hAsub : Alive ⊆ Finset.range D.length := Finset.filter_subset _ _
  have hsplit : ∑ j ∈ Finset.range D.length, (if j ∈ ZG then 2 else if j ∈ Alive then 0 else 1) =
      2 * ZG.card + (D.length - ZG.card - Alive.card) := by
    have h1 : ∀ j ∈ Finset.range D.length,
        (if j ∈ ZG then 2 else if j ∈ Alive then 0 else 1) + (if j ∈ Alive then 1 else 0) =
        1 + (if j ∈ ZG then 1 else 0) := by
      intro j _
      by_cases hZ : j ∈ ZG
      · have hA : j ∉ Alive := Finset.disjoint_left.mp hdisj hZ
        simp [hZ, hA]
      · by_cases hA : j ∈ Alive <;> simp [hZ, hA]
    have hsum1 := Finset.sum_congr rfl h1
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        smul_eq_mul, mul_one] at hsum1
    have hZsum : ∑ j ∈ Finset.range D.length, (if j ∈ ZG then 1 else 0) = ZG.card := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hZsub]
      simp
    have hAsum : ∑ j ∈ Finset.range D.length, (if j ∈ Alive then 1 else 0) = Alive.card := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hAsub]
      simp
    rw [hZsum, hAsum] at hsum1
    have hUA : ZG.card + Alive.card ≤ D.length := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact (Finset.card_le_card (Finset.union_subset hZsub hAsub)).trans (by simp)
    omega
  exact hsum.trans_eq hsplit

def shiftW (cut w : ℕ) : ℕ := if cut < w then w - 1 else w

def eraseGate (m : ℕ) (D : BDag) (idx : ℕ) : BDag :=
  D.take idx ++ (D.drop (idx + 1)).map fun g => (g.1, shiftW (m + idx) g.2.1, shiftW (m + idx) g.2.2)

lemma eraseGate_spec (m : ℕ) (D : BDag) (hWF : WellFormed m D) (idx : ℕ) (hidx : idx < D.length)
    (hdead : fanout D (m + idx) = 0) :
    let D' := eraseGate m D idx
    WellFormed m D' ∧ D'.length = D.length - 1 ∧
    ∀ (x : List Bool), x.length = m → ∀ w < m + D.length, w ≠ m + idx →
      (evalBDag D' x).getD (shiftW (m + idx) w) false = (evalBDag D x).getD w false := by
  have hnoRead : ∀ j (hj : j < D.length), (D[j]).2.1 ≠ m + idx ∧ (D[j]).2.2 ≠ m + idx := by
    intro j hj
    have h0 : j ∉ (Finset.range D.length).filter (fun j =>
        if hj : j < D.length then (D[j]).2.1 = m + idx ∨ (D[j]).2.2 = m + idx else false) := by
      intro hm
      have := Finset.card_pos.mpr ⟨j, hm⟩
      unfold fanout at hdead; omega
    rw [Finset.mem_filter, Finset.mem_range] at h0
    simp only [hj, ↓reduceDIte, not_and, not_or] at h0
    exact h0 trivial
  set D' := eraseGate m D idx
  have hlenD' : D'.length = D.length - 1 := by
    simp only [D', eraseGate, List.length_append, List.length_take, List.length_map, List.length_drop]
    omega
  have hWFD' : WellFormed m D' := by
    intro j hj
    have hj_len : j < D.length - 1 := hlenD' ▸ hj
    simp only [D', eraseGate]
    have htk : (D.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
    by_cases hlt : j < idx
    · simp only [List.getElem_append_left (by rw [htk]; exact hlt), List.getElem_take]
      exact hWF j (by omega)
    · have hj1 : j + 1 < D.length := by omega
      have hsub : idx + 1 + (j - idx) = j + 1 := by omega
      rw [List.getElem_append_right (by rw [htk]; omega)]
      simp only [htk, List.getElem_map, List.getElem_drop, hsub]
      obtain ⟨ha, hb, hab⟩ := hWF (j + 1) hj1
      obtain ⟨hna, hnb⟩ := hnoRead (j + 1) hj1
      refine ⟨?_, ?_, ?_⟩
      · simp only [shiftW]; split_ifs <;> omega
      · simp only [shiftW]; split_ifs <;> omega
      · intro heq; simp only [shiftW] at heq; split_ifs at heq <;> omega
  refine ⟨hWFD', hlenD', ?_⟩
  intro x hx w hw hne
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hlt : w < m + idx
    · have hsh : shiftW (m + idx) w = w := by simp [shiftW, show ¬ m + idx < w by omega]
      rw [hsh]
      have h1 : D = D.take idx ++ D.drop idx := (List.take_append_drop idx D).symm
      have hlen1 : (evalBDag (D.take idx) x).length = m + idx := by
        rw [evalBDag_length, hx, List.length_take_of_le (Nat.le_of_lt hidx)]
      conv_lhs => simp only [D', eraseGate]
      rw [evalBDag_append, evalBDag_getD_lt _ (evalBDag (D.take idx) x) w (by rw [hlen1]; exact hlt)]
      conv_rhs => rw [h1]
      rw [evalBDag_append, evalBDag_getD_lt (D.drop idx) (evalBDag (D.take idx) x) w (by rw [hlen1]; exact hlt)]
    · have hgt : m + idx < w := by omega
      have hsh : shiftW (m + idx) w = w - 1 := by simp [shiftW, hgt]
      rw [hsh]
      let j := w - 1 - m
      have hjD' : j < D'.length := by omega
      have hj1 : j + 1 < D.length := by omega
      have hw1 : w - 1 = m + j := by omega
      have hw2 : w = m + (j + 1) := by omega
      rw [hw1, evalBDag_at_gate hWFD' x hx j hjD', hw2, evalBDag_at_gate hWF x hx (j + 1) hj1]
      have htk : (D.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
      have hge : idx ≤ j := by omega
      have hsub : idx + 1 + (j - idx) = j + 1 := by omega
      have hget : D'[j] = ((D[j + 1]).1, shiftW (m + idx) (D[j + 1]).2.1, shiftW (m + idx) (D[j + 1]).2.2) := by
        simp only [D', eraseGate]
        rw [List.getElem_append_right (by rw [htk]; exact hge)]
        simp only [htk, List.getElem_map, List.getElem_drop, hsub]
      rw [hget]
      obtain ⟨ha, hb, _⟩ := hWF (j + 1) hj1
      obtain ⟨hna, hnb⟩ := hnoRead (j + 1) hj1
      rw [ih (D[j + 1]).2.1 (by omega) (by omega) hna,
          ih (D[j + 1]).2.2 (by omega) (by omega) hnb]

inductive InCone (m : ℕ) (D : BDag) : ℕ → ℕ → Prop
  | refl (w : ℕ) : InCone m D w w
  | left {u j : ℕ} (hj : j < D.length) : InCone m D u (D[j]).2.1 → InCone m D u (m + j)
  | right {u j : ℕ} (hj : j < D.length) : InCone m D u (D[j]).2.2 → InCone m D u (m + j)

lemma inCone_le {m : ℕ} {D : BDag} (hWF : WellFormed m D) {u w : ℕ} (h : InCone m D u w) : u ≤ w := by
  induction h with
  | refl => exact le_rfl
  | left hj _ ih => have := (hWF _ hj).1; omega
  | right hj _ ih => have := (hWF _ hj).2.1; omega

lemma inCone_trans {m : ℕ} {D : BDag} {u v w : ℕ} (h1 : InCone m D u v) (h2 : InCone m D v w) :
    InCone m D u w := by
  induction h2 with
  | refl => exact h1
  | left hj _ ih => exact InCone.left hj ih
  | right hj _ ih => exact InCone.right hj ih

lemma inCone_lt_of_ne {m : ℕ} {D : BDag} (hWF : WellFormed m D) {u w : ℕ}
    (h : InCone m D u w) (hne : u ≠ w) : u < w :=
  Nat.lt_of_le_of_ne (inCone_le hWF h) hne

lemma inCone_has_reader {m : ℕ} {D : BDag} (hWF : WellFormed m D) {u w : ℕ}
    (h : InCone m D u w) (hne : u ≠ w) :
    ∃ j, ∃ hj : j < D.length, InCone m D (m + j) w ∧ ((D[j]).2.1 = u ∨ (D[j]).2.2 = u) := by
  induction h with
  | refl => exact (hne rfl).elim
  | @left j hj h1 ih =>
    by_cases he : u = (D[j]).2.1
    · exact ⟨j, hj, InCone.refl _, Or.inl he.symm⟩
    · obtain ⟨j', hj', hc, hr⟩ := ih he
      exact ⟨j', hj', InCone.left hj hc, hr⟩
  | @right j hj h1 ih =>
    by_cases he : u = (D[j]).2.2
    · exact ⟨j, hj, InCone.refl _, Or.inr he.symm⟩
    · obtain ⟨j', hj', hc, hr⟩ := ih he
      exact ⟨j', hj', InCone.right hj hc, hr⟩

def ReadOnce (m : ℕ) (D : BDag) (g : ℕ) : Prop :=
  ∀ u, InCone m D u g → u ≠ g → fanout D u = 1

lemma readOnce_sub {m : ℕ} {D : BDag} (hWF : WellFormed m D) {g w : ℕ}
    (hRO : ReadOnce m D g) (hw : InCone m D w g) : ReadOnce m D w := by
  intro u hu hne
  have hlt : u < w := inCone_lt_of_ne hWF hu hne
  have hle : w ≤ g := inCone_le hWF hw
  exact hRO u (inCone_trans hu hw) (by omega)

lemma readOnce_reader_inCone {m : ℕ} {D : BDag} (hWF : WellFormed m D) {g : ℕ}
    (hRO : ReadOnce m D g) {u : ℕ} (hu : InCone m D u g) (hne : u ≠ g)
    {j : ℕ} (hj : j < D.length) (hread : (D[j]).2.1 = u ∨ (D[j]).2.2 = u) :
    InCone m D (m + j) g := by
  obtain ⟨j0, hj0, hc0, hr0⟩ := inCone_has_reader hWF hu hne
  have hfan : fanout D u = 1 := hRO u hu hne
  let S := (Finset.range D.length).filter fun k =>
    if hk : k < D.length then (D[k]).2.1 = u ∨ (D[k]).2.2 = u else false
  have hm1 : j ∈ S := by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hj, by simp [hj, hread]⟩
  have hm0 : j0 ∈ S := by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hj0, by simp [hj0, hr0]⟩
  have heq : j = j0 := Finset.card_le_one.mp (le_of_eq hfan) j hm1 j0 hm0
  exact heq ▸ hc0

lemma readOnce_operands_disjoint {m : ℕ} {D : BDag} (hWF : WellFormed m D) {g j : ℕ}
    (hRO : ReadOnce m D g) (hj : j < D.length) (hcg : InCone m D (m + j) g) :
    ∀ u, ¬ (InCone m D u (D[j]).2.1 ∧ InCone m D u (D[j]).2.2) := by
  intro u ⟨h1, h2⟩
  obtain ⟨ha, hb, hab⟩ := hWF j hj

  suffices h : ∀ k u, k = m + j - u → InCone m D u (D[j]).2.1 → InCone m D u (D[j]).2.2 → False by
    exact h (m + j - u) u rfl h1 h2
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro u hk hu1 hu2
    have hle1 : u ≤ (D[j]).2.1 := inCone_le hWF hu1
    have hle2 : u ≤ (D[j]).2.2 := inCone_le hWF hu2
    have hneG : u ≠ m + j := by omega
    have hcu : InCone m D u g := inCone_trans (InCone.left hj hu1) hcg
    have hROj : ReadOnce m D (m + j) := readOnce_sub hWF hRO hcg
    have hfan : fanout D u = 1 := hROj u (InCone.left hj hu1) hneG
    let S := (Finset.range D.length).filter fun t =>
      if ht : t < D.length then (D[t]).2.1 = u ∨ (D[t]).2.2 = u else false
    by_cases he1 : u = (D[j]).2.1
    · have he2 : u ≠ (D[j]).2.2 := he1 ▸ hab
      obtain ⟨j2, hj2, hc2, hr2⟩ := inCone_has_reader hWF hu2 he2
      have hm1 : j ∈ S := by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hj, by simp [hj, he1]⟩
      have hm2 : j2 ∈ S := by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hj2, by simp [hj2, hr2]⟩
      have heq : j2 = j := Finset.card_le_one.mp (le_of_eq hfan) j2 hm2 j hm1
      rw [heq] at hc2
      have := inCone_le hWF hc2
      omega
    · by_cases he2 : u = (D[j]).2.2
      · obtain ⟨j1, hj1, hc1, hr1⟩ := inCone_has_reader hWF hu1 he1
        have hm1 : j ∈ S := by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hj, by simp [hj, he2]⟩
        have hm2 : j1 ∈ S := by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hj1, by simp [hj1, hr1]⟩
        have heq : j1 = j := Finset.card_le_one.mp (le_of_eq hfan) j1 hm2 j hm1
        rw [heq] at hc1
        have := inCone_le hWF hc1
        omega
      · obtain ⟨j1, hj1, hc1, hr1⟩ := inCone_has_reader hWF hu1 he1
        obtain ⟨j2, hj2, hc2, hr2⟩ := inCone_has_reader hWF hu2 he2
        have hm1 : j1 ∈ S := by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hj1, by simp [hj1, hr1]⟩
        have hm2 : j2 ∈ S := by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hj2, by simp [hj2, hr2]⟩
        have heq : j1 = j2 := Finset.card_le_one.mp (le_of_eq hfan) j1 hm1 j2 hm2
        have hu_lt : u < m + j1 := by
          obtain ⟨h1a, h1b, _⟩ := hWF j1 hj1
          rcases hr1 with h | h <;> omega
        exact ih (m + j - (m + j1)) (by omega) (m + j1) rfl hc1 (heq ▸ hc2)

lemma eval_agree_outside_readOnce {m : ℕ} {D : BDag} (hWF : WellFormed m D) {g : ℕ}
    (hRO : ReadOnce m D g) (x y : List Bool) (hx : x.length = m) (hy : y.length = m)
    (hin : ∀ i < m, ¬ (InCone m D i g ∧ i ≠ g) → x.getD i false = y.getD i false)
    (hg : (evalBDag D x).getD g false = (evalBDag D y).getD g false) :
    ∀ w < m + D.length, ¬ (InCone m D w g ∧ w ≠ g) →
      (evalBDag D x).getD w false = (evalBDag D y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hout
    by_cases hwg : w = g
    · exact hwg ▸ hg
    · by_cases hwm : w < m
      · rw [evalBDag_getD_lt D x w (hx ▸ hwm), evalBDag_getD_lt D y w (hy ▸ hwm)]
        exact hin w hwm hout
      · let j := w - m
        have hj : j < D.length := by omega
        have hwj : w = m + j := by omega
        rw [hwj, evalBDag_at_gate hWF x hx j hj, evalBDag_at_gate hWF y hy j hj]
        obtain ⟨ha, hb, _⟩ := hWF j hj
        have ha_out : ¬ (InCone m D (D[j]).2.1 g ∧ (D[j]).2.1 ≠ g) := by
          rintro ⟨hc, hne⟩
          have hmg := readOnce_reader_inCone hWF hRO hc hne hj (Or.inl rfl)
          exact hout ⟨hwj ▸ hmg, hwg⟩
        have hb_out : ¬ (InCone m D (D[j]).2.2 g ∧ (D[j]).2.2 ≠ g) := by
          rintro ⟨hc, hne⟩
          have hmg := readOnce_reader_inCone hWF hRO hc hne hj (Or.inr rfl)
          exact hout ⟨hwj ▸ hmg, hwg⟩
        rw [ih (D[j]).2.1 (by omega) (by omega) ha_out,
            ih (D[j]).2.2 (by omega) (by omega) hb_out]

lemma eval_or_cone {m : ℕ} {D : BDag} (hWF : WellFormed m D) {w : ℕ} (hw : w < m + D.length)
    (hnoAnd : ∀ j (hj : j < D.length), InCone m D (m + j) w → (D[j]).1 = false)
    (x : List Bool) (hx : x.length = m) :
    (evalBDag D x).getD w false = true ↔ ∃ i < m, InCone m D i w ∧ x.getD i false = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwm : w < m
    · rw [evalBDag_getD_lt D x w (hx ▸ hwm)]
      constructor
      · intro h; exact ⟨w, hwm, InCone.refl w, h⟩
      · rintro ⟨i, him, hic, hxi⟩
        have hle : i ≤ w := inCone_le hWF hic
        cases hic with
        | refl => exact hxi
        | left hj _ => omega
        | right hj _ => omega
    · let j := w - m
      have hj : j < D.length := by omega
      have hwj : w = m + j := by omega
      have hop : (D[j]).1 = false := hnoAnd j hj (hwj ▸ InCone.refl w)
      rw [hwj, evalBDag_at_gate hWF x hx j hj, hop]
      simp only [evalOp, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true]
      obtain ⟨ha, hb, _⟩ := hWF j hj
      have iha := ih (D[j]).2.1 (by omega) (by omega)
        (fun j' hj' hc => hnoAnd j' hj' (hwj ▸ InCone.left hj hc))
      have ihb := ih (D[j]).2.2 (by omega) (by omega)
        (fun j' hj' hc => hnoAnd j' hj' (hwj ▸ InCone.right hj hc))
      rw [iha, ihb]
      constructor
      · rintro (⟨i, hi, hc, hx⟩ | ⟨i, hi, hc, hx⟩)
        · exact ⟨i, hi, hwj ▸ InCone.left hj hc, hx⟩
        · exact ⟨i, hi, hwj ▸ InCone.right hj hc, hx⟩
      · rintro ⟨i, hi, hc, hx⟩
        generalize hweq : m + j = w0 at hc
        cases hc with
        | refl => omega
        | @left j' hj' hc' =>
          have heq : j' = j := by omega
          subst heq; exact Or.inl ⟨i, hi, hc', hx⟩
        | @right j' hj' hc' =>
          have heq : j' = j := by omega
          subst heq; exact Or.inr ⟨i, hi, hc', hx⟩

lemma exists_leaf_inCone {m : ℕ} {D : BDag} (hWF : WellFormed m D) {w : ℕ} (hw : w < m + D.length) :
    ∃ i < m, InCone m D i w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwm : w < m
    · exact ⟨w, hwm, InCone.refl w⟩
    · let j := w - m
      have hj : j < D.length := by omega
      have hwj : w = m + j := by omega
      obtain ⟨ha, _, _⟩ := hWF j hj
      obtain ⟨i, hi, hc⟩ := ih (D[j]).2.1 (by omega) (by omega)
      exact ⟨i, hi, hwj ▸ InCone.left hj hc⟩

end BDag

section MainProof

open Classical

variable {n : ℕ}

def cycA (n : ℕ) (u v : Fin n) : Bool :=
  decide (v.val = u.val ∨ v.val = (u.val + 1) % n)

def ReprSub (n : ℕ) (S : Finset (Fin (2 * n))) (D : BDag) (out : ℕ) : Prop :=
  WellFormed (2 * n) D ∧ out < 2 * n + D.length ∧
  ∀ u v : Fin n,
    (evalBDag D (oneEach u v)).getD out false =
      (decide (leftV u ∈ S ∧ rightV v ∈ S) && cycA n u v)

lemma oneEach_length (u v : Fin n) : (oneEach u v).length = 2 * n := by
  simp [oneEach]; omega

lemma oneEach_getD (u v : Fin n) (i : ℕ) (hi : i < 2 * n) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  unfold oneEach
  by_cases h : i < n
  · rw [List.getD_append _ _ _ _ (by simp [h]), List.getD_eq_getElem _ _ (by simp [h]),
        List.getElem_ofFn]
    have hne : i ≠ n + v.val := by omega
    simp only [hne, or_false, Fin.ext_iff]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_ofFn]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
    have hne : i ≠ u.val := by omega
    simp only [hne, false_or, Fin.ext_iff]
    apply decide_eq_decide.mpr; omega

lemma oneEach_getD_toWire (u v : Fin n) (a : Fin (2 * n)) :
    (oneEach u v).getD (toWire a) false = decide (a = leftV u ∨ a = rightV v) := by
  rw [oneEach_getD u v (toWire a) (toWire_lt a)]
  apply decide_eq_decide.mpr
  constructor
  · rintro (h | h)
    · left; exact toWire_inj (h.trans (toWire_leftV u).symm)
    · right; exact toWire_inj (h.trans (toWire_rightV v).symm)
  · rintro (rfl | rfl)
    · left; exact toWire_leftV u
    · right; exact toWire_rightV v

lemma cycA_eq_cycAdj (hn : 3 ≤ n) (u v : Fin n) :
    cycA n u v = true ↔ cycAdj hn (leftV u) (rightV v) := by
  rw [cycAdj_left_right hn u v]
  simp [cycA]

lemma reprSub_eval_zero_left (hn : 3 ≤ n) {S : Finset (Fin (2 * n))} {D : BDag} {out : ℕ}
    (hR : ReprSub n S D out) (v : Fin n) :
    (evalBDag D (List.ofFn fun i : Fin (2 * n) => decide (i.val = n + v.val))).getD out false = false := by
  obtain ⟨u0, hu0⟩ := exists_non_adj_left hn v
  have hle : ∀ i, (List.ofFn fun j : Fin (2 * n) => decide (j.val = n + v.val)).getD i false = true →
      (oneEach u0 v).getD i false = true := by
    intro i hi
    by_cases hlt : i < 2 * n
    · rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn] at hi
      rw [oneEach_getD u0 v i hlt, decide_eq_true_iff]
      exact Or.inr (of_decide_eq_true hi)
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; exact Bool.noConfusion hi
  have hm := evalBDag_mono D _ _ (by simp [oneEach_length]) hle out
  have hf : (evalBDag D (oneEach u0 v)).getD out false = false := by
    rw [hR.2.2 u0 v]
    have : cycA n u0 v = false := by
      cases h : cycA n u0 v
      · rfl
      · exact (hu0 ((cycA_eq_cycAdj hn u0 v).mp h)).elim
    simp [this]
  cases h : (evalBDag D (List.ofFn fun i : Fin (2 * n) => decide (i.val = n + v.val))).getD out false
  · rfl
  · exact (Bool.false_ne_true (hf.symm.trans (hm h))).elim

lemma reprSub_eval_zero_right (hn : 3 ≤ n) {S : Finset (Fin (2 * n))} {D : BDag} {out : ℕ}
    (hR : ReprSub n S D out) (u : Fin n) :
    (evalBDag D (List.ofFn fun i : Fin (2 * n) => decide (i.val = u.val))).getD out false = false := by
  obtain ⟨v0, hv0⟩ := exists_non_adj_right hn u
  have hle : ∀ i, (List.ofFn fun j : Fin (2 * n) => decide (j.val = u.val)).getD i false = true →
      (oneEach u v0).getD i false = true := by
    intro i hi
    by_cases hlt : i < 2 * n
    · rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn] at hi
      rw [oneEach_getD u v0 i hlt, decide_eq_true_iff]
      exact Or.inl (of_decide_eq_true hi)
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; exact Bool.noConfusion hi
  have hm := evalBDag_mono D _ _ (by simp [oneEach_length]) hle out
  have hf : (evalBDag D (oneEach u v0)).getD out false = false := by
    rw [hR.2.2 u v0]
    have : cycA n u v0 = false := by
      cases h : cycA n u v0
      · rfl
      · exact (hv0 ((cycA_eq_cycAdj hn u v0).mp h)).elim
    simp [this]
  cases h : (evalBDag D (List.ofFn fun i : Fin (2 * n) => decide (i.val = u.val))).getD out false
  · rfl
  · exact (Bool.false_ne_true (hf.symm.trans (hm h))).elim

lemma reprSub_has_true_and_false (hn : 3 ≤ n) {S : Finset (Fin (2 * n))}
    (hS : NoShortRun hn S) (hne : S.Nonempty) :
    (∃ u v : Fin n, (decide (leftV u ∈ S ∧ rightV v ∈ S) && cycA n u v) = true) ∧
    (∃ u v : Fin n, (decide (leftV u ∈ S ∧ rightV v ∈ S) && cycA n u v) = false) := by
  constructor
  · obtain ⟨a, ha⟩ := hne
    obtain ⟨b, hb, hab⟩ := noShortRun_deg_pos hn hS ha
    have hpar := cycAdj_parity hn hab
    by_cases hp : a.val % 2 = 1
    · let u : Fin n := ⟨a.val / 2, by omega⟩
      let v : Fin n := ⟨b.val / 2, by omega⟩
      have hae : a = leftV u := Fin.ext (by simp [leftV, u]; omega)
      have hbe : b = rightV v := Fin.ext (by simp [rightV, v]; omega)
      refine ⟨u, v, ?_⟩
      rw [Bool.and_eq_true, decide_eq_true_iff, cycA_eq_cycAdj hn]
      exact ⟨⟨hae ▸ ha, hbe ▸ hb⟩, hae ▸ hbe ▸ hab⟩
    · let v : Fin n := ⟨a.val / 2, by omega⟩
      let u : Fin n := ⟨b.val / 2, by omega⟩
      have hae : a = rightV v := Fin.ext (by simp [rightV, v]; omega)
      have hbe : b = leftV u := Fin.ext (by simp [leftV, u]; omega)
      refine ⟨u, v, ?_⟩
      rw [Bool.and_eq_true, decide_eq_true_iff, cycA_eq_cycAdj hn]
      exact ⟨⟨hbe ▸ hb, hae ▸ ha⟩, hae ▸ hbe ▸ (cycAdj_symm hn hab)⟩
  · obtain ⟨v0, hv0⟩ := exists_non_adj_right hn ⟨0, by omega⟩
    refine ⟨⟨0, by omega⟩, v0, ?_⟩
    have : cycA n ⟨0, by omega⟩ v0 = false := by
      cases h : cycA n ⟨0, by omega⟩ v0
      · rfl
      · exact (hv0 ((cycA_eq_cycAdj hn _ _).mp h)).elim
    simp [this]

lemma reprSub_out_ge (hn : 3 ≤ n) {S : Finset (Fin (2 * n))}
    (hS : NoShortRun hn S) (hne : S.Nonempty) {D : BDag} {out : ℕ} (hR : ReprSub n S D out) :
    2 * n ≤ out := by
  by_contra hlt
  push_neg at hlt
  by_cases h1 : out < n
  · let u : Fin n := ⟨out, h1⟩
    obtain ⟨v0, hv0⟩ := exists_non_adj_right hn u
    have h := hR.2.2 u v0
    rw [evalBDag_getD_lt D (oneEach u v0) out (by rw [oneEach_length]; omega),
        oneEach_getD u v0 out hlt] at h
    have ht : decide (out = u.val ∨ out = n + v0.val) = true := by simp [u]
    have hf : cycA n u v0 = false := by
      cases hc : cycA n u v0
      · rfl
      · exact (hv0 ((cycA_eq_cycAdj hn u v0).mp hc)).elim
    rw [ht, hf, Bool.and_false] at h
    exact Bool.noConfusion h
  · let v : Fin n := ⟨out - n, by omega⟩
    obtain ⟨u0, hu0⟩ := exists_non_adj_left hn v
    have h := hR.2.2 u0 v
    rw [evalBDag_getD_lt D (oneEach u0 v) out (by rw [oneEach_length]; omega),
        oneEach_getD u0 v out hlt] at h
    have ht : decide (out = u0.val ∨ out = n + v.val) = true := by
      rw [decide_eq_true_iff]; right; simp [v]; omega
    have hf : cycA n u0 v = false := by
      cases hc : cycA n u0 v
      · rfl
      · exact (hu0 ((cycA_eq_cycAdj hn u0 v).mp hc)).elim
    rw [ht, hf, Bool.and_false] at h
    exact Bool.noConfusion h

def IsMinBDag (n : ℕ) (S : Finset (Fin (2 * n))) (D : BDag) (out : ℕ) : Prop :=
  ReprSub n S D out ∧ ∀ D' out', ReprSub n S D' out' → D.length ≤ D'.length

lemma minBDag_out_last (hn : 3 ≤ n) {S : Finset (Fin (2 * n))} (hS : NoShortRun hn S)
    (hne : S.Nonempty) {D : BDag} {out : ℕ} (hM : IsMinBDag n S D out) :
    out + 1 = 2 * n + D.length ∧ fanout D out = 0 := by
  have hge := reprSub_out_ge hn hS hne hM.1
  have hlt := hM.1.2.1
  have hlast : out + 1 = 2 * n + D.length := by
    by_contra hne_last
    let k := out - 2 * n + 1
    have hklt : k < D.length := by omega
    let D' := D.take k
    have hWF' : WellFormed (2 * n) D' := fun j hj => by
      have hj' : j < D.length := by simp only [D', List.length_take] at hj; omega
      simpa [D', List.getElem_take] using hM.1.1 j hj'
    have hR' : ReprSub n S D' out := by
      refine ⟨hWF', by simp only [D', List.length_take]; omega, fun u v => ?_⟩
      have h1 : D = D' ++ D.drop k := (List.take_append_drop k D).symm
      have hlen : (evalBDag D' (oneEach u v)).length = 2 * n + k := by
        rw [evalBDag_length, oneEach_length, List.length_take_of_le (Nat.le_of_lt hklt)]
      have heq := hM.1.2.2 u v
      conv_lhs at heq => rw [h1]
      rw [evalBDag_append, evalBDag_getD_lt _ _ out (by rw [hlen]; omega)] at heq
      exact heq
    have hmin := hM.2 D' out hR'
    simp only [D', List.length_take] at hmin
    omega
  refine ⟨hlast, ?_⟩
  unfold fanout
  have hemp : (Finset.range D.length).filter (fun j =>
      if hj : j < D.length then (D[j]).2.1 = out ∨ (D[j]).2.2 = out else false) = ∅ := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
    intro hj
    simp only [hj, ↓reduceDIte, not_or]
    obtain ⟨ha, hb, _⟩ := hM.1.1 j hj
    exact ⟨by omega, by omega⟩
  rw [hemp, Finset.card_empty]

lemma minBDag_live_gates (hn : 3 ≤ n) {S : Finset (Fin (2 * n))} (hS : NoShortRun hn S)
    (hne : S.Nonempty) {D : BDag} {out : ℕ} (hM : IsMinBDag n S D out)
    (j : ℕ) (hj : j < D.length) (hne_out : 2 * n + j ≠ out) :
    1 ≤ fanout D (2 * n + j) := by
  by_contra h0
  have hdead : fanout D (2 * n + j) = 0 := by omega
  obtain ⟨hWF', hlen', hev'⟩ := eraseGate_spec (2 * n) D hM.1.1 j hj hdead
  have hR' : ReprSub n S (eraseGate (2 * n) D j) (shiftW (2 * n + j) out) := by
    refine ⟨hWF', ?_, fun u v => ?_⟩
    · have := hM.1.2.1; rw [hlen']; simp only [shiftW]; split_ifs <;> omega
    · rw [hev' (oneEach u v) (oneEach_length u v) out hM.1.2.1 hne_out.symm]
      exact hM.1.2.2 u v
  have hmin := hM.2 _ _ hR'
  omega

lemma minBDag_no_const_false_gate (hn : 3 ≤ n) {S : Finset (Fin (2 * n))} (hS : NoShortRun hn S)
    (hne : S.Nonempty) {D : BDag} {out : ℕ} (hM : IsMinBDag n S D out)
    (j : ℕ) (hj : j < D.length) :
    ∃ u v : Fin n, (evalBDag D (oneEach u v)).getD (2 * n + j) false = true := by
  by_contra hno
  push_neg at hno
  have hall : ∀ u v : Fin n, (evalBDag D (oneEach u v)).getD (2 * n + j) false = false :=
    fun u v => Bool.eq_false_iff.mpr (hno u v)
  let killG : ℕ → Bool := fun k => decide (k = j)
  obtain ⟨hWF', helen, hok, _, _, hcnt, hev⟩ :=
    zeroFold_spec (2 * n) (fun _ => false) killG D hM.1.1
  set res := zeroFold (2 * n) (fun _ => false) killG D
  have hlen_lt : res.1.length < D.length := by
    have hnot : j ∉ (Finset.range D.length |>.filter fun k =>
        if hk : k < D.length then
          killG k = false ∧
          res.2.getD (D[k]).2.1 .cFalse ≠ .cFalse ∧
          res.2.getD (D[k]).2.2 .cFalse ≠ .cFalse
        else false) := by
      simp [killG]
    have hsub : (Finset.range D.length |>.filter fun k =>
        if hk : k < D.length then
          killG k = false ∧
          res.2.getD (D[k]).2.1 .cFalse ≠ .cFalse ∧
          res.2.getD (D[k]).2.2 .cFalse ≠ .cFalse
        else false) ⊆ (Finset.range D.length).erase j := by
      intro k hk
      exact Finset.mem_erase.mpr ⟨fun heq => hnot (heq ▸ hk), (Finset.mem_filter.mp hk).1⟩
    have hc := (Finset.card_le_card hsub).trans_eq (Finset.card_erase_of_mem (Finset.mem_range.mpr hj))
    simp only [Finset.card_range] at hc
    omega
  have hev_out : ∀ u v : Fin n,
      evalRef (evalBDag res.1 (oneEach u v)) (res.2.getD out .cFalse) =
        (decide (leftV u ∈ S ∧ rightV v ∈ S) && cycA n u v) := by
    intro u v
    have hid : (List.ofFn fun i : Fin (2 * n) => if false then false else (oneEach u v).getD i.val false) =
        oneEach u v := by
      apply List.ext_getElem (by simp [oneEach_length])
      intro i h1 h2
      simp only [Bool.false_eq_true, ite_false, List.getElem_ofFn, List.getD_eq_getElem _ _ h2]
    have h1 := hev (oneEach u v) (oneEach_length u v) (by
      intro k hk hkk
      have heq : k = j := of_decide_eq_true hkk
      subst heq; rw [hid]; exact hall u v) out hM.1.2.1
    rw [hid, hM.1.2.2 u v] at h1
    exact h1
  have hrout_ok : refOk (2 * n + res.1.length) (res.2.getD out .cFalse) ∧
      res.2.getD out .cFalse ≠ .cTrue := by
    rw [List.getD_eq_getElem _ _ (by rw [helen]; exact hM.1.2.1)]
    exact hok _ (List.getElem_mem _)
  cases hro : res.2.getD out .cFalse with
  | cFalse =>
    obtain ⟨u, v, huv⟩ := (reprSub_has_true_and_false hn hS hne).1
    have := hev_out u v
    rw [hro, huv] at this
    exact Bool.noConfusion this
  | cTrue => exact (hrout_ok.2 hro).elim
  | wire out' =>
    rw [hro] at hrout_ok hev_out
    have hR' : ReprSub n S res.1 out' := ⟨hWF', hrout_ok.1, fun u v => hev_out u v⟩
    have hmin := hM.2 res.1 out' hR'
    omega

lemma minBDag_active_input_fanout (hn : 3 ≤ n) {S : Finset (Fin (2 * n))} (hS : NoShortRun hn S)
    (hne : S.Nonempty) {D : BDag} {out : ℕ} (hM : IsMinBDag n S D out)
    {a : Fin (2 * n)} (ha : a ∈ S) :
    1 ≤ fanout D (toWire a) := by
  by_contra h0
  have hfan0 : fanout D (toWire a) = 0 := by omega
  have hnoRead : ∀ j (hj : j < D.length), (D[j]).2.1 ≠ toWire a ∧ (D[j]).2.2 ≠ toWire a := by
    intro j hj
    have hm : j ∉ (Finset.range D.length).filter (fun k =>
        if hk : k < D.length then (D[k]).2.1 = toWire a ∨ (D[k]).2.2 = toWire a else false) := by
      intro h; have := Finset.card_pos.mpr ⟨j, h⟩; unfold fanout at hfan0; omega
    rw [Finset.mem_filter, Finset.mem_range] at hm
    simp only [hj, ↓reduceDIte, not_and, not_or] at hm
    exact hm trivial

  have hagree : ∀ (x y : List Bool), x.length = 2 * n → y.length = 2 * n →
      (∀ i < 2 * n, i ≠ toWire a → x.getD i false = y.getD i false) →
      ∀ w < 2 * n + D.length, w ≠ toWire a → (evalBDag D x).getD w false = (evalBDag D y).getD w false := by
    intro x y hx hy hxy w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hne_a
      by_cases hwm : w < 2 * n
      · rw [evalBDag_getD_lt D x w (hx ▸ hwm), evalBDag_getD_lt D y w (hy ▸ hwm)]
        exact hxy w hwm hne_a
      · let j := w - 2 * n
        have hj : j < D.length := by omega
        have hwj : w = 2 * n + j := by omega
        rw [hwj, evalBDag_at_gate hM.1.1 x hx j hj, evalBDag_at_gate hM.1.1 y hy j hj]
        obtain ⟨h1, h2, _⟩ := hM.1.1 j hj
        obtain ⟨hn1, hn2⟩ := hnoRead j hj
        rw [ih (D[j]).2.1 (by omega) (by omega) hn1, ih (D[j]).2.2 (by omega) (by omega) hn2]
  have hout_ne : out ≠ toWire a := by
    have := reprSub_out_ge hn hS hne hM.1
    have := toWire_lt a
    omega
  obtain ⟨b, hb, hab⟩ := noShortRun_deg_pos hn hS ha
  have hpar := cycAdj_parity hn hab
  by_cases hp : a.val % 2 = 1
  · let u : Fin n := ⟨a.val / 2, by omega⟩
    let v : Fin n := ⟨b.val / 2, by omega⟩
    have hae : a = leftV u := Fin.ext (by simp [leftV, u]; omega)
    have hbe : b = rightV v := Fin.ext (by simp [rightV, v]; omega)
    have htrue : (evalBDag D (oneEach u v)).getD out false = true := by
      rw [hM.1.2.2 u v, Bool.and_eq_true, decide_eq_true_iff, cycA_eq_cycAdj hn]
      exact ⟨⟨hae ▸ ha, hbe ▸ hb⟩, hae ▸ hbe ▸ hab⟩
    let y : List Bool := List.ofFn fun i : Fin (2 * n) => decide (i.val = n + v.val)
    have heq := hagree (oneEach u v) y (oneEach_length u v) (by simp [y]) (by
      intro i hi hne_a
      rw [oneEach_getD u v i hi]
      rw [List.getD_eq_getElem _ _ (by simp [y, hi]), List.getElem_ofFn]
      have hne_u : i ≠ u.val := by rw [hae, toWire_leftV] at hne_a; exact hne_a
      simp [hne_u]) out hM.1.2.1 hout_ne
    have hfalse := reprSub_eval_zero_left hn hM.1 v
    rw [htrue, hfalse] at heq
    exact Bool.noConfusion heq
  · let v : Fin n := ⟨a.val / 2, by omega⟩
    let u : Fin n := ⟨b.val / 2, by omega⟩
    have hae : a = rightV v := Fin.ext (by simp [rightV, v]; omega)
    have hbe : b = leftV u := Fin.ext (by simp [leftV, u]; omega)
    have htrue : (evalBDag D (oneEach u v)).getD out false = true := by
      rw [hM.1.2.2 u v, Bool.and_eq_true, decide_eq_true_iff, cycA_eq_cycAdj hn]
      exact ⟨⟨hbe ▸ hb, hae ▸ ha⟩, hae ▸ hbe ▸ (cycAdj_symm hn hab)⟩
    let y : List Bool := List.ofFn fun i : Fin (2 * n) => decide (i.val = u.val)
    have heq := hagree (oneEach u v) y (oneEach_length u v) (by simp [y]) (by
      intro i hi hne_a
      rw [oneEach_getD u v i hi]
      rw [List.getD_eq_getElem _ _ (by simp [y, hi]), List.getElem_ofFn]
      have hne_v : i ≠ n + v.val := by rw [hae, toWire_rightV] at hne_a; exact hne_a
      simp [hne_v]) out hM.1.2.1 hout_ne
    have hfalse := reprSub_eval_zero_right hn hM.1 u
    rw [htrue, hfalse] at heq
    exact Bool.noConfusion heq

lemma minBDag_inactive_input_fanout (hn : 3 ≤ n) {S : Finset (Fin (2 * n))} (hS : NoShortRun hn S)
    (hne : S.Nonempty) {D : BDag} {out : ℕ} (hM : IsMinBDag n S D out)
    {a : Fin (2 * n)} (ha : a ∉ S) :
    fanout D (toWire a) = 0 := by
  by_contra hne0
  have hpos : 0 < fanout D (toWire a) := by omega
  obtain ⟨j0, hj0⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter, Finset.mem_range] at hj0
  have hj0lt : j0 < D.length := hj0.1
  simp only [hj0lt, ↓reduceDIte] at hj0
  let killIn : ℕ → Bool := fun i => decide (i = toWire a)
  obtain ⟨hWF', helen, hok, hin, _, hcnt, hev⟩ :=
    zeroFold_spec (2 * n) killIn (fun _ => false) D hM.1.1
  set res := zeroFold (2 * n) killIn (fun _ => false) D
  have hlen_lt : res.1.length < D.length := by
    have hcf : res.2.getD (toWire a) .cFalse = .cFalse := by
      rw [hin (toWire a) (toWire_lt a)]; simp [killIn]
    have hnot : j0 ∉ (Finset.range D.length |>.filter fun k =>
        if hk : k < D.length then
          false = false ∧
          res.2.getD (D[k]).2.1 .cFalse ≠ .cFalse ∧
          res.2.getD (D[k]).2.2 .cFalse ≠ .cFalse
        else false) := by
      rw [Finset.mem_filter]
      simp only [hj0lt, ↓reduceDIte, not_and]
      intro _ _ h1 h2
      rcases hj0.2 with h | h
      · exact h1 (h ▸ hcf)
      · exact h2 (h ▸ hcf)
    have hsub : (Finset.range D.length |>.filter fun k =>
        if hk : k < D.length then
          false = false ∧
          res.2.getD (D[k]).2.1 .cFalse ≠ .cFalse ∧
          res.2.getD (D[k]).2.2 .cFalse ≠ .cFalse
        else false) ⊆ (Finset.range D.length).erase j0 := by
      intro k hk
      exact Finset.mem_erase.mpr ⟨fun heq => hnot (heq ▸ hk), (Finset.mem_filter.mp hk).1⟩
    have hc := (Finset.card_le_card hsub).trans_eq (Finset.card_erase_of_mem (Finset.mem_range.mpr hj0lt))
    rw [Finset.card_range] at hc
    have hle1 : res.1.length ≤ D.length - 1 := hcnt.trans hc
    omega
  have hev_out : ∀ u v : Fin n,
      evalRef (evalBDag res.1 (oneEach u v)) (res.2.getD out .cFalse) =
        (decide (leftV u ∈ S ∧ rightV v ∈ S) && cycA n u v) := by
    intro u v
    have h1 := hev (oneEach u v) (oneEach_length u v) (fun _ _ h => Bool.noConfusion h) out hM.1.2.1
    rw [h1]
    set x0 := List.ofFn fun i : Fin (2 * n) => if killIn i.val then false else (oneEach u v).getD i.val false
    by_cases hmem : leftV u ∈ S ∧ rightV v ∈ S
    · have hsame : x0 = oneEach u v := by
        apply List.ext_getElem (by simp [x0, oneEach_length])
        intro i hi1 hi2
        simp only [x0, List.getElem_ofFn, killIn]
        have hi : i < 2 * n := by rw [oneEach_length] at hi2; exact hi2
        split_ifs with hia
        · have hia' : i = toWire a := of_decide_eq_true hia
          rw [← List.getD_eq_getElem _ false hi2, hia', oneEach_getD_toWire]
          have h1 : a ≠ leftV u := fun h => ha (h ▸ hmem.1)
          have h2 : a ≠ rightV v := fun h => ha (h ▸ hmem.2)
          simp [h1, h2]
        · exact List.getD_eq_getElem (oneEach u v) false hi2
      rw [hsame, hM.1.2.2 u v]
    · have hle : ∀ i, x0.getD i false = true → (oneEach u v).getD i false = true := by
        intro i hi
        by_cases hlt : i < 2 * n
        · rw [List.getD_eq_getElem _ _ (by simp [x0, hlt])] at hi
          simp only [x0, List.getElem_ofFn] at hi
          by_cases hki : killIn i = true
          · simp [hki] at hi
          · simpa [hki] using hi
        · rw [List.getD_eq_default _ _ (by simp [x0]; omega)] at hi; exact Bool.noConfusion hi
      have hm := evalBDag_mono D x0 (oneEach u v) (by simp [x0, oneEach_length]) hle out
      have hf : (evalBDag D (oneEach u v)).getD out false = false := by
        rw [hM.1.2.2 u v]; simp [hmem]
      have hresf : (decide (leftV u ∈ S ∧ rightV v ∈ S) && cycA n u v) = false := by simp [hmem]
      rw [hresf]
      cases hval : (evalBDag D x0).getD out false
      · rfl
      · exact (Bool.false_ne_true (hf.symm.trans (hm hval))).elim
  have hrout_ok : refOk (2 * n + res.1.length) (res.2.getD out .cFalse) ∧
      res.2.getD out .cFalse ≠ .cTrue := by
    rw [List.getD_eq_getElem _ _ (by rw [helen]; exact hM.1.2.1)]
    exact hok _ (List.getElem_mem _)
  cases hro : res.2.getD out .cFalse with
  | cFalse =>
    obtain ⟨u, v, huv⟩ := (reprSub_has_true_and_false hn hS hne).1
    have := hev_out u v
    rw [hro, huv] at this; exact Bool.noConfusion this
  | cTrue => exact (hrout_ok.2 hro).elim
  | wire out' =>
    rw [hro] at hrout_ok hev_out
    have hR' : ReprSub n S res.1 out' := ⟨hWF', hrout_ok.1, fun u v => hev_out u v⟩
    have hmin := hM.2 res.1 out' hR'
    omega

lemma readOnce_or_leaves_card_le (hn : 3 ≤ n) {S : Finset (Fin (2 * n))} (hS : NoShortRun hn S)
    (hne : S.Nonempty) {D : BDag} {out : ℕ} (hM : IsMinBDag n S D out)
    {w : ℕ} (hw : w < 2 * n + D.length) (hRO : ReadOnce (2 * n) D w)
    (hnoAnd : ∀ j (hj : j < D.length), InCone (2 * n) D (2 * n + j) w → (D[j]).1 = false) :
    let L := Finset.univ.filter fun a : Fin (2 * n) => InCone (2 * n) D (toWire a) w
    (∀ a ∈ L, a ∈ S ∨ w = toWire a) ∧
    (∀ a ∈ L, ∀ b ∈ L, a ∈ S → b ∈ S → a.val % 2 = b.val % 2 → a = b) := by
  intro L
  constructor
  · intro a ha
    have hc : InCone (2 * n) D (toWire a) w := (Finset.mem_filter.mp ha).2
    by_cases heq : toWire a = w
    · exact Or.inr heq.symm
    · left
      by_contra hnotS
      have h0 := minBDag_inactive_input_fanout hn hS hne hM hnotS
      have h1 := hRO (toWire a) hc heq
      omega
  · intro a ha b hb haS hbS hpar
    by_contra hne_ab
    have hca : InCone (2 * n) D (toWire a) w := (Finset.mem_filter.mp ha).2
    have hcb : InCone (2 * n) D (toWire b) w := (Finset.mem_filter.mp hb).2
    have hwa_ne_wb : toWire a ≠ toWire b := fun h => hne_ab (toWire_inj h)
    have hOutNotStrict : ¬ (InCone (2 * n) D out w ∧ out ≠ w) := by
      rintro ⟨hc, hne_o⟩
      have h0 := (minBDag_out_last hn hS hne hM).2
      have h1 := hRO out hc hne_o
      omega
    obtain ⟨c, hcS, hdiff⟩ := noShortRun_no_twin hn hS haS hbS hne_ab
    have hagree_w : ∀ (x y : List Bool), x.length = 2 * n → y.length = 2 * n →
        x.getD (toWire a) false = true → y.getD (toWire b) false = true →
        (∀ i < 2 * n, i ≠ toWire a → i ≠ toWire b → x.getD i false = y.getD i false) →
        (evalBDag D x).getD out false = (evalBDag D y).getD out false := by
      intro x y hx hy hxa hyb hxy
      have hwx : (evalBDag D x).getD w false = true :=
        (eval_or_cone hM.1.1 hw hnoAnd x hx).mpr ⟨toWire a, toWire_lt a, hca, hxa⟩
      have hwy : (evalBDag D y).getD w false = true :=
        (eval_or_cone hM.1.1 hw hnoAnd y hy).mpr ⟨toWire b, toWire_lt b, hcb, hyb⟩
      refine eval_agree_outside_readOnce hM.1.1 hRO x y hx hy ?_ (hwx.trans hwy.symm) out hM.1.2.1 hOutNotStrict
      intro i hi hout_i
      apply hxy i hi
      · rintro rfl
        have hne_aw : toWire a ≠ w := by
          rintro heq
          have hle := inCone_le hM.1.1 hcb
          cases hcb with
          | refl => exact hwa_ne_wb heq
          | left hj _ => have := toWire_lt a; omega
          | right hj _ => have := toWire_lt a; omega
        exact hout_i ⟨hca, hne_aw⟩
      · rintro rfl
        have hne_bw : toWire b ≠ w := by
          rintro heq
          cases hca with
          | refl => exact hwa_ne_wb heq.symm
          | left hj _ => have := toWire_lt b; omega
          | right hj _ => have := toWire_lt b; omega
        exact hout_i ⟨hcb, hne_bw⟩
    have hc_par : c.val % 2 ≠ a.val % 2 := by
      rcases hdiff with ⟨hac, _⟩ | ⟨hbc, _⟩
      · exact (cycAdj_parity hn hac).symm
      · rw [hpar]; exact (cycAdj_parity hn hbc).symm
    by_cases hp : a.val % 2 = 1
    · let ua : Fin n := ⟨a.val / 2, by omega⟩
      let ub : Fin n := ⟨b.val / 2, by omega⟩
      let vc : Fin n := ⟨c.val / 2, by omega⟩
      have hae : a = leftV ua := Fin.ext (by simp [leftV, ua]; omega)
      have hbe : b = leftV ub := Fin.ext (by simp [leftV, ub]; omega)
      have hce : c = rightV vc := Fin.ext (by simp [rightV, vc]; omega)
      have hev := hagree_w (oneEach ua vc) (oneEach ub vc) (oneEach_length ua vc) (oneEach_length ub vc)
        (by rw [oneEach_getD_toWire, hae]; simp)
        (by rw [oneEach_getD_toWire, hbe]; simp) (by
        intro i hi h1 h2
        rw [oneEach_getD ua vc i hi, oneEach_getD ub vc i hi]
        rw [hae, toWire_leftV] at h1; rw [hbe, toWire_leftV] at h2
        simp [h1, h2])
      rw [hM.1.2.2 ua vc, hM.1.2.2 ub vc] at hev
      have hma : decide (leftV ua ∈ S ∧ rightV vc ∈ S) = true := decide_eq_true ⟨hae ▸ haS, hce ▸ hcS⟩
      have hmb : decide (leftV ub ∈ S ∧ rightV vc ∈ S) = true := decide_eq_true ⟨hbe ▸ hbS, hce ▸ hcS⟩
      rw [hma, hmb, Bool.true_and, Bool.true_and] at hev
      rcases hdiff with ⟨hac, hnbc⟩ | ⟨hbc, hnac⟩
      · have h1 : cycA n ua vc = true := (cycA_eq_cycAdj hn ua vc).mpr (hae ▸ hce ▸ hac)
        have h2 : cycA n ub vc = false := by
          cases hc' : cycA n ub vc
          · rfl
          · exact (hnbc (hbe ▸ hce ▸ (cycA_eq_cycAdj hn ub vc).mp hc')).elim
        rw [h1, h2] at hev; exact Bool.noConfusion hev
      · have h1 : cycA n ub vc = true := (cycA_eq_cycAdj hn ub vc).mpr (hbe ▸ hce ▸ hbc)
        have h2 : cycA n ua vc = false := by
          cases hc' : cycA n ua vc
          · rfl
          · exact (hnac (hae ▸ hce ▸ (cycA_eq_cycAdj hn ua vc).mp hc')).elim
        rw [h1, h2] at hev; exact Bool.noConfusion hev
    · let va : Fin n := ⟨a.val / 2, by omega⟩
      let vb : Fin n := ⟨b.val / 2, by omega⟩
      let uc : Fin n := ⟨c.val / 2, by omega⟩
      have hae : a = rightV va := Fin.ext (by simp [rightV, va]; omega)
      have hbe : b = rightV vb := Fin.ext (by simp [rightV, vb]; omega)
      have hce : c = leftV uc := Fin.ext (by simp [leftV, uc]; omega)
      have hev := hagree_w (oneEach uc va) (oneEach uc vb) (oneEach_length uc va) (oneEach_length uc vb)
        (by rw [oneEach_getD_toWire, hae]; simp)
        (by rw [oneEach_getD_toWire, hbe]; simp) (by
        intro i hi h1 h2
        rw [oneEach_getD uc va i hi, oneEach_getD uc vb i hi]
        rw [hae, toWire_rightV] at h1; rw [hbe, toWire_rightV] at h2
        simp [h1, h2])
      rw [hM.1.2.2 uc va, hM.1.2.2 uc vb] at hev
      have hma : decide (leftV uc ∈ S ∧ rightV va ∈ S) = true := decide_eq_true ⟨hce ▸ hcS, hae ▸ haS⟩
      have hmb : decide (leftV uc ∈ S ∧ rightV vb ∈ S) = true := decide_eq_true ⟨hce ▸ hcS, hbe ▸ hbS⟩
      rw [hma, hmb, Bool.true_and, Bool.true_and] at hev
      rcases hdiff with ⟨hac, hnbc⟩ | ⟨hbc, hnac⟩
      · have h1 : cycA n uc va = true := (cycA_eq_cycAdj hn uc va).mpr (hae ▸ hce ▸ (cycAdj_symm hn hac))
        have h2 : cycA n uc vb = false := by
          cases hc' : cycA n uc vb
          · rfl
          · exact (hnbc (cycAdj_symm hn (hbe ▸ hce ▸ (cycA_eq_cycAdj hn uc vb).mp hc'))).elim
        rw [h1, h2] at hev; exact Bool.noConfusion hev
      · have h1 : cycA n uc vb = true := (cycA_eq_cycAdj hn uc vb).mpr (hbe ▸ hce ▸ (cycAdj_symm hn hbc))
        have h2 : cycA n uc va = false := by
          cases hc' : cycA n uc va
          · rfl
          · exact (hnac (cycAdj_symm hn (hae ▸ hce ▸ (cycA_eq_cycAdj hn uc va).mp hc'))).elim
        rw [h1, h2] at hev; exact Bool.noConfusion hev

lemma readOnce_no_and (hn : 3 ≤ n) {S : Finset (Fin (2 * n))} (hS : NoShortRun hn S)
    (hne : S.Nonempty) {D : BDag} {out : ℕ} (hM : IsMinBDag n S D out)
    {g : ℕ} (hg : g < 2 * n + D.length) (hRO : ReadOnce (2 * n) D g) :
    ∀ j (hj : j < D.length), InCone (2 * n) D (2 * n + j) g → (D[j]).1 = false := by
  by_contra hhas
  push_neg at hhas
  have hex : ∃ j, ∃ hj : j < D.length, InCone (2 * n) D (2 * n + j) g ∧ (D[j]).1 = true := by
    obtain ⟨j, hj, hc, hne_f⟩ := hhas
    exact ⟨j, hj, hc, Bool.eq_true_of_not_eq_false hne_f⟩
  classical
  let j0 := Nat.find hex
  obtain ⟨hj0, hc0, hop0⟩ := Nat.find_spec hex
  have hmin_j0 : ∀ j' < j0, ∀ hj' : j' < D.length, InCone (2 * n) D (2 * n + j') g → (D[j']).1 = false := by
    intro j' hlt hj' hc'
    by_contra hne_f
    exact Nat.find_min hex hlt ⟨hj', hc', Bool.eq_true_of_not_eq_false hne_f⟩
  let w1 := (D[j0]).2.1
  let w2 := (D[j0]).2.2
  obtain ⟨hw1, hw2, hw12⟩ := hM.1.1 j0 hj0
  have hcw1 : InCone (2 * n) D w1 g := inCone_trans (InCone.left hj0 (InCone.refl _)) hc0
  have hcw2 : InCone (2 * n) D w2 g := inCone_trans (InCone.right hj0 (InCone.refl _)) hc0
  have hRO0 : ReadOnce (2 * n) D (2 * n + j0) := readOnce_sub hM.1.1 hRO hc0
  have hRO1 : ReadOnce (2 * n) D w1 := readOnce_sub hM.1.1 hRO hcw1
  have hRO2 : ReadOnce (2 * n) D w2 := readOnce_sub hM.1.1 hRO hcw2
  have hnoAnd1 : ∀ j (hj : j < D.length), InCone (2 * n) D (2 * n + j) w1 → (D[j]).1 = false := by
    intro j hj hc
    have hle := inCone_le hM.1.1 hc
    exact hmin_j0 j (by omega) hj (inCone_trans hc hcw1)
  have hnoAnd2 : ∀ j (hj : j < D.length), InCone (2 * n) D (2 * n + j) w2 → (D[j]).1 = false := by
    intro j hj hc
    have hle := inCone_le hM.1.1 hc
    exact hmin_j0 j (by omega) hj (inCone_trans hc hcw2)
  have hdisj := readOnce_operands_disjoint hM.1.1 hRO hj0 hc0

  obtain ⟨u, v, huv⟩ := minBDag_no_const_false_gate hn hS hne hM j0 hj0
  rw [evalBDag_at_gate hM.1.1 (oneEach u v) (oneEach_length u v) j0 hj0, hop0] at huv
  simp only [evalOp, ↓reduceIte, Bool.and_eq_true] at huv
  obtain ⟨i1, hi1, hci1, hxi1⟩ := (eval_or_cone hM.1.1 (by omega) hnoAnd1 (oneEach u v) (oneEach_length u v)).mp huv.1
  obtain ⟨i2, hi2, hci2, hxi2⟩ := (eval_or_cone hM.1.1 (by omega) hnoAnd2 (oneEach u v) (oneEach_length u v)).mp huv.2
  rw [oneEach_getD u v i1 hi1, decide_eq_true_iff] at hxi1
  rw [oneEach_getD u v i2 hi2, decide_eq_true_iff] at hxi2
  have hi1_ne_i2 : i1 ≠ i2 := fun h => hdisj i1 ⟨hci1, h ▸ hci2⟩

  have hcu_in : InCone (2 * n) D (toWire (leftV u)) (2 * n + j0) := by
    rcases hxi1 with rfl | rfl
    · rw [toWire_leftV]; exact InCone.left hj0 hci1
    · rcases hxi2 with rfl | rfl
      · rw [toWire_leftV]; exact InCone.right hj0 hci2
      · exact (hi1_ne_i2 rfl).elim
  have hcv_in : InCone (2 * n) D (toWire (rightV v)) (2 * n + j0) := by
    rcases hxi1 with rfl | rfl
    · rcases hxi2 with rfl | rfl
      · exact (hi1_ne_i2 rfl).elim
      · rw [toWire_rightV]; exact InCone.right hj0 hci2
    · rw [toWire_rightV]; exact InCone.left hj0 hci1
  have huS : leftV u ∈ S := by
    by_contra hnot
    have h0 := minBDag_inactive_input_fanout hn hS hne hM hnot
    have h1 := hRO0 (toWire (leftV u)) hcu_in (by have := toWire_lt (leftV u); omega)
    omega
  have hvS : rightV v ∈ S := by
    by_contra hnot
    have h0 := minBDag_inactive_input_fanout hn hS hne hM hnot
    have h1 := hRO0 (toWire (rightV v)) hcv_in (by have := toWire_lt (rightV v); omega)
    omega

  have hcases : (InCone (2 * n) D (toWire (leftV u)) w1 ∧ InCone (2 * n) D (toWire (rightV v)) w2) ∨
      (InCone (2 * n) D (toWire (leftV u)) w2 ∧ InCone (2 * n) D (toWire (rightV v)) w1) := by
    rcases hxi1 with rfl | rfl <;> rcases hxi2 with rfl | rfl
    · exact (hi1_ne_i2 rfl).elim
    · left; rw [toWire_leftV, toWire_rightV]; exact ⟨hci1, hci2⟩
    · right; rw [toWire_leftV, toWire_rightV]; exact ⟨hci2, hci1⟩
    · exact (hi1_ne_i2 rfl).elim
  have hOutNotStrict0 : ¬ (InCone (2 * n) D out (2 * n + j0) ∧ out ≠ 2 * n + j0) := by
    rintro ⟨hc, hne_o⟩
    have h0 := (minBDag_out_last hn hS hne hM).2
    have h1 := hRO0 out hc hne_o
    omega
  have hno_other_right : ∀ v' : Fin n, rightV v' ∈ S → v' ≠ v → ¬ cycAdj hn (leftV u) (rightV v') := by
    intro v' hv'S hv'ne hadj

    have hj0_false : (evalBDag D (oneEach u v')).getD (2 * n + j0) false = false := by
      rw [evalBDag_at_gate hM.1.1 (oneEach u v') (oneEach_length u v') j0 hj0, hop0]
      simp only [evalOp, ↓reduceIte]
      have hkill : (evalBDag D (oneEach u v')).getD w2 false = false ∨
          (evalBDag D (oneEach u v')).getD w1 false = false := by
        rcases hcases with ⟨hL1, hR2⟩ | ⟨hL2, hR1⟩
        · left
          cases hval : (evalBDag D (oneEach u v')).getD w2 false
          · rfl
          · exfalso
            obtain ⟨i, hi, hci, hxi⟩ := (eval_or_cone hM.1.1 (by omega) hnoAnd2 (oneEach u v') (oneEach_length u v')).mp hval
            rw [oneEach_getD u v' i hi, decide_eq_true_iff] at hxi
            rcases hxi with rfl | rfl
            · exact hdisj u.val ⟨by rwa [toWire_leftV] at hL1, hci⟩
            · have htw := (readOnce_or_leaves_card_le hn hS hne hM (by omega) hRO2 hnoAnd2).2
                (rightV v) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR2⟩)
                (rightV v') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [toWire_rightV]⟩)
                hvS hv'S (by simp [rightV])
              exact hv'ne (Fin.ext (by have := congrArg Fin.val htw; simp [rightV] at this; omega)).symm
        · right
          cases hval : (evalBDag D (oneEach u v')).getD w1 false
          · rfl
          · exfalso
            obtain ⟨i, hi, hci, hxi⟩ := (eval_or_cone hM.1.1 (by omega) hnoAnd1 (oneEach u v') (oneEach_length u v')).mp hval
            rw [oneEach_getD u v' i hi, decide_eq_true_iff] at hxi
            rcases hxi with rfl | rfl
            · exact hdisj u.val ⟨hci, by rwa [toWire_leftV] at hL2⟩
            · have htw := (readOnce_or_leaves_card_le hn hS hne hM (by omega) hRO1 hnoAnd1).2
                (rightV v) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR1⟩)
                (rightV v') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [toWire_rightV]⟩)
                hvS hv'S (by simp [rightV])
              exact hv'ne (Fin.ext (by have := congrArg Fin.val htw; simp [rightV] at this; omega)).symm
      rcases hkill with h | h
      · change (evalBDag D (oneEach u v')).getD (D[j0]).2.2 false = false at h
        rw [h]; exact Bool.and_false _
      · change (evalBDag D (oneEach u v')).getD (D[j0]).2.1 false = false at h
        rw [h]; exact Bool.false_and _

    let y : List Bool := List.ofFn fun i : Fin (2 * n) => decide (i.val = n + v'.val)
    have hj0_y : (evalBDag D y).getD (2 * n + j0) false = false := by
      have hle : ∀ i, y.getD i false = true → (oneEach u v').getD i false = true := by
        intro i hi
        by_cases hlt : i < 2 * n
        · rw [List.getD_eq_getElem _ _ (by simp [y, hlt])] at hi
          simp only [y, List.getElem_ofFn] at hi
          rw [oneEach_getD u v' i hlt, decide_eq_true_iff]
          exact Or.inr (of_decide_eq_true hi)
        · rw [List.getD_eq_default _ _ (by simp [y]; omega)] at hi; exact Bool.noConfusion hi
      cases hval : (evalBDag D y).getD (2 * n + j0) false
      · rfl
      · have := evalBDag_mono D y (oneEach u v') (by simp [y, oneEach_length]) hle (2 * n + j0) hval
        rw [hj0_false] at this; exact Bool.noConfusion this
    have heq := eval_agree_outside_readOnce hM.1.1 hRO0 (oneEach u v') y (oneEach_length u v') (by simp [y]) (by
      intro i hi hout_i
      rw [oneEach_getD u v' i hi, List.getD_eq_getElem _ _ (by simp [y, hi])]
      simp only [y, List.getElem_ofFn]
      have hne_u : i ≠ u.val := by
        rintro rfl
        exact hout_i ⟨by rwa [toWire_leftV] at hcu_in, by omega⟩
      simp [hne_u]) (hj0_false.trans hj0_y.symm) out hM.1.2.1 hOutNotStrict0
    have htr : (evalBDag D (oneEach u v')).getD out false = true := by
      rw [hM.1.2.2 u v', Bool.and_eq_true, decide_eq_true_iff, cycA_eq_cycAdj hn]
      exact ⟨⟨huS, hv'S⟩, hadj⟩
    have hfl := reprSub_eval_zero_left hn hM.1 v'
    rw [htr, hfl] at heq
    exact Bool.noConfusion heq
  have hno_other_left : ∀ u' : Fin n, leftV u' ∈ S → u' ≠ u → ¬ cycAdj hn (leftV u') (rightV v) := by
    intro u' hu'S hu'ne hadj
    have hj0_false : (evalBDag D (oneEach u' v)).getD (2 * n + j0) false = false := by
      rw [evalBDag_at_gate hM.1.1 (oneEach u' v) (oneEach_length u' v) j0 hj0, hop0]
      simp only [evalOp, ↓reduceIte]
      have hkill : (evalBDag D (oneEach u' v)).getD w1 false = false ∨
          (evalBDag D (oneEach u' v)).getD w2 false = false := by
        rcases hcases with ⟨hL1, hR2⟩ | ⟨hL2, hR1⟩
        · left
          cases hval : (evalBDag D (oneEach u' v)).getD w1 false
          · rfl
          · exfalso
            obtain ⟨i, hi, hci, hxi⟩ := (eval_or_cone hM.1.1 (by omega) hnoAnd1 (oneEach u' v) (oneEach_length u' v)).mp hval
            rw [oneEach_getD u' v i hi, decide_eq_true_iff] at hxi
            rcases hxi with rfl | rfl
            · have htw := (readOnce_or_leaves_card_le hn hS hne hM (by omega) hRO1 hnoAnd1).2
                (leftV u) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL1⟩)
                (leftV u') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [toWire_leftV]⟩)
                huS hu'S (by simp [leftV])
              exact hu'ne (Fin.ext (by have := congrArg Fin.val htw; simp [leftV] at this; omega)).symm
            · exact hdisj (n + v.val) ⟨hci, by rwa [toWire_rightV] at hR2⟩
        · right
          cases hval : (evalBDag D (oneEach u' v)).getD w2 false
          · rfl
          · exfalso
            obtain ⟨i, hi, hci, hxi⟩ := (eval_or_cone hM.1.1 (by omega) hnoAnd2 (oneEach u' v) (oneEach_length u' v)).mp hval
            rw [oneEach_getD u' v i hi, decide_eq_true_iff] at hxi
            rcases hxi with rfl | rfl
            · have htw := (readOnce_or_leaves_card_le hn hS hne hM (by omega) hRO2 hnoAnd2).2
                (leftV u) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hL2⟩)
                (leftV u') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [toWire_leftV]⟩)
                huS hu'S (by simp [leftV])
              exact hu'ne (Fin.ext (by have := congrArg Fin.val htw; simp [leftV] at this; omega)).symm
            · exact hdisj (n + v.val) ⟨by rwa [toWire_rightV] at hR1, hci⟩
      rcases hkill with h | h
      · change (evalBDag D (oneEach u' v)).getD (D[j0]).2.1 false = false at h
        rw [h]; exact Bool.false_and _
      · change (evalBDag D (oneEach u' v)).getD (D[j0]).2.2 false = false at h
        rw [h]; exact Bool.and_false _
    let y : List Bool := List.ofFn fun i : Fin (2 * n) => decide (i.val = u'.val)
    have hj0_y : (evalBDag D y).getD (2 * n + j0) false = false := by
      have hle : ∀ i, y.getD i false = true → (oneEach u' v).getD i false = true := by
        intro i hi
        by_cases hlt : i < 2 * n
        · rw [List.getD_eq_getElem _ _ (by simp [y, hlt])] at hi
          simp only [y, List.getElem_ofFn] at hi
          rw [oneEach_getD u' v i hlt, decide_eq_true_iff]
          exact Or.inl (of_decide_eq_true hi)
        · rw [List.getD_eq_default _ _ (by simp [y]; omega)] at hi; exact Bool.noConfusion hi
      cases hval : (evalBDag D y).getD (2 * n + j0) false
      · rfl
      · have := evalBDag_mono D y (oneEach u' v) (by simp [y, oneEach_length]) hle (2 * n + j0) hval
        rw [hj0_false] at this; exact Bool.noConfusion this
    have heq := eval_agree_outside_readOnce hM.1.1 hRO0 (oneEach u' v) y (oneEach_length u' v) (by simp [y]) (by
      intro i hi hout_i
      rw [oneEach_getD u' v i hi, List.getD_eq_getElem _ _ (by simp [y, hi])]
      simp only [y, List.getElem_ofFn]
      have hne_v : i ≠ n + v.val := by
        rintro rfl
        exact hout_i ⟨by rwa [toWire_rightV] at hcv_in, by omega⟩
      simp [hne_v]) (hj0_false.trans hj0_y.symm) out hM.1.2.1 hOutNotStrict0
    have htr : (evalBDag D (oneEach u' v)).getD out false = true := by
      rw [hM.1.2.2 u' v, Bool.and_eq_true, decide_eq_true_iff, cycA_eq_cycAdj hn]
      exact ⟨⟨hu'S, hvS⟩, hadj⟩
    have hfl := reprSub_eval_zero_right hn hM.1 u'
    rw [htr, hfl] at heq
    exact Bool.noConfusion heq

  by_cases hadj : cycAdj hn (leftV u) (rightV v)
  · rcases noShortRun_no_isolated_edge hn hS huS hvS hadj with ⟨c, hcS, hcn, hac⟩ | ⟨c, hcS, hcn, hbc⟩
    · have hpar := cycAdj_parity hn hac
      let v' : Fin n := ⟨c.val / 2, by omega⟩
      have hce : c = rightV v' := Fin.ext (by simp [rightV, v', leftV] at hpar ⊢; omega)
      exact hno_other_right v' (hce ▸ hcS) (fun h => hcn (hce.trans (congrArg rightV h))) (hce ▸ hac)
    · have hpar := cycAdj_parity hn hbc
      let u' : Fin n := ⟨c.val / 2, by omega⟩
      have hce : c = leftV u' := Fin.ext (by simp [leftV, u', rightV] at hpar ⊢; omega)
      exact hno_other_left u' (hce ▸ hcS) (fun h => hcn (hce.trans (congrArg leftV h))) (cycAdj_symm hn (hce ▸ hbc))
  · obtain ⟨c, hcS, hac⟩ := noShortRun_deg_pos hn hS huS
    have hpar := cycAdj_parity hn hac
    let v' : Fin n := ⟨c.val / 2, by omega⟩
    have hce : c = rightV v' := Fin.ext (by simp [rightV, v', leftV] at hpar ⊢; omega)
    have hne_v : v' ≠ v := fun h => hadj (h ▸ hce ▸ hac)
    exact hno_other_right v' (hce ▸ hcS) hne_v (hce ▸ hac)

lemma minBDag_exists_branch (hn : 3 ≤ n) {S : Finset (Fin (2 * n))} (hS : NoShortRun hn S)
    (hne : S.Nonempty) {D : BDag} {out : ℕ} (hM : IsMinBDag n S D out) :
    ∃ g < 2 * n + D.length, 2 ≤ fanout D g := by
  by_contra hno
  push_neg at hno
  have hRO : ReadOnce (2 * n) D out := by
    intro u hu hne_u
    have hle := hno u (Nat.lt_of_le_of_lt (inCone_le hM.1.1 hu) hM.1.2.1)
    obtain ⟨j, hj, _, hr⟩ := inCone_has_reader hM.1.1 hu hne_u
    have hpos : 1 ≤ fanout D u := Finset.card_pos.mpr ⟨j, by
      rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hj, by simp [hj, hr]⟩⟩
    omega
  have hnoAnd := readOnce_no_and hn hS hne hM hM.1.2.1 hRO

  have hLcard : (Finset.univ.filter fun a : Fin (2 * n) => InCone (2 * n) D (toWire a) out).card ≤ 2 := by
    let L := Finset.univ.filter fun a : Fin (2 * n) => InCone (2 * n) D (toWire a) out
    have hout_ge := reprSub_out_ge hn hS hne hM.1
    have hsubS : ∀ a ∈ L, a ∈ S := fun a ha => by
      rcases (readOnce_or_leaves_card_le hn hS hne hM hM.1.2.1 hRO hnoAnd).1 a ha with h | h
      · exact h
      · have := toWire_lt a; omega
    have huniq := (readOnce_or_leaves_card_le hn hS hne hM hM.1.2.1 hRO hnoAnd).2
    have hL0 : (L.filter fun a => a.val % 2 = 0).card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb =>
      huniq a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
        (hsubS a (Finset.mem_filter.mp ha).1) (hsubS b (Finset.mem_filter.mp hb).1)
        ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
    have hL1 : (L.filter fun a => a.val % 2 = 1).card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb =>
      huniq a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
        (hsubS a (Finset.mem_filter.mp ha).1) (hsubS b (Finset.mem_filter.mp hb).1)
        ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
    have hpart : L = (L.filter fun a => a.val % 2 = 0) ∪ (L.filter fun a => a.val % 2 = 1) := by
      ext a; simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro ha; by_cases h : a.val % 2 = 0
        · exact Or.inl ⟨ha, h⟩
        · exact Or.inr ⟨ha, by omega⟩
      · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
    calc L.card = ((L.filter fun a => a.val % 2 = 0) ∪ (L.filter fun a => a.val % 2 = 1)).card := by rw [← hpart]
      _ ≤ (L.filter fun a => a.val % 2 = 0).card + (L.filter fun a => a.val % 2 = 1).card := Finset.card_union_le _ _
      _ ≤ 1 + 1 := Nat.add_le_add hL0 hL1

  obtain ⟨i, hi, hci⟩ := exists_leaf_inCone hM.1.1 hM.1.2.1
  let a := fromWire i hi
  have hca : InCone (2 * n) D (toWire a) out := by rwa [toWire_fromWire]
  by_cases hp : a.val % 2 = 1
  · let u : Fin n := ⟨a.val / 2, by omega⟩
    have hae : a = leftV u := Fin.ext (by simp [leftV, u]; omega)
    obtain ⟨v0, hv0⟩ := exists_non_adj_right hn u
    have htr : (evalBDag D (oneEach u v0)).getD out false = true :=
      (eval_or_cone hM.1.1 hM.1.2.1 hnoAnd (oneEach u v0) (oneEach_length u v0)).mpr
        ⟨toWire a, toWire_lt a, hca, by rw [oneEach_getD_toWire, hae]; simp⟩
    rw [hM.1.2.2 u v0] at htr
    have hca_tr : cycA n u v0 = true := (Bool.and_eq_true _ _ |>.mp htr).2
    exact hv0 ((cycA_eq_cycAdj hn u v0).mp hca_tr)
  · let v : Fin n := ⟨a.val / 2, by omega⟩
    have hae : a = rightV v := Fin.ext (by simp [rightV, v]; omega)
    obtain ⟨u0, hu0⟩ := exists_non_adj_left hn v
    have htr : (evalBDag D (oneEach u0 v)).getD out false = true :=
      (eval_or_cone hM.1.1 hM.1.2.1 hnoAnd (oneEach u0 v) (oneEach_length u0 v)).mpr
        ⟨toWire a, toWire_lt a, hca, by rw [oneEach_getD_toWire, hae]; simp⟩
    rw [hM.1.2.2 u0 v] at htr
    have hca_tr : cycA n u0 v = true := (Bool.and_eq_true _ _ |>.mp htr).2
    exact hu0 ((cycA_eq_cycAdj hn u0 v).mp hca_tr)

lemma minBDag_card_le (hn : 3 ≤ n) {S : Finset (Fin (2 * n))} (hS : NoShortRun hn S)
    (hne : S.Nonempty) {D : BDag} {out : ℕ} (hM : IsMinBDag n S D out) :
    S.card ≤ D.length := by
  obtain ⟨g, hg, hfg⟩ := minBDag_exists_branch hn hS hne hM
  have hout_last := minBDag_out_last hn hS hne hM
  have hg_ne_out : g ≠ out := fun h => by rw [h, hout_last.2] at hfg; omega
  let W := (S.image toWire) ∪ ((Finset.range D.length).image (fun j => 2 * n + j)).erase out
  have hWsub : W ⊆ Finset.range (2 * n + D.length) := by
    intro w hw
    rw [Finset.mem_union] at hw
    rcases hw with hw | hw
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_range.mpr (by have := toWire_lt a; omega)
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hw)
      exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega)
  have hWdisj : Disjoint (S.image toWire) (((Finset.range D.length).image (fun j => 2 * n + j)).erase out) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase h2)
    have := toWire_lt a; omega
  have hWcard : W.card = S.card + D.length - 1 := by
    rw [Finset.card_union_of_disjoint hWdisj, Finset.card_image_of_injective S toWire_inj]
    have hout_mem : out ∈ (Finset.range D.length).image (fun j => 2 * n + j) := by
      have := reprSub_out_ge hn hS hne hM.1
      have := hM.1.2.1
      refine Finset.mem_image.mpr ⟨out - 2 * n, Finset.mem_range.mpr (by omega), by omega⟩
    rw [Finset.card_erase_of_mem hout_mem, Finset.card_image_of_injective _ (fun a b h => by omega),
        Finset.card_range]
    have hDpos : 1 ≤ D.length := by have := reprSub_out_ge hn hS hne hM.1; omega
    omega
  have hgW : g ∈ W := by
    by_cases hgm : g < 2 * n
    · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨fromWire g hgm, ?_, toWire_fromWire g hgm⟩)
      by_contra hnot
      have h0 := minBDag_inactive_input_fanout hn hS hne hM hnot
      rw [toWire_fromWire] at h0; omega
    · refine Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hg_ne_out,
        Finset.mem_image.mpr ⟨g - 2 * n, Finset.mem_range.mpr (by omega), by omega⟩⟩)
  have hge1 : ∀ w ∈ W, 1 ≤ fanout D w := by
    intro w hw
    rw [Finset.mem_union] at hw
    rcases hw with hw | hw
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
      exact minBDag_active_input_fanout hn hS hne hM ha
    · have hne_o := (Finset.mem_erase.mp hw).1
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hw)
      exact minBDag_live_gates hn hS hne hM j (Finset.mem_range.mp hj) hne_o
  have hsum_ge : W.card + 1 ≤ ∑ w ∈ W, fanout D w := by
    rw [← Finset.add_sum_erase _ _ hgW]
    have hrest : (W.erase g).card ≤ ∑ w ∈ W.erase g, fanout D w := by
      calc (W.erase g).card = ∑ _ ∈ W.erase g, 1 := by simp
        _ ≤ ∑ w ∈ W.erase g, fanout D w := Finset.sum_le_sum fun w hw => hge1 w (Finset.mem_of_mem_erase hw)
    have hce := Finset.card_erase_add_one hgW
    omega
  have hsum_le : ∑ w ∈ W, fanout D w ≤ 2 * D.length :=
    (Finset.sum_le_sum_of_subset hWsub).trans_eq (sum_fanout (2 * n) D hM.1.1)
  have hDpos : 1 ≤ D.length := by have := reprSub_out_ge hn hS hne hM.1; omega
  omega

lemma bdag_lower_bound (hn : 3 ≤ n) :
    ∀ k : ℕ, ∀ (S : Finset (Fin (2 * n))), S.card = k → NoShortRun hn S → S.Nonempty →
      ∀ (D : BDag) (out : ℕ), ReprSub n S D out →
        S.card - 1 + (phi hn S + 7) / 8 ≤ D.length := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro S hSk hS hne D0 out0 hR0

    have hexMin : ∃ s, ∃ D out, D.length = s ∧ ReprSub n S D out := ⟨D0.length, D0, out0, rfl, hR0⟩
    classical
    let sMin := Nat.find hexMin
    obtain ⟨D, out, hDlen, hRD⟩ := Nat.find_spec hexMin
    have hM : IsMinBDag n S D out := ⟨hRD, fun D' out' hR' => by
      rw [hDlen]; exact Nat.find_min' hexMin ⟨D', out', rfl, hR'⟩⟩
    have hDleD0 : D.length ≤ D0.length := hM.2 D0 out0 hR0
    suffices hgoal : S.card - 1 + (phi hn S + 7) / 8 ≤ D.length by omega
    by_cases hsmall : phi hn S ≤ 8
    · have hbase := minBDag_card_le hn hS hne hM
      have h4 := card_ge_four_of_nonempty hn hS hne
      omega
    ·
      have hexB := minBDag_exists_branch hn hS hne hM
      let g := Nat.find hexB
      obtain ⟨hg_lt, hfg⟩ := Nat.find_spec hexB
      have hROg : ReadOnce (2 * n) D g := by
        intro u hu hne_u
        have hult : u < g := inCone_lt_of_ne hM.1.1 hu hne_u
        have hle1 : fanout D u < 2 := by
          by_contra hge2
          push_neg at hge2
          exact Nat.find_min hexB hult ⟨by omega, hge2⟩
        obtain ⟨j, hj, _, hr⟩ := inCone_has_reader hM.1.1 hu hne_u
        have hpos : 1 ≤ fanout D u := Finset.card_pos.mpr ⟨j, by
          rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hj, by simp [hj, hr]⟩⟩
        omega
      have hnoAnd := readOnce_no_and hn hS hne hM hg_lt hROg
      let L := Finset.univ.filter fun a : Fin (2 * n) => InCone (2 * n) D (toWire a) g
      have hLsubS : L ⊆ S := by
        intro a ha
        rcases (readOnce_or_leaves_card_le hn hS hne hM hg_lt hROg hnoAnd).1 a ha with h | h
        · exact h
        · by_contra hnot
          have h0 := minBDag_inactive_input_fanout hn hS hne hM hnot
          rw [← h] at h0; omega
      have hLcard : L.card ≤ 2 := by
        have huniq := (readOnce_or_leaves_card_le hn hS hne hM hg_lt hROg hnoAnd).2
        have hL0 : (L.filter fun a => a.val % 2 = 0).card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb =>
          huniq a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
            (hLsubS (Finset.mem_filter.mp ha).1) (hLsubS (Finset.mem_filter.mp hb).1)
            ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
        have hL1 : (L.filter fun a => a.val % 2 = 1).card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb =>
          huniq a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
            (hLsubS (Finset.mem_filter.mp ha).1) (hLsubS (Finset.mem_filter.mp hb).1)
            ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
        have hpart : L = (L.filter fun a => a.val % 2 = 0) ∪ (L.filter fun a => a.val % 2 = 1) := by
          ext a; simp only [Finset.mem_union, Finset.mem_filter]
          constructor
          · intro ha; by_cases h : a.val % 2 = 0
            · exact Or.inl ⟨ha, h⟩
            · exact Or.inr ⟨ha, by omega⟩
          · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
        calc L.card = ((L.filter fun a => a.val % 2 = 0) ∪ (L.filter fun a => a.val % 2 = 1)).card := by rw [← hpart]
          _ ≤ (L.filter fun a => a.val % 2 = 0).card + (L.filter fun a => a.val % 2 = 1).card := Finset.card_union_le _ _
          _ ≤ 1 + 1 := Nat.add_le_add hL0 hL1
      have hLne : L.Nonempty := by
        obtain ⟨i, hi, hci⟩ := exists_leaf_inCone hM.1.1 hg_lt
        exact ⟨fromWire i hi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [toWire_fromWire]⟩⟩

      obtain ⟨S', hS'sub, hdisjL, hgood', hphi'⟩ := trim_le2_exists hn hS L hLsubS hLcard
      have hphi'_pos : 0 < phi hn S' := by omega
      have hS'ne : S'.Nonempty := nonempty_of_phi_pos hn hphi'_pos
      let Z := S \ S'
      have hZsub : Z ⊆ S := Finset.sdiff_subset
      have hLZ : L ⊆ Z := fun a ha => Finset.mem_sdiff.mpr ⟨hLsubS ha, Finset.disjoint_left.mp hdisjL ha⟩
      have hS'lt : S'.card < k := by
        obtain ⟨a, ha⟩ := hLne
        have hss : S' ⊂ S := Finset.ssubset_iff_subset_ne.mpr
          ⟨hS'sub, fun h => Finset.disjoint_left.mp hdisjL ha (h ▸ hLsubS ha)⟩
        exact hSk ▸ Finset.card_lt_card hss

      let killIn : ℕ → Bool := fun i => if h : i < 2 * n then decide (fromWire i h ∈ Z) else false
      obtain ⟨hWF', helen, hok, hin, hiff, hcnt, hev⟩ :=
        zeroFold_spec (2 * n) killIn (fun _ => false) D hM.1.1
      set res := zeroFold (2 * n) killIn (fun _ => false) D

      have hev_out : ∀ u v : Fin n,
          evalRef (evalBDag res.1 (oneEach u v)) (res.2.getD out .cFalse) =
            (decide (leftV u ∈ S' ∧ rightV v ∈ S') && cycA n u v) := by
        intro u v
        have h1 := hev (oneEach u v) (oneEach_length u v) (fun _ _ h => Bool.noConfusion h) out hM.1.2.1
        rw [h1]
        set x0 := List.ofFn fun i : Fin (2 * n) => if killIn i.val then false else (oneEach u v).getD i.val false
        by_cases hmem : leftV u ∈ S' ∧ rightV v ∈ S'
        · have hsame : x0 = oneEach u v := by
            apply List.ext_getElem (by simp [x0, oneEach_length])
            intro i hi1 hi2
            have hi : i < 2 * n := by rw [oneEach_length] at hi2; exact hi2
            simp only [x0, List.getElem_ofFn, killIn, hi, ↓reduceDIte]
            split_ifs with hiz
            · have hz : fromWire i hi ∈ Z := of_decide_eq_true hiz
              rw [← List.getD_eq_getElem _ _ hi2]
              have heq_w : i = toWire (fromWire i hi) := (toWire_fromWire i hi).symm
              rw [heq_w, oneEach_getD_toWire]
              have h1 : fromWire i hi ≠ leftV u := fun h => (Finset.mem_sdiff.mp hz).2 (h ▸ hmem.1)
              have h2 : fromWire i hi ≠ rightV v := fun h => (Finset.mem_sdiff.mp hz).2 (h ▸ hmem.2)
              simp [h1, h2]
            · exact List.getD_eq_getElem (oneEach u v) false hi2
          rw [hsame, hM.1.2.2 u v]
          simp [hmem, hS'sub hmem.1, hS'sub hmem.2]
        · have hresf : (decide (leftV u ∈ S' ∧ rightV v ∈ S') && cycA n u v) = false := by simp [hmem]
          rw [hresf]
          by_cases hmemS : leftV u ∈ S ∧ rightV v ∈ S
          ·
            have horZ : leftV u ∈ Z ∨ rightV v ∈ Z := by
              by_cases hu' : leftV u ∈ S'
              · exact Or.inr (Finset.mem_sdiff.mpr ⟨hmemS.2, fun hv' => hmem ⟨hu', hv'⟩⟩)
              · exact Or.inl (Finset.mem_sdiff.mpr ⟨hmemS.1, hu'⟩)
            rcases horZ with huZ | hvZ
            · have hle : ∀ i, x0.getD i false = true →
                  (List.ofFn fun j : Fin (2 * n) => decide (j.val = n + v.val)).getD i false = true := by
                intro i hi
                by_cases hlt : i < 2 * n
                · rw [List.getD_eq_getElem _ _ (by simp [x0, hlt])] at hi
                  simp only [x0, List.getElem_ofFn, killIn, hlt, ↓reduceDIte] at hi
                  by_cases hiz : decide (fromWire i hlt ∈ Z) = true
                  · simp [hiz] at hi
                  · simp only [hiz, Bool.false_eq_true, ↓reduceIte] at hi
                    rw [oneEach_getD u v i hlt, decide_eq_true_iff] at hi
                    rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn, decide_eq_true_iff]
                    rcases hi with rfl | hnv
                    · exfalso; apply hiz; rw [decide_eq_true_iff]
                      have : fromWire u.val hlt = leftV u := by
                        apply toWire_inj; rw [toWire_fromWire, toWire_leftV]
                      rwa [this]
                    · exact hnv
                · rw [List.getD_eq_default _ _ (by simp [x0]; omega)] at hi; exact Bool.noConfusion hi
              have hm := evalBDag_mono D x0 _ (by simp [x0]) hle out
              have hf := reprSub_eval_zero_left hn hM.1 v
              cases hval : (evalBDag D x0).getD out false
              · rfl
              · exact (Bool.false_ne_true (hf.symm.trans (hm hval))).elim
            · have hle : ∀ i, x0.getD i false = true →
                  (List.ofFn fun j : Fin (2 * n) => decide (j.val = u.val)).getD i false = true := by
                intro i hi
                by_cases hlt : i < 2 * n
                · rw [List.getD_eq_getElem _ _ (by simp [x0, hlt])] at hi
                  simp only [x0, List.getElem_ofFn, killIn, hlt, ↓reduceDIte] at hi
                  by_cases hiz : decide (fromWire i hlt ∈ Z) = true
                  · simp [hiz] at hi
                  · simp only [hiz, Bool.false_eq_true, ↓reduceIte] at hi
                    rw [oneEach_getD u v i hlt, decide_eq_true_iff] at hi
                    rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_ofFn, decide_eq_true_iff]
                    rcases hi with hu_eq | rfl
                    · exact hu_eq
                    · exfalso; apply hiz; rw [decide_eq_true_iff]
                      have : fromWire (n + v.val) hlt = rightV v := by
                        apply toWire_inj; rw [toWire_fromWire, toWire_rightV]
                      rwa [this]
                · rw [List.getD_eq_default _ _ (by simp [x0]; omega)] at hi; exact Bool.noConfusion hi
              have hm := evalBDag_mono D x0 _ (by simp [x0]) hle out
              have hf := reprSub_eval_zero_right hn hM.1 u
              cases hval : (evalBDag D x0).getD out false
              · rfl
              · exact (Bool.false_ne_true (hf.symm.trans (hm hval))).elim
          · have hle : ∀ i, x0.getD i false = true → (oneEach u v).getD i false = true := by
              intro i hi
              by_cases hlt : i < 2 * n
              · rw [List.getD_eq_getElem _ _ (by simp [x0, hlt])] at hi
                simp only [x0, List.getElem_ofFn] at hi
                by_cases hki : killIn i = true
                · simp [hki] at hi
                · simpa [hki] using hi
              · rw [List.getD_eq_default _ _ (by simp [x0]; omega)] at hi; exact Bool.noConfusion hi
            have hm := evalBDag_mono D x0 (oneEach u v) (by simp [x0, oneEach_length]) hle out
            have hf : (evalBDag D (oneEach u v)).getD out false = false := by
              rw [hM.1.2.2 u v]; simp [hmemS]
            cases hval : (evalBDag D x0).getD out false
            · rfl
            · exact (Bool.false_ne_true (hf.symm.trans (hm hval))).elim

      have hrout_ok : refOk (2 * n + res.1.length) (res.2.getD out .cFalse) ∧
          res.2.getD out .cFalse ≠ .cTrue := by
        rw [List.getD_eq_getElem _ _ (by rw [helen]; exact hM.1.2.1)]
        exact hok _ (List.getElem_mem _)
      have hrout_ncf : res.2.getD out .cFalse ≠ .cFalse := by
        intro hcf
        obtain ⟨u, v, huv⟩ := (reprSub_has_true_and_false hn hgood' hS'ne).1
        have := hev_out u v
        rw [hcf, huv] at this; exact Bool.noConfusion this
      obtain ⟨out', hout'_eq⟩ : ∃ out', res.2.getD out .cFalse = .wire out' := by
        cases h : res.2.getD out .cFalse with
        | cFalse => exact (hrout_ncf h).elim
        | cTrue => exact (hrout_ok.2 h).elim
        | wire idx => exact ⟨idx, rfl⟩
      rw [hout'_eq] at hrout_ok hev_out
      have hR' : ReprSub n S' res.1 out' := ⟨hWF', hrout_ok.1, fun u v => hev_out u v⟩

      have hg_cf : res.2.getD g .cFalse = .cFalse := by
        suffices h : ∀ w < 2 * n + D.length, InCone (2 * n) D w g → res.2.getD w .cFalse = .cFalse from
          h g hg_lt (InCone.refl g)
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ihw =>
          intro hw hcw
          by_cases hwm : w < 2 * n
          · rw [hin w hwm]
            simp only [killIn, hwm, ↓reduceDIte]
            have hmemL : fromWire w hwm ∈ L :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [toWire_fromWire]⟩
            simp [hLZ hmemL]
          · let j := w - 2 * n
            have hj : j < D.length := by omega
            have hwj : w = 2 * n + j := by omega
            have hop : (D[j]).1 = false := hnoAnd j hj (hwj ▸ hcw)
            obtain ⟨ha, hb, _⟩ := hM.1.1 j hj
            rw [hwj, hiff j hj]
            refine Or.inr (Or.inr ⟨hop, ?_, ?_⟩)
            · exact ihw (D[j]).2.1 (by omega) (by omega) (inCone_trans (InCone.left hj (InCone.refl _)) (hwj ▸ hcw))
            · exact ihw (D[j]).2.2 (by omega) (by omega) (inCone_trans (InCone.right hj (InCone.refl _)) (hwj ▸ hcw))

      let K := (Finset.range (2 * n + D.length)).filter fun w => res.2.getD w .cFalse = .cFalse
      let ZG := (Finset.range D.length).filter fun j => res.2.getD (2 * n + j) .cFalse = .cFalse
      let Alive := (Finset.range D.length).filter fun j =>
        if hj : j < D.length then
          res.2.getD (D[j]).2.1 .cFalse ≠ .cFalse ∧ res.2.getD (D[j]).2.2 .cFalse ≠ .cFalse
        else false
      have hK_eq : K = (Z.image toWire) ∪ (ZG.image fun j => 2 * n + j) := by
        ext w
        simp only [K, ZG, Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image]
        constructor
        · rintro ⟨hw, hcf⟩
          by_cases hwm : w < 2 * n
          · left
            refine ⟨fromWire w hwm, ?_, toWire_fromWire w hwm⟩
            rw [hin w hwm] at hcf
            simp only [killIn, hwm, ↓reduceDIte] at hcf
            by_cases h : fromWire w hwm ∈ Z
            · exact h
            · simp [h] at hcf
          · right
            exact ⟨w - 2 * n, ⟨by omega, by rwa [show 2 * n + (w - 2 * n) = w by omega]⟩, by omega⟩
        · rintro (⟨a, ha, rfl⟩ | ⟨j, ⟨hj, hcf⟩, rfl⟩)
          · refine ⟨by have := toWire_lt a; omega, ?_⟩
            rw [hin (toWire a) (toWire_lt a)]
            simp [killIn, toWire_lt a, fromWire_toWire, ha]
          · exact ⟨by omega, hcf⟩
      have hK_disj : Disjoint (Z.image toWire) (ZG.image fun j => 2 * n + j) := by
        rw [Finset.disjoint_left]
        intro w h1 h2
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h2
        have := toWire_lt a; omega
      have hK_card : K.card = Z.card + ZG.card := by
        rw [hK_eq, Finset.card_union_of_disjoint hK_disj,
            Finset.card_image_of_injective _ toWire_inj,
            Finset.card_image_of_injective _ (fun a b h => by omega)]
      have hgK : g ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg_lt, hg_cf⟩
      have hK_ge1 : ∀ w ∈ K, 1 ≤ fanout D w := by
        intro w hw
        rw [hK_eq, Finset.mem_union] at hw
        rcases hw with hw | hw
        · obtain ⟨a, haZ, rfl⟩ := Finset.mem_image.mp hw
          exact minBDag_active_input_fanout hn hS hne hM (hZsub haZ)
        · obtain ⟨j, hjZG, rfl⟩ := Finset.mem_image.mp hw
          have hj := Finset.mem_range.mp (Finset.mem_filter.mp hjZG).1
          have hne_o : 2 * n + j ≠ out := fun h => hrout_ncf (h ▸ (Finset.mem_filter.mp hjZG).2)
          exact minBDag_live_gates hn hS hne hM j hj hne_o
      have hsum_lo : K.card + 1 ≤ ∑ w ∈ K, fanout D w := by
        rw [← Finset.add_sum_erase _ _ hgK]
        have hrest : (K.erase g).card ≤ ∑ w ∈ K.erase g, fanout D w := by
          calc (K.erase g).card = ∑ _ ∈ K.erase g, 1 := by simp
            _ ≤ ∑ w ∈ K.erase g, fanout D w := Finset.sum_le_sum fun w hw => hK_ge1 w (Finset.mem_of_mem_erase hw)
        have hce := Finset.card_erase_add_one hgK
        have hfg' : 2 ≤ fanout D g := hfg
        omega
      have hsum_hi : ∑ w ∈ K, fanout D w ≤ 2 * ZG.card + (D.length - ZG.card - Alive.card) :=
        sum_fanout_zero_bound (2 * n) D hM.1.1 res.2 (fun j hj => by simpa using hiff j hj)
      have hres_le_Alive : res.1.length ≤ Alive.card := by
        refine hcnt.trans (Finset.card_le_card ?_)
        intro j hj
        rw [Finset.mem_filter] at hj ⊢
        refine ⟨hj.1, ?_⟩
        have hjlt := Finset.mem_range.mp hj.1
        simp only [hjlt, ↓reduceDIte] at hj ⊢
        exact ⟨hj.2.2.1, hj.2.2.2⟩
      have hstep_drop : res.1.length + Z.card + 1 ≤ D.length := by
        have hZA : ZG.card + Alive.card ≤ D.length := by
          have hdisjZA : Disjoint ZG Alive := by
            rw [Finset.disjoint_left]
            intro j h1 h2
            rw [Finset.mem_filter] at h1 h2
            have hj := Finset.mem_range.mp h1.1
            simp only [hj, ↓reduceDIte] at h2
            rcases (hiff j hj).mp h1.2 with h | ⟨_, h | h⟩ | ⟨_, h, _⟩
            · exact Bool.noConfusion h
            · exact h2.2.1 h
            · exact h2.2.2 h
            · exact h2.2.1 h
          rw [← Finset.card_union_of_disjoint hdisjZA]
          exact (Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))).trans (by simp)
        omega

      have hIH := ih S'.card hS'lt S' rfl hgood' hS'ne res.1 out' hR'
      have hZS : S'.card + Z.card = S.card := by
        rw [add_comm]; exact Finset.card_sdiff_add_card_eq_card hS'sub
      have hS'4 := card_ge_four_of_nonempty hn hgood' hS'ne
      omega

theorem main (n s : ℕ) (hn : 3 ≤ n)
    (hrep : RepSizeAtMost (fun u v : Fin n => decide (v.val = u.val ∨ v.val = (u.val + 1) % n)) s) :
    2 * n - 1 + (n + 2) / 4 ≤ s := by
  obtain ⟨C, hmono, hsz, hrepr⟩ := hrep
  obtain ⟨D, r, hWF, hDle, hrok, hev⟩ := compile_monotone2 (2 * n) C hmono
  have hS : NoShortRun hn (Finset.univ : Finset (Fin (2 * n))) := noShortRun_univ hn
  have hne : (Finset.univ : Finset (Fin (2 * n))).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hrf : ∀ u v : Fin n, evalRef (evalBDag D (oneEach u v)) r =
      (decide (leftV u ∈ (Finset.univ : Finset (Fin (2 * n))) ∧ rightV v ∈ (Finset.univ : Finset (Fin (2 * n)))) && cycA n u v) := by
    intro u v
    rw [hev (oneEach u v) (oneEach_length u v), hrepr u v]
    simp [cycA]
  cases hr : r with
  | cFalse =>
    obtain ⟨u, v, huv⟩ := (reprSub_has_true_and_false hn hS hne).1
    have := hrf u v; rw [hr, huv] at this; exact Bool.noConfusion this
  | cTrue =>
    obtain ⟨u, v, huv⟩ := (reprSub_has_true_and_false hn hS hne).2
    have := hrf u v; rw [hr, huv] at this; exact Bool.noConfusion this
  | wire out =>
    have hR : ReprSub n Finset.univ D out :=
      ⟨hWF, by simpa [hr, refOk] using hrok, fun u v => by simpa [hr, evalRef] using hrf u v⟩
    have hlb := bdag_lower_bound hn (2 * n) Finset.univ (by simp) hS hne D out hR
    rw [Finset.card_univ, Fintype.card_fin, phi_univ hn] at hlb
    change D.length ≤ C.size at hDle
    omega

end MainProof

end PEqualNP.Outside.L_meta_17154_aux

theorem PEqualNP.Outside.L_meta_17154 : (∀ n s : ℕ, 3 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (v.val = u.val ∨ v.val = (u.val + 1) % n)) s → 2 * n - 1 + (n + 2) / 4 ≤ s) :=
  PEqualNP.Outside.L_meta_17154_aux.main
