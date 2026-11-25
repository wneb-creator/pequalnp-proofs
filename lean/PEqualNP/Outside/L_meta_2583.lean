import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma incidence_prime_iff (P L : ℕ) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    (S : Finset (Fin (P + L))) :
    IsPrimeImplicant (P + L) C S ↔
      ∃ p : Fin P, ∃ l : Fin L, I p l ∧ S = {Fin.castAdd L p, Fin.natAdd P l} := by
  classical
  have separated (p : Fin P) (l : Fin L) :
      Fin.castAdd L p ≠ Fin.natAdd P l := by
    intro h
    have hv := congrArg Fin.val h
    change p.val = P + l.val at hv
    omega
  have accepts (T : Finset (Fin (P + L))) :
      circuitFun (P + L) C (setInput T) = true ↔
        ∃ p : Fin P, ∃ l : Fin L, I p l ∧
          Fin.castAdd L p ∈ T ∧ Fin.natAdd P l ∈ T := by
    rw [hC]
    simp [setInput]
  constructor
  · rintro ⟨htrue, hproper⟩
    obtain ⟨p, l, hI, hp, hl⟩ := (accepts S).mp htrue
    let T : Finset (Fin (P + L)) := {Fin.castAdd L p, Fin.natAdd P l}
    have hsub : T ⊆ S := by
      simp only [T, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hp, hl⟩
    have heq : T = S := by
      by_contra hne
      have hstrict : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
      have ht : circuitFun (P + L) C (setInput T) = true :=
        (accepts T).mpr ⟨p, l, hI, by simp [T], by simp [T]⟩
      have hf := hproper T (Finset.mem_ssubsets.mpr hstrict)
      exact Bool.noConfusion (ht.symm.trans hf)
    exact ⟨p, l, hI, heq.symm⟩
  · rintro ⟨p, l, hI, rfl⟩
    refine ⟨(accepts _).mpr ⟨p, l, hI, by simp, by simp⟩, ?_⟩
    intro T hT
    by_contra hnot
    have htrue : circuitFun (P + L) C (setInput T) = true := by simpa using hnot
    obtain ⟨p', l', _, hp', hl'⟩ := (accepts T).mp htrue
    have hsub : {Fin.castAdd L p', Fin.natAdd P l'} ⊆ T := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hp', hl'⟩
    have htwo : 2 ≤ T.card := by
      simpa [separated] using Finset.card_le_card hsub
    have hlt := Finset.card_lt_card (Finset.mem_ssubsets.mp hT)
    have hcard : ({Fin.castAdd L p, Fin.natAdd P l} : Finset (Fin (P + L))).card = 2 := by
      simp [separated]
    omega

lemma lines_through (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

lemma incidence_no_four_cycle {N : ℕ} (I : Fin N → Fin N → Prop)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l') := by
  intro p p' l l' hp hl
  rintro ⟨hpl, hpl', hp'l, hp'l'⟩
  exact hl ((hu p p' hp).unique ⟨hpl, hp'l⟩ ⟨hpl', hp'l'⟩)

lemma lines_meet_at_most_once {N : ℕ} (I : Fin N → Fin N → Prop)
    [DecidableRel I]
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (l m : Fin N) (hlm : l ≠ m) :
    (Finset.univ.filter (fun p => I p l ∧ I p m)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_contra hab
  exact hlm ((hu a b hab).unique ⟨ha.1, hb.1⟩ ⟨ha.2, hb.2⟩)

lemma each_line_has_point {q N : ℕ} (I : Fin N → Fin N → Prop)
    [DecidableRel I]
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (l : Fin N) : ∃ p : Fin N, I p l := by
  have hpos : 0 < (Finset.univ.filter (fun p => I p l)).card := by rw [hl]; omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  exact ⟨p, (Finset.mem_filter.mp hp).2⟩

lemma each_point_has_line {q N : ℕ} (I : Fin N → Fin N → Prop)
    [DecidableRel I] (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p : Fin N) : ∃ l : Fin N, I p l := by
  have hpos : 0 < (Finset.univ.filter (fun l => I p l)).card := by
    rw [lines_through q N I hq hN hl hu p]
    omega
  obtain ⟨l, hl⟩ := Finset.card_pos.mp hpos
  exact ⟨l, (Finset.mem_filter.mp hl).2⟩

lemma regular_incidence_matching {N k : ℕ} (I : Fin N → Fin N → Prop)
    [DecidableRel I] (hk : 0 < k)
    (hrow : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = k)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = k) :
    ∃ σ : Equiv.Perm (Fin N), ∀ p : Fin N, I p (σ p) := by
  classical
  let S (p : Fin N) : Finset (Fin N) := Finset.univ.filter (fun l => I p l)
  have hall : ∀ B : Finset (Fin N), B.card ≤ (B.biUnion S).card := by
    intro B
    let U := B.biUnion S
    have h1 : ∑ p ∈ B, (U ∩ S p).card = B.card * k := by
      rw [Finset.sum_congr rfl (fun p hp => by
        rw [Finset.inter_eq_right.mpr (Finset.subset_biUnion_of_mem S hp), hrow]),
        Finset.sum_const, smul_eq_mul]
    have h2 : ∑ p ∈ B, (U ∩ S p).card =
        ∑ l ∈ U, (B.filter (fun p => l ∈ S p)).card := by
      simp_rw [← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    have h3 : ∑ l ∈ U, (B.filter (fun p => l ∈ S p)).card ≤ U.card * k := by
      have hbound (l : Fin N) : (B.filter (fun p => l ∈ S p)).card ≤ k := by
        have he : B.filter (fun p => l ∈ S p) = B.filter (fun p => I p l) := by
          ext p
          simp [S]
        rw [he, ← hcol l]
        exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ B))
      have hsum := Finset.sum_le_card_nsmul U
        (fun l => (B.filter (fun p => l ∈ S p)).card) k (fun l _ => hbound l)
      simpa [smul_eq_mul] using hsum
    have h4 : B.card * k ≤ U.card * k := by omega
    exact Nat.le_of_mul_le_mul_right h4 hk
  obtain ⟨f, hinj, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective S).mp hall
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), ?_⟩
  intro p
  exact (Finset.mem_filter.mp (hf p)).2

lemma incidence_card {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] :
    (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card =
      ∑ p : Fin N, (Finset.univ.filter (fun l => I p l)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_product Finset.univ Finset.univ
    (fun e : Fin N × Fin N => if I e.1 e.2 then 1 else 0)

namespace PlaneUpper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma ofFn_getD {α : Type} {n : ℕ} (x : Fin n → α) (dflt : α) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i dflt = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

def F {α : Type} (step : Gate → List α → α) (gs : List Gate) (d : List α) : List α :=
  gs.foldl (fun d g => d ++ [step g d]) d

lemma F_append {α : Type} (step : Gate → List α → α) (a b : List Gate) (d : List α) :
    F step (a ++ b) d = F step b (F step a d) := by
  simp [F, List.foldl_append]

def chain : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | acc, w, i :: is => ⟨GateOp.or, [acc, i]⟩ :: chain w (w + 1) is

def cfin : ℕ → ℕ → List ℕ → ℕ
  | acc, _, [] => acc
  | _, w, _ :: is => cfin w (w + 1) is

lemma chain_len : ∀ (ins : List ℕ) (acc w : ℕ), (chain acc w ins).length = ins.length
  | [], _, _ => rfl
  | _ :: is, _, w => by simp [chain, chain_len is]

lemma chain_or : ∀ (ins : List ℕ) (acc w : ℕ), ∀ g ∈ chain acc w ins,
    g.op = GateOp.or ∧ g.inputs.length = 2
  | [], _, _ => by simp [chain]
  | i :: is, acc, w => by
    intro g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨rfl, rfl⟩
    · exact chain_or is w (w + 1) g hg

lemma chain_spec {α : Type} (step : Gate → List α → α) (dflt : α) (op : α → α → α)
    (hstep : ∀ (a b : ℕ) (d : List α),
      step ⟨GateOp.or, [a, b]⟩ d = op (d.getD a dflt) (d.getD b dflt))
    (ins : List ℕ) : ∀ (acc w : ℕ) (d : List α), d.length = w → acc < w → (∀ i ∈ ins, i < w) →
      (F step (chain acc w ins) d).length = w + ins.length ∧
      (∀ i < w, (F step (chain acc w ins) d).getD i dflt = d.getD i dflt) ∧
      (F step (chain acc w ins) d).getD (cfin acc w ins) dflt =
        ins.foldl (fun v i => op v (d.getD i dflt)) (d.getD acc dflt) ∧
      cfin acc w ins < w + ins.length := by
  induction ins with
  | nil =>
    intro acc w d hw hacc _
    refine ⟨by simp [chain, F, hw], fun i _ => by simp [chain, F], by simp [chain, F, cfin],
      by simpa [cfin] using hacc⟩
  | cons i is ih =>
    intro acc w d hw hacc hins
    have hi : i < w := hins i (by simp)
    obtain ⟨h1, h2, h3, h4⟩ := ih w (w + 1) (d ++ [step ⟨GateOp.or, [acc, i]⟩ d])
      (by simp [hw]) (by omega) (fun k hk => by have := hins k (by simp [hk]); omega)
    have hF : F step (chain acc w (i :: is)) d =
        F step (chain w (w + 1) is) (d ++ [step ⟨GateOp.or, [acc, i]⟩ d]) := by
      simp [F, chain]
    have hpre : ∀ k < w, (d ++ [step ⟨GateOp.or, [acc, i]⟩ d]).getD k dflt = d.getD k dflt :=
      fun k hk => List.getD_append _ _ _ _ (by omega)
    have hd : (d ++ [step ⟨GateOp.or, [acc, i]⟩ d]).getD w dflt =
        op (d.getD acc dflt) (d.getD i dflt) := by
      rw [List.getD_append_right _ _ _ _ (by omega), hstep]
      simp [hw]
    have hc : cfin acc w (i :: is) = cfin w (w + 1) is := by simp [cfin]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hF, h1]; simp only [List.length_cons]; omega
    · intro k hk; rw [hF, h2 k (by omega), hpre k hk]
    · rw [hF, hc, h3, hd, List.foldl_cons]
      exact List.foldl_ext _ _ _ (fun v k hk => by rw [hpre k (hins k (by simp [hk]))])
    · rw [hc]; simp only [List.length_cons]; omega

def wstep (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

lemma wstep_or (a b : ℕ) (d : List Bool) :
    wstep ⟨GateOp.or, [a, b]⟩ d = (d.getD a false || d.getD b false) := by
  simp [wstep, GateOp.eval]

lemma wstep_and (a b : ℕ) (d : List Bool) :
    wstep ⟨GateOp.and, [a, b]⟩ d = (d.getD a false && d.getD b false) := by
  simp [wstep, GateOp.eval]

lemma foldl_or (f : ℕ → Bool) : ∀ (l : List ℕ) (a : Bool),
    l.foldl (fun v i => v || f i) a = (a || l.any f)
  | [], a => by simp
  | i :: is, a => by simp [foldl_or f is, Bool.or_assoc]

lemma F_one {α : Type} (step : Gate → List α → α) (g : Gate) (d : List α) :
    F step [g] d = d ++ [step g d] := rfl

lemma F_len {α : Type} (step : Gate → List α → α) : ∀ (gs : List Gate) (d : List α),
    (F step gs d).length = d.length + gs.length
  | [], d => by simp [F]
  | g :: gs, d => by
    have h := F_len step gs (d ++ [step g d])
    have e : F step (g :: gs) d = F step gs (d ++ [step g d]) := rfl
    rw [e, h]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma F_pre {α : Type} (step : Gate → List α → α) (dflt : α) :
    ∀ (gs : List Gate) (d : List α) (i : ℕ), i < d.length →
      (F step gs d).getD i dflt = d.getD i dflt
  | [], _, _, _ => rfl
  | g :: gs, d, i, hi => by
    have e : F step (g :: gs) d = F step gs (d ++ [step g d]) := rfl
    rw [e, F_pre step dflt gs (d ++ [step g d]) i (by rw [List.length_append]; omega)]
    exact List.getD_append _ _ _ _ hi

def blk (c h : ℕ) (t : List ℕ) (w : ℕ) : List Gate :=
  chain h w t ++ [⟨GateOp.and, [cfin h w t, c]⟩]

lemma blk_len (c h : ℕ) (t : List ℕ) (w : ℕ) : (blk c h t w).length = t.length + 1 := by
  simp [blk, chain_len]

lemma blk_shape (c h : ℕ) (t : List ℕ) (w : ℕ) :
    ∀ g ∈ blk c h t w, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  unfold blk at hg
  rw [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · obtain ⟨a, b⟩ := chain_or _ _ _ g hg
    exact ⟨Or.inr a, b⟩
  · exact ⟨Or.inl rfl, rfl⟩

lemma blk_val (c h : ℕ) (t : List ℕ) (w : ℕ) (d : List Bool)
    (hw : d.length = w) (h1 : h < w) (h2 : ∀ i ∈ t, i < w) (h3 : c < w) :
    (F wstep (blk c h t w) d).getD (w + t.length) false =
      ((d.getD h false || t.any fun i => d.getD i false) && d.getD c false) := by
  obtain ⟨c1, c2, c3, c4⟩ :=
    chain_spec wstep false (fun u v => u || v) wstep_or t h w d hw h1 h2
  unfold blk
  rw [F_append, F_one, List.getD_append_right _ _ _ _ (le_of_eq c1), c1, Nat.sub_self,
    List.getD_cons_zero, wstep_and, c3, c2 _ h3, foldl_or (fun i => d.getD i false)]

lemma blk_iff (n c h : ℕ) (t : List ℕ) (w : ℕ) (d x : List Bool)
    (hw : d.length = w) (hpre : ∀ i < n, d.getD i false = x.getD i false)
    (h1 : h < n) (h2 : ∀ i ∈ t, i < n) (hl : c < n) (hNw : n ≤ w) :
    (F wstep (blk c h t w) d).getD (w + t.length) false = true ↔
      (x.getD c false = true ∧ ∃ i ∈ h :: t, x.getD i false = true) := by
  rw [blk_val c h t w d hw (by omega) (fun i hi => by have := h2 i hi; omega) (by omega),
    Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, hpre h (by omega),
    hpre c (by omega)]
  constructor
  · rintro ⟨hh | ⟨i, hi, hh⟩, hy⟩
    · exact ⟨hy, h, by simp, hh⟩
    · exact ⟨hy, i, by simp [hi], by rw [← hpre i (h2 i hi)]; exact hh⟩
  · rintro ⟨hy, i, hi, hh⟩
    refine ⟨?_, hy⟩
    rcases List.mem_cons.mp hi with e | hi2
    · rw [e] at hh; exact Or.inl hh
    · exact Or.inr ⟨i, hi2, by rw [hpre i (h2 i hi2)]; exact hh⟩

def G (n : ℕ) (s0 : ℕ × ℕ × List ℕ) : List (ℕ × ℕ × List ℕ) → List Gate
  | [] => blk s0.1 s0.2.1 s0.2.2 n
  | s :: r => G n s0 r ++ blk s.1 s.2.1 s.2.2 (n + (G n s0 r).length) ++
      [⟨GateOp.or, [n + (G n s0 r).length - 1, n + (G n s0 r).length + s.2.2.length]⟩]

lemma G_pos (n : ℕ) (s0 : ℕ × ℕ × List ℕ) : ∀ r, 0 < (G n s0 r).length
  | [] => by simp [G, blk_len]
  | s :: r => by simp [G]

lemma G_len (n : ℕ) (s0 : ℕ × ℕ × List ℕ) : ∀ r : List (ℕ × ℕ × List ℕ),
    (G n s0 r).length + 1 = (s0.2.2.length + 2) + (r.map fun s => s.2.2.length + 2).sum
  | [] => by simp [G, blk_len]
  | s :: r => by
    have ih := G_len n s0 r
    simp only [G, List.length_append, blk_len, List.length_cons, List.length_nil,
      List.map_cons, List.sum_cons]
    omega

lemma G_shape (n : ℕ) (s0 : ℕ × ℕ × List ℕ) : ∀ r : List (ℕ × ℕ × List ℕ),
    ∀ g ∈ G n s0 r, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  | [] => by
    intro g hg
    simp only [G] at hg
    exact blk_shape _ _ _ _ g hg
  | s :: r => by
    intro g hg
    simp only [G, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact G_shape n s0 r g hg
    · exact blk_shape _ _ _ _ g hg
    · exact ⟨Or.inr rfl, rfl⟩

lemma G_val (n : ℕ) (s0 : ℕ × ℕ × List ℕ) (x : List Bool) (hx : x.length = n)
    (h0 : s0.1 < n ∧ ∀ i ∈ s0.2.1 :: s0.2.2, i < n) :
    ∀ r : List (ℕ × ℕ × List ℕ), (∀ s ∈ r, s.1 < n ∧ ∀ i ∈ s.2.1 :: s.2.2, i < n) →
      ((F wstep (G n s0 r) x).getD (n + (G n s0 r).length - 1) false = true ↔
        ∃ s ∈ s0 :: r, x.getD s.1 false = true ∧ ∃ i ∈ s.2.1 :: s.2.2, x.getD i false = true)
  | [], _ => by
    have e : n + (G n s0 []).length - 1 = n + s0.2.2.length := by
      simp only [G, blk_len]
      omega
    rw [e]
    simp only [G]
    rw [blk_iff n s0.1 s0.2.1 s0.2.2 n x x hx (fun i _ => rfl) (h0.2 _ (by simp))
      (fun i hi => h0.2 i (by simp [hi])) h0.1 (le_refl _)]
    constructor
    · intro a
      exact ⟨s0, by simp, a⟩
    · rintro ⟨s, hs, a⟩
      rw [List.mem_singleton.mp hs] at a
      exact a
  | s :: r, hr => by
    have ih := G_val n s0 x hx h0 r (fun s' hs' => hr s' (by simp [hs']))
    have hs := hr s (by simp)
    have hL : (F wstep (G n s0 r) x).length = n + (G n s0 r).length := by
      rw [F_len, hx]
    have hpre : ∀ i < n, (F wstep (G n s0 r) x).getD i false = x.getD i false :=
      fun i hi => F_pre wstep false _ _ i (by omega)
    have hb := blk_iff n s.1 s.2.1 s.2.2 (n + (G n s0 r).length)
      (F wstep (G n s0 r) x) x hL hpre (hs.2 _ (by simp)) (fun i hi => hs.2 i (by simp [hi]))
      hs.1 (by omega)
    have hL2 : (F wstep (G n s0 r ++ blk s.1 s.2.1 s.2.2 (n + (G n s0 r).length))
        x).length = n + (G n s0 r).length + s.2.2.length + 1 := by
      rw [F_len, List.length_append, blk_len, hx]
      omega
    have hpos := G_pos n s0 r
    have e : n + (G n s0 (s :: r)).length - 1 =
        n + (G n s0 r).length + s.2.2.length + 1 := by
      simp only [G, List.length_append, blk_len, List.length_cons, List.length_nil]
      omega
    rw [e]
    simp only [G]
    rw [F_append, F_one, List.getD_append_right _ _ _ _ (le_of_eq hL2), hL2, Nat.sub_self,
      List.getD_cons_zero, wstep_or, Bool.or_eq_true]
    rw [F_append, F_pre wstep false _ _ (n + (G n s0 r).length - 1)
      (by rw [hL]; omega), ih, hb]
    constructor
    · rintro (⟨s', hs', a⟩ | a)
      · refine ⟨s', ?_, a⟩
        simp only [List.mem_cons] at hs' ⊢
        tauto
      · exact ⟨s, by simp, a⟩
    · rintro ⟨s', hs', a⟩
      simp only [List.mem_cons] at hs'
      rcases hs' with h | h | h
      · exact Or.inl ⟨s', by simp [h], a⟩
      · rw [h] at a
        exact Or.inr a
      · exact Or.inl ⟨s', by simp [h], a⟩

def RB (w : ℕ) (b : List Gate) : Prop :=
  ∀ j < b.length, ∀ i ∈ (b.getD j ⟨GateOp.or, []⟩).inputs, i < w + j

lemma RB_app (w : ℕ) (a b : List Gate) (ha : RB w a) (hb : RB (w + a.length) b) :
    RB w (a ++ b) := by
  intro j hj i hi
  rcases Nat.lt_or_ge j a.length with h | h
  · rw [List.getD_append _ _ _ _ h] at hi
    exact ha j h i hi
  · rw [List.getD_append_right _ _ _ _ h] at hi
    have hj2 : j - a.length < b.length := by
      rw [List.length_append] at hj; omega
    have := hb (j - a.length) hj2 i hi
    omega

lemma RB_two (w : ℕ) (op : GateOp) (a b : ℕ) (ha : a < w) (hb : b < w) :
    RB w [⟨op, [a, b]⟩] := by
  intro j hj i hi
  have hj0 : j = 0 := by simpa using hj
  subst hj0
  have hi' : i ∈ [a, b] := hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with hi' | hi' <;> omega

lemma cfin_lt : ∀ (ins : List ℕ) (acc w : ℕ), acc < w → cfin acc w ins < w + ins.length
  | [], acc, w, h => by simpa [cfin] using h
  | i :: is, acc, w, h => by
    have := cfin_lt is w (w + 1) (by omega)
    simp only [cfin, List.length_cons]
    omega

lemma RB_chain : ∀ (ins : List ℕ) (acc w : ℕ), acc < w → (∀ i ∈ ins, i < w) →
    RB w (chain acc w ins)
  | [], _, _, _, _ => by
    intro j hj
    simp [chain] at hj
  | i :: is, acc, w, hacc, hins => by
    have e : chain acc w (i :: is) = [⟨GateOp.or, [acc, i]⟩] ++ chain w (w + 1) is := rfl
    rw [e]
    apply RB_app
    · exact RB_two w GateOp.or acc i hacc (hins i (by simp))
    · exact RB_chain is w (w + 1) (by omega)
        (fun k hk => by have := hins k (by simp [hk]); omega)

lemma RB_blk (c h : ℕ) (t : List ℕ) (w : ℕ) (h1 : h < w) (h2 : ∀ i ∈ t, i < w)
    (h3 : c < w) : RB w (blk c h t w) := by
  unfold blk
  apply RB_app _ _ _ (RB_chain t h w h1 h2)
  rw [chain_len]
  exact RB_two _ GateOp.and _ _ (cfin_lt t h w h1) (by omega)

lemma RB_G (n : ℕ) (s0 : ℕ × ℕ × List ℕ) (h0 : s0.1 < n ∧ ∀ i ∈ s0.2.1 :: s0.2.2, i < n) :
    ∀ r : List (ℕ × ℕ × List ℕ), (∀ s ∈ r, s.1 < n ∧ ∀ i ∈ s.2.1 :: s.2.2, i < n) →
      RB n (G n s0 r)
  | [], _ => by
    simp only [G]
    exact RB_blk _ _ _ _ (h0.2 _ (by simp)) (fun i hi => h0.2 i (by simp [hi])) h0.1
  | s :: r, hr => by
    have ih := RB_G n s0 h0 r (fun s' hs' => hr s' (by simp [hs']))
    have hs := hr s (by simp)
    have hpos := G_pos n s0 r
    simp only [G]
    apply RB_app
    · apply RB_app _ _ _ ih
      exact RB_blk _ _ _ _ (by have := hs.2 s.2.1 (by simp); omega)
        (fun i hi => by have := hs.2 i (by simp [hi]); omega) (by have := hs.1; omega)
    · rw [List.length_append, blk_len]
      exact RB_two _ GateOp.or _ _ (by omega) (by omega)

def rstep (S : List ℕ) (k : ℕ) (g : Gate) (R : List (List (List ℕ))) : List (List ℕ) :=
  match g.op with
  | GateOp.or =>
    (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

lemma rv_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = F (rstep S k) C.gates ((List.range n).map (leafVectors S k)) := rfl

lemma mem_insertNew (A : List (List ℕ)) (v x : List ℕ) :
    x ∈ insertNew A v ↔ x ∈ A ∨ x = v := by
  unfold insertNew
  split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (h1 | h1)
      · exact h1
      · rw [h1]; exact h
  · simp

lemma mem_foldl_insertNew (x : List ℕ) : ∀ (B A : List (List ℕ)),
    x ∈ B.foldl insertNew A ↔ x ∈ A ∨ x ∈ B
  | [], A => by simp
  | b :: B, A => by
    rw [List.foldl_cons, mem_foldl_insertNew x B, mem_insertNew, List.mem_cons]
    tauto

def orv (A B : List (List ℕ)) : List (List ℕ) := B.foldl insertNew (A.foldl insertNew [])

lemma mem_orv (x : List ℕ) (A B : List (List ℕ)) : x ∈ orv A B ↔ x ∈ A ∨ x ∈ B := by
  unfold orv
  rw [mem_foldl_insertNew, mem_foldl_insertNew]
  simp

lemma rstep_or (S : List ℕ) (k a b : ℕ) (R : List (List (List ℕ))) :
    rstep S k ⟨GateOp.or, [a, b]⟩ R = orv (R.getD a []) (R.getD b []) := rfl

lemma mem_andStep (k : ℕ) (x : List ℕ) (A B : List (List ℕ)) :
    x ∈ andStep k A B ↔ ∃ u ∈ A, ∃ v ∈ B, capAdd k u v = x := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp [List.mem_flatMap]

lemma rstep_and (S : List ℕ) (k a b : ℕ) (R : List (List (List ℕ))) :
    rstep S k ⟨GateOp.and, [a, b]⟩ R =
      andStep k (andStep k [S.map fun _ => 0] (R.getD a [])) (R.getD b []) := rfl

lemma foldl_orv (x : List ℕ) (g : ℕ → List (List ℕ)) : ∀ (l : List ℕ) (a : List (List ℕ)),
    (x ∈ a ∨ ∃ i ∈ l, x ∈ g i) → x ∈ l.foldl (fun v i => orv v (g i)) a
  | [], a, h => by
    rcases h with h | ⟨i, hi, _⟩
    · exact h
    · simp at hi
  | i :: is, a, h => by
    rw [List.foldl_cons]
    apply foldl_orv x g is
    rcases h with h | ⟨j, hj, hx⟩
    · exact Or.inl ((mem_orv _ _ _).mpr (Or.inl h))
    · rcases List.mem_cons.mp hj with e | hj2
      · rw [e] at hx
        exact Or.inl ((mem_orv _ _ _).mpr (Or.inr hx))
      · exact Or.inr ⟨j, hj2, hx⟩

lemma blk_rv (S : List ℕ) (k : ℕ) (c h : ℕ) (t : List ℕ) (w : ℕ)
    (d : List (List (List ℕ))) (hw : d.length = w) (h1 : h < w) (h2 : ∀ i ∈ t, i < w)
    (h3 : c < w) (i : ℕ) (hi : i ∈ h :: t) (u y : List ℕ) (hu : u ∈ d.getD i [])
    (hy : y ∈ d.getD c []) :
    capAdd k (capAdd k (S.map fun _ => 0) u) y ∈
      (F (rstep S k) (blk c h t w) d).getD (w + t.length) [] := by
  obtain ⟨c1, c2, c3, c4⟩ :=
    chain_spec (rstep S k) [] orv (rstep_or S k) t h w d hw h1 h2
  unfold blk
  rw [F_append, F_one, List.getD_append_right _ _ _ _ (le_of_eq c1), c1, Nat.sub_self,
    List.getD_cons_zero, rstep_and, c3, c2 _ h3, mem_andStep]
  refine ⟨_, ?_, y, hy, rfl⟩
  rw [mem_andStep]
  refine ⟨_, by simp, u, ?_, rfl⟩
  apply foldl_orv u (fun i => d.getD i [])
  rcases List.mem_cons.mp hi with e | hi2
  · rw [e] at hu
    exact Or.inl hu
  · exact Or.inr ⟨i, hi2, hu⟩

lemma G_rv (S : List ℕ) (k : ℕ) (n : ℕ) (s0 : ℕ × ℕ × List ℕ) (x : List (List (List ℕ)))
    (hx : x.length = n) (h0 : s0.1 < n ∧ ∀ i ∈ s0.2.1 :: s0.2.2, i < n) :
    ∀ r : List (ℕ × ℕ × List ℕ), (∀ s ∈ r, s.1 < n ∧ ∀ i ∈ s.2.1 :: s.2.2, i < n) →
      ∀ s ∈ s0 :: r, ∀ i ∈ s.2.1 :: s.2.2, ∀ u ∈ x.getD i [], ∀ y ∈ x.getD s.1 [],
        capAdd k (capAdd k (S.map fun _ => 0) u) y ∈
          (F (rstep S k) (G n s0 r) x).getD (n + (G n s0 r).length - 1) []
  | [], _ => by
    intro s hs i hi u hu y hy
    have hs2 := List.mem_singleton.mp hs
    rw [hs2] at hi hy
    have e : n + (G n s0 []).length - 1 = n + s0.2.2.length := by
      simp only [G, blk_len]
      omega
    rw [e]
    simp only [G]
    exact blk_rv S k s0.1 s0.2.1 s0.2.2 n x hx (h0.2 _ (by simp))
      (fun i hi => h0.2 i (by simp [hi])) h0.1 i hi u y hu hy
  | s :: r, hr => by
    intro s' hs' i hi u hu y hy
    have ih := G_rv S k n s0 x hx h0 r (fun s' hs' => hr s' (by simp [hs']))
    have hs := hr s (by simp)
    have hL : (F (rstep S k) (G n s0 r) x).length = n + (G n s0 r).length := by
      rw [F_len, hx]
    have hpre : ∀ i < n, (F (rstep S k) (G n s0 r) x).getD i [] = x.getD i [] :=
      fun i hi => F_pre (rstep S k) [] _ _ i (by omega)
    have hL2 : (F (rstep S k) (G n s0 r ++ blk s.1 s.2.1 s.2.2 (n + (G n s0 r).length))
        x).length = n + (G n s0 r).length + s.2.2.length + 1 := by
      rw [F_len, List.length_append, blk_len, hx]
      omega
    have hpos := G_pos n s0 r
    have e : n + (G n s0 (s :: r)).length - 1 =
        n + (G n s0 r).length + s.2.2.length + 1 := by
      simp only [G, List.length_append, blk_len, List.length_cons, List.length_nil]
      omega
    rw [e]
    simp only [G]
    rw [F_append, F_one, List.getD_append_right _ _ _ _ (le_of_eq hL2), hL2, Nat.sub_self,
      List.getD_cons_zero, rstep_or, mem_orv]
    rw [F_append, F_pre (rstep S k) [] _ _ (n + (G n s0 r).length - 1)
      (by rw [hL]; omega)]
    simp only [List.mem_cons] at hs'
    rcases hs' with h | h | h
    · exact Or.inl (ih s' (by simp [h]) i hi u hu y hy)
    · rw [h] at hi hy
      refine Or.inr (blk_rv S k s.1 s.2.1 s.2.2 (n + (G n s0 r).length) _ hL
        (by have := hs.2 s.2.1 (by simp); omega)
        (fun i hi => by have := hs.2 i (by simp [hi]); omega) (by have := hs.1; omega)
        i hi u y ?_ ?_)
      · rw [hpre i (hs.2 i hi)]
        exact hu
      · rw [hpre _ hs.1]
        exact hy
    · exact Or.inl (ih s' (by simp [h]) i hi u hu y hy)

lemma capAdd_map (k : ℕ) (f g : ℕ → ℕ) : ∀ S : List ℕ,
    capAdd k (S.map f) (S.map g) = S.map fun j => min (f j + g j) (k + 1)
  | [] => rfl
  | a :: S => by
    have ih := capAdd_map k f g S
    unfold capAdd at ih ⊢
    simp only [List.map_cons, List.zipWith_cons_cons, ih]

lemma read_ok (S : List ℕ) (k a b : ℕ) (hk : 1 ≤ k) (hab : a ≠ b) :
    ((capAdd k (capAdd k (S.map fun _ => 0)
        (S.map fun j => if j = a then min 1 (k + 1) else 0))
      (S.map fun j => if j = b then min 1 (k + 1) else 0)).all
        fun x => decide (x ≤ k)) = true := by
  rw [capAdd_map, capAdd_map, List.all_eq_true]
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  rw [decide_eq_true_eq]
  split_ifs with h1 h2 <;> omega

lemma leaf_getD (S : List ℕ) (k n i : ℕ) (hi : i < n) (hS : i ∈ S) :
    (S.map fun j => if j = i then min 1 (k + 1) else 0) ∈
      ((List.range n).map (leafVectors S k)).getD i [] := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [leafVectors, hS]

def pts {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) : List ℕ :=
  ((List.finRange N).filter fun p => decide (I p l)).map Fin.val

def star {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) : ℕ × ℕ × List ℕ :=
  (N + l.val, (pts I l).headD 0, (pts I l).tail)

lemma mem_pts {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) (i : ℕ) :
    i ∈ pts I l ↔ ∃ p : Fin N, I p l ∧ p.val = i := by
  simp [pts]

lemma pts_len {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) :
    (pts I l).length = (Finset.univ.filter (fun p => I p l)).card := by
  have e : (Finset.univ.filter (fun p => I p l)) =
      ((List.finRange N).filter fun p => decide (I p l)).toFinset := by
    ext p
    simp
  rw [e, List.toFinset_card_of_nodup ((List.nodup_finRange N).filter _)]
  simp [pts]

lemma hd_tl {α : Type} (d : α) : ∀ l : List α, l ≠ [] → l.headD d :: l.tail = l
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

lemma upper (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hN : 0 < N)
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ z2 : Fin (N + N) → Bool, circuitFun (N + N) D z2 =
        decide (∃ p4 l4 : Fin N, I p4 l4 ∧ z2 (Fin.castAdd N p4) = true ∧
          z2 (Fin.natAdd N l4) = true)) ∧
      IsReadK (N + N) D 1 ∧ D.size + 1 = N * (q + 2) := by
  have hall0 : (List.finRange N).map (star I) ≠ [] := by
    intro h
    have h2 := congrArg List.length h
    simp at h2
    omega
  have hall := hd_tl (0, 0, []) _ hall0
  generalize ((List.finRange N).map (star I)).headD (0, 0, []) = s0 at hall
  generalize ((List.finRange N).map (star I)).tail = r at hall
  have hmem : ∀ s ∈ s0 :: r, ∃ l : Fin N, s = star I l := by
    intro s hs
    rw [hall] at hs
    obtain ⟨l, _, hl⟩ := List.mem_map.mp hs
    exact ⟨l, hl.symm⟩
  have hlen : ∀ l : Fin N, (pts I l).length = q + 1 := fun l => by rw [pts_len, hc]
  have hcons : ∀ l : Fin N, (star I l).2.1 :: (star I l).2.2 = pts I l := by
    intro l
    apply hd_tl
    intro h
    have := hlen l
    rw [h] at this
    simp at this
  have hbd : ∀ s ∈ s0 :: r, s.1 < N + N ∧ ∀ i ∈ s.2.1 :: s.2.2, i < N + N := by
    intro s hs
    obtain ⟨l, rfl⟩ := hmem s hs
    refine ⟨?_, ?_⟩
    · show N + l.val < N + N
      have := l.isLt
      omega
    · intro i hi
      rw [hcons l] at hi
      obtain ⟨p, _, rfl⟩ := (mem_pts I l i).mp hi
      have := p.isLt
      omega
  have hb0 := hbd s0 (by simp)
  have hbr : ∀ s ∈ r, s.1 < N + N ∧ ∀ i ∈ s.2.1 :: s.2.2, i < N + N :=
    fun s hs => hbd s (by simp [hs])
  have hzl : ∀ (z : Fin (N + N) → Bool) (l : Fin N),
      (List.ofFn z).getD (N + l.val) false = z (Fin.natAdd N l) :=
    fun z l => ofFn_getD z false (N + l.val) (by have := l.isLt; omega)
  have hzp : ∀ (z : Fin (N + N) → Bool) (p : Fin N),
      (List.ofFn z).getD p.val false = z (Fin.castAdd N p) :=
    fun z p => ofFn_getD z false p.val (by have := p.isLt; omega)
  have hval : ∀ z2 : Fin (N + N) → Bool,
      circuitFun (N + N) ⟨G (N + N) s0 r, N + N + (G (N + N) s0 r).length - 1⟩ z2 =
        decide (∃ p4 l4 : Fin N, I p4 l4 ∧ z2 (Fin.castAdd N p4) = true ∧
          z2 (Fin.natAdd N l4) = true) := by
    intro z
    have hv := G_val (N + N) s0 (List.ofFn z) (by simp) hb0 r hbr
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    refine Iff.trans hv ?_
    constructor
    · rintro ⟨s, hs, h1, i, hi, h2⟩
      obtain ⟨l, rfl⟩ := hmem s hs
      rw [hcons l] at hi
      obtain ⟨p, hp, rfl⟩ := (mem_pts I l i).mp hi
      refine ⟨p, l, hp, ?_, ?_⟩
      · rw [← hzp z p]
        exact h2
      · rw [← hzl z l]
        exact h1
    · rintro ⟨p, l, hp, h1, h2⟩
      refine ⟨star I l, ?_, ?_, p.val, ?_, ?_⟩
      · rw [hall]
        exact List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩
      · show (List.ofFn z).getD (N + l.val) false = true
        rw [hzl z l]
        exact h2
      · rw [hcons l]
        exact (mem_pts I l _).mpr ⟨p, hp, rfl⟩
      · rw [hzp z p]
        exact h1
  refine ⟨⟨G (N + N) s0 r, N + N + (G (N + N) s0 r).length - 1⟩, ?_, hval, ?_, ?_⟩
  · refine And.intro ?_ (And.intro ?_ ?_)
    · intro g hg
      exact (G_shape _ _ _ g hg).1
    · exact RB_G (N + N) s0 hb0 r hbr
    · intro g hg
      exact (G_shape _ _ _ g hg).2
  · intro S hS
    have ht := hS.1
    rw [hval, decide_eq_true_iff] at ht
    obtain ⟨p, l, hpl, h1, h2⟩ := ht
    have h1' : Fin.castAdd N p ∈ S := of_decide_eq_true h1
    have h2' : Fin.natAdd N l ∈ S := of_decide_eq_true h2
    have hpL : p.val ∈ setList S :=
      List.mem_map.mpr ⟨Fin.castAdd N p,
        List.mem_filter.mpr ⟨List.mem_finRange _, by simpa using h1'⟩, rfl⟩
    have hlL : N + l.val ∈ setList S :=
      List.mem_map.mpr ⟨Fin.natAdd N l,
        List.mem_filter.mpr ⟨List.mem_finRange _, by simpa using h2'⟩, rfl⟩
    have hpn : p.val < N + N := by have := p.isLt; omega
    have hln : N + l.val < N + N := by have := l.isLt; omega
    have hmemv := G_rv (setList S) 1 (N + N) s0
      ((List.range (N + N)).map (leafVectors (setList S) 1)) (by simp) hb0 r hbr
      (star I l) (by rw [hall]; exact List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩)
      p.val (by rw [hcons l]; exact (mem_pts I l _).mpr ⟨p, hpl, rfl⟩)
      _ (leaf_getD (setList S) 1 (N + N) p.val hpn hpL)
      _ (leaf_getD (setList S) 1 (N + N) (N + l.val) hln hlL)
    show ((readVectors ⟨G (N + N) s0 r, N + N + (G (N + N) s0 r).length - 1⟩ (N + N)
      (setList S) 1).getD (N + N + (G (N + N) s0 r).length - 1) []).any
        (fun v => v.all fun a => decide (a ≤ 1)) = true
    rw [rv_eq, List.any_eq_true]
    exact ⟨_, hmemv, read_ok (setList S) 1 p.val (N + l.val) (le_refl 1)
      (by have := p.isLt; omega)⟩
  · show (G (N + N) s0 r).length + 1 = N * (q + 2)
    rw [G_len]
    have hq2 : ∀ s ∈ s0 :: r, s.2.2.length + 2 = q + 2 := by
      intro s hs
      obtain ⟨l, rfl⟩ := hmem s hs
      have := hlen l
      show (pts I l).tail.length + 2 = q + 2
      rw [List.length_tail]
      omega
    have e : (s0.2.2.length + 2) + (r.map fun s => s.2.2.length + 2).sum =
        ((s0 :: r).map fun s => s.2.2.length + 2).sum := by
      simp only [List.map_cons, List.sum_cons]
    have e2 : ((s0 :: r).map fun s => s.2.2.length + 2) = List.replicate N (q + 2) := by
      apply List.eq_replicate_iff.mpr
      refine ⟨?_, ?_⟩
      · rw [List.length_map, hall]
        simp
      · intro b hb
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hb
        exact hq2 s hs
    rw [e, e2, List.sum_replicate, smul_eq_mul]

lemma from_exact_lower (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hN : 0 < N)
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hlower : N * (q + 2) ≤ C.size + 1) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ IsReadK (N + N) D 1 := by
  obtain ⟨D, hAO, hfun, hread, hsize⟩ := upper q N I hN hc
  exact ⟨D, hAO, hfun, by omega, hread⟩

end PlaneUpper

lemma regular_plane_dual {N k : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hk : 0 < k)
    (hrow : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = k)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = k)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (l m : Fin N) (hlm : l ≠ m) : ∃! p : Fin N, I p l ∧ I p m := by
  classical
  have hex : ∃ p : Fin N, I p l ∧ I p m := by
    by_contra h
    have hdisj : ∀ p : Fin N, ¬ (I p l ∧ I p m) := by
      intro p hp
      exact h ⟨p, hp⟩
    have hpos : 0 < (Finset.univ.filter (fun p => I p l)).card := by
      rw [hcol]
      exact hk
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
    have hpl : I p l := (Finset.mem_filter.mp hp).2
    have hpm : ¬ I p m := fun hpm => hdisj p ⟨hpl, hpm⟩
    choose! f hf using fun (r : Fin N) (hr : I r m) =>
      (hu p r (by intro he; exact hpm (he.symm ▸ hr))).exists
    let A : Finset (Fin N) := Finset.univ.filter (fun r => I r m)
    let B : Finset (Fin N) := (Finset.univ.filter (fun n => I p n)).erase l
    have hfA (r : Fin N) (hr : r ∈ A) : I p (f r) ∧ I r (f r) :=
      hf r (Finset.mem_filter.mp hr).2
    have hsub : A.image f ⊆ B := by
      intro n hn
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hn
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hfA r hr).1⟩⟩
      intro he
      exact hdisj r ⟨he ▸ (hfA r hr).2, (Finset.mem_filter.mp hr).2⟩
    have hinj : Set.InjOn f (A : Set (Fin N)) := by
      intro r hr s hs he
      by_contra hrs
      have hm : I r m ∧ I s m :=
        ⟨(Finset.mem_filter.mp hr).2, (Finset.mem_filter.mp hs).2⟩
      have hn : I r (f r) ∧ I s (f r) := ⟨(hfA r hr).2, he.symm ▸ (hfA s hs).2⟩
      have hfm : f r = m := (hu r s hrs).unique hn hm
      exact hpm (hfm ▸ (hfA r hr).1)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_iff.mpr hinj] at hcard
    have hA : A.card = k := hcol m
    have hB : B.card = k - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hrow]
    omega
  obtain ⟨p, hp⟩ := hex
  refine ⟨p, hp, ?_⟩
  intro r hr
  by_contra hrp
  exact hlm ((hu r p hrp).unique ⟨hr.1, hp.1⟩ ⟨hr.2, hp.2⟩)

lemma incidence_induced_hexagon {N : ℕ} (I : Fin N → Fin N → Prop)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hv : ∀ l l' : Fin N, l ≠ l' → ∃! p : Fin N, I p l ∧ I p l')
    (p r l m : Fin N) (hpl : I p l) (hrm : I r m)
    (hpm : ¬ I p m) (hrl : ¬ I r l) :
    ∃ s n : Fin N, p ≠ r ∧ p ≠ s ∧ r ≠ s ∧ l ≠ m ∧ l ≠ n ∧ m ≠ n ∧
      I p l ∧ I r m ∧ I p n ∧ I r n ∧ I s l ∧ I s m ∧ ¬ I s n := by
  have hpr : p ≠ r := by intro h; exact hrl (h ▸ hpl)
  have hlm : l ≠ m := by intro h; exact hpm (h ▸ hpl)
  obtain ⟨n, hn, _⟩ := hu p r hpr
  obtain ⟨s, hs, _⟩ := hv l m hlm
  have hps : p ≠ s := by intro h; exact hpm (h.symm ▸ hs.2)
  have hrs : r ≠ s := by intro h; exact hrl (h.symm ▸ hs.1)
  have hln : l ≠ n := by intro h; exact hrl (h.symm ▸ hn.2)
  have hmn : m ≠ n := by intro h; exact hpm (h.symm ▸ hn.1)
  refine ⟨s, n, hpr, hps, hrs, hlm, hln, hmn, hpl, hrm, hn.1, hn.2, hs.1, hs.2, ?_⟩
  intro hsn
  exact hln ((hu p s hps).unique ⟨hpl, hs.1⟩ ⟨hn.1, hsn⟩)

end PEqualNP.Outside.L_meta_2583
