import Mathlib
import PEqualNP.Defs

-- Adapted from the checked construction in L_meta_2393, lines 4174–4804.
-- Source revision: 851a7132.

namespace PEqualNP.Outside.L_meta_2583.StarUpper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

theorem ofFn_getD {α : Type} {n : ℕ} (x : Fin n → α) (dflt : α) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i dflt = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

def F {α : Type} (step : Gate → List α → α) (gs : List Gate) (d : List α) : List α :=
  gs.foldl (fun d g => d ++ [step g d]) d

theorem F_append {α : Type} (step : Gate → List α → α) (a b : List Gate) (d : List α) :
    F step (a ++ b) d = F step b (F step a d) := by
  simp [F, List.foldl_append]

def chain : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | acc, w, i :: is => ⟨GateOp.or, [acc, i]⟩ :: chain w (w + 1) is

def cfin : ℕ → ℕ → List ℕ → ℕ
  | acc, _, [] => acc
  | _, w, _ :: is => cfin w (w + 1) is

theorem chain_len : ∀ (ins : List ℕ) (acc w : ℕ), (chain acc w ins).length = ins.length
  | [], _, _ => rfl
  | _ :: is, _, w => by simp [chain, chain_len is]

theorem chain_or : ∀ (ins : List ℕ) (acc w : ℕ), ∀ g ∈ chain acc w ins,
    g.op = GateOp.or ∧ g.inputs.length = 2
  | [], _, _ => by simp [chain]
  | i :: is, acc, w => by
    intro g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨rfl, rfl⟩
    · exact chain_or is w (w + 1) g hg

theorem chain_spec {α : Type} (step : Gate → List α → α) (dflt : α) (op : α → α → α)
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

theorem wstep_or (a b : ℕ) (d : List Bool) :
    wstep ⟨GateOp.or, [a, b]⟩ d = (d.getD a false || d.getD b false) := by
  simp [wstep, GateOp.eval]

theorem wstep_and (a b : ℕ) (d : List Bool) :
    wstep ⟨GateOp.and, [a, b]⟩ d = (d.getD a false && d.getD b false) := by
  simp [wstep, GateOp.eval]

theorem foldl_or (f : ℕ → Bool) : ∀ (l : List ℕ) (a : Bool),
    l.foldl (fun v i => v || f i) a = (a || l.any f)
  | [], a => by simp
  | i :: is, a => by simp [foldl_or f is, Bool.or_assoc]

theorem F_one {α : Type} (step : Gate → List α → α) (g : Gate) (d : List α) :
    F step [g] d = d ++ [step g d] := rfl

theorem F_len {α : Type} (step : Gate → List α → α) : ∀ (gs : List Gate) (d : List α),
    (F step gs d).length = d.length + gs.length
  | [], d => by simp [F]
  | g :: gs, d => by
    have h := F_len step gs (d ++ [step g d])
    have e : F step (g :: gs) d = F step gs (d ++ [step g d]) := rfl
    rw [e, h]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem F_pre {α : Type} (step : Gate → List α → α) (dflt : α) :
    ∀ (gs : List Gate) (d : List α) (i : ℕ), i < d.length →
      (F step gs d).getD i dflt = d.getD i dflt
  | [], _, _, _ => rfl
  | g :: gs, d, i, hi => by
    have e : F step (g :: gs) d = F step gs (d ++ [step g d]) := rfl
    rw [e, F_pre step dflt gs (d ++ [step g d]) i (by rw [List.length_append]; omega)]
    exact List.getD_append _ _ _ _ hi

def blk (c h : ℕ) (t : List ℕ) (w : ℕ) : List Gate :=
  chain h w t ++ [⟨GateOp.and, [cfin h w t, c]⟩]

theorem blk_len (c h : ℕ) (t : List ℕ) (w : ℕ) : (blk c h t w).length = t.length + 1 := by
  simp [blk, chain_len]

theorem blk_shape (c h : ℕ) (t : List ℕ) (w : ℕ) :
    ∀ g ∈ blk c h t w, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  unfold blk at hg
  rw [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · obtain ⟨a, b⟩ := chain_or _ _ _ g hg
    exact ⟨Or.inr a, b⟩
  · exact ⟨Or.inl rfl, rfl⟩

theorem blk_val (c h : ℕ) (t : List ℕ) (w : ℕ) (d : List Bool)
    (hw : d.length = w) (h1 : h < w) (h2 : ∀ i ∈ t, i < w) (h3 : c < w) :
    (F wstep (blk c h t w) d).getD (w + t.length) false =
      ((d.getD h false || t.any fun i => d.getD i false) && d.getD c false) := by
  obtain ⟨c1, c2, c3, c4⟩ :=
    chain_spec wstep false (fun u v => u || v) wstep_or t h w d hw h1 h2
  unfold blk
  rw [F_append, F_one, List.getD_append_right _ _ _ _ (le_of_eq c1), c1, Nat.sub_self,
    List.getD_cons_zero, wstep_and, c3, c2 _ h3, foldl_or (fun i => d.getD i false)]

theorem blk_iff (n c h : ℕ) (t : List ℕ) (w : ℕ) (d x : List Bool)
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

theorem G_pos (n : ℕ) (s0 : ℕ × ℕ × List ℕ) : ∀ r, 0 < (G n s0 r).length
  | [] => by simp [G, blk_len]
  | s :: r => by simp [G]

theorem G_len (n : ℕ) (s0 : ℕ × ℕ × List ℕ) : ∀ r : List (ℕ × ℕ × List ℕ),
    (G n s0 r).length + 1 = (s0.2.2.length + 2) + (r.map fun s => s.2.2.length + 2).sum
  | [] => by simp [G, blk_len]
  | s :: r => by
    have ih := G_len n s0 r
    simp only [G, List.length_append, blk_len, List.length_cons, List.length_nil,
      List.map_cons, List.sum_cons]
    omega

theorem G_shape (n : ℕ) (s0 : ℕ × ℕ × List ℕ) : ∀ r : List (ℕ × ℕ × List ℕ),
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

theorem G_val (n : ℕ) (s0 : ℕ × ℕ × List ℕ) (x : List Bool) (hx : x.length = n)
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

theorem RB_app (w : ℕ) (a b : List Gate) (ha : RB w a) (hb : RB (w + a.length) b) :
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

theorem RB_two (w : ℕ) (op : GateOp) (a b : ℕ) (ha : a < w) (hb : b < w) :
    RB w [⟨op, [a, b]⟩] := by
  intro j hj i hi
  have hj0 : j = 0 := by simpa using hj
  subst hj0
  have hi' : i ∈ [a, b] := hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with hi' | hi' <;> omega

theorem cfin_lt : ∀ (ins : List ℕ) (acc w : ℕ), acc < w → cfin acc w ins < w + ins.length
  | [], acc, w, h => by simpa [cfin] using h
  | i :: is, acc, w, h => by
    have := cfin_lt is w (w + 1) (by omega)
    simp only [cfin, List.length_cons]
    omega

theorem RB_chain : ∀ (ins : List ℕ) (acc w : ℕ), acc < w → (∀ i ∈ ins, i < w) →
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

theorem RB_blk (c h : ℕ) (t : List ℕ) (w : ℕ) (h1 : h < w) (h2 : ∀ i ∈ t, i < w)
    (h3 : c < w) : RB w (blk c h t w) := by
  unfold blk
  apply RB_app _ _ _ (RB_chain t h w h1 h2)
  rw [chain_len]
  exact RB_two _ GateOp.and _ _ (cfin_lt t h w h1) (by omega)

theorem RB_G (n : ℕ) (s0 : ℕ × ℕ × List ℕ) (h0 : s0.1 < n ∧ ∀ i ∈ s0.2.1 :: s0.2.2, i < n) :
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

theorem rv_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = F (rstep S k) C.gates ((List.range n).map (leafVectors S k)) := rfl

theorem mem_insertNew (A : List (List ℕ)) (v x : List ℕ) :
    x ∈ insertNew A v ↔ x ∈ A ∨ x = v := by
  unfold insertNew
  split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (h1 | h1)
      · exact h1
      · rw [h1]; exact h
  · simp

theorem mem_foldl_insertNew (x : List ℕ) : ∀ (B A : List (List ℕ)),
    x ∈ B.foldl insertNew A ↔ x ∈ A ∨ x ∈ B
  | [], A => by simp
  | b :: B, A => by
    rw [List.foldl_cons, mem_foldl_insertNew x B, mem_insertNew, List.mem_cons]
    tauto

def orv (A B : List (List ℕ)) : List (List ℕ) := B.foldl insertNew (A.foldl insertNew [])

theorem mem_orv (x : List ℕ) (A B : List (List ℕ)) : x ∈ orv A B ↔ x ∈ A ∨ x ∈ B := by
  unfold orv
  rw [mem_foldl_insertNew, mem_foldl_insertNew]
  simp

theorem rstep_or (S : List ℕ) (k a b : ℕ) (R : List (List (List ℕ))) :
    rstep S k ⟨GateOp.or, [a, b]⟩ R = orv (R.getD a []) (R.getD b []) := rfl

theorem mem_andStep (k : ℕ) (x : List ℕ) (A B : List (List ℕ)) :
    x ∈ andStep k A B ↔ ∃ u ∈ A, ∃ v ∈ B, capAdd k u v = x := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp [List.mem_flatMap]

theorem rstep_and (S : List ℕ) (k a b : ℕ) (R : List (List (List ℕ))) :
    rstep S k ⟨GateOp.and, [a, b]⟩ R =
      andStep k (andStep k [S.map fun _ => 0] (R.getD a [])) (R.getD b []) := rfl

theorem foldl_orv (x : List ℕ) (g : ℕ → List (List ℕ)) : ∀ (l : List ℕ) (a : List (List ℕ)),
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

theorem blk_rv (S : List ℕ) (k : ℕ) (c h : ℕ) (t : List ℕ) (w : ℕ)
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

theorem G_rv (S : List ℕ) (k : ℕ) (n : ℕ) (s0 : ℕ × ℕ × List ℕ) (x : List (List (List ℕ)))
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

theorem capAdd_map (k : ℕ) (f g : ℕ → ℕ) : ∀ S : List ℕ,
    capAdd k (S.map f) (S.map g) = S.map fun j => min (f j + g j) (k + 1)
  | [] => rfl
  | a :: S => by
    have ih := capAdd_map k f g S
    unfold capAdd at ih ⊢
    simp only [List.map_cons, List.zipWith_cons_cons, ih]

theorem read_ok (S : List ℕ) (k a b : ℕ) (hk : 1 ≤ k) (hab : a ≠ b) :
    ((capAdd k (capAdd k (S.map fun _ => 0)
        (S.map fun j => if j = a then min 1 (k + 1) else 0))
      (S.map fun j => if j = b then min 1 (k + 1) else 0)).all
        fun x => decide (x ≤ k)) = true := by
  rw [capAdd_map, capAdd_map, List.all_eq_true]
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  rw [decide_eq_true_eq]
  split_ifs with h1 h2 <;> omega

theorem leaf_getD (S : List ℕ) (k n i : ℕ) (hi : i < n) (hS : i ∈ S) :
    (S.map fun j => if j = i then min 1 (k + 1) else 0) ∈
      ((List.range n).map (leafVectors S k)).getD i [] := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [leafVectors, hS]

def pts {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) : List ℕ :=
  ((List.finRange N).filter fun p => decide (I p l)).map Fin.val

def star {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) : ℕ × ℕ × List ℕ :=
  (N + l.val, (pts I l).headD 0, (pts I l).tail)

theorem mem_pts {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) (i : ℕ) :
    i ∈ pts I l ↔ ∃ p : Fin N, I p l ∧ p.val = i := by
  simp [pts]

theorem pts_len {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) :
    (pts I l).length = (Finset.univ.filter (fun p => I p l)).card := by
  have e : (Finset.univ.filter (fun p => I p l)) =
      ((List.finRange N).filter fun p => decide (I p l)).toFinset := by
    ext p
    simp
  rw [e, List.toFinset_card_of_nodup ((List.nodup_finRange N).filter _)]
  simp [pts]

theorem hd_tl {α : Type} (d : α) : ∀ l : List α, l ≠ [] → l.headD d :: l.tail = l
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

theorem upper (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hN : 0 < N)
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

lemma no_larger_of_size (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hN : 0 < N)
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hsize : N * (q + 2) ≤ C.size + 1) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true)) ∧
      D.size ≤ C.size ∧ IsReadK (N + N) D 1 := by
  obtain ⟨D, hD, hfun, hread, hcount⟩ := upper q N I hN hc
  exact ⟨D, hD, hfun, by omega, hread⟩

lemma order_card_pos (q N : ℕ) (_hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1) :
    0 < N := by
  omega

lemma step_of_lower_bound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → N * (q + 2) ≤ C.size + 1 → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  intro q N I inst C hq hN hlines huniq hAO hfun hsize
  exact no_larger_of_size q N I C (order_card_pos q N hq hN) hlines hsize

end PEqualNP.Outside.L_meta_2583.StarUpper
