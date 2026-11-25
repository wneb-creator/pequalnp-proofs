import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.StarCover

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem read {N : ℕ} (x : Fin N → Bool) (i : Fin N) : (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD]

def part (w : List Bool) (v : ℕ) (rest : List ℕ) (i : ℕ) : Bool :=
  w.getD v false || (rest.take i).any fun r => w.getD r false

def acc (w : List Bool) (v : ℕ) (rest : List ℕ) (k : ℕ) : List Bool :=
  w ++ (List.range k).map fun i => part w v rest (i + 1)

theorem acc_length (w v rest k) : (acc w v rest k).length = w.length + k := by simp [acc]

theorem acc_low (w v rest k) (i : ℕ) (h : i < w.length) :
    (acc w v rest k).getD i false = w.getD i false := List.getD_append _ _ _ _ h

theorem acc_chain (w : List Bool) (v : ℕ) (rest : List ℕ) (k : ℕ) (hv : v < w.length)
    (hk : k ≤ rest.length) :
    (acc w v rest k).getD ((v :: (List.range rest.length).map (fun j => w.length + j)).getD k 0) false =
      part w v rest k := by
  cases k with
  | zero =>
    rw [List.getD_cons_zero, acc_low _ _ _ _ _ hv]
    simp [part]
  | succ k =>
    rw [List.getD_cons_succ]
    have : ((List.range rest.length).map (fun j => w.length + j)).getD k 0 = w.length + k := by
      rw [List.getD_eq_getElem?_getD]
      simp [show k < rest.length by omega]
    rw [this, acc, List.getD_append_right _ _ _ _ (by omega)]
    rw [List.getD_eq_getElem?_getD]
    simp

theorem chain_run (w : List Bool) (v : ℕ) (rest : List ℕ) (hv : v < w.length)
    (hr : ∀ r ∈ rest, r < w.length) (k : ℕ) (hk : k ≤ rest.length) :
    ((List.range k).map (fun i => (⟨GateOp.or,
      [(v :: (List.range rest.length).map (fun j => w.length + j)).getD i 0, rest.getD i 0]⟩ : Gate))).foldl
        step w = acc w v rest k := by
  induction k with
  | zero => simp [acc]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, step, GateOp.eval]
    rw [acc_chain w v rest k hv (by omega)]
    have hk' : k < rest.length := by omega
    have g : rest.getD k 0 = rest[k] := by
      rw [List.getD_eq_getElem?_getD]
      simp [hk']
    rw [g, acc_low _ _ _ _ _ (hr _ (List.getElem_mem hk'))]
    rw [acc, acc, List.range_succ, List.map_append, List.append_assoc]
    congr 2
    simp only [List.map_cons, List.map_nil, part, List.any_cons, List.any_nil, id, Bool.or_false]
    rw [List.take_succ_eq_append_getElem hk', List.any_append]
    simp [Bool.or_assoc]

theorem block_length (B a t v : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v rest lead).length = rest.length + 1 + if lead then 0 else 1 := by
  cases lead <;> simp [blockGates]

theorem block_run (w : List Bool) (a t v : ℕ) (rest : List ℕ) (lead : Bool)
    (ha : lead = false → a < w.length) (ht : t < w.length) (hv : v < w.length)
    (hr : ∀ r ∈ rest, r < w.length) :
    ((blockGates w.length a t v rest lead).foldl step w).length =
        w.length + (blockGates w.length a t v rest lead).length ∧
      (∀ i < w.length, ((blockGates w.length a t v rest lead).foldl step w).getD i false = w.getD i false) ∧
      ((blockGates w.length a t v rest lead).foldl step w).getD
        (w.length + (blockGates w.length a t v rest lead).length - 1) false =
        ((!lead && w.getD a false) || (w.getD t false && (v :: rest).any fun r => w.getD r false)) := by
  have full : part w v rest rest.length = (v :: rest).any fun r => w.getD r false := by
    simp [part]
  let w1 := acc w v rest rest.length
  let b : Bool := w.getD t false && (v :: rest).any fun r => w.getD r false
  have l1 : w1.length = w.length + rest.length := acc_length _ _ _ _
  have first : step w1 ⟨GateOp.and, [t, (v :: (List.range rest.length).map
      (fun j => w.length + j)).getD rest.length 0]⟩ = w1 ++ [b] := by
    simp only [step, GateOp.eval, List.map_cons, List.map_nil, w1]
    rw [acc_chain w v rest _ hv le_rfl, acc_low _ _ _ _ _ ht, full]
    simp [b]
  have low (i : ℕ) (hi : i < w.length) (l : List Bool) : (w1 ++ l).getD i false = w.getD i false := by
    rw [List.getD_append _ _ _ _ (by omega)]
    exact acc_low _ _ _ _ _ hi
  have last (u : List Bool) (c : Bool) (j : ℕ) (hj : j = u.length) : (u ++ [c]).getD j false = c := by
    rw [hj, List.getD_append_right _ _ _ _ le_rfl]
    simp
  cases lead with
  | true =>
    have run : (blockGates w.length a t v rest true).foldl step w = w1 ++ [b] := by
      rw [blockGates, List.foldl_append, chain_run w v rest hv hr _ le_rfl]
      simp only [if_true, List.foldl_cons, List.foldl_nil]
      exact first
    rw [run, block_length]
    refine ⟨by simp [l1]; omega, fun i hi => low i hi _, ?_⟩
    rw [last _ _ _ (by rw [l1]; simp)]
    simp [b]
  | false =>
    have run : (blockGates w.length a t v rest false).foldl step w = (w1 ++ [b]) ++ [w.getD a false || b] := by
      rw [blockGates, List.foldl_append, chain_run w v rest hv hr _ le_rfl]
      simp only [Bool.false_eq_true, if_false, List.foldl_cons, List.foldl_nil]
      rw [show step (acc w v rest rest.length) _ = _ from first]
      simp only [step, GateOp.eval, List.map_cons, List.map_nil]
      rw [low a (ha rfl), last w1 b _ (by rw [l1])]
      simp
    rw [run, block_length]
    refine ⟨by simp [l1]; omega, fun i hi => ?_, ?_⟩
    · rw [List.append_assoc]
      exact low i hi _
    · rw [last _ _ _ (by simp [l1]; omega)]
      simp [b]

def hit (w : List Bool) (own : List (ℕ × List ℕ)) : Bool :=
  own.any fun o => w.getD o.1 false && o.2.any fun r => w.getD r false

theorem hit_congr (w w' : List Bool) (n : ℕ) (own : List (ℕ × List ℕ))
    (h : ∀ i < n, w.getD i false = w'.getD i false) (ho : ∀ o ∈ own, o.1 < n ∧ ∀ r ∈ o.2, r < n) :
    hit w own = hit w' own := by
  rw [Bool.eq_iff_iff]
  simp only [hit, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨o, hm, h1, r, hr, h2⟩
    exact ⟨o, hm, by rw [← h _ (ho o hm).1]; exact h1, r, hr, by rw [← h _ ((ho o hm).2 r hr)]; exact h2⟩
  · rintro ⟨o, hm, h1, r, hr, h2⟩
    exact ⟨o, hm, by rw [h _ (ho o hm).1]; exact h1, r, hr, by rw [h _ ((ho o hm).2 r hr)]; exact h2⟩

theorem cover_run (n : ℕ) (own : List (ℕ × List ℕ)) (ho : ∀ o ∈ own, o.1 < n ∧ ∀ r ∈ o.2, r < n)
    (w : List Bool) (hw : n ≤ w.length) (a : ℕ) (ha : a < w.length) :
    ((coverGatesB w.length false a own).foldl step w).getD
      (if (coverGatesB w.length false a own).length = 0 then a
        else w.length + (coverGatesB w.length false a own).length - 1) false =
      (w.getD a false || hit w own) := by
  induction own generalizing w a with
  | nil => simp [coverGatesB, hit]
  | cons o os ih =>
    have hos : ∀ o ∈ os, o.1 < n ∧ ∀ r ∈ o.2, r < n := fun o h => ho o (List.mem_cons_of_mem _ h)
    obtain ⟨t, l⟩ := o
    cases l with
    | nil =>
      rw [coverGatesB, ih hos w hw a ha]
      simp [hit]
    | cons v rest =>
      obtain ⟨h1, h2⟩ := ho (t, v :: rest) List.mem_cons_self
      have ht : t < w.length := by have : t < n := h1; omega
      have hr : ∀ r ∈ v :: rest, r < w.length := fun r h => lt_of_lt_of_le (h2 r h) hw
      obtain ⟨q1, q2, q3⟩ := block_run w a t v rest false (fun _ => ha) ht (hr v List.mem_cons_self)
        (fun r h => hr r (List.mem_cons_of_mem _ h))
      have pos : 0 < (blockGates w.length a t v rest false).length := by rw [block_length]; omega
      rw [coverGatesB, List.foldl_append]
      generalize hbg : blockGates w.length a t v rest false = bg at *
      have key := ih hos (bg.foldl step w) (by omega) (w.length + bg.length - 1) (by omega)
      rw [q1] at key
      rw [q3] at key
      rw [List.length_append]
      have idx : (if bg.length + (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length = 0
          then a else w.length + (bg.length +
            (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length) - 1) =
          if (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length = 0
            then w.length + bg.length - 1 else w.length + bg.length +
            (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length - 1 := by
        rw [if_neg (by omega)]
        split <;> omega
      rw [idx, key, hit_congr _ w n os (fun i hi => q2 i (by omega)) hos]
      simp [hit, Bool.or_assoc]

theorem cover_length (own : List (ℕ × List ℕ)) (ho : ∀ o ∈ own, o.2 ≠ []) (B a : ℕ) :
    (coverGatesB B false a own).length = (own.map fun o => o.2.length).sum + own.length := by
  induction own generalizing B a with
  | nil => simp [coverGatesB]
  | cons o os ih =>
    obtain ⟨t, l⟩ := o
    cases l with
    | nil => exact absurd rfl (ho (t, []) List.mem_cons_self)
    | cons v rest =>
      rw [coverGatesB, List.length_append, ih (fun o h => ho o (List.mem_cons_of_mem _ h)), block_length]
      simp
      omega

theorem cover_all (n : ℕ) (own : List (ℕ × List ℕ)) (ho : ∀ o ∈ own, o.1 < n ∧ ∀ r ∈ o.2, r < n)
    (hne : ∀ o ∈ own, o.2 ≠ []) :
    (coverCircuitB n own).size = (own.map fun o => o.2.length).sum + own.length - 1 ∧
      ∀ w : List Bool, w.length = n → (coverCircuitB n own).eval w = hit w own := by
  cases own with
  | nil =>
    refine ⟨by simp [coverCircuitB, coverGatesB, Circuit.size], ?_⟩
    intro w hw
    simp only [coverCircuitB, coverGatesB, if_true]
    change w.getD n false = false
    exact List.getD_eq_default _ _ hw.le
  | cons o os =>
    obtain ⟨t, l⟩ := o
    cases l with
    | nil => exact absurd rfl (hne (t, []) List.mem_cons_self)
    | cons v rest =>
      have hos : ∀ o ∈ os, o.1 < n ∧ ∀ r ∈ o.2, r < n := fun o h => ho o (List.mem_cons_of_mem _ h)
      have len := block_length n 0 t v rest true
      rw [coverCircuitB, if_neg (by
        rw [coverGatesB]
        intro h
        have := congrArg List.length h
        rw [List.length_append, len] at this
        simp at this)]
      constructor
      · change (coverGatesB n true 0 ((t, v :: rest) :: os)).length = _
        rw [coverGatesB, List.length_append, cover_length os (fun o h => hne o (List.mem_cons_of_mem _ h)), len]
        simp
        omega
      · intro w hw
        subst hw
        obtain ⟨h1, h2⟩ := ho (t, v :: rest) List.mem_cons_self
        obtain ⟨q1, q2, q3⟩ := block_run w 0 t v rest true (fun h => by cases h) h1
          (h2 v List.mem_cons_self) (fun r h => h2 r (List.mem_cons_of_mem _ h))
        change ((coverGatesB w.length true 0 ((t, v :: rest) :: os)).foldl step w).getD _ false = _
        rw [coverGatesB, List.foldl_append, List.length_append]
        generalize hbg : blockGates w.length 0 t v rest true = bg at *
        have pos : 0 < bg.length := by rw [len]; omega
        have key := cover_run w.length os hos (bg.foldl step w) (by omega) (w.length + bg.length - 1) (by omega)
        rw [q1, q3] at key
        have idx : w.length + (bg.length +
            (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length) - 1 =
          if (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length = 0
            then w.length + bg.length - 1 else w.length + bg.length +
            (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length - 1 := by
          split <;> omega
        rw [idx, key, hit_congr _ w w.length os q2 hos]
        simp [hit]


namespace Shape
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Inv (p q : ℕ → Prop) (B : ℕ) (L : List Gate) (S T : Finset ℕ) : Prop :=
  (∀ (k : ℕ) (g : Gate), L[k]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧
    ∀ i ∈ g.inputs, i < B + k) ∧
  (∀ w ∈ S, ∃ (k : ℕ) (g : Gate), L[k]? = some g ∧ w = B + k ∧ g.op = GateOp.or ∧ ∀ i ∈ g.inputs, p i ∨ i ∈ S) ∧
  (∀ w ∈ T, ∃ (k : ℕ) (g : Gate), L[k]? = some g ∧ w = B + k ∧ g.op = GateOp.or ∧ ∀ i ∈ g.inputs, q i ∨ i ∈ T) ∧
  (∀ (k : ℕ) (g : Gate), L[k]? = some g → g.op = GateOp.and → ∃ a b, g.inputs = [a, b] ∧
     (((p a ∨ a ∈ S) ∧ (q b ∨ b ∈ T)) ∨ ((q a ∨ a ∈ T) ∧ (p b ∨ b ∈ S))))

theorem inv_swap {p q : ℕ → Prop} {B : ℕ} {L : List Gate} {S T : Finset ℕ}
    (h : Inv p q B L S T) : Inv q p B L T S := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h3, h2, ?_⟩
  intro k g hk ho
  obtain ⟨a, b, e, h⟩ := h4 k g hk ho
  exact ⟨a, b, e, h.symm⟩

theorem inv_nil (p q : ℕ → Prop) (B : ℕ) : Inv p q B [] ∅ ∅ := by
  simp [Inv]

theorem app_cases {L1 L2 : List Gate} {k : ℕ} {g : Gate} (h : (L1 ++ L2)[k]? = some g) :
    L1[k]? = some g ∨ ∃ k2, k = L1.length + k2 ∧ L2[k2]? = some g := by
  rw [List.getElem?_append] at h
  split at h
  · exact Or.inl h
  · exact Or.inr ⟨k - L1.length, by omega, h⟩

theorem app_left {L1 L2 : List Gate} {k : ℕ} {g : Gate} (h : L1[k]? = some g) :
    (L1 ++ L2)[k]? = some g := by
  have hk : k < L1.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.getElem?_append_left hk]
  exact h

theorem app_right {L1 L2 : List Gate} {k : ℕ} {g : Gate} (h : L2[k]? = some g) :
    (L1 ++ L2)[L1.length + k]? = some g := by
  rw [List.getElem?_append_right (by omega)]
  simpa using h

theorem inv_app {p q : ℕ → Prop} {B : ℕ} {L1 L2 : List Gate} {S1 T1 S2 T2 : Finset ℕ}
    (h : Inv p q B L1 S1 T1) (h' : Inv p q (B + L1.length) L2 S2 T2) :
    Inv p q B (L1 ++ L2) (S1 ∪ S2) (T1 ∪ T2) := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  obtain ⟨b1, b2, b3, b4⟩ := h'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k g hk
    rcases app_cases hk with h | ⟨k2, rfl, h⟩
    · exact a1 k g h
    · obtain ⟨x, y, z⟩ := b1 k2 g h
      exact ⟨x, y, fun i hi => by have := z i hi; omega⟩
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨k, g, e1, e2, e3, e4⟩ := a2 w hw
      exact ⟨k, g, app_left e1, e2, e3, fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_left _ h)⟩
    · obtain ⟨k, g, e1, e2, e3, e4⟩ := b2 w hw
      exact ⟨L1.length + k, g, app_right e1, by omega, e3,
        fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_right _ h)⟩
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨k, g, e1, e2, e3, e4⟩ := a3 w hw
      exact ⟨k, g, app_left e1, e2, e3, fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_left _ h)⟩
    · obtain ⟨k, g, e1, e2, e3, e4⟩ := b3 w hw
      exact ⟨L1.length + k, g, app_right e1, by omega, e3,
        fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_right _ h)⟩
  · intro k g hk ho
    rcases app_cases hk with h | ⟨k2, rfl, h⟩
    · obtain ⟨a, b, e, hh⟩ := a4 k g h ho
      refine ⟨a, b, e, ?_⟩
      simp only [Finset.mem_union]
      tauto
    · obtain ⟨a, b, e, hh⟩ := b4 k2 g h ho
      refine ⟨a, b, e, ?_⟩
      simp only [Finset.mem_union]
      tauto

theorem cval (B v1 m i : ℕ) (hi : i ≤ m) :
    (i = 0 ∧ (v1 :: (List.range m).map (fun j => B + j)).getD i 0 = v1) ∨
    (0 < i ∧ (v1 :: (List.range m).map (fun j => B + j)).getD i 0 = B + (i - 1)) := by
  cases i with
  | zero => left; simp
  | succ j =>
    right
    have hj : j < m := by omega
    simp [List.getD_eq_getElem?_getD, hj]

theorem block_get {B a t v1 : ℕ} {rest : List ℕ} {lead : Bool} {k : ℕ} {g : Gate}
    (h : (blockGates B a t v1 rest lead)[k]? = some g) :
    (k < rest.length ∧ g = ⟨GateOp.or,
      [(v1 :: (List.range rest.length).map (fun j => B + j)).getD k 0, rest.getD k 0]⟩) ∨
    (k = rest.length ∧ g = ⟨GateOp.and,
      [t, (v1 :: (List.range rest.length).map (fun j => B + j)).getD rest.length 0]⟩) ∨
    (k = rest.length + 1 ∧ lead = false ∧ g = ⟨GateOp.or, [a, B + rest.length]⟩) := by
  unfold blockGates at h
  rcases app_cases h with h | ⟨k2, hk, h⟩
  · left
    have hk : k < rest.length := by
      have := (List.getElem?_eq_some_iff.mp h).1
      simpa using this
    refine ⟨hk, ?_⟩
    simp only [List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.some.injEq] at h
    exact h.symm
  · right
    simp only [List.length_map, List.length_range] at hk
    cases k2 with
    | zero =>
      left
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact ⟨by omega, h.symm⟩
    | succ k3 =>
      right
      cases lead with
      | true => simp at h
      | false =>
        cases k3 with
        | zero =>
          simp only [List.getElem?_cons_succ, Bool.false_eq_true, ite_false,
            List.getElem?_cons_zero, Option.some.injEq] at h
          exact ⟨by omega, rfl, h.symm⟩
        | succ k4 => simp at h

theorem block_chain {B a t v1 : ℕ} {rest : List ℕ} {lead : Bool} {k : ℕ} (hk : k < rest.length) :
    (blockGates B a t v1 rest lead)[k]? = some ⟨GateOp.or,
      [(v1 :: (List.range rest.length).map (fun j => B + j)).getD k 0, rest.getD k 0]⟩ := by
  unfold blockGates
  apply app_left
  simp [hk]

theorem rest_mem {rest : List ℕ} {k : ℕ} (hk : k < rest.length) : rest.getD k 0 ∈ rest := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem inv_block {p q : ℕ → Prop} {B a t v1 : ℕ} {rest : List ℕ} {lead : Bool}
    (hp : ∀ i, p i → i < B) (hq : ∀ i, q i → i < B) (ha : lead = false → a < B)
    (ht : q t) (hv : p v1) (hr : ∀ v ∈ rest, p v) :
    Inv p q B (blockGates B a t v1 rest lead)
      ((Finset.range rest.length).image (fun j => B + j)) ∅ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k g hk
    rcases block_get hk with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
    · refine ⟨Or.inr rfl, rfl, ?_⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · rcases cval B v1 rest.length k (by omega) with ⟨_, e⟩ | ⟨h0, e⟩
        · rw [e]; have := hp _ hv; omega
        · rw [e]; omega
      · have := hp _ (hr _ (rest_mem h1)); omega
    · refine ⟨Or.inl rfl, rfl, ?_⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · have := hq _ ht; omega
      · rcases cval B v1 rest.length rest.length (le_refl _) with ⟨_, e⟩ | ⟨h0, e⟩
        · rw [e]; have := hp _ hv; omega
        · rw [e]; omega
    · refine ⟨Or.inr rfl, rfl, ?_⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      have := ha h2
      rcases hi with rfl | rfl <;> omega
  · intro w hw
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
    have hk : k < rest.length := Finset.mem_range.mp hk
    refine ⟨k, _, block_chain hk, rfl, rfl, ?_⟩
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · rcases cval B v1 rest.length k (by omega) with ⟨_, e⟩ | ⟨h0, e⟩
      · rw [e]; exact Or.inl hv
      · rw [e]; right
        exact Finset.mem_image.mpr ⟨k - 1, Finset.mem_range.mpr (by omega), rfl⟩
    · exact Or.inl (hr _ (rest_mem hk))
  · intro w hw
    simp at hw
  · intro k g hk ho
    rcases block_get hk with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
    · simp at ho
    · refine ⟨_, _, rfl, Or.inr ⟨Or.inl ht, ?_⟩⟩
      rcases cval B v1 rest.length rest.length (le_refl _) with ⟨_, e⟩ | ⟨h0, e⟩
      · rw [e]; exact Or.inl hv
      · rw [e]; right
        exact Finset.mem_image.mpr ⟨rest.length - 1, Finset.mem_range.mpr (by omega), rfl⟩
    · simp at ho

theorem block_len (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    1 ≤ (blockGates B a t v1 rest lead).length := by
  unfold blockGates
  simp
  omega

theorem inv_cover (p q : ℕ → Prop) (own : List (ℕ × List ℕ)) :
    ∀ (B : ℕ) (lead : Bool) (a : ℕ), (∀ i, p i → i < B) → (∀ i, q i → i < B) →
      (lead = false → a < B) →
      (∀ o ∈ own, (q o.1 ∧ ∀ v ∈ o.2, p v) ∨ (p o.1 ∧ ∀ v ∈ o.2, q v)) →
      ∃ S T, Inv p q B (coverGatesB B lead a own) S T := by
  induction own with
  | nil =>
    intro B lead a _ _ _ _
    exact ⟨∅, ∅, by simpa [coverGatesB] using inv_nil p q B⟩
  | cons o os ih =>
    intro B lead a hp hq ha ho
    obtain ⟨t, l⟩ := o
    have hos : ∀ o ∈ os, (q o.1 ∧ ∀ v ∈ o.2, p v) ∨ (p o.1 ∧ ∀ v ∈ o.2, q v) :=
      fun o h => ho o (List.mem_cons_of_mem _ h)
    cases l with
    | nil =>
      simp only [coverGatesB]
      exact ih B lead a hp hq ha hos
    | cons v1 rest =>
      simp only [coverGatesB]
      have hl := block_len B a t v1 rest lead
      obtain ⟨S2, T2, h2⟩ := ih (B + (blockGates B a t v1 rest lead).length) false
        (B + (blockGates B a t v1 rest lead).length - 1)
        (fun i h => by have := hp i h; omega) (fun i h => by have := hq i h; omega)
        (fun _ => by omega) hos
      have h0 := ho (t, v1 :: rest) List.mem_cons_self
      simp only [List.mem_cons, forall_eq_or_imp] at h0
      rcases h0 with ⟨h1, h3, h4⟩ | ⟨h1, h3, h4⟩
      · exact ⟨_, _, inv_app (inv_block hp hq ha h1 h3 h4) h2⟩
      · exact ⟨_, _, inv_app (inv_swap (inv_block hq hp ha h1 h3 h4)) h2⟩

theorem gates_eq (n : ℕ) (own : List (ℕ × List ℕ)) :
    (coverCircuitB n own).gates = coverGatesB n true 0 own := by
  unfold coverCircuitB
  split <;> simp_all

end Shape

lemma run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm]

lemma run_low (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma block_and_run (w : List Bool) (a t v : ℕ) (rest : List ℕ) (lead : Bool)
    (ht : t < w.length) (hv : v < w.length) (hr : ∀ r ∈ rest, r < w.length) :
    ((blockGates w.length a t v rest lead).foldl step w).getD
      (w.length + rest.length) false =
      (w.getD t false && (v :: rest).any (fun r => w.getD r false)) := by
  obtain ⟨hlen, _, hval⟩ := block_run w a t v rest true (by simp) ht hv hr
  have he : blockGates w.length a t v rest lead =
      blockGates w.length a t v rest true ++
        if lead then [] else [⟨GateOp.or, [a, w.length + rest.length]⟩] := by
    cases lead <;> simp [blockGates, List.append_assoc]
  rw [he, List.foldl_append, run_low _ _ _ (by rw [hlen, block_length]; simp)]
  simpa [block_length] using hval

lemma cover_and_formula (n : ℕ) (own : List (ℕ × List ℕ))
    (ho : ∀ o ∈ own, o.1 < n ∧ ∀ r ∈ o.2, r < n) :
    ∀ (B : ℕ) (hB : n ≤ B) (lead : Bool) (a : ℕ)
      (ha : lead = false → a < B) (k : ℕ) (g : Gate),
      (coverGatesB B lead a own)[k]? = some g → g.op = GateOp.and →
      ∃ (t : ℕ) (l : List ℕ), (t, l) ∈ own ∧ l ≠ [] ∧
        ∀ (w : List Bool), w.length = B →
          ((coverGatesB B lead a own).foldl step w).getD (B + k) false =
            (w.getD t false && l.any (fun r => w.getD r false)) := by
  induction own with
  | nil => intro B hB lead a ha k g hg; simp [coverGatesB] at hg
  | cons o os ih =>
    intro B hB lead a ha k g hg hop
    obtain ⟨t, l⟩ := o
    have hos : ∀ o ∈ os, o.1 < n ∧ ∀ r ∈ o.2, r < n :=
      fun o h => ho o (List.mem_cons_of_mem _ h)
    cases l with
    | nil =>
      obtain ⟨t', l', hm, hne, hv⟩ := ih hos B hB lead a ha k g hg hop
      exact ⟨t', l', List.mem_cons_of_mem _ hm, hne, hv⟩
    | cons v rest =>
      have ht := (ho (t, v :: rest) List.mem_cons_self).1
      have hr := (ho (t, v :: rest) List.mem_cons_self).2
      have hpos := Shape.block_len B a t v rest lead
      rw [coverGatesB] at hg
      rcases Shape.app_cases hg with hg | ⟨k2, hk, hg⟩
      · rcases Shape.block_get hg with ⟨_, rfl⟩ | ⟨rfl, rfl⟩ | ⟨_, _, rfl⟩
        · cases hop
        · refine ⟨t, v :: rest, List.mem_cons_self, List.cons_ne_nil _ _, ?_⟩
          intro w hw
          subst B
          rw [coverGatesB, List.foldl_append, run_low _ _ _ (by
            rw [run_length, block_length]; split <;> omega)]
          exact block_and_run w a t v rest lead (ht.trans_le hB)
            ((hr v List.mem_cons_self).trans_le hB)
            (fun r h => (hr r (List.mem_cons_of_mem _ h)).trans_le hB)
        · cases hop
      · obtain ⟨t', l', hm, hne, hv⟩ := ih hos
          (B + (blockGates B a t v rest lead).length) (by omega) false
          (B + (blockGates B a t v rest lead).length - 1) (fun _ => by omega)
          k2 g hg hop
        refine ⟨t', l', List.mem_cons_of_mem _ hm, hne, ?_⟩
        intro w hw
        subst B
        let w' := (blockGates w.length a t v rest lead).foldl step w
        have hv' := hv w' (run_length _ _)
        have heq : l'.any (fun r => w'.getD r false) =
            l'.any (fun r => w.getD r false) := by
          apply Bool.eq_iff_iff.mpr
          simp only [List.any_eq_true]
          constructor
          · rintro ⟨r, hr', hval⟩
            refine ⟨r, hr', ?_⟩
            rw [← run_low (blockGates w.length a t v rest lead) w r
              (((hos (t', l') hm).2 r hr').trans_le hB)]
            exact hval
          · rintro ⟨r, hr', hval⟩
            refine ⟨r, hr', ?_⟩
            rw [run_low _ _ _ (((hos (t', l') hm).2 r hr').trans_le hB)]
            exact hval
        rw [coverGatesB, List.foldl_append, hk]
        rw [run_low _ _ t' (((hos (t', l') hm).1).trans_le hB), heq] at hv'
        simpa only [w', Nat.add_assoc] using hv'

def EdgeStep (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ k h, b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs

def OrClosed (n : ℕ) (C : Circuit) (S : Finset ℕ) : Prop :=
  ∀ w ∈ S, ∃ k g, C.gates[k]? = some g ∧ w = n + k ∧ g.op = GateOp.or ∧
    ∀ i ∈ g.inputs, i < n ∨ i ∈ S

lemma cover_flat (n : ℕ) (own : List (ℕ × List ℕ))
    (ho : ∀ o ∈ own, o.1 < n ∧ ∀ r ∈ o.2, r < n) :
    (∀ (k : ℕ) (g : Gate), (coverCircuitB n own).gates[k]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧
        ∀ i ∈ g.inputs, i < n + k) ∧
    ∃ S : Finset ℕ, OrClosed n (coverCircuitB n own) S ∧
      ∀ (k : ℕ) (g : Gate), (coverCircuitB n own).gates[k]? = some g → g.op = GateOp.and →
        ∀ i ∈ g.inputs, i < n ∨ i ∈ S := by
  classical
  obtain ⟨S, T, hshape, hS, hT, hA⟩ := Shape.inv_cover (fun i => i < n)
    (fun i => i < n) own n true 0 (fun _ h => h) (fun _ h => h) (by simp)
      (fun o h => Or.inl (ho o h))
  refine ⟨?_, S ∪ T, ?_, ?_⟩
  · simpa only [Shape.gates_eq] using hshape
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨k, g, hg, he, hop, hin⟩ := hS w hw
      refine ⟨k, g, by simpa only [Shape.gates_eq] using hg, he, hop, ?_⟩
      intro i hi
      exact (hin i hi).imp id (fun h => Finset.mem_union_left T h)
    · obtain ⟨k, g, hg, he, hop, hin⟩ := hT w hw
      refine ⟨k, g, by simpa only [Shape.gates_eq] using hg, he, hop, ?_⟩
      intro i hi
      exact (hin i hi).imp id (fun h => Finset.mem_union_right S h)
  · intro k g hg hop i hi
    rw [Shape.gates_eq] at hg
    obtain ⟨a, b, he, h⟩ := hA k g hg hop
    rw [he] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · rcases h with h | h
      · exact h.1.imp id (fun h => Finset.mem_union_left T h)
      · exact h.1.imp id (fun h => Finset.mem_union_right S h)
    · rcases h with h | h
      · exact h.2.imp id (fun h => Finset.mem_union_right S h)
      · exact h.2.imp id (fun h => Finset.mem_union_left T h)

lemma step_safe {n : ℕ} {C : Circuit} {S : Finset ℕ}
    (hS : OrClosed n C S) {a b : ℕ} (hab : EdgeStep n C a b)
    (hb : b < n ∨ b ∈ S) : a < n ∨ a ∈ S := by
  obtain ⟨hlt, k, g, hbk, hg, hin⟩ := hab
  rcases hb with hb | hb
  · omega
  · obtain ⟨j, h, hh, hbj, hop, inputs⟩ := hS b hb
    have hkj : k = j := by omega
    subst j
    have hgh : g = h := Option.some.inj (hg.symm.trans hh)
    subst h
    exact inputs a hin

lemma no_and_ancestor {n : ℕ} {C : Circuit} {S : Finset ℕ}
    (hS : OrClosed n C S) (t : ℕ) (g : Gate) (hg : C.gates[t]? = some g)
    (hin : ∀ i ∈ g.inputs, i < n ∨ i ∈ S)
    (t' : ℕ) (g' : Gate) (hg' : C.gates[t']? = some g') (hop' : g'.op = GateOp.and) :
    ¬ Relation.TransGen (EdgeStep n C) (n + t') (n + t) := by
  intro hpath
  have hsafe : ∀ a, Relation.TransGen (EdgeStep n C) a (n + t) → a < n ∨ a ∈ S := by
    intro a h
    induction h using Relation.TransGen.head_induction_on with
    | single h =>
      obtain ⟨hlt, k, gk, hkt, hgk, hmem⟩ := h
      have hkt' : k = t := by omega
      subst k
      have hgg : gk = g := Option.some.inj (hgk.symm.trans hg)
      subst gk
      exact hin _ hmem
    | head h _ ih => exact step_safe hS h ih
  rcases hsafe (n + t') hpath with h | h
  · omega
  · obtain ⟨j, gj, hgj, hj, hopj, _⟩ := hS (n + t') h
    have he : j = t' := by omega
    subst j
    have he' : gj = g' := Option.some.inj (hgj.symm.trans hg')
    subst gj
    rw [hop'] at hopj
    cases hopj

lemma cover_no_and_ancestor (n : ℕ) (own : List (ℕ × List ℕ))
    (ho : ∀ o ∈ own, o.1 < n ∧ ∀ r ∈ o.2, r < n)
    (t : ℕ) (g : Gate) (hg : (coverCircuitB n own).gates[t]? = some g)
    (hop : g.op = GateOp.and)
    (t' : ℕ) (g' : Gate) (hg' : (coverCircuitB n own).gates[t']? = some g')
    (hop' : g'.op = GateOp.and) :
    ¬ Relation.TransGen (EdgeStep n (coverCircuitB n own)) (n + t') (n + t) := by
  obtain ⟨_, S, hS, hA⟩ := cover_flat n own ho
  exact no_and_ancestor hS t g hg (hA t g hg hop) t' g' hg' hop'

def encodeOwners {n : ℕ} (own : List (Fin n × List (Fin n))) : List (ℕ × List ℕ) :=
  own.map (fun o => (o.1.val, o.2.map Fin.val))

lemma encodeOwners_bounded {n : ℕ} (own : List (Fin n × List (Fin n))) :
    ∀ o ∈ encodeOwners own, o.1 < n ∧ ∀ r ∈ o.2, r < n := by
  intro o ho
  obtain ⟨⟨c, vs⟩, hm, rfl⟩ := List.mem_map.mp ho
  refine ⟨c.isLt, ?_⟩
  intro r hr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
  exact v.isLt

def OwnsDirect (n : ℕ) (C : Circuit) (t : ℕ) (u v : Fin n) : Prop :=
  (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧
  ∀ t' g', C.gates[t']? = some g' → g'.op = GateOp.and →
    Relation.TransGen (EdgeStep n C) (n + t') (n + t) →
    (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false

lemma cover_owned_stars {n : ℕ} (G : SimpleGraph (Fin n))
    (own : List (Fin n × List (Fin n)))
    (hadj : ∀ o ∈ own, ∀ v ∈ o.2, G.Adj o.1 v) :
    ∀ (t : ℕ) (g : Gate), (coverCircuitB n (encodeOwners own)).gates[t]? = some g →
      g.op = GateOp.and → ∃ c : Fin n,
        (∃ u v : Fin n, G.Adj u v ∧ OwnsDirect n (coverCircuitB n (encodeOwners own)) t u v) ∧
        ∀ u v : Fin n, OwnsDirect n (coverCircuitB n (encodeOwners own)) t u v → u = c ∨ v = c := by
  intro t g hg hop
  have hbounds := encodeOwners_bounded own
  have hg' := hg
  rw [Shape.gates_eq] at hg'
  obtain ⟨c0, vs0, hmem, hne, heval⟩ := cover_and_formula n (encodeOwners own)
    hbounds n le_rfl true 0 (by simp) t g hg' hop
  obtain ⟨⟨c, vs⟩, howner, hpair⟩ := List.mem_map.mp hmem
  have hc : c.val = c0 := congrArg Prod.fst hpair
  have hvs : vs.map Fin.val = vs0 := congrArg Prod.snd hpair
  subst c0
  subst vs0
  cases vs with
  | nil => simp at hne
  | cons v rest =>
    have hformula (x : Fin n → Bool) :
        ((coverCircuitB n (encodeOwners own)).wires (List.ofFn x)).getD (n + t) false =
          (x c && (v :: rest).any x) := by
      have h := heval (List.ofFn x) List.length_ofFn
      change ((coverCircuitB n (encodeOwners own)).gates.foldl step (List.ofFn x)).getD
        (n + t) false = _
      rw [Shape.gates_eq]
      simpa only [List.any_map, Function.comp_def, read] using h
    have hno (u v : Fin n) :
        ((coverCircuitB n (encodeOwners own)).wires
          (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true →
        OwnsDirect n (coverCircuitB n (encodeOwners own)) t u v := by
      intro hval
      refine ⟨hval, ?_⟩
      intro t' g' hg' hop' hpath
      exact False.elim (cover_no_and_ancestor n (encodeOwners own) hbounds
        t g hg hop t' g' hg' hop' hpath)
    refine ⟨c, ⟨c, v, hadj (c, v :: rest) howner v List.mem_cons_self, hno c v ?_⟩, ?_⟩
    · rw [hformula]
      simp
    · intro u v huv
      have hval := huv.1
      rw [hformula, Bool.and_eq_true] at hval
      have hcv : c = u ∨ c = v := of_decide_eq_true hval.1
      exact hcv.imp Eq.symm Eq.symm

lemma cover_monotone (n : ℕ) (own : List (Fin n × List (Fin n))) :
    ∀ g ∈ (coverCircuitB n (encodeOwners own)).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hg
  have hget : (coverCircuitB n (encodeOwners own)).gates[i]? = some g := by
    rw [List.getElem?_eq_getElem hi, he]
  have hshape := (cover_flat n (encodeOwners own) (encodeOwners_bounded own)).1 i g hget
  exact ⟨hshape.1, hshape.2.1.le⟩

lemma single_star_data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n) (U : List (Fin n)) (hne : U ≠ [])
    (hgraph : ∀ u v : Fin n, G.Adj u v ↔ (u = c ∧ v ∈ U) ∨ (v = c ∧ u ∈ U)) :
    let C := coverCircuitB n (encodeOwners [(c, U)])
    C.size = U.length ∧
    (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
    ∀ t g, C.gates[t]? = some g → g.op = GateOp.and → ∃ c' : Fin n,
      (∃ u v : Fin n, G.Adj u v ∧ OwnsDirect n C t u v) ∧
      ∀ u v : Fin n, OwnsDirect n C t u v → u = c' ∨ v = c' := by
  dsimp only
  have hn : ∀ o ∈ encodeOwners [(c, U)], o.2 ≠ [] := by
    simpa [encodeOwners] using hne
  obtain ⟨hsize, heval⟩ := cover_all n (encodeOwners [(c, U)])
    (encodeOwners_bounded _) hn
  refine ⟨by simpa [encodeOwners] using hsize, cover_monotone _ _, ?_, ?_⟩
  · intro x
    rw [heval (List.ofFn x) List.length_ofFn]
    apply Bool.eq_iff_iff.mpr
    simp only [hit, encodeOwners, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, Bool.or_false, List.any_map, Function.comp_def, read,
      Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hc, v, hv, hxv⟩
      exact ⟨c, v, (hgraph c v).mpr (Or.inl ⟨rfl, hv⟩), hc, hxv⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      rcases (hgraph u v).mp huv with ⟨rfl, hmem⟩ | ⟨rfl, hmem⟩
      · exact ⟨hu, v, hmem, hv⟩
      · exact ⟨hv, u, hmem, hu⟩
  · apply cover_owned_stars G [(c, U)]
    intro o ho v hv
    have he : o = (c, U) := by simpa using ho
    subst o
    exact (hgraph c v).mpr (Or.inl ⟨rfl, hv⟩)

lemma cover_data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (own : List (Fin n × List (Fin n)))
    (hne : ∀ o ∈ own, o.2 ≠ [])
    (hgraph : ∀ u v : Fin n, G.Adj u v ↔
      ∃ o ∈ own, (o.1 = u ∧ v ∈ o.2) ∨ (o.1 = v ∧ u ∈ o.2)) :
    let C := coverCircuitB n (encodeOwners own)
    C.size = (own.map (fun o => o.2.length)).sum + own.length - 1 ∧
    (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
    ∀ (t : ℕ) (g : Gate), C.gates[t]? = some g → g.op = GateOp.and → ∃ c : Fin n,
      (∃ u v : Fin n, G.Adj u v ∧ OwnsDirect n C t u v) ∧
      ∀ u v : Fin n, OwnsDirect n C t u v → u = c ∨ v = c := by
  dsimp only
  have hn : ∀ o ∈ encodeOwners own, o.2 ≠ [] := by
    intro o ho
    obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
    simpa using hne o' ho'
  obtain ⟨hsize, heval⟩ := cover_all n (encodeOwners own) (encodeOwners_bounded own) hn
  refine ⟨by simpa [encodeOwners, List.map_map, Function.comp_def] using hsize, cover_monotone _ _, ?_, ?_⟩
  · intro x
    rw [heval (List.ofFn x) List.length_ofFn]
    apply Bool.eq_iff_iff.mpr
    simp only [hit, encodeOwners, List.any_map, Function.comp_def, List.any_eq_true,
      Bool.and_eq_true, read, decide_eq_true_eq]
    constructor
    · rintro ⟨o, ho, hc, v, hv, hxv⟩
      exact ⟨o.1, v, (hgraph o.1 v).mpr ⟨o, ho, Or.inl ⟨rfl, hv⟩⟩, hc, hxv⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      obtain ⟨o, ho, hcase⟩ := (hgraph u v).mp huv
      rcases hcase with ⟨rfl, hmem⟩ | ⟨rfl, hmem⟩
      · exact ⟨o, ho, hu, v, hmem, hv⟩
      · exact ⟨o, ho, hv, u, hmem, hu⟩
  · apply cover_owned_stars G own
    intro o ho v hv
    exact (hgraph o.1 v).mpr ⟨o, ho, Or.inl ⟨rfl, hv⟩⟩

end PEqualNP.Outside.L_meta_1031.StarCover
