import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896_aux

namespace PackingThree

structure Block where
  vertices : Nat
  active : Nat
  edges : Nat

structure State where
  used : Nat
  covered : Nat
  seen : Nat
  twice : Nat
  thrice : Nat
  count : Nat

def emptyState : State := ⟨0, 0, 0, 0, 0, 0⟩

def ok (s : State) (b : Block) : Bool :=
  (s.used &&& b.vertices == 0) && (s.thrice &&& b.active == 0)

def step (s : State) (b : Block) : State :=
  ⟨s.used ||| b.vertices, s.covered ||| b.edges,
   s.seen ||| b.active, s.twice ||| (s.seen &&& b.active),
   s.thrice ||| (s.twice &&& b.active), s.count + 1⟩

def flagCount (mask : Nat) : Nat :=
  (Finset.univ.filter fun a : Fin 52 => mask.testBit a.val).card

def good (s : State) : Bool := decide (flagCount s.covered ≤ 29 + s.count)

def upperEdges (s : State) (bs : List Block) : Nat :=
  bs.foldl (fun mask b => mask ||| b.edges) s.covered

def prune (s : State) (bs : List Block) : Bool :=
  decide (flagCount (upperEdges s bs) ≤ 29 + s.count)

end PackingThree

namespace PackingPrunedDFS

variable {α σ : Type}

def branches (ok : σ → α → Bool) (step : σ → α → σ)
    (recur : σ → List α → Bool) (s : σ) : List α → Bool
  | [] => true
  | b :: bs =>
      (if ok s b then recur (step s b) (bs.filter (ok (step s b))) else true) &&
        branches ok step recur s bs

def check (ok : σ → α → Bool) (step : σ → α → σ)
    (good : σ → Bool) (prune : σ → List α → Bool) : Nat → σ → List α → Bool
  | 0, s, bs => good s && bs.isEmpty
  | fuel + 1, s, bs =>
      if prune s bs then true
      else good s && branches ok step (check ok step good prune fuel) s bs

def validTrace (ok : σ → α → Bool) (step : σ → α → σ) : σ → List α → Bool
  | _, [] => true
  | s, b :: bs => ok s b && validTrace ok step (step s b) bs

end PackingPrunedDFS

namespace PackingPrunedDFS

variable {α σ : Type}

def branchAt (ok : σ → α → Bool) (step : σ → α → σ)
    (recur : σ → List α → Bool) (s : σ) (bs : List α) (i : Nat) : Bool :=
  match bs.drop i with
  | [] => true
  | b :: rest =>
      if ok s b then recur (step s b) (rest.filter (ok (step s b))) else true

def chunk (ok : σ → α → Bool) (step : σ → α → σ)
    (recur : σ → List α → Bool) (s : σ) (bs : List α)
    (start count : Nat) : Bool :=
  (List.range count).all (fun j => branchAt ok step recur s bs (start + j))

end PackingPrunedDFS


namespace PackingPrunedDFS

variable {α σ : Type}

lemma branchAt_cons_succ (ok : σ → α → Bool) (step : σ → α → σ)
    (recur : σ → List α → Bool) (s : σ) (b : α) (bs : List α) (i : Nat) :
    branchAt ok step recur s (b :: bs) (i + 1) = branchAt ok step recur s bs i := by
  rfl

lemma branches_of_branchAt (ok : σ → α → Bool) (step : σ → α → σ)
    (recur : σ → List α → Bool) (s : σ) (bs : List α)
    (h : ∀ i < bs.length, branchAt ok step recur s bs i = true) :
    branches ok step recur s bs = true := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [branches, Bool.and_eq_true]
    constructor
    · exact h 0 (by simp)
    · apply ih
      intro i hi
      have hh := h (i + 1) (by simp; omega)
      exact hh

lemma branchAt_of_chunk (ok : σ → α → Bool) (step : σ → α → σ)
    (recur : σ → List α → Bool) (s : σ) (bs : List α)
    (start count offset : Nat)
    (h : chunk ok step recur s bs start count = true) (hoffset : offset < count) :
    branchAt ok step recur s bs (start + offset) = true := by
  unfold chunk at h
  exact (List.all_eq_true.mp h) offset (List.mem_range.mpr hoffset)

lemma branches_of_chunk_cover (ok : σ → α → Bool) (step : σ → α → σ)
    (recur : σ → List α → Bool) (s : σ) (bs : List α)
    (intervals : List (Nat × Nat))
    (hchunks : ∀ p ∈ intervals, chunk ok step recur s bs p.1 p.2 = true)
    (hcover : ∀ i < bs.length, ∃ p ∈ intervals, p.1 ≤ i ∧ i < p.1 + p.2) :
    branches ok step recur s bs = true := by
  apply branches_of_branchAt
  intro i hi
  obtain ⟨p, hp, hstart, hend⟩ := hcover i hi
  have hoffset : i - p.1 < p.2 := by omega
  have hsum : p.1 + (i - p.1) = i := by omega
  have h := branchAt_of_chunk ok step recur s bs p.1 p.2 (i - p.1)
    (hchunks p hp) hoffset
  simpa only [hsum] using h

lemma branches_of_full_chunk (ok : σ → α → Bool) (step : σ → α → σ)
    (recur : σ → List α → Bool) (s : σ) (bs : List α)
    (h : chunk ok step recur s bs 0 bs.length = true) :
    branches ok step recur s bs = true := by
  apply branches_of_branchAt
  intro i hi
  simpa only [Nat.zero_add] using branchAt_of_chunk ok step recur s bs 0 bs.length i h hi

end PackingPrunedDFS

end PEqualNP.Outside.L_meta_1896_aux
