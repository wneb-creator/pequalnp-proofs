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


namespace PackingThree

def touchCount (bs : List Block) (r : Nat) : Nat :=
  (bs.filter fun b => b.active.testBit r).length

def traceState (bs : List Block) : State := bs.foldl step emptyState

lemma traceState_append_singleton (bs : List Block) (b : Block) :
    traceState (bs ++ [b]) = step (traceState bs) b := by
  simp [traceState]

lemma touchCount_append (as bs : List Block) (r : Nat) :
    touchCount (as ++ bs) r = touchCount as r + touchCount bs r := by
  simp [touchCount, List.filter_append]

lemma touchCount_cons (b : Block) (bs : List Block) (r : Nat) :
    touchCount (b :: bs) r = (if b.active.testBit r then 1 else 0) + touchCount bs r := by
  cases hb : b.active.testBit r <;> simp [touchCount, hb, Nat.add_comm]

lemma touchCount_append_singleton (bs : List Block) (b : Block) (r : Nat) :
    touchCount (bs ++ [b]) r = touchCount bs r + (if b.active.testBit r then 1 else 0) := by
  rw [touchCount_append]
  cases hb : b.active.testBit r <;> simp [touchCount, hb]

lemma trace_used (bs : List Block) (r : Nat) :
    (traceState bs).used.testBit r = true ↔
      ∃ b ∈ bs, b.vertices.testBit r = true := by
  induction bs using List.reverseRecOn with
  | nil => simp [traceState, emptyState]
  | append_singleton bs b ih =>
    rw [traceState_append_singleton]
    change ((traceState bs).used ||| b.vertices).testBit r = true ↔ _
    rw [Nat.testBit_lor, Bool.or_eq_true]
    constructor
    · rintro (h | h)
      · obtain ⟨c, hc, hv⟩ := ih.mp h
        exact ⟨c, List.mem_append.mpr (Or.inl hc), hv⟩
      · exact ⟨b, by simp, h⟩
    · rintro ⟨c, hc, hv⟩
      rcases List.mem_append.mp hc with hc | hc
      · exact Or.inl (ih.mpr ⟨c, hc, hv⟩)
      · have he : c = b := by simpa using hc
        subst c
        exact Or.inr hv

lemma trace_rows (bs : List Block) (r : Nat) :
    ((traceState bs).seen.testBit r = true ↔ 1 ≤ touchCount bs r) ∧
    ((traceState bs).twice.testBit r = true ↔ 2 ≤ touchCount bs r) ∧
    ((traceState bs).thrice.testBit r = true ↔ 3 ≤ touchCount bs r) := by
  induction bs using List.reverseRecOn with
  | nil => simp [traceState, emptyState, touchCount]
  | append_singleton bs b ih =>
    simp only [traceState_append_singleton, touchCount_append_singleton, step,
      Nat.testBit_lor, Nat.testBit_land, Bool.or_eq_true, Bool.and_eq_true,
      ih.1, ih.2.1, ih.2.2]
    cases b.active.testBit r <;> simp
    omega

lemma trace_count (bs : List Block) : (traceState bs).count = bs.length := by
  induction bs using List.reverseRecOn with
  | nil => rfl
  | append_singleton bs b ih =>
    rw [traceState_append_singleton]
    simpa [step] using congrArg (fun n : Nat => n + 1) ih

lemma trace_disjoint_bits (a b : Nat) (h : a &&& b = 0) (r : Nat) :
    ¬ (a.testBit r = true ∧ b.testBit r = true) := by
  rintro ⟨ha, hb⟩
  have hi := congrArg (fun n : Nat => n.testBit r) h
  rw [Nat.testBit_land, ha, hb] at hi
  simp at hi

lemma trace_and_zero (a b : Nat)
    (h : ∀ r, ¬ (a.testBit r = true ∧ b.testBit r = true)) : a &&& b = 0 := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [Nat.testBit_land]
  cases ha : a.testBit r with
  | false => simp
  | true =>
    cases hb : b.testBit r with
    | false => simp
    | true => exact False.elim (h r ⟨ha, hb⟩)

lemma validTrace_prefix (pre rest : List Block)
    (hpair : (pre ++ rest).Pairwise fun b c => b.vertices &&& c.vertices = 0)
    (hquota : ∀ r, touchCount (pre ++ rest) r ≤ 3) :
    PackingPrunedDFS.validTrace ok step (traceState pre) rest = true := by
  induction rest generalizing pre with
  | nil => rfl
  | cons b bs ih =>
    have hu : (traceState pre).used &&& b.vertices = 0 := by
      apply trace_and_zero
      intro r hr
      obtain ⟨c, hc, hv⟩ := (trace_used pre r).mp hr.1
      have hcb : c.vertices &&& b.vertices = 0 :=
        (List.pairwise_append.mp hpair).2.2 c hc b (by simp)
      exact trace_disjoint_bits _ _ hcb r ⟨hv, hr.2⟩
    have ht : (traceState pre).thrice &&& b.active = 0 := by
      apply trace_and_zero
      intro r hr
      have hc : 3 ≤ touchCount pre r := (trace_rows pre r).2.2.mp hr.1
      have hq := hquota r
      rw [touchCount_append, touchCount_cons] at hq
      simp only [hr.2, ↓reduceIte] at hq
      omega
    have hok : ok (traceState pre) b = true := by simp [ok, hu, ht]
    rw [PackingPrunedDFS.validTrace, hok, Bool.true_and]
    have hp : ((pre ++ [b]) ++ bs).Pairwise fun c d => c.vertices &&& d.vertices = 0 := by
      simpa [List.append_assoc] using hpair
    have hq : ∀ r, touchCount ((pre ++ [b]) ++ bs) r ≤ 3 := by
      simpa [List.append_assoc] using hquota
    simpa only [traceState_append_singleton] using ih (pre ++ [b]) hp hq

lemma validTrace_of_packing (bs : List Block)
    (hpair : bs.Pairwise fun b c => b.vertices &&& c.vertices = 0)
    (hquota : ∀ r, touchCount bs r ≤ 3) :
    PackingPrunedDFS.validTrace ok step emptyState bs = true := by
  simpa [traceState] using
    validTrace_prefix [] bs (by simpa using hpair) (by simpa using hquota)

end PackingThree

end PEqualNP.Outside.L_meta_1896_aux
