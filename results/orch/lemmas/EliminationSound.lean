import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bitwise

namespace PEqualNP.Outside.L_meta_2592_aux.ProfileCheck

def key (m : Nat) : Nat := min m (Nat.xor m 127)

def seeds : List Nat := [0, 2, 4, 8, 16, 32, 63]

def targets : List Nat := [15, 22, 42, 51]

def extras : List Nat := (List.range 64).filter fun a =>
  !(seeds.contains a || targets.contains a)

def canMake (known : List Nat) (z : Nat) : Bool :=
  known.any fun a => known.any fun b =>
    key (Nat.land a b) == z ||
    key (Nat.land a (Nat.xor b 127)) == z ||
    key (Nat.land (Nat.xor a 127) b) == z ||
    key (Nat.land (Nat.xor a 127) (Nat.xor b 127)) == z

def extend (candidates known : List Nat) : List Nat :=
  candidates.foldl (fun seen z =>
    if seen.contains z then seen
    else if canMake seen z then z :: seen
    else seen) known

def closure (a b c : Nat) : List Nat :=
  (List.range 7).foldl (fun seen _ => extend (targets ++ [a,b,c]) seen) seeds

def missing (a b c : Nat) : Bool :=
  let seen := closure a b c
  (seeds.all fun t => seen.contains t) &&
  ((targets ++ [a,b,c]).all fun t => !(canMake seen t) || seen.contains t) &&
  !(targets.all fun t => seen.contains t)

def checked : Bool :=
  extras.all fun a => extras.all fun b =>
    !(decide (a < b)) || extras.all fun c => !(decide (b < c)) || missing a b c

def Builds (known : List Nat) : List Nat → Prop
  | [] => True
  | z :: tail => canMake known z = true ∧ Builds (z :: known) tail

lemma canMake_mono {known seen : List Nat} (h : known ⊆ seen) {z : Nat}
    (hz : canMake known z = true) : canMake seen z = true := by
  obtain ⟨a,ha,bits⟩ := List.any_eq_true.mp hz
  obtain ⟨b,hb,hit⟩ := List.any_eq_true.mp bits
  exact List.any_eq_true.mpr ⟨a,h ha,List.any_eq_true.mpr ⟨b,h hb,hit⟩⟩

lemma builds_within {allowed seen known gs : List Nat}
    (initial : known ⊆ seen)
    (closed : ∀ z ∈ allowed, canMake seen z = true → z ∈ seen)
    (build : Builds known gs) (bounded : gs ⊆ allowed) : gs ⊆ seen := by
  induction gs generalizing known with
  | nil => simp
  | cons z gs ih =>
    obtain ⟨make,rest⟩ := build
    have hz := closed z (bounded List.mem_cons_self) (canMake_mono initial make)
    have inside : z :: known ⊆ seen := by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hz
      · exact initial hw
    have tail := ih inside rest (fun w hw => bounded (List.mem_cons_of_mem z hw))
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hz
    · exact tail hw

lemma obstruction (hc : checked = true) {a b c : Nat}
    (ha : a ∈ extras) (hb : b ∈ extras) (hc' : c ∈ extras)
    (ab : a < b) (bc : b < c) :
    seeds ⊆ closure a b c ∧
    (∀ z ∈ targets ++ [a,b,c], canMake (closure a b c) z = true → z ∈ closure a b c) ∧
    ¬ targets ⊆ closure a b c := by
  have aa := List.all_eq_true.mp hc a ha
  have bb := List.all_eq_true.mp aa b hb
  simp only [ab, decide_true, Bool.not_true, Bool.false_or] at bb
  have cc := List.all_eq_true.mp bb c hc'
  simp only [bc, decide_true, Bool.not_true, Bool.false_or] at cc
  unfold missing at cc
  simp only [Bool.and_eq_true] at cc
  obtain ⟨⟨initial,closed⟩,notAll⟩ := cc
  refine ⟨?_,?_,?_⟩
  · intro z hz
    exact List.contains_iff_mem.mp (List.all_eq_true.mp initial z hz)
  · intro z hz make
    have fact := List.all_eq_true.mp closed z hz
    simpa only [make,Bool.not_true,Bool.false_or,List.contains_iff_mem] using fact
  · intro all
    have yes : targets.all (fun z => (closure a b c).contains z) = true :=
      List.all_eq_true.mpr fun z hz => List.contains_iff_mem.mpr (all hz)
    rw [yes] at notAll
    cases notAll

lemma no_build_on_three_helpers (hc : checked = true) {a b c : Nat}
    (ha : a ∈ extras) (hb : b ∈ extras) (hc' : c ∈ extras)
    (ab : a < b) (bc : b < c) {gs : List Nat}
    (build : Builds seeds gs) (bounded : gs ⊆ targets ++ [a,b,c])
    (outputs : targets ⊆ gs ++ seeds) : False := by
  obtain ⟨initial,closed,missing⟩ := obstruction hc ha hb hc' ab bc
  have within := builds_within initial closed build bounded
  apply missing
  intro z hz
  rcases List.mem_append.mp (outputs hz) with hz | hz
  · exact within hz
  · exact initial hz

end PEqualNP.Outside.L_meta_2592_aux.ProfileCheck
