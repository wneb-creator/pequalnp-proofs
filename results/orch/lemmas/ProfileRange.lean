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

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma signed_keys_small : ∀ a b : Fin 64,
    key (Nat.land a.val b.val) < 64 ∧
    key (Nat.land a.val (Nat.xor b.val 127)) < 64 ∧
    key (Nat.land (Nat.xor a.val 127) b.val) < 64 ∧
    key (Nat.land (Nat.xor a.val 127) (Nat.xor b.val 127)) < 64 := by
  decide +kernel

lemma canMake_small {known : List Nat} (range : ∀ z ∈ known, z < 64)
    {z : Nat} (make : canMake known z = true) : z < 64 := by
  obtain ⟨a,ha,rest⟩ := List.any_eq_true.mp make
  obtain ⟨b,hb,hit⟩ := List.any_eq_true.mp rest
  have bounds := signed_keys_small ⟨a,range a ha⟩ ⟨b,range b hb⟩
  simp only [Bool.or_eq_true, beq_iff_eq] at hit
  dsimp at bounds
  rcases hit with ((h | h) | h) | h
  · exact h ▸ bounds.1
  · exact h ▸ bounds.2.1
  · exact h ▸ bounds.2.2.1
  · exact h ▸ bounds.2.2.2

lemma builds_small {known gs : List Nat} (range : ∀ z ∈ known, z < 64)
    (build : Builds known gs) : ∀ z ∈ gs, z < 64 := by
  induction gs generalizing known with
  | nil => simp
  | cons z gs ih =>
    have zSmall := canMake_small range build.1
    have next : ∀ w ∈ z :: known, w < 64 := by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact zSmall
      · exact range w hw
    have rest := ih next build.2
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact zSmall
    · exact rest w hw

lemma seed_builds_small {gs : List Nat} (build : Builds seeds gs) :
    ∀ z ∈ gs, z < 64 := by
  apply builds_small ?_ build
  intro z hz
  simp only [seeds,List.mem_cons,List.not_mem_nil,or_false] at hz
  omega

end PEqualNP.Outside.L_meta_2592_aux.ProfileCheck
