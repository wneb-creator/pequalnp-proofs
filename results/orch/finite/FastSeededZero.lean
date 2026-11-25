import Mathlib.Data.Nat.Bitwise

namespace PEqualNP.Outside.L_meta_2592_aux.FastSeededMatch

abbrev Sig := Nat

def inv (a : Sig) : Sig := a ^^^ 8191

def target : Sig := 30

def seeds : List Sig :=
  [0, 8191, 2726, 5446, 1642, 6538, 498, 7698,
    6142, 7166, 7934, 8158, 7630, 2042, 7802, 6650]

def generated (bank : List Sig) : List Sig :=
  bank ++ bank.map (fun a => inv a) ++
    bank.flatMap (fun a => bank.flatMap (fun b => [a &&& b, a ||| b]))

def choices (bank : List Sig) : List Sig := (generated bank).eraseDups

def Safe (bank : List Sig) : Prop :=
  (∀ a ∈ bank, a ≠ target) ∧
  (∀ a ∈ bank, inv a ≠ target) ∧
  (∀ a ∈ bank, ∀ b ∈ bank, a &&& b ≠ target ∧ a ||| b ≠ target)

def newOK (bank : List Sig) (a : Sig) : Bool :=
  decide (a ≠ target ∧ inv a ≠ target) &&
    bank.all (fun b => decide (a &&& b ≠ target ∧ a ||| b ≠ target))

lemma safe_cons {bank : List Sig} (hs : Safe bank) {a : Sig}
    (ha : newOK bank a = true) : Safe (a :: bank) := by
  simp only [newOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ha
  rcases ha with ⟨⟨ha, hn⟩, hb⟩
  refine ⟨?_, ?_, ?_⟩
  · intro b hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact ha
    · exact hs.1 b hmem
  · intro b hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hn
    · exact hs.2.1 b hmem
  · intro b hbm c hcm
    rcases List.mem_cons.mp hbm with hba | hbB
    · subst b
      rcases List.mem_cons.mp hcm with rfl | hcB
      · simpa using And.intro ha ha
      · exact hb c hcB
    · rcases List.mem_cons.mp hcm with hca | hcB
      · subst c
        simpa [Nat.and_comm, Nat.or_comm] using hb b hbB
      · exact hs.2.2 b hbB c hcB

lemma safe_choices {bank : List Sig} (hs : Safe bank) {a : Sig}
    (ha : a ∈ choices bank) : a ≠ target := by
  simp only [choices, List.mem_eraseDups, generated, List.mem_append,
    List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with (h | ⟨b, hb, rfl⟩) | ⟨b, hb, c, hc, h⟩
  · exact hs.1 a h
  · exact hs.2.1 b hb
  · rcases h with rfl | rfl
    · exact (hs.2.2 b hb c hc).1
    · exact (hs.2.2 b hb c hc).2

lemma seeds_safe : Safe seeds := by
  unfold Safe
  decide +kernel

def afterFirst (a : Sig) : Bool :=
  newOK seeds a && (choices (a :: seeds)).all (fun b => newOK (a :: seeds) b)

def noThree : Bool := (choices seeds).all afterFirst

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma checked_zero : afterFirst 0 = true := by decide +kernel

end PEqualNP.Outside.L_meta_2592_aux.FastSeededMatch
