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

end PEqualNP.Outside.L_meta_2592_aux.FastSeededMatch

namespace PEqualNP.Outside.L_meta_2592_aux.SeededRows

def rows : List Nat := [0, 63, 3, 12, 48, 21, 22, 25, 26, 37, 38, 41, 42]

def seeds : List Nat :=
  [0, 8191, 2726, 5446, 1642, 6538, 498, 7698,
    6142, 7166, 7934, 8158, 7630, 2042, 7802, 6650]

def seedValues (r : Nat) : List Bool :=
  let a := r.testBit 0
  let b := r.testBit 1
  let c := r.testBit 2
  let d := r.testBit 3
  let e := r.testBit 4
  let f := r.testBit 5
  [false, true, a, b, c, d, e, f,
    b || c || e, a || d || e, a || c || f, b || d || f,
    b || d, c || e, c || f, d || e]

def matching (r : Nat) : Bool :=
  (r.testBit 0 && r.testBit 1) ||
  (r.testBit 2 && r.testBit 3) ||
  (r.testBit 4 && r.testBit 5)

lemma seeds_semantics :
    ∀ r : Fin 13,
      seeds.map (fun mask => mask.testBit r.val) = seedValues (rows.getD r.val 0) := by
  decide +kernel

lemma target_semantics :
    ∀ r : Fin 13, (30 : Nat).testBit r.val = matching (rows.getD r.val 0) := by
  decide +kernel

lemma rows_distinct : rows.Nodup := by decide +kernel

lemma rows_small : ∀ r ∈ rows, r < 64 := by decide +kernel

def Agrees (mask : Nat) (f : Nat → Bool) : Prop :=
  ∀ r : Fin 13, mask.testBit r.val = f (rows.getD r.val 0)

lemma agrees_and {a b : Nat} {f g : Nat → Bool}
    (ha : Agrees a f) (hb : Agrees b g) :
    Agrees (a &&& b) (fun r => f r && g r) := by
  intro r
  rw [Nat.testBit_land, ha r, hb r]

lemma agrees_or {a b : Nat} {f g : Nat → Bool}
    (ha : Agrees a f) (hb : Agrees b g) :
    Agrees (a ||| b) (fun r => f r || g r) := by
  intro r
  rw [Nat.testBit_lor, ha r, hb r]

lemma agrees_not {a : Nat} {f : Nat → Bool} (ha : Agrees a f) :
    Agrees (a ^^^ 8191) (fun r => !(f r)) := by
  have mask : ∀ r : Fin 13, (8191 : Nat).testBit r.val = true := by decide +kernel
  intro r
  rw [Nat.testBit_xor, ha r, mask r]
  simp

lemma agrees_matching {a : Nat} (ha : a < 8192) (hf : Agrees a matching) : a = 30 := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 13
  · exact (hf ⟨i, hi⟩).trans (target_semantics ⟨i, hi⟩).symm
  · have hp : (2 : Nat) ^ 13 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    have haa : a < 2 ^ i := lt_of_lt_of_le ha hp
    have htt : 30 < 2 ^ i := lt_of_lt_of_le (by decide : 30 < 2 ^ 13) hp
    rw [Nat.testBit_lt_two_pow haa, Nat.testBit_lt_two_pow htt]

def generated (bank : List Nat) : List Nat :=
  bank ++ bank.map (fun a => a ^^^ 8191) ++
    bank.flatMap (fun a => bank.flatMap (fun b => [a &&& b, a ||| b]))

def choices (bank : List Nat) : List Nat := (generated bank).eraseDups

lemma choices_small {bank : List Nat} (hb : ∀ a ∈ bank, a < 8192)
    {a : Nat} (ha : a ∈ choices bank) : a < 8192 := by
  simp only [choices, List.mem_eraseDups, generated, List.mem_append,
    List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with (h | ⟨b, hbmem, rfl⟩) | ⟨b, hbmem, c, hcmem, h⟩
  · exact hb a h
  · exact Nat.xor_lt_two_pow (n := 13) (hb b hbmem) (by decide)
  · rcases h with rfl | rfl
    · exact Nat.and_lt_two_pow (n := 13) b (hb c hcmem)
    · exact Nat.or_lt_two_pow (n := 13) (hb b hbmem) (hb c hcmem)

end PEqualNP.Outside.L_meta_2592_aux.SeededRows

namespace PEqualNP.Outside.L_meta_2592_aux.FastSeededMatch

lemma matching_requires_four
    (choices_noThree : ∀ a b c, a ∈ choices seeds → b ∈ choices (a :: seeds) →
      c ∈ choices (b :: a :: seeds) → c ≠ target) (a b c : Sig)
    (ha : a ∈ choices seeds) (hb : b ∈ choices (a :: seeds))
    (hc : c ∈ choices (b :: a :: seeds))
    (hf : SeededRows.Agrees c SeededRows.matching) : False := by
  have hs : ∀ x ∈ SeededRows.seeds, x < 8192 := by decide +kernel
  have hsa : ∀ x ∈ a :: SeededRows.seeds, x < 8192 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact SeededRows.choices_small hs ha
    · exact hs x hx
  have hsb : ∀ x ∈ b :: a :: SeededRows.seeds, x < 8192 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact SeededRows.choices_small hsa hb
    · exact hsa x hx
  have ht := SeededRows.agrees_matching (SeededRows.choices_small hsb hc) hf
  exact choices_noThree a b c ha hb hc ht

end PEqualNP.Outside.L_meta_2592_aux.FastSeededMatch
