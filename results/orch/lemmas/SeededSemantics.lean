import Mathlib.Data.Nat.Bitwise

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

lemma no_matching_three
    (hcert : (choices seeds).all (fun a =>
      (choices (a :: seeds)).all (fun b => !(generated (b :: a :: seeds)).contains 30)) = true)
    (a b c : Nat) (ha : a ∈ choices seeds)
    (hb : b ∈ choices (a :: seeds)) (hc : c ∈ choices (b :: a :: seeds))
    (hf : Agrees c matching) : False := by
  have hs : ∀ x ∈ seeds, x < 8192 := by decide +kernel
  have hsa : ∀ x ∈ a :: seeds, x < 8192 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact choices_small hs ha
    · exact hs x hx
  have hsb : ∀ x ∈ b :: a :: seeds, x < 8192 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact choices_small hsa hb
    · exact hsa x hx
  have ht := agrees_matching (choices_small hsb hc) hf
  have h := List.all_eq_true.mp (List.all_eq_true.mp hcert a ha) b hb
  have hn : 30 ∉ choices (b :: a :: seeds) := by simpa [choices] using h
  exact hn (ht ▸ hc)

end PEqualNP.Outside.L_meta_2592_aux.SeededRows
