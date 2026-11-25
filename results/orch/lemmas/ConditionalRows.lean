import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2373

def edge (x : Fin 10 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5


def pairInput (a c : Fin 10) (i : Fin 10) : Bool := decide (i = a ∨ i = c)


def singleInput (c i : Fin 10) : Bool := decide (i = c)

def tripleInput (a b c i : Fin 10) : Bool := decide (i = a ∨ i = b ∨ i = c)

lemma singleton_no_edge : ∀ c : Fin 10, edge (singleInput c) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma zero_separator : ∀ a b : Fin 10, a ≠ b → ∃ c : Fin 10,
    c ≠ a ∧ c ≠ b ∧ edge (pairInput a c) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma one_separator : ∀ a b : Fin 10, a ≠ b → ∃ c : Fin 10,
    c ≠ a ∧ edge (pairInput b c) = false ∧ edge (tripleInput a b c) = true := by
  decide +kernel

lemma conditional_influence (a b : Fin 10) (hab : a ≠ b) (t : Bool) :
    ∃ x y : Fin 10 → Bool,
      (∀ i, i ≠ a → x i = y i) ∧ x b = t ∧ y b = t ∧
      x a = false ∧ y a = true ∧ edge x ≠ edge y := by
  cases t
  · obtain ⟨c, hca, hcb, he⟩ := zero_separator a b hab
    refine ⟨singleInput c, pairInput a c, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hia
      simp [singleInput, pairInput, hia]
    · simp [singleInput, Ne.symm hcb]
    · simp [pairInput, Ne.symm hab, Ne.symm hcb]
    · simp [singleInput, Ne.symm hca]
    · simp [pairInput]
    · rw [singleton_no_edge, he]
      decide
  · obtain ⟨c, hca, he0, he1⟩ := one_separator a b hab
    refine ⟨pairInput b c, tripleInput a b c, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hia
      simp [pairInput, tripleInput, hia]
    · simp [pairInput]
    · simp [tripleInput]
    · simp [pairInput, hab, Ne.symm hca]
    · simp [tripleInput]
    · rw [he0, he1]
      decide

def boolBin (d : Nat) (a b : Bool) : Bool :=
  if d = 0 then a && b else if d = 1 then a || b else
    if d = 2 then a && !b else !a && b

lemma no_binary_identification_left (d : Nat) (hd : d < 4) (a b : Fin 10)
    (hab : a ≠ b) : ∃ x y : Fin 10 → Bool,
      (∀ i, i ≠ a → x i = y i) ∧
      boolBin d (x a) (x b) = boolBin d (y a) (y b) ∧ edge x ≠ edge y := by
  obtain ⟨x, y, same, xb, yb, xa, ya, different⟩ :=
    conditional_influence a b hab (decide (d = 1 ∨ d = 2))
  refine ⟨x, y, same, ?_, different⟩
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;> simp_all [boolBin]


namespace Live1024

abbrev Sig := BitVec 1024
abbrev Row := Fin 1024

def zero : Sig := 0

def bit (i : Row) (a : Sig) : Bool := a.getLsbD i.val

def bin (d : Nat) (a b : Sig) : Sig :=
  if d = 0 then a &&& b else if d = 1 then a ||| b else
    if d = 2 then a &&& ~~~b else ~~~a &&& b

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
  0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
  0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8


def singleRow (c : Fin 10) : Row := Fin.ofNat 1024 (1 <<< c.val)

def pairRow (a c : Fin 10) : Row := Fin.ofNat 1024 ((1 <<< a.val) ||| (1 <<< c.val))

def tripleRow (a b c : Fin 10) : Row :=
  Fin.ofNat 1024 ((1 <<< a.val) ||| (1 <<< b.val) ||| (1 <<< c.val))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma singleRow_input : ∀ c i : Fin 10,
    bit (singleRow c) (inputs.getD i.val zero) = singleInput c i := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma pairRow_input : ∀ a c i : Fin 10,
    bit (pairRow a c) (inputs.getD i.val zero) = pairInput a c i := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tripleRow_input : ∀ a b c i : Fin 10,
    bit (tripleRow a b c) (inputs.getD i.val zero) = tripleInput a b c i := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma singleRow_graph : ∀ c : Fin 10,
    bit (singleRow c) graph = PEqualNP.Outside.L_meta_2373.edge (singleInput c) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma pairRow_graph : ∀ a c : Fin 10,
    bit (pairRow a c) graph = PEqualNP.Outside.L_meta_2373.edge (pairInput a c) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tripleRow_graph : ∀ a b c : Fin 10,
    bit (tripleRow a b c) graph = PEqualNP.Outside.L_meta_2373.edge (tripleInput a b c) := by
  decide +kernel

lemma conditional_influence_rows (a b : Fin 10) (hab : a ≠ b) (t : Bool) :
    ∃ r s : Row,
      (∀ i : Fin 10, i ≠ a →
        bit r (inputs.getD i.val zero) = bit s (inputs.getD i.val zero)) ∧
      bit r (inputs.getD b.val zero) = t ∧ bit s (inputs.getD b.val zero) = t ∧
      bit r graph ≠ bit s graph := by
  cases t
  · obtain ⟨c, hca, hcb, he⟩ := zero_separator a b hab
    refine ⟨singleRow c, pairRow a c, ?_, ?_, ?_, ?_⟩
    · intro i hia
      rw [singleRow_input, pairRow_input]
      simp [singleInput, pairInput, hia]
    · rw [singleRow_input]
      simp [singleInput, Ne.symm hcb]
    · rw [pairRow_input]
      simp [pairInput, Ne.symm hab, Ne.symm hcb]
    · rw [singleRow_graph, pairRow_graph, singleton_no_edge, he]
      decide
  · obtain ⟨c, hca, he0, he1⟩ := one_separator a b hab
    refine ⟨pairRow b c, tripleRow a b c, ?_, ?_, ?_, ?_⟩
    · intro i hia
      rw [pairRow_input, tripleRow_input]
      simp [pairInput, tripleInput, hia]
    · rw [pairRow_input]
      simp [pairInput]
    · rw [tripleRow_input]
      simp [tripleInput]
    · rw [pairRow_graph, tripleRow_graph, he0, he1]
      decide

lemma bit_bin_eq_boolBin (r : Row) (d : Nat) (a b : Sig) :
    bit r (bin d a b) = boolBin d (bit r a) (bit r b) := by
  unfold bin boolBin
  split_ifs <;> simp [bit, r.isLt]

lemma no_binary_identification_left_rows (d : Nat) (hd : d < 4) (a b : Fin 10)
    (hab : a ≠ b) : ∃ r s : Row,
      (∀ i : Fin 10, i ≠ a →
        bit r (inputs.getD i.val zero) = bit s (inputs.getD i.val zero)) ∧
      bit r (bin d (inputs.getD a.val zero) (inputs.getD b.val zero)) =
        bit s (bin d (inputs.getD a.val zero) (inputs.getD b.val zero)) ∧
      bit r graph ≠ bit s graph := by
  obtain ⟨r, s, same, xb, yb, different⟩ :=
    conditional_influence_rows a b hab (decide (d = 1 ∨ d = 2))
  refine ⟨r, s, same, ?_, different⟩
  rw [bit_bin_eq_boolBin, bit_bin_eq_boolBin]
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;> simp_all [boolBin]

end Live1024

end PEqualNP.Outside.L_meta_2373
