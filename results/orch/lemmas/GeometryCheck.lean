import Mathlib

namespace PEqualNP.Outside.L_meta_2592.Binary17

abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩


abbrev Wire (R : Type) := R → Bool

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r


def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]

def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8

namespace Extended

abbrev Sig := BitVec 1024
def zero : Sig := 0
def one : Sig := BitVec.allOnes 1024
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b

def bit (i : Fin 1024) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩


abbrev Row := Fin 1024

def observe (a : Sig) : Wire Row := fun r => bit r a

def pins : List Sig := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc]

def target : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8

end Extended

namespace Geometry

def pin (i : Fin 10) : Extended.Sig :=
  Extended.pins.getD i.val Extended.zero

def position : Fin 10 → Nat := ![9, 7, 5, 8, 6, 4, 2, 0, 3, 1]

def relabel : Fin 10 → Fin 10 → Fin 10 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], ![1, 0, 4, 3, 2, 6, 5, 9, 8, 7], ![2, 1, 0, 4, 3, 7, 6, 5, 9, 8], ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6], ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5], ![1, 2, 3, 8, 6, 0, 7, 4, 5, 9], ![2, 1, 6, 8, 3, 7, 0, 9, 5, 4], ![2, 3, 4, 9, 7, 1, 8, 0, 6, 5], ![2, 3, 8, 5, 7, 1, 4, 6, 0, 9], ![2, 3, 8, 6, 1, 7, 4, 5, 9, 0]]

lemma relabel_self : ∀ v : Fin 10, relabel v v = 0 := by decide

lemma relabel_bijective : ∀ v : Fin 10, Function.Bijective (relabel v) := by decide

def embedV (v : Fin 10) (r : Row) : Extended.Row :=
  Fin.ofNat 1024 ((List.ofFn (fun i : Fin 10 =>
    if r.val.testBit (position (relabel v i)) then 2 ^ position i else 0)).sum)

def projectV (v : Fin 10) (a : Extended.Sig) : Sig :=
  table (fun r => Extended.bit (embedV v r) a)

lemma observe_projectV (v : Fin 10) (a : Extended.Sig) :
    restrictRows (embedV v) (Extended.observe a) = observe (projectV v a) := by
  funext r
  exact (bit_table (fun r => Extended.bit (embedV v r) a) r).symm

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma project_target : ∀ v : Fin 10, projectV v Extended.target = graph := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma project_pin : ∀ v i : Fin 10,
    projectV v (pin i) = zero ∨ projectV v (pin i) ∈ inputs := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma project_self : ∀ v : Fin 10, projectV v (pin v) = zero := by
  decide +kernel

lemma project_bin_commute (v : Fin 10) (d : Nat) (a b : Extended.Sig) :
    projectV v (Extended.bin d a b) = bin d (projectV v a) (projectV v b) := by
  apply bit_ext
  intro r
  simp only [projectV, bit_table, Extended.bit_bin, bit_bin]

lemma bin_zero_left (d : Fin 4) (a : Sig) :
    bin d.val zero a = if d.val = 0 ∨ d.val = 2 then zero else a := by
  apply bit_ext
  intro r
  fin_cases d <;> simp [bit_bin, bit_zero]

lemma project_bin (v u : Fin 10) (d : Fin 4) :
    projectV v (Extended.bin d.val (pin v) (pin u)) = zero ∨
      projectV v (Extended.bin d.val (pin v) (pin u)) = one ∨
      projectV v (Extended.bin d.val (pin v) (pin u)) ∈ inputs ∨
      neg (projectV v (Extended.bin d.val (pin v) (pin u))) ∈ inputs := by
  rw [project_bin_commute, project_self, bin_zero_left]
  split_ifs
  · exact Or.inl rfl
  · rcases project_pin v u with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))

def witnessBase : Fin 10 → Fin 10 → Fin 4 → Extended.Row :=
  ![![![0, 0, 0, 0], ![16, 128, 128, 16], ![16, 48, 48, 16], ![16, 272, 272, 16], ![16, 64, 64, 16], ![64, 16, 16, 64], ![16, 20, 20, 16], ![16, 65, 65, 16], ![16, 72, 72, 16], ![16, 18, 18, 16]], ![![4, 512, 512, 4], ![0, 0, 0, 0], ![4, 32, 32, 4], ![4, 260, 260, 4], ![4, 68, 68, 4], ![4, 20, 20, 4], ![32, 4, 4, 32], ![4, 5, 5, 4], ![4, 40, 40, 4], ![4, 34, 34, 4]], ![![1, 513, 513, 1], ![1, 128, 128, 1], ![0, 0, 0, 0], ![1, 256, 256, 1], ![1, 65, 65, 1], ![1, 144, 144, 1], ![1, 5, 5, 1], ![128, 1, 1, 128], ![1, 9, 9, 1], ![1, 130, 130, 1]], ![![8, 520, 520, 8], ![8, 136, 136, 8], ![8, 32, 32, 8], ![0, 0, 0, 0], ![8, 64, 64, 8], ![8, 48, 48, 8], ![8, 36, 36, 8], ![8, 9, 9, 8], ![32, 8, 8, 32], ![8, 10, 10, 8]], ![![2, 512, 512, 2], ![2, 130, 130, 2], ![2, 34, 34, 2], ![2, 256, 256, 2], ![0, 0, 0, 0], ![2, 18, 18, 2], ![2, 260, 260, 2], ![2, 257, 257, 2], ![2, 10, 10, 2], ![256, 2, 2, 256]], ![![1, 512, 512, 1], ![1, 129, 129, 1], ![1, 40, 40, 1], ![1, 257, 257, 1], ![1, 65, 65, 1], ![0, 0, 0, 0], ![1, 5, 5, 1], ![8, 1, 1, 8], ![1, 8, 8, 1], ![1, 10, 10, 1]], ![![2, 514, 514, 2], ![2, 128, 128, 2], ![2, 34, 34, 2], ![2, 258, 258, 2], ![2, 72, 72, 2], ![2, 18, 18, 2], ![0, 0, 0, 0], ![2, 9, 9, 2], ![2, 8, 8, 2], ![8, 2, 2, 8]], ![![2, 514, 514, 2], ![2, 130, 130, 2], ![2, 32, 32, 2], ![2, 258, 258, 2], ![2, 80, 80, 2], ![2, 16, 16, 2], ![2, 20, 20, 2], ![0, 0, 0, 0], ![2, 10, 10, 2], ![16, 2, 2, 16]], ![![4, 516, 516, 4], ![4, 144, 144, 4], ![4, 36, 36, 4], ![4, 256, 256, 4], ![4, 68, 68, 4], ![4, 16, 16, 4], ![16, 4, 4, 16], ![4, 5, 5, 4], ![0, 0, 0, 0], ![4, 18, 18, 4]], ![![1, 513, 513, 1], ![1, 129, 129, 1], ![1, 36, 36, 1], ![1, 257, 257, 1], ![1, 64, 64, 1], ![1, 20, 20, 1], ![1, 4, 4, 1], ![4, 1, 1, 4], ![1, 9, 9, 1], ![0, 0, 0, 0]]]

def witness (v u : Fin 10) (d : Fin 4) : Extended.Row × Extended.Row :=
  let r := witnessBase v u d
  (r, Fin.ofNat 1024 (r.val + 2 ^ position v))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma witness_target : ∀ (v u : Fin 10) (d : Fin 4), v ≠ u →
    Extended.bit (witness v u d).1 Extended.target ≠
      Extended.bit (witness v u d).2 Extended.target := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma witness_other_pin : ∀ (v u : Fin 10) (d : Fin 4) (i : Fin 10), i ≠ v →
    Extended.bit (witness v u d).1 (pin i) =
      Extended.bit (witness v u d).2 (pin i) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma witness_binary : ∀ (v u : Fin 10) (d : Fin 4), v ≠ u →
    Extended.bit (witness v u d).1 (Extended.bin d.val (pin v) (pin u)) =
      Extended.bit (witness v u d).2 (Extended.bin d.val (pin v) (pin u)) := by
  decide +kernel

lemma pins_eq : Extended.pins = List.ofFn pin := by rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma pin_injective : Function.Injective pin := by decide +kernel

end Geometry

end PEqualNP.Outside.L_meta_2592.Binary17
