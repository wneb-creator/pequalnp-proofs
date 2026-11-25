import CountTableChecker
import CountDagCheck

namespace PEqualNP.Outside.L_meta_2373.Weak80905
open Live1024 CountVector

def s1 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def s2 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def s3 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def s4 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def s5 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def s6 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def s7 : Sig := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def s8 : Sig := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
def s9 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000
def s10 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def s12 : Sig := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def s34 : Sig := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f000
def s138 : Sig := 0xffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeeeffffffffffffffffeeeeeeeeeeeeeeee
def s4786 : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffafff0fffafff0fffafff0fffafff0fffafff0fffafff0fffafff0fffafff0fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffafff0fffafff0fffafff0fffafff0fffafff0fffafff0fffafff0fffafff0
def s13864 : Sig := 0xfffffffffffffffffeeefeeefeeefeeefffffffffffffffffeeefeeefeeefeeefffffffffffffffffeeefeeefeeefeeefffffffffffffffffeeefeeefeeefeeefffffffffffffffffeeefeeefeeefeeefffffffffffffffffeeefeeefeeefeeefffffffffffffffffeeefeeefeeefeeefffffffffffffffffeeefeeefeeefeee
def s15934 : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffffeeefeeefeeefeeefffffffffffffffffffffffffffffffffffffffffffffffffeeefeeefeeefeeefffffffffffffffffffffffffffffffffffffffffffffffffeeefeeefeeefeeefffffffffffffffffffffffffffffffffffffffffffffffffeeefeeefeeefeee
def s29951 : Sig := 0xfffffffffffffffffeeefeeefeeefeee00000000000000000000000000000000fffffffffffffffffeeefeeefeeefeee00000000000000000000000000000000fffffffffffffffffeeefeeefeeefeee00000000000000000000000000000000fffffffffffffffffeeefeeefeeefeee00000000000000000000000000000000
def s30561 : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0fffffff0fffffff0fffffff0fffffff0fffffff0fffffff0fffffff0fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0

def signal : Fin 11 → Sig := ![s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s13864]
def unit (i : Fin 11) : Fin 11 → Nat := fun j => if i = j then 1 else 0
def entries : List (CountEntry 11) := List.ofFn (fun i : Fin 11 => (unit i, signal i))
def sources : List (Sum (Fin 11) (Nat × Nat × Nat)) := List.ofFn (fun i : Fin 11 => Sum.inl i)
lemma checked_provenance : dagCheck false signal entries sources = true := by decide +kernel

def total76616 : Fin 11 → Nat := ![1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2]
def cuts76616 : List (CountEntry 11) := [(![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], s29951), (![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1], s15934)]
def rows76616 : List (Row × Row) := [(⟨24, by decide⟩, ⟨116, by decide⟩), (⟨264, by decide⟩, ⟨201, by decide⟩), (⟨528, by decide⟩, ⟨773, by decide⟩), (⟨640, by decide⟩, ⟨201, by decide⟩), (⟨288, by decide⟩, ⟨402, by decide⟩), (⟨12, by decide⟩, ⟨201, by decide⟩), (⟨6, by decide⟩, ⟨773, by decide⟩), (⟨33, by decide⟩, ⟨104, by decide⟩), (⟨66, by decide⟩, ⟨50, by decide⟩), (⟨528, by decide⟩, ⟨116, by decide⟩), (⟨3, by decide⟩, ⟨201, by decide⟩), (⟨24, by decide⟩, ⟨138, by decide⟩), (⟨132, by decide⟩, ⟨385, by decide⟩), (⟨3, by decide⟩, ⟨138, by decide⟩), (⟨6, by decide⟩, ⟨50, by decide⟩), (⟨24, by decide⟩, ⟨208, by decide⟩), (⟨66, by decide⟩, ⟨138, by decide⟩), (⟨264, by decide⟩, ⟨521, by decide⟩)]
def tag76616 : Fin 13 → Fin 11 := ![0, 1, 2, 3, 4, 5, 6, 7, 7, 8, 9, 10, 10]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma checked_gates76616 : countGateCheck false graph total76616 signal entries cuts76616 rows76616 = true := by decide +kernel
lemma checked_leaves76616 : countLeafCheck total76616 signal entries = true := by decide +kernel
lemma missing76616 : (total76616, graph) ∉ entries := by decide +kernel
lemma counts76616 : count tag76616 (Finset.univ : Finset (Fin 13)) = total76616 := by
  funext j; fin_cases j <;> decide +kernel

def total80905 : Fin 11 → Nat := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2]
def cuts80905 : List (CountEntry 11) := []
def rows80905 : List (Row × Row) := [(⟨24, by decide⟩, ⟨116, by decide⟩), (⟨264, by decide⟩, ⟨201, by decide⟩), (⟨528, by decide⟩, ⟨773, by decide⟩), (⟨640, by decide⟩, ⟨201, by decide⟩), (⟨132, by decide⟩, ⟨116, by decide⟩), (⟨288, by decide⟩, ⟨773, by decide⟩), (⟨6, by decide⟩, ⟨770, by decide⟩), (⟨3, by decide⟩, ⟨201, by decide⟩), (⟨17, by decide⟩, ⟨116, by decide⟩), (⟨3, by decide⟩, ⟨138, by decide⟩), (⟨3, by decide⟩, ⟨773, by decide⟩), (⟨6, by decide⟩, ⟨116, by decide⟩), (⟨24, by decide⟩, ⟨104, by decide⟩), (⟨132, by decide⟩, ⟨201, by decide⟩), (⟨24, by decide⟩, ⟨208, by decide⟩), (⟨33, by decide⟩, ⟨69, by decide⟩), (⟨264, by decide⟩, ⟨521, by decide⟩)]
def tag80905 : Fin 12 → Fin 11 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma checked_gates80905 : countGateCheck false graph total80905 signal entries cuts80905 rows80905 = true := by decide +kernel
lemma checked_leaves80905 : countLeafCheck total80905 signal entries = true := by decide +kernel
lemma missing80905 : (total80905, graph) ∉ entries := by decide +kernel
lemma counts80905 : count tag80905 (Finset.univ : Finset (Fin 12)) = total80905 := by
  funext j; fin_cases j <;> decide +kernel

end PEqualNP.Outside.L_meta_2373.Weak80905
