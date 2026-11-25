import CountTableChecker

namespace PEqualNP.Outside.L_meta_2373.CountFixture1098
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
def s15 : Sig := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def s38 : Sig := 0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00
def s39 : Sig := 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa
def s43 : Sig := 0xee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00
def s44 : Sig := 0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffee
def s51 : Sig := 0xeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaaeeaa
def s1514 : Sig := 0xfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfc
def s1536 : Sig := 0xfffffffffffffffffefefefefefefefefffffffffffffffffefefefefefefefefffffffffffffffffefefefefefefefefffffffffffffffffefefefefefefefefffffffffffffffffefefefefefefefefffffffffffffffffefefefefefefefefffffffffffffffffefefefefefefefefffffffffffffffffefefefefefefefe
def s1557 : Sig := 0xfffffffffffffffffffcfffcfffcfffcfffffffffffffffffffcfffcfffcfffcfffffffffffffffffffcfffcfffcfffcfffffffffffffffffffcfffcfffcfffcfffffffffffffffffffcfffcfffcfffcfffffffffffffffffffcfffcfffcfffcfffffffffffffffffffcfffcfffcfffcfffffffffffffffffffcfffcfffcfffc
def s1609 : Sig := 0xfffffffffffffffffffefffefffefffefffffffffffffffffffefffefffefffefffffffffffffffffffefffefffefffefffffffffffffffffffefffefffefffefffffffffffffffffffefffefffefffefffffffffffffffffffefffefffefffefffffffffffffffffffefffefffefffefffffffffffffffffffefffefffefffe
def s1672 : Sig := 0xaaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a8aaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a8aaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a8aaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a8aaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a8aaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a8aaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a8aaaaaaaaaaaaaaaaa8a8a8a8a8a8a8a8
def s1673 : Sig := 0xff00ff00ff00ff00fc00fc00fc00fc00ff00ff00ff00ff00fc00fc00fc00fc00ff00ff00ff00ff00fc00fc00fc00fc00ff00ff00ff00ff00fc00fc00fc00fc00ff00ff00ff00ff00fc00fc00fc00fc00ff00ff00ff00ff00fc00fc00fc00fc00ff00ff00ff00ff00fc00fc00fc00fc00ff00ff00ff00ff00fc00fc00fc00fc00
def s1675 : Sig := 0xeeeeeeeeeeeeeeeeececececececececeeeeeeeeeeeeeeeeececececececececeeeeeeeeeeeeeeeeececececececececeeeeeeeeeeeeeeeeececececececececeeeeeeeeeeeeeeeeececececececececeeeeeeeeeeeeeeeeececececececececeeeeeeeeeeeeeeeeececececececececeeeeeeeeeeeeeeeeecececececececec
def s1676 : Sig := 0xffaaffaaffaaffaafca8fca8fca8fca8ffaaffaaffaaffaafca8fca8fca8fca8ffaaffaaffaaffaafca8fca8fca8fca8ffaaffaaffaaffaafca8fca8fca8fca8ffaaffaaffaaffaafca8fca8fca8fca8ffaaffaaffaaffaafca8fca8fca8fca8ffaaffaaffaaffaafca8fca8fca8fca8ffaaffaaffaaffaafca8fca8fca8fca8

def total : Fin 12 → Nat := ![2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2]
def signal : Fin 12 → Sig := ![s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s12, s1514]
def entries : List (CountEntry 12) := [
  (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], s1),
  (![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], s2),
  (![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], s3),
  (![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], s4),
  (![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], s5),
  (![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], s6),
  (![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], s7),
  (![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], s8),
  (![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], s9),
  (![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], s10),
  (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], s12),
  (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], s1514),
  (![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], s39)]
def cuts : List (CountEntry 12) := [
  (![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], s38),
  (![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0], s43),
  (![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0], s44),
  (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], s1672),
  (![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], s1536),
  (![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], s1673),
  (![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], s1557),
  (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], s1675),
  (![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], s1536),
  (![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0], s51),
  (![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0], s44),
  (![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], s1676),
  (![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], s1609)]
def rows : List (Row × Row) := [
  (⟨528, by decide⟩, ⟨554, by decide⟩),
  (⟨640, by decide⟩, ⟨201, by decide⟩),
  (⟨160, by decide⟩, ⟨201, by decide⟩),
  (⟨640, by decide⟩, ⟨773, by decide⟩),
  (⟨288, by decide⟩, ⟨554, by decide⟩),
  (⟨132, by decide⟩, ⟨201, by decide⟩),
  (⟨320, by decide⟩, ⟨402, by decide⟩),
  (⟨6, by decide⟩, ⟨773, by decide⟩),
  (⟨17, by decide⟩, ⟨385, by decide⟩),
  (⟨528, by decide⟩, ⟨116, by decide⟩),
  (⟨3, by decide⟩, ⟨201, by decide⟩),
  (⟨6, by decide⟩, ⟨50, by decide⟩),
  (⟨66, by decide⟩, ⟨138, by decide⟩),
  (⟨320, by decide⟩, ⟨69, by decide⟩),
  (⟨160, by decide⟩, ⟨104, by decide⟩),
  (⟨160, by decide⟩, ⟨138, by decide⟩),
  (⟨576, by decide⟩, ⟨773, by decide⟩)]
def basisTag : Fin 16 → Fin 12 := ![0, 0, 1, 2, 3, 3, 3, 4, 5, 6, 7, 8, 9, 10, 11, 11]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma checked_gates : countGateCheck false graph total signal entries cuts rows = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma checked_leaves : countLeafCheck total signal entries = true := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma missing : (total, graph) ∉ entries := by decide +kernel

lemma basis_counts : count basisTag (Finset.univ : Finset (Fin 16)) = total := by
  funext j
  fin_cases j <;> decide +kernel

lemma closed : CountClosed total signal (pairColumn false) (pairColumn false graph)
    (fun c v => (c, v) ∈ entries) (fun c v => (c, v) ∈ cuts) false :=
  countGateCheck_sound checked_gates

end PEqualNP.Outside.L_meta_2373.CountFixture1098
