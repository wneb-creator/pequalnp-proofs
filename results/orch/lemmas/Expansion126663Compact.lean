import CofactorCheck

namespace PEqualNP.Outside.L_meta_2373.Live1024.Expansion126663

abbrev atom (i : Nat) : Sig := inputs.getD i zero

def pre0 : Sig := bin 1 (atom 0) (atom 1)
def pre1 : Sig := bin 1 (atom 2) (atom 3)
def pre2 : Sig := bin 1 (atom 9) pre0
def pre3 : Sig := bin 1 pre1 pre2
def pre4 : Sig := bin 3 (atom 4) pre3

def words : List Sig := [
  atom 0,
  atom 1,
  atom 2,
  atom 3,
  atom 4,
  atom 5,
  atom 6,
  atom 7,
  atom 8,
  atom 9,
  pre0,
  bin 1 (atom 0) (atom 5),
  bin 1 (atom 1) (atom 2),
  bin 1 (atom 1) (atom 6),
  bin 1 (atom 5) (atom 7),
  bin 1 (atom 5) (atom 8),
  pre1,
  bin 1 (atom 2) (atom 7),
  bin 1 (atom 6) (atom 8),
  bin 1 (atom 6) (atom 9),
  bin 1 (atom 3) (atom 8),
  bin 1 (atom 7) (atom 9),
  bin 0 (atom 0) (atom 1),
  bin 2 (atom 0) (atom 1),
  bin 3 (atom 0) (atom 1),
  bin 0 (atom 0) (atom 2),
  bin 1 (atom 0) (atom 2),
  bin 1 (atom 0) (atom 9),
  bin 1 (atom 1) (atom 9),
  bin 1 (atom 5) (atom 9),
  bin 1 (atom 3) (atom 9),
  bin 1 (atom 2) (atom 9),
  bin 1 (atom 8) (atom 9),
  bin 0 (atom 1) (atom 2),
  bin 2 (atom 1) (atom 2),
  bin 3 (atom 1) (atom 2),
  bin 0 (atom 1) (atom 3),
  bin 1 (atom 1) (atom 3),
  bin 2 (atom 1) (atom 3),
  bin 3 (atom 1) (atom 3),
  bin 2 (atom 1) pre4,
  bin 1 (atom 6) (atom 7),
  bin 0 (atom 2) (atom 3),
  bin 2 (atom 2) (atom 3),
  bin 3 (atom 2) (atom 3),
  bin 2 (atom 2) pre4,
  bin 1 (atom 7) (atom 8),
  bin 0 (atom 3) (atom 5),
  bin 1 (atom 3) (atom 5),
  bin 1 (atom 1) (atom 5),
  bin 2 (atom 3) (atom 5),
  bin 3 (atom 3) (atom 5),
  bin 0 (atom 3) (atom 6),
  bin 1 (atom 3) (atom 6),
  bin 2 (atom 3) (atom 6),
  bin 3 (atom 3) (atom 6),
  bin 0 (atom 3) (atom 7),
  bin 1 (atom 3) (atom 7),
  bin 1 (atom 5) (atom 6),
  bin 1 (atom 0) (atom 6),
  bin 1 (atom 2) (atom 6),
  bin 1 (atom 1) (atom 7),
  bin 1 (atom 0) (atom 7),
  bin 1 (atom 0) (atom 8),
  bin 1 (atom 2) (atom 5),
  bin 1 (atom 2) (atom 8),
  bin 1 (atom 1) (atom 8),
  bin 2 (atom 3) (atom 7),
  bin 2 (atom 5) (atom 8),
  bin 2 (atom 7) (atom 8),
  bin 3 (atom 3) (atom 7),
  bin 0 (atom 3) (atom 8),
  bin 2 (atom 3) (atom 8),
  bin 3 (atom 3) (atom 8),
  bin 0 (atom 3) (atom 9),
  bin 2 (atom 3) (atom 9),
  bin 3 (atom 3) (atom 9),
  bin 0 (atom 5) (atom 6),
  bin 2 (atom 5) (atom 6),
  bin 3 (atom 5) (atom 6),
  bin 0 (atom 5) (atom 7),
  bin 2 (atom 5) (atom 7),
  bin 3 (atom 5) (atom 7),
  bin 0 (atom 5) (atom 8),
  bin 3 (atom 7) (atom 8),
  bin 3 (atom 5) (atom 8),
  bin 0 (atom 5) (atom 9),
  bin 2 (atom 5) (atom 9),
  bin 3 (atom 5) (atom 9),
  bin 0 (atom 6) (atom 7),
  bin 2 (atom 6) (atom 7),
  bin 3 (atom 6) (atom 7),
  bin 0 (atom 6) (atom 8),
  bin 2 (atom 6) (atom 8),
  bin 3 (atom 6) (atom 8),
  bin 0 (atom 6) (atom 9),
  bin 2 (atom 6) (atom 9),
  bin 3 (atom 6) (atom 9),
  bin 0 (atom 7) (atom 8),
  bin 1 (atom 0) (atom 3),
  bin 0 (atom 7) (atom 9),
  bin 2 (atom 7) (atom 9),
  bin 3 (atom 7) (atom 9),
  bin 0 (atom 8) (atom 9),
  bin 2 (atom 8) (atom 9),
  bin 3 (atom 8) (atom 9),
  pre2,
  bin 0 (atom 2) pre4,
  bin 0 (atom 2) (atom 5),
  bin 2 (atom 3) pre4,
  bin 0 (atom 3) pre4,
  bin 0 (atom 1) pre4,
  bin 2 (atom 9) pre4,
  bin 0 (atom 9) pre4,
  bin 2 (atom 2) (atom 5),
  bin 3 (atom 1) pre4,
  bin 3 (atom 2) (atom 5),
  bin 0 (atom 2) (atom 6),
  bin 2 (atom 2) (atom 6),
  bin 3 (atom 2) (atom 6),
  bin 0 (atom 2) (atom 7),
  bin 2 (atom 2) (atom 7),
  bin 3 (atom 2) (atom 7),
  bin 0 (atom 2) (atom 8),
  bin 2 (atom 2) (atom 8),
  bin 3 (atom 2) (atom 8),
  bin 0 (atom 2) (atom 9),
  bin 2 (atom 2) (atom 9),
  bin 3 (atom 2) (atom 9),
  bin 2 (atom 0) (atom 2),
  bin 0 (atom 1) (atom 5),
  bin 2 (atom 1) (atom 5),
  bin 3 (atom 1) (atom 5),
  bin 0 (atom 1) (atom 6),
  bin 2 (atom 1) (atom 6),
  bin 3 (atom 1) (atom 6),
  bin 0 (atom 1) (atom 7),
  bin 2 (atom 1) (atom 7),
  bin 3 (atom 1) (atom 7),
  bin 0 (atom 1) (atom 8),
  bin 2 (atom 1) (atom 8),
  bin 3 (atom 1) (atom 8),
  bin 0 (atom 1) (atom 9),
  bin 2 (atom 1) (atom 9),
  bin 3 (atom 1) (atom 9),
  bin 3 (atom 2) pre4,
  bin 3 (atom 0) (atom 2),
  bin 0 (atom 0) (atom 3),
  bin 2 (atom 0) (atom 3),
  bin 3 (atom 0) (atom 3),
  bin 2 (atom 0) pre4,
  bin 0 (atom 0) pre4,
  bin 0 (atom 0) (atom 5),
  bin 2 (atom 0) (atom 5),
  bin 3 (atom 0) (atom 5),
  bin 0 (atom 0) (atom 6),
  bin 2 (atom 0) (atom 6),
  bin 3 (atom 0) (atom 6),
  bin 0 (atom 0) (atom 7),
  bin 2 (atom 0) (atom 7),
  bin 3 (atom 0) (atom 7),
  bin 0 (atom 0) (atom 8),
  bin 2 (atom 0) (atom 8),
  bin 3 (atom 0) (atom 8),
  bin 0 (atom 0) (atom 9),
  bin 2 (atom 0) (atom 9),
  bin 3 (atom 0) (atom 9),
  pre3,
  bin 3 (atom 7) pre4,
  bin 3 (atom 5) pre4,
  bin 3 (atom 8) pre4,
  pre4,
  bin 3 (atom 0) pre4,
  bin 1 (atom 0) pre4,
  bin 0 (atom 5) pre4,
  bin 1 (atom 5) pre4,
  bin 2 (atom 5) pre4,
  bin 1 (atom 7) pre4,
  bin 1 (atom 8) pre4,
  bin 3 (atom 9) pre4,
  bin 1 (atom 9) pre4,
  bin 3 (atom 6) pre4,
  bin 1 (atom 1) pre4,
  bin 0 (atom 6) pre4,
  bin 1 (atom 6) pre4,
  bin 2 (atom 6) pre4,
  bin 1 (atom 2) pre4,
  bin 1 (atom 3) pre4,
  bin 3 (atom 3) pre4,
  bin 0 (atom 7) pre4,
  bin 2 (atom 7) pre4,
  bin 0 (atom 8) pre4,
  bin 2 (atom 8) pre4]

def word (i : Nat) : Sig := words.getD i zero
def state (ids : List Nat) : List Sig := ids.map word
def choices (cs : List (Nat × Nat × Nat)) : List Choice :=
  cs.map fun c => (c.1, word c.2.1, word c.2.2)

def profiles : List (Sig × Nat) := [
  (0x5555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 15),
  (0x3333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333, 15),
  (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 15),
  (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 15),
  (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 15),
  (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 15),
  (0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff, 15),
  (0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff, 15),
  (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 15),
  (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 15),
  (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 11),
  (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 10),
  (0xcccccccccccccccc0000000000000000cccccccccccccccc0000000000000000cccccccccccccccc0000000000000000cccccccccccccccc0000000000000000cccccccccccccccc0000000000000000cccccccccccccccc0000000000000000cccccccccccccccc0000000000000000cccccccccccccccc, 10),
  (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 10)]

def domain (i : Nat) : Sig := (profiles.getD i (zero, 0)).1
def lower (i : Nat) : Nat := (profiles.getD i (zero, 0)).2

def certificateGroup0 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 22, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 23, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 24, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 25, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 26, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 129, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 146, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)])]

def certificateGroup1 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 147, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 99, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 148, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 149, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 152, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 11, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 153, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 154, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)])]

def certificateGroup2 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 155, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 59, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 156, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 157, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 158, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 62, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 159, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 160, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)])]

def certificateGroup3 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 161, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 63, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 162, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 163, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 164, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 27, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 165, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 166, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)])]

def certificateGroup4 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 151, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 173], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 150, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 172], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 33, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 12, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 34, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 35, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)])]

def certificateGroup5 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 36, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 37, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 38, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 39, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 130, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 49, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 131, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 132, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)])]

def certificateGroup6 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 133, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 13, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 134, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 135, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 136, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 61, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 137, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 138, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)])]

def certificateGroup7 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 139, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 66, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 140, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 141, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 142, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 28, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 143, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 144, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)])]

def certificateGroup8 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 111, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 182], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 40, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (1, [0, 1, 2, 3, 5, 6, 7, 8, 9, 115, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 42, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (0, [0, 1, 2, 3, 5, 6, 7, 8, 9, 16, 171], [(1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 43, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 44, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)])]

def certificateGroup9 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 108, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 64, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 114, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 116, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 117, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 60, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 118, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 119, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)])]

def certificateGroup10 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 120, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 17, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 121, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 122, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 123, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 65, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 124, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 125, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)])]

def certificateGroup11 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 126, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 31, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 127, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 128, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 107, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 186], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 45, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (2, [0, 1, 2, 3, 5, 6, 7, 8, 9, 145, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)])]

def certificateGroup12 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 47, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 48, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 50, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 51, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 52, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 53, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 54, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 55, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)])]

def certificateGroup13 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 56, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 57, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 67, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 70, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 71, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 20, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 72, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 73, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)])]

def certificateGroup14 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 74, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 30, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 75, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 76, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 110, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 187], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 109, 171], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (3, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 188], [(1, 0, 1), (1, 9, 10), (1, 16, 106), (3, 4, 167)])]

def certificateGroup15 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (5, [0, 1, 2, 3, 5, 6, 7, 8, 9, 77, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (11, [0, 1, 2, 3, 5, 6, 7, 8, 9, 58, 171], []),
  (5, [0, 1, 2, 3, 5, 6, 7, 8, 9, 78, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (6, [0, 1, 2, 3, 5, 6, 7, 8, 9, 79, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (5, [0, 1, 2, 3, 5, 6, 7, 8, 9, 80, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (11, [0, 1, 2, 3, 5, 6, 7, 8, 9, 14, 171], []),
  (5, [0, 1, 2, 3, 5, 6, 7, 8, 9, 81, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (7, [0, 1, 2, 3, 5, 6, 7, 8, 9, 82, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)])]

def certificateGroup16 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (5, [0, 1, 2, 3, 5, 6, 7, 8, 9, 83, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (11, [0, 1, 2, 3, 5, 6, 7, 8, 9, 15, 171], []),
  (5, [0, 1, 2, 3, 5, 6, 7, 8, 9, 68, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (8, [0, 1, 2, 3, 5, 6, 7, 8, 9, 85, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (5, [0, 1, 2, 3, 5, 6, 7, 8, 9, 86, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (9, [0, 1, 2, 3, 5, 6, 7, 8, 9, 29, 171], [(1, 0, 1), (1, 2, 3), (1, 16, 106), (3, 4, 167)]),
  (5, [0, 1, 2, 3, 5, 6, 7, 8, 9, 87, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (9, [0, 1, 2, 3, 5, 6, 7, 8, 9, 88, 171], [(1, 0, 1), (1, 2, 3), (1, 16, 106), (3, 4, 167)])]

def certificateGroup17 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (5, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 174], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (10, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 175], []),
  (5, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 176], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (10, [0, 1, 2, 3, 5, 6, 7, 8, 9, 169, 171], []),
  (6, [0, 1, 2, 3, 5, 6, 7, 8, 9, 89, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (12, [0, 1, 2, 3, 5, 6, 7, 8, 9, 41, 171], []),
  (6, [0, 1, 2, 3, 5, 6, 7, 8, 9, 90, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (7, [0, 1, 2, 3, 5, 6, 7, 8, 9, 91, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)])]

def certificateGroup18 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (6, [0, 1, 2, 3, 5, 6, 7, 8, 9, 92, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (12, [0, 1, 2, 3, 5, 6, 7, 8, 9, 18, 171], []),
  (6, [0, 1, 2, 3, 5, 6, 7, 8, 9, 93, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (8, [0, 1, 2, 3, 5, 6, 7, 8, 9, 94, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (6, [0, 1, 2, 3, 5, 6, 7, 8, 9, 95, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (9, [0, 1, 2, 3, 5, 6, 7, 8, 9, 19, 171], [(1, 0, 1), (1, 2, 3), (1, 16, 106), (3, 4, 167)]),
  (6, [0, 1, 2, 3, 5, 6, 7, 8, 9, 96, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (9, [0, 1, 2, 3, 5, 6, 7, 8, 9, 97, 171], [(1, 0, 1), (1, 2, 3), (1, 16, 106), (3, 4, 167)])]

def certificateGroup19 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (6, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 183], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (10, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 184], []),
  (6, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 185], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (10, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 181], []),
  (7, [0, 1, 2, 3, 5, 6, 7, 8, 9, 98, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (13, [0, 1, 2, 3, 5, 6, 7, 8, 9, 46, 171], []),
  (7, [0, 1, 2, 3, 5, 6, 7, 8, 9, 69, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (8, [0, 1, 2, 3, 5, 6, 7, 8, 9, 84, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)])]

def certificateGroup20 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (7, [0, 1, 2, 3, 5, 6, 7, 8, 9, 100, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (9, [0, 1, 2, 3, 5, 6, 7, 8, 9, 21, 171], [(1, 0, 1), (1, 2, 3), (1, 16, 106), (3, 4, 167)]),
  (7, [0, 1, 2, 3, 5, 6, 7, 8, 9, 101, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (9, [0, 1, 2, 3, 5, 6, 7, 8, 9, 102, 171], [(1, 0, 1), (1, 2, 3), (1, 16, 106), (3, 4, 167)]),
  (7, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 189], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (10, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 177], []),
  (7, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 190], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (10, [0, 1, 2, 3, 5, 6, 7, 8, 9, 168, 171], [])]

def certificateGroup21 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (8, [0, 1, 2, 3, 5, 6, 7, 8, 9, 103, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (9, [0, 1, 2, 3, 5, 6, 7, 8, 9, 32, 171], [(1, 0, 1), (1, 2, 3), (1, 16, 106), (3, 4, 167)]),
  (8, [0, 1, 2, 3, 5, 6, 7, 8, 9, 104, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (9, [0, 1, 2, 3, 5, 6, 7, 8, 9, 105, 171], [(1, 0, 1), (1, 2, 3), (1, 16, 106), (3, 4, 167)]),
  (8, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 191], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (10, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 178], []),
  (8, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 192], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106), (3, 4, 167)]),
  (10, [0, 1, 2, 3, 5, 6, 7, 8, 9, 170, 171], [])]

def certificateGroup22 : List (Nat × List Nat × List (Nat × Nat × Nat)) := [
  (9, [0, 1, 2, 3, 5, 6, 7, 8, 9, 113, 171], [(1, 0, 1), (1, 2, 3), (1, 16, 106), (3, 4, 167)]),
  (9, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 180], [(1, 0, 1), (1, 2, 3), (1, 16, 106), (3, 4, 167)]),
  (4, [0, 1, 2, 3, 5, 6, 7, 8, 9, 112, 171], [(1, 0, 1), (1, 2, 3), (1, 9, 10), (1, 16, 106)]),
  (9, [0, 1, 2, 3, 5, 6, 7, 8, 9, 171, 179], [(1, 0, 1), (1, 2, 3), (1, 16, 106), (3, 4, 167)])]

def certificates : List (Nat × List Nat × List (Nat × Nat × Nat)) :=
  certificateGroup0 ++ certificateGroup1 ++ certificateGroup2 ++ certificateGroup3 ++ certificateGroup4 ++ certificateGroup5 ++ certificateGroup6 ++ certificateGroup7 ++ certificateGroup8 ++ certificateGroup9 ++ certificateGroup10 ++ certificateGroup11 ++ certificateGroup12 ++ certificateGroup13 ++ certificateGroup14 ++ certificateGroup15 ++ certificateGroup16 ++ certificateGroup17 ++ certificateGroup18 ++ certificateGroup19 ++ certificateGroup20 ++ certificateGroup21 ++ certificateGroup22

def rawState : List Sig := state [0, 1, 2, 3, 5, 6, 7, 8, 9, 171]

def known : List (Finset Sig) := certificates.map fun c => (state c.2.1).toFinset

def rowWitnesses : List (Row × Row) :=
  [(320, 256), (132, 4), (12, 4), (264, 8), (33, 1), (131, 130), (3, 1), (528, 0), (24, 8), (6, 2), (81, 64), (194, 130), (26, 18), (160, 32), (577, 65), (288, 256), (38, 36), (320, 64), (133, 129), (21, 5), (292, 36), (265, 257), (76, 72), (162, 130), (545, 513), (38, 34), (97, 65), (530, 18), (392, 136), (776, 520), (259, 258), (76, 68), (168, 40), (44, 36), (518, 514), (524, 516), (131, 129), (259, 257), (641, 129), (22, 20), (67, 65), (56, 40), (81, 65), (37, 5), (22, 18), (560, 32), (528, 512), (324, 260), (321, 257), (152, 128), (145, 129), (41, 9), (273, 257), (21, 20), (265, 9), (11, 10), (388, 260), (11, 9), (196, 68), (515, 514), (162, 34), (576, 512), (26, 10), (584, 72), (262, 258), (515, 513), (266, 10), (35, 34), (98, 34), (133, 5), (74, 10), (784, 256), (532, 20), (640, 512)]

def entryCheck (c : Nat × List Nat × List (Nat × Nat × Nat)) : Bool :=
  decide (c.1 < 14) && cofactorCheck true inputs (domain c.1) (lower c.1) 11
    (state c.2.1) (choices c.2.2)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup0 : certificateGroup0.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup1 : certificateGroup1.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup2 : certificateGroup2.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup3 : certificateGroup3.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup4 : certificateGroup4.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup5 : certificateGroup5.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup6 : certificateGroup6.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup7 : certificateGroup7.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup8 : certificateGroup8.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup9 : certificateGroup9.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup10 : certificateGroup10.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup11 : certificateGroup11.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup12 : certificateGroup12.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup13 : certificateGroup13.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup14 : certificateGroup14.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup15 : certificateGroup15.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup16 : certificateGroup16.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup17 : certificateGroup17.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup18 : certificateGroup18.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup19 : certificateGroup19.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup20 : certificateGroup20.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup21 : certificateGroup21.all entryCheck = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedGroup22 : certificateGroup22.all entryCheck = true := by
  decide +kernel

lemma allCertificatesChecked : certificates.all entryCheck = true := by
  simp only [certificates, List.all_append, checkedGroup0, checkedGroup1, checkedGroup2, checkedGroup3, checkedGroup4, checkedGroup5, checkedGroup6, checkedGroup7, checkedGroup8, checkedGroup9, checkedGroup10, checkedGroup11, checkedGroup12, checkedGroup13, checkedGroup14, checkedGroup15, checkedGroup16, checkedGroup17, checkedGroup18, checkedGroup19, checkedGroup20, checkedGroup21, checkedGroup22, Bool.and_self]

def coverageFor (a : Sig) : Bool :=
  (rawState.flatMap fun b => (successorOps true).flatMap fun d =>
    [false, true].flatMap fun ka => [false, true].filterMap fun kb =>
      if successorGuard rawState 12 a b d ka kb then some (childTwo rawState a b d ka kb) else none).all
    (fun child => decide (child.toFinset ∈ known) || rowWitnesses.any (rowReject true graph child))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedOperand0 : coverageFor (word 0) = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedOperand1 : coverageFor (word 1) = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedOperand2 : coverageFor (word 2) = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedOperand3 : coverageFor (word 3) = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedOperand4 : coverageFor (word 5) = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedOperand5 : coverageFor (word 6) = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedOperand6 : coverageFor (word 7) = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedOperand7 : coverageFor (word 8) = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedOperand8 : coverageFor (word 9) = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checkedOperand9 : coverageFor (word 171) = true := by
  decide +kernel

lemma allSuccessorsChecked : successorCheck true graph rawState 12 known rowWitnesses = true := by
  unfold successorCheck successorLists
  rw [List.all_flatMap]
  change rawState.all coverageFor = true
  simp only [rawState, state, List.map_cons, List.map_nil, List.all_cons, List.all_nil, checkedOperand0, checkedOperand1, checkedOperand2, checkedOperand3, checkedOperand4, checkedOperand5, checkedOperand6, checkedOperand7, checkedOperand8, checkedOperand9, Bool.and_self]

theorem closed_of_slices
    (slices : ∀ i : Fin 14, Slice true inputs graph (domain i.val) (lower i.val)) :
    Impossible true graph 12 rawState.toFinset := by
  apply successorCheck_sound (by decide +kernel) (by decide +kernel) ?_ allSuccessorsChecked
  intro S hS
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hS
  have check := List.all_eq_true.mp allCertificatesChecked c hc
  have both := Bool.and_eq_true_iff.mp check
  have hlt : c.1 < 14 := of_decide_eq_true both.1
  exact cofactorCheck_sound (slices ⟨c.1, hlt⟩) both.2

end PEqualNP.Outside.L_meta_2373.Live1024.Expansion126663
