import Lean

namespace DomainEquality
abbrev Sig := BitVec 128

def zero : Sig := 0

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000]

def graph : Sig := 0xfffffffffffefffafffeffeefefeeca0

def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero

def graphGoal (m : Nat) : Sig :=
  let x := vertex m
 (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6)

def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1

def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1

def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1

def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 128 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)

abbrev SliceSpec := Nat × Nat × Nat × Nat × Nat × Nat × Nat

def specDomain (s : SliceSpec) : Sig × Nat :=
  (subcube s.1 s.2.1, s.2.2.2.2.2.1)

abbrev RichDomains := Array (Nat × Sig × Nat)

def richSpecDomain (s : Nat × SliceSpec) := (s.1, specDomain s.2)

def ax31S : List (Nat × SliceSpec) := [(0, 8, 0, 23, 0, 0, 5, 5), (0, 0, 8, 21, 2, 240, 5, 4), (0, 1, 0, 30, 0, 0, 4, 4), (0, 4, 0, 27, 0, 0, 4, 4), (0, 2, 8, 21, 0, 0, 4, 4), (0, 10, 0, 21, 0, 0, 4, 4)]

def ax31D : RichDomains := (ax31S.map richSpecDomain).toArray

def ax55S : List (Nat × SliceSpec) := [(0, 2, 0, 53, 0, 0, 5, 5), (0, 32, 0, 23, 0, 0, 5, 5), (0, 1, 0, 54, 0, 0, 4, 4), (0, 16, 0, 39, 0, 0, 4, 4)]

def ax55D : RichDomains := (ax55S.map richSpecDomain).toArray

def ax87S : List (Nat × SliceSpec) := [(0, 2, 0, 85, 0, 0, 5, 5), (0, 64, 0, 23, 0, 0, 5, 5), (0, 0, 2, 69, 16, 983040, 5, 4), (0, 1, 0, 86, 0, 0, 4, 4), (0, 4, 0, 83, 0, 0, 4, 4), (0, 16, 2, 69, 0, 0, 4, 4), (0, 18, 0, 69, 0, 0, 4, 4), (0, 66, 0, 21, 0, 0, 4, 4)]

def ax87D : RichDomains := (ax87S.map richSpecDomain).toArray

def ax91S : List (Nat × SliceSpec) := [(0, 1, 0, 90, 0, 0, 4, 4), (0, 2, 0, 89, 0, 0, 4, 4), (0, 8, 0, 83, 0, 0, 4, 4), (0, 16, 0, 75, 0, 0, 4, 4), (0, 64, 0, 27, 0, 0, 4, 4)]

def ax91D : RichDomains := (ax91S.map richSpecDomain).toArray

def ax107S : List (Nat × SliceSpec) := [(0, 1, 0, 106, 0, 0, 5, 5), (0, 2, 0, 105, 0, 0, 5, 5), (0, 8, 0, 99, 0, 0, 5, 5), (0, 64, 0, 43, 0, 0, 5, 5), (0, 32, 0, 75, 0, 0, 4, 4), (0, 3, 0, 104, 0, 0, 4, 4), (0, 10, 0, 97, 0, 0, 4, 4), (0, 65, 0, 42, 0, 0, 4, 4)]

def ax107D : RichDomains := (ax107S.map richSpecDomain).toArray

def ax63S : List (Nat × SliceSpec) := [(0, 1, 0, 62, 0, 0, 7, 7), (30, 1, 0, 62, 0, 0, 7, 7), (111, 1, 0, 62, 0, 0, 7, 7), (119, 1, 0, 62, 0, 0, 7, 7), (120, 1, 0, 62, 0, 0, 7, 7), (129, 1, 0, 62, 0, 0, 7, 7), (182, 1, 0, 62, 0, 0, 7, 7), (191, 1, 0, 62, 0, 0, 7, 7), (192, 1, 0, 62, 0, 0, 7, 7), (273, 1, 0, 62, 0, 0, 7, 7), (282, 1, 0, 62, 0, 0, 7, 7), (291, 1, 0, 62, 0, 0, 7, 7), (292, 1, 0, 62, 0, 0, 7, 7), (0, 2, 0, 61, 0, 0, 7, 7), (30, 2, 0, 61, 0, 0, 7, 7), (40, 2, 0, 61, 0, 0, 7, 7), (111, 2, 0, 61, 0, 0, 7, 7), (121, 2, 0, 61, 0, 0, 7, 7), (130, 2, 0, 61, 0, 0, 7, 7), (181, 2, 0, 61, 0, 0, 7, 7), (192, 2, 0, 61, 0, 0, 7, 7), (201, 2, 0, 61, 0, 0, 7, 7), (202, 2, 0, 61, 0, 0, 7, 7), (211, 2, 0, 61, 0, 0, 7, 7), (273, 2, 0, 61, 0, 0, 7, 7), (282, 2, 0, 61, 0, 0, 7, 7), (283, 2, 0, 61, 0, 0, 7, 7), (291, 2, 0, 61, 0, 0, 7, 7), (292, 2, 0, 61, 0, 0, 7, 7), (0, 16, 0, 47, 0, 0, 7, 7), (20, 16, 0, 47, 0, 0, 7, 7), (100, 16, 0, 47, 0, 0, 7, 7), (101, 16, 0, 47, 0, 0, 7, 7), (111, 16, 0, 47, 0, 0, 7, 7), (181, 16, 0, 47, 0, 0, 7, 7), (182, 16, 0, 47, 0, 0, 7, 7), (192, 16, 0, 47, 0, 0, 7, 7), (0, 32, 0, 31, 0, 0, 7, 7), (111, 32, 0, 31, 0, 0, 7, 7), (119, 32, 0, 31, 0, 0, 7, 7), (181, 32, 0, 31, 0, 0, 7, 7), (182, 32, 0, 31, 0, 0, 7, 7), (192, 32, 0, 31, 0, 0, 7, 7), (100, 8, 0, 55, 0, 0, 6, 6), (0, 0, 4, 42, 17, 983055, 6, 4), (0, 0, 8, 21, 34, 15728880, 6, 4), (0, 5, 0, 58, 0, 0, 5, 5), (0, 1, 4, 42, 16, 983040, 5, 4)]

def ax63D : RichDomains := (ax63S.map richSpecDomain).toArray

def ax95S : List (Nat × SliceSpec) := [(0, 1, 0, 94, 0, 0, 7, 7), (20, 1, 0, 94, 0, 0, 7, 7), (56, 1, 0, 94, 0, 0, 7, 7), (110, 1, 0, 94, 0, 0, 7, 7), (119, 1, 0, 94, 0, 0, 7, 7), (120, 1, 0, 94, 0, 0, 7, 7), (138, 1, 0, 94, 0, 0, 7, 7), (139, 1, 0, 94, 0, 0, 7, 7), (182, 1, 0, 94, 0, 0, 7, 7), (191, 1, 0, 94, 0, 0, 7, 7), (192, 1, 0, 94, 0, 0, 7, 7), (200, 1, 0, 94, 0, 0, 7, 7), (201, 1, 0, 94, 0, 0, 7, 7), (202, 1, 0, 94, 0, 0, 7, 7), (218, 1, 0, 94, 0, 0, 7, 7), (219, 1, 0, 94, 0, 0, 7, 7), (220, 1, 0, 94, 0, 0, 7, 7), (221, 1, 0, 94, 0, 0, 7, 7), (263, 1, 0, 94, 0, 0, 7, 7), (272, 1, 0, 94, 0, 0, 7, 7), (273, 1, 0, 94, 0, 0, 7, 7), (281, 1, 0, 94, 0, 0, 7, 7), (282, 1, 0, 94, 0, 0, 7, 7), (283, 1, 0, 94, 0, 0, 7, 7), (299, 1, 0, 94, 0, 0, 7, 7), (300, 1, 0, 94, 0, 0, 7, 7), (301, 1, 0, 94, 0, 0, 7, 7), (302, 1, 0, 94, 0, 0, 7, 7), (0, 2, 0, 93, 0, 0, 7, 7), (28, 2, 0, 93, 0, 0, 7, 7), (37, 2, 0, 93, 0, 0, 7, 7), (39, 2, 0, 93, 0, 0, 7, 7), (40, 2, 0, 93, 0, 0, 7, 7), (55, 2, 0, 93, 0, 0, 7, 7), (57, 2, 0, 93, 0, 0, 7, 7), (59, 2, 0, 93, 0, 0, 7, 7), (109, 2, 0, 93, 0, 0, 7, 7), (111, 2, 0, 93, 0, 0, 7, 7), (118, 2, 0, 93, 0, 0, 7, 7), (120, 2, 0, 93, 0, 0, 7, 7), (121, 2, 0, 93, 0, 0, 7, 7), (136, 2, 0, 93, 0, 0, 7, 7), (138, 2, 0, 93, 0, 0, 7, 7), (139, 2, 0, 93, 0, 0, 7, 7), (181, 2, 0, 93, 0, 0, 7, 7), (190, 2, 0, 93, 0, 0, 7, 7), (199, 2, 0, 93, 0, 0, 7, 7), (201, 2, 0, 93, 0, 0, 7, 7), (202, 2, 0, 93, 0, 0, 7, 7), (217, 2, 0, 93, 0, 0, 7, 7), (219, 2, 0, 93, 0, 0, 7, 7), (220, 2, 0, 93, 0, 0, 7, 7), (221, 2, 0, 93, 0, 0, 7, 7), (262, 2, 0, 93, 0, 0, 7, 7), (271, 2, 0, 93, 0, 0, 7, 7), (273, 2, 0, 93, 0, 0, 7, 7), (280, 2, 0, 93, 0, 0, 7, 7), (282, 2, 0, 93, 0, 0, 7, 7), (283, 2, 0, 93, 0, 0, 7, 7), (298, 2, 0, 93, 0, 0, 7, 7), (300, 2, 0, 93, 0, 0, 7, 7), (302, 2, 0, 93, 0, 0, 7, 7), (0, 4, 0, 91, 0, 0, 7, 7), (110, 4, 0, 91, 0, 0, 7, 7), (118, 4, 0, 91, 0, 0, 7, 7), (119, 4, 0, 91, 0, 0, 7, 7), (172, 4, 0, 91, 0, 0, 7, 7), (191, 4, 0, 91, 0, 0, 7, 7), (202, 4, 0, 91, 0, 0, 7, 7), (217, 4, 0, 91, 0, 0, 7, 7), (253, 4, 0, 91, 0, 0, 7, 7), (271, 4, 0, 91, 0, 0, 7, 7), (280, 4, 0, 91, 0, 0, 7, 7), (283, 4, 0, 91, 0, 0, 7, 7), (299, 4, 0, 91, 0, 0, 7, 7), (0, 8, 0, 87, 0, 0, 7, 7), (10, 8, 0, 87, 0, 0, 7, 7), (59, 8, 0, 87, 0, 0, 7, 7), (91, 8, 0, 87, 0, 0, 7, 7), (101, 8, 0, 87, 0, 0, 7, 7), (118, 8, 0, 87, 0, 0, 7, 7), (119, 8, 0, 87, 0, 0, 7, 7), (120, 8, 0, 87, 0, 0, 7, 7), (136, 8, 0, 87, 0, 0, 7, 7), (137, 8, 0, 87, 0, 0, 7, 7), (138, 8, 0, 87, 0, 0, 7, 7), (172, 8, 0, 87, 0, 0, 7, 7), (181, 8, 0, 87, 0, 0, 7, 7), (199, 8, 0, 87, 0, 0, 7, 7), (200, 8, 0, 87, 0, 0, 7, 7), (201, 8, 0, 87, 0, 0, 7, 7), (217, 8, 0, 87, 0, 0, 7, 7), (218, 8, 0, 87, 0, 0, 7, 7), (219, 8, 0, 87, 0, 0, 7, 7), (221, 8, 0, 87, 0, 0, 7, 7), (253, 8, 0, 87, 0, 0, 7, 7), (262, 8, 0, 87, 0, 0, 7, 7), (263, 8, 0, 87, 0, 0, 7, 7), (280, 8, 0, 87, 0, 0, 7, 7), (298, 8, 0, 87, 0, 0, 7, 7), (299, 8, 0, 87, 0, 0, 7, 7), (302, 8, 0, 87, 0, 0, 7, 7), (0, 16, 0, 79, 0, 0, 7, 7), (10, 16, 0, 79, 0, 0, 7, 7), (20, 16, 0, 79, 0, 0, 7, 7), (56, 16, 0, 79, 0, 0, 7, 7), (91, 16, 0, 79, 0, 0, 7, 7), (101, 16, 0, 79, 0, 0, 7, 7), (110, 16, 0, 79, 0, 0, 7, 7), (139, 16, 0, 79, 0, 0, 7, 7), (172, 16, 0, 79, 0, 0, 7, 7), (191, 16, 0, 79, 0, 0, 7, 7), (192, 16, 0, 79, 0, 0, 7, 7), (217, 16, 0, 79, 0, 0, 7, 7), (218, 16, 0, 79, 0, 0, 7, 7), (219, 16, 0, 79, 0, 0, 7, 7), (220, 16, 0, 79, 0, 0, 7, 7), (253, 16, 0, 79, 0, 0, 7, 7), (262, 16, 0, 79, 0, 0, 7, 7), (263, 16, 0, 79, 0, 0, 7, 7), (272, 16, 0, 79, 0, 0, 7, 7), (298, 16, 0, 79, 0, 0, 7, 7), (299, 16, 0, 79, 0, 0, 7, 7), (301, 16, 0, 79, 0, 0, 7, 7), (0, 64, 0, 31, 0, 0, 7, 7), (20, 64, 0, 31, 0, 0, 7, 7), (109, 64, 0, 31, 0, 0, 7, 7), (110, 64, 0, 31, 0, 0, 7, 7), (119, 64, 0, 31, 0, 0, 7, 7), (181, 64, 0, 31, 0, 0, 7, 7), (191, 64, 0, 31, 0, 0, 7, 7), (199, 64, 0, 31, 0, 0, 7, 7), (263, 64, 0, 31, 0, 0, 7, 7), (283, 64, 0, 31, 0, 0, 7, 7), (0, 0, 2, 69, 24, 1044480, 6, 4), (0, 0, 8, 21, 66, 251658480, 6, 4), (0, 10, 0, 85, 0, 0, 5, 5), (0, 18, 0, 77, 0, 0, 5, 5), (0, 72, 0, 23, 0, 0, 5, 5), (0, 2, 8, 21, 64, 251658240, 5, 4), (0, 8, 2, 69, 16, 983040, 5, 4), (0, 16, 2, 69, 8, 61440, 5, 4), (0, 64, 8, 21, 2, 240, 5, 4), (0, 3, 0, 92, 0, 0, 4, 4), (0, 5, 0, 90, 0, 0, 4, 4), (0, 6, 0, 89, 0, 0, 4, 4), (0, 17, 0, 78, 0, 0, 4, 4), (0, 20, 0, 75, 0, 0, 4, 4), (0, 65, 0, 30, 0, 0, 4, 4), (0, 68, 0, 27, 0, 0, 4, 4), (0, 24, 2, 69, 0, 0, 4, 4), (0, 26, 0, 69, 0, 0, 4, 4), (0, 66, 8, 21, 0, 0, 4, 4), (0, 74, 0, 21, 0, 0, 4, 4)]

def ax95D : RichDomains := (ax95S.map richSpecDomain).toArray

def ax111S : List (Nat × SliceSpec) := [(0, 1, 0, 110, 0, 0, 7, 7), (48, 1, 0, 110, 0, 0, 7, 7), (101, 1, 0, 110, 0, 0, 7, 7), (129, 1, 0, 110, 0, 0, 7, 7), (141, 1, 0, 110, 0, 0, 7, 7), (210, 1, 0, 110, 0, 0, 7, 7), (0, 2, 0, 109, 0, 0, 7, 7), (30, 2, 0, 109, 0, 0, 7, 7), (48, 2, 0, 109, 0, 0, 7, 7), (111, 2, 0, 109, 0, 0, 7, 7), (127, 2, 0, 109, 0, 0, 7, 7), (130, 2, 0, 109, 0, 0, 7, 7), (192, 2, 0, 109, 0, 0, 7, 7), (210, 2, 0, 109, 0, 0, 7, 7), (222, 2, 0, 109, 0, 0, 7, 7), (273, 2, 0, 109, 0, 0, 7, 7), (291, 2, 0, 109, 0, 0, 7, 7), (292, 2, 0, 109, 0, 0, 7, 7), (300, 2, 0, 109, 0, 0, 7, 7), (0, 4, 0, 107, 0, 0, 7, 7), (10, 4, 0, 107, 0, 0, 7, 7), (49, 4, 0, 107, 0, 0, 7, 7), (91, 4, 0, 107, 0, 0, 7, 7), (127, 4, 0, 107, 0, 0, 7, 7), (128, 4, 0, 107, 0, 0, 7, 7), (136, 4, 0, 107, 0, 0, 7, 7), (172, 4, 0, 107, 0, 0, 7, 7), (209, 4, 0, 107, 0, 0, 7, 7), (217, 4, 0, 107, 0, 0, 7, 7), (299, 4, 0, 107, 0, 0, 7, 7), (0, 8, 0, 103, 0, 0, 7, 7), (101, 8, 0, 103, 0, 0, 7, 7), (127, 8, 0, 103, 0, 0, 7, 7), (137, 8, 0, 103, 0, 0, 7, 7), (141, 8, 0, 103, 0, 0, 7, 7), (210, 8, 0, 103, 0, 0, 7, 7), (218, 8, 0, 103, 0, 0, 7, 7), (0, 32, 0, 79, 0, 0, 7, 7), (20, 32, 0, 79, 0, 0, 7, 7), (56, 32, 0, 79, 0, 0, 7, 7), (91, 32, 0, 79, 0, 0, 7, 7), (101, 32, 0, 79, 0, 0, 7, 7), (110, 32, 0, 79, 0, 0, 7, 7), (139, 32, 0, 79, 0, 0, 7, 7), (172, 32, 0, 79, 0, 0, 7, 7), (182, 32, 0, 79, 0, 0, 7, 7), (190, 32, 0, 79, 0, 0, 7, 7), (191, 32, 0, 79, 0, 0, 7, 7), (220, 32, 0, 79, 0, 0, 7, 7), (253, 32, 0, 79, 0, 0, 7, 7), (271, 32, 0, 79, 0, 0, 7, 7), (272, 32, 0, 79, 0, 0, 7, 7), (273, 32, 0, 79, 0, 0, 7, 7), (299, 32, 0, 79, 0, 0, 7, 7), (300, 32, 0, 79, 0, 0, 7, 7), (301, 32, 0, 79, 0, 0, 7, 7), (0, 64, 0, 47, 0, 0, 7, 7), (48, 64, 0, 47, 0, 0, 7, 7), (127, 64, 0, 47, 0, 0, 7, 7), (208, 64, 0, 47, 0, 0, 7, 7), (210, 64, 0, 47, 0, 0, 7, 7), (291, 64, 0, 47, 0, 0, 7, 7), (0, 0, 2, 69, 40, 15790080, 6, 4), (0, 0, 4, 42, 65, 251658255, 6, 4), (0, 6, 0, 105, 0, 0, 5, 5), (0, 1, 4, 42, 64, 251658240, 5, 4), (0, 8, 2, 69, 32, 15728640, 5, 4), (0, 32, 2, 69, 8, 61440, 5, 4), (0, 64, 4, 42, 1, 15, 5, 4), (0, 9, 0, 102, 0, 0, 4, 4), (0, 7, 0, 104, 0, 0, 4, 4), (0, 14, 0, 97, 0, 0, 4, 4), (0, 40, 2, 69, 0, 0, 4, 4), (0, 65, 4, 42, 0, 0, 4, 4)]

def ax111D : RichDomains := (ax111S.map richSpecDomain).toArray

def ax127S : List (Nat × SliceSpec) := [(0, 1, 0, 126, 0, 0, 10, 10), (111, 1, 0, 126, 0, 0, 10, 10), (119, 1, 0, 126, 0, 0, 10, 10), (120, 1, 0, 126, 0, 0, 10, 10), (121, 1, 0, 126, 0, 0, 10, 10), (129, 1, 0, 126, 0, 0, 10, 10), (131, 1, 0, 126, 0, 0, 10, 10), (138, 1, 0, 126, 0, 0, 10, 10), (182, 1, 0, 126, 0, 0, 10, 10), (201, 1, 0, 126, 0, 0, 10, 10), (282, 1, 0, 126, 0, 0, 10, 10), (302, 1, 0, 126, 0, 0, 10, 10), (0, 2, 0, 125, 0, 0, 10, 10), (121, 2, 0, 125, 0, 0, 10, 10), (221, 2, 0, 125, 0, 0, 10, 10), (271, 2, 0, 125, 0, 0, 10, 10), (0, 4, 0, 123, 0, 0, 10, 10), (0, 8, 0, 119, 0, 0, 10, 10), (0, 16, 0, 111, 0, 0, 10, 10), (101, 16, 0, 111, 0, 0, 10, 10), (218, 16, 0, 111, 0, 0, 10, 10), (0, 32, 0, 95, 0, 0, 10, 10), (91, 32, 0, 95, 0, 0, 10, 10), (101, 32, 0, 95, 0, 0, 10, 10), (109, 32, 0, 95, 0, 0, 10, 10), (110, 32, 0, 95, 0, 0, 10, 10), (111, 32, 0, 95, 0, 0, 10, 10), (119, 32, 0, 95, 0, 0, 10, 10), (139, 32, 0, 95, 0, 0, 10, 10), (191, 32, 0, 95, 0, 0, 10, 10), (272, 32, 0, 95, 0, 0, 10, 10), (299, 32, 0, 95, 0, 0, 10, 10), (0, 64, 0, 63, 0, 0, 9, 9), (100, 64, 0, 63, 0, 0, 9, 9), (101, 64, 0, 63, 0, 0, 9, 9), (109, 64, 0, 63, 0, 0, 9, 9), (110, 64, 0, 63, 0, 0, 9, 9), (111, 64, 0, 63, 0, 0, 9, 9), (119, 64, 0, 63, 0, 0, 9, 9), (120, 64, 0, 63, 0, 0, 9, 9), (121, 64, 0, 63, 0, 0, 9, 9), (127, 64, 0, 63, 0, 0, 9, 9), (181, 64, 0, 63, 0, 0, 9, 9), (182, 64, 0, 63, 0, 0, 9, 9), (190, 64, 0, 63, 0, 0, 9, 9), (191, 64, 0, 63, 0, 0, 9, 9), (192, 64, 0, 63, 0, 0, 9, 9), (273, 64, 0, 63, 0, 0, 9, 9), (282, 64, 0, 63, 0, 0, 9, 9), (283, 64, 0, 63, 0, 0, 9, 9), (291, 64, 0, 63, 0, 0, 9, 9), (292, 64, 0, 63, 0, 0, 9, 9), (0, 0, 2, 69, 56, 16773120, 7, 4), (0, 0, 4, 42, 81, 252641295, 7, 4), (0, 0, 8, 21, 98, 267387120, 7, 4), (0, 0, 16, 104, 7, 4095, 7, 4), (0, 3, 0, 124, 0, 0, 7, 7), (0, 5, 0, 122, 0, 0, 7, 7), (0, 6, 0, 121, 0, 0, 7, 7), (0, 9, 0, 118, 0, 0, 7, 7), (0, 10, 0, 117, 0, 0, 7, 7), (0, 17, 0, 110, 0, 0, 7, 7), (0, 18, 0, 109, 0, 0, 7, 7), (0, 20, 0, 107, 0, 0, 7, 7), (0, 24, 0, 103, 0, 0, 7, 7), (0, 33, 0, 94, 0, 0, 7, 7), (0, 34, 0, 93, 0, 0, 7, 7), (0, 36, 0, 91, 0, 0, 7, 7), (0, 40, 0, 87, 0, 0, 7, 7), (0, 48, 0, 79, 0, 0, 7, 7), (0, 65, 0, 62, 0, 0, 7, 7), (0, 66, 0, 61, 0, 0, 7, 7), (0, 80, 0, 47, 0, 0, 7, 7), (0, 96, 0, 31, 0, 0, 7, 7), (0, 12, 0, 115, 0, 0, 6, 6), (0, 68, 0, 59, 0, 0, 6, 6), (0, 72, 0, 55, 0, 0, 6, 6), (0, 1, 4, 42, 80, 252641280, 6, 4), (0, 1, 16, 104, 6, 4080, 6, 4), (0, 2, 8, 21, 96, 267386880, 6, 4), (0, 2, 16, 104, 5, 3855, 6, 4), (0, 4, 16, 104, 3, 255, 6, 4), (0, 8, 2, 69, 48, 16711680, 6, 4), (0, 16, 2, 69, 40, 15790080, 6, 4), (0, 16, 4, 42, 65, 251658255, 6, 4), (0, 32, 2, 69, 24, 1044480, 6, 4), (0, 32, 8, 21, 66, 251658480, 6, 4), (0, 64, 4, 42, 17, 983055, 6, 4), (0, 64, 8, 21, 34, 15728880, 6, 4), (0, 14, 0, 113, 0, 0, 5, 5), (0, 19, 0, 108, 0, 0, 5, 5), (0, 21, 0, 106, 0, 0, 5, 5), (0, 26, 0, 101, 0, 0, 5, 5), (0, 69, 0, 58, 0, 0, 5, 5), (0, 74, 0, 53, 0, 0, 5, 5), (0, 84, 0, 43, 0, 0, 5, 5), (0, 104, 0, 23, 0, 0, 5, 5), (0, 3, 16, 104, 4, 3840, 5, 4), (0, 5, 16, 104, 2, 240, 5, 4), (0, 6, 16, 104, 1, 15, 5, 4), (0, 17, 4, 42, 64, 251658240, 5, 4), (0, 24, 2, 69, 32, 15728640, 5, 4), (0, 34, 8, 21, 64, 251658240, 5, 4), (0, 40, 2, 69, 16, 983040, 5, 4), (0, 48, 2, 69, 8, 61440, 5, 4), (0, 65, 4, 42, 16, 983040, 5, 4), (0, 66, 8, 21, 32, 15728640, 5, 4), (0, 80, 4, 42, 1, 15, 5, 4), (0, 96, 8, 21, 2, 240, 5, 4), (0, 11, 0, 116, 0, 0, 4, 4), (0, 13, 0, 114, 0, 0, 4, 4), (0, 25, 0, 102, 0, 0, 4, 4), (0, 35, 0, 92, 0, 0, 4, 4), (0, 37, 0, 90, 0, 0, 4, 4), (0, 38, 0, 89, 0, 0, 4, 4), (0, 41, 0, 86, 0, 0, 4, 4), (0, 44, 0, 83, 0, 0, 4, 4), (0, 49, 0, 78, 0, 0, 4, 4), (0, 73, 0, 54, 0, 0, 4, 4), (0, 82, 0, 45, 0, 0, 4, 4), (0, 88, 0, 39, 0, 0, 4, 4), (0, 97, 0, 30, 0, 0, 4, 4), (0, 7, 16, 104, 0, 0, 4, 4), (0, 30, 0, 97, 0, 0, 4, 4), (0, 56, 2, 69, 0, 0, 4, 4), (0, 81, 4, 42, 0, 0, 4, 4), (0, 85, 0, 42, 0, 0, 4, 4), (0, 98, 8, 21, 0, 0, 4, 4), (0, 106, 0, 21, 0, 0, 4, 4)]

def ax127D : RichDomains := (ax127S.map richSpecDomain).toArray

def fixedWord0x2 : Sig := 0xcccccccccccccccccccccccccccccccc

def fixedWord0x4 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0

def fixedWord0x8 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00

def fixedWord0x16 : Sig := 0xffff0000ffff0000ffff0000ffff0000

def fixedWord1x0 : Sig := 0x55555555555555555555555555555555

def fixedWord1x4 : Sig := 0x50505050505050505050505050505050

def fixedWord1x16 : Sig := 0x55550000555500005555000055550000

def fixedWord2x0 : Sig := 0x33333333333333333333333333333333

def fixedWord2x8 : Sig := 0x33003300330033003300330033003300

def fixedWord2x16 : Sig := 0x33330000333300003333000033330000

def fixedWord3x0 : Sig := 0x11111111111111111111111111111111

def fixedWord3x16 : Sig := 0x11110000111100001111000011110000

def fixedWord4x0 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f

def fixedWord4x16 : Sig := 0xf0f00000f0f00000f0f00000f0f0000

def fixedWord5x0 : Sig := 0x5050505050505050505050505050505

def fixedWord5x16 : Sig := 0x5050000050500000505000005050000

def fixedWord6x0 : Sig := 0x3030303030303030303030303030303

def fixedWord6x16 : Sig := 0x3030000030300000303000003030000

def fixedWord7x0 : Sig := 0x1010101010101010101010101010101

def fixedWord7x16 : Sig := 0x1010000010100000101000001010000

def fixedWord8x0 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff

def fixedWord8x2 : Sig := 0xcc00cc00cc00cc00cc00cc00cc00cc

def fixedWord9x0 : Sig := 0x550055005500550055005500550055

def fixedWord10x0 : Sig := 0x330033003300330033003300330033

def fixedWord11x0 : Sig := 0x110011001100110011001100110011

def fixedWord12x0 : Sig := 0xf000f000f000f000f000f000f000f

def fixedWord13x0 : Sig := 0x50005000500050005000500050005

def fixedWord14x0 : Sig := 0x30003000300030003000300030003

def fixedWord16x0 : Sig := 0xffff0000ffff0000ffff0000ffff

def fixedWord16x2 : Sig := 0xcccc0000cccc0000cccc0000cccc

def fixedWord16x4 : Sig := 0xf0f00000f0f00000f0f00000f0f0

def fixedWord17x0 : Sig := 0x5555000055550000555500005555

def fixedWord17x4 : Sig := 0x5050000050500000505000005050

def fixedWord18x0 : Sig := 0x3333000033330000333300003333

def fixedWord19x0 : Sig := 0x1111000011110000111100001111

def fixedWord20x0 : Sig := 0xf0f00000f0f00000f0f00000f0f

def fixedWord21x0 : Sig := 0x505000005050000050500000505

def fixedWord24x0 : Sig := 0xff000000ff000000ff000000ff

def fixedWord24x2 : Sig := 0xcc000000cc000000cc000000cc

def fixedWord25x0 : Sig := 0x55000000550000005500000055

def fixedWord26x0 : Sig := 0x33000000330000003300000033

def fixedWord30x0 : Sig := 0x3000000030000000300000003

def fixedWord32x0 : Sig := 0xffffffff00000000ffffffff

def fixedWord32x2 : Sig := 0xcccccccc00000000cccccccc

def fixedWord32x8 : Sig := 0xff00ff0000000000ff00ff00

def fixedWord33x0 : Sig := 0x555555550000000055555555

def fixedWord34x0 : Sig := 0x333333330000000033333333

def fixedWord34x8 : Sig := 0x330033000000000033003300

def fixedWord35x0 : Sig := 0x111111110000000011111111

def fixedWord36x0 : Sig := 0xf0f0f0f000000000f0f0f0f

def fixedWord37x0 : Sig := 0x50505050000000005050505

def fixedWord38x0 : Sig := 0x30303030000000003030303

def fixedWord40x0 : Sig := 0xff00ff0000000000ff00ff

def fixedWord40x2 : Sig := 0xcc00cc0000000000cc00cc

def fixedWord41x0 : Sig := 0x5500550000000000550055

def fixedWord44x0 : Sig := 0xf000f00000000000f000f

def fixedWord48x0 : Sig := 0xffff000000000000ffff

def fixedWord48x2 : Sig := 0xcccc000000000000cccc

def fixedWord49x0 : Sig := 0x55550000000000005555

def fixedWord56x2 : Sig := 0xcc00000000000000cc

def fixedWord64x0 : Sig := 0xffffffffffffffff

def fixedWord64x4 : Sig := 0xf0f0f0f0f0f0f0f0

def fixedWord64x8 : Sig := 0xff00ff00ff00ff00

def fixedWord65x0 : Sig := 0x5555555555555555

def fixedWord65x4 : Sig := 0x5050505050505050

def fixedWord66x0 : Sig := 0x3333333333333333

def fixedWord66x8 : Sig := 0x3300330033003300

def fixedWord68x0 : Sig := 0xf0f0f0f0f0f0f0f

def fixedWord69x0 : Sig := 0x505050505050505

def fixedWord72x0 : Sig := 0xff00ff00ff00ff

def fixedWord73x0 : Sig := 0x55005500550055

def fixedWord74x0 : Sig := 0x33003300330033

def fixedWord80x0 : Sig := 0xffff0000ffff

def fixedWord80x4 : Sig := 0xf0f00000f0f0

def fixedWord81x4 : Sig := 0x505000005050

def fixedWord82x0 : Sig := 0x333300003333

def fixedWord84x0 : Sig := 0xf0f00000f0f

def fixedWord85x0 : Sig := 0x50500000505

def fixedWord88x0 : Sig := 0xff000000ff

def fixedWord96x0 : Sig := 0xffffffff

def fixedWord96x8 : Sig := 0xff00ff00

def fixedWord97x0 : Sig := 0x55555555

def fixedWord98x8 : Sig := 0x33003300

def fixedWord104x0 : Sig := 0xff00ff

def fixedWord106x0 : Sig := 0x330033

def fastax31D : RichDomains := [(0, fixedWord8x0, 5), (0, fixedWord0x8, 5), (0, fixedWord1x0, 4), (0, fixedWord4x0, 4), (0, fixedWord2x8, 4), (0, fixedWord10x0, 4)].toArray

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains_ax31D : fastax31D = ax31D := by decide +kernel

def fastax55D : RichDomains := [(0, fixedWord2x0, 5), (0, fixedWord32x0, 5), (0, fixedWord1x0, 4), (0, fixedWord16x0, 4)].toArray

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains_ax55D : fastax55D = ax55D := by decide +kernel

def fastax87D : RichDomains := [(0, fixedWord2x0, 5), (0, fixedWord64x0, 5), (0, fixedWord0x2, 5), (0, fixedWord1x0, 4), (0, fixedWord4x0, 4), (0, fixedWord16x2, 4), (0, fixedWord18x0, 4), (0, fixedWord66x0, 4)].toArray

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains_ax87D : fastax87D = ax87D := by decide +kernel

def fastax91D : RichDomains := [(0, fixedWord1x0, 4), (0, fixedWord2x0, 4), (0, fixedWord8x0, 4), (0, fixedWord16x0, 4), (0, fixedWord64x0, 4)].toArray

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains_ax91D : fastax91D = ax91D := by decide +kernel

def fastax107D : RichDomains := [(0, fixedWord1x0, 5), (0, fixedWord2x0, 5), (0, fixedWord8x0, 5), (0, fixedWord64x0, 5), (0, fixedWord32x0, 4), (0, fixedWord3x0, 4), (0, fixedWord10x0, 4), (0, fixedWord65x0, 4)].toArray

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains_ax107D : fastax107D = ax107D := by decide +kernel

def fastax63D : RichDomains := [(0, fixedWord1x0, 7), (30, fixedWord1x0, 7), (111, fixedWord1x0, 7), (119, fixedWord1x0, 7), (120, fixedWord1x0, 7), (129, fixedWord1x0, 7), (182, fixedWord1x0, 7), (191, fixedWord1x0, 7), (192, fixedWord1x0, 7), (273, fixedWord1x0, 7), (282, fixedWord1x0, 7), (291, fixedWord1x0, 7), (292, fixedWord1x0, 7), (0, fixedWord2x0, 7), (30, fixedWord2x0, 7), (40, fixedWord2x0, 7), (111, fixedWord2x0, 7), (121, fixedWord2x0, 7), (130, fixedWord2x0, 7), (181, fixedWord2x0, 7), (192, fixedWord2x0, 7), (201, fixedWord2x0, 7), (202, fixedWord2x0, 7), (211, fixedWord2x0, 7), (273, fixedWord2x0, 7), (282, fixedWord2x0, 7), (283, fixedWord2x0, 7), (291, fixedWord2x0, 7), (292, fixedWord2x0, 7), (0, fixedWord16x0, 7), (20, fixedWord16x0, 7), (100, fixedWord16x0, 7), (101, fixedWord16x0, 7), (111, fixedWord16x0, 7), (181, fixedWord16x0, 7), (182, fixedWord16x0, 7), (192, fixedWord16x0, 7), (0, fixedWord32x0, 7), (111, fixedWord32x0, 7), (119, fixedWord32x0, 7), (181, fixedWord32x0, 7), (182, fixedWord32x0, 7), (192, fixedWord32x0, 7), (100, fixedWord8x0, 6), (0, fixedWord0x4, 6), (0, fixedWord0x8, 6), (0, fixedWord5x0, 5), (0, fixedWord1x4, 5)].toArray

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains_ax63D : fastax63D = ax63D := by decide +kernel

def fastax95D : RichDomains := [(0, fixedWord1x0, 7), (20, fixedWord1x0, 7), (56, fixedWord1x0, 7), (110, fixedWord1x0, 7), (119, fixedWord1x0, 7), (120, fixedWord1x0, 7), (138, fixedWord1x0, 7), (139, fixedWord1x0, 7), (182, fixedWord1x0, 7), (191, fixedWord1x0, 7), (192, fixedWord1x0, 7), (200, fixedWord1x0, 7), (201, fixedWord1x0, 7), (202, fixedWord1x0, 7), (218, fixedWord1x0, 7), (219, fixedWord1x0, 7), (220, fixedWord1x0, 7), (221, fixedWord1x0, 7), (263, fixedWord1x0, 7), (272, fixedWord1x0, 7), (273, fixedWord1x0, 7), (281, fixedWord1x0, 7), (282, fixedWord1x0, 7), (283, fixedWord1x0, 7), (299, fixedWord1x0, 7), (300, fixedWord1x0, 7), (301, fixedWord1x0, 7), (302, fixedWord1x0, 7), (0, fixedWord2x0, 7), (28, fixedWord2x0, 7), (37, fixedWord2x0, 7), (39, fixedWord2x0, 7), (40, fixedWord2x0, 7), (55, fixedWord2x0, 7), (57, fixedWord2x0, 7), (59, fixedWord2x0, 7), (109, fixedWord2x0, 7), (111, fixedWord2x0, 7), (118, fixedWord2x0, 7), (120, fixedWord2x0, 7), (121, fixedWord2x0, 7), (136, fixedWord2x0, 7), (138, fixedWord2x0, 7), (139, fixedWord2x0, 7), (181, fixedWord2x0, 7), (190, fixedWord2x0, 7), (199, fixedWord2x0, 7), (201, fixedWord2x0, 7), (202, fixedWord2x0, 7), (217, fixedWord2x0, 7), (219, fixedWord2x0, 7), (220, fixedWord2x0, 7), (221, fixedWord2x0, 7), (262, fixedWord2x0, 7), (271, fixedWord2x0, 7), (273, fixedWord2x0, 7), (280, fixedWord2x0, 7), (282, fixedWord2x0, 7), (283, fixedWord2x0, 7), (298, fixedWord2x0, 7), (300, fixedWord2x0, 7), (302, fixedWord2x0, 7), (0, fixedWord4x0, 7), (110, fixedWord4x0, 7), (118, fixedWord4x0, 7), (119, fixedWord4x0, 7), (172, fixedWord4x0, 7), (191, fixedWord4x0, 7), (202, fixedWord4x0, 7), (217, fixedWord4x0, 7), (253, fixedWord4x0, 7), (271, fixedWord4x0, 7), (280, fixedWord4x0, 7), (283, fixedWord4x0, 7), (299, fixedWord4x0, 7), (0, fixedWord8x0, 7), (10, fixedWord8x0, 7), (59, fixedWord8x0, 7), (91, fixedWord8x0, 7), (101, fixedWord8x0, 7), (118, fixedWord8x0, 7), (119, fixedWord8x0, 7), (120, fixedWord8x0, 7), (136, fixedWord8x0, 7), (137, fixedWord8x0, 7), (138, fixedWord8x0, 7), (172, fixedWord8x0, 7), (181, fixedWord8x0, 7), (199, fixedWord8x0, 7), (200, fixedWord8x0, 7), (201, fixedWord8x0, 7), (217, fixedWord8x0, 7), (218, fixedWord8x0, 7), (219, fixedWord8x0, 7), (221, fixedWord8x0, 7), (253, fixedWord8x0, 7), (262, fixedWord8x0, 7), (263, fixedWord8x0, 7), (280, fixedWord8x0, 7), (298, fixedWord8x0, 7), (299, fixedWord8x0, 7), (302, fixedWord8x0, 7), (0, fixedWord16x0, 7), (10, fixedWord16x0, 7), (20, fixedWord16x0, 7), (56, fixedWord16x0, 7), (91, fixedWord16x0, 7), (101, fixedWord16x0, 7), (110, fixedWord16x0, 7), (139, fixedWord16x0, 7), (172, fixedWord16x0, 7), (191, fixedWord16x0, 7), (192, fixedWord16x0, 7), (217, fixedWord16x0, 7), (218, fixedWord16x0, 7), (219, fixedWord16x0, 7), (220, fixedWord16x0, 7), (253, fixedWord16x0, 7), (262, fixedWord16x0, 7), (263, fixedWord16x0, 7), (272, fixedWord16x0, 7), (298, fixedWord16x0, 7), (299, fixedWord16x0, 7), (301, fixedWord16x0, 7), (0, fixedWord64x0, 7), (20, fixedWord64x0, 7), (109, fixedWord64x0, 7), (110, fixedWord64x0, 7), (119, fixedWord64x0, 7), (181, fixedWord64x0, 7), (191, fixedWord64x0, 7), (199, fixedWord64x0, 7), (263, fixedWord64x0, 7), (283, fixedWord64x0, 7), (0, fixedWord0x2, 6), (0, fixedWord0x8, 6), (0, fixedWord10x0, 5), (0, fixedWord18x0, 5), (0, fixedWord72x0, 5), (0, fixedWord2x8, 5), (0, fixedWord8x2, 5), (0, fixedWord16x2, 5), (0, fixedWord64x8, 5), (0, fixedWord3x0, 4), (0, fixedWord5x0, 4), (0, fixedWord6x0, 4), (0, fixedWord17x0, 4), (0, fixedWord20x0, 4), (0, fixedWord65x0, 4), (0, fixedWord68x0, 4), (0, fixedWord24x2, 4), (0, fixedWord26x0, 4), (0, fixedWord66x8, 4), (0, fixedWord74x0, 4)].toArray

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains_ax95D : fastax95D = ax95D := by decide +kernel

def fastax111D : RichDomains := [(0, fixedWord1x0, 7), (48, fixedWord1x0, 7), (101, fixedWord1x0, 7), (129, fixedWord1x0, 7), (141, fixedWord1x0, 7), (210, fixedWord1x0, 7), (0, fixedWord2x0, 7), (30, fixedWord2x0, 7), (48, fixedWord2x0, 7), (111, fixedWord2x0, 7), (127, fixedWord2x0, 7), (130, fixedWord2x0, 7), (192, fixedWord2x0, 7), (210, fixedWord2x0, 7), (222, fixedWord2x0, 7), (273, fixedWord2x0, 7), (291, fixedWord2x0, 7), (292, fixedWord2x0, 7), (300, fixedWord2x0, 7), (0, fixedWord4x0, 7), (10, fixedWord4x0, 7), (49, fixedWord4x0, 7), (91, fixedWord4x0, 7), (127, fixedWord4x0, 7), (128, fixedWord4x0, 7), (136, fixedWord4x0, 7), (172, fixedWord4x0, 7), (209, fixedWord4x0, 7), (217, fixedWord4x0, 7), (299, fixedWord4x0, 7), (0, fixedWord8x0, 7), (101, fixedWord8x0, 7), (127, fixedWord8x0, 7), (137, fixedWord8x0, 7), (141, fixedWord8x0, 7), (210, fixedWord8x0, 7), (218, fixedWord8x0, 7), (0, fixedWord32x0, 7), (20, fixedWord32x0, 7), (56, fixedWord32x0, 7), (91, fixedWord32x0, 7), (101, fixedWord32x0, 7), (110, fixedWord32x0, 7), (139, fixedWord32x0, 7), (172, fixedWord32x0, 7), (182, fixedWord32x0, 7), (190, fixedWord32x0, 7), (191, fixedWord32x0, 7), (220, fixedWord32x0, 7), (253, fixedWord32x0, 7), (271, fixedWord32x0, 7), (272, fixedWord32x0, 7), (273, fixedWord32x0, 7), (299, fixedWord32x0, 7), (300, fixedWord32x0, 7), (301, fixedWord32x0, 7), (0, fixedWord64x0, 7), (48, fixedWord64x0, 7), (127, fixedWord64x0, 7), (208, fixedWord64x0, 7), (210, fixedWord64x0, 7), (291, fixedWord64x0, 7), (0, fixedWord0x2, 6), (0, fixedWord0x4, 6), (0, fixedWord6x0, 5), (0, fixedWord1x4, 5), (0, fixedWord8x2, 5), (0, fixedWord32x2, 5), (0, fixedWord64x4, 5), (0, fixedWord9x0, 4), (0, fixedWord7x0, 4), (0, fixedWord14x0, 4), (0, fixedWord40x2, 4), (0, fixedWord65x4, 4)].toArray

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains_ax111D : fastax111D = ax111D := by decide +kernel

def fastax127D : RichDomains := [(0, fixedWord1x0, 10), (111, fixedWord1x0, 10), (119, fixedWord1x0, 10), (120, fixedWord1x0, 10), (121, fixedWord1x0, 10), (129, fixedWord1x0, 10), (131, fixedWord1x0, 10), (138, fixedWord1x0, 10), (182, fixedWord1x0, 10), (201, fixedWord1x0, 10), (282, fixedWord1x0, 10), (302, fixedWord1x0, 10), (0, fixedWord2x0, 10), (121, fixedWord2x0, 10), (221, fixedWord2x0, 10), (271, fixedWord2x0, 10), (0, fixedWord4x0, 10), (0, fixedWord8x0, 10), (0, fixedWord16x0, 10), (101, fixedWord16x0, 10), (218, fixedWord16x0, 10), (0, fixedWord32x0, 10), (91, fixedWord32x0, 10), (101, fixedWord32x0, 10), (109, fixedWord32x0, 10), (110, fixedWord32x0, 10), (111, fixedWord32x0, 10), (119, fixedWord32x0, 10), (139, fixedWord32x0, 10), (191, fixedWord32x0, 10), (272, fixedWord32x0, 10), (299, fixedWord32x0, 10), (0, fixedWord64x0, 9), (100, fixedWord64x0, 9), (101, fixedWord64x0, 9), (109, fixedWord64x0, 9), (110, fixedWord64x0, 9), (111, fixedWord64x0, 9), (119, fixedWord64x0, 9), (120, fixedWord64x0, 9), (121, fixedWord64x0, 9), (127, fixedWord64x0, 9), (181, fixedWord64x0, 9), (182, fixedWord64x0, 9), (190, fixedWord64x0, 9), (191, fixedWord64x0, 9), (192, fixedWord64x0, 9), (273, fixedWord64x0, 9), (282, fixedWord64x0, 9), (283, fixedWord64x0, 9), (291, fixedWord64x0, 9), (292, fixedWord64x0, 9), (0, fixedWord0x2, 7), (0, fixedWord0x4, 7), (0, fixedWord0x8, 7), (0, fixedWord0x16, 7), (0, fixedWord3x0, 7), (0, fixedWord5x0, 7), (0, fixedWord6x0, 7), (0, fixedWord9x0, 7), (0, fixedWord10x0, 7), (0, fixedWord17x0, 7), (0, fixedWord18x0, 7), (0, fixedWord20x0, 7), (0, fixedWord24x0, 7), (0, fixedWord33x0, 7), (0, fixedWord34x0, 7), (0, fixedWord36x0, 7), (0, fixedWord40x0, 7), (0, fixedWord48x0, 7), (0, fixedWord65x0, 7), (0, fixedWord66x0, 7), (0, fixedWord80x0, 7), (0, fixedWord96x0, 7), (0, fixedWord12x0, 6), (0, fixedWord68x0, 6), (0, fixedWord72x0, 6), (0, fixedWord1x4, 6), (0, fixedWord1x16, 6), (0, fixedWord2x8, 6), (0, fixedWord2x16, 6), (0, fixedWord4x16, 6), (0, fixedWord8x2, 6), (0, fixedWord16x2, 6), (0, fixedWord16x4, 6), (0, fixedWord32x2, 6), (0, fixedWord32x8, 6), (0, fixedWord64x4, 6), (0, fixedWord64x8, 6), (0, fixedWord14x0, 5), (0, fixedWord19x0, 5), (0, fixedWord21x0, 5), (0, fixedWord26x0, 5), (0, fixedWord69x0, 5), (0, fixedWord74x0, 5), (0, fixedWord84x0, 5), (0, fixedWord104x0, 5), (0, fixedWord3x16, 5), (0, fixedWord5x16, 5), (0, fixedWord6x16, 5), (0, fixedWord17x4, 5), (0, fixedWord24x2, 5), (0, fixedWord34x8, 5), (0, fixedWord40x2, 5), (0, fixedWord48x2, 5), (0, fixedWord65x4, 5), (0, fixedWord66x8, 5), (0, fixedWord80x4, 5), (0, fixedWord96x8, 5), (0, fixedWord11x0, 4), (0, fixedWord13x0, 4), (0, fixedWord25x0, 4), (0, fixedWord35x0, 4), (0, fixedWord37x0, 4), (0, fixedWord38x0, 4), (0, fixedWord41x0, 4), (0, fixedWord44x0, 4), (0, fixedWord49x0, 4), (0, fixedWord73x0, 4), (0, fixedWord82x0, 4), (0, fixedWord88x0, 4), (0, fixedWord97x0, 4), (0, fixedWord7x16, 4), (0, fixedWord30x0, 4), (0, fixedWord56x2, 4), (0, fixedWord81x4, 4), (0, fixedWord85x0, 4), (0, fixedWord98x8, 4), (0, fixedWord106x0, 4)].toArray

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains_ax127D : fastax127D = ax127D := by decide +kernel

def fastGraph (m : Nat) : Sig := if m = 127 then graph else graphGoal m

theorem graph_match (m : Nat) : fastGraph m = graphGoal m := by
  by_cases h : m = 127
  · subst m
    decide +kernel
  · simp only [fastGraph, h, ite_false]

end DomainEquality
