import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896_aux.Geometry

def inc (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

def avoids (S : Finset (Fin 13)) (l : Fin 13) : Prop := ∀ p ∈ S, ¬inc p l

def maximal (S : Finset (Fin 13)) : Prop :=
  ∀ p ∉ S, ∃ l : Fin 13, avoids S l ∧ inc p l

def generic (S : Finset (Fin 13)) : Prop :=
  (¬∃ l : Fin 13, ∀ p ∈ S, inc p l) ∧
  ¬∃ p : Fin 13, ∀ l : Fin 13, avoids S l → inc p l

def decode (m : ℕ) : Finset (Fin 13) := Finset.univ.filter fun p => m.testBit p.val

def pointTable : List ℕ :=
  [7, 7, 7, 13, 19, 35, 67, 131, 259, 517, 1027, 2051, 4099,
    7, 7, 7, 14, 19, 35, 67, 131, 259, 518, 1027, 2051, 4099,
    7, 7, 7, 13, 21, 37, 69, 133, 262, 517, 1029, 2053, 4102,
    13, 14, 13, 13, 25, 41, 73, 137, 265, 524, 1033, 2057, 4105,
    19, 19, 21, 25, 19, 50, 81, 146, 273, 529, 1041, 2065, 4113,
    35, 35, 37, 41, 50, 35, 97, 162, 289, 545, 1057, 2081, 4129,
    67, 67, 69, 73, 81, 97, 67, 193, 321, 577, 1090, 2114, 4161,
    131, 131, 133, 137, 146, 162, 193, 131, 385, 641, 1153, 2177, 4225,
    259, 259, 262, 265, 273, 289, 321, 385, 259, 769, 1281, 2305, 4354,
    517, 518, 517, 524, 529, 545, 577, 641, 769, 517, 1537, 2561, 4609,
    1027, 1027, 1029, 1033, 1041, 1057, 1090, 1153, 1281, 1537, 1027, 3074, 5121,
    2051, 2051, 2053, 2057, 2065, 2081, 2114, 2177, 2305, 2561, 3074, 2051, 6145,
    4099, 4099, 4102, 4105, 4113, 4129, 4161, 4225, 4354, 4609, 5121, 6145, 4099]

def lineTable : List ℕ :=
  [52, 224, 208, 164, 324, 148, 304, 52, 100, 84, 52, 52, 112,
    224, 41, 193, 289, 328, 137, 41, 97, 41, 73, 168, 41, 104,
    208, 193, 19, 131, 578, 529, 19, 19, 67, 19, 146, 81, 82,
    164, 289, 131, 7, 262, 133, 35, 7, 7, 7, 38, 37, 162,
    324, 328, 578, 262, 14, 524, 266, 70, 14, 14, 14, 76, 74,
    148, 137, 529, 133, 524, 13, 25, 21, 13, 13, 28, 13, 152,
    304, 41, 19, 35, 266, 25, 19, 19, 35, 19, 26, 25, 26,
    52, 97, 19, 7, 70, 21, 19, 7, 7, 7, 38, 21, 50,
    100, 41, 67, 7, 14, 13, 35, 7, 7, 7, 14, 13, 42,
    84, 73, 19, 7, 14, 13, 19, 7, 7, 7, 14, 13, 26,
    52, 168, 146, 38, 14, 28, 26, 38, 14, 14, 14, 28, 26,
    52, 41, 81, 37, 76, 13, 25, 21, 13, 13, 28, 13, 56,
    112, 104, 82, 162, 74, 152, 26, 50, 42, 26, 26, 56, 26]

def mixedTable : List ℕ :=
  [7, 41, 19, 7, 7, 13, 19, 7, 7, 7, 7, 13, 7,
    7, 7, 19, 7, 14, 7, 19, 7, 7, 7, 14, 7, 26,
    52, 7, 7, 7, 14, 13, 7, 7, 7, 7, 14, 13, 7,
    7, 41, 7, 7, 14, 13, 25, 7, 13, 13, 14, 13, 26,
    52, 7, 19, 7, 7, 21, 19, 19, 7, 19, 26, 21, 26,
    52, 41, 7, 35, 7, 7, 35, 35, 35, 7, 38, 37, 42,
    84, 73, 67, 7, 70, 7, 7, 67, 67, 67, 7, 69, 74,
    148, 137, 131, 131, 7, 133, 7, 7, 131, 131, 134, 7, 138,
    276, 265, 259, 259, 262, 7, 259, 7, 7, 259, 262, 265, 7,
    7, 545, 529, 517, 518, 517, 7, 517, 7, 7, 518, 517, 530,
    1060, 7, 1027, 1027, 1034, 1029, 1027, 7, 1027, 7, 7, 1029, 1034,
    2068, 2057, 7, 2051, 2054, 2053, 2051, 2051, 7, 2051, 7, 7, 2058,
    4116, 4105, 4099, 7, 4102, 4105, 4099, 4099, 4099, 7, 4102, 7, 7]

def pointWitness (p q : Fin 13) : Finset (Fin 13) :=
  decode (pointTable.getD (13 * p.val + q.val) 0)

def lineWitness (l m : Fin 13) : Finset (Fin 13) :=
  decode (lineTable.getD (13 * l.val + m.val) 0)

def mixedWitness (p l : Fin 13) : Finset (Fin 13) :=
  decode (mixedTable.getD (13 * p.val + l.val) 0)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma point_coverage : ∀ p q : Fin 13,
    maximal (pointWitness p q) ∧ generic (pointWitness p q) ∧
    p ∈ pointWitness p q ∧ q ∈ pointWitness p q := by
  unfold maximal generic avoids inc
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma line_coverage : ∀ l m : Fin 13,
    maximal (lineWitness l m) ∧ generic (lineWitness l m) ∧
    avoids (lineWitness l m) l ∧ avoids (lineWitness l m) m := by
  unfold maximal generic avoids inc
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma mixed_coverage : ∀ p l : Fin 13, ¬inc p l →
    maximal (mixedWitness p l) ∧ generic (mixedWitness p l) ∧
    p ∈ mixedWitness p l ∧ avoids (mixedWitness p l) l := by
  unfold maximal generic avoids inc
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma point_completion : ∀ p q r l : Fin 13,
    inc p l → inc q l → inc r l → p ≠ q → p ≠ r → q ≠ r →
    ∀ m : Fin 13, ¬inc p m → ¬inc q m → ¬inc r m → inc (4 * l - p - q - r) m := by
  unfold inc
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma line_completion : ∀ l m n p : Fin 13,
    inc p l → inc p m → inc p n → l ≠ m → l ≠ n → m ≠ n →
    ∀ q : Fin 13, ¬inc q l → ¬inc q m → ¬inc q n → inc q (4 * p - l - m - n) := by
  unfold inc
  decide +kernel

lemma generic_no_point_triple (S : Finset (Fin 13)) (h : generic S)
    (p q r l : Fin 13) (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S)
    (hpl : inc p l) (hql : inc q l) (hrl : inc r l)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : False := by
  apply h.2
  refine ⟨4 * l - p - q - r, ?_⟩
  intro m hm
  exact point_completion p q r l hpl hql hrl hpq hpr hqr m
    (hm p hp) (hm q hq) (hm r hr)

lemma generic_no_line_triple (S : Finset (Fin 13)) (h : generic S)
    (l m n p : Fin 13) (hl : avoids S l) (hm : avoids S m) (hn : avoids S n)
    (hpl : inc p l) (hpm : inc p m) (hpn : inc p n)
    (hlm : l ≠ m) (hln : l ≠ n) (hmn : m ≠ n) : False := by
  apply h.1
  refine ⟨4 * p - l - m - n, ?_⟩
  intro q hq
  exact line_completion l m n p hpl hpm hpn hlm hln hmn q
    (hl q hq) (hm q hq) (hn q hq)

end PEqualNP.Outside.L_meta_1896_aux.Geometry
