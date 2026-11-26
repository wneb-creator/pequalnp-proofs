import PEqualNP.Defs

-- The search engine is adapted from PEqualNP.Outside.L_meta_1673 by Trey Kind (pull request 6929, Apache License 2.0).
-- This file declares its own data types (records for the search state and inductive predicates).

namespace PEqualNP.Outside.L_meta_17357
section hz1
variable {R : ℕ → ℕ}
def op (d : Bool) (a b : ℕ) : ℕ := bif d then a ||| b else a &&& b
def Al (R : ℕ → ℕ) (d : Bool) (a b : ℕ) : Prop := (R a &&& R b) ≤ (bif d then 1 else 0)
def Z0 : ℕ → ℕ := fun _ => 0
inductive Sol (R : ℕ → ℕ) (m T : ℕ) : ℕ → Set ℕ → Prop
  | done {q : ℕ} {S : Set ℕ} : T ∈ S → Sol R m T q S
  | un {q : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S → Sol R m T q (insert (a ^^^ m) S) → Sol R m T (q + 1) S
  | bi {q : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S → Al R d a b →
      Sol R m T q (insert (op d a b) S) → Sol R m T (q + 1) S
inductive Live (R : ℕ → ℕ) (m T : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | stop : Live R m T 0 0 {T}
  | un {k t : ℕ} {a : ℕ} {U : Finset ℕ} : Live R m T k t (insert (a ^^^ m) U) →
      Live R m T (k + 1) (t + 1) (insert a U)
  | bi {k t : ℕ} {d : Bool} {a b : ℕ} {U : Finset ℕ} : a ≠ b → Al R d a b → Live R m T k t (insert (op d a b) U) →
      Live R m T (k + 1) t (insert a (insert b U))
def C (m : ℕ) (S : Set ℕ) : Set ℕ := S ∪ {0, m}
def Un (m a : ℕ) (S S' : Finset ℕ) : Prop := ∃ U, S = insert a U ∧ S' = insert (a ^^^ m) U
def Bi (R : ℕ → ℕ) (d : Bool) (a b : ℕ) (S S' : Finset ℕ) : Prop :=
  a ≠ b ∧ ∃ U, S = insert a (insert b U) ∧ S' = insert (op d a b) U ∧ Al R d a b
def Min (R : ℕ → ℕ) (m T k t : ℕ) (S : Finset ℕ) : Prop := Live R m T k t S ∧ ∀ q < k, ¬ Sol Z0 m T q (C m S)
def phi (a n : ℕ) (X : Finset ℕ) : Finset ℕ := insert a (X.erase n)
abbrev Cst (n x : ℕ) : Prop := x &&& n = 0 ∨ x &&& n = n
def Im (n : ℕ) (S : Finset ℕ) : Set ℕ := (fun x => x &&& n) '' (S : Set ℕ)
def sepb (N : ℕ) (d : Bool) (w i : ℕ) : Bool :=
  bif d then xor (w.testBit i) (w.testBit (N + i)) else w.testBit i && !w.testBit (N + i)
def pos' (t : ℕ) : Bool := decide (0 < t)
def Uq (N : ℕ) (e : Bool) (S : Finset ℕ) (a i : ℕ) : Prop :=
  sepb N e a i = true ∧ ∀ c ∈ S, c ≠ a → sepb N e c i = false
end hz1
section hz2
variable {R : ℕ → ℕ}
variable {N m T : ℕ}
def Lg (N m T i : ℕ) : Prop := m.testBit i = true ∧ m.testBit (N + i) = true ∧ T.testBit i = true ∧ T.testBit (N + i) = false
def Ht (N m T : ℕ) (e : Bool) (S : Finset ℕ) (a b : ℕ) : Prop := ∃ i1 i2 j1 j2, Lg N m T i1 ∧ Lg N m T i2 ∧ Lg N m T j1 ∧ Lg N m T j2 ∧
  (∀ w ∈ S, w.testBit i1 = w.testBit i2) ∧ (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) ∧
  Uq N e S a i1 ∧ Uq N e S b i2 ∧ Uq N e S a j1 ∧ Uq N e S b j2 ∧ a.testBit i1 = a.testBit j1 ∧ b.testBit i2 = b.testBit j2
end hz2
section hz3
variable {R : ℕ → ℕ}
open Finset in
def Acc (n T k b : ℕ) (D : ℕ → ℕ) (S : Finset ℕ) : Prop :=
  ∀ U ⊆ S, ∀ q, q + b < k + ∑ w ∈ S \ U, D w → ¬ Sol Z0 n (T &&& n) q (C n (Im n U))
inductive Kd
  | N | K0 | KA | KC
def Kd.ok (n : ℕ) (d : Bool) (a c : ℕ) : Kd → Prop
  | .N => True
  | .K0 => Cst n (op d a c)
  | .KA => op d a c &&& n = a &&& n
  | .KC => op d a c &&& n = c &&& n
def Kd.del (la lc : ℕ) : Kd → ℕ
  | .N => 0
  | .K0 => 1 + la + lc
  | .KA => 1 + lc
  | .KC => 1 + la
def Kd.out (la lc : ℕ) : Kd → ℕ
  | .N => 1 + la + lc
  | .K0 => 0
  | .KA => la
  | .KC => lc
def Kd.kpa (x : ℕ) : Kd → ℕ
  | .N => 0
  | .K0 => x
  | .KA => 0
  | .KC => x
def Kd.kpc (x : ℕ) : Kd → ℕ
  | .N => 0
  | .K0 => x
  | .KA => x
  | .KC => 0
structure DStep (κ : Kd) (D D' : ℕ → ℕ) (g a c : ℕ) (S' : Finset ℕ) : Prop where
  hg : D' g ≤ κ.out (if a ∈ S' then 0 else D a) (if c ∈ S' then 0 else D c)
  ha : a ∈ S' → D' a ≤ κ.kpa (D a)
  hc : c ∈ S' → D' c ≤ κ.kpc (D c)
  ho : ∀ w ∈ S', w ≠ g → w ≠ a → w ≠ c → D' w ≤ D w
structure W where
  s : Nat
  a : Nat
  b : Nat
  c : Nat
  r : Nat
  d : Nat
structure Cm where
  a : List Nat
  b : List Nat
def NN : Nat := 1119
def AA : Nat := 0x3ffff7effffdf7fffefbf7bffff7fffefbffff7bffff7df77fffdf7defbeffffdefbbfffef7ddf7bdbfffef7ddf7bdbfffef7ddf7bdbef7b7dddffed6d6ab56dad6ad55fffd6dab6d56db5555afffeb5fffdbfffadb5ab6db556db5ad555abfffab6adfffdb6fffed5ab5b5adb5b6adb6adfffdbfffb5ad6adadadafffefffedb6db7fff0000000000000000
def HX : Nat := 0x1292954a9252952aa0002925492a924aaaa500014a00024000524a54924aa924a52aaa540005495200024900012a54a4a524a49524952000240004a5295252525000100012492480000000000000000000
def HY : Nat := 0x4000081000020800010408400008000104000084000082088000208210410000210440001082208424000108220842400010822084241084822200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
end hz3
noncomputable section hz4
variable {R : ℕ → ℕ}
def st (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f m) (Nat.succ n)
def sp (d : Bool) (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) (Bool.rec (motive := fun _ => Nat) (Nat.land s l) l d)
def cov (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor (sp d l w.s) ih) v
def twice (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (sp d l w.s) (cov d l t)) ih) v
def hit (f e : Nat) : Bool := (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (true) (false) (Nat.beq (Nat.land (Nat.land f e) HY) 0))) (false) (Nat.beq (Nat.land (Nat.land f e) HX) 0))
def hits (f : Nat) (m : List Nat) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun e _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (hit f e))) (m))
def flag (d : Bool) (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (sp d l w.s) o) AA
def rect (d : Bool) (l o : Nat) (v : List W) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => (Bool.rec (motive := fun _ => Bool) (ih (flag d l o w :: m)) (true) (hits (flag d l o w) m))) v
def app (x y : List Nat) : List Nat := List.rec (motive := fun _ => List Nat) y (fun e _ ih => e :: ih) x
def join (k : List Cm → Bool) (f : Nat) (cs : List Cm) : List Nat → List Nat → List Cm → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → List Cm → Bool) (fun S O R => k (⟨S, O⟩ :: R))
    (fun c _ ih S O R => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih S O (c :: R)) (ih (app c.a S) (app c.b O) R) (hits f c.b))
      (Bool.rec (motive := fun _ => Bool) (ih (app c.b S) (app c.a O) R) true (hits f c.b)) (hits f c.a)) cs
def bip (l o : Nat) (v : List W) : List Cm → Bool :=
  List.rec (motive := fun _ => List Cm → Bool) (fun _ => false)
    (fun w _ ih cs => (fun f => join ih f cs [f] [] []) (flag false l o w)) v
def anyE (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) false (fun f t ih => Bool.rec (motive := fun _ => Bool) ih true (hits f t)) m
def rmF (f : Nat) (m : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun e t ih => Bool.rec (motive := fun _ => List Nat) (e :: ih) t (hit f e)) m
def star (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) true (fun f t ih => Bool.rec (motive := fun _ => Bool) ih
  (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false (anyE (rmF f t))) false (hits f (rmF f t))) (anyE t)) (hits f t)) m
def flk (l o : Nat) (v : List W) : (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k []) (fun w _ ih k => (fun f => ih (fun r => k (f :: r))) (flag false l o w)) v
def rm (x y : Nat) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (ih h) (Nat.beq w.s y)) (ih h) (Nat.beq w.s x)) v
def ins (o : W) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [o]) (fun w t ih h => Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive := fun _ => Bool) (h (o :: w :: t)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def child (f : Nat → List W → Bool) (g : Nat) (kb : Bool) (mk : (List W → Bool) → Bool) (z : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) (st z (fun z => mk (f z))) false kb) (Nat.beq (Nat.land z g) g)
def laneL (w : Nat) (L : List Nat) : Nat := List.rec (motive := fun _ => Nat) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih w) d) L
def WL (N : Nat) : Nat := Nat.succ (Nat.mul 2 N)
def FM2 (N : Nat) : Nat := Nat.sub (Nat.pow 2 (Nat.mul 2 N)) 1
def R16 (N : Nat) : Nat := laneL (WL N) (List.replicate 16 1)
def MM16 (N : Nat) : Nat := laneL (WL N) (List.replicate 16 (FM2 N))
def GG16 (N : Nat) : Nat := laneL (WL N) (List.replicate 16 (Nat.pow 2 (Nat.mul 2 N)))
def MD16 (N : Nat) : Nat := Nat.sub (Nat.pow 2 (WL N)) 32
def U16 : Nat := laneL 5 (List.replicate 16 1)
def zflG (N np q nc : Nat) : Nat := Nat.land (Nat.sub U16 (Nat.mod (Nat.shiftRight (Nat.land (Nat.add (Nat.land (Nat.mul (Nat.land q (FM2 N)) (R16 N)) np) (MM16 N)) (GG16 N)) (Nat.mul 2 N)) (MD16 N))) nc
def zfl (np q nc : Nat) : Nat := zflG NN np q nc
def MU (f : Nat) : Nat := Nat.mul 31 f
def rmk (sa : Nat) (ka : Bool) (da : Nat) (sc : Nat) (kc : Bool) (dc : Nat) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive := fun _ => Bool) (ih h) (st dc fun d => W.rec (motive := fun _ => Bool) (fun s a b c r0 _ => ih (fun r => h (⟨s, a, b, c, r0, d⟩ :: r))) w) kc) (Nat.beq w.s sc))
    (Bool.rec (motive := fun _ => Bool) (ih h) (st da fun d => W.rec (motive := fun _ => Bool) (fun s a b c r0 _ => ih (fun r => h (⟨s, a, b, c, r0, d⟩ :: r))) w) ka) (Nat.beq w.s sa)) v
def rmkB (sa da sc dc d0 : Nat) (v : List W) (h : List W → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (rmk sa true da sc true dc v h) (h v) (Nat.beq d0 0)
def put (m s x y : Nat) (v : List W) (d : Nat) (h : List W → Bool) : Bool :=
  st s fun s => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (st x fun x1 => st y fun y1 => st (Nat.lor x y) fun w => st d fun d => ins ⟨s, x1, y1, w, 0, d⟩ v h) false (Nat.beq s m)) false (Nat.beq s 0)
def kids (c : Bool → ((List W → Bool) → Bool) → Nat → Bool) (e n z u w fA fC : Nat) (a c' : W) (oa oc ka kc kb : Bool) (mk : Nat → (List W → Bool) → Bool) : Bool :=
  (fun fN sA sC =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
        (c kb (fun h => mk fN (fun r => rmkB a.s (Nat.land sC a.d) c'.s (Nat.land sA c'.d) (Nat.add a.d c'.d) r h)) (Nat.sub (Nat.sub z a.c) c'.c))
        (Nat.ble (Nat.succ (Nat.succ n)) e)) true
      (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
          (c kc (fun h => mk (Nat.add fN (Nat.land (MU (Nat.add fN fA)) a.d)) (fun r => rmk a.s false 0 c'.s true (Nat.land sA c'.d) r h)) (Nat.sub (Nat.sub z (Nat.land sC a.d)) c'.c)) oa) true
        (Bool.rec (motive := fun _ => Bool) false
          (c ka (fun h => mk (Nat.add fN (Nat.land (MU (Nat.add fN fC)) c'.d)) (fun r => rmk a.s true (Nat.land sC a.d) c'.s false 0 r h)) (Nat.sub (Nat.sub z a.c) (Nat.land sA c'.d))) oc)) (Nat.ble (Nat.succ n) e))) true
      (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
        (c false (fun h => mk (Nat.add (Nat.add fN (Nat.land (MU (Nat.add fN fA)) a.d)) (Nat.land (MU (Nat.add fN fC)) c'.d)) (fun r => rmk a.s false 0 c'.s false 0 r h)) (Nat.sub (Nat.sub z (Nat.land sC a.d)) (Nat.land sA c'.d))) oc) oa))
  (Nat.sub (Nat.sub (Nat.sub u w) fA) fC) (MU (Nat.add w fA)) (MU (Nat.add w fC))
def mid (f : Nat → List W → Bool) (m g np e n z : Nat) (v : List W) (a c : W) (oa oc ka kc kb : Bool) (s x y : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    ((fun u w => (fun nc => st (zfl np (Nat.xor a.s s) nc) fun eA => st (zfl np (Nat.xor c.s s) (Nat.sub nc eA)) fun eC =>
      Bool.rec (motive := fun _ => Bool) false
        (st (Nat.sub (Nat.sub (Nat.add z (Nat.land a.c c.c)) w) (Nat.add eA eC)) fun z =>
          kids (child f g) e n z u w (Nat.add eA (Nat.sub c.c (Nat.land c.c w))) (Nat.add eC (Nat.sub a.c (Nat.land a.c w))) a c oa oc ka kc kb (put m s x y v))
        (Nat.beq (Nat.land (Nat.sub (Nat.sub (Nat.add z (Nat.land a.c c.c)) w) (Nat.add eA eC)) g) g))
      (Nat.sub u (Nat.lor (Nat.lor a.c c.c) w))) (Nat.shiftRight g 4) (Nat.lor x y))
    (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g)
def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => Bool.rec (motive := fun _ => Bool) ih true (Bool.rec (motive := fun _ => Bool)
    (st (Nat.xor a.s m) fun s => st (Nat.sub z a.c) fun z => (fun u =>
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false (st u fun d1 => ins ⟨s, a.b, a.a, a.c, 0, d1⟩ v (fun v => child (f s) g false (rmk a.s true 0 a.s true 0 v) (Nat.sub z a.c))) (Nat.ble (Nat.succ n) e)) true
        (Bool.rec (motive := fun _ => Bool) false (st (Nat.add u a.d) fun d1 => ins ⟨s, a.b, a.a, a.c, 0, d1⟩ v (fun v => child (f s) g false (rmk a.s false 0 a.s false 0 v) z)) (Nat.ble n e)))
      (Nat.sub (Nat.shiftRight g 4) a.c)) false (Nat.beq (Nat.succ a.s) q))) r
def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t
def wst (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twice d l v)
def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t
def cv (d : Bool) (l : Nat) (v : List W) (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false b (Nat.beq (cov d l v) l)) b d
end hz4
section hz5
variable {R : ℕ → ℕ}
def Rep (v : List W) (S : Finset ℕ) : Prop := (v.map W.s).Nodup ∧ (v.map W.s).toFinset = S
def segsX : List (ℕ × ℕ) := [(63, 79), (79, 82), (82, 85), (85, 88), (88, 91), (91, 94), (94, 97), (97, 100), (100, 116), (116, 132), (132, 134), (134, 137), (137, 140), (140, 142), (142, 145), (145, 148), (148, 150), (150, 153), (153, 156), (156, 158), (158, 160), (160, 163), (163, 165), (165, 168), (168, 170), (170, 173), (173, 175), (175, 178), (178, 194), (194, 197), (197, 213), (213, 216), (216, 218), (218, 220), (220, 223), (223, 226), (226, 229), (229, 232), (232, 234), (234, 236), (236, 239), (239, 242), (242, 245), (245, 247), (247, 250), (250, 253), (253, 256), (256, 258), (258, 261), (261, 263), (263, 266), (266, 269), (269, 271), (271, 274), (274, 276), (276, 278), (278, 281), (281, 283), (283, 285), (285, 288), (288, 304), (304, 307), (307, 310), (310, 313), (313, 329), (329, 332), (332, 334), (334, 336), (336, 339), (339, 342), (342, 344), (344, 346), (346, 362), (362, 364), (364, 366), (366, 369), (369, 371), (371, 373), (373, 375), (375, 377), (377, 379), (379, 381), (381, 384), (384, 386), (386, 389), (389, 391), (391, 394), (394, 397), (397, 400), (400, 403), (403, 405), (405, 407), (407, 409), (409, 411), (411, 414), (414, 417), (417, 420), (420, 423), (423, 426), (426, 428), (428, 430), (430, 433), (433, 435), (435, 438), (438, 441), (441, 444), (444, 446), (446, 462), (462, 465), (465, 481), (481, 483), (483, 486), (486, 488), (488, 504), (504, 506), (506, 509), (509, 511), (511, 513), (513, 515), (515, 517), (517, 519), (519, 521), (521, 523), (523, 526), (526, 529), (529, 532), (532, 535), (535, 537), (537, 539), (539, 541), (541, 544), (544, 547), (547, 550), (550, 552), (552, 554), (554, 557), (557, 560), (560, 563), (563, 565), (565, 581), (581, 583), (583, 585), (585, 587), (587, 589), (589, 592), (592, 594), (594, 596), (596, 599), (599, 601), (601, 604), (604, 606), (606, 609), (609, 612), (612, 615), (615, 617), (617, 619), (619, 622), (622, 624), (624, 626), (626, 628), (628, 631), (631, 633), (633, 636), (636, 639), (639, 641), (641, 644)]
def segsY : List (ℕ × ℕ) := [(644, 657), (657, 661), (661, 665), (665, 671), (671, 674), (674, 679), (679, 684), (684, 690), (690, 693), (693, 698), (698, 703), (703, 709), (709, 713), (713, 719), (719, 724), (724, 742), (742, 745), (745, 750), (750, 755), (755, 761), (761, 765), (765, 771), (771, 776), (776, 794), (794, 797), (797, 802), (802, 807), (807, 813), (813, 817), (817, 823), (823, 828), (828, 846), (846, 850), (850, 856), (856, 861), (861, 880), (880, 886), (886, 892), (892, 897), (897, 903), (903, 909), (909, 927), (927, 931), (931, 937), (937, 943), (943, 962), (962, 967), (967, 986), (986, 992), (992, 1011), (1011, 1030), (1030, 1035), (1035, 1042), (1042, 1048), (1048, 1067), (1067, 1073), (1073, 1092), (1092, 1099), (1099, 1118)]
def segOk (s : ℕ × ℕ) : Bool := decide (s.1 < s.2) && decide (AA % 2 ^ s.2 + 2 ^ (s.1 + 1) = 2 ^ s.2 + AA % 2 ^ s.1) &&
  !AA.testBit s.1 && !AA.testBit s.2
def bitsOf (L : List (ℕ × ℕ)) : ℕ := L.foldr (fun s x => 2 ^ s.2 ||| x) 0
def Same (L : List (ℕ × ℕ)) (i j : ℕ) : Prop := ∃ s ∈ L, s.1 < i ∧ i < s.2 ∧ s.1 < j ∧ j < s.2
def Good (l s : ℕ) : Prop := (∀ i j, Same segsX i j → l.testBit i = true → l.testBit j = true → s.testBit i = s.testBit j) ∧
  (∀ i j, Same segsY i j → l.testBit i = true → l.testBit j = true → s.testBit (NN + i) = s.testBit (NN + j))
def pk (n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range n, f j * 2 ^ (5 * j)
def isPk (n x : ℕ) : Prop := ∀ i, x.testBit i = true → i % 5 = 0 ∧ i / 5 < n
def fl (w : W) (j : ℕ) : ℕ := (w.c.testBit (5 * j)).toNat
def cnt (v : List W) (j : ℕ) : ℕ := (v.map (fun w => fl w j)).sum
structure WOk (P : List ℕ) (w : W) : Prop where
  pa : isPk P.length w.a
  pb : isPk P.length w.b
  ec : w.c = w.a ||| w.b
  ca : ∀ j < P.length, w.a.testBit (5 * j) = true → w.s &&& P.getD j 0 = 0
  cb : ∀ j < P.length, w.b.testBit (5 * j) = true → w.s &&& P.getD j 0 = P.getD j 0
def lane (w n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range n, f j * 2 ^ (w * j)
def fb (x j : ℕ) : ℕ := (x.testBit (5 * j)).toNat
structure StOk (P : List ℕ) (T l k z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  bud : ∃ (b : ℕ → ℕ) (D : ℕ → ℕ → ℕ), (∀ j < P.length, b j ≤ 15) ∧ (∀ j < P.length, Acc (P.getD j 0) T k (b j) (D j) S) ∧
    (∀ w ∈ v, w.d = pk P.length (fun j => D j w.s)) ∧ (∀ j < P.length, k + ∑ s ∈ S, D j s ≤ 15) ∧ z = pk P.length (fun j => 16 + b j - cnt v j)
structure Ctx (P : List ℕ) (l m g np T : ℕ) : Prop where
  lg : ∀ i, l.testBit i = true → Lg NN m T i ∧ AA.testBit i = true
  hP : ∀ j < P.length, P.getD j 0 &&& m = P.getD j 0 ∧ T &&& P.getD j 0 ≠ 0 ∧ T &&& P.getD j 0 ≠ P.getD j 0
  hg : g = pk P.length (fun _ => 16)
  hnp : ∃ f : ℕ → ℕ, (∀ j < 16, f j < 2 ^ (2 * NN)) ∧ np = lane (WL NN) 16 f ∧ ∀ j < P.length, j < 16 → P.getD j 0 &&& f j = P.getD j 0
inductive Shape (o a c : W) (v : List W) : Bool → Bool → List W → Prop
  | ff {r} : (a :: c :: r).Perm (o :: v) → Shape o a c v false false r
  | tf {r} : (c :: r).Perm (o :: v) → Shape o a c v true false r
  | ft {r} : (a :: r).Perm (o :: v) → Shape o a c v false true r
  | tt {r} : r.Perm (o :: v) → Shape o a c v true true r
def opW (d : Bool) (a c : W) : W := bif d then ⟨a.s ||| c.s, a.a &&& c.a, a.b ||| c.b, (a.a &&& c.a) ||| (a.b ||| c.b), 0, 0⟩
  else ⟨a.s &&& c.s, a.a ||| c.a, a.b &&& c.b, (a.a ||| c.a) ||| (a.b &&& c.b), 0, 0⟩
def wd (w : W) (d : ℕ) : W := ⟨w.s, w.a, w.b, w.c, w.r, d⟩
def upd (sa da sc dc : ℕ) (w : W) : W := bif Nat.beq w.s sa then wd w da else bif Nat.beq w.s sc then wd w dc else w
def kp (sa : ℕ) (ka : Bool) (sc : ℕ) (kc : Bool) (w : W) : Bool := bif Nat.beq w.s sa then ka else bif Nat.beq w.s sc then kc else true
def kdOf (fo FA FC : ℕ) : Kd := if fo = 1 then .K0 else if FA = 1 then .KA else if FC = 1 then .KC else .N
def fAo (e o c : ℕ) : ℕ := Nat.add e (Nat.sub c (Nat.land c o))
def fNo (u w fA fC : ℕ) : ℕ := Nat.sub (Nat.sub (Nat.sub u w) fA) fC
def notW (m : ℕ) (a : W) : W := ⟨a.s ^^^ m, a.b, a.a, a.c, 0, 0⟩
end hz5
noncomputable section hz6
variable {R : ℕ → ℕ}
def len (v : List W) : Nat := List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) v
def geo (w n : Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun _ ih => Nat.add (Nat.shiftLeft ih w) 1) n
def LNN : Nat := Nat.mul 12 NN
def LN2 : Nat := Nat.mul 24 NN
def LN4 : Nat := Nat.mul 48 NN
def LM1 : Nat := Nat.mul 13 NN
def LM2 : Nat := Nat.mul 26 NN
def LM4 : Nat := Nat.mul 52 NN
def RL : Nat := geo NN 12
def PLN : Nat := Nat.pow 2 LNN
def AAR : Nat := Nat.mul AA RL
def HXR : Nat := Nat.mul HX (geo NN 84)
def HYR : Nat := Nat.mul HY (geo NN 84)
def MRR : Nat := Nat.mul (Nat.sub (Nat.pow 2 NN) (Nat.pow 2 64)) (geo NN 84)
def TOPR : Nat := Nat.shiftLeft (geo NN 72) LM1
def GMD : Nat := Nat.sub (Nat.pow 2 (Nat.sub NN 1)) 1
def pkd (d : Bool) (l : Nat) (v : List W) : Nat := List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.shiftLeft (sp d l w.s) (Nat.mul NN (len t))) ih) v
def dbl (m x : Nat) : Nat := Nat.lor x (Nat.shiftLeft x m)
def eg2 (G : Nat) : Nat := Nat.shiftRight (Nat.mod (Nat.land (Nat.land (Nat.add (Nat.land G HXR) MRR) (Nat.add (Nat.land G HYR) MRR)) TOPR) GMD) 1
def eg1 (F : Nat) : Nat := eg2 (Nat.land (dbl LN4 (dbl LN2 (dbl LNN F))) (dbl LM4 (dbl LM2 (dbl LM1 F))))
def edg (d : Bool) (l o : Nat) (v : List W) : Nat := eg1 (Nat.mod (Nat.add (Nat.land (pkd d l v) (Nat.mul o RL)) AAR) PLN)
def f12c (b : Nat) : Nat := Nat.land (Nat.lor b (Nat.shiftRight b 12)) 4095
def f12b (a : Nat) : Nat := f12c (Nat.lor a (Nat.shiftRight a 24))
def f12 (w : Nat) : Nat := f12b (Nat.lor w (Nat.shiftRight w 48))
def f13c (b : Nat) : Nat := Nat.land (Nat.lor b (Nat.shiftRight b 13)) 4095
def f13b (a : Nat) : Nat := f13c (Nat.lor a (Nat.shiftRight a 26))
def f13 (w : Nat) : Nat := f13b (Nat.lor w (Nat.shiftRight w 52))
def nbr (e S : Nat) : Nat := Nat.lor (f12 (Nat.land e (Nat.mul S 302268352895954163081217))) (f13 (Nat.land e (Nat.mul S 4723519685917965029377)))
def bfs (e : Nat) (fuel : Nat) : Nat → Nat → (Nat → Bool) → Bool := Nat.rec (motive := fun _ => Nat → Nat → (Nat → Bool) → Bool) (fun _ _ _ => false)
  (fun _ ih A B k => st (Nat.lor A (nbr e B)) (fun a => st (Nat.lor B (nbr e a)) (fun b => Bool.rec (motive := fun _ => Bool) true
    (Bool.rec (motive := fun _ => Bool) (ih a b k) (k (Nat.lor a b)) (Nat.beq (Nat.lor A B) (Nat.lor a b))) (Nat.beq (Nat.land a b) 0)))) fuel
def nonb (e : Nat) (fuel : Nat) : Nat → Bool := Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
  (fun _ ih r => Bool.rec (motive := fun _ => Bool) (bfs e 12 (Nat.gcd r 2048) 0 (fun c => ih (Nat.sub r (Nat.land r c)))) false (Nat.beq r 0)) fuel
def nonbip (e : Nat) : Bool := nonb e 12 (Nat.lor (f12 e) (f13 e))
def tch (i : Nat) : Nat := Nat.lor (Nat.mul i 302268352895954163081217) (Nat.mul i 4723519685917965029377)
def del (e i : Nat) : Nat := Nat.xor (Nat.lor e (tch i)) (tch i)
def ne0 (e : Nat) : Bool := Bool.rec (motive := fun _ => Bool) true false (Nat.beq e 0)
def kF (_ : Nat) : Bool := false
def kF2 (_ _ : Nat) : Bool := false
def kT2 (_ _ : Nat) : Bool := true
def tst1 (h : Nat) (F : (Nat → Bool) → (Nat → Nat → Bool) → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (F (fun i => ne0 (del h i)) kT2) false (nonbip h)
def tri5 (a L r : Nat) : Nat := Bool.rec (motive := fun _ => Nat) (Nat.lor a (Nat.gcd L 4096)) r (Nat.beq L 0)
def tri4 (h i N k r : Nat) : Nat := tri5 (Nat.lor i k) (Nat.land (nbr h k) N) r
def tri3 (h i N M r : Nat) : Nat := Bool.rec (motive := fun _ => Nat) (tri4 h i N (Nat.gcd M 4096) r) r (Nat.beq M 0)
def tri2 (h i N r : Nat) : Nat := tri3 h i N (Nat.land (nbr h N) N) r
def tri1 (h i r : Nat) : Nat := tri2 h i (nbr h i) r
def tri (h : Nat) (fuel : Nat) : Nat → Nat := Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
  (fun _ ih r => Bool.rec (motive := fun _ => Nat) (tri1 h (Nat.gcd r 2048) (ih (Nat.sub r (Nat.gcd r 2048)))) 0 (Nat.beq r 0)) fuel
def k1 (h i : Nat) : Bool := nonbip (del h i)
def k2 (h i j : Nat) : Bool := ne0 (del (del h i) j)
def k3 (h T i : Nat) : Bool := Bool.rec (motive := fun _ => Bool) (nonbip (del h i)) true (Nat.beq (Nat.land i T) 0)
def k4 (h T i j : Nat) : Bool := Bool.rec (motive := fun _ => Bool) true (ne0 (del (del h i) j)) (Nat.beq (Nat.land (Nat.lor i j) T) (Nat.lor i j))
def tst2 (h : Nat) (F : (Nat → Bool) → (Nat → Nat → Bool) → Bool) : Bool := st (tri h 12 (f12 h)) (fun T => Bool.rec (motive := fun _ => Bool) (F (k3 h T) (k4 h T)) (F (k1 h) (k2 h)) (Nat.beq T 0))
def tsn (d : Bool) (l e : Nat) (v : List W) (F : (Nat → Bool) → (Nat → Nat → Bool) → Bool) : Bool :=
  (fun n => (fun o => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F kF kF2) (st (edg false l o v) (fun h => tst2 h F)) (Nat.beq (Nat.succ (Nat.succ n)) e))
      (st (edg false l o v) (fun h => tst1 h F)) (Nat.beq (Nat.succ n) e))
    (Bool.rec (motive := fun _ => Bool) false (F kF kF2) (Nat.beq (edg d l o v) 0)) (Nat.beq n e)) (wst d l v)) (len v)
end hz6
section hz7
variable {R : ℕ → ℕ}
structure X where
  w : W
  s : Nat
  q : Nat
  u : Nat
  i : Nat
end hz7
noncomputable section hz8
variable {R : ℕ → ℕ}
def mkX (d : Bool) (l o : Nat) (v : List W) : List X :=
  List.rec (motive := fun _ => List X) [] (fun w t ih => ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o, Nat.shiftLeft 1 (len t)⟩ :: ih) v
def f0 (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (a c : W) (ia ic da dc s x y : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (h a c true true true true true s x y) (Nat.beq (Nat.lor da dc) 0)
def f1 (κ : Nat → Bool) (κ2 : Nat → Nat → Bool) (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (a c : W) (ia ic da dc s x y : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (h a c false false true true false s x y) false (κ2 ia ic))
      (Bool.rec (motive := fun _ => Bool) (h a c false true false true (κ2 ia ic) s x y) (Bool.rec (motive := fun _ => Bool) (h a c false false true true false s x y) false (κ2 ia ic)) (κ ia)) (Nat.beq dc 0))
    (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (h a c true false true false (κ2 ia ic) s x y) (Bool.rec (motive := fun _ => Bool) (h a c false false true true false s x y) false (κ2 ia ic)) (κ ic))
      (h a c true true (κ ia) (κ ic) (κ2 ia ic) s x y) (Nat.beq dc 0))
    (Nat.beq da 0)
def f2 (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (a c : W) (ia ic da dc s x y : Nat) : Bool :=
  h a c (Nat.beq da 0) (Nat.beq dc 0) false false false s x y
def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool) (a c : X) : Bool :=
  X.rec (motive := fun _ => Bool) (fun a s q u i => X.rec (motive := fun _ => Bool) (fun c s' q' u' j => Bool.rec (motive := fun _ => Bool)
    (h a c i j (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)) true
    (h a c i j (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b))) c) a
def scan (p : X → Bool) (xs : List X) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun c _ jh => (Bool.rec (motive := fun _ => Bool) (jh) (true) (p c))) (xs))
def pairs (h : X → X → Bool) (xs : List X) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a r ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (scan (h a) r))) (xs))
def pairsP (q : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (h a c) (false) (Nat.beq c.s q))) xs) (Nat.beq a.s q))) xs
def pairsQ (q q' : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (false) (h a c) (Nat.beq c.s q'))) xs) (Nat.beq a.s q))) xs
def fr (xs : List X) : List X := List.rec (motive := fun _ => List X) [] (fun a _ ih => Bool.rec (motive := fun _ => List X) ih (a :: ih) (Nat.beq a.w.r 0)) xs
def fs (xs : List X) : List X := List.rec (motive := fun _ => List X) [] (fun a _ ih => Bool.rec (motive := fun _ => List X) (a :: ih) ih (Nat.beq a.w.r 0)) xs
def pairsN (h : X → X → Bool) (xs : List X) : Bool :=
  Bool.rec (motive := fun _ => Bool) (scan (fun a => scan (h a) (fs xs)) (fr xs)) true (pairs h (fr xs))
def pairsS (h : X → X → Bool) (xs : List X) : Bool := pairs h (fs xs)
def nodeH (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (d : Bool) (l e n : Nat) (v : List W) (κ : Nat → Bool) (κ2 : Nat → Nat → Bool) (go : (X → X → Bool) → List X → Bool) : Bool :=
  (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive := fun _ => Bool) (go (pair (f1 κ κ2 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ (Nat.succ n)) e)) (Nat.ble n e))
    (mkX d l (wst d l v) v)
def node (f : Nat → List W → Bool) (d : Bool) (l m g np e n z : Nat) (v : List W) (κ : Nat → Bool) (κ2 : Nat → Nat → Bool) (go : (X → X → Bool) → List X → Bool) : Bool :=
  nodeH (mid f m g np e (Nat.pred n) z v) d l e n v κ κ2 go
def forb (fm fh s : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight fh (Nat.mod s fm)) 1) 1
def mid1 (fm fh : Nat) (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (a c : W) (oa oc ka kc kb : Bool) (s x y : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (h a c oa oc ka kc kb s x y) false (forb fm fh s)
def node1 (f : Nat → List W → Bool) (d : Bool) (l m g np fm fh e n z : Nat) (v : List W) (κ : Nat → Bool) (κ2 : Nat → Nat → Bool) (go : (X → X → Bool) → List X → Bool) : Bool :=
  nodeH (mid1 fm fh (mid f m g np e (Nat.pred n) z v)) d l e n v κ κ2 go
def mv (F : Nat → Nat → Nat → List W → Bool) (l m g np k t z : Nat) (v : List W) (κ : Nat → Bool) (κ2 : Nat → Nat → Bool) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tsn (pos s) l (Nat.sub k s) v (fun κ κ2 =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tsn (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun κ κ2 =>
          st (Nat.sub k 3) fun k3 => node (F k3 s) (pos s) l m g np (Nat.sub (Nat.sub k 2) s) (len v) z v κ κ2 (pairsQ q q'))))
          m g (Nat.sub (Nat.sub k 1) s) (len v) z (Nat.succ q) v v)) true
        (st (Nat.sub k 2) fun k2 => node (F k2 s) (pos s) l m g np (Nat.sub (Nat.sub k 1) s) (len v) z v κ κ2 (pairsP q)))))
      m g (Nat.sub k s) n z 0 v v)) true
    (st (Nat.sub k 1) fun k1 => node (F k1 t) (pos t) l m g np (Nat.sub k t) n z v κ κ2 pairsN)) (len v)
def look (l m g np : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tsn (pos t) l (Nat.sub (Nat.succ k) t) v (fun κ κ2 => mv ih l m g np k t z v κ κ2)) true (Nat.ble (len v) 1)) fuel
def look1 (l m g np fm fh K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tsn (pos t) l (Nat.sub (Nat.succ k) t) v (fun κ κ2 =>
      Bool.rec (motive := fun _ => Bool) (mv (look l m g np k) l m g np k t z v κ κ2) true
        (st (Nat.sub k 1) fun k1 => node1 (ih k1 t) (pos t) l m g np fm fh (Nat.sub k t) (len v) z v κ κ2 pairsS))) true (Nat.ble (len v) 1)) fuel
end hz8
section hz9
variable {R : ℕ → ℕ}
def Pos (v : List W) (w : W) (i : ℕ) : Prop := ∃ pre t, v = pre ++ w :: t ∧ t.length = i
structure KP (R : ℕ → ℕ) (m T k' t : ℕ) (S : Finset ℕ) (v : List W) (κ : ℕ → Bool) (κ2 : ℕ → ℕ → Bool) : Prop where
  g1 : ∀ {d : Bool} {a b : ℕ} {S1 : Finset ℕ} {k0 : ℕ}, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → a ∈ S1 → b ∉ S1 →
    ∀ w i, Pos v w i → w.s = a → κ (2 ^ i) = false
  g2 : ∀ {d : Bool} {a b : ℕ} {S1 : Finset ℕ} {k0 : ℕ}, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → a ∈ S1 → b ∈ S1 →
    ∀ wa i wb j, Pos v wa i → wa.s = a → Pos v wb j → wb.s = b → κ2 (2 ^ i) (2 ^ j) = false
def segOkR (s : ℕ × ℕ) : Bool := decide (s.2 < NN) && (List.range 12).all (fun i =>
  decide (AAR % 2 ^ (NN * i + s.2) + 2 ^ (NN * i + s.1 + 1) = 2 ^ (NN * i + s.2) + AAR % 2 ^ (NN * i + s.1)) && !AAR.testBit (NN * i + s.2))
def laneOk (p : ℕ) : Bool := decide (MRR % 2 ^ (NN * p + NN) + 2 ^ (NN * p + 63 + 1) = 2 ^ (NN * p + NN) + MRR % 2 ^ (NN * p + 63)) &&
  !MRR.testBit (NN * p + NN) && !HXR.testBit (NN * p + NN) && !HXR.testBit (NN * p + 63) && !HYR.testBit (NN * p + NN) && !HYR.testBit (NN * p + 63)
def Hq (d : Bool) (l o a b : ℕ) : Prop :=
  (∃ s ∈ segsX, ∃ i1 i2, s.1 < i1 ∧ i1 < s.2 ∧ s.1 < i2 ∧ i2 < s.2 ∧ (Nat.land (sp d l a) o).testBit i1 = true ∧ (Nat.land (sp d l b) o).testBit i2 = true) ∧
  (∃ s ∈ segsY, ∃ i1 i2, s.1 < i1 ∧ i1 < s.2 ∧ s.1 < i2 ∧ i2 < s.2 ∧ (Nat.land (sp d l a) o).testBit i1 = true ∧ (Nat.land (sp d l b) o).testBit i2 = true)
def Adj (e x y : ℕ) : Prop := ∃ p, e.testBit p = true ∧ ((p % 13 = x ∧ p % 12 = y) ∨ (p % 13 = y ∧ p % 12 = x))
def Eb (e : ℕ) : Prop := ∀ p, e.testBit p = true → 12 ≤ p ∧ p < 84
def Pc (e : ℕ) (c : ℕ → Bool) : Prop := ∀ x y, Adj e x y → c x ≠ c y
def Cod (R : ℕ → ℕ) (v : List W) : Prop := ∀ w ∈ v, w.r = 0 ∨ w.r = R w.s
def RR (R : ℕ → ℕ) : Prop := ∀ d a b, R a ≠ 0 → R b ≠ 0 → ¬ Al R d a b
def xof (d : Bool) (l o : ℕ) (w : W) (i : ℕ) : X := ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o, 2 ^ i⟩
def modeH (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (n e : ℕ) (κ : ℕ → Bool) (κ2 : ℕ → ℕ → Bool) : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ (Nat.succ n)) e then f2 h else f1 κ κ2 h) else f0 h
def dfc (d d' : Bool) (l o : ℕ) (a c : W) : ℕ := bif d' then Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s NN)
  else Nat.xor (Nat.land (Nat.land (sp d l a.s) o) c.s) (Nat.land (sp d l a.s) o)
def rawP : List ℕ := [0x3ffff00000001ffff80f80000000000007fffe07c000000000000000000000000001ffff03e0f81e1f03c3e0e0000800000804000082054400000000000222102a442054840a980004430c2000004200204148918460a48c3052400000404008014618460a88c151000001050505054405462492482a3000000000000000001103020240c10120608108210347e060021030a3d4301f00408c10420828c78c0f802016104410848200e104410849292e07c1f03c3e0787c1c206100020101800010400000020010000544420000840001bfff8001886184000018c004080002308c000186000004081818030068c308c0001800004210a1a1a1a0000fffedb6db7fffeadfebf2195dd8de, 0x3ffff01f8000000000000000000000000000000000000000000000000000000000001ffff03e0f81e1ffff7800fbc01f7803ee00000000040020001008200c004002230c2282c100c582018c403000000000000000008881040294050201849100e000000010420850095020184403884211212121100e100c61861880a00000000000000000202c04040b026f05803f00022c0025808022c10006c0411005302084104008b020880268208821091137407c1f03c10b74f001f7803ef007dc005800008800c0002010000001800c4618450580000b0000180000004000005000042111020000280a00001b6fffe1020404218430a036a00001bfffb18c62c2c2c2fffe0000c30c30000cde57ebfbe6dfd4f, 0x1ffff81ffffbe00000000000000000000001ffff03e0f81e1ffff7800fbc01ffff7bee00001f7bd80000000001000900000000031c820410280482a80019c4a033c00670008000048230c2c0a0ac00c695b000638d8031c2040808120240524052063c00c71a06816c016c032c032c6c06c019a000000000000000004210080884040242010210441008420125f10025d507c0008240410820810140411151b007c1f03c151a4f001f780149a4f7dc00003ef7b0000420000600160000000000010c0860501b055000000b5fffc000000300001b04618581415800002b6000001b00000c1830302c0580ad80adfffc0000340d02d802d800000000d80d800008769d3e1bf0f2ec6, 0x3fffe03e07c07fffef001ffff7800fbc01ffff7bee00001ffff7beefbdec0000000000000000000010840a000dc900480292002aa5007e0000f8001f10401012002804800aa00001e9495200fc00007c6a01ac016d80056db0001b800371ad0016d6c0000ec00ec6db00007a000000000000000008440101110080488020420884010880208440208180082252b8007c0f80a5781e0019530f001f78019524f7dc000018d24f7ddf7bd80000000088000100040021081400001600b0056c00555afffe00000000002180206c00501b001540000002b6adfffc000000d4035802db000adb6000000000035a002dad80000000000db600000090367f54237be926, 0x7fffe03ffff7c00000000000000000000000000003fffef8007df000000001ffff7bee00001ffff7beefbdec00000000000000000000000000200480016056006098b6d0002b6da800030580060b00c1612001080002920000aa850c170000060b00030586ad400016d2da00000061300c261ad6b400000030a830a849249185c00000000000000001008120de20406f102f8000108101102400881400601104443385f000fbe0220402011932f7dc000011926f7ddf7bd810060040100402008040410200c00b0002c0ac0000016da00056db50000000000000000002c002b000056c0001555abfff800000000000000d5a80002db5b60000000000000035ad6800000000000000db6db7ffff6c30a1f71ba46d1, 0x1ffff807fffef8000000001ffff8000001ffffbc000000003fffefbef000000000001ffff7beefbdec0000000000000000000000000000000000000606b5000016b0000ca90b695b4800000000655000caa0195416da8000002b6da9400001a9400000d4a0006a506ad5a9a800000000000d5201aa41294a44848486ab06ab000000355000000000000000003f00600de019f0800c008021f060200c021f06780806008042399f7de000004180401113cf7ddf7bd8003800802008000381080208804110084800cc0d6a00002d6000000016dab6d000000000000000000000002db580000056db5ac00000000000000000000000d5ab5b58000000000000000000035ad6adadadafffefffe000000000ebea746cce75171b, 0x1ffffbffff7c000000000000003fffefbef7df7fffef7dc0000000000000000000000000000000000000000000000000029000000012942a20ce00000000000000000660000cc0019816d2d5b6928000000000003180000018c0000c604a952d2c4989304920419c083380000000000000cc00cc00000006600000000000000000208184060061030030410431f1863e30f910180110182000623e1f7defbec47e1efba01c001004010201c021004110201c021044100082211081030d600000002d6ad55fffc000000000000000000000000000002db5ab6db5000000000000000000000000000000d5ab5b5adb5b6adb6adfffdbfff8000000000000000000000000000087f8da6ffcecbfe7, 0x1ffffbf0000000000000001ffffbffff7dffffbdffffbefb800000000000000000000000000000000000000000000000000000000000000000000006b4b512b4c0000008f000000000000000004780008f0011e0049ac524da82492d6002853e0012049f00924f8000000000000000000009e0013c00000000000004f004f0000000278000000000000000003f0e07e803800401c0820021fe043fc0fa1fe07a1fe07df703c0082004100780080001e004210820001e004208822101e00420882109040021001c0d6d6ab56d80000000000000000000000000000000000000002db5ab6db556db5ad555abfffab6adfffdb6fffe00000000000000000000000000000000000000000000000000000000f5966fde6be7baf8, 0x1ffffbf7fffefbffff7dfbc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000426a55a268421408f00024d126824928008780010f0009e000000000000000000000001c0000000e0000070000000000000000000000e0001c000000000000007000700000000380000000000000000003ff007effc01f7fe00fbf7be0007c00083e00003e00041007c0010410820f80010823e000840104203e000841104003e00084110421208424011e00d6d6ab56dad6ad55fffd6dab6d56db5555afffeb5fffdbfff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001d7f8fad45d7fdfd]
def TG : ℕ := 0x3ffff7effffdf7fffefbf7bffff7fffefbffff7bffff7df77fffdf7defbeffffdefbbfffef7ddf7bdbfffef7ddf7bdbfffef7ddf7bdbef7b7dddffed6d6ab56dad6ad55fffd6dab6d56db5555afffeb5fffdbfffadb5ab6db556db5ad555abfffab6adfffdb6fffed5ab5b5adb5b6adb6adfffdbfffb5ad6adadadafffefffedb6db7fffffffffffffffffff
def FPM : ℕ := 2 ^ 64 - 1
def FULL : ℕ := 2 ^ NN - 1
def kz (Z : ℕ) : ℕ := (List.range 9).foldr (fun i x => bif Nat.testBit Z i then Nat.lor x (Nat.land (Nat.lor (rawP.getD i 0) (Nat.shiftRight (rawP.getD i 0) NN)) FULL) else
  (bif Nat.testBit Z (i + 9) then Nat.lor x (Nat.xor FULL (Nat.land (rawP.getD i 0) (Nat.lor (Nat.shiftRight (rawP.getD i 0) NN) FPM))) else x)) 0
def lz (Z : ℕ) : ℕ := Nat.land AA (Nat.xor (kz Z) FULL)
def fz (Z : ℕ) : ℕ := Nat.land FPM (Nat.xor (kz Z) FULL)
def mz (Z : ℕ) : ℕ := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) NN)
def tz (Z : ℕ) : ℕ := Nat.land TG (mz Z)
def MASKN : ℕ := 2 ^ (2 * NN) - 1
def tw (e : Bool × ℕ × ℕ) : ℕ := bif Nat.beq e.2.2 9 then rawP.getD e.2.1 0 ^^^ MASKN else op e.1 (rawP.getD e.2.1 0) (rawP.getD e.2.2 0)
def rawL (E : List (Bool × ℕ × ℕ)) : List ℕ := rawP ++ E.map tw
def WZ (E : List (Bool × ℕ × ℕ)) (Z : ℕ) : Set ℕ := {x | ∃ w ∈ rawL E, x = w &&& mz Z}
def Imp (E : List (Bool × ℕ × ℕ)) (Z L : ℕ) : Prop := ∀ q < L, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z))
def segGood (w o : ℕ) (s : ℕ × ℕ) : Bool :=
  Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) 0 || Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) (2 ^ (s.2 - s.1 - 1) - 1)
def trivE (e : Bool × ℕ × ℕ) (Z : ℕ) : Bool :=
  (fun m => (fun s => Nat.beq s 0 || Nat.beq s m || rawP.any (fun w => Nat.beq (Nat.land w m) s)) (Nat.land (tw e) m)) (mz Z)
def tabV (e : Bool × ℕ × ℕ) (own : List ℕ) (x : ℕ × ℕ) : ℕ := bif own.any (fun c => Nat.beq c x.1) || trivE e x.1 then x.2 else Nat.sub x.2 1
def tabE (e : Bool × ℕ × ℕ) (own : List ℕ) (raw : List (ℕ × ℕ)) : List (ℕ × ℕ) := raw.map (fun x => (x.1, tabV e own x))
def PZ (Q : List (ℕ × ℕ)) : List ℕ := Q.map (fun e => mz e.1)
def pOk (Z : ℕ) (Q : List (ℕ × ℕ)) : Bool := !Nat.beq (tz Z) 0 && !Nat.beq (tz Z) (mz Z) && Q.all (fun e => Nat.beq (Nat.land (mz e.1) (mz Z)) (mz e.1) &&
  !Nat.beq (tz e.1) 0 && !Nat.beq (tz e.1) (mz e.1))
def npOf (P : List ℕ) : ℕ := laneL (WL NN) ((List.range 16).map (fun j => P.getD j 0))
end hz9
noncomputable section hz10
variable {R : ℕ → ℕ}
def pL (L : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih 5) d) L
end hz10
section hz11
variable {R : ℕ → ℕ}
def bit01 (b : Bool) : ℕ := bif b then 1 else 0
end hz11
noncomputable section hz12
variable {R : ℕ → ℕ}
def fl0 (s : ℕ) (P : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun n _ ih => Nat.add (Nat.shiftLeft ih 5) (bit01 (Nat.beq (Nat.land s n) 0))) P
def fl1 (s : ℕ) (P : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun n _ ih => Nat.add (Nat.shiftLeft ih 5) (bit01 (Nat.beq (Nat.land s n) n))) P
def mkW (P : List ℕ) (s : ℕ) : W := ⟨s, fl0 s P, fl1 s P, Nat.lor (fl0 s P) (fl1 s P), 3, 0⟩
def addN (o : ℕ) (v : List ℕ) : List ℕ := List.rec (motive := fun _ => List ℕ) [o]
  (fun w t ih => Bool.rec (motive := fun _ => List ℕ) (w :: ih) (Bool.rec (motive := fun _ => List ℕ) (o :: w :: t) (w :: t) (Nat.beq o w)) (Nat.ble w o)) v
def avl (m : ℕ) (L : List ℕ) : List ℕ := List.rec (motive := fun _ => List ℕ) []
  (fun w _ ih => Bool.rec (motive := fun _ => List ℕ) (Bool.rec (motive := fun _ => List ℕ) (addN (Nat.land w m) ih) ih (Nat.beq (Nat.land w m) m)) ih (Nat.beq (Nat.land w m) 0)) L
def mkA (P : List ℕ) (L : List ℕ) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun s _ ih h => st s fun s => st (fl0 s P) fun a => st (fl1 s P) fun b => st (Nat.lor a b) fun c => ih fun r => h (⟨s, a, b, c, 3, 0⟩ :: r)) L
def frcP (L : List ℕ) : (List ℕ → Bool) → Bool := List.rec (motive := fun _ => (List ℕ → Bool) → Bool) (fun h => h [])
  (fun s _ ih h => st s fun s => ih fun r => h (s :: r)) L
def anySub (d : Bool) (l : ℕ) (v : List W) : ℕ → (List W → Bool) → Bool := List.rec (motive := fun _ => ℕ → (List W → Bool) → Bool) (fun _ h => h [])
  (fun w t ih c h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (ih c h) (Nat.beq (Nat.lor c (cov d l t)) l)) true
    (st (Nat.lor c (sp d l w.s)) fun c => ih c fun r => h (w :: r))) v
def sumc (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add w.c ih) v
def MM : ℕ := 214
def hb (H x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1
def fbit (fm fh s : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight fh (Nat.mod s fm)) 1) 1
def hasP (p : ℕ) (v : List W) : Bool := Bool.rec (motive := fun _ => Bool)
  (List.rec (motive := fun _ => Bool) false (fun w _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w.s p)) v) true (Nat.beq p 0)
end hz12
section hz13
variable {R : ℕ → ℕ}
def Srt (v : List ℕ) : Prop := v.Pairwise (fun a b => b < a)
def mFull (M : List (ℕ × ℕ)) : Bool := (List.range MM).all (fun r => M.any (fun p => hb p.1 r)) && M.any (fun p => Nat.beq p.2 1)
def FF : ℕ := 2 ^ MM - 1
def fbOk (E F : List (Bool × ℕ × ℕ)) (fb : ℕ × ℕ) : Bool :=
  (fun m => (fun W => (fun G => W.all (fun x => W.all (fun y => Nat.beq x y ||
      ((!fbit fb.1 fb.2 (Nat.land x y) || G.any (Nat.beq (Nat.land x y))) && (!fbit fb.1 fb.2 (Nat.lor x y) || G.any (Nat.beq (Nat.lor x y)))))))
    (F.map (fun e => Nat.land (tw e) m))) ((rawL E).map (fun w => Nat.land w m))) (mz 0)
def pwr (E : List (Bool × ℕ × ℕ)) (Z : ℕ) : ℕ := (E.map fun e => Nat.land (tw e) (mz Z)).headD 0
open Classical in
noncomputable def RZ (E : List (Bool × ℕ × ℕ)) (Z : ℕ) : ℕ → ℕ := fun s => if s ∈ WZ E Z then 3 else 0
end hz13
noncomputable section hz14
variable {R : ℕ → ℕ}
def frcQ (Q : List (ℕ × ℕ)) : (List (ℕ × ℕ) → Bool) → Bool := List.rec (motive := fun _ => (List (ℕ × ℕ) → Bool) → Bool) (fun h => h [])
  (fun x _ ih h => st x.1 fun c => st x.2 fun L => ih fun r => h ((c, L) :: r)) Q
def lnW (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih) v
def anyN (h : ℕ → Bool) (L : List ℕ) : Bool := List.rec (motive := fun _ => Bool) false (fun a _ ih => Bool.rec (motive := fun _ => Bool) ih true (h a)) L
def pre (E : List (Bool × ℕ × ℕ)) (Q : List (ℕ × ℕ)) (Z K : ℕ) (h : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) : Bool :=
  frcQ Q fun Q => frcP (PZ Q) fun P => st (lz Z) fun l => st (mz Z) fun m => st (npOf P) fun np => st (pL (Q.map fun _ => 16)) fun g => st (pL (Q.map fun e => 16 + (K - e.2))) fun B =>
    st (pwr E Z) fun p => frcP (avl m (rawL E)) fun sg => mkA P sg fun v => h l m np g B p v
def startG (f : ℕ → List W → Bool) (g B K t p : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child f g false (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble (lnW v) (Nat.sub (Nat.succ K) t))) (hasP p v)
def chkG (top : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) (E : List (Bool × ℕ × ℕ)) (Q : List (ℕ × ℕ)) (fb : ℕ × ℕ) (Z K t H ph : ℕ) : Bool :=
  st fb.1 fun fm => st fb.2 fun fh => pre E Q Z K fun l m np g B p v => anySub (pos t) l v 0 fun r => startG (fun z r => top l m g np fm fh K H ph K t z r) g B K t p r
def chkT (top : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) (E : List (Bool × ℕ × ℕ)) (Q : List (ℕ × ℕ)) (fb : ℕ × ℕ) (Z K : ℕ) (ts : List ℕ) (H ph : ℕ) : Bool :=
  st fb.1 fun fm => st fb.2 fun fh => pre E Q Z K fun l m np g B p v => anyN (fun t => anySub (pos t) l v 0 fun r => startG (fun z r => top l m g np fm fh K H ph K t z r) g B K t p r) ts
end hz14
section hz15
variable {R : ℕ → ℕ}
def TopOk (top : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) : Prop :=
  ∀ {P : List ℕ} {l m g np T : ℕ}, Ctx P l m g np T → ∀ {R : ℕ → ℕ}, (∀ d a b, R a ≠ 0 → R b ≠ 0 → ¬ Al R d a b) → (∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) →
    ∀ {fm fh K k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)} {Fs : Set ℕ}, mFull M = true → (∀ p ∈ M, top l m g np fm fh K p.1 p.2 k t z v = false) →
      StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) → ∀ {k' : ℕ}, k' ≤ k → Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) →
      (∀ d x y, x ≠ y → R x ≠ 0 → R y ≠ 0 → fbit fm fh (op d x y) = true → op d x y ∈ Fs) →
      (∀ s ∈ Fs, ∀ q < k', ¬ Sol Z0 m T q (C m (insert s ({x | R x ≠ 0} ∪ (S : Set ℕ))))) → False
def MW (R : ℕ → ℕ) (m T k : ℕ) (S : Finset ℕ) : Prop := ∀ q < k, ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))
def MF (R : ℕ → ℕ) (m T k : ℕ) (Fs : Set ℕ) (S : Finset ℕ) : Prop := ∀ s ∈ Fs, ∀ q < k, ¬ Sol Z0 m T q (C m (insert s ({x | R x ≠ 0} ∪ (S : Set ℕ))))
end hz15
noncomputable section hz16
variable {R : ℕ → ℕ}
def pairsC (H : ℕ) (h : X → X → Bool) (xs : List X) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a r ih => Bool.rec (motive := fun _ => Bool) ih true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r)) xs
def topC (l m g np fm fh K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tsn (pos t) l (Nat.sub (Nat.succ k) t) v (fun κ κ2 =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g np k) l m g np k t z v κ κ2) (Nat.beq ph 1)) true
      (st (Nat.sub k 1) fun k1 => node1 (look1 l m g np fm fh K K k1 t) (pos t) l m g np fm fh (Nat.sub k t) (len v) z v κ κ2 (fun h xs => pairsC H h (fs xs))))) true (Nat.ble (len v) 1)
end hz16
section hz17
variable {R : ℕ → ℕ}
def P1 (R : ℕ → ℕ) (P : List ℕ) (l m T : ℕ) (Fs : Set ℕ) (f : ℕ → ℕ → ℕ → List W → Bool) : Prop :=
  ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), f k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
    ∀ k' ≤ k, Live Z0 m T k' t S → MW R m T k' S → MF R m T k' Fs S → False
abbrev TopT := ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool
noncomputable def okR (top : TopT) (E : List (Bool × ℕ × ℕ)) (Q : List (ℕ × ℕ)) (x : ℕ × ℕ) : Bool :=
  pOk x.1 Q && Nat.ble x.2 15 && (Q.any (fun y => Nat.ble x.2 y.2) || !chkT top E Q (1, 0) x.1 (x.2 - 1) (List.range x.2) FF 1)
def pr (T : List (ℕ × ℕ)) (c : ℕ) : List (ℕ × ℕ) := T.filter (fun y => Nat.beq (Nat.land c y.1) c && !Nat.beq c y.1)
def pick (T : List (ℕ × ℕ)) (cs : List ℕ) : List (ℕ × ℕ) := cs.filterMap (fun c => T.find? (fun x => Nat.beq x.1 c))
noncomputable def okU (top : TopT) (T : List (ℕ × ℕ)) (r : (ℕ × ℕ) × List ℕ) : Bool := okR top [] (pick T r.2) r.1
noncomputable def okO (top : TopT) (e : Bool × ℕ × ℕ) (own : List ℕ) (raw : List (ℕ × ℕ)) (r : (ℕ × ℕ) × List ℕ) : Bool :=
  raw.all (fun x => !Nat.beq x.1 r.1.1 || Nat.beq x.2 r.1.2) && okR top [e] (tabE e own (pick raw r.2)) r.1
def inC (cs : List ℕ) (x : ℕ × ℕ) : Bool := cs.any (fun c => Nat.beq c x.1)
def fbOkH (Z : ℕ) (E F : List (Bool × ℕ × ℕ)) (pv : List ℕ) (fb : ℕ × ℕ) : Bool :=
  (fun m => (fun W => (fun G => W.all (fun x => W.all (fun y => Nat.beq x y || pv.any (fun H => hb H (x + y)) ||
      ((!fbit fb.1 fb.2 (Nat.land x y) || G.any (Nat.beq (Nat.land x y))) && (!fbit fb.1 fb.2 (Nat.lor x y) || G.any (Nat.beq (Nat.lor x y)))))))
    (F.map (fun e => Nat.land (tw e) m))) ((rawL E).map (fun w => Nat.land w m))) (mz Z)
def FsH (Z : ℕ) (E F : List (Bool × ℕ × ℕ)) (pv : List ℕ) : Set ℕ :=
  {s | (∃ f ∈ F, s = tw f &&& mz Z) ∨ ∃ (d : Bool) (x y H : ℕ), x ∈ WZ E Z ∧ y ∈ WZ E Z ∧ x ≠ y ∧ H ∈ pv ∧ hb H (x + y) = true ∧ s = op d x y}
def seqOk (Z : ℕ) (E F : List (Bool × ℕ × ℕ)) : List ℕ → List (ℕ × ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | pv, p :: M => fbOkH Z E F pv p.2.2 && seqOk Z E F (p.1 :: pv) M
abbrev Sq := ℕ × ℕ × ℕ × ℕ
noncomputable def okSq (E : List (Bool × ℕ × ℕ)) (Q : List (ℕ × ℕ)) (Z K : ℕ) (M : List Sq) (r : ℕ × List ℕ) : Bool :=
  (fun p : Sq => st p.1 fun H => st p.2.1 fun ph => !chkT topC E Q p.2.2 Z K r.2 H ph) (M.getD r.1 (0, 0, 1, 0))
noncomputable def okSw (E : List (Bool × ℕ × ℕ)) (Q : List (ℕ × ℕ)) (Z K : ℕ) (fb0 : ℕ × ℕ) (ts : List ℕ) : Bool := !chkT topC E Q fb0 Z K ts FF 1
def covSq (M : List Sq) (L : ℕ) (tt : List (List ℕ)) (R : List (ℕ × List ℕ)) : Bool :=
  (List.range L).all (fun t => tt.any (fun ts => ts.any (Nat.beq t)) || (List.range M.length).all (fun j => R.any (fun r => Nat.beq r.1 j && r.2.any (Nat.beq t))))
def sqOk (Z : ℕ) (E F : List (Bool × ℕ × ℕ)) (fb0 : ℕ × ℕ) (M : List Sq) (L : ℕ) (tt : List (List ℕ)) (R : List (ℕ × List ℕ)) : Bool :=
  fbOkH Z E F [] fb0 && (seqOk Z E F [] M && (((List.range MM).all (fun r => M.any (fun p => hb p.1 r)) && M.any (fun p => Nat.beq p.2.1 1)) && covSq M L tt R))
def okTyS (gs : List (Bool × ℕ × ℕ)) (raw : List (ℕ × ℕ)) (K i : ℕ) (e : Bool × ℕ × ℕ) (own cs : List ℕ) (fb : ℕ × ℕ) (tt : List (List ℕ)) (M : List Sq) (R : List (ℕ × List ℕ)) : Bool :=
  Nat.blt e.2.1 10 && (Nat.blt e.2.2 10 && (Nat.ble K 15 && (pOk 0 (tabE e own (pick raw cs)) && sqOk 0 [e] (gs.take i) fb M (K + 1) tt R)))
abbrev Gt := Bool × ℕ × ℕ
def okTy (gs : List Gt) (raw : List (ℕ × ℕ)) (K i : ℕ) (e : Gt) (own cs : List ℕ) (fb : ℕ × ℕ) (tt : List (List ℕ)) : Bool :=
  Nat.blt e.2.1 10 && Nat.blt e.2.2 10 && Nat.ble K 15 && pOk 0 (tabE e own (pick raw cs)) && fbOk [e] (gs.take i) fb && (List.range (K + 1)).all (fun t => tt.any (fun ts => ts.any (Nat.beq t)))
noncomputable def okTs (raw : List (ℕ × ℕ)) (K : ℕ) (e : Gt) (own cs : List ℕ) (fb : ℕ × ℕ) (ts : List ℕ) : Bool := !chkT topC [e] (tabE e own (pick raw cs)) fb 0 K ts FF 1
noncomputable def okLs (Q : List (ℕ × ℕ)) (K : ℕ) (fb : ℕ × ℕ) (ts : List ℕ) : Bool := !chkT topC [] Q fb 0 K ts FF 1
def ac0 : List (ℕ × ℕ) := []
def g4_0 : List (ℕ × ℕ) := [(51, 7), (53, 7), (153, 7), (170, 7), (177, 6), (178, 6), (332, 7), (1220, 5), (2321, 5), (2376, 7), (2440, 5), (8354, 6), (65562, 7), (65571, 6), (65577, 6), (65585, 6), (65618, 5), (131085, 5)]
def ac1 : List (ℕ × ℕ) := g4_0 ++ (ac0)
def g3_0 : List (ℕ × ℕ) := [(21, 8), (22, 7), (25, 8), (28, 8), (35, 8), (37, 8), (38, 8), (41, 8), (44, 8), (49, 9), (50, 8), (56, 8), (69, 7), (70, 8), (74, 7), (76, 8), (81, 7), (84, 8), (88, 7), (98, 8), (100, 8), (104, 7), (138, 8), (140, 8), (145, 8), (146, 8), (148, 8), (152, 9), (162, 8), (164, 7), (196, 7), (200, 7), (265, 7), (273, 7), (276, 7), (280, 7), (292, 7), (296, 7), (324, 8), (392, 7), (2312, 8), (2368, 8), (4480, 7), (8321, 8), (8328, 8), (16387, 8), (16401, 8), (65546, 8), (65554, 8), (65560, 8), (65569, 7), (131077, 6)]
def ac2 : List (ℕ × ℕ) := g3_0 ++ (ac1)
def g2_0 : List (ℕ × ℕ) := [(5, 9), (6, 9), (9, 10), (10, 10), (12, 11), (17, 11), (20, 11), (24, 11)]
def g2_1 : List (ℕ × ℕ) := [(34, 11), (36, 11), (40, 11), (65, 8), (66, 9), (68, 11), (72, 10), (80, 9), (96, 9), (130, 9), (132, 9), (136, 11), (144, 10), (160, 9), (257, 8), (260, 9), (264, 10), (272, 8), (288, 8), (2056, 9), (2112, 9), (2304, 9), (8320, 9), (16385, 9), (16386, 9), (16400, 9), (65538, 9)]
def ac3 : List (ℕ × ℕ) := g2_0 ++ (g2_1 ++ (ac2))
def g1_0 : List (ℕ × ℕ) := [(1, 12), (2, 12), (4, 13), (8, 13), (16, 13)]
def g1_1 : List (ℕ × ℕ) := [(32, 13), (64, 12), (128, 12), (256, 11), (131072, 8)]
def ac4 : List (ℕ × ℕ) := g1_0 ++ (g1_1 ++ (ac3))
abbrev rawT := ac4
def gtypes : List Gt := [(false, 7, 8), (true, 7, 8), (false, 7, 9)]
def w0_3_0 : List ((ℕ × ℕ) × List ℕ) := [((21, 8), []), ((38, 8), []), ((49, 9), []), ((69, 7), []), ((70, 8), []), ((84, 8), []), ((98, 8), []), ((100, 8), [])]
def w0_2_0 : List ((ℕ × ℕ) × List ℕ) := [((17, 11), [21, 49, 273, 16401, 51, 153, 177, 2321]), ((34, 11), [38, 98, 170, 178, 8354]), ((68, 11), [69, 70, 84, 100, 196, 332, 1220]), ((16385, 9), []), ((16386, 9), [])]
def w0_1_0 : List ((ℕ × ℕ) × List ℕ) := [((1, 12), [17]), ((2, 12), [34]), ((64, 12), [68])]
def sl0 : List ℕ := [256, 17, 34, 68, 136, 160, 288, 2304, 8320, 16385, 16386, 69, 70, 84, 145, 146, 324]
def fb0 : ℕ × ℕ := (1, 0)
def w1_3_0 : List ((ℕ × ℕ) × List ℕ) := [((25, 8), []), ((28, 8), []), ((35, 8), []), ((49, 9), [53, 65585]), ((74, 7), []), ((76, 8), []), ((88, 7), [])]
def w1_2_0 : List ((ℕ × ℕ) × List ℕ) := [((5, 9), [37]), ((6, 9), [38]), ((9, 10), [25, 265]), ((10, 10), [65546]), ((24, 11), [25, 28, 152, 65562]), ((65, 8), []), ((66, 9), [74]), ((72, 10), [74, 88, 332]), ((80, 9), []), ((96, 9), [98]), ((2056, 9), [2312]), ((2112, 9), [2368]), ((16385, 9), []), ((16386, 9), [])]
def w1_1_0 : List ((ℕ × ℕ) × List ℕ) := [((1, 12), [5, 9, 65, 257, 35, 49, 8321, 16387, 131077, 65571]), ((2, 12), [6, 10, 34, 66, 35, 65554]), ((8, 13), [9, 10, 12, 24, 40, 72, 136, 264, 74, 76, 392, 2376, 2440, 65562, 65577, 131085]), ((64, 12), [65, 66, 68, 72, 80, 96, 2368, 65618])]
def sl1 : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 131072, 5, 6, 20, 34, 36, 65, 66, 68, 80, 96, 130, 132, 144, 160, 257, 260, 272, 288, 16385, 16386, 35, 49, 2368, 4480, 8321, 65546, 65554, 65569]
def fb1 : ℕ × ℕ := (26, 4194304)
def mt1 : List Sq := [(0x3d1c7f8ffffefe3bfe7c1fc7fdf7fefff7beffdffe3b1f7fffff7d, 0, 26, 0x400000), (0x24000100000000401028000000000000801000000000000000002, 0, 113, 0x8040420000080000), (0xa38060000101c000816038020801000040002001c4e080000080, 1, 250, 0xc004000002080000a1000004006360400004100021200082400000080201)]
def rt1_0 : List (ℕ × List ℕ) := [(0, [0])]
def rt1_1 : List (ℕ × List ℕ) := [(0, [1])]
def rt1_2 : List (ℕ × List ℕ) := [(1, [0])]
def rt1_3 : List (ℕ × List ℕ) := [(1, [1]), (2, [0])]
def rt1_4 : List (ℕ × List ℕ) := [(2, [1])]
def w2_3_0 : List ((ℕ × ℕ) × List ℕ) := [((21, 8), []), ((25, 8), []), ((35, 8), []), ((49, 9), []), ((69, 7), []), ((70, 8), []), ((76, 8), []), ((84, 8), []), ((98, 8), []), ((100, 8), []), ((324, 8), [])]
def w2_2_0 : List ((ℕ × ℕ) × List ℕ) := [((10, 10), [138]), ((17, 11), [21, 49, 153, 65585]), ((34, 11), [35, 38, 98, 170, 178, 8354]), ((68, 11), [69, 70, 76, 84, 100, 196, 324]), ((264, 10), [392]), ((2056, 9), []), ((2304, 9), []), ((16400, 9), [])]
def w2_1_0 : List ((ℕ × ℕ) × List ℕ) := [((1, 12), [17]), ((8, 13), [9, 10, 12, 24, 40, 72, 136, 264, 2056, 8328]), ((64, 12), [68]), ((256, 11), [264])]
def sl2 : List ℕ := [8, 128, 256, 17, 34, 36, 68, 2304, 16400, 21, 35, 49, 69, 70, 84, 98, 148, 152, 162, 324, 8321, 65554, 65560, 65569]
def fb2 : ℕ × ℕ := (52, 316659348799488)
def mt2 : List Sq := [(0x3d1c7f8feffdfffbfefc1fc7ffffffefe3beffdffe3f1f7fefff7d, 0, 52, 0x1200000000000), (0x4000500000000401020000000000000001000000800000100002, 0, 187, 0x8000000000000010000000a000000000010048000100), (0x2a38020100200000001e038000000101c4000200140e080000080, 1, 452, 0x200000000400000000008004008000828202000000108000401000100008804100820000400842004010000000000000020)]
def rt2_0 : List (ℕ × List ℕ) := [(0, [1])]
def rt2_1 : List (ℕ × List ℕ) := [(1, [1])]
def rt2_2 : List (ℕ × List ℕ) := [(2, [1])]
end hz17
section hz18
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {R : ℕ → ℕ}
variable (m : ℕ)
def gv (w : List ℕ) (g : Gate) : ℕ := match g.op, g.inputs with
  | .and, [] => m
  | .and, [i] => w.getD i 0
  | .and, i :: j :: _ => w.getD i 0 &&& w.getD j 0
  | .or, [] => 0
  | .or, [i] => w.getD i 0
  | .or, i :: j :: _ => w.getD i 0 ||| w.getD j 0
  | .not, [] => m
  | .not, i :: _ => w.getD i 0 ^^^ m
  | _, _ => 0
def ex (gs : List Gate) (w : List ℕ) : List ℕ := gs.foldl (fun w g => w ++ [gv m w g]) w
end hz18
section hz19
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {R : ℕ → ℕ}
def f (x : Fin 9 → Bool) : Bool := (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)
def EF : ℕ := ((((((((((((rawP.getD 0 0 &&& rawP.getD 4 0) ||| (rawP.getD 0 0 &&& rawP.getD 5 0)) ||| (rawP.getD 1 0 &&& rawP.getD 5 0)) ||| (rawP.getD 1 0 &&& rawP.getD 6 0)) ||| (rawP.getD 2 0 &&& rawP.getD 6 0)) ||| (rawP.getD 1 0 &&& rawP.getD 7 0)) ||| (rawP.getD 3 0 &&& rawP.getD 7 0)) ||| (rawP.getD 4 0 &&& rawP.getD 7 0)) ||| (rawP.getD 0 0 &&& rawP.getD 8 0)) ||| (rawP.getD 2 0 &&& rawP.getD 8 0)) ||| (rawP.getD 3 0 &&& rawP.getD 8 0)) ||| (rawP.getD 6 0 &&& rawP.getD 8 0))
end hz19
section hz20
variable {R : ℕ → ℕ}
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segX_ok : segsX.all segOk = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segY_ok : segsY.all segOk = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HX_eq : HX = bitsOf segsX := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HY_eq : HY = bitsOf segsY := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_lt1 : AA < 2 ^ NN := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segXR_ok : segsX.all segOkR = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segYR_ok : segsY.all segOkR = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma lanes_ok : (List.range 84).all laneOk = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HXY_lt : HX < 2 ^ NN ∧ HY < 2 ^ NN ∧ 100 < NN := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma GMD_eq : GMD = 2 ^ (NN - 1) - 1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma PLN_eq : PLN = 2 ^ (NN * 12) := by decide +kernel
lemma geo13 : geo 13 7 = 302268352895954163081217 := by decide +kernel
lemma geo12 : geo 12 7 = 4723519685917965029377 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_TG : AA &&& TG = AA := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_lt : TG < 2 ^ NN := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_lt : AA < 2 ^ NN := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raw_good : rawP.all (fun w => segsX.all (segGood w 0) && segsY.all (segGood w NN)) = true := by decide +kernel
lemma ffull : mFull [(FF, 1)] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k4_0 : g4_0.all (fun x => okR topC [] (pr ac0 x.1) x) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k3_0 : g3_0.all (fun x => okR topC [] (pr ac1 x.1) x) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k2_0 : g2_0.all (fun x => okR topC [] (pr ac2 x.1) x) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k2_1 : g2_1.all (fun x => okR topC [] (pr ac2 x.1) x) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k1_0 : g1_0.all (fun x => okR topC [] (pr ac3 x.1) x) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem k1_1 : g1_1.all (fun x => okR topC [] (pr ac3 x.1) x) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem base_k : okR topC [] (pick rawT [1, 2, 4, 8, 16, 32, 64, 128, 256, 2112, 65538, 35, 69, 70, 145, 146, 273, 324]) (0, 15) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w0_3_0_r : w0_3_0.all (okO topC (false, 7, 8) ([] : List ℕ) rawT) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w0_2_0_r : w0_2_0.all (okO topC (false, 7, 8) (w0_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)) rawT) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w0_1_0_r : w0_1_0.all (okO topC (false, 7, 8) (w0_2_0.map (fun r => r.1.1) ++ (w0_3_0.map (fun r => r.1.1) ++ ([] : List ℕ))) rawT) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w1_3_0_r : w1_3_0.all (okO topC (true, 7, 8) ([] : List ℕ) rawT) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w1_2_0_r : w1_2_0.all (okO topC (true, 7, 8) (w1_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)) rawT) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w1_1_0_r : w1_1_0.all (okO topC (true, 7, 8) (w1_2_0.map (fun r => r.1.1) ++ (w1_3_0.map (fun r => r.1.1) ++ ([] : List ℕ))) rawT) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w2_3_0_r : w2_3_0.all (okO topC (false, 7, 9) ([] : List ℕ) rawT) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w2_2_0_r : w2_2_0.all (okO topC (false, 7, 9) (w2_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)) rawT) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem w2_1_0_r : w2_1_0.all (okO topC (false, 7, 9) (w2_2_0.map (fun r => r.1.1) ++ (w2_3_0.map (fun r => r.1.1) ++ ([] : List ℕ))) rawT) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem qqk0 : (okTy gtypes rawT 14 0 (false, 7, 8) (w0_1_0.map (fun r => r.1.1) ++ (w0_2_0.map (fun r => r.1.1) ++ (w0_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)))) sl0 fb0 ([[0], [1], [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]] : List (List ℕ)) = true) ∧
 (okTs rawT 14 (false, 7, 8) (w0_1_0.map (fun r => r.1.1) ++ (w0_2_0.map (fun r => r.1.1) ++ (w0_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)))) sl0 fb0 [0] = true) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem qqk1 : okTs rawT 14 (false, 7, 8) (w0_1_0.map (fun r => r.1.1) ++ (w0_2_0.map (fun r => r.1.1) ++ (w0_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)))) sl0 fb0 [1] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem qqk2 : (okTs rawT 14 (false, 7, 8) (w0_1_0.map (fun r => r.1.1) ++ (w0_2_0.map (fun r => r.1.1) ++ (w0_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)))) sl0 fb0 [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] = true) ∧
 (okTyS gtypes rawT 14 1 (true, 7, 8) (w1_1_0.map (fun r => r.1.1) ++ (w1_2_0.map (fun r => r.1.1) ++ (w1_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)))) sl1 fb1 ([[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]] : List (List ℕ)) mt1 (rt1_0 ++ (rt1_1 ++ (rt1_2 ++ (rt1_3 ++ (rt1_4))))) = true) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem qqk3 : rt1_0.all (okSq [(true, 7, 8)] (tabE (true, 7, 8) (w1_1_0.map (fun r => r.1.1) ++ (w1_2_0.map (fun r => r.1.1) ++ (w1_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)))) (pick rawT sl1)) 0 14 mt1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem qqk4 : rt1_1.all (okSq [(true, 7, 8)] (tabE (true, 7, 8) (w1_1_0.map (fun r => r.1.1) ++ (w1_2_0.map (fun r => r.1.1) ++ (w1_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)))) (pick rawT sl1)) 0 14 mt1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem qqk5 : rt1_2.all (okSq [(true, 7, 8)] (tabE (true, 7, 8) (w1_1_0.map (fun r => r.1.1) ++ (w1_2_0.map (fun r => r.1.1) ++ (w1_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)))) (pick rawT sl1)) 0 14 mt1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem qqk6 : rt1_3.all (okSq [(true, 7, 8)] (tabE (true, 7, 8) (w1_1_0.map (fun r => r.1.1) ++ (w1_2_0.map (fun r => r.1.1) ++ (w1_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)))) (pick rawT sl1)) 0 14 mt1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem qqk7 : rt1_4.all (okSq [(true, 7, 8)] (tabE (true, 7, 8) (w1_1_0.map (fun r => r.1.1) ++ (w1_2_0.map (fun r => r.1.1) ++ (w1_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)))) (pick rawT sl1)) 0 14 mt1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem qqk8 : okSw [(true, 7, 8)] (tabE (true, 7, 8) (w1_1_0.map (fun r => r.1.1) ++ (w1_2_0.map (fun r => r.1.1) ++ (w1_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)))) (pick rawT sl1)) 0 14 fb1 [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem qqk9 : (okTyS gtypes rawT 14 2 (false, 7, 9) (w2_1_0.map (fun r => r.1.1) ++ (w2_2_0.map (fun r => r.1.1) ++ (w2_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)))) sl2 fb2 ([[0], [2, 3, 4, 5, 6], [7, 8, 9, 10, 11, 12, 13, 14]] : List (List ℕ)) mt2 (rt2_0 ++ (rt2_1 ++ (rt2_2))) = true) ∧
 (rt2_0.all (okSq [(false, 7, 9)] (tabE (false, 7, 9) (w2_1_0.map (fun r => r.1.1) ++ (w2_2_0.map (fun r => r.1.1) ++ (w2_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)))) (pick rawT sl2)) 0 14 mt2) = true) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem qqk10 : rt2_1.all (okSq [(false, 7, 9)] (tabE (false, 7, 9) (w2_1_0.map (fun r => r.1.1) ++ (w2_2_0.map (fun r => r.1.1) ++ (w2_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)))) (pick rawT sl2)) 0 14 mt2) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem qqk11 : (rt2_2.all (okSq [(false, 7, 9)] (tabE (false, 7, 9) (w2_1_0.map (fun r => r.1.1) ++ (w2_2_0.map (fun r => r.1.1) ++ (w2_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)))) (pick rawT sl2)) 0 14 mt2) = true) ∧
 (okSw [(false, 7, 9)] (tabE (false, 7, 9) (w2_1_0.map (fun r => r.1.1) ++ (w2_2_0.map (fun r => r.1.1) ++ (w2_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)))) (pick rawT sl2)) 0 14 fb2 [0] = true) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem qqk12 : okSw [(false, 7, 9)] (tabE (false, 7, 9) (w2_1_0.map (fun r => r.1.1) ++ (w2_2_0.map (fun r => r.1.1) ++ (w2_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)))) (pick rawT sl2)) 0 14 fb2 [2, 3, 4, 5, 6] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem qqk13 : okSw [(false, 7, 9)] (tabE (false, 7, 9) (w2_1_0.map (fun r => r.1.1) ++ (w2_2_0.map (fun r => r.1.1) ++ (w2_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)))) (pick rawT sl2)) 0 14 fb2 [7, 8, 9, 10, 11, 12, 13, 14] = true := by decide +kernel
end hz20
section hz21
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {R : ℕ → ℕ}
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma memA : ∀ j : Fin 9, (7 : Fin 9) < j → (false, 7, j.val) ∈ gtypes := by decide +kernel
lemma memO : ∀ j : Fin 9, (7 : Fin 9) < j → (true, 7, j.val) ∈ gtypes := by decide +kernel
lemma memN : (false, 7, 9) ∈ gtypes := by decide +kernel
end hz21
variable {R : ℕ → ℕ}
lemma op_comm (d : Bool) (a b : ℕ) : op d a b = op d b a := by
  cases d <;> simp [op, Nat.and_comm, Nat.or_comm]
lemma op_bit (d : Bool) (a b i : ℕ) : (op d a b).testBit i =
    bif d then a.testBit i || b.testBit i else a.testBit i && b.testBit i := by
  cases d <;> simp [op]
lemma op_self (d : Bool) (a : ℕ) : op d a a = a := by cases d <;> simp [op]
lemma Al.symm {d : Bool} {a b : ℕ} (h : Al R d a b) : Al R d b a := by unfold Al at *; rwa [Nat.and_comm]
lemma al0 (d : Bool) (a b : ℕ) : Al Z0 d a b := by simp [Al, Z0]
lemma Sol.mono {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∀ {q' : ℕ} {S' : Set ℕ}, q ≤ q' → S ⊆ S' → Sol R m T q' S' := by
  induction h with
  | done h => intro q' S' _ hs; exact .done (hs h)
  | un h _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .un (hs h) (ih (by omega) (Set.insert_subset_insert hs))
  | bi h1 h2 ha _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .bi (hs h1) (hs h2) ha (ih (by omega) (Set.insert_subset_insert hs))
lemma Sol.rel {R' : ℕ → ℕ} {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Sol R' m T q S := by
  induction h with
  | done h => exact .done h
  | un h _ ih => exact .un h ih
  | bi h1 h2 ha _ ih => exact .bi h1 h2 (hR _ _ _ ha) ih
lemma Sol.to0 {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) : Sol Z0 m T q S := h.rel fun d a b _ => al0 d a b
lemma Live.sol {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : Sol Z0 m T k (S : Set ℕ) := by
  induction h with
  | stop => exact .done (by simp)
  | @un k t a U _ ih =>
    refine .un (a := a) (by simp) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; grind
  | @bi k t d a b U _ _ _ ih =>
    refine .bi (d := d) (a := a) (b := b) (by simp) (by simp) (al0 _ _ _) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; grind
lemma Sol.live {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∃ k ≤ q, ∃ t, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live R m T k t S0 := by
  induction h with
  | @done q S h => exact ⟨0, by omega, 0, {T}, by simpa using h, .stop⟩
  | @un q S a ha _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : a ^^^ m ∈ S1
    · refine ⟨k + 1, by omega, t + 1, insert a (S1.erase (a ^^^ m)), ?_, .un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1, h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
  | @bi q S d a b ha hb hal _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : op d a b ∈ S1
    · by_cases hab : a = b
      · subst hab; rw [op_self] at hs
        exact ⟨k, by omega, t, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
      refine ⟨k + 1, by omega, t, insert a (insert b (S1.erase (op d a b))), ?_, .bi hab hal (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1, h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
lemma C_mono {m : ℕ} {S S' : Set ℕ} (h : S ⊆ S') : C m S ⊆ C m S' := Set.union_subset_union_left _ h
lemma sub_C (m : ℕ) (S : Set ℕ) : S ⊆ C m S := Set.subset_union_left
lemma Un.live {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) (t + 1) S := by obtain ⟨U, rfl, rfl⟩ := h; exact .un hl
lemma Bi.live {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) t S := by obtain ⟨hab, U, rfl, rfl, hal⟩ := h; exact .bi hab hal hl
lemma Bi.symm {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') : Bi R d b a S S' := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  exact ⟨hab.symm, U, Finset.insert_comm _ _ _, by rw [op_comm], hal.symm⟩
lemma Un.sub {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') : a ∈ S ∧ S' ⊆ insert (a ^^^ m) S := by
  obtain ⟨U, rfl, rfl⟩ := h
  exact ⟨by simp, Finset.insert_subset_insert _ (Finset.subset_insert _ _)⟩
lemma Bi.sub {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') :
    a ∈ S ∧ b ∈ S ∧ S' ⊆ insert (op d a b) S := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  refine ⟨by simp, by simp, Finset.insert_subset_insert _ ?_⟩
  intro x hx; simp [hx]
lemma Un.sol {m T a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (a := a) (sub_C _ _ (by simpa using ha)) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Bi.sol {m T a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (a := a) (b := b) (sub_C _ _ (by simpa using ha)) (sub_C _ _ (by simpa using hb)) (al0 _ _ _) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Un.min {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Bi.min {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Un.fresh {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : a ^^^ m ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Bi.fresh {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : op d a b ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Min.size {m T : ℕ} : ∀ {k t : ℕ} {S : Finset ℕ}, Min R m T k t S → S.card + t ≤ k + 1 ∧ t ≤ k := by
  intro k t S ⟨hl, hm⟩
  induction hl with
  | stop => simp
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have ih := ih (hu.min hl hm).2
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have ih := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
lemma phi_un {m a n c : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (h1 : c ≠ n) (h2 : c ^^^ m ≠ n) :
    Un m c (phi a n X) (phi a n X') := by
  obtain ⟨U, rfl, rfl⟩ := h
  refine ⟨insert a (U.erase n), ?_, ?_⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_bi {a n b c : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (h1 : b ≠ n) (h2 : c ≠ n)
    (h3 : op d b c ≠ n) : Bi R d b c (phi a n X) (phi a n X') := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  refine ⟨hab, insert a (U.erase n), ?_, ?_, hal⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_back {m a : ℕ} {X : Finset ℕ} (h : a ^^^ m ∈ X) : Un m a (phi a (a ^^^ m) X) X :=
  ⟨X.erase (a ^^^ m), rfl, by rw [Finset.insert_erase h]⟩
lemma phi_start {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hn : a ^^^ m ∉ S) : phi a (a ^^^ m) S' = S := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn
  simp [phi, hn.2]
lemma un_keep {m c n : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (hn : n ∈ X) (h1 : c ≠ n) : n ∈ X' := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn ⊢; exact Or.inr (hn.resolve_left (Ne.symm h1))
lemma bi_keep {b c n : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (hn : n ∈ X) (h1 : b ≠ n)
    (h2 : c ≠ n) : n ∈ X' := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  simp at hn ⊢; rcases hn with h | h | h
  · exact absurd h.symm h1
  · exact absurd h.symm h2
  · exact Or.inr h
lemma first_move {m T : ℕ} : ∀ (k t : ℕ) (S : Finset ℕ), Min R m T k t S → 2 ≤ S.card →
    (∃ k0 d a b S1, k = k0 + 1 ∧ Bi R d a b S S1 ∧ Live R m T k0 t S1) ∨
    (∃ k0 t0 a d c S1 S2, k = k0 + 2 ∧ t = t0 + 1 ∧ Un m a S S1 ∧ Bi R d (a ^^^ m) c S1 S2 ∧ Live R m T k0 t0 S2) ∨
    (∃ k0 t0 a a' d S1 S2 S3, k = k0 + 3 ∧ t = t0 + 2 ∧ Un m a S S1 ∧ a' ≠ a ^^^ m ∧ Un m a' S1 S2 ∧
      Bi R d (a ^^^ m) (a' ^^^ m) S2 S3 ∧ Live R m T k0 t0 S3) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro t S hS hc
  obtain ⟨hl, hm⟩ := hS
  cases hl with
  | stop => simp at hc
  | @bi k t d a b U hab hal hl => exact Or.inl ⟨k, d, a, b, _, rfl, ⟨hab, U, rfl, rfl, hal⟩, hl⟩
  | @un k t a U hl =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf := hu.fresh hl hm
    have hn : a ^^^ m ∉ insert a U := fun h => hf (sub_C _ _ (by simpa using h))
    have hmin := hu.min hl hm
    have hxx : ∀ c : ℕ, c ^^^ m ^^^ m = c := fun c => by simp
    have hc' : 2 ≤ (insert (a ^^^ m) U).card := by
      have h1 := Finset.card_insert_le a U
      rw [Finset.card_insert_of_notMem (fun h => hn (by simp [h]))]; omega
    generalize hS1 : insert (a ^^^ m) U = S1 at *
    have hnS1 : a ^^^ m ∈ S1 := by rw [← hS1]; simp
    have hst := phi_start hu hn
    have dbl : ∀ {c k2 t2 S2}, Un m c S1 S2 → Live R m T k2 t2 S2 → k = k2 + 1 → c ≠ a ^^^ m ∧ c ^^^ m ≠ a ^^^ m := by
      intro c k2 t2 S2 h2 hl2 hk
      constructor
      · rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        apply hm (k2 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (hl2.sol.mono le_rfl fun x hx => ?_)
        have h3 := hsub hx
        have h4 : x ∈ insert a (insert (a ^^^ m) U) := by rw [hS1]; exact h3
        simp at h4
        rcases h4 with rfl | rfl | h4
        · exact Or.inr (sub_C _ _ (by simp))
        · exact Or.inl rfl
        · exact Or.inr (sub_C _ _ (by simp [h4]))
      · intro e
        exact h2.fresh hl2 (by rw [← hk]; exact hmin.2) (sub_C _ _ (by rw [e]; simpa using hnS1))
    rcases ih k (by omega) t S1 hmin hc' with
      ⟨k0, d, x, y, S2, rfl, hb, hl2⟩ | ⟨k0, t0, c, d, y, S2, S3, rfl, rfl, h1, hb, hl2⟩ |
      ⟨k0, t0, c, c', d, S2, S3, S4, rfl, rfl, h1, hne, h2, hb, hl2⟩
    · by_cases hx : x = a ^^^ m
      · subst hx; exact Or.inr (Or.inl ⟨k0, t, a, d, y, S1, S2, rfl, rfl, hu, hb, hl2⟩)
      by_cases hy : y = a ^^^ m
      · subst hy; exact Or.inr (Or.inl ⟨k0, t, a, d, x, S1, S2, rfl, rfl, hu, hb.symm, hl2⟩)
      have hg : op d x y ≠ a ^^^ m := fun e => hb.fresh hl2 hmin.2 (sub_C _ _ (by rw [e]; simpa using hnS1))
      refine Or.inl ⟨k0 + 1, d, x, y, phi a (a ^^^ m) S2, rfl, ?_, ?_⟩
      · rw [← hst]; exact phi_bi hb hx hy hg
      · exact (phi_back (bi_keep hb hnS1 hx hy)).live hl2
    · have hb1 := hb.live hl2
      obtain ⟨n1, n2⟩ := dbl h1 hb1 rfl
      have hm2 := h1.min hb1 hmin.2
      by_cases hy : y = a ^^^ m
      · subst hy
        exact Or.inr (Or.inr ⟨k0, t0, a, c, d, S1, S2, S3, rfl, rfl, hu, n1, h1, hb.symm, hl2⟩)
      have hk2 := un_keep h1 hnS1 n1
      have hg : op d (c ^^^ m) y ≠ a ^^^ m := fun e => hb.fresh hl2 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      refine Or.inr (Or.inl ⟨k0 + 1, t0 + 1, c, d, y, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, rfl, rfl, ?_, phi_bi hb n2 hy hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk2 n2 hy)).live hl2
    · have hb1 := hb.live hl2
      have hb2 := h2.live hb1
      obtain ⟨n1, n2⟩ := dbl h1 hb2 rfl
      have hm2 := h1.min hb2 hmin.2
      have hk2 := un_keep h1 hnS1 n1
      have hm3 := h2.min hb1 hm2.2
      have n3 : c' ≠ a ^^^ m := by
        rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        obtain ⟨hcS, hsub1⟩ := h1.sub
        have hcS' : c ∈ insert a U := by
          have : c ∈ insert (a ^^^ m) U := by rw [hS1]; exact hcS
          simp at this ⊢; exact Or.inr (this.resolve_left n1)
        apply hm (k0 + 1 + 1 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (.un (a := c) (Or.inr (sub_C _ _ (by simpa using hcS'))) (hb1.sol.mono le_rfl fun x hx => ?_))
        have h3 : x = a ∨ x = c ^^^ m ∨ x ∈ S1 := by
          have := hsub hx; simp at this
          rcases this with h | h
          · exact Or.inl h
          · have := hsub1 h; simp at this; exact Or.inr this
        rcases h3 with rfl | rfl | h3
        · exact Or.inr (Or.inr (sub_C _ _ (by simp)))
        · exact Or.inl rfl
        · rw [← hS1] at h3; simp at h3
          rcases h3 with rfl | h3
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (sub_C _ _ (by simp [h3])))
      have n4 : c' ^^^ m ≠ a ^^^ m := fun e => h2.fresh hb1 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      have hk3 := un_keep h2 hk2 n3
      have hg : op d (c ^^^ m) (c' ^^^ m) ≠ a ^^^ m := fun e => hb.fresh hl2 hm3.2 (sub_C _ _ (by rw [e]; simpa using hk3))
      refine Or.inr (Or.inr ⟨k0 + 1, t0 + 1, c, c', d, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, phi a (a ^^^ m) S4, rfl, rfl, ?_, hne,
        phi_un h2 n3 n4, phi_bi hb n2 n4 hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk3 n2 n4)).live hl2
lemma and_op (d : Bool) (a b n : ℕ) : op d a b &&& n = op d (a &&& n) (b &&& n) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases d <;> simp [op_bit] <;> grind
lemma and_neg {m n : ℕ} (hn : n &&& m = n) (a : ℕ) : (a ^^^ m) &&& n = (a &&& n) ^^^ n := by
  apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (fun x => x.testBit i) hn
  simp at this ⊢
  grind
lemma Im_mem {n x : ℕ} {S : Finset ℕ} (h : x ∈ S) : x &&& n ∈ C n (Im n S) := Or.inl ⟨x, by simpa using h, rfl⟩
lemma Cst_mem {n x : ℕ} {S : Set ℕ} (h : Cst n x) : x &&& n ∈ C n S := by
  rcases h with h | h <;> simp [C, h]
lemma Cst_neg {m n a : ℕ} (hn : n &&& m = n) : Cst n (a ^^^ m) ↔ Cst n a := by
  unfold Cst; rw [and_neg hn]
  constructor
  · rintro (h | h)
    · right; have := congrArg (· ^^^ n) h; simpa using this
    · left; have := congrArg (· ^^^ n) h; simpa using this
  · rintro (h | h) <;> simp [h]
lemma op_cst {n a b : ℕ} (d : Bool) (ha : Cst n a) :
    op d a b &&& n = 0 ∨ op d a b &&& n = n ∨ op d a b &&& n = b &&& n := by
  rw [and_op]
  rcases ha with h | h <;> rw [h] <;> cases d
  · left; simp [op]
  · right; right; simp [op]
  · right; right; apply Nat.eq_of_testBit_eq; intro i; simp [op]
  · right; left; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_cst2 {n a b : ℕ} (d : Bool) (ha : Cst n a) (hb : Cst n b) : Cst n (op d a b) := by
  rcases op_cst (b := b) d ha with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · unfold Cst at hb ⊢; rw [h]; exact hb
lemma op_cst_mem {n a b : ℕ} {S : Finset ℕ} (d : Bool) (h : Cst n a ∨ Cst n b) (ha : a ∈ S) (hb : b ∈ S) :
    op d a b &&& n ∈ C n (Im n S) := by
  rcases h with h | h
  · rcases op_cst (b := b) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem hb
  · rw [op_comm]
    rcases op_cst (b := a) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem ha
lemma C_Im_sub {n g : ℕ} {S S' : Finset ℕ} {Q : Set ℕ} (h : S' ⊆ insert g S) (hg : g &&& n ∈ Q)
    (hQ : C n (Im n S) ⊆ Q) : C n (Im n S') ⊆ Q := by
  rintro x (⟨y, hy, rfl⟩ | hx)
  · have := h hy; simp at this
    rcases this with rfl | h'
    · exact hg
    · exact hQ (Im_mem h')
  · exact hQ (Or.inr hx)
section proj
variable {m T n : ℕ} (hn : n &&& m = n)
include hn
lemma Un.im {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (Im_mem ha) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_neg hn]; exact Or.inl rfl
omit hn in
lemma Bi.im {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (Im_mem ha) (Im_mem hb) (al0 _ _ _) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
lemma Un.kill {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hc : Cst n a) (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2 (Cst_mem ((Cst_neg hn).2 hc)) subset_rfl)
omit hn in
lemma Bi.kill {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hc : Cst n a ∨ Cst n b)
    (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) : Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)
lemma Min.const (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n) {k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) :
    ∃ q, q + (S.filter (Cst n)).card ≤ k ∧ Sol Z0 n (T &&& n) q (C n (Im n S)) := by
  obtain ⟨hl, hm⟩ := h
  induction hl with
  | stop =>
    refine ⟨0, ?_, .done (Im_mem (by simp))⟩
    rw [Finset.filter_eq_empty_iff.2]; · simp
    intro x hx; simp at hx; subst hx
    rintro (h | h); exacts [hT0 h, hT1 h]
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have h1 : (U.filter (Cst n)).card ≤ ((insert (a ^^^ m) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    by_cases hc : Cst n a
    · refine ⟨q, ?_, hu.kill hn hc hs⟩
      rw [Finset.filter_insert, ite_eq_left hc]
      have := Finset.card_insert_le a (U.filter (Cst n)); omega
    · refine ⟨q + 1, ?_, hu.im hn hs⟩
      rw [Finset.filter_insert, ite_eq_right hc]; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (op d a b) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have ca := Finset.card_insert_le a (U.filter (Cst n))
    have cb := Finset.card_insert_le b (U.filter (Cst n))
    by_cases hca : Cst n a
    · refine ⟨q, ?_, hu.kill (Or.inl hca) hs⟩
      rw [Finset.filter_insert, ite_eq_left hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert, ite_eq_left (op_cst2 d hca hcb), Finset.card_insert_of_notMem (by simp [hf])] at hq
        have := Finset.card_insert_le a (insert b (U.filter (Cst n))); omega
      · rw [ite_eq_right hcb]; omega
    · rw [Finset.filter_insert, ite_eq_right hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · refine ⟨q, ?_, hu.kill (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]; omega
      · refine ⟨q + 1, ?_, hu.im hs⟩
        rw [ite_eq_right hcb]; omega
end proj
lemma Min.proper {m T k t : ℕ} (hT : T &&& m = T) (hT0 : T ≠ 0) (hT1 : T ≠ m) {S : Finset ℕ} (hS : ∀ x ∈ S, x &&& m = x)
    (h : Min R m T k t S) : 0 ∉ S ∧ m ∉ S := by
  obtain ⟨q, hq, hs⟩ := h.const (n := m) (by simp) (by rwa [hT]) (by rwa [hT])
  have hi : Im m S = (S : Set ℕ) := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; have := hS y hy; simp only; rw [this]; exact hy
    · intro hx; exact ⟨x, hx, hS x hx⟩
  rw [hi, hT] at hs
  have key : ∀ x ∈ S, ¬ Cst m x := by
    intro x hx hc
    have : 0 < (S.filter (Cst m)).card := Finset.card_pos.2 ⟨x, by simp [hx, hc]⟩
    exact h.2 q (by omega) hs
  exact ⟨fun h0 => key 0 h0 (Or.inl (by simp)), fun h1 => key m h1 (Or.inr (by simp))⟩
section cov
variable {N m T i : ℕ} (m1 : m.testBit i = true) (m2 : m.testBit (N + i) = true)
  (t1 : T.testBit i = true) (t2 : T.testBit (N + i) = false)
include t1 t2 m1 m2
lemma Live.cov {k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : ∃ w ∈ S, sepb N (pos' t) w i = true := by
  induction h with
  | stop => exact ⟨T, by simp, by simp [sepb, pos', t1, t2]⟩
  | @un k t a U _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    have weak : sepb N true w i = true := by
      revert hs; cases pos' t <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨a, by simp, ?_⟩
      revert weak; simp [sepb, pos', m1, m2]
    · exact ⟨w, by simp [hw], by simpa [pos'] using weak⟩
  | @bi k t d a b U _ _ _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    simp at hw
    rcases hw with rfl | hw
    · by_cases ha : sepb N (pos' t) a i = true
      · exact ⟨a, by simp, ha⟩
      · refine ⟨b, by simp, ?_⟩
        revert hs ha
        unfold sepb; simp only [op_bit]
        cases pos' t <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact ⟨w, by simp [hw], hs⟩
end cov
lemma sepb_weak {N w i : ℕ} (e : Bool) (h : sepb N e w i = true) : sepb N true w i = true := by
  revert h; cases e <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
section rect
variable {N m T : ℕ}
lemma bi_uq {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (hi : Lg N m T i)
    (hc : c ∈ insert a (insert b U)) (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl
      rcases hcc with rfl | rfl; exacts [ha hx, hb hx]
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma un_uq {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (ha : a ∉ U)
    (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
  by_cases hcc : c = a
  · rw [ite_eq_left hcc]; subst hcc
    refine ⟨by rw [hn]; exact h.1, fun x hx hne => ?_⟩
    simp at hx
    exact h.2 x (by simp [hx.resolve_left hne]) (fun e => ha (e ▸ hx.resolve_left hne))
  · rw [ite_eq_right hcc]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hcc)
    · exact h.2 x (by simp [hx]) hne
lemma phi_mem {x y g c : ℕ} {U : Finset ℕ} (hc : c ∈ insert x (insert y U)) :
    (if c = x ∨ c = y then g else c) ∈ insert g U := by
  split_ifs with h
  · simp
  · simp only [Finset.mem_insert] at hc ⊢; grind
lemma phi_ne {x y g a b : ℕ} {U : Finset ℕ} (hg : g ∉ U) (ha : a ∈ insert x (insert y U)) (hb : b ∈ insert x (insert y U))
    (hab : a ≠ b) (h : ¬ ((a = x ∨ a = y) ∧ (b = x ∨ b = y))) :
    (if a = x ∨ a = y then g else a) ≠ (if b = x ∨ b = y then g else b) := by
  simp only [Finset.mem_insert] at ha hb
  split_ifs with p q q
  · exact absurd ⟨p, q⟩ h
  · rintro rfl; grind
  · rintro rfl; grind
  · exact hab
lemma bi_tight {a b k t : ℕ} {d : Bool} {U : Finset ℕ} (hab : a ≠ b) (hal : Al R d a b) (hl : Live R m T k t (insert (op d a b) U))
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m ((insert a (insert b U) : Finset ℕ) : Set ℕ)))
    (hc : (insert a (insert b U)).card + t = k + 2) :
    a ∉ U ∧ b ∉ U ∧ op d a b ∉ U ∧ (insert (op d a b) U).card + t = k + 1 ∧ Min R m T k t (insert (op d a b) U) := by
  have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
  have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a (insert b U)
  have h2 := Finset.card_insert_le b U
  have ha : a ∉ insert b U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  have hb : b ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc h1; omega
  exact ⟨fun h => ha (by simp [h]), hb, hf, by omega, hmin⟩
lemma un_tight {a k t : ℕ} {U : Finset ℕ} (hl : Live R m T k t (insert (a ^^^ m) U))
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m ((insert a U : Finset ℕ) : Set ℕ)))
    (hc : (insert a U).card + (t + 1) = k + 2) :
    a ∉ U ∧ a ^^^ m ∉ U ∧ (insert (a ^^^ m) U).card + t = k + 1 ∧ Min R m T k t (insert (a ^^^ m) U) := by
  have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
  have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a U
  have ha : a ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  exact ⟨ha, hf, by omega, hmin⟩
lemma rect0 {k : ℕ} {S : Finset ℕ} (hl : Live R m T k 0 S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N false S a i1 → Uq N false S b i2 → Uq N false S a j1 → Uq N false S b j2 → False := by
  generalize ht : 0 = t at hl
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | un => omega
  | @bi k t d x y U hxy hal hl ih =>
    subst ht
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by simpa using hc)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N false (insert x (insert y U)) c i →
        Uq N false (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inr (by simp [pos'])) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4
      have e1 := r1 b hb; have e2 := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have s1 := v1.1; have s3 := v3.1; have s2 := u2.1; have s4 := u4.1
      revert e1 e2 n1 n3 s1 s3 s2 s4
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 (by simpa using hc') rfl ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
lemma polar {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i j : ℕ} (h1 : Lg N m T i) (h2 : Lg N m T j) :
    ∀ {a : ℕ}, a ∈ S → Uq N true S a i → Uq N true S a j → a.testBit i = a.testBit j := by
  induction hl with
  | stop => intro a ha _ _; simp at ha; subst ha; rw [h1.2.2.1, h2.2.2.1]
  | @un k t x U hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    have := ih hmin.2 hc' (a := if a = x then x ^^^ m else a) (by split_ifs with h <;> simp at ha ⊢; grind)
      (un_uq h1 hx ha u1) (un_uq h2 hx ha u2)
    split_ifs at this with h
    · subst h; simpa [h1.1, h2.1] using this
    · exact this
  | @bi k t d x y U hxy hal hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have v1 := bi_uq (Or.inl rfl) hl hx hy h1 ha u1
    have v2 := bi_uq (Or.inl rfl) hl hx hy h2 ha u2
    have := ih hmin.2 hc' (phi_mem ha) v1 v2
    split_ifs at this v1 v2 with h
    · obtain ⟨b, hb, hab, hop⟩ : ∃ b ∈ insert x (insert y U), b ≠ a ∧ op d x y = op d a b := by
        rcases h with rfl | rfl
        · exact ⟨y, by simp, Ne.symm hxy, rfl⟩
        · exact ⟨x, by simp, hxy, op_comm _ _ _⟩
      rw [hop] at this v1 v2
      have n1 := u1.2 b hb hab; have n2 := u2.2 b hb hab
      have s1 := v1.1; have s2 := v2.1; have p1 := u1.1; have p2 := u2.1
      revert this n1 n2 s1 s2 p1 p2
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · exact this
lemma rect1 {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N true S a i1 → Uq N true S b i2 → Uq N true S a j1 → Uq N true S b j2 → False := by
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t x U hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (un_uq h1 hx ha u1) (un_uq h2 hx hb u2) (un_uq h3 hx ha u3) (un_uq h4 hx hb u4)
    · split_ifs with h <;> simp at ha ⊢; grind
    · split_ifs with h <;> simp at hb ⊢; grind
    · split_ifs with p q q
      · exact absurd (p.trans q.symm) hab
      · intro e; simp at hb; rw [← e] at hb; rcases hb with h | h
        · exact q (by rw [← e, h])
        · exact hg h
      · intro e; simp at ha; rw [e] at ha; rcases ha with h | h
        · exact p (by rw [e, h])
        · exact hg h
      · exact hab
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r1 x (by simp), h1.1, h2.1]
      · exact r1 w (by simp [hw])
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r2 x (by simp), h3.2.1, h4.2.1]
      · exact r2 w (by simp [hw])
  | @bi k t d x y U hxy hal hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N true (insert x (insert y U)) c i →
        Uq N true (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inl rfl) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hpol := polar hl hmin.2 hc' h1 h3 (by simp) v1 v3
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4 hpol
      have e1 := r1 a ha; have e2 := r2 a ha; have e1b := r1 b hb; have e2b := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have n2 := u2.2 a ha hab; have n4 := u4.2 a ha hab
      have s1 := v1.1; have s3 := v3.1; have s2 := v2.1; have s4 := v4.1
      have p1 := u1.1; have p2 := u2.1; have p3 := u3.1; have p4 := u4.1
      revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 p1 p2 p3 p4 hpol
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
end rect
section chrom
variable {N m T : ℕ}
lemma Ht.symm {e : Bool} {S : Finset ℕ} {a b : ℕ} (h : Ht N m T e S a b) : Ht N m T e S b a := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  exact ⟨i2, i1, j2, j1, l2, l1, l4, l3, fun w hw => (r1 w hw).symm, fun w hw => (r2 w hw).symm, u2, u1, u4, u3, p2, p1⟩
lemma bi_uq2 {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hi : Lg N m T i) (hc : c ∈ insert a (insert b U)) (h1 : c = a → a ∉ U) (h2 : c = b → b ∉ U)
    (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hcU : c ∉ U := by
      rcases hcc with rfl | rfl; exacts [h1 rfl, h2 rfl]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl; exact hcU hx
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma pol_op {a b i : ℕ} {d e : Bool} (ha : sepb N e a i = true) (hb : sepb N e b i = false) (ho : sepb N e (op d a b) i = true) :
    (op d a b).testBit i = a.testBit i := by
  revert ha hb ho; unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
    cases b.testBit (N + i) <;> simp
lemma pol_phi {a b c i : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (h : Uq N e (insert a (insert b U)) c i)
    (hu : Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i) :
    (if c = a ∨ c = b then op d a b else c).testBit i = c.testBit i := by
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc] at hu ⊢
    rcases hcc with rfl | rfl
    · exact pol_op h.1 (h.2 b (by simp) (Ne.symm hab)) hu.1
    · rw [op_comm] at hu ⊢
      exact pol_op h.1 (h.2 a (by simp) hab) hu.1
  · rw [ite_eq_right hcc]
lemma ht_bi {a b k t c1 c2 : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hc1 : c1 ∈ insert a (insert b U)) (hc2 : c2 ∈ insert a (insert b U))
    (h1 : c1 = a → a ∉ U) (h1' : c1 = b → b ∉ U) (h2 : c2 = a → a ∉ U) (h2' : c2 = b → b ∉ U)
    (h : Ht N m T e (insert a (insert b U)) c1 c2) :
    Ht N m T e (insert (op d a b) U) (if c1 = a ∨ c1 = b then op d a b else c1) (if c2 = a ∨ c2 = b then op d a b else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := bi_uq2 he hl l1 hc1 h1 h1' u1
  have v2 := bi_uq2 he hl l2 hc2 h2 h2' u2
  have v3 := bi_uq2 he hl l3 hc1 h1 h1' u3
  have v4 := bi_uq2 he hl l4 hc2 h2 h2' u4
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, v1, v2, v3, v4, ?_, ?_⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r1 a (by simp), r1 b (by simp)]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r2 a (by simp), r2 b (by simp)]
    · exact r2 w (by simp [hw])
  · rw [pol_phi hab u1 v1, pol_phi hab u3 v3, p1]
  · rw [pol_phi hab u2 v2, pol_phi hab u4 v4, p2]
lemma ht_merge {a b k t : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (h : Ht N m T e (insert a (insert b U)) a b) : False := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := (bi_uq2 he hl l1 (by simp) (fun _ => ha) (fun _ => hb) u1).1
  have v2 := (bi_uq2 he hl l2 (by simp) (fun _ => ha) (fun _ => hb) u2).1
  have v3 := (bi_uq2 he hl l3 (by simp) (fun _ => ha) (fun _ => hb) u3).1
  have v4 := (bi_uq2 he hl l4 (by simp) (fun _ => ha) (fun _ => hb) u4).1
  simp only [true_or, or_true, if_true] at v1 v2 v3 v4
  have e1 := r1 a (by simp); have e2 := r2 a (by simp); have e1b := r1 b (by simp); have e2b := r2 b (by simp)
  have n1 := u1.2 b (by simp) (Ne.symm hab); have n3 := u3.2 b (by simp) (Ne.symm hab)
  have n2 := u2.2 a (by simp) hab; have n4 := u4.2 a (by simp) hab
  have s1 := u1.1; have s2 := u2.1; have s3 := u3.1; have s4 := u4.1
  revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 v1 v2 v3 v4 p1 p2
  unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> simp <;> grind
lemma un_uq2 {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (h1 : c = a → a ∉ U) (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  by_cases hca : c = a
  · exact un_uq hi (h1 hca) hc h
  · rw [ite_eq_right hca]
    have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
    · exact h.2 x (by simp [hx]) hne
lemma ht_un {a c1 c2 : ℕ} {U : Finset ℕ} (hc1 : c1 ∈ insert a U) (hc2 : c2 ∈ insert a U) (h1 : c1 = a → a ∉ U) (h2 : c2 = a → a ∉ U)
    (h : Ht N m T true (insert a U) c1 c2) :
    Ht N m T true (insert (a ^^^ m) U) (if c1 = a then a ^^^ m else c1) (if c2 = a then a ^^^ m else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have pp : ∀ {c i j : ℕ}, m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
      (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j := by
    intro c i j m1 m2 p
    split_ifs with h
    · subst h; simp [m1, m2, p]
    · exact p
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, un_uq2 l1 h1 hc1 u1, un_uq2 l2 h2 hc2 u2, un_uq2 l3 h1 hc1 u3, un_uq2 l4 h2 hc2 u4,
    pp l1.1 l3.1 p1, pp l2.1 l4.1 p2⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r1 a (by simp), l1.1, l2.1]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r2 a (by simp), l3.2.1, l4.2.1]
    · exact r2 w (by simp [hw])
lemma chrom {e : Bool} {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (he : e = true ∨ t = 0) :
    ∃ (x : ℕ) (f : ℕ → ℕ), S.card + t + x = k + 1 ∧ (∀ a ∈ S, f a ≤ x) ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Ht N m T e S a b → f a ≠ f b := by
  induction hl with
  | stop =>
    refine ⟨0, fun _ => 0, by simp, by simp, ?_⟩
    intro a ha b hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t a U hl ih =>
    have he1 : e = true := he.resolve_right (by omega)
    subst he1
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have hmin := hu.min hl hm
    obtain ⟨x, f, hx, hfx, hc⟩ := ih hmin.2 (Or.inl rfl)
    rw [Finset.card_insert_of_notMem hf] at hx
    have sm : ∀ {i1 i2 : ℕ}, m.testBit i1 = true → m.testBit i2 = true → (∀ w ∈ insert a U, w.testBit i1 = w.testBit i2) →
        ∀ w ∈ insert (a ^^^ m) U, w.testBit i1 = w.testBit i2 := by
      intro i1 i2 m1 m2 r w hw
      simp at hw
      rcases hw with rfl | hw
      · simp [r a (by simp), m1, m2]
      · exact r w (by simp [hw])
    by_cases ha : a ∈ U
    · have eS : insert a U = U := Finset.insert_eq_of_mem ha
      refine ⟨x + 1, fun c => if c = a then x + 1 else f c, by rw [eS]; omega, ?_, ?_⟩
      · intro c hcS
        rw [eS] at hcS
        by_cases hca : c = a
        · simp [hca]
        · simp only [hca, if_false]
          have := hfx c (by simp [hcS]); omega
      · intro c1 h1 c2 h2 h12 hh
        rw [eS] at h1 h2
        by_cases q1 : c1 = a
        · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
          have := hfx c2 (by simp [h2])
          simp only [q1, q2, if_true, if_false]; omega
        · by_cases q2 : c2 = a
          · have := hfx c1 (by simp [h1])
            simp only [q1, q2, if_true, if_false]; omega
          · simp only [q1, q2, if_false]
            refine hc c1 (by simp [h1]) c2 (by simp [h2]) h12 ?_
            obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := hh
            have tr : ∀ {c i : ℕ}, c ≠ a → Lg N m T i → Uq N true (insert a U) c i → Uq N true (insert (a ^^^ m) U) c i := by
              intro c i hca hi h
              refine ⟨h.1, fun y hy hne => ?_⟩
              simp at hy
              rcases hy with rfl | hy
              · have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
                rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
              · exact h.2 y (by simp [hy]) hne
            exact ⟨i1, i2, j1, j2, l1, l2, l3, l4, sm l1.1 l2.1 r1, sm l3.2.1 l4.2.1 r2, tr q1 l1 u1, tr q2 l2 u2, tr q1 l3 u3, tr q2 l4 u4, p1, p2⟩
    · rw [Finset.card_insert_of_notMem ha]
      have mem : ∀ {c : ℕ}, c ∈ insert a U → (if c = a then a ^^^ m else c) ∈ insert (a ^^^ m) U := by
        intro c hcS; split_ifs with h <;> simp at hcS ⊢; grind
      refine ⟨x, fun c => f (if c = a then a ^^^ m else c), by omega, fun c hcS => hfx _ (mem hcS), ?_⟩
      intro c1 h1 c2 h2 h12 hh
      refine hc _ (mem h1) _ (mem h2) ?_ ?_
      · split_ifs with p q q
        · exact absurd (p.trans q.symm) h12
        · intro e; simp at h2; rw [← e] at h2; rcases h2 with h | h
          · exact q (by rw [← e, h])
          · exact hf h
        · intro e; simp at h1; rw [e] at h1; rcases h1 with h | h
          · exact p (by rw [e, h])
          · exact hf h
        · exact h12
      · obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := hh
        have pp : ∀ {c i j : ℕ}, m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
            (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j := by
          intro c i j m1 m2 p
          split_ifs with h
          · subst h; simp [m1, m2, p]
          · exact p
        exact ⟨i1, i2, j1, j2, l1, l2, l3, l4, sm l1.1 l2.1 r1, sm l3.2.1 l4.2.1 r2, un_uq l1 ha h1 u1, un_uq l2 ha h2 u2, un_uq l3 ha h1 u3, un_uq l4 ha h2 u4,
          pp l1.1 l3.1 p1, pp l2.1 l4.1 p2⟩
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have hfS : op d a b ∉ insert a (insert b U) := fun h => hu.fresh hl hm (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by simp [h])
    have hmin := hu.min hl hm
    have he2 : e = true ∨ e = pos' t := by
      rcases he with h | h
      · exact Or.inl h
      · subst h; cases e <;> simp [pos']
    obtain ⟨x, f, hx, hfx, hc⟩ := ih hmin.2 he
    rw [Finset.card_insert_of_notMem hf] at hx
    have mem : ∀ {c : ℕ}, c ∈ insert a (insert b U) → (if c = a ∨ c = b then op d a b else c) ∈ insert (op d a b) U := fun h => phi_mem h
    by_cases ha : a ∈ U
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = U := by rw [Finset.insert_eq_of_mem hb, Finset.insert_eq_of_mem ha]
        refine ⟨x + 2, fun c => if c = a then x + 2 else if c = b then x + 1 else f c, by rw [eS]; omega, ?_, ?_⟩
        · intro c hcS
          rw [eS] at hcS
          have := hfx c (by simp [hcS])
          dsimp only; split_ifs <;> omega
        · intro c1 h1 c2 h2 h12 hh
          have k1 := h1; have k2 := h2
          rw [eS] at h1 h2
          have f1 := hfx c1 (by simp [h1]); have f2 := hfx c2 (by simp [h2])
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
            · by_cases q3 : c1 = b
              · have q4 : c2 ≠ b := fun e => h12 (q3.trans e.symm)
                simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
              · by_cases q4 : c2 = b
                · simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
                · simp only [q1, q2, q3, q4, if_false]
                  have := ht_bi hab he2 hl k1 k2 (fun e => absurd e q1) (fun e => absurd e q3) (fun e => absurd e q2) (fun e => absurd e q4) hh
                  simp only [q1, q2, q3, q4, or_self, if_false] at this
                  exact hc c1 (by simp [h1]) c2 (by simp [h2]) h12 this
      · have eS : insert a (insert b U) = insert b U := Finset.insert_eq_of_mem (by simp [ha])
        refine ⟨x + 1, fun c => if c = a then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem hb]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = a
          · simp [hca]
          · simp only [hca, if_false, false_or] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, false_or] at f2 ⊢; omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false, false_or] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun e => absurd e q1) (fun _ => hb) (fun e => absurd e q2) (fun _ => hb) hh
              simp only [q1, q2, if_false, false_or] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = b ∨ c1 ∈ U := by simp at h1; grind
              have h2' : c2 = b ∨ c2 ∈ U := by simp at h2; grind
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = insert a U := by rw [Finset.insert_eq_of_mem hb]
        refine ⟨x + 1, fun c => if c = b then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem ha]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = b
          · simp [hca]
          · simp only [hca, if_false, or_false] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = b
          · have q2 : c2 ≠ b := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, or_false] at f2 ⊢; omega
          · by_cases q2 : c2 = b
            · simp only [q1, q2, if_true, if_false, or_false] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun e => absurd e q1) (fun _ => ha) (fun e => absurd e q2) hh
              simp only [q1, q2, if_false, or_false] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = a ∨ c1 ∈ U := by simp at h1; grind
              have h2' : c2 = a ∨ c2 ∈ U := by simp at h2; grind
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
      · refine ⟨x, fun c => f (if c = a ∨ c = b then op d a b else c), ?_, fun c hcS => hfx _ (mem hcS), ?_⟩
        · rw [Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hb]; omega
        · intro c1 h1 c2 h2 h12 hh
          by_cases hab' : (c1 = a ∨ c1 = b) ∧ (c2 = a ∨ c2 = b)
          · exfalso
            have : Ht N m T e (insert a (insert b U)) a b := by
              rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
              · exact absurd rfl h12
              · exact hh
              · exact hh.symm
              · exact absurd rfl h12
            exact ht_merge hab he2 hl ha hb this
          · exact hc _ (mem h1) _ (mem h2) (phi_ne hf h1 h2 h12 hab')
              (ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun _ => hb) (fun _ => ha) (fun _ => hb) hh)
end chrom
lemma Acc.start {n T K b L : ℕ} {W : Set ℕ} {S : Finset ℕ} (h : ∀ q < L, ¬ Sol Z0 n (T &&& n) q (C n W)) (hS : Im n S ⊆ W)
    (hb : K ≤ b + L) : Acc n T K b (fun _ => 0) S := by
  intro U hU q hq hs
  simp only [Finset.sum_const_zero] at hq
  refine h q (by omega) (hs.mono le_rfl (C_mono (subset_trans ?_ hS)))
  exact Set.image_mono (by exact_mod_cast hU)
lemma Acc.const {m n T k k' t b : ℕ} {D : ℕ → ℕ} {S : Finset ℕ} (hn : n &&& m = n) (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n)
    (h : Acc n T k b D S) (hm : Min R m T k' t S) (hk : k' ≤ k) : (S.filter (Cst n)).card ≤ b := by
  obtain ⟨q, hq, hs⟩ := hm.const hn hT0 hT1
  by_contra hc
  exact h S subset_rfl q (by simp only [sdiff_self, Finset.bot_eq_empty, Finset.sum_empty]; omega) hs
lemma Acc.step {n T k b δ c' : ℕ} {D D' : ℕ → ℕ} {S S' : Finset ℕ} (h : Acc n T (k + 1) b D S)
    (H : ∀ U' ⊆ S', ∀ q, Sol Z0 n (T &&& n) q (C n (Im n U')) → ∃ U ⊆ S, ∃ r, Sol Z0 n (T &&& n) r (C n (Im n U)) ∧
      r + δ + ∑ w ∈ S' \ U', D' w ≤ q + 1 + ∑ w ∈ S \ U, D w)
    (he : ∃ q, q + c' ≤ k ∧ Sol Z0 n (T &&& n) q (C n (Im n S'))) : δ + c' ≤ b ∧ Acc n T k (b - δ) D' S' := by
  have hd : δ + c' ≤ b := by
    obtain ⟨q, hq, hs⟩ := he
    obtain ⟨U, hU, r, hr, hle⟩ := H S' subset_rfl q hs
    by_contra hc
    refine h U hU r ?_ hr
    simp only [sdiff_self, Finset.bot_eq_empty, Finset.sum_empty] at hle
    omega
  refine ⟨hd, fun U' hU' q hq hs => ?_⟩
  obtain ⟨U, hU, r, hr, hle⟩ := H U' hU' q hs
  exact h U hU r (by omega) hr
section sums
variable {g a c : ℕ} {U0 U' : Finset ℕ} {D D' : ℕ → ℕ}
lemma sum_child (hg : g ∉ U0) : ∑ w ∈ insert g U0 \ U', D' w = (if g ∈ U' then 0 else D' g) + ∑ w ∈ U0 \ U'.erase g, D' w := by
  have e : U0 \ U'.erase g = U0 \ U' := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_erase, not_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 (fun e => hg (e ▸ h1)) h⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun _ => h2⟩
  rw [e]
  by_cases h : g ∈ U'
  · rw [ite_eq_left h, Finset.insert_sdiff_of_mem _ h, zero_add]
  · rw [ite_eq_right h, Finset.insert_sdiff_of_notMem _ h, Finset.sum_insert (by simp [hg])]
lemma sum_parent {V : Finset ℕ} (hV : V ⊆ U0) (hac : a ≠ c) :
    ∑ w ∈ insert a (insert c U0) \ V, D w = ∑ w ∈ U0 \ V, D w + (if a ∈ U0 then 0 else D a) + (if c ∈ U0 then 0 else D c) := by
  have e : insert a (insert c U0) \ V = (insert a (insert c U0)) \ V := rfl
  by_cases ha : a ∈ U0 <;> by_cases hc : c ∈ U0
  · rw [Finset.insert_eq_of_mem (by simp [ha]), Finset.insert_eq_of_mem hc]; simp [ha, hc]
  · rw [Finset.insert_eq_of_mem (by simp [ha]), Finset.insert_sdiff_of_notMem _ (fun h => hc (hV h)), Finset.sum_insert (by simp [hc])]
    simp [ha, hc]; omega
  · rw [Finset.insert_eq_of_mem hc, Finset.insert_sdiff_of_notMem _ (fun h => ha (hV h)), Finset.sum_insert (by simp [ha])]
    simp [ha, hc]; omega
  · rw [Finset.insert_sdiff_of_notMem _ (fun h => ha (hV h)), Finset.insert_sdiff_of_notMem _ (fun h => hc (hV h)),
      Finset.sum_insert (by simp [ha, hac]), Finset.sum_insert (by simp [hc])]
    simp [ha, hc]; omega
lemma sum_mono {A B : Finset ℕ} (hAB : ∀ w ∈ A, w ∉ B → D' w = 0) (hD : ∀ w ∈ A, w ∈ B → D' w ≤ D w) : ∑ w ∈ A, D' w ≤ ∑ w ∈ B, D w := by
  calc ∑ w ∈ A, D' w = ∑ w ∈ A.filter (· ∈ B), D' w := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun w hw => ?_
        split_ifs with h
        · rfl
        · exact hAB w hw h
    _ ≤ ∑ w ∈ A.filter (· ∈ B), D w := Finset.sum_le_sum fun w hw => by simp at hw; exact hD w hw.1 hw.2
    _ ≤ ∑ w ∈ B, D w := Finset.sum_le_sum_of_subset fun w hw => by simp at hw; exact hw.2
end sums
lemma kpa_le (κ : Kd) (x : ℕ) : κ.kpa x ≤ x := by cases κ <;> simp [Kd.kpa]
lemma kpc_le (κ : Kd) (x : ℕ) : κ.kpc x ≤ x := by cases κ <;> simp [Kd.kpc]
theorem Acc.bi {m n T k k' t b : ℕ} {d : Bool} {a c : ℕ} {D D' : ℕ → ℕ} {S S' : Finset ℕ} (hn : n &&& m = n) (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n)
    (h : Acc n T (k + 1) b D S) (hb : Bi R d a c S S') (hm : Min R m T (k' + 1) t S) (hl : Live R m T k' t S') (hk : k' ≤ k)
    (κ : Kd) (hκ : κ.ok n d a c) (hD : DStep κ D D' (op d a c) a c S') :
    κ.del (if a ∈ S' then 0 else D a) (if c ∈ S' then 0 else D c) + (S'.filter (Cst n)).card ≤ b ∧
      Acc n T k (b - κ.del (if a ∈ S' then 0 else D a) (if c ∈ S' then 0 else D c)) D' S' := by
  have hfr : op d a c ∉ S := fun h' => hb.fresh hl hm.2 (sub_C _ _ (by simpa using h'))
  have hmin := hb.min hl hm.2
  obtain ⟨hac, U0, hS, hS', hal⟩ := hb
  set g := op d a c with hgdef
  have hgU : g ∉ U0 := fun h' => hfr (by rw [hS]; simp [h'])
  have hga : a ≠ g := fun e => hfr (by rw [hS, ← e]; simp)
  have hgc : c ≠ g := fun e => hfr (by rw [hS, ← e]; simp)
  have iffa : a ∈ S' ↔ a ∈ U0 := by rw [hS']; simp [hga]
  have iffc : c ∈ S' ↔ c ∈ U0 := by rw [hS']; simp [hgc]
  have hDa : a ∈ U0 → D' a ≤ κ.kpa (D a) := fun h' => hD.ha (iffa.2 h')
  have hDc : c ∈ U0 → D' c ≤ κ.kpc (D c) := fun h' => hD.hc (iffc.2 h')
  have hDg := hD.hg
  simp only [iffa, iffc] at hDg ⊢
  have hDo : ∀ w ∈ U0, w ≠ a → w ≠ c → D' w ≤ D w := fun w hw h1 h2 => hD.ho w (by rw [hS']; simp [hw]) (fun e => hgU (e ▸ hw)) h1 h2
  have hDle : ∀ w ∈ U0, D' w ≤ D w := by
    intro w hw
    by_cases h1 : w = a
    · subst h1; exact (hDa hw).trans (kpa_le _ _)
    by_cases h2 : w = c
    · subst h2; exact (hDc hw).trans (kpc_le _ _)
    exact hDo w hw h1 h2
  refine Acc.step h ?_ ?_
  · intro U' hU' q hs
    have hV : U'.erase g ⊆ U0 := by
      intro x hx
      rw [Finset.mem_erase] at hx
      have := hU' hx.2; rw [hS', Finset.mem_insert] at this
      exact this.resolve_left hx.1
    have hVS : U'.erase g ⊆ S := hV.trans (by rw [hS]; intro x hx; simp [hx])
    have hUi : U' ⊆ insert g (U'.erase g) := fun x hx => by by_cases e : x = g <;> simp [e, hx]
    rw [hS', sum_child (D' := D') hgU]
    by_cases hgU' : g ∈ U'
    · rw [ite_eq_left hgU', zero_add]
      cases κ with
      | N =>
        refine ⟨insert a (insert c (U'.erase g)), ?_, q + 1, ?_, ?_⟩
        · intro x hx; simp only [Finset.mem_insert] at hx
          rcases hx with rfl | rfl | hx
          · rw [hS]; simp
          · rw [hS]; simp
          · exact hVS hx
        · refine .bi (d := d) (Im_mem (x := a) (by simp)) (Im_mem (x := c) (by simp)) (al0 _ _ _)
            (hs.mono le_rfl (C_Im_sub (S := insert a (insert c (U'.erase g))) (hUi.trans (Finset.insert_subset_insert _ ?_)) ?_ (Set.subset_insert _ _)))
          · intro x hx; simp only [Finset.mem_insert]; exact Or.inr (Or.inr hx)
          · rw [hgdef, and_op]; exact Or.inl rfl
        · have : ∑ w ∈ U0 \ U'.erase g, D' w ≤ ∑ w ∈ S \ insert a (insert c (U'.erase g)), D w := by
            refine sum_mono (fun w hw hw2 => ?_) (fun w hw _ => hDle w (Finset.mem_sdiff.1 hw).1)
            rw [Finset.mem_sdiff] at hw
            have : w = a ∨ w = c := by
              by_contra hno; push Not at hno
              exact hw2 (Finset.mem_sdiff.2 ⟨by rw [hS]; simp [hw.1], by simp only [Finset.mem_insert]; grind⟩)
            rcases this with rfl | rfl
            · have := hDa hw.1; simpa [Kd.kpa] using this
            · have := hDc hw.1; simpa [Kd.kpc] using this
          simp only [Kd.del]; omega
      | K0 =>
        refine ⟨U'.erase g, hVS, q, hs.mono le_rfl (C_Im_sub hUi (Cst_mem hκ) subset_rfl), ?_⟩
        have h1 : ∑ w ∈ U0 \ U'.erase g, D' w ≤ ∑ w ∈ U0 \ U'.erase g, D w := Finset.sum_le_sum fun w hw => hDle w (Finset.mem_sdiff.1 hw).1
        rw [hS, sum_parent hV hac]; simp only [Kd.del]; omega
      | KA =>
        refine ⟨insert a (U'.erase g), ?_, q, hs.mono le_rfl (C_Im_sub (S := insert a (U'.erase g)) (hUi.trans (Finset.insert_subset_insert _ (Finset.subset_insert _ _))) ?_ subset_rfl), ?_⟩
        · intro x hx; simp only [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · rw [hS]; simp
          · exact hVS hx
        · have e : g &&& n = a &&& n := hκ
          rw [e]; exact Im_mem (by simp)
        · have : ∑ w ∈ U0 \ U'.erase g, D' w + (if c ∈ U0 then 0 else D c) ≤ ∑ w ∈ S \ insert a (U'.erase g), D w := by
            have key : ∀ B : Finset ℕ, (∀ w ∈ U0 \ U'.erase g, w ≠ a → w ∈ B) → ∑ w ∈ U0 \ U'.erase g, D' w ≤ ∑ w ∈ B, D w := by
              intro B hB
              refine sum_mono (fun w hw hw2 => ?_) (fun w hw _ => hDle w (Finset.mem_sdiff.1 hw).1)
              have : w = a := by by_contra hno; exact hw2 (hB w hw hno)
              subst this
              have := hDa (Finset.mem_sdiff.1 hw).1; simpa [Kd.kpa] using this
            by_cases hc : c ∈ U0
            · rw [ite_eq_left hc, add_zero]
              refine key _ fun w hw hne => ?_
              rw [Finset.mem_sdiff] at hw ⊢
              exact ⟨by rw [hS]; simp [hw.1], by simp only [Finset.mem_insert]; grind⟩
            · rw [ite_eq_right hc]
              have hcB : c ∈ S \ insert a (U'.erase g) := by
                rw [Finset.mem_sdiff]
                refine ⟨by rw [hS]; simp, ?_⟩
                simp only [Finset.mem_insert]
                rintro (h1 | h1)
                · exact hac h1.symm
                · exact hc (hV h1)
              rw [← Finset.sum_erase_add _ _ hcB]
              refine Nat.add_le_add_right (key _ fun w hw hne => ?_) _
              rw [Finset.mem_sdiff] at hw
              rw [Finset.mem_erase, Finset.mem_sdiff]
              exact ⟨fun e => hc (e ▸ hw.1), by rw [hS]; simp [hw.1], by simp only [Finset.mem_insert]; grind⟩
          simp only [Kd.del]; omega
      | KC =>
        refine ⟨insert c (U'.erase g), ?_, q, hs.mono le_rfl (C_Im_sub (S := insert c (U'.erase g)) (hUi.trans (Finset.insert_subset_insert _ (Finset.subset_insert _ _))) ?_ subset_rfl), ?_⟩
        · intro x hx; simp only [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · rw [hS]; simp
          · exact hVS hx
        · have e : g &&& n = c &&& n := hκ
          rw [e]; exact Im_mem (by simp)
        · have : ∑ w ∈ U0 \ U'.erase g, D' w + (if a ∈ U0 then 0 else D a) ≤ ∑ w ∈ S \ insert c (U'.erase g), D w := by
            have key : ∀ B : Finset ℕ, (∀ w ∈ U0 \ U'.erase g, w ≠ c → w ∈ B) → ∑ w ∈ U0 \ U'.erase g, D' w ≤ ∑ w ∈ B, D w := by
              intro B hB
              refine sum_mono (fun w hw hw2 => ?_) (fun w hw _ => hDle w (Finset.mem_sdiff.1 hw).1)
              have : w = c := by by_contra hno; exact hw2 (hB w hw hno)
              subst this
              have := hDc (Finset.mem_sdiff.1 hw).1; simpa [Kd.kpc] using this
            by_cases ha : a ∈ U0
            · rw [ite_eq_left ha, add_zero]
              refine key _ fun w hw hne => ?_
              rw [Finset.mem_sdiff] at hw ⊢
              exact ⟨by rw [hS]; simp [hw.1], by simp only [Finset.mem_insert]; grind⟩
            · rw [ite_eq_right ha]
              have haB : a ∈ S \ insert c (U'.erase g) := by
                rw [Finset.mem_sdiff]
                refine ⟨by rw [hS]; simp, ?_⟩
                simp only [Finset.mem_insert]
                rintro (h1 | h1)
                · exact hac h1
                · exact ha (hV h1)
              rw [← Finset.sum_erase_add _ _ haB]
              refine Nat.add_le_add_right (key _ fun w hw hne => ?_) _
              rw [Finset.mem_sdiff] at hw
              rw [Finset.mem_erase, Finset.mem_sdiff]
              exact ⟨fun e => ha (e ▸ hw.1), by rw [hS]; simp [hw.1], by simp only [Finset.mem_insert]; grind⟩
          simp only [Kd.del]; omega
    · rw [ite_eq_right hgU']
      have e : U'.erase g = U' := Finset.erase_eq_of_notMem hgU'
      rw [e] at hV hVS ⊢
      refine ⟨U', hVS, q, hs, ?_⟩
      have h1 : ∑ w ∈ U0 \ U', D' w ≤ ∑ w ∈ U0 \ U', D w := Finset.sum_le_sum fun w hw => hDle w (Finset.mem_sdiff.1 hw).1
      rw [hS, sum_parent hV hac]
      cases κ <;> simp only [Kd.del, Kd.out] at hDg ⊢ <;> omega
  · obtain ⟨q, hq, hs⟩ := hmin.const hn hT0 hT1
    exact ⟨q, by omega, hs⟩
theorem Acc.un {m n T k k' t b : ℕ} {a : ℕ} {D D' : ℕ → ℕ} {S S' : Finset ℕ} (hn : n &&& m = n) (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n)
    (h : Acc n T (k + 1) b D S) (hb : Un m a S S') (hm : Min R m T (k' + 1) (t + 1) S) (hl : Live R m T k' t S') (hk : k' ≤ k) (κ : Bool)
    (hκ : κ = true → Cst n a) (hg : D' (a ^^^ m) ≤ (if κ then 0 else 1) + (if a ∈ S' then 0 else D a))
    (hka : a ∈ S' → D' a ≤ if κ then D a else 0) (ho : ∀ w ∈ S', w ≠ a ^^^ m → w ≠ a → D' w ≤ D w) :
    (if κ then 1 else 0) + (S'.filter (Cst n)).card ≤ b ∧ Acc n T k (b - if κ then 1 else 0) D' S' := by
  have hfr : a ^^^ m ∉ S := fun h' => hb.fresh hl hm.2 (sub_C _ _ (by simpa using h'))
  have hmin := hb.min hl hm.2
  obtain ⟨U0, hS, hS'⟩ := hb
  set g := a ^^^ m with hgdef
  have hgU : g ∉ U0 := fun h' => hfr (by rw [hS]; simp [h'])
  have hga : a ≠ g := fun e => hfr (by rw [hS, ← e]; simp)
  have iffa : a ∈ S' ↔ a ∈ U0 := by rw [hS']; simp [hga]
  simp only [iffa] at hg hka
  have hDle : ∀ w ∈ U0, D' w ≤ D w := by
    intro w hw
    by_cases h1 : w = a
    · subst h1
      have := hka hw
      split_ifs at this <;> omega
    exact ho w (by rw [hS']; simp [hw]) (fun e => hgU (e ▸ hw)) h1
  have par : ∀ V ⊆ U0, ∑ w ∈ S \ V, D w = ∑ w ∈ U0 \ V, D w + (if a ∈ U0 then 0 else D a) := by
    intro V hV
    by_cases ha : a ∈ U0
    · rw [hS, Finset.insert_eq_of_mem ha]; simp [ha]
    · rw [hS, Finset.insert_sdiff_of_notMem _ (fun h => ha (hV h)), Finset.sum_insert (by simp [ha])]; simp [ha]; omega
  refine Acc.step h ?_ ?_
  · intro U' hU' q hs
    have hV : U'.erase g ⊆ U0 := by
      intro x hx
      rw [Finset.mem_erase] at hx
      have := hU' hx.2; rw [hS', Finset.mem_insert] at this
      exact this.resolve_left hx.1
    have hVS : U'.erase g ⊆ S := hV.trans (by rw [hS]; exact Finset.subset_insert _ _)
    have hUi : U' ⊆ insert g (U'.erase g) := fun x hx => by by_cases e : x = g <;> simp [e, hx]
    rw [hS', sum_child (D' := D') hgU]
    by_cases hgU' : g ∈ U'
    · rw [ite_eq_left hgU', zero_add]
      by_cases hk1 : κ = true
      · have hc := hκ hk1
        refine ⟨U'.erase g, hVS, q, hs.mono le_rfl (C_Im_sub hUi (Cst_mem (by rw [hgdef]; exact (Cst_neg hn).2 hc)) subset_rfl), ?_⟩
        have h1 : ∑ w ∈ U0 \ U'.erase g, D' w ≤ ∑ w ∈ U0 \ U'.erase g, D w := Finset.sum_le_sum fun w hw => hDle w (Finset.mem_sdiff.1 hw).1
        rw [par _ hV]; simp only [hk1, ite_true]; omega
      · refine ⟨insert a (U'.erase g), ?_, q + 1, ?_, ?_⟩
        · intro x hx; simp only [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · rw [hS]; simp
          · exact hVS hx
        · refine .un (Im_mem (x := a) (by simp)) (hs.mono le_rfl (C_Im_sub (S := insert a (U'.erase g))
            (hUi.trans (Finset.insert_subset_insert _ (Finset.subset_insert _ _))) ?_ (Set.subset_insert _ _)))
          rw [hgdef, and_neg hn]; exact Or.inl rfl
        · have : ∑ w ∈ U0 \ U'.erase g, D' w ≤ ∑ w ∈ S \ insert a (U'.erase g), D w := by
            refine sum_mono (fun w hw hw2 => ?_) (fun w hw _ => hDle w (Finset.mem_sdiff.1 hw).1)
            rw [Finset.mem_sdiff] at hw
            have : w = a := by
              by_contra hno
              exact hw2 (Finset.mem_sdiff.2 ⟨by rw [hS]; simp [hw.1], by simp only [Finset.mem_insert]; grind⟩)
            subst this
            have := hka hw.1; simpa [hk1] using this
          rw [ite_eq_right hk1]; omega
    · rw [ite_eq_right hgU']
      have e : U'.erase g = U' := Finset.erase_eq_of_notMem hgU'
      rw [e] at hV hVS ⊢
      refine ⟨U', hVS, q, hs, ?_⟩
      have h1 : ∑ w ∈ U0 \ U', D' w ≤ ∑ w ∈ U0 \ U', D w := Finset.sum_le_sum fun w hw => hDle w (Finset.mem_sdiff.1 hw).1
      rw [par _ hV]
      split_ifs at hg ⊢ <;> omega
  · obtain ⟨q, hq, hs⟩ := hmin.const hn hT0 hT1
    exact ⟨q, by omega, hs⟩
lemma Kd.out_le (κ : Kd) (la lc : ℕ) : κ.out la lc ≤ 1 + la + lc := by cases κ <;> simp [Kd.out] <;> omega
lemma DStep.le {κ : Kd} {D D' : ℕ → ℕ} {g a c : ℕ} {S' : Finset ℕ} (h : DStep κ D D' g a c S') : ∀ w ∈ S', w ≠ g → D' w ≤ D w := by
  intro w hw hg
  by_cases h1 : w = a
  · subst h1; exact (h.ha hw).trans (kpa_le _ _)
  by_cases h2 : w = c
  · subst h2; exact (h.hc hw).trans (kpc_le _ _)
  exact h.ho w hw hg h1 h2
lemma DStep.sum_le {κ : Kd} {d : Bool} {a c : ℕ} {D D' : ℕ → ℕ} {S S' : Finset ℕ} (hb : Bi R d a c S S') (hfr : op d a c ∉ S)
    (h : DStep κ D D' (op d a c) a c S') : ∑ w ∈ S', D' w ≤ 1 + ∑ w ∈ S, D w := by
  obtain ⟨hac, U0, hS, hS', hal⟩ := hb
  set g := op d a c with hgdef
  have hgU : g ∉ U0 := fun h' => hfr (by rw [hS]; simp [h'])
  have hga : a ≠ g := fun e => hfr (by rw [hS, ← e]; simp)
  have hgc : c ≠ g := fun e => hfr (by rw [hS, ← e]; simp)
  have iffa : a ∈ S' ↔ a ∈ U0 := by rw [hS']; simp [hga]
  have iffc : c ∈ S' ↔ c ∈ U0 := by rw [hS']; simp [hgc]
  have h1 := h.hg.trans (Kd.out_le _ _ _)
  simp only [iffa, iffc] at h1
  have h2 : ∑ w ∈ U0, D' w ≤ ∑ w ∈ U0, D w := Finset.sum_le_sum fun w hw => h.le w (by rw [hS']; simp [hw]) (fun e => hgU (e ▸ hw))
  have h3 := sum_parent (D := D) (U0 := U0) (V := ∅) (by simp) hac
  simp only [Finset.sdiff_empty] at h3
  rw [hS', Finset.sum_insert hgU, hS, h3]
  omega
lemma un_sum_le {m a e : ℕ} {D D' : ℕ → ℕ} {S S' : Finset ℕ} (hb : Un m a S S') (hfr : a ^^^ m ∉ S) (he : e ≤ 1)
    (hg : D' (a ^^^ m) ≤ e + (if a ∈ S' then 0 else D a)) (ho : ∀ w ∈ S', w ≠ a ^^^ m → D' w ≤ D w) : ∑ w ∈ S', D' w ≤ 1 + ∑ w ∈ S, D w := by
  obtain ⟨U0, hS, hS'⟩ := hb
  set g := a ^^^ m with hgdef
  have hgU : g ∉ U0 := fun h' => hfr (by rw [hS]; simp [h'])
  have hga : a ≠ g := fun e => hfr (by rw [hS, ← e]; simp)
  have iffa : a ∈ S' ↔ a ∈ U0 := by rw [hS']; simp [hga]
  simp only [iffa] at hg
  have h2 : ∑ w ∈ U0, D' w ≤ ∑ w ∈ U0, D w := Finset.sum_le_sum fun w hw => ho w (by rw [hS']; simp [hw]) (fun e => hgU (e ▸ hw))
  have h3 : ∑ w ∈ S, D w = ∑ w ∈ U0, D w + (if a ∈ U0 then 0 else D a) := by
    by_cases ha : a ∈ U0
    · rw [hS, Finset.insert_eq_of_mem ha]; simp [ha]
    · rw [hS, Finset.sum_insert ha]; simp [ha]; omega
  rw [hS', Finset.sum_insert hgU, h3]
  omega
noncomputable section core
end core
lemma bR (c e t : Bool) : (Bool.rec (motive := fun _ => Bool) e t c : Bool) = bif c then t else e := by cases c <;> rfl
lemma st_eq (n : ℕ) (f : ℕ → Bool) : st n f = f n := by cases n <;> rfl
lemma nl (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma no (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nx (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nsr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma sp_bit (d : Bool) (l s i : ℕ) : (sp d l s).testBit i = (l.testBit i && sepb NN d s i) := by
  cases d <;> simp [sp, sepb, nl, nx, nsr, Nat.testBit_shiftRight] <;>
    cases l.testBit i <;> cases s.testBit i <;> cases s.testBit (NN + i) <;> rfl
lemma cov_bit (d : Bool) (l i : ℕ) (v : List W) : (cov d l v).testBit i = true ↔ ∃ w ∈ v, (sp d l w.s).testBit i = true := by
  induction v with
  | nil => simp [cov]
  | cons w v ih =>
    change (Nat.lor (sp d l w.s) (cov d l v)).testBit i = true ↔ _
    simp [no, ih]
lemma twice_bit (d : Bool) (l i : ℕ) (v : List W) (h : (twice d l v).testBit i = false) :
    v.Pairwise (fun w w' => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) := by
  induction v with
  | nil => simp
  | cons w v ih =>
    change (Nat.lor (Nat.land (sp d l w.s) (cov d l v)) (twice d l v)).testBit i = false at h
    simp only [no, nl, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff] at h
    refine List.pairwise_cons.2 ⟨fun w' hw' ⟨h1, h2⟩ => ?_, ih h.2⟩
    have := (cov_bit d l i v).2 ⟨w', hw', h2⟩
    simp [h1, this] at h
lemma Rep.mem {v : List W} {S : Finset ℕ} (h : Rep v S) {x : ℕ} : x ∈ S ↔ ∃ w ∈ v, w.s = x := by
  rw [← h.2]; simp
lemma Rep.inj {v : List W} {S : Finset ℕ} (h : Rep v S) {w w' : W} (hw : w ∈ v) (hw' : w' ∈ v) (e : w.s = w'.s) : w = w' :=
  List.inj_on_of_nodup_map h.1 hw hw' e
lemma Rep.card {v : List W} {S : Finset ℕ} (h : Rep v S) : S.card = v.length := by
  rw [← h.2, List.toFinset_card_of_nodup h.1, List.length_map]
lemma uq_of {d : Bool} {l i : ℕ} {v : List W} {S : Finset ℕ} (h : Rep v S) {w : W} (hw : w ∈ v)
    (hu : (Nat.land (sp d l w.s) (wst d l v)).testBit i = true) : l.testBit i = true ∧ Uq NN d S w.s i := by
  simp only [nl, wst, nx, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true, sp_bit] at hu
  obtain ⟨⟨hl, hs⟩, ht⟩ := hu
  have ht : (twice d l v).testBit i = false := by simpa [hl] using ht
  refine ⟨hl, hs, fun c hc hne => ?_⟩
  obtain ⟨w', hw', rfl⟩ := h.mem.1 hc
  have hp := twice_bit d l i v ht
  haveI : Std.Symm (fun w w' : W => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) :=
    ⟨fun a b h h' => h h'.symm⟩
  have := hp.forall hw hw' (fun e => hne (by rw [e]))
  simp only [sp_bit, hl, hs, Bool.true_and, true_and] at this
  simpa using this
lemma bitsOf_bit {L : List (ℕ × ℕ)} {h : ℕ} (hh : (bitsOf L).testBit h = true) : ∃ s ∈ L, s.2 = h := by
  induction L with
  | nil => simp [bitsOf] at hh
  | cons s L ih =>
    change (2 ^ s.2 ||| bitsOf L).testBit h = true at hh
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact ⟨s, by simp, by simpa using hh⟩
    · obtain ⟨s', hs', e⟩ := ih hh; exact ⟨s', by simp [hs'], e⟩
lemma carry {u A p h : ℕ} (hp : p < h) (hA : A % 2 ^ h + 2 ^ (p + 1) = 2 ^ h + A % 2 ^ p) (hAh : A.testBit h = false)
    (huh : u.testBit h = false) (hup : u.testBit p = false) (hs : (u + A).testBit h = true) :
    ∃ i, p < i ∧ i < h ∧ u.testBit i = true := by
  by_contra hno
  push Not at hno
  have e1 : u % 2 ^ h = u % 2 ^ p := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_mod_two_pow]
    by_cases h1 : i < p
    · simp [h1, show i < h by omega]
    · by_cases h2 : i < h
      · rcases Nat.lt_or_ge p i with h3 | h3
        · simp [h1, hno i h3 h2]
        · obtain rfl : i = p := by omega
          simp [hup]
      · simp [h1, h2]
  have l1 := Nat.mod_lt u (Nat.two_pow_pos p)
  have l2 := Nat.mod_lt A (Nat.two_pow_pos p)
  have hlt : u % 2 ^ h + A % 2 ^ h < 2 ^ h := by rw [e1]; have := Nat.pow_succ 2 p; omega
  have e2 : (u + A).testBit h = (u / 2 ^ h + A / 2 ^ h).testBit 0 := by
    have : u + A = 2 ^ h * (u / 2 ^ h + A / 2 ^ h) + (u % 2 ^ h + A % 2 ^ h) := by
      have a1 := Nat.div_add_mod u (2 ^ h); have a2 := Nat.div_add_mod A (2 ^ h)
      rw [Nat.mul_add]; omega
    rw [this, Nat.testBit_two_pow_mul_add _ hlt]; simp
  have b1 : (u / 2 ^ h).testBit 0 = false := by rw [← huh, Nat.testBit_div_two_pow]; simp
  have b2 : (A / 2 ^ h).testBit 0 = false := by rw [← hAh, Nat.testBit_div_two_pow]; simp
  rw [e2] at hs
  simp [Nat.testBit_zero] at hs b1 b2
  omega
lemma flag_seg {L : List (ℕ × ℕ)} (hL : L.all segOk = true) {u : ℕ} (hu : ∀ i, u.testBit i = true → AA.testBit i = true)
    {s : ℕ × ℕ} (hs : s ∈ L) (hb : (u + AA).testBit s.2 = true) : ∃ i, s.1 < i ∧ i < s.2 ∧ u.testBit i = true := by
  have h := List.all_eq_true.1 hL s hs
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  refine carry h.1.1.1 h.1.1.2 h.2 ?_ ?_ hb
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.2] at this; simp at this
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.1.2] at this; simp at this
lemma hit_spec {f e : ℕ} (h : hit f e = true) :
    (∃ s ∈ segsX, f.testBit s.2 = true ∧ e.testBit s.2 = true) ∧ (∃ s ∈ segsY, f.testBit s.2 = true ∧ e.testBit s.2 = true) := by
  have aux : ∀ H, Nat.beq (Nat.land (Nat.land f e) H) 0 = false → ∃ i, f.testBit i = true ∧ e.testBit i = true ∧ H.testBit i = true := by
    intro H hH
    have hne : (f &&& e &&& H) ≠ 0 := fun h0 => by rw [nl, nl, h0] at hH; simp at hH
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
    simp at hi; exact ⟨i, hi.1.1, hi.1.2, hi.2⟩
  simp only [hit, bR] at h
  cases h1 : Nat.beq (Nat.land (Nat.land f e) HX) 0 with
  | true => rw [h1] at h; simp only [cond_true, Bool.false_eq_true] at h
  | false =>
    cases h2 : Nat.beq (Nat.land (Nat.land f e) HY) 0 with
    | true => rw [h1, h2] at h; simp only [cond_true, cond_false, Bool.false_eq_true] at h
    | false =>
      obtain ⟨i, a1, a2, a3⟩ := aux _ h1
      obtain ⟨j, b1, b2, b3⟩ := aux _ h2
      rw [HX_eq] at a3; rw [HY_eq] at b3
      obtain ⟨s, hs, rfl⟩ := bitsOf_bit a3
      obtain ⟨s', hs', rfl⟩ := bitsOf_bit b3
      exact ⟨⟨s, hs, a1, a2⟩, ⟨s', hs', b1, b2⟩⟩
lemma hits_false {f : ℕ} {m : List ℕ} (h : ∀ e ∈ m, hit f e = false) : hits f m = false := by
  induction m with
  | nil => rfl
  | cons e m ih =>
    change (Bool.rec (motive := fun _ => Bool) (hits f m) true (hit f e) : Bool) = false
    rw [bR, h e (by simp), ih (fun x hx => h x (by simp [hx]))]; rfl
lemma rect_false {d : Bool} {l o : ℕ} {v : List W} : ∀ {m : List ℕ}, v.Pairwise (fun a b => hit (flag d l o b) (flag d l o a) = false) →
    (∀ w ∈ v, ∀ e ∈ m, hit (flag d l o w) e = false) → rect d l o v m = false := by
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro m hp hm
    change (Bool.rec (motive := fun _ => Bool) (rect d l o v (flag d l o w :: m)) true (hits (flag d l o w) m) : Bool) = false
    rw [List.pairwise_cons] at hp
    rw [bR, hits_false (hm w (by simp)), ih hp.2]; · rfl
    intro w' hw' e he
    simp at he
    rcases he with rfl | he
    · exact hp.1 w' hw'
    · exact hm w' (by simp [hw']) e he
lemma Live.pos {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : 0 < S.card := by
  cases h with
  | stop => simp
  | un => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
  | bi => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
lemma pk_succ (n : ℕ) (f : ℕ → ℕ) : pk (n + 1) f = 2 ^ (5 * n) * f n + pk n f := by
  rw [pk, Finset.sum_range_succ, ← pk]; ring
lemma pk_lt {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j < 32) : pk n f < 2 ^ (5 * n) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    rw [pk_succ, show 5 * (n + 1) = 5 * n + 5 by ring, pow_add]
    have : 2 ^ (5 * n) * f n ≤ 2 ^ (5 * n) * 31 := Nat.mul_le_mul_left _ (by omega)
    omega
lemma pk_add (n : ℕ) (f g : ℕ → ℕ) : pk n f + pk n g = pk n (fun j => f j + g j) := by
  simp [pk, ← Finset.sum_add_distrib, add_mul]
lemma pk_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) : pk n f = pk n g :=
  Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]
lemma pk_sub {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, g j ≤ f j) : pk n f - pk n g = pk n (fun j => f j - g j) := by
  have : pk n (fun j => f j - g j) + pk n g = pk n f := by
    rw [pk_add]; exact pk_congr fun j hj => Nat.sub_add_cancel (h j hj)
  omega
lemma pk_guard {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, 16 ≤ f j ∧ f j < 32) :
    pk n f &&& pk n (fun _ => 16) = pk n (fun _ => 16) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have ih := ih (fun j hj => h j (by omega))
    have h1 : pk n f < 2 ^ (5 * n) := pk_lt fun j hj => (h j (by omega)).2
    have h2 : pk n (fun _ => 16) < 2 ^ (5 * n) := pk_lt fun _ _ => by omega
    have h3 : f n &&& 16 = 16 := by
      obtain ⟨a, b⟩ := h n (by omega)
      generalize f n = x at *
      interval_cases x <;> rfl
    rw [pk_succ, pk_succ]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2]
    split_ifs with hi
    · rw [← Nat.testBit_and, ih]
    · rw [← Nat.testBit_and, h3]
lemma pk_of {n : ℕ} : ∀ {x : ℕ}, isPk n x → x = pk n (fun j => (x.testBit (5 * j)).toNat) := by
  induction n with
  | zero =>
    intro x h
    simp only [pk, Finset.range_zero, Finset.sum_empty]
    apply Nat.eq_of_testBit_eq; intro i
    by_contra hc
    have := h i (by simpa using hc); omega
  | succ n ih =>
    intro x h
    have hm : isPk n (x % 2 ^ (5 * n)) := by
      intro i hi
      simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hi
      exact ⟨(h i hi.2).1, by omega⟩
    have e := ih hm
    have hd : x / 2 ^ (5 * n) = (x.testBit (5 * n)).toNat := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_div_two_pow]
      cases i with
      | zero => cases hb : x.testBit (5 * n) <;> simp [hb]
      | succ i =>
        have e1 : x.testBit (i + 1 + 5 * n) = false := by
          by_contra hc
          have := h _ (by simpa using hc); omega
        rw [e1]
        cases x.testBit (5 * n) <;> simp [Nat.testBit_succ]
    rw [pk_succ, ← hd]
    have e2 : pk n (fun j => (x.testBit (5 * j)).toNat) = x % 2 ^ (5 * n) := by
      conv_rhs => rw [e]
      refine pk_congr fun j hj => ?_
      rw [Nat.testBit_mod_two_pow]; simp [show 5 * j < 5 * n by omega]
    rw [e2]; exact (Nat.div_add_mod x _).symm
lemma isPk_and {n x y : ℕ} (hx : isPk n x) : isPk n (x &&& y) := fun i hi => hx i (by simp at hi; exact hi.1)
lemma isPk_or {n x y : ℕ} (hx : isPk n x) (hy : isPk n y) : isPk n (x ||| y) := fun i hi => by
  simp at hi; exact hi.elim (hx i) (hy i)
lemma fl_le (w : W) (j : ℕ) : fl w j ≤ 1 := by unfold fl; cases w.c.testBit (5 * j) <;> simp
lemma cnt_cons (w : W) (v : List W) (j : ℕ) : cnt (w :: v) j = fl w j + cnt v j := by simp [cnt]
lemma cnt_perm {v v' : List W} (h : v.Perm v') (j : ℕ) : cnt v j = cnt v' j := (h.map _).sum_eq
lemma WOk.pc {P : List ℕ} {w : W} (h : WOk P w) : isPk P.length w.c := by rw [h.ec]; exact isPk_or h.pa h.pb
lemma WOk.cst {P : List ℕ} {w : W} (h : WOk P w) {j : ℕ} (hj : j < P.length) (hf : w.c.testBit (5 * j) = true) :
    Cst (P.getD j 0) w.s := by
  rw [h.ec, Nat.testBit_or, Bool.or_eq_true] at hf
  exact hf.elim (fun h1 => Or.inl (h.ca j hj h1)) (fun h1 => Or.inr (h.cb j hj h1))
lemma lane_succ (w n : ℕ) (f : ℕ → ℕ) : lane w (n + 1) f = 2 ^ (w * n) * f n + lane w n f := by
  rw [lane, Finset.sum_range_succ, ← lane]; ring
lemma lane_congr {w n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) : lane w n f = lane w n g :=
  Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]
lemma lane_lt {w n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j < 2 ^ w) : lane w n f < 2 ^ (w * n) := by
  induction n with
  | zero => simp [lane]
  | succ n ih =>
    have h1 := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    rw [lane_succ, show w * (n + 1) = w * n + w by ring, pow_add]
    have : 2 ^ (w * n) * f n ≤ 2 ^ (w * n) * (2 ^ w - 1) := Nat.mul_le_mul_left _ (by omega)
    have e : 2 ^ (w * n) * 2 ^ w = 2 ^ (w * n) * (2 ^ w - 1) + 2 ^ (w * n) := by
      have : 0 < 2 ^ w := Nat.two_pow_pos w
      conv_lhs => rw [show 2 ^ w = (2 ^ w - 1) + 1 by omega]
      ring
    omega
lemma lane_add (w n : ℕ) (f g : ℕ → ℕ) : lane w n f + lane w n g = lane w n (fun j => f j + g j) := by
  simp [lane, ← Finset.sum_add_distrib, add_mul]
lemma lane_mul (w n q : ℕ) (f : ℕ → ℕ) : q * lane w n f = lane w n (fun j => q * f j) := by
  rw [lane, lane, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
lemma lane_and {w n : ℕ} {f g : ℕ → ℕ} (hf : ∀ j < n, f j < 2 ^ w) (hg : ∀ j < n, g j < 2 ^ w) :
    lane w n f &&& lane w n g = lane w n (fun j => f j &&& g j) := by
  induction n with
  | zero => simp [lane]
  | succ n ih =>
    have i1 := ih (fun j hj => hf j (by omega)) (fun j hj => hg j (by omega))
    have h1 : lane w n f < 2 ^ (w * n) := lane_lt fun j hj => hf j (by omega)
    have h2 : lane w n g < 2 ^ (w * n) := lane_lt fun j hj => hg j (by omega)
    have h3 : lane w n (fun j => f j &&& g j) < 2 ^ (w * n) := lane_lt fun j hj => lt_of_le_of_lt Nat.and_le_left (hf j (by omega))
    rw [lane_succ, lane_succ, lane_succ]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2, Nat.testBit_two_pow_mul_add _ h3]
    split_ifs with hi
    · rw [← Nat.testBit_and, i1]
    · rw [Nat.testBit_and]
lemma lane_mod {w n : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j ≤ 1) (hw : 5 * n + 6 ≤ w) : lane w n f % (2 ^ w - 32) = pk n f := by
  have h64 : 64 ≤ 2 ^ w := by
    calc 64 = 2 ^ 6 := rfl
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have base : 2 ^ w ≡ 32 [MOD 2 ^ w - 32] := by
    have : 2 ^ w = (2 ^ w - 32) + 32 := by omega
    conv_lhs => rw [this]
    exact Nat.add_modEq_left
  have key : ∀ n, lane w n f ≡ pk n f [MOD 2 ^ w - 32] := by
    intro n
    induction n with
    | zero => simp [lane, pk]; rfl
    | succ n ih =>
      rw [lane_succ, pk_succ]
      refine Nat.ModEq.add (Nat.ModEq.mul_right _ ?_) ih
      rw [pow_mul, pow_mul]
      exact base.pow n
  have hlt : pk n f < 2 ^ w - 32 := by
    have h1 : pk n f < 2 ^ (5 * n) := pk_lt fun j hj => lt_of_le_of_lt (hf j hj) (by norm_num)
    have h2 : 2 ^ (5 * n) ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  have := key n
  rw [Nat.ModEq, Nat.mod_eq_of_lt hlt] at this
  exact this
lemma lane_testBit {w : ℕ} {f : ℕ → ℕ} {i j : ℕ} (hi : i < w) : ∀ {n : ℕ}, (∀ j < n, f j < 2 ^ w) →
    (lane w n f).testBit (w * j + i) = (decide (j < n) && (f j).testBit i) := by
  intro n
  induction n with
  | zero => intro _; simp [lane]
  | succ n ih =>
    intro h
    have h1 : lane w n f < 2 ^ (w * n) := lane_lt fun j hj => h j (by omega)
    rw [lane_succ, Nat.testBit_two_pow_mul_add _ h1]
    rcases lt_trichotomy j n with hj | rfl | hj
    · have : w * j + i < w * n := by
        have : w * (j + 1) ≤ w * n := Nat.mul_le_mul_left _ hj
        have e : w * (j + 1) = w * j + w := by ring
        omega
      rw [ite_eq_left this, ih fun j hj => h j (by omega)]
      simp [hj, show j < n + 1 by omega]
    · rw [ite_eq_right (by omega), show w * j + i - w * j = i by omega]; simp
    · have e0 : ¬ w * j + i < w * n := by
        have : w * n ≤ w * j := Nat.mul_le_mul_left _ (by omega)
        omega
      have hlt : f n < 2 ^ w := h n (by omega)
      have : w ≤ w * j + i - w * n := by
        have : w * (n + 1) ≤ w * j := Nat.mul_le_mul_left _ hj
        have e : w * (n + 1) = w * n + w := by ring
        omega
      rw [ite_eq_right e0, Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) this))]
      simp [show ¬ j < n + 1 by omega]
lemma laneL_eq (w : ℕ) (L : List ℕ) : laneL w L = lane w L.length (fun j => L.getD j 0) := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    change (laneL w L) <<< w + d = _
    rw [ih, Nat.shiftLeft_eq, List.length_cons, lane, lane, Finset.sum_range_succ', Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [List.getD_cons_succ]; rw [mul_assoc, ← pow_add]; congr 2
    · simp
lemma laneL_rep (w n x : ℕ) : laneL w (List.replicate n x) = lane w n (fun _ => x) := by
  rw [laneL_eq, List.length_replicate]
  refine lane_congr fun j hj => ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; simp [hj]
lemma fb_le (x j : ℕ) : fb x j ≤ 1 := by unfold fb; cases x.testBit (5 * j) <;> simp
lemma fb_pk {n x : ℕ} (h : isPk n x) : x = pk n (fb x) := pk_of h
lemma pk_bit {n : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j ≤ 1) (j : ℕ) : (pk n f).testBit (5 * j) = (decide (j < n) && decide (f j = 1)) := by
  have h := lane_testBit (w := 5) (f := f) (i := 0) (j := j) (by norm_num) (n := n) fun j hj => lt_of_le_of_lt (hf j hj) (by norm_num)
  rw [add_zero] at h
  change (lane 5 n f).testBit (5 * j) = _
  rw [h]
  by_cases hj : j < n
  · have := hf j hj
    simp only [hj, decide_true, Bool.true_and]
    generalize f j = x at *
    interval_cases x <;> rfl
  · simp [hj]
lemma pk_isPk {n : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j ≤ 1) : isPk n (pk n f) := by
  intro i hi
  have hlt : pk n f < 2 ^ (5 * n) := pk_lt fun j hj => lt_of_le_of_lt (hf j hj) (by norm_num)
  have h5 := Nat.mod_lt i (show 0 < 5 by norm_num)
  have e : 5 * (i / 5) + i % 5 = i := Nat.div_add_mod i 5
  have h := lane_testBit (w := 5) (f := f) (i := i % 5) (j := i / 5) h5 (n := n) fun j hj => lt_of_le_of_lt (hf j hj) (by norm_num)
  rw [e] at h
  change (lane 5 n f).testBit i = true at hi
  rw [h, Bool.and_eq_true, decide_eq_true_eq] at hi
  refine ⟨?_, hi.1⟩
  by_contra hne
  have := hf _ hi.1
  have hx := hi.2
  generalize f (i / 5) = x at *
  interval_cases x
  · simp at hx
  · exact hne (Nat.testBit_one_eq_true_iff_self_eq_zero.1 hx)
lemma fb_of_pk {n : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j ≤ 1) {j : ℕ} (hj : j < n) : fb (pk n f) j = f j := by
  unfold fb; rw [pk_bit hf]
  have := hf j hj
  simp only [hj, decide_true, Bool.true_and]
  generalize f j = x at *
  interval_cases x <;> rfl
lemma fb_one {x j : ℕ} : fb x j = 1 ↔ x.testBit (5 * j) = true := by unfold fb; cases x.testBit (5 * j) <;> simp
lemma MU_land {n : ℕ} {f d : ℕ → ℕ} (hf : ∀ j < n, f j ≤ 1) (hd : ∀ j < n, d j < 32) :
    Nat.land (MU (pk n f)) (pk n d) = pk n (fun j => f j * d j) := by
  change (31 * lane 5 n f) &&& lane 5 n d = lane 5 n _
  rw [lane_mul, lane_and]
  · refine lane_congr fun j hj => ?_
    have h1 := hf j hj; have h2 := hd j hj
    generalize f j = x at *
    generalize d j = y at *
    interval_cases x
    · simp
    · rw [mul_one, one_mul]
      interval_cases y <;> rfl
  · intro j hj; have := hf j hj; omega
  · intro j hj; exact hd j hj
lemma shr4 (n : ℕ) : Nat.shiftRight (pk n (fun _ => 16)) 4 = pk n (fun _ => 1) := by
  change pk n (fun _ => 16) >>> 4 = _
  have : pk n (fun _ => 16) = 16 * pk n (fun _ => 1) := by
    change lane 5 n _ = 16 * lane 5 n _; rw [lane_mul]
  rw [this, Nat.shiftRight_eq_div_pow]; norm_num
lemma zflG_spec {N np q nc : ℕ} {f : ℕ → ℕ} (hf : ∀ j < 16, f j < 2 ^ (2 * N)) (hnp : np = lane (WL N) 16 f) (hw : 86 ≤ 2 * N + 1) {j : ℕ}
    (h : (zflG N np q nc).testBit (5 * j) = true) : j < 16 ∧ q &&& f j = 0 ∧ nc.testBit (5 * j) = true := by
  have hWL : WL N = 2 * N + 1 := rfl
  have hFM : FM2 N = 2 ^ (2 * N) - 1 := rfl
  have pw : 2 ^ (WL N) = 2 * 2 ^ (2 * N) := by rw [hWL, pow_succ']
  have hpos : 0 < 2 ^ (2 * N) := Nat.two_pow_pos _
  set q' := q &&& (FM2 N) with hq'
  have hq'lt : q' < 2 ^ (2 * N) := lt_of_le_of_lt Nat.and_le_right (by rw [hFM]; omega)
  have hqf : ∀ j < 16, q' &&& f j = q &&& f j := by
    intro j hj
    apply Nat.eq_of_testBit_eq; intro i
    simp only [hq', hFM, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < 2 * N
    · simp [hi]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf j hj) (Nat.pow_le_pow_right (by norm_num) (by omega)))]; simp
  let b : ℕ → ℕ := fun j => if q &&& f j = 0 then 0 else 1
  have hb : ∀ j, b j ≤ 1 := fun j => by simp only [b]; split_ifs <;> simp
  have e1 : Nat.land (Nat.mul (Nat.land q (FM2 N)) (R16 N)) np = lane (WL N) 16 (fun j => q &&& f j) := by
    change (q' * (R16 N)) &&& np = _
    rw [R16, laneL_rep, lane_mul, hnp, lane_and]
    · refine lane_congr fun j hj => ?_
      rw [mul_one, hqf j hj]
    · intro j hj; rw [mul_one, pw]; omega
    · intro j hj; have := hf j hj; rw [pw]; omega
  have e2 : Nat.land (Nat.add (Nat.land (Nat.mul (Nat.land q (FM2 N)) (R16 N)) np) (MM16 N)) (GG16 N) = lane (WL N) 16 (fun j => 2 ^ (2 * N) * b j) := by
    rw [e1]
    change (lane (WL N) 16 _ + (MM16 N)) &&& (GG16 N) = _
    have hlt : ∀ j < 16, q &&& f j < 2 ^ (2 * N) := fun j hj => lt_of_le_of_lt Nat.and_le_right (hf j hj)
    rw [MM16, GG16, laneL_rep, laneL_rep, lane_add, lane_and]
    · refine lane_congr fun j hj => ?_
      have h1 := hlt j hj
      change (_ + (2 ^ (2 * N) - 1)) &&& 2 ^ (2 * N) = 2 ^ (2 * N) * b j
      generalize hx : q &&& f j = x at *
      have hbx : b j = if x = 0 then 0 else 1 := by simp only [b, hx]
      rw [hbx]
      split_ifs with h0
      · subst h0
        apply Nat.eq_of_testBit_eq; intro i
        rw [Nat.testBit_and, zero_add, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow]
        by_cases hi : 2 * N = i <;> simp [hi]
      · have e : x + (2 ^ (2 * N) - 1) = 2 ^ (2 * N) * 1 + (x - 1) := by omega
        rw [e]
        apply Nat.eq_of_testBit_eq; intro i
        rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ (show x - 1 < 2 ^ (2 * N) by omega), Nat.testBit_two_pow, mul_one, Nat.testBit_two_pow]
        by_cases hi : 2 * N = i
        · subst hi; simp
        · simp [hi]
    · intro j hj; have := hlt j hj
      change _ + (2 ^ (2 * N) - 1) < _; rw [pw]; omega
    · intro j hj
      change 2 ^ (2 * N) < _; rw [pw]; omega
  have e3 : Nat.mod (Nat.shiftRight (Nat.land (Nat.add (Nat.land (Nat.mul (Nat.land q (FM2 N)) (R16 N)) np) (MM16 N)) (GG16 N)) (Nat.mul 2 N)) (MD16 N) = pk 16 b := by
    rw [e2]
    change (lane (WL N) 16 (fun j => 2 ^ (2 * N) * b j) >>> (2 * N)) % (2 ^ (WL N) - 32) = _
    rw [← lane_mul, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ hpos]
    exact lane_mod (fun j _ => hb j) (by rw [hWL]; omega)
  unfold zflG at h
  rw [e3] at h
  change ((U16 - pk 16 b) &&& nc).testBit (5 * j) = true at h
  have e4 : U16 - pk 16 b = pk 16 (fun j => 1 - b j) := by
    rw [U16, laneL_rep]
    change pk 16 (fun _ => 1) - pk 16 b = _
    exact pk_sub fun j _ => hb j
  rw [e4, Nat.testBit_and, pk_bit (fun j _ => by omega), Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  refine ⟨h.1.1, ?_, h.2⟩
  have := h.1.2
  by_contra hne
  simp [b, hne] at this
lemma zfl_spec {np q nc : ℕ} {f : ℕ → ℕ} (hf : ∀ j < 16, f j < 2 ^ (2 * NN)) (hnp : np = lane (WL NN) 16 f) (hw : 86 ≤ 2 * NN + 1) {j : ℕ}
    (h : (zfl np q nc).testBit (5 * j) = true) : j < 16 ∧ q &&& f j = 0 ∧ nc.testBit (5 * j) = true := zflG_spec hf hnp hw h
lemma cnt_card {P : List ℕ} {v : List W} {S : Finset ℕ} (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w) {j : ℕ} (hj : j < P.length) :
    cnt v j ≤ (S.filter (Cst (P.getD j 0))).card := by
  have e : cnt v j = (v.filter (fun w => w.c.testBit (5 * j))).length := by
    clear hr hw
    induction v with
    | nil => rfl
    | cons w v ih =>
      rw [cnt_cons, ih, List.filter_cons, fl]
      cases w.c.testBit (5 * j) <;> simp; omega
  rw [e, ← List.length_map W.s, ← List.toFinset_card_of_nodup (hr.1.sublist (List.filter_sublist.map _))]
  apply Finset.card_le_card
  intro x hx
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hx
  obtain ⟨w, ⟨h1, h2⟩, rfl⟩ := hx
  rw [Finset.mem_filter]
  exact ⟨hr.mem.2 ⟨w, h1, rfl⟩, (hw w h1).cst hj h2⟩
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma cnt_le {k k' t : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ} {D : ℕ → ℕ → ℕ} (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w)
    (hc : ∀ j < P.length, Acc (P.getD j 0) T k (b j) (D j) S) (hm : Min R m T k' t S) (hk : k' ≤ k) : ∀ j < P.length, cnt v j ≤ b j := by
  intro j hj
  obtain ⟨p1, p2, p3⟩ := X.hP j hj
  exact (cnt_card hr hw hj).trans ((hc j hj).const p1 p2 p3 hm hk)
lemma guard_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hr : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    Nat.beq (Nat.land z g) g = true := by
  obtain ⟨b, D, hb, hc, _, _, hz⟩ := hr.bud
  have hle := cnt_le X hr.rep hr.wok hc hm hk
  rw [nl, hz, X.hg, pk_guard]; · simp
  intro j hj
  have := hb j hj; have := hle j hj; omega
lemma child_sound {f : ℕ → List W → Bool} {z t k k' : ℕ} {r : List W} {S : Finset ℕ} {kb : Bool}
    {mk : (List W → Bool) → Bool} (hmk : ∀ h, mk h = h r) (hkb : kb = false)
    (hr : StOk P T l k z r S) (hm : Min R m T k' t S) (hk : k' ≤ k) (h : child f g kb mk z = false) : f z r = false := by
  subst hkb
  simp only [child, bR, st_eq, guard_ok X hr hm hk, cond_true, cond_false, hmk] at h
  exact h
end sound
lemma StOk.start {P : List ℕ} {T l K : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ} (hrep : Rep v S) (hwok : ∀ w ∈ v, WOk P w) (hgood : ∀ w ∈ v, Good l w.s)
    (hK : K ≤ 15) (hb : ∀ j < P.length, b j ≤ 15) (hd : ∀ w ∈ v, w.d = 0) (hA : ∀ j < P.length, Acc (P.getD j 0) T K (b j) (fun _ => 0) S) :
    StOk P T l K (pk P.length (fun j => 16 + b j - cnt v j)) v S := by
  refine ⟨hrep, hwok, hgood, b, fun _ _ => 0, hb, hA, fun w hw => ?_, fun j _ => by simpa using hK, rfl⟩
  rw [hd w hw]; simp [pk]
lemma rm_eq (x y : ℕ) (v : List W) : ∀ h, rm x y v h = h (v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y))) := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (rm x y v (fun r => h (w :: r)))
      (rm x y v h) (Nat.beq w.s y)) (rm x y v h) (Nat.beq w.s x) : Bool) = _
    rw [bR, bR, ih, ih, List.filter_cons]
    cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> simp
lemma ins_spec (o : W) (v : List W) (hv : ∀ w ∈ v, w.s ≠ o.s) : ∃ r : List W, r.Perm (o :: v) ∧ ∀ h, ins o v h = h r := by
  induction v with
  | nil => exact ⟨[o], List.Perm.refl _, fun h => rfl⟩
  | cons w v ih =>
    obtain ⟨r, hp, hr⟩ := ih fun w' hw' => hv w' (by simp [hw'])
    have e : ∀ h, ins o (w :: v) h = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then false else h (o :: w :: v)) else ins o v (fun r => h (w :: r)) := by
      intro h
      change (Bool.rec (motive := fun _ => Bool) (ins o v (fun r => h (w :: r)))
        (Bool.rec (motive := fun _ => Bool) (h (o :: w :: v)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s) : Bool) = _
      rw [bR, bR]
    cases hb : Nat.ble w.s o.s with
    | true =>
      refine ⟨o :: w :: v, List.Perm.refl _, fun h => ?_⟩
      have : Nat.beq o.s w.s = false := Bool.eq_false_iff.2 fun h => hv w (by simp) (Nat.eq_of_beq_eq_true h).symm
      rw [e, hb, this]; rfl
    | false =>
      refine ⟨w :: r, (List.Perm.cons w hp).trans (List.Perm.swap _ _ _), fun h => ?_⟩
      rw [e, hb, hr]; rfl
lemma filter_perm {v : List W} (hv : (v.map W.s).Nodup) {a : W} (ha : a ∈ v) :
    (a :: v.filter (fun w => !Nat.beq w.s a.s)).Perm v := by
  induction v with
  | nil => simp at ha
  | cons w v ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hv
    have hne : ∀ x y : ℕ, x ≠ y → Nat.beq x y = false := fun x y h => Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · have : v.filter (fun w => !Nat.beq w.s a.s) = v := by
        rw [List.filter_eq_self]
        intro w' hw'
        rw [hne _ _ (hv.1 w' hw')]; rfl
      rw [List.filter_cons, this]; simp
    · rw [List.filter_cons, hne w.s a.s (fun e => hv.1 a ha e.symm)]
      simp only [Bool.not_false, if_true]
      exact (List.Perm.swap _ _ _).trans ((ih hv.2 ha).cons w)
lemma filter2 {v : List W} {x y : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y)) =
    (v.filter (fun w => !Nat.beq w.s x)).filter (fun w => !Nat.beq w.s y) := by
  rw [List.filter_filter]; congr 1; funext w; cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> rfl
lemma filter1 {v : List W} {x : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s x)) = v.filter (fun w => !Nat.beq w.s x) := by
  congr 1; funext w; cases Nat.beq w.s x <;> rfl
lemma Shape.cnt {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) (j : ℕ) :
    cnt r j + (bif ka then 0 else fl a j) + (bif kc then 0 else fl c j) = fl o j + cnt v j := by
  cases h with
  | ff h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tf h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | ft h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tt h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
lemma Shape.mem {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {w : W} (hw : w ∈ r) : w = o ∨ w ∈ v := by
  have : w ∈ o :: v := by
    cases h with
    | ff h => exact h.subset (by simp [hw])
    | tf h => exact h.subset (by simp [hw])
    | ft h => exact h.subset (by simp [hw])
    | tt h => exact h.subset (by simp [hw])
  simpa using this
lemma Shape.len {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) :
    r.length + (bif ka then 0 else 1) + (bif kc then 0 else 1) = v.length + 1 := by
  cases h with
  | ff h => have := h.length_eq; simp at this ⊢; omega
  | tf h => have := h.length_eq; simp at this ⊢; omega
  | ft h => have := h.length_eq; simp at this ⊢; omega
  | tt h => have := h.length_eq; simp at this ⊢; omega
lemma Shape.rep {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {S S' : Finset ℕ} (hr : Rep v S)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) (ho : o.s ∉ S)
    (hS : ∀ x, x ∈ S' ↔ x = o.s ∨ (x ∈ S ∧ (x = a.s → ka = true) ∧ (x = c.s → kc = true))) : Rep r S' := by
  have hov : ((o :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ho ?_, hr.1⟩
    rw [← hr.2]; simpa using hm
  have hvS : ∀ x, x ∈ v.map W.s ↔ x ∈ S := fun x => by rw [← hr.2]; simp
  have hm : ∀ x, x ∈ (o :: v).map W.s ↔ x = o.s ∨ x ∈ S := fun x => by simp only [List.map_cons, List.mem_cons, hvS]
  have haS := (hvS a.s).1 (List.mem_map_of_mem ha)
  have hcS := (hvS c.s).1 (List.mem_map_of_mem hc)
  have hao : a.s ≠ o.s := fun e => ho (e ▸ haS)
  have hco : c.s ≠ o.s := fun e => ho (e ▸ hcS)
  cases h with
  | ff h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hn
    refine ⟨hn.2.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n1 : x ≠ a.s := fun e => hn.1.2 (e ▸ h1)
      have n2 : x ≠ c.s := fun e => hn.2.1 (e ▸ h1)
      rcases hx.1 (Or.inr (Or.inr h1)) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n1, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · rcases hx.2 (Or.inl e) with e' | e' | e'
        · exact absurd (e'.symm.trans e) hao
        · exact absurd (e'.symm.trans e) hco
        · exact e'
      · rcases hx.2 (Or.inr e) with e' | e' | e'
        · exact absurd (f1 e') (by simp)
        · exact absurd (f2 e') (by simp)
        · exact e'
  | tf h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ c.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun _ => rfl, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hco (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f2 e'
  | ft h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ a.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n2, fun _ => rfl⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hao (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  | tt h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    refine ⟨hn, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx
    rw [List.mem_toFinset, hS, hx]; simp
lemma shape_all {o a c : W} {v r : List W} (ho : ∀ w ∈ v, w.s ≠ o.s) (hp : r.Perm (o :: v)) (hv : (v.map W.s).Nodup)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) :
    Shape o a c v false false (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s c.s))) ∧
    Shape o a c v true false (r.filter (fun w => !(Nat.beq w.s c.s || Nat.beq w.s c.s))) ∧
    Shape o a c v false true (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))) ∧ Shape o a c v true true r := by
  have hnd : (r.map W.s).Nodup := by
    refine (hp.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => ho w hw, hv⟩
  have har : a ∈ r := hp.symm.subset (by simp [ha])
  have hcr : c ∈ r := hp.symm.subset (by simp [hc])
  refine ⟨.ff ?_, .tf ?_, .ft ?_, .tt hp⟩
  · rw [filter2]
    have h1 := filter_perm hnd har
    have h2 : c ∈ r.filter (fun w => !Nat.beq w.s a.s) := by
      rw [List.mem_filter]; refine ⟨hcr, ?_⟩
      rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
    exact ((filter_perm (hnd.sublist (List.filter_sublist.map _)) h2).cons a).trans (h1.trans hp)
  · rw [filter1]; exact (filter_perm hnd hcr).trans hp
  · rw [filter1]; exact (filter_perm hnd har).trans hp
lemma cnt_two {v : List W} {a c : W} (ha : a ∈ v) (hc : c ∈ v) (hv : (v.map W.s).Nodup) (hac : a.s ≠ c.s) (j : ℕ) :
    fl a j + fl c j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  have h2 : c ∈ v.filter (fun w => !Nat.beq w.s a.s) := by
    rw [List.mem_filter]; refine ⟨hc, ?_⟩
    rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
  have h3 := cnt_perm (filter_perm (hv.sublist (List.filter_sublist.map _)) h2) j
  simp only [cnt_cons] at h1 h3; omega
lemma cnt_one {v : List W} {a : W} (ha : a ∈ v) (hv : (v.map W.s).Nodup) (j : ℕ) : fl a j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  simp only [cnt_cons] at h1; omega
lemma opW_s (d : Bool) (a c : W) : (opW d a c).s = op d a.s c.s := by cases d <;> rfl
lemma opW_ok {P : List ℕ} {a c : W} (d : Bool) (ha : WOk P a) (hc : WOk P c) : WOk P (opW d a c) := by
  cases d
  · refine ⟨isPk_or ha.pa hc.pa, isPk_and ha.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a ||| c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.ca j hj h]; simp [op]
      · rw [hc.ca j hj h]; simp [op]
    · have h : (a.b &&& c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.cb j hj h.1, hc.cb j hj h.2, op_self]
  · refine ⟨isPk_and ha.pa, isPk_or ha.pb hc.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a &&& c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.ca j hj h.1, hc.ca j hj h.2, op_self]
    · have h : (a.b ||| c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
      · rw [hc.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_good {l x y : ℕ} (d : Bool) (hx : Good l x) (hy : Good l y) : Good l (op d x y) := by
  refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
  · rw [op_bit, op_bit, hx.1 i j h h1 h2, hy.1 i j h h1 h2]
  · rw [op_bit, op_bit, hx.2 i j h h1 h2, hy.2 i j h h1 h2]
lemma fl_and {P : List ℕ} {a c : W} (ha : WOk P a) : a.c &&& c.c = pk P.length (fun j => fl a j * fl c j) := by
  rw [pk_of (isPk_and (y := c.c) ha.pc)]
  refine pk_congr fun j _ => ?_
  rw [Nat.testBit_and]; unfold fl; cases a.c.testBit (5 * j) <;> cases c.c.testBit (5 * j) <;> rfl
lemma fl_pk {P : List ℕ} {a : W} (ha : WOk P a) : a.c = pk P.length (fl a) := pk_of ha.pc
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma drop_ok {k' t : ℕ} {v : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {i : ℕ} (hr : Rep v S)
    (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S')
    (ha : a ∈ v) (hk : a.s ∉ S')
    (hu : (Nat.land (sp (pos' t) l a.s) (wst (pos' t) l v)).testBit i = true) :
    bif d' then c.s.testBit (NN + i) = false else c.s.testBit i = true := by
  obtain ⟨hli, u1, u2⟩ := uq_of hr ha hu
  obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
  obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
  have hac : c.s ≠ a.s := hb.1.symm
  have hsub := hb.sub.2.2 hw
  rw [Finset.mem_insert] at hsub
  have hg : sepb NN (pos' t) (op d' a.s c.s) i = true := by
    rcases hsub with rfl | h
    · exact hs
    · have := u2 w h (fun e => hk (e ▸ hw))
      rw [this] at hs; simp at hs
  have hcn := u2 c.s hb.sub.2.1 hac
  revert hg hcn u1
  unfold sepb; simp only [op_bit]
  cases pos' t <;> cases d' <;> cases a.s.testBit i <;> cases a.s.testBit (NN + i) <;> cases c.s.testBit i <;>
    cases c.s.testBit (NN + i) <;> simp
end sound
lemma upd_s (sa da sc dc : ℕ) (w : W) : (upd sa da sc dc w).s = w.s := by
  unfold upd; cases Nat.beq w.s sa <;> cases Nat.beq w.s sc <;> rfl
lemma upd_c (sa da sc dc : ℕ) (w : W) : (upd sa da sc dc w).c = w.c := by
  unfold upd; cases Nat.beq w.s sa <;> cases Nat.beq w.s sc <;> rfl
lemma upd_r (sa da sc dc : ℕ) (w : W) : (upd sa da sc dc w).r = w.r := by
  unfold upd; cases Nat.beq w.s sa <;> cases Nat.beq w.s sc <;> rfl
lemma fl_upd (sa da sc dc : ℕ) (w : W) (j : ℕ) : fl (upd sa da sc dc w) j = fl w j := by unfold fl; rw [upd_c]
lemma WOk.upd {P : List ℕ} {w : W} (h : WOk P w) (sa da sc dc : ℕ) : WOk P (upd sa da sc dc w) := by
  unfold L_meta_17357.upd
  cases Nat.beq w.s sa <;> cases Nat.beq w.s sc
  · exact h
  · exact ⟨h.pa, h.pb, h.ec, h.ca, h.cb⟩
  · exact ⟨h.pa, h.pb, h.ec, h.ca, h.cb⟩
  · exact ⟨h.pa, h.pb, h.ec, h.ca, h.cb⟩
lemma map_upd_s (sa da sc dc : ℕ) (v : List W) : (v.map (upd sa da sc dc)).map W.s = v.map W.s := by
  rw [List.map_map]; exact List.map_congr_left fun w _ => upd_s _ _ _ _ w
lemma cnt_upd (sa da sc dc : ℕ) (v : List W) (j : ℕ) : cnt (v.map (upd sa da sc dc)) j = cnt v j := by
  unfold cnt; rw [List.map_map]; congr 1; exact List.map_congr_left fun w _ => fl_upd _ _ _ _ w j
lemma Rep.upd {v : List W} {S : Finset ℕ} (h : Rep v S) (sa da sc dc : ℕ) : Rep (v.map (L_meta_17357.upd sa da sc dc)) S := by
  unfold Rep; rw [map_upd_s]; exact h
lemma rmk_eq (sa : ℕ) (ka : Bool) (da sc : ℕ) (kc : Bool) (dc : ℕ) (v : List W) : ∀ h, rmk sa ka da sc kc dc v h = h ((v.filter (kp sa ka sc kc)).map (upd sa da sc dc)) := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    obtain ⟨ws, wa, wb, wc, wr, wd'⟩ := w
    change (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (rmk sa ka da sc kc dc v (fun r => h (⟨ws, wa, wb, wc, wr, wd'⟩ :: r))) (Bool.rec (motive := fun _ => Bool) (rmk sa ka da sc kc dc v h)
        (st dc fun d => rmk sa ka da sc kc dc v (fun r => h (⟨ws, wa, wb, wc, wr, d⟩ :: r))) kc) (Nat.beq ws sc))
      (Bool.rec (motive := fun _ => Bool) (rmk sa ka da sc kc dc v h) (st da fun d => rmk sa ka da sc kc dc v (fun r => h (⟨ws, wa, wb, wc, wr, d⟩ :: r))) ka) (Nat.beq ws sa) : Bool) = _
    simp only [bR, st_eq, ih]
    rw [List.filter_cons]
    unfold kp
    cases h1 : Nat.beq ws sa <;> cases h2 : Nat.beq ws sc <;> cases ka <;> cases kc <;> simp [upd, h1, h2, wd]
lemma beq_f {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
lemma beq_t (x : ℕ) : Nat.beq x x = true := Nat.beq_refl x
lemma shape_upd {o a c : W} {v r0 : List W} (da dc : ℕ) (ho : ∀ w ∈ v, w.s ≠ o.s) (hp : r0.Perm (o :: v)) (hv : (v.map W.s).Nodup)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) (ka kc : Bool) :
    Shape o (upd a.s da c.s dc a) (upd a.s da c.s dc c) (v.map (upd a.s da c.s dc)) ka kc ((r0.filter (kp a.s ka c.s kc)).map (upd a.s da c.s dc)) := by
  set u := upd a.s da c.s dc with hu
  have us : ∀ w, (u w).s = w.s := fun w => upd_s _ _ _ _ w
  have uo : u o = o := by
    rw [hu]; unfold upd; rw [beq_f (ho a ha).symm, beq_f (ho c hc).symm]; rfl
  have hp' : (r0.map u).Perm (o :: v.map u) := by
    have := hp.map u; rw [List.map_cons, uo] at this; exact this
  have hv' : ((v.map u).map W.s).Nodup := by rw [hu, map_upd_s]; exact hv
  have ho' : ∀ w ∈ v.map u, w.s ≠ o.s := by
    intro w hw
    obtain ⟨w0, h0, rfl⟩ := List.mem_map.1 hw
    rw [us]; exact ho w0 h0
  obtain ⟨s1, s2, s3, s4⟩ := shape_all ho' hp' hv' (List.mem_map_of_mem ha) (List.mem_map_of_mem hc) (by rw [us, us]; exact hac)
  simp only [us, List.filter_map] at s1 s2 s3
  have filt : ∀ q : W → Bool, (∀ w, kp a.s ka c.s kc w = q (u w)) → r0.filter (kp a.s ka c.s kc) = r0.filter (q ∘ u) := by
    intro q hq; congr 1; funext w; exact hq w
  cases ka <;> cases kc
  · rw [filt _ fun w => ?_]
    · exact s1
    · simp only [us, kp]; cases Nat.beq w.s a.s <;> cases Nat.beq w.s c.s <;> rfl
  · rw [filt _ fun w => ?_]
    · exact s3
    · simp only [us, kp]; cases Nat.beq w.s a.s <;> cases Nat.beq w.s c.s <;> rfl
  · rw [filt _ fun w => ?_]
    · exact s2
    · simp only [us, kp]
      by_cases h1 : w.s = a.s
      · rw [h1, beq_t, beq_f hac]; rfl
      · rw [beq_f h1]; cases Nat.beq w.s c.s <;> rfl
  · have : r0.filter (kp a.s true c.s true) = r0 := by
      rw [List.filter_eq_self]; intro w _
      unfold kp; cases Nat.beq w.s a.s <;> cases Nat.beq w.s c.s <;> rfl
    rw [this]; exact s4
lemma num1 {b cv cr fa fc fo ea ec da dc : ℕ} {ka kc : Bool} (hfa : fa ≤ 1) (hfc : fc ≤ 1) (hfo : fo ≤ 1) (h2 : fa = 1 → fc = 1 → fo = 1) (h3 : fo = 1 → fa = 1 ∨ fc = 1)
    (he : ea + ec + max fa (max fc fo) ≤ 1) (hb : b ≤ 15) (hcv : cv ≤ b) (hcnt : cr + (bif ka then 0 else fa) + (bif kc then 0 else fc) = fo + cv)
    (hd : (kdOf fo (ea + (fc - fc * fo)) (ec + (fa - fa * fo))).del (if ka then 0 else da) (if kc then 0 else dc) + cr ≤ b) :
    (fo ≤ 16 + b - cv + fa * fc ∧ 16 ≤ 16 + b - cv + fa * fc - fo ∧ 16 + b - cv + fa * fc - fo < 32 ∧ ea + ec ≤ 16 + b - cv + fa * fc - fo ∧
      16 ≤ 16 + b - cv + fa * fc - fo - (ea + ec) ∧ 16 + b - cv + fa * fc - fo - (ea + ec) < 32) ∧
    (bif ka then fa else (fo + (ec + (fa - fa * fo))) * da) ≤ 16 + b - cv + fa * fc - fo - (ea + ec) ∧
    (bif kc then fc else (fo + (ea + (fc - fc * fo))) * dc) ≤ 16 + b - cv + fa * fc - fo - (ea + ec) - (bif ka then fa else (fo + (ec + (fa - fa * fo))) * da) ∧
    16 + b - cv + fa * fc - fo - (ea + ec) - (bif ka then fa else (fo + (ec + (fa - fa * fo))) * da) - (bif kc then fc else (fo + (ea + (fc - fc * fo))) * dc) =
      16 + (b - (kdOf fo (ea + (fc - fc * fo)) (ec + (fa - fa * fo))).del (if ka then 0 else da) (if kc then 0 else dc)) - cr := by
  have hea : ea ≤ 1 := by omega
  have hec : ec ≤ 1 := by omega
  interval_cases fa <;> interval_cases fc <;> interval_cases fo <;> simp at h2 h3 he <;> interval_cases ea <;> interval_cases ec <;> simp at he <;>
    cases ka <;> cases kc <;> simp [kdOf, Kd.del] at hd hcnt ⊢ <;> omega
lemma num2 {fa fc fo ea ec da dc : ℕ} {ka kc : Bool} (hfa : fa ≤ 1) (hfc : fc ≤ 1) (hfo : fo ≤ 1) (h2 : fa = 1 → fc = 1 → fo = 1)
    (he : ea + ec + max fa (max fc fo) ≤ 1) :
    (ea + (fc - fc * fo) ≤ 1 ∧ ec + (fa - fa * fo) ≤ 1 ∧ fo + (ea + (fc - fc * fo)) + (ec + (fa - fa * fo)) ≤ 1) ∧
    (1 - fo - (ea + (fc - fc * fo)) - (ec + (fa - fa * fo))) + (bif ka then 0 else ((1 - fo - (ea + (fc - fc * fo)) - (ec + (fa - fa * fo))) + (ea + (fc - fc * fo))) * da) +
      (bif kc then 0 else ((1 - fo - (ea + (fc - fc * fo)) - (ec + (fa - fa * fo))) + (ec + (fa - fa * fo))) * dc) =
      (kdOf fo (ea + (fc - fc * fo)) (ec + (fa - fa * fo))).out (if ka then 0 else da) (if kc then 0 else dc) ∧
    (fo + (ec + (fa - fa * fo))) * da = (kdOf fo (ea + (fc - fc * fo)) (ec + (fa - fa * fo))).kpa da ∧
    (fo + (ea + (fc - fc * fo))) * dc = (kdOf fo (ea + (fc - fc * fo)) (ec + (fa - fa * fo))).kpc dc := by
  have hea : ea ≤ 1 := by omega
  have hec : ec ≤ 1 := by omega
  interval_cases fa <;> interval_cases fc <;> interval_cases fo <;> simp at h2 he <;> interval_cases ea <;> interval_cases ec <;> simp at he <;>
    cases ka <;> cases kc <;> simp [kdOf, Kd.out, Kd.kpa, Kd.kpc]
lemma opW_flags {P : List ℕ} {a c : W} (d : Bool) (ha : WOk P a) (hc : WOk P c) (j : ℕ) :
    (fl a j = 1 → fl c j = 1 → fl (opW d a c) j = 1) ∧ (fl (opW d a c) j = 1 → fl a j = 1 ∨ fl c j = 1) := by
  unfold fl
  rw [ha.ec, hc.ec]
  cases d <;> simp only [opW, cond_true, cond_false, Nat.testBit_or, Nat.testBit_and] <;>
    cases a.a.testBit (5 * j) <;> cases a.b.testBit (5 * j) <;> cases c.a.testBit (5 * j) <;> cases c.b.testBit (5 * j) <;> simp
lemma pass_ok {P : List ℕ} {a c : W} (d : Bool) (ha : WOk P a) (hc : WOk P c) {j : ℕ} (hj : j < P.length) (h1 : fl c j = 1) (h0 : fl (opW d a c) j = 0) :
    op d a.s c.s &&& P.getD j 0 = a.s &&& P.getD j 0 := by
  have e1 : c.c.testBit (5 * j) = true := by unfold fl at h1; cases h : c.c.testBit (5 * j) <;> simp_all
  have e0 : (opW d a c).c.testBit (5 * j) = false := by unfold fl at h0; cases h : (opW d a c).c.testBit (5 * j) <;> simp_all
  rw [hc.ec, Nat.testBit_or, Bool.or_eq_true] at e1
  cases d
  · simp only [opW, cond_false, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff] at e0
    have hb := e1.resolve_left (by simp [e0.1.2])
    rw [and_op, hc.cb j hj hb]
    apply Nat.eq_of_testBit_eq; intro i; simp [op]
  · simp only [opW, cond_true, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff] at e0
    have hb := e1.resolve_right (by simp [e0.2.2])
    rw [and_op, hc.ca j hj hb]
    apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma opW_symm (d : Bool) (a c : W) : (opW d a c).c = (opW d c a).c := by
  cases d
  · change (a.a ||| c.a) ||| (a.b &&& c.b) = (c.a ||| a.a) ||| (c.b &&& a.b); rw [Nat.or_comm a.a, Nat.and_comm a.b]
  · change (a.a &&& c.a) ||| (a.b ||| c.b) = (c.a &&& a.a) ||| (c.b ||| a.b); rw [Nat.and_comm a.a, Nat.or_comm a.b]
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma bi_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {ka kc : Bool} {eA eC w fA fC fN dn : ℕ}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hb : Bi R d' a.s c.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v) (hka : ka = decide (a.s ∈ S')) (hkc : kc = decide (c.s ∈ S'))
    (hEA : isPk P.length eA) (hEC : isPk P.length eC)
    (he : ∀ j < P.length, fb eA j + fb eC j + max (fl a j) (max (fl c j) (fl (opW d' a c) j)) ≤ 1)
    (hAo : ∀ j < P.length, fb eA j = 1 → op d' a.s c.s &&& P.getD j 0 = a.s &&& P.getD j 0)
    (hCo : ∀ j < P.length, fb eC j = 1 → op d' a.s c.s &&& P.getD j 0 = c.s &&& P.getD j 0)
    (hw : w = (opW d' a c).c) (hfA : fA = fAo eA w c.c) (hfC : fC = fAo eC w a.c) (hfN : fN = fNo (Nat.shiftRight g 4) w fA fC)
    (hdn : dn = fN + (bif ka then 0 else Nat.land (MU (fN + fA)) a.d) + (bif kc then 0 else Nat.land (MU (fN + fC)) c.d))
    (hsh : Shape (wd (opW d' a c) dn) (upd a.s (Nat.land (MU (w + fC)) a.d) c.s (Nat.land (MU (w + fA)) c.d) a)
      (upd a.s (Nat.land (MU (w + fC)) a.d) c.s (Nat.land (MU (w + fA)) c.d) c)
      (v.map (upd a.s (Nat.land (MU (w + fC)) a.d) c.s (Nat.land (MU (w + fA)) c.d))) ka kc r) :
    StOk P T l k (z + (a.c &&& c.c) - w - (eA + eC) - (bif ka then a.c else Nat.land (MU (w + fC)) a.d) -
      (bif kc then c.c else Nat.land (MU (w + fA)) c.d)) r S' ∧
    Nat.beq (Nat.land (z + (a.c &&& c.c) - w) g) g = true ∧ Nat.beq (Nat.land (z + (a.c &&& c.c) - w - (eA + eC)) g) g = true := by
  obtain ⟨b, D, hb15, hacc, hdv, hsum, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hacc hm (by omega)
  have hab : a.s ≠ c.s := hb.1
  have hfr := hb.fresh hl hm.2
  have hfS : (opW d' a c).s ∉ S := by rw [opW_s]; exact fun h => hfr (sub_C _ _ (by simpa using h))
  have hfS' : op d' a.s c.s ∉ S := by rw [← opW_s]; exact hfS
  have wa := hs.wok a ha; have wc := hs.wok c hc
  have wo := opW_ok d' wa wc
  have haS : a.s ∈ S := hs.rep.mem.2 ⟨a, ha, rfl⟩
  have hcS : c.s ∈ S := hs.rep.mem.2 ⟨c, hc, rfl⟩
  set u := upd a.s (Nat.land (MU (w + fC)) a.d) c.s (Nat.land (MU (w + fA)) c.d) with hu
  set N := P.length with hN
  have us : ∀ x, (u x).s = x.s := fun x => upd_s _ _ _ _ x
  have f1 : ∀ j, fl a j ≤ 1 := fl_le a
  have f2 : ∀ j, fl c j ≤ 1 := fl_le c
  have f3 : ∀ j, fl (opW d' a c) j ≤ 1 := fl_le _
  have f4 := opW_flags (P := P) d' wa wc
  let FA : ℕ → ℕ := fun j => fb eA j + (fl c j - fl c j * fl (opW d' a c) j)
  let FC : ℕ → ℕ := fun j => fb eC j + (fl a j - fl a j * fl (opW d' a c) j)
  let FN : ℕ → ℕ := fun j => 1 - fl (opW d' a c) j - FA j - FC j
  have n2 : ∀ j < N, _ := fun j hj => num2 (da := D j a.s) (dc := D j c.s) (ka := ka) (kc := kc) (f1 j) (f2 j) (f3 j) (f4 j).1 (he j hj)
  have pw : w = pk N (fl (opW d' a c)) := by rw [hw]; exact fl_pk wo
  have pa : a.c = pk N (fl a) := fl_pk wa
  have pc : c.c = pk N (fl c) := fl_pk wc
  have peA : eA = pk N (fb eA) := fb_pk hEA
  have peC : eC = pk N (fb eC) := fb_pk hEC
  have mulle : ∀ x y : ℕ, y ≤ 1 → x * y ≤ x := fun x y h => by
    calc x * y ≤ x * 1 := Nat.mul_le_mul_left _ h
      _ = x := mul_one x
  have pfA : fA = pk N FA := by
    rw [hfA]
    change eA + (c.c - (c.c &&& w)) = _
    rw [hw, fl_and wc]
    conv_lhs => rw [peA, pc]
    rw [pk_sub fun j _ => mulle _ _ (f3 j), pk_add]
  have pfC : fC = pk N FC := by
    rw [hfC]
    change eC + (a.c - (a.c &&& w)) = _
    rw [hw, fl_and wa]
    conv_lhs => rw [peC, pa]
    rw [pk_sub fun j _ => mulle _ _ (f3 j), pk_add]
  have pfN : fN = pk N FN := by
    rw [hfN, X.hg]
    change Nat.shiftRight (pk P.length fun _ => 16) 4 - w - fA - fC = _
    rw [shr4, pw, pfA, pfC, pk_sub, pk_sub, pk_sub]
    · intro j hj; obtain ⟨⟨q1, q2, q3⟩, _⟩ := n2 j hj; simp only [FA, FC]; omega
    · intro j hj; obtain ⟨⟨q1, q2, q3⟩, _⟩ := n2 j hj; simp only [FA]; omega
    · intro j hj; exact f3 j
  have hDb : ∀ j < N, D j a.s + D j c.s ≤ 14 := by
    intro j hj
    have h1 := hsum j hj
    have h2 : ∑ s ∈ ({a.s, c.s} : Finset ℕ), D j s ≤ ∑ s ∈ S, D j s :=
      Finset.sum_le_sum_of_subset fun x hx => by simp at hx; rcases hx with rfl | rfl; exacts [haS, hcS]
    rw [Finset.sum_pair hab] at h2; omega
  have land : ∀ {x : ℕ} {f : ℕ → ℕ} {y : W}, x = pk N f → (∀ j < N, f j ≤ 1) → y ∈ v → (y = a ∨ y = c) →
      Nat.land (MU x) y.d = pk N (fun j => f j * D j y.s) := by
    intro x f y hx hf hy hyac
    rw [hx, hdv y hy]
    refine MU_land hf fun j hj => ?_
    have := hDb j hj
    rcases hyac with rfl | rfl <;> omega
  have lsC : Nat.land (MU (w + fC)) a.d = pk N (fun j => (fl (opW d' a c) j + FC j) * D j a.s) :=
    land (by rw [pw, pfC, pk_add]) (fun j hj => by obtain ⟨⟨q1, q2, q3⟩, _⟩ := n2 j hj; simp only [FC]; omega) ha (Or.inl rfl)
  have lsA : Nat.land (MU (w + fA)) c.d = pk N (fun j => (fl (opW d' a c) j + FA j) * D j c.s) :=
    land (by rw [pw, pfA, pk_add]) (fun j hj => by obtain ⟨⟨q1, q2, q3⟩, _⟩ := n2 j hj; simp only [FA]; omega) hc (Or.inr rfl)
  have llA : Nat.land (MU (fN + fA)) a.d = pk N (fun j => (FN j + FA j) * D j a.s) :=
    land (by rw [pfN, pfA, pk_add]) (fun j hj => by obtain ⟨⟨q1, q2, q3⟩, _⟩ := n2 j hj; simp only [FN, FA, FC]; omega) ha (Or.inl rfl)
  have llC : Nat.land (MU (fN + fC)) c.d = pk N (fun j => (FN j + FC j) * D j c.s) :=
    land (by rw [pfN, pfC, pk_add]) (fun j hj => by obtain ⟨⟨q1, q2, q3⟩, _⟩ := n2 j hj; simp only [FN, FA, FC]; omega) hc (Or.inr rfl)
  let κ : ℕ → Kd := fun j => kdOf (fl (opW d' a c) j) (FA j) (FC j)
  let D' : ℕ → ℕ → ℕ := fun j s => if s = op d' a.s c.s then (κ j).out (if ka then 0 else D j a.s) (if kc then 0 else D j c.s)
    else if s = a.s then (κ j).kpa (D j a.s) else if s = c.s then (κ j).kpc (D j c.s) else D j s
  have hao : a.s ≠ op d' a.s c.s := fun e => hfS' (e ▸ haS)
  have hco : c.s ≠ op d' a.s c.s := fun e => hfS' (e ▸ hcS)
  have kaif : ∀ x : ℕ, (if a.s ∈ S' then 0 else x) = if ka then 0 else x := fun x => by
    by_cases h : a.s ∈ S'
    · have e : ka = true := by rw [hka]; exact decide_eq_true h
      rw [e, ite_eq_left h]; rfl
    · have e : ka = false := by rw [hka]; exact decide_eq_false h
      rw [e, ite_eq_right h]; rfl
  have kcif : ∀ x : ℕ, (if c.s ∈ S' then 0 else x) = if kc then 0 else x := fun x => by
    by_cases h : c.s ∈ S'
    · have e : kc = true := by rw [hkc]; exact decide_eq_true h
      rw [e, ite_eq_left h]; rfl
    · have e : kc = false := by rw [hkc]; exact decide_eq_false h
      rw [e, ite_eq_right h]; rfl
  have hDS : ∀ j, DStep (κ j) (D j) (D' j) (op d' a.s c.s) a.s c.s S' := by
    intro j
    refine ⟨?_, fun _ => ?_, fun _ => ?_, fun x _ h1 h2 h3 => ?_⟩
    · simp only [D', ite_true]; rw [kaif, kcif]
    · simp only [D', if_neg hao, if_true]; exact le_rfl
    · simp only [D', if_neg hco, if_neg hab.symm, if_true]; exact le_rfl
    · simp only [D', if_neg h1, if_neg h2, if_neg h3]; exact le_rfl
  have hκ : ∀ j < N, (κ j).ok (P.getD j 0) d' a.s c.s := by
    intro j hj
    have h0 := he j hj
    simp only [κ, kdOf]
    split_ifs with q1 q2 q3
    · refine (?_ : Cst (P.getD j 0) (op d' a.s c.s))
      rw [← opW_s]
      exact wo.cst hj (fb_one.1 q1)
    · refine (?_ : op d' a.s c.s &&& P.getD j 0 = a.s &&& P.getD j 0)
      have q0 : fl (opW d' a c) j = 0 := by have := f3 j; omega
      by_cases h1 : fb eA j = 1
      · exact hAo j hj h1
      · refine pass_ok d' wa wc hj ?_ q0
        have := fb_le eA j; have := f2 j
        simp only [FA, q0] at q2; omega
    · refine (?_ : op d' a.s c.s &&& P.getD j 0 = c.s &&& P.getD j 0)
      have q0 : fl (opW d' a c) j = 0 := by have := f3 j; omega
      by_cases h1 : fb eC j = 1
      · exact hCo j hj h1
      · have q0' : fl (opW d' c a) j = 0 := by rw [← q0]; unfold fl; rw [opW_symm]
        rw [op_comm]
        refine pass_ok d' wc wa hj ?_ q0'
        have := fb_le eC j; have := f1 j
        simp only [FC, q0] at q3; omega
    · trivial
  have hA : ∀ j < N, (κ j).del (if ka then 0 else D j a.s) (if kc then 0 else D j c.s) + (S'.filter (Cst (P.getD j 0))).card ≤ b j ∧
      Acc (P.getD j 0) T k (b j - (κ j).del (if ka then 0 else D j a.s) (if kc then 0 else D j c.s)) (D' j) S' := by
    intro j hj
    obtain ⟨p1, p2, p3⟩ := X.hP j hj
    have := (hacc j hj).bi p1 p2 p3 hb hm hl hk (κ j) (hκ j hj) (hDS j)
    simp only [kaif, kcif] at this
    exact this
  have hrep' : Rep (v.map u) S := hs.rep.upd _ _ _ _
  have hrep : Rep r S' := by
    refine hsh.rep hrep' (List.mem_map_of_mem ha) (List.mem_map_of_mem hc) (by rw [us, us]; exact hab) hfS fun x => ?_
    rw [us, us]
    obtain ⟨_, U, e1, e2, _⟩ := hb
    change x ∈ S' ↔ x = (opW d' a c).s ∨ _
    rw [opW_s, e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_, ?_⟩
        · rintro rfl; rw [hka, e2]; simp [h]
        · rintro rfl; rw [hkc, e2]; simp [h]
    · rintro (h | ⟨h, g1, g2⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h | h
        · have := g1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · have := g2 h; rw [hkc, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hmem : ∀ x ∈ r, x = wd (opW d' a c) dn ∨ ∃ y ∈ v, x = u y := fun x hx => by
    rcases hsh.mem hx with h | h
    · exact Or.inl h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h; exact Or.inr ⟨y, hy, rfl⟩
  have hwok : ∀ x ∈ r, WOk P x := fun x hx => by
    rcases hmem x hx with rfl | ⟨y, hy, rfl⟩
    · exact ⟨wo.pa, wo.pb, wo.ec, wo.ca, wo.cb⟩
    · exact (hs.wok y hy).upd _ _ _ _
  have hgood : ∀ x ∈ r, Good l x.s := fun x hx => by
    rcases hmem x hx with rfl | ⟨y, hy, rfl⟩
    · change Good l (opW d' a c).s
      rw [opW_s]; exact op_good _ (hs.good a ha) (hs.good c hc)
    · rw [us]; exact hs.good y hy
  have hcnt : ∀ j, cnt r j + (bif ka then 0 else fl a j) + (bif kc then 0 else fl c j) = fl (opW d' a c) j + cnt v j := by
    intro j
    have := hsh.cnt j
    rw [fl_upd, fl_upd, cnt_upd] at this
    exact this
  have n1 : ∀ j < N, _ := fun j hj => num1 (b := b j) (cv := cnt v j) (cr := cnt r j) (da := D j a.s) (dc := D j c.s) (ka := ka) (kc := kc)
    (f1 j) (f2 j) (f3 j) (f4 j).1 (f4 j).2 (he j hj) (hb15 j hj) (hle j hj) (hcnt j) (by
      have h1 := (hA j hj).1
      have h2 := cnt_card hrep hwok hj
      exact (Nat.add_le_add_left h2 _).trans h1)
  have e1 : z + (a.c &&& c.c) - w = pk N (fun j => 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j) := by
    rw [hz, fl_and wa, pw, pk_add, pk_sub]
    intro j hj; exact (n1 j hj).1.1
  have e2 : z + (a.c &&& c.c) - w - (eA + eC) = pk N (fun j => 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j - (fb eA j + fb eC j)) := by
    rw [e1]
    conv_lhs => rw [peA, peC]
    rw [pk_add, pk_sub]
    intro j hj; exact (n1 j hj).1.2.2.2.1
  refine ⟨⟨hrep, hwok, hgood, _, D', fun j hj => ?_, fun j hj => (hA j hj).2, ?_, fun j hj => ?_, ?_⟩, ?_, ?_⟩
  · have := hb15 j hj; omega
  · intro x hx
    rcases hmem x hx with rfl | ⟨y, hy, rfl⟩
    · change dn = pk N (fun j => D' j (opW d' a c).s)
      rw [hdn, pfN]
      have eA' : (bif ka then 0 else Nat.land (MU (fN + fA)) a.d) = pk N (fun j => bif ka then 0 else (FN j + FA j) * D j a.s) := by
        cases ka
        · exact llA
        · simp [pk]
      have eC' : (bif kc then 0 else Nat.land (MU (fN + fC)) c.d) = pk N (fun j => bif kc then 0 else (FN j + FC j) * D j c.s) := by
        cases kc
        · exact llC
        · simp [pk]
      rw [← pfN, eA', eC', pfN, pk_add, pk_add]
      refine pk_congr fun j hj => ?_
      obtain ⟨_, q, _, _⟩ := n2 j hj
      simp only [D', opW_s, if_true]
      exact q
    · by_cases h1 : y.s = a.s
      · have hya := hs.rep.inj hy ha h1
        subst hya
        have : u y = wd y (Nat.land (MU (w + fC)) y.d) := by rw [hu]; unfold upd; rw [beq_t]; rfl
        rw [this]
        change Nat.land (MU (w + fC)) y.d = pk N (fun j => D' j y.s)
        rw [lsC]
        refine pk_congr fun j hj => ?_
        simp only [D', if_neg hao, if_true]
        exact (n2 j hj).2.2.1
      · by_cases h2 : y.s = c.s
        · have hyc := hs.rep.inj hy hc h2
          subst hyc
          have : u y = wd y (Nat.land (MU (w + fA)) y.d) := by rw [hu]; unfold upd; rw [beq_f h1, beq_t]; rfl
          rw [this]
          change Nat.land (MU (w + fA)) y.d = pk N (fun j => D' j y.s)
          rw [lsA]
          refine pk_congr fun j hj => ?_
          simp only [D', if_neg hco, if_neg hab.symm, if_true]
          exact (n2 j hj).2.2.2
        · have : u y = y := by rw [hu]; unfold upd; rw [beq_f h1, beq_f h2]; rfl
          rw [this, hdv y hy]
          refine pk_congr fun j hj => ?_
          have h3 : y.s ≠ op d' a.s c.s := fun e => hfS' (e ▸ hs.rep.mem.2 ⟨y, hy, rfl⟩)
          simp only [D', if_neg h3, if_neg h1, if_neg h2]
  · have h1 := hsum j hj
    have h2 := (hDS j).sum_le hb hfS'
    omega
  · rw [e2]
    have ea : (bif ka then a.c else Nat.land (MU (w + fC)) a.d) = pk N (fun j => bif ka then fl a j else (fl (opW d' a c) j + FC j) * D j a.s) := by
      cases ka
      · exact lsC
      · exact pa
    have ec : (bif kc then c.c else Nat.land (MU (w + fA)) c.d) = pk N (fun j => bif kc then fl c j else (fl (opW d' a c) j + FA j) * D j c.s) := by
      cases kc
      · exact lsA
      · exact pc
    rw [ea, ec, pk_sub, pk_sub]
    · exact pk_congr fun j hj => (n1 j hj).2.2.2
    · intro j hj; exact (n1 j hj).2.2.1
    · intro j hj; exact (n1 j hj).2.1
  · rw [e1, nl, X.hg, ← hN, pk_guard]; · simp
    intro j hj; exact ⟨(n1 j hj).1.2.1, (n1 j hj).1.2.2.1⟩
  · rw [e2, nl, X.hg, ← hN, pk_guard]; · simp
    intro j hj; exact ⟨(n1 j hj).1.2.2.2.2.1, (n1 j hj).1.2.2.2.2.2⟩
end sound
lemma upd_irrel {sa sc da dc da' dc' : ℕ} {ka kc : Bool} (h1 : ka = false ∨ da = da') (h2 : kc = false ∨ dc = dc') (v : List W) :
    (v.filter (kp sa ka sc kc)).map (upd sa da sc dc) = (v.filter (kp sa ka sc kc)).map (upd sa da' sc dc') := by
  refine List.map_congr_left fun w hw => ?_
  have hk := (List.mem_filter.1 hw).2
  unfold kp at hk; unfold upd
  cases e1 : Nat.beq w.s sa with
  | true =>
    rw [e1] at hk; simp only [Bool.cond_true] at hk ⊢
    rcases h1 with h | h
    · rw [h] at hk; simp at hk
    · rw [h]
  | false =>
    rw [e1] at hk; simp only [Bool.cond_false] at hk ⊢
    cases e2 : Nat.beq w.s sc with
    | true =>
      rw [e2] at hk; simp only [Bool.cond_true] at hk ⊢
      rcases h2 with h | h
      · rw [h] at hk; simp at hk
      · rw [h]
    | false => rfl
lemma put_eq {m : ℕ} {o : W} {v : List W} {d : ℕ} (ho : Nat.lor o.a o.b = o.c) (hr : o.r = 0) (h0 : o.s ≠ 0) (h1 : o.s ≠ m) (h : List W → Bool) :
    put m o.s o.a o.b v d h = ins (wd o d) v h := by
  simp only [put, st_eq, beq_f h0, beq_f h1, ho]
  rw [← hr]; rfl
lemma mid_false {f : ℕ → List W → Bool} {m g np e n z : ℕ} {v : List W} {a c : W} {oa oc ka kc kb : Bool} {s x y w eA eC : ℕ}
    (hw : w = Nat.lor x y) (heA : eA = zfl np (Nat.xor a.s s) (Nat.sub (Nat.shiftRight g 4) (Nat.lor (Nat.lor a.c c.c) w)))
    (heC : eC = zfl np (Nat.xor c.s s) (Nat.sub (Nat.sub (Nat.shiftRight g 4) (Nat.lor (Nat.lor a.c c.c) w)) eA))
    (h : mid f m g np e n z v a c oa oc ka kc kb s x y = false)
    (g1 : Nat.beq (Nat.land (z + (a.c &&& c.c) - w) g) g = true) (g2 : Nat.beq (Nat.land (z + (a.c &&& c.c) - w - (eA + eC)) g) g = true) :
    kids (child f g) e n (z + (a.c &&& c.c) - w - (eA + eC)) (Nat.shiftRight g 4) w (fAo eA w c.c) (fAo eC w a.c) a c oa oc ka kc kb (put m s x y v) = false := by
  simp only [mid, st_eq, bR, ← hw, ← heA, ← heC] at h
  have g1' : Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) w) g) g = true := g1
  have g2' : Nat.beq (Nat.land (Nat.sub (Nat.sub (Nat.add z (Nat.land a.c c.c)) w) (Nat.add eA eC)) g) g = true := g2
  rw [g1', g2', Bool.cond_true, Bool.cond_true] at h
  exact h
lemma kids_false {ch : Bool → ((List W → Bool) → Bool) → ℕ → Bool} {e n z u w fA fC fN : ℕ} {a c : W} {oa oc ka kc kb : Bool} {mk : ℕ → (List W → Bool) → Bool}
    (hN : fN = fNo u w fA fC) (h : kids ch e n z u w fA fC a c oa oc ka kc kb mk = false) :
    (oa = true → oc = true → ch false (fun h => mk (fN + Nat.land (MU (fN + fA)) a.d + Nat.land (MU (fN + fC)) c.d) (fun r => rmk a.s false 0 c.s false 0 r h))
      (z - Nat.land (MU (w + fC)) a.d - Nat.land (MU (w + fA)) c.d) = false) ∧
    (oa = true → n + 1 ≤ e → ch kc (fun h => mk (fN + Nat.land (MU (fN + fA)) a.d) (fun r => rmk a.s false 0 c.s true (Nat.land (MU (w + fA)) c.d) r h))
      (z - Nat.land (MU (w + fC)) a.d - c.c) = false) ∧
    (oc = true → n + 1 ≤ e → ch ka (fun h => mk (fN + Nat.land (MU (fN + fC)) c.d) (fun r => rmk a.s true (Nat.land (MU (w + fC)) a.d) c.s false 0 r h))
      (z - a.c - Nat.land (MU (w + fA)) c.d) = false) ∧
    (n + 2 ≤ e → ch kb (fun h => mk fN (fun r => rmkB a.s (Nat.land (MU (w + fC)) a.d) c.s (Nat.land (MU (w + fA)) c.d) (a.d + c.d) r h))
      (z - a.c - c.c) = false) := by
  subst hN
  simp only [kids, bR] at h
  have b1 : n + 1 ≤ e → Nat.ble (Nat.succ n) e = true := fun h => Nat.ble_eq_true_of_le h
  have b2 : n + 2 ≤ e → Nat.ble (Nat.succ (Nat.succ n)) e = true := fun h => Nat.ble_eq_true_of_le h
  have key : ∀ {p q : Bool}, (bif p then true else q) = false → p = false ∧ q = false := fun {p q} h => by cases p <;> simp_all
  obtain ⟨h1, h2⟩ := key h
  obtain ⟨h3, h4⟩ := key h2
  refine ⟨fun p q => ?_, fun p q => ?_, fun p q => ?_, fun q => ?_⟩
  · rw [p, q] at h1; exact h1
  · rw [b1 q, Bool.cond_true] at h3
    have := (key h3).2; rw [p] at this; exact this
  · rw [b1 q, Bool.cond_true] at h3
    have := (key h3).1; rw [p] at this; exact this
  · rw [b2 q] at h4; exact h4
lemma nc_spec {P : List ℕ} {a c o : W} {g w : ℕ} (hg : g = pk P.length (fun _ => 16)) (ha : WOk P a) (hc : WOk P c) (ho : WOk P o) (hw : w = o.c) :
    Nat.sub (Nat.shiftRight g 4) (Nat.lor (Nat.lor a.c c.c) w) = pk P.length (fun j => 1 - max (fl a j) (max (fl c j) (fl o j))) := by
  have hx : isPk P.length ((a.c ||| c.c) ||| w) := by rw [hw]; exact isPk_or (isPk_or ha.pc hc.pc) ho.pc
  have e : (a.c ||| c.c) ||| w = pk P.length (fun j => max (fl a j) (max (fl c j) (fl o j))) := by
    rw [pk_of hx]
    refine pk_congr fun j _ => ?_
    rw [hw, Nat.testBit_or, Nat.testBit_or]; unfold fl
    cases a.c.testBit (5 * j) <;> cases c.c.testBit (5 * j) <;> cases o.c.testBit (5 * j) <;> rfl
  change Nat.shiftRight g 4 - ((a.c ||| c.c) ||| w) = _
  rw [hg, shr4, e, pk_sub]
  intro j _
  have := fl_le a j; have := fl_le c j; have := fl_le o j; omega
lemma zfl_isPk {n np q nc : ℕ} (h : isPk n nc) : isPk n (zfl np q nc) := by
  unfold zfl zflG
  change isPk n (_ &&& nc)
  rw [Nat.and_comm]; exact isPk_and h
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma zfl_eq {q nc j : ℕ} {a o : ℕ} (hj : j < P.length) (hq : q = a ^^^ o) (h : fb (zfl np q nc) j = 1) : o &&& P.getD j 0 = a &&& P.getD j 0 := by
  obtain ⟨f, f1, f2, f3⟩ := X.hnp
  obtain ⟨h16, h0, _⟩ := zfl_spec f1 f2 (by decide) (fb_one.1 h)
  have h1 : q &&& P.getD j 0 = 0 := by
    rw [← f3 j hj h16, Nat.and_comm (P.getD j 0), ← Nat.and_assoc, h0, Nat.zero_and]
  subst hq
  apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (fun x => x.testBit i) h1
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at this ⊢
  revert this
  cases a.testBit i <;> cases o.testBit i <;> cases (P.getD j 0).testBit i <;> simp
lemma gate_sound {f : ℕ → List W → Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool} {oa oc ka kc kb : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hoa : a.s ∉ S' → oa = true) (hoc : c.s ∉ S' → oc = true) (hka : a.s ∈ S' → c.s ∉ S' → ka = false) (hkc : c.s ∈ S' → a.s ∉ S' → kc = false)
    (hkb : a.s ∈ S' → c.s ∈ S' → kb = false)
    (hp : mid f m g np e (Nat.pred n) z v a c oa oc ka kc kb (opW d' a c).s (opW d' a c).a (opW d' a c).b = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, (w.s = op d' a.s c.s ∧ w.r = 0) ∨ ∃ w' ∈ v, w'.s = w.s ∧ w'.r = w.r := by
  subst hn
  have hmin := hb.min hl hm.2
  have hfr := hb.fresh hl hm.2
  have wa := hs.wok a ha; have wc := hs.wok c hc
  have wo := opW_ok d' wa wc
  have hosS : ∀ w ∈ v, w.s ≠ (opW d' a c).s := fun w hw e => hfr (by
    rw [← opW_s, ← e]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  have ho0 : (opW d' a c).s ≠ 0 := fun e => hfr (by rw [← opW_s, e]; simp [C])
  have ho1 : (opW d' a c).s ≠ m := fun e => hfr (by rw [← opW_s, e]; simp [C])
  have hab : a.s ≠ c.s := hb.1
  have ec : Nat.lor (opW d' a c).a (opW d' a c).b = (opW d' a c).c := by cases d' <;> rfl
  have er : (opW d' a c).r = 0 := by cases d' <;> rfl
  obtain ⟨w, hw⟩ : ∃ w, w = Nat.lor (opW d' a c).a (opW d' a c).b := ⟨_, rfl⟩
  have hw' : w = (opW d' a c).c := hw.trans ec
  obtain ⟨nc, hnc⟩ : ∃ nc, nc = Nat.sub (Nat.shiftRight g 4) (Nat.lor (Nat.lor a.c c.c) w) := ⟨_, rfl⟩
  have pnc : nc = pk P.length (fun j => 1 - max (fl a j) (max (fl c j) (fl (opW d' a c) j))) := by rw [hnc]; exact nc_spec X.hg wa wc wo hw'
  have hncP : isPk P.length nc := by rw [pnc]; exact pk_isPk fun j _ => by omega
  have fbnc : ∀ j < P.length, fb nc j = 1 - max (fl a j) (max (fl c j) (fl (opW d' a c) j)) := fun j hj => by
    rw [pnc]; exact fb_of_pk (fun j _ => by omega) hj
  obtain ⟨eA, heA⟩ : ∃ eA, eA = zfl np (Nat.xor a.s (opW d' a c).s) nc := ⟨_, rfl⟩
  have hEA : isPk P.length eA := by rw [heA]; exact zfl_isPk hncP
  have zle : ∀ {q x j : ℕ}, fb (zfl np q x) j ≤ fb x j := by
    intro q x j
    unfold fb zfl zflG
    change ((_ &&& x).testBit (5 * j)).toNat ≤ _
    rw [Nat.testBit_and]
    cases x.testBit (5 * j) <;> simp
    cases Nat.testBit _ _ <;> simp
  have fbA : ∀ j < P.length, fb eA j ≤ 1 - max (fl a j) (max (fl c j) (fl (opW d' a c) j)) := fun j hj => by
    rw [← fbnc j hj, heA]; exact zle
  have pnc2 : nc - eA = pk P.length (fun j => fb nc j - fb eA j) := by
    conv_lhs => rw [fb_pk hncP, fb_pk hEA]
    exact pk_sub fun j hj => by rw [fbnc j hj]; exact fbA j hj
  obtain ⟨eC, heC⟩ : ∃ eC, eC = zfl np (Nat.xor c.s (opW d' a c).s) (Nat.sub nc eA) := ⟨_, rfl⟩
  have hnc2 : isPk P.length (Nat.sub nc eA) := by
    change isPk P.length (nc - eA); rw [pnc2]; exact pk_isPk fun j _ => by have := fb_le nc j; omega
  have hEC : isPk P.length eC := by rw [heC]; exact zfl_isPk hnc2
  have fbC : ∀ j < P.length, fb eC j ≤ fb nc j - fb eA j := fun j hj => by
    rw [heC]
    refine zle.trans ?_
    change fb (nc - eA) j ≤ _
    rw [pnc2, fb_of_pk (fun j _ => by have := fb_le nc j; omega) hj]
  have he : ∀ j < P.length, fb eA j + fb eC j + max (fl a j) (max (fl c j) (fl (opW d' a c) j)) ≤ 1 := fun j hj => by
    have h1 := fbA j hj; have h2 := fbC j hj; rw [fbnc j hj] at h2
    have := fl_le a j; have := fl_le c j; have := fl_le (opW d' a c) j; omega
  have hAo : ∀ j < P.length, fb eA j = 1 → op d' a.s c.s &&& P.getD j 0 = a.s &&& P.getD j 0 := fun j hj h => by
    rw [← opW_s]; rw [heA] at h; exact zfl_eq X hj rfl h
  have hCo : ∀ j < P.length, fb eC j = 1 → op d' a.s c.s &&& P.getD j 0 = c.s &&& P.getD j 0 := fun j hj h => by
    rw [← opW_s]; rw [heC] at h; exact zfl_eq X hj rfl h
  obtain ⟨fA, hfA⟩ : ∃ fA, fA = fAo eA w c.c := ⟨_, rfl⟩
  obtain ⟨fC, hfC⟩ : ∃ fC, fC = fAo eC w a.c := ⟨_, rfl⟩
  obtain ⟨fN, hfN⟩ : ∃ fN, fN = fNo (Nat.shiftRight g 4) w fA fC := ⟨_, rfl⟩
  obtain ⟨da, hda⟩ : ∃ da, da = Nat.land (MU (w + fC)) a.d := ⟨_, rfl⟩
  obtain ⟨dc, hdc⟩ : ∃ dc, dc = Nat.land (MU (w + fA)) c.d := ⟨_, rfl⟩
  have main : ∀ qa qc : Bool, qa = decide (a.s ∈ S') → qc = decide (c.s ∈ S') → ∃ r0 : List W, r0.Perm (wd (opW d' a c) (fN + (bif qa then 0 else Nat.land (MU (fN + fA)) a.d) + (bif qc then 0 else Nat.land (MU (fN + fC)) c.d)) :: v) ∧
      (∀ h, put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v (fN + (bif qa then 0 else Nat.land (MU (fN + fA)) a.d) + (bif qc then 0 else Nat.land (MU (fN + fC)) c.d)) h = h r0) ∧
      ((r0.filter (kp a.s qa c.s qc)).map (upd a.s da c.s dc)).length = S'.card ∧
      ((r0.filter (kp a.s qa c.s qc)).map (upd a.s da c.s dc)).length + (bif qa then 0 else 1) + (bif qc then 0 else 1) = v.length + 1 ∧
      StOk P T l k (z + (a.c &&& c.c) - w - (eA + eC) - (bif qa then a.c else da) - (bif qc then c.c else dc)) ((r0.filter (kp a.s qa c.s qc)).map (upd a.s da c.s dc)) S' ∧
      (∀ x ∈ (r0.filter (kp a.s qa c.s qc)).map (upd a.s da c.s dc), (x.s = op d' a.s c.s ∧ x.r = 0) ∨ ∃ w' ∈ v, w'.s = x.s ∧ w'.r = x.r) ∧
      Nat.beq (Nat.land (z + (a.c &&& c.c) - w) g) g = true ∧ Nat.beq (Nat.land (z + (a.c &&& c.c) - w - (eA + eC)) g) g = true := by
    intro qa qc h1 h2
    obtain ⟨r0, hr0, hins⟩ := ins_spec (wd (opW d' a c) (fN + (bif qa then 0 else Nat.land (MU (fN + fA)) a.d) + (bif qc then 0 else Nat.land (MU (fN + fC)) c.d))) v hosS
    have hsh := shape_upd (o := wd (opW d' a c) (fN + (bif qa then 0 else Nat.land (MU (fN + fA)) a.d) + (bif qc then 0 else Nat.land (MU (fN + fC)) c.d))) da dc hosS hr0 hs.rep.1 ha hc hab qa qc
    have hst := bi_st X hs hm hk hb hl ha hc h1 h2 hEA hEC he hAo hCo hw' hfA hfC hfN rfl (by rw [← hda, ← hdc]; exact hsh)
    rw [← hda, ← hdc] at hst
    have hlen := hsh.len
    refine ⟨r0, hr0, fun h => ?_, hst.1.rep.card.symm, by rw [List.length_map (as := v)] at hlen; exact hlen, hst.1, fun x hx => ?_, hst.2.1, hst.2.2⟩
    · rw [put_eq ec er ho0 ho1, hins]
    · rcases hsh.mem hx with rfl | hx'
      · exact Or.inl ⟨opW_s _ _ _, er⟩
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx'
        exact Or.inr ⟨y, hy, (upd_s _ _ _ _ _).symm, (upd_r _ _ _ _ _).symm⟩
  have hv2 : 2 ≤ v.length := by
    rw [← hs.rep.card]
    have : ({a.s, c.s} : Finset ℕ) ⊆ S := by
      intro x hx; simp at hx; rcases hx with rfl | rfl; exacts [hb.sub.1, hb.sub.2.1]
    have h2 := Finset.card_le_card this
    rwa [Finset.card_pair hab] at h2
  have hpr : Nat.pred v.length + 1 = v.length := by simp [Nat.pred_eq_sub_one]; omega
  by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
  · obtain ⟨r0, p0, p1, p2, p3, p4, p5, g1, g2⟩ := main true true (by simp [q1]) (by simp [q2])
    have hkd := (kids_false hfN (by rw [hfA, hfC]; exact mid_false hw (by rw [heA, hnc]) (by rw [heC, hnc]) hp g1 g2)).2.2.2 (by rw [p2] at p3; simp only [Bool.cond_true, Bool.cond_false] at p3; omega)
    rw [← hda, ← hdc] at hkd
    simp only [Bool.cond_true, add_zero] at p0 p1 p3 p4
    refine ⟨_, _, child_sound X (fun h => ?_) (hkb q1 q2) p4 hmin hk hkd, p4, p5⟩
    rw [p1]
    unfold rmkB
    rw [bR]
    cases hz : Nat.beq (a.d + c.d) 0 with
    | false => rw [Bool.cond_false, rmk_eq]
    | true =>
      rw [Bool.cond_true]
      have hz0 : a.d + c.d = 0 := Nat.eq_of_beq_eq_true hz
      have ha0 : a.d = 0 := by omega
      have hc0 : c.d = 0 := by omega
      have e1 : r0.filter (kp a.s true c.s true) = r0 := by
        rw [List.filter_eq_self]; intro x _
        unfold kp; cases Nat.beq x.s a.s <;> cases Nat.beq x.s c.s <;> rfl
      rw [e1]
      congr 1
      have e2 : ∀ x ∈ r0, upd a.s da c.s dc x = x := by
        intro x hx
        have hda0 : da = 0 := by rw [hda, ha0]; exact Nat.and_zero _
        have hdc0 : dc = 0 := by rw [hdc, hc0]; exact Nat.and_zero _
        have hx' := p0.subset hx
        simp only [List.mem_cons] at hx'
        unfold upd
        rcases hx' with rfl | hx'
        · have n1 : (wd (opW d' a c) fN).s ≠ a.s := (hosS a ha).symm
          have n2 : (wd (opW d' a c) fN).s ≠ c.s := (hosS c hc).symm
          rw [beq_f n1, beq_f n2]; rfl
        · by_cases n1 : x.s = a.s
          · have := hs.rep.inj hx' ha n1
            subst this; rw [beq_t, hda0, ← ha0]; rfl
          · by_cases n2 : x.s = c.s
            · have := hs.rep.inj hx' hc n2
              subst this; rw [beq_f n1, beq_t, hdc0, ← hc0]; rfl
            · rw [beq_f n1, beq_f n2]; rfl
      conv_lhs => rw [← List.map_id r0]
      exact List.map_congr_left fun x hx => (e2 x hx).symm
  · obtain ⟨r0, p0, p1, p2, p3, p4, p5, g1, g2⟩ := main true false (by simp [q1]) (by simp [q2])
    have hkd := (kids_false hfN (by rw [hfA, hfC]; exact mid_false hw (by rw [heA, hnc]) (by rw [heC, hnc]) hp g1 g2)).2.2.1 (hoc q2) (by rw [p2] at p3; simp only [Bool.cond_true, Bool.cond_false] at p3; omega)
    rw [← hda, ← hdc] at hkd
    simp only [Bool.cond_true, Bool.cond_false, add_zero] at p0 p1 p3 p4
    refine ⟨_, _, child_sound X (fun h => ?_) (hka q1 q2) p4 hmin hk hkd, p4, p5⟩
    rw [p1, rmk_eq]; congr 1; exact upd_irrel (Or.inr rfl) (Or.inl rfl) _
  · obtain ⟨r0, p0, p1, p2, p3, p4, p5, g1, g2⟩ := main false true (by simp [q1]) (by simp [q2])
    have hkd := (kids_false hfN (by rw [hfA, hfC]; exact mid_false hw (by rw [heA, hnc]) (by rw [heC, hnc]) hp g1 g2)).2.1 (hoa q1) (by rw [p2] at p3; simp only [Bool.cond_true, Bool.cond_false] at p3; omega)
    rw [← hda, ← hdc] at hkd
    simp only [Bool.cond_true, Bool.cond_false, add_zero] at p0 p1 p3 p4
    refine ⟨_, _, child_sound X (fun h => ?_) (hkc q2 q1) p4 hmin hk hkd, p4, p5⟩
    rw [p1, rmk_eq]; congr 1; exact upd_irrel (Or.inl rfl) (Or.inr rfl) _
  · obtain ⟨r0, p0, p1, p2, p3, p4, p5, g1, g2⟩ := main false false (by simp [q1]) (by simp [q2])
    have hkd := (kids_false hfN (by rw [hfA, hfC]; exact mid_false hw (by rw [heA, hnc]) (by rw [heC, hnc]) hp g1 g2)).1 (hoa q1) (hoc q2)
    rw [← hda, ← hdc] at hkd
    simp only [Bool.cond_false] at p0 p1 p3 p4
    refine ⟨_, _, child_sound X (fun h => ?_) rfl p4 hmin hk hkd, p4, p5⟩
    rw [p1, rmk_eq]; congr 1; exact upd_irrel (Or.inl rfl) (Or.inl rfl) _
end sound
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma un_st {k k' t z : ℕ} {v r0 : List W} {S S' : Finset ℕ} {a : W} {ka : Bool} {dn : ℕ}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hb : Un m a.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hka : ka = decide (a.s ∈ S'))
    (hdn : dn = (Nat.shiftRight g 4 - a.c) + (bif ka then 0 else a.d)) (hr0 : r0.Perm (wd (notW m a) dn :: v)) :
    StOk P T l k (z - a.c - (bif ka then a.c else 0)) ((r0.filter (kp a.s ka a.s ka)).map (upd a.s 0 a.s 0)) S' ∧
    ∀ x ∈ (r0.filter (kp a.s ka a.s ka)).map (upd a.s 0 a.s 0), (x.s = a.s ^^^ m ∧ x.r = 0) ∨ ∃ w' ∈ v, w'.s = x.s ∧ w'.r = x.r := by
  obtain ⟨b, D, hb15, hacc, hdv, hsum, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hacc hm (by omega)
  have hfr := hb.fresh hl hm.2
  have hfS : a.s ^^^ m ∉ S := fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha
  have haS : a.s ∈ S := hb.sub.1
  have hne : a.s ≠ a.s ^^^ m := fun e => hfS (e ▸ haS)
  set u := upd a.s 0 a.s 0 with hu
  set r := (r0.filter (kp a.s ka a.s ka)).map u with hr
  have us : ∀ x, (u x).s = x.s := fun x => upd_s _ _ _ _ x
  have pa : a.c = pk P.length (fl a) := fl_pk wa
  have wo : WOk P (notW m a) := by
    refine ⟨wa.pb, wa.pa, by rw [Nat.or_comm]; exact wa.ec, fun j hj h => ?_, fun j hj h => ?_⟩
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.cb j hj h]; simp
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.ca j hj h]; simp
  have hS' : ∀ x, x ∈ S' ↔ x = a.s ^^^ m ∨ (x ∈ S ∧ (x = a.s → ka = true)) := by
    intro x
    obtain ⟨U, e1, e2⟩ := hb
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_⟩
        rintro rfl; rw [hka, e2]; simp [h]
    · rintro (h | ⟨h, f1⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hnd0 : (r0.map W.s).Nodup := by
    refine (hr0.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => hfS ?_, hs.rep.1⟩
    rw [← hs.rep.2]; simpa [notW, wd] using hm
  have hmap : r.map W.s = (r0.filter (kp a.s ka a.s ka)).map W.s := by rw [hr]; exact map_upd_s _ _ _ _ _
  have hkp : ∀ x : W, kp a.s ka a.s ka x = true ↔ (x.s = a.s → ka = true) := by
    intro x; unfold kp
    by_cases h : x.s = a.s
    · rw [h, beq_t]; simp
    · rw [beq_f h]; simp [h]
  have hrep : Rep r S' := by
    refine ⟨?_, Finset.ext fun x => ?_⟩
    · rw [hmap]; exact hnd0.sublist (List.filter_sublist.map _)
    · rw [hmap, List.mem_toFinset, hS', List.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨hy1, hy2⟩ := List.mem_filter.1 hy
        have hy3 := hr0.subset hy1
        simp only [List.mem_cons] at hy3
        rcases hy3 with rfl | hy3
        · exact Or.inl rfl
        · exact Or.inr ⟨hs.rep.mem.2 ⟨y, hy3, rfl⟩, (hkp y).1 hy2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · refine ⟨wd (notW m a) dn, List.mem_filter.2 ⟨hr0.symm.subset (by simp), (hkp _).2 fun e => absurd e.symm hne⟩, rfl⟩
        · obtain ⟨y, hy, rfl⟩ := hs.rep.mem.1 h1
          exact ⟨y, List.mem_filter.2 ⟨hr0.symm.subset (by simp [hy]), (hkp _).2 h2⟩, rfl⟩
  have hmem : ∀ x ∈ r, x = wd (notW m a) dn ∨ ∃ y ∈ v, x = u y := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    have hy3 := hr0.subset (List.mem_filter.1 hy).1
    simp only [List.mem_cons] at hy3
    rcases hy3 with rfl | hy3
    · left
      rw [hu]; unfold upd
      have : (wd (notW m a) dn).s ≠ a.s := fun e => hne e.symm
      rw [beq_f this]; rfl
    · exact Or.inr ⟨y, hy3, rfl⟩
  have hwok : ∀ x ∈ r, WOk P x := fun x hx => by
    rcases hmem x hx with rfl | ⟨y, hy, rfl⟩
    · exact ⟨wo.pa, wo.pb, wo.ec, wo.ca, wo.cb⟩
    · exact (hs.wok y hy).upd _ _ _ _
  have hgood : ∀ x ∈ r, Good l x.s := fun x hx => by
    rcases hmem x hx with rfl | ⟨y, hy, rfl⟩
    · have hg := hs.good a ha
      refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
      · change (a.s ^^^ m).testBit i = (a.s ^^^ m).testBit j
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.1 i j h h1 h2, (X.lg i h1).1.1, (X.lg j h2).1.1]
      · change (a.s ^^^ m).testBit (NN + i) = (a.s ^^^ m).testBit (NN + j)
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.2 i j h h1 h2, (X.lg i h1).1.2.1, (X.lg j h2).1.2.1]
    · rw [us]; exact hs.good y hy
  have hcnt : ∀ j, cnt r j + (bif ka then 0 else fl a j) = fl a j + cnt v j := by
    intro j
    have e0 := cnt_perm hr0 j
    rw [cnt_cons] at e0
    change cnt r0 j = fl a j + cnt v j at e0
    have e1 : cnt r j = cnt (r0.filter (kp a.s ka a.s ka)) j := by rw [hr]; exact cnt_upd _ _ _ _ _ _
    rw [e1, ← e0]
    cases hkk : ka with
    | true =>
      have : r0.filter (kp a.s true a.s true) = r0 := by
        rw [List.filter_eq_self]; intro x _
        unfold kp; cases Nat.beq x.s a.s <;> rfl
      rw [this]; simp
    | false =>
      have har : a ∈ r0 := hr0.symm.subset (by simp [ha])
      have h1 := cnt_perm (filter_perm hnd0 har) j
      rw [cnt_cons] at h1
      have : r0.filter (kp a.s false a.s false) = r0.filter (fun w => !Nat.beq w.s a.s) := by
        congr 1; funext x; unfold kp; cases Nat.beq x.s a.s <;> rfl
      rw [this, ← h1]; simp only [Bool.cond_false]; omega
  let D' : ℕ → ℕ → ℕ := fun j s => if s = a.s ^^^ m then (1 - fl a j) + (if ka then 0 else D j a.s) else if s = a.s then 0 else D j s
  have kaif : ∀ x : ℕ, (if a.s ∈ S' then 0 else x) = if ka then 0 else x := fun x => by
    by_cases h : a.s ∈ S'
    · have e : ka = true := by rw [hka]; exact decide_eq_true h
      rw [e, ite_eq_left h]; rfl
    · have e : ka = false := by rw [hka]; exact decide_eq_false h
      rw [e, ite_eq_right h]; rfl
  have hg' : ∀ j, D' j (a.s ^^^ m) = (1 - fl a j) + (if a.s ∈ S' then 0 else D j a.s) := fun j => by rw [kaif]; simp only [D', ite_true]
  have ho' : ∀ j, ∀ s ∈ S', s ≠ a.s ^^^ m → s ≠ a.s → D' j s ≤ D j s := fun j s _ h1 h2 => by simp only [D', ite_eq_right h1, ite_eq_right h2]; exact le_rfl
  have hka' : ∀ j, D' j a.s = 0 := fun j => by simp only [D', ite_eq_right hne, ite_true]
  have hA : ∀ j < P.length, fl a j + (S'.filter (Cst (P.getD j 0))).card ≤ b j ∧ Acc (P.getD j 0) T k (b j - fl a j) (D' j) S' := by
    intro j hj
    obtain ⟨p1, p2, p3⟩ := X.hP j hj
    have h1 := fl_le a j
    have := (hacc j hj).un (D' := D' j) p1 p2 p3 hb hm hl hk (decide (fl a j = 1)) (fun h => wa.cst hj (by
        have := of_decide_eq_true h; exact fb_one.1 this)) ?_ ?_ (ho' j)
    · have e : (if decide (fl a j = 1) = true then 1 else 0) = fl a j := by
        generalize fl a j = x at *
        interval_cases x <;> rfl
      rw [e] at this; exact this
    · rw [hg']
      generalize fl a j = x at *
      interval_cases x <;> simp
    · intro _; rw [hka']; exact Nat.zero_le _
  have hle' : ∀ j < P.length, fl a j + cnt r j ≤ b j := fun j hj =>
    (Nat.add_le_add_left (cnt_card hrep hwok hj) _).trans (hA j hj).1
  refine ⟨⟨hrep, hwok, hgood, _, D', fun j hj => ?_, fun j hj => (hA j hj).2, ?_, fun j hj => ?_, ?_⟩, ?_⟩
  · have := hb15 j hj; omega
  · intro x hx
    rcases hmem x hx with rfl | ⟨y, hy, rfl⟩
    · change dn = pk P.length (fun j => D' j (a.s ^^^ m))
      have e1 : Nat.shiftRight g 4 - a.c = pk P.length (fun j => 1 - fl a j) := by
        rw [X.hg, shr4]; conv_lhs => rw [pa]
        exact pk_sub fun j _ => fl_le a j
      have e2 : (bif ka then 0 else a.d) = pk P.length (fun j => if ka then 0 else D j a.s) := by
        cases hkk : ka
        · simpa using hdv a ha
        · simp [pk]
      rw [hdn, e1, e2, pk_add]
      exact pk_congr fun j _ => by simp only [D', ite_true]
    · by_cases h1 : y.s = a.s
      · have : u y = wd y 0 := by rw [hu]; unfold upd; rw [h1, beq_t]; rfl
        rw [this]
        change 0 = pk P.length (fun j => D' j y.s)
        rw [h1]
        have : pk P.length (fun j => D' j a.s) = pk P.length (fun _ => 0) := pk_congr fun j _ => hka' j
        rw [this]; simp [pk]
      · have : u y = y := by rw [hu]; unfold upd; rw [beq_f h1]; rfl
        rw [this, hdv y hy]
        refine pk_congr fun j hj => ?_
        have h3 : y.s ≠ a.s ^^^ m := fun e => hfS (e ▸ hs.rep.mem.2 ⟨y, hy, rfl⟩)
        simp only [D', ite_eq_right h3, ite_eq_right h1]
  · have h1 := hsum j hj
    have h2 := un_sum_le (D := D j) (D' := D' j) (e := 1 - fl a j) hb hfS (by omega) (by rw [hg']) (fun s hs' hne' => by
      by_cases h : s = a.s
      · subst h; rw [hka']; exact Nat.zero_le _
      · exact ho' j s hs' hne' h)
    omega
  · have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact pa
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    rw [ea, hz]
    conv_lhs => rw [pa]
    rw [pk_sub, pk_sub]
    · refine pk_congr fun j hj => ?_
      have q1 := hle j hj; have q2 := hle' j hj; have q4 := hb15 j hj
      have q5 := hcnt j; have q6 := fl_le a j
      cases ka <;> simp at q5 ⊢ <;> omega
    · intro j hj; have := hle j hj; have := le1 j; have := fl_le a j; omega
    · intro j hj; have := hle j hj; have := fl_le a j; omega
  · intro x hx
    rcases hmem x hx with rfl | ⟨y, hy, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨y, hy, (us y).symm, (upd_r _ _ _ _ _).symm⟩
end sound
lemma nots_false {f : ℕ → ℕ → List W → Bool} {m g e n z q : ℕ} {v r : List W} (h : nots f m g e n z q v r = false)
    {a : W} (ha : a ∈ r) (hq : a.s + 1 ≠ q) :
    (n ≤ e → ins (wd (notW m a) (Nat.shiftRight g 4 - a.c + a.d)) v (fun v => child (f (a.s ^^^ m)) g false (rmk a.s false 0 a.s false 0 v) (z - a.c)) = false) ∧
    (n + 1 ≤ e → ins (wd (notW m a) (Nat.shiftRight g 4 - a.c)) v (fun v => child (f (a.s ^^^ m)) g false (rmk a.s true 0 a.s true 0 v) (z - a.c - a.c)) = false) := by
  induction r with
  | nil => simp at ha
  | cons w r ih =>
    change (Bool.rec (motive := fun _ => Bool) (nots f m g e n z q v r) true (Bool.rec (motive := fun _ => Bool)
      (st (Nat.xor w.s m) fun s => st (Nat.sub z w.c) fun z => (fun u =>
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false (st u fun d1 => ins ⟨s, w.b, w.a, w.c, 0, d1⟩ v (fun v => child (f s) g false (rmk w.s true 0 w.s true 0 v) (Nat.sub z w.c))) (Nat.ble (Nat.succ n) e)) true
        (Bool.rec (motive := fun _ => Bool) false (st (Nat.add u w.d) fun d1 => ins ⟨s, w.b, w.a, w.c, 0, d1⟩ v (fun v => child (f s) g false (rmk w.s false 0 w.s false 0 v) z)) (Nat.ble n e)))
      (Nat.sub (Nat.shiftRight g 4) w.c)) false (Nat.beq (Nat.succ w.s) q)) : Bool) = false at h
    simp only [bR, st_eq] at h
    have key : ∀ {p q : Bool}, (bif p then true else q) = false → p = false ∧ q = false := fun {p q} h => by cases p <;> simp_all
    obtain ⟨h1, h2⟩ := key h
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · have hq' : Nat.beq (Nat.succ a.s) q = false := beq_f hq
      rw [hq', Bool.cond_false] at h1
      obtain ⟨h3, h4⟩ := key h1
      refine ⟨fun hn => ?_, fun hn => ?_⟩
      · rw [show Nat.ble n e = true from Nat.ble_eq_true_of_le hn] at h3
        exact h3
      · rw [show Nat.ble (Nat.succ n) e = true from Nat.ble_eq_true_of_le hn] at h4
        exact h4
    · exact ih h2 ha
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma nots_sound {f : ℕ → ℕ → List W → Bool} {e n z q t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Un m a.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hq : a.s + 1 ≠ q) {rr : List W} (har' : a ∈ rr)
    (hp : nots f m g e n z q v rr = false) : ∃ z' r, f (a.s ^^^ m) z' r = false ∧ StOk P T l k z' r S' ∧
      ∀ w ∈ r, (w.s = a.s ^^^ m ∧ w.r = 0) ∨ ∃ w' ∈ v, w'.s = w.s ∧ w'.r = w.r := by
  subst hn
  have hmin := hb.min hl hm.2
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (notW m a).s := fun w hw e => hfr (by
    change a.s ^^^ m ∈ _
    have : w.s = a.s ^^^ m := e
    rw [← this]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  obtain ⟨h1, h2⟩ := nots_false hp har' hq
  by_cases q1 : a.s ∈ S'
  · obtain ⟨r0, hr0, hins⟩ := ins_spec (wd (notW m a) (Nat.shiftRight g 4 - a.c)) v hosS
    obtain ⟨hst, hmem⟩ := un_st X hs hm hk hb hl ha (ka := true) (by simp [q1]) (by simp) hr0
    have hc := hst.rep.card
    have hlen : ((r0.filter (kp a.s true a.s true)).map (upd a.s 0 a.s 0)).length = v.length + 1 := by
      have : r0.filter (kp a.s true a.s true) = r0 := by
        rw [List.filter_eq_self]; intro x _
        unfold kp; cases Nat.beq x.s a.s <;> rfl
      rw [this, List.length_map, hr0.length_eq]; simp
    have h := h2 (by omega)
    rw [hins] at h
    simp only [Bool.cond_true] at hst
    exact ⟨_, _, child_sound X (fun h => rmk_eq _ _ _ _ _ _ _ h) rfl hst hmin hk h, hst, hmem⟩
  · obtain ⟨r0, hr0, hins⟩ := ins_spec (wd (notW m a) (Nat.shiftRight g 4 - a.c + a.d)) v hosS
    obtain ⟨hst, hmem⟩ := un_st X hs hm hk hb hl ha (ka := false) (by simp [q1]) (by simp) hr0
    have hc := hst.rep.card
    have hnd0 : (r0.map W.s).Nodup := by
      refine (hr0.map W.s).nodup_iff.2 ?_
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
      exact ⟨fun w hw => hosS w hw, hs.rep.1⟩
    have har : a ∈ r0 := hr0.symm.subset (by simp [ha])
    have hlen : ((r0.filter (kp a.s false a.s false)).map (upd a.s 0 a.s 0)).length = v.length := by
      have e : r0.filter (kp a.s false a.s false) = r0.filter (fun w => !Nat.beq w.s a.s) := by
        congr 1; funext x; unfold kp; cases Nat.beq x.s a.s <;> rfl
      have h5 := (filter_perm hnd0 har).length_eq
      rw [hr0.length_eq] at h5
      simp only [List.length_cons] at h5
      rw [e, List.length_map]; omega
    have h := h1 (by omega)
    rw [hins] at h
    simp only [Bool.cond_false, Nat.sub_zero] at hst
    exact ⟨_, _, child_sound X (fun h => rmk_eq _ _ _ _ _ _ _ h) rfl hst hmin hk h, hst, hmem⟩
end sound
noncomputable section hitcore
end hitcore
noncomputable section core12
end core12
lemma len_eq (v : List W) : len v = v.length := by
  induction v with
  | nil => rfl
  | cons w v ih => change Nat.succ (len v) = _; rw [ih]; rfl
lemma geo_succ (w n : ℕ) : geo w (n + 1) = 2 ^ w * geo w n + 1 := by
  change (geo w n <<< w) + 1 = _; rw [Nat.shiftLeft_eq, Nat.mul_comm]
lemma mul_geo {w x : ℕ} (hx : x < 2 ^ w) : ∀ n i, i < w * n → (x * geo w n).testBit i = x.testBit (i % w) := by
  intro n
  induction n with
  | zero => intro i hi; simp at hi
  | succ n ih =>
    intro i hi
    rw [geo_succ, show x * (2 ^ w * geo w n + 1) = 2 ^ w * (x * geo w n) + x by ring, Nat.testBit_two_pow_mul_add _ hx]
    split_ifs with h
    · rw [Nat.mod_eq_of_lt h]
    · rw [ih (i - w) (by rw [Nat.mul_succ] at hi; omega), ← Nat.mod_eq_sub_mod (by omega)]
lemma mul_geo_lt {w x : ℕ} (hx : x < 2 ^ w) : ∀ n, x * geo w n < 2 ^ (w * n) := by
  intro n
  induction n with
  | zero => change x * 0 < _; simp
  | succ n ih =>
    rw [geo_succ, show x * (2 ^ w * geo w n + 1) = 2 ^ w * (x * geo w n) + x by ring, Nat.mul_succ, pow_add, Nat.mul_comm (2 ^ (w * n))]
    have : 2 ^ w * (x * geo w n) + 2 ^ w ≤ 2 ^ w * 2 ^ (w * n) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ih
    omega
lemma dbl_bit {m x i : ℕ} (hx : x < 2 ^ m) (hi : i < 2 * m) : (dbl m x).testBit i = x.testBit (i % m) := by
  change (x ||| x <<< m).testBit i = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h : i < m
  · rw [Nat.mod_eq_of_lt h]; simp [show ¬ m ≤ i by omega]
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (show i - m < m by omega),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [show m ≤ i by omega]
lemma dbl_lt {m x : ℕ} (hx : x < 2 ^ m) : dbl m x < 2 ^ (2 * m) := by
  change x ||| x <<< m < _
  refine Nat.or_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega))) ?_
  rw [Nat.shiftLeft_eq, two_mul, pow_add]
  exact Nat.mul_lt_mul_of_pos_right hx (by positivity)
lemma rep3 {m x i : ℕ} (hx : x < 2 ^ m) (hi : i < 8 * m) : (dbl (4 * m) (dbl (2 * m) (dbl m x))).testBit i = x.testBit (i % m) := by
  have h1 := dbl_lt hx
  have h2 := dbl_lt h1
  rw [dbl_bit (by rw [show 4 * m = 2 * (2 * m) by ring]; exact h2) (by omega), dbl_bit h1 (by have := Nat.mod_lt i (show 4 * m > 0 by omega); omega),
    dbl_bit hx (by have := Nat.mod_lt (i % (4 * m)) (show 2 * m > 0 by omega); omega), Nat.mod_mod_of_dvd _ ⟨2, by ring⟩,
    Nat.mod_mod_of_dvd _ ⟨4, by ring⟩]
lemma Pos.mem {v : List W} {w : W} {i : ℕ} (h : Pos v w i) : w ∈ v := by
  obtain ⟨p, t, rfl, _⟩ := h; simp
lemma Pos.uniq {v : List W} {w w' : W} {i : ℕ} (h : Pos v w i) (h' : Pos v w' i) : w = w' := by
  obtain ⟨p, t, rfl, e⟩ := h
  obtain ⟨p', t', e', rfl⟩ := h'
  have := List.append_inj_right' (s₁ := p) (s₂ := p') (t₁ := w :: t) (t₂ := w' :: t') e' (by simp [e])
  exact (List.cons.inj this).1
lemma Pos.cons {v : List W} {w x : W} {i : ℕ} (h : Pos v w i) : Pos (x :: v) w i := by
  obtain ⟨p, t, rfl, e⟩ := h; exact ⟨x :: p, t, rfl, e⟩
lemma Pos.lt {v : List W} {w : W} {i : ℕ} (h : Pos v w i) : i < v.length := by
  obtain ⟨p, t, rfl, rfl⟩ := h; simp; omega
lemma sp_lt {l : ℕ} (hl : ∀ i, l.testBit i = true → AA.testBit i = true) {d : Bool} {s i : ℕ} (h : (sp d l s).testBit i = true) : i < NN := by
  rw [sp_bit, Bool.and_eq_true] at h
  by_contra hc
  have := hl i h.1
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le AA_lt1 (Nat.pow_le_pow_right (by omega) (by omega)))] at this
  simp at this
lemma pkd_bit {l : ℕ} (hl : ∀ i, l.testBit i = true → AA.testBit i = true) {d : Bool} {v : List W} {i b : ℕ} (hb : b < NN)
    (h : (pkd d l v).testBit (NN * i + b) = true) : ∃ w, Pos v w i ∧ (sp d l w.s).testBit b = true := by
  induction v with
  | nil => simp [pkd] at h
  | cons w t ih =>
    change (sp d l w.s <<< (NN * len t) ||| pkd d l t).testBit (NN * i + b) = true at h
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, len_eq] at h
    rcases h with ⟨h1, h2⟩ | h
    · have h3 := sp_lt hl h2
      have : i = t.length := by
        rcases Nat.lt_trichotomy i t.length with q | q | q
        · have : NN * (i + 1) ≤ NN * t.length := Nat.mul_le_mul_left _ q
          rw [Nat.mul_succ] at this; omega
        · exact q
        · have : NN * (t.length + 1) ≤ NN * i := Nat.mul_le_mul_left _ q
          rw [Nat.mul_succ] at this; omega
      subst this
      refine ⟨w, ⟨[], t, rfl, rfl⟩, ?_⟩
      rwa [Nat.add_sub_cancel_left] at h2
    · obtain ⟨x, hx, h⟩ := ih h
      exact ⟨x, hx.cons, h⟩
lemma twice_sub {d : Bool} {l i : ℕ} {v : List W} (h : (twice d l v).testBit i = true) : l.testBit i = true := by
  induction v with
  | nil => simp [twice] at h
  | cons w v ih =>
    change ((sp d l w.s &&& cov d l v) ||| twice d l v).testBit i = true at h
    rw [Nat.testBit_or, Nat.testBit_and, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | h
    · have := h.1; rw [sp_bit, Bool.and_eq_true] at this; exact this.1
    · exact ih h
lemma wst_sub {d : Bool} {l i : ℕ} {v : List W} (h : (wst d l v).testBit i = true) : l.testBit i = true := by
  change (l ^^^ twice d l v).testBit i = true at h
  rw [Nat.testBit_xor] at h
  cases h1 : l.testBit i with
  | true => rfl
  | false =>
    rw [h1, Bool.false_xor] at h
    rw [twice_sub h] at h1; simp at h1
lemma lt_of_bits {x n : ℕ} (h : ∀ i, x.testBit i = true → i < n) : x < 2 ^ n := by
  by_contra hc
  obtain ⟨i, hi, hb⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow (Nat.le_of_not_lt hc)
  have := h i hb; omega
lemma bit_lt {x n i : ℕ} (hx : x < 2 ^ n) (h : x.testBit i = true) : i < n := by
  by_contra hc
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))] at h
  simp at h
lemma laneM {a b c k : ℕ} (hb : b < a) : (a * k + b) % (a * c) = a * (k % c) + b := by
  rw [Nat.mod_mul, Nat.mul_add_mod, Nat.mod_eq_of_lt hb, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hb, Nat.add_zero, Nat.add_comm]
section lanes
variable {l o : ℕ} (hl : ∀ i, l.testBit i = true → AA.testBit i = true) (ho : ∀ i, o.testBit i = true → l.testBit i = true)
include hl
lemma o_lt (ho : ∀ i, o.testBit i = true → l.testBit i = true) : o < 2 ^ NN :=
  lt_of_bits fun i hi => bit_lt AA_lt1 (hl i (ho i hi))
include ho
lemma U_bit {d : Bool} {v : List W} {i b : ℕ} (hb : b < NN) (h : (Nat.land (pkd d l v) (Nat.mul o RL)).testBit (NN * i + b) = true) :
    i < 12 ∧ ∃ w, Pos v w i ∧ (Nat.land (sp d l w.s) o).testBit b = true := by
  simp only [nl, Nat.testBit_and, Bool.and_eq_true] at h
  have h2 : (o * geo NN 12).testBit (NN * i + b) = true := h.2
  have hlt := bit_lt (mul_geo_lt (o_lt hl ho) 12) h2
  have hi : i < 12 := by
    by_contra hc
    have : NN * 12 ≤ NN * i := Nat.mul_le_mul_left _ (by omega)
    omega
  rw [mul_geo (o_lt hl ho) _ _ hlt, Nat.mul_add_mod, Nat.mod_eq_of_lt hb] at h2
  obtain ⟨w, hw, hs⟩ := pkd_bit hl hb h.1
  exact ⟨hi, w, hw, by simp only [nl, Nat.testBit_and, hs, h2, Bool.and_self]⟩
end lanes
lemma flagR {l o : ℕ} (hl : ∀ i, l.testBit i = true → AA.testBit i = true) (ho : ∀ i, o.testBit i = true → l.testBit i = true)
    {L : List (ℕ × ℕ)} (hL : L.all segOk = true) (hLR : L.all segOkR = true) {d : Bool} {v : List W} {i : ℕ} {s : ℕ × ℕ} (hs : s ∈ L) (hi : i < 12)
    (h : (Nat.mod (Nat.add (Nat.land (pkd d l v) (Nat.mul o RL)) AAR) PLN).testBit (NN * i + s.2) = true) :
    ∃ w b, Pos v w i ∧ s.1 < b ∧ b < s.2 ∧ (Nat.land (sp d l w.s) o).testBit b = true := by
  have h1 := List.all_eq_true.1 hL s hs
  have h2 := List.all_eq_true.1 hLR s hs
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
  simp only [segOkR, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h2
  obtain ⟨hN, h2⟩ := h2
  obtain ⟨e1, e2⟩ := h2 i hi
  have hh : (Nat.land (pkd d l v) (Nat.mul o RL) + AAR).testBit (NN * i + s.2) = true := by
    have h : ((Nat.land (pkd d l v) (Nat.mul o RL) + AAR) % 2 ^ LNN).testBit (NN * i + s.2) = true := h
    rw [Nat.testBit_mod_two_pow, Bool.and_eq_true] at h; exact h.2
  have nb : ∀ c, c < NN → AA.testBit c = false → (Nat.land (pkd d l v) (Nat.mul o RL)).testBit (NN * i + c) = false := by
    intro c hc hA
    by_contra hb
    obtain ⟨_, w, _, hw⟩ := U_bit hl ho hc (by simpa using hb)
    simp only [nl, Nat.testBit_and, Bool.and_eq_true] at hw
    rw [hl c (ho c hw.2)] at hA; simp at hA
  obtain ⟨t, t1, t2, t3⟩ := carry (u := Nat.land (pkd d l v) (Nat.mul o RL)) (A := AAR) (p := NN * i + s.1) (h := NN * i + s.2) (by omega) e1 e2
    (nb _ hN h1.2) (nb _ (by omega) h1.1.2) hh
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le (show NN * i ≤ t by omega)
  obtain ⟨_, w, hw, hb⟩ := U_bit hl ho (show b < NN by omega) t3
  exact ⟨w, b, hw, by omega, by omega, hb⟩
lemma one_bit {i : ℕ} (h : (1 : ℕ).testBit i = true) : i = 0 := by
  by_contra hc
  rw [Nat.testBit_lt_two_pow (Nat.one_lt_two_pow hc)] at h; simp at h
lemma laneC {X G p : ℕ} (hp : p < 84) (hX : X.testBit (NN * p + NN) = false) (hX2 : X.testBit (NN * p + 63) = false)
    (h : (Nat.add (Nat.land G X) MRR).testBit (NN * p + NN) = true) : ∃ b < NN, (Nat.land G X).testBit (NN * p + b) = true := by
  have hk := List.all_eq_true.1 lanes_ok p (List.mem_range.2 hp)
  simp only [laneOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hk
  obtain ⟨t, t1, t2, t3⟩ := carry (u := Nat.land G X) (A := MRR) (p := NN * p + 63) (h := NN * p + NN) (by have := HXY_lt.2.2; omega) hk.1.1.1.1.1 hk.1.1.1.1.2
    (by simp only [nl, Nat.testBit_and, hX, Bool.and_false]) (by simp only [nl, Nat.testBit_and, hX2, Bool.and_false]) h
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le (show NN * p ≤ t by omega)
  exact ⟨b, by omega, t3⟩
lemma gather {w Q E : ℕ} (hQ : Q + 1 < w) (hb : ∀ i, E.testBit i = true → i % w = 0 ∧ i < w * Q) {q : ℕ}
    (h : (E % (2 ^ (w - 1) - 1)).testBit q = true) : E.testBit (w * q) = true := by
  have key : ∀ n, ∃ s, s < 2 ^ n ∧ (E % 2 ^ (w * n)) ≡ s [MOD 2 ^ (w - 1) - 1] ∧ ∀ q, s.testBit q = true → E.testBit (w * q) = true := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp, by rw [Nat.mul_zero, pow_zero, Nat.mod_one], by simp⟩
    | succ n ih =>
      obtain ⟨s, h1, h2, h3⟩ := ih
      have hd : E / 2 ^ (w * n) % 2 ^ w = (E.testBit (w * n)).toNat := by
        apply Nat.eq_of_testBit_eq; intro i
        rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
        by_cases hi : i = 0
        · subst hi; cases hE : E.testBit (w * n) <;> simp [hE, show 0 < w by omega]
        · have h0 : E.testBit (w * n + i) = true → ¬ i < w := by
            intro he hlt
            have := (hb _ he).1
            rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt] at this; exact hi this
          have h1 : ((E.testBit (w * n)).toNat).testBit i = false := by
            cases E.testBit (w * n)
            · simp
            · by_contra hc
              exact hi (one_bit (by simpa using hc))
          rw [h1]
          by_cases hlt : i < w
          · have : E.testBit (w * n + i) = false := by
              by_contra hc; exact h0 (by simpa using hc) hlt
            rw [Nat.add_comm] at this
            simp [this]
          · simp [hlt]
      have he : E % 2 ^ (w * (n + 1)) = 2 ^ (w * n) * (E.testBit (w * n)).toNat + E % 2 ^ (w * n) := by
        rw [Nat.mul_succ, pow_add, Nat.mod_mul, hd, Nat.add_comm]
      refine ⟨2 ^ n * (E.testBit (w * n)).toNat + s, ?_, ?_, ?_⟩
      · rw [pow_succ]
        cases E.testBit (w * n)
        · simp; omega
        · simp; omega
      · rw [he]
        refine Nat.ModEq.add (Nat.ModEq.mul_right _ ?_) h2
        have e1 : 2 ^ (w - 1) ≡ 1 [MOD 2 ^ (w - 1) - 1] := by
          have : 1 ≤ 2 ^ (w - 1) := Nat.one_le_two_pow
          exact ((Nat.modEq_iff_dvd' this).2 dvd_rfl).symm
        calc 2 ^ (w * n) = 2 ^ ((w - 1) * n + n) := by congr 1; rw [← Nat.succ_mul]; congr 1; omega
          _ = (2 ^ (w - 1)) ^ n * 2 ^ n := by rw [pow_add, pow_mul]
          _ ≡ 1 ^ n * 2 ^ n [MOD _] := Nat.ModEq.mul_right _ (e1.pow n)
          _ = 2 ^ n := by simp
      · intro q hq
        rw [Nat.testBit_two_pow_mul_add _ h1] at hq
        split_ifs at hq with hlt
        · exact h3 q hq
        · by_cases h0 : q - n = 0
          · have : q = n := by omega
            subst this
            rw [h0] at hq
            cases hE : E.testBit (w * q) with
            | true => rfl
            | false => rw [hE] at hq; simp at hq
          · exfalso
            cases hE : E.testBit (w * n) with
            | true =>
              rw [hE] at hq
              exact h0 (one_bit hq)
            | false => rw [hE] at hq; simp at hq
  obtain ⟨s, h1, h2, h3⟩ := key Q
  have hE : E < 2 ^ (w * Q) := lt_of_bits fun i hi => (hb i hi).2
  rw [Nat.mod_eq_of_lt hE] at h2
  have hs : s < 2 ^ (w - 1) - 1 := by
    have e2 : 2 ^ Q * 2 ≤ 2 ^ (w - 1) := by rw [← pow_succ]; exact Nat.pow_le_pow_right (by omega) (by omega)
    rcases Nat.eq_zero_or_pos Q with rfl | hQ0
    · have : 2 ^ 1 ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      simp at h1; omega
    · have : 2 ^ 1 ≤ 2 ^ Q := Nat.pow_le_pow_right (by omega) hQ0
      omega
  have : E % (2 ^ (w - 1) - 1) = s := by
    have := h2
    unfold Nat.ModEq at this
    rw [this, Nat.mod_eq_of_lt hs]
  rw [this] at h
  exact h3 q h
lemma edg_spec {l o : ℕ} (hl : ∀ i, l.testBit i = true → AA.testBit i = true) (ho : ∀ i, o.testBit i = true → l.testBit i = true)
    {d : Bool} {v : List W} {p : ℕ} (h : (edg d l o v).testBit p = true) :
    12 ≤ p ∧ p < 84 ∧ ∃ a b, Pos v a (p % 13) ∧ Pos v b (p % 12) ∧ Hq d l o a.s b.s := by
  obtain ⟨hHX, hHY, hN⟩ := HXY_lt
  set F := Nat.mod (Nat.add (Nat.land (pkd d l v) (Nat.mul o RL)) AAR) PLN with hF
  have hF1 : F < 2 ^ (NN * 12) := by
    have e0 : PLN = 2 ^ (NN * 12) := PLN_eq
    rw [hF, ← e0]; exact Nat.mod_lt _ (by rw [e0]; exact Nat.two_pow_pos _)
  set G := Nat.land (dbl LN4 (dbl LN2 (dbl LNN F))) (dbl LM4 (dbl LM2 (dbl LM1 F))) with hG
  set E := Nat.land (Nat.land (Nat.add (Nat.land G HXR) MRR) (Nat.add (Nat.land G HYR) MRR)) TOPR with hE
  have hbits : ∀ i, E.testBit i = true → i % NN = 0 ∧ i < NN * 85 ∧ 13 * NN ≤ i := by
    intro i hi
    have hT : (geo NN 72 <<< (13 * NN)).testBit i = true := by
      rw [hE, nl, Nat.testBit_and, Bool.and_eq_true] at hi; exact hi.2
    rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hT
    obtain ⟨t1, t2⟩ := hT
    have t2 : (1 * geo NN 72).testBit (i - 13 * NN) = true := by rwa [one_mul]
    have h1 : 1 < 2 ^ NN := Nat.one_lt_two_pow (by omega)
    have hlt := bit_lt (mul_geo_lt h1 72) t2
    rw [mul_geo h1 _ _ hlt] at t2
    have t2 := one_bit t2
    refine ⟨?_, by omega, t1⟩
    have : (i - 13 * NN + NN * 13) % NN = 0 := by rw [Nat.add_mul_mod_self_left]; exact t2
    rwa [Nat.mul_comm NN, Nat.sub_add_cancel t1] at this
  have h : ((E % GMD) >>> 1).testBit p = true := h
  rw [Nat.testBit_shiftRight, GMD_eq] at h
  have hp := gather (Q := 85) (by omega) (fun i hi => ⟨(hbits i hi).1, (hbits i hi).2.1⟩) h
  obtain ⟨_, b2, b3⟩ := hbits _ hp
  have p1 : 12 ≤ p := by
    by_contra hc
    have : NN * (1 + p) ≤ NN * 12 := Nat.mul_le_mul_left _ (by omega)
    omega
  have p2 : p < 84 := by
    by_contra hc
    have : NN * 85 ≤ NN * (1 + p) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hp : E.testBit (NN * p + NN) = true := by rwa [show NN * p + NN = NN * (1 + p) by ring]
  rw [hE, nl, nl, Nat.testBit_and, Nat.testBit_and, Bool.and_eq_true, Bool.and_eq_true] at hp
  obtain ⟨⟨hx, hy⟩, _⟩ := hp
  have hk := List.all_eq_true.1 lanes_ok p (List.mem_range.2 p2)
  simp only [laneOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hk
  obtain ⟨x, hx1, hx2⟩ := laneC p2 hk.1.1.1.2 hk.1.1.2 hx
  obtain ⟨y, hy1, hy2⟩ := laneC p2 hk.1.2 hk.2 hy
  have gb : ∀ b, b < NN → G.testBit (NN * p + b) = true → F.testBit (NN * (p % 12) + b) = true ∧ F.testBit (NN * (p % 13) + b) = true := by
    intro b hb hgb
    rw [hG, nl, Nat.testBit_and, Bool.and_eq_true] at hgb
    obtain ⟨g1, g2⟩ := hgb
    have hlt : NN * p + b < NN * 84 := by
      have : NN * (p + 1) ≤ NN * 84 := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ] at this; omega
    have g1 : (dbl (4 * (NN * 12)) (dbl (2 * (NN * 12)) (dbl (NN * 12) F))).testBit (NN * p + b) = true := by
      have e1 : LN4 = 4 * (NN * 12) := by change 48 * NN = _; ring
      have e2 : LN2 = 2 * (NN * 12) := by change 24 * NN = _; ring
      have e3 : LNN = NN * 12 := by change 12 * NN = _; ring
      rwa [e1, e2, e3] at g1
    have g2 : (dbl (4 * (NN * 13)) (dbl (2 * (NN * 13)) (dbl (NN * 13) F))).testBit (NN * p + b) = true := by
      have e1 : LM4 = 4 * (NN * 13) := by change 52 * NN = _; ring
      have e2 : LM2 = 2 * (NN * 13) := by change 26 * NN = _; ring
      have e3 : LM1 = NN * 13 := by change 13 * NN = _; ring
      rwa [e1, e2, e3] at g2
    rw [rep3 hF1 (by omega), laneM hb] at g1
    rw [rep3 (lt_of_lt_of_le hF1 (Nat.pow_le_pow_right (by omega) (by omega))) (by omega), laneM hb] at g2
    exact ⟨g1, g2⟩
  have big : ∀ {H : ℕ}, H < 2 ^ NN → ∀ {b : ℕ}, b < NN → (Nat.mul H (geo NN 84)).testBit (NN * p + b) = true → H.testBit b = true := by
    intro H hH b hb hh
    have hh : (H * geo NN 84).testBit (NN * p + b) = true := hh
    rw [mul_geo hH _ _ (bit_lt (mul_geo_lt hH 84) hh), Nat.mul_add_mod, Nat.mod_eq_of_lt hb] at hh
    exact hh
  have fin : ∀ {L : List (ℕ × ℕ)} {H : ℕ}, L.all segOk = true → L.all segOkR = true → H < 2 ^ NN → H = bitsOf L → ∀ {x : ℕ}, x < NN →
      (Nat.land G (Nat.mul H (geo NN 84))).testBit (NN * p + x) = true → ∃ a b, Pos v a (p % 13) ∧ Pos v b (p % 12) ∧
      ∃ s ∈ L, ∃ i1 i2, s.1 < i1 ∧ i1 < s.2 ∧ s.1 < i2 ∧ i2 < s.2 ∧ (Nat.land (sp d l a.s) o).testBit i1 = true ∧ (Nat.land (sp d l b.s) o).testBit i2 = true := by
    intro L H q1 q2 q3 q4 x q5 q6
    rw [nl, Nat.testBit_and, Bool.and_eq_true] at q6
    obtain ⟨g1, g2⟩ := gb x q5 q6.1
    have hb := big q3 q5 q6.2
    rw [q4] at hb
    obtain ⟨s, hs, rfl⟩ := bitsOf_bit hb
    obtain ⟨b, i2, w1, w2, w3, w4⟩ := flagR hl ho q1 q2 hs (Nat.mod_lt _ (by omega)) g1
    have hp13 : p % 13 < 12 := by
      by_contra hc
      have e : p % 13 = 12 := by omega
      rw [e] at g2
      have := bit_lt hF1 g2
      omega
    obtain ⟨a, i1, v1, v2, v3, v4⟩ := flagR hl ho q1 q2 hs hp13 g2
    exact ⟨a, b, v1, w1, s, hs, i1, i2, v2, v3, w2, w3, v4, w4⟩
  obtain ⟨a, b, r1, r2, r3⟩ := fin segX_ok segXR_ok hHX HX_eq hx1 hx2
  obtain ⟨a', b', r4, r5, r6⟩ := fin segY_ok segYR_ok hHY HY_eq hy1 hy2
  obtain rfl := r4.uniq r1
  obtain rfl := r5.uniq r2
  exact ⟨p1, p2, a', b', r1, r2, r3, r6⟩
lemma f12_bit {w x : ℕ} (h : (f12 w).testBit x = true) : x < 12 ∧ ∃ k < 8, w.testBit (12 * k + x) = true := by
  have h : ((((w ||| w >>> 48) ||| (w ||| w >>> 48) >>> 24) ||| ((w ||| w >>> 48) ||| (w ||| w >>> 48) >>> 24) >>> 12) &&& (2 ^ 12 - 1)).testBit x = true := h
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.2, ?_⟩
  have h := h.1
  simp only [Nat.testBit_or, Nat.testBit_shiftRight, Bool.or_eq_true] at h
  rcases h with ((h | h) | (h | h)) | ((h | h) | (h | h))
  · exact ⟨0, by omega, by simpa using h⟩
  · exact ⟨4, by omega, by convert h using 2⟩
  · exact ⟨2, by omega, by convert h using 2⟩
  · exact ⟨6, by omega, by convert h using 2; omega⟩
  · exact ⟨1, by omega, by convert h using 2⟩
  · exact ⟨5, by omega, by convert h using 2; omega⟩
  · exact ⟨3, by omega, by convert h using 2; omega⟩
  · exact ⟨7, by omega, by convert h using 2; omega⟩
lemma f13_bit {w x : ℕ} (h : (f13 w).testBit x = true) : x < 12 ∧ ∃ k < 8, w.testBit (13 * k + x) = true := by
  have h : ((((w ||| w >>> 52) ||| (w ||| w >>> 52) >>> 26) ||| ((w ||| w >>> 52) ||| (w ||| w >>> 52) >>> 26) >>> 13) &&& (2 ^ 12 - 1)).testBit x = true := h
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.2, ?_⟩
  have h := h.1
  simp only [Nat.testBit_or, Nat.testBit_shiftRight, Bool.or_eq_true] at h
  rcases h with ((h | h) | (h | h)) | ((h | h) | (h | h))
  · exact ⟨0, by omega, by simpa using h⟩
  · exact ⟨4, by omega, by convert h using 2⟩
  · exact ⟨2, by omega, by convert h using 2⟩
  · exact ⟨6, by omega, by convert h using 2; omega⟩
  · exact ⟨1, by omega, by convert h using 2⟩
  · exact ⟨5, by omega, by convert h using 2; omega⟩
  · exact ⟨3, by omega, by convert h using 2; omega⟩
  · exact ⟨7, by omega, by convert h using 2; omega⟩
lemma Adj.symm {e x y : ℕ} (h : Adj e x y) : Adj e y x := by
  obtain ⟨p, hp, h⟩ := h; exact ⟨p, hp, h.symm⟩
lemma Adj.ne {e x y : ℕ} (he : Eb e) (h : Adj e x y) : x ≠ y := by
  obtain ⟨p, hp, h⟩ := h
  obtain ⟨h1, h2⟩ := he p hp
  have key : ∀ p < 84, 12 ≤ p → p % 13 ≠ p % 12 := by decide
  have := key p h2 h1
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact this
  · exact this.symm
lemma nbr_adj {e S x : ℕ} (he : Eb e) (hS : S < 2 ^ 12) (h : (nbr e S).testBit x = true) : x < 12 ∧ ∃ y, S.testBit y = true ∧ Adj e x y := by
  have h : (f12 (e &&& S * 302268352895954163081217) ||| f13 (e &&& S * 4723519685917965029377)).testBit x = true := h
  rw [Nat.testBit_or, Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨h1, k, hk, h2⟩ := f12_bit h
    rw [Nat.testBit_and, Bool.and_eq_true, ← geo13] at h2
    have hp := he _ h2.1
    rw [mul_geo (lt_of_lt_of_le hS (by norm_num)) 7 _ (by omega)] at h2
    exact ⟨h1, _, h2.2, _, h2.1, Or.inr ⟨rfl, by omega⟩⟩
  · obtain ⟨h1, k, hk, h2⟩ := f13_bit h
    rw [Nat.testBit_and, Bool.and_eq_true, ← geo12] at h2
    have hp := he _ h2.1
    rw [mul_geo hS 7 _ (by omega)] at h2
    exact ⟨h1, _, h2.2, _, h2.1, Or.inl ⟨by omega, rfl⟩⟩
lemma nbr_lt {e S : ℕ} : nbr e S < 2 ^ 12 := by
  refine lt_of_bits fun i hi => ?_
  have h : (f12 (e &&& S * 302268352895954163081217) ||| f13 (e &&& S * 4723519685917965029377)).testBit i = true := hi
  rw [Nat.testBit_or, Bool.or_eq_true] at h
  rcases h with h | h
  · exact (f12_bit h).1
  · exact (f13_bit h).1
lemma bfs_ok {e : ℕ} (he : Eb e) {c : ℕ → Bool} (hc : Pc e c) {κ : Bool} {k : ℕ → Bool} (hk : ∀ C, k C = false) :
    ∀ fuel A B, A < 2 ^ 12 → B < 2 ^ 12 → (∀ y, A.testBit y = true → c y = κ) → (∀ y, B.testBit y = true → c y = !κ) → bfs e fuel A B k = false := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro A B hA hB cA cB
    change (st (Nat.lor A (nbr e B)) fun a => st (Nat.lor B (nbr e a)) fun b => Bool.rec (motive := fun _ => Bool) true
      (Bool.rec (motive := fun _ => Bool) (bfs e fuel a b k) (k (Nat.lor a b)) (Nat.beq (Nat.lor A B) (Nat.lor a b))) (Nat.beq (Nat.land a b) 0)) = false
    rw [st_eq, st_eq, bR, bR]
    set a := Nat.lor A (nbr e B) with ha
    set b := Nat.lor B (nbr e a) with hb
    have ha1 : a < 2 ^ 12 := by rw [ha]; exact Nat.or_lt_two_pow hA nbr_lt
    have hb1 : b < 2 ^ 12 := by rw [hb]; exact Nat.or_lt_two_pow hB nbr_lt
    have ca : ∀ y, a.testBit y = true → c y = κ := by
      intro y hy
      rw [ha, no, Nat.testBit_or, Bool.or_eq_true] at hy
      rcases hy with hy | hy
      · exact cA y hy
      · obtain ⟨_, z, hz, hadj⟩ := nbr_adj he hB hy
        have := hc _ _ hadj; rw [cB z hz] at this
        clear hk ih
        revert this; generalize c y = q; cases q <;> cases κ <;> simp
    have cb : ∀ y, b.testBit y = true → c y = !κ := by
      intro y hy
      rw [hb, no, Nat.testBit_or, Bool.or_eq_true] at hy
      rcases hy with hy | hy
      · exact cB y hy
      · obtain ⟨_, z, hz, hadj⟩ := nbr_adj he ha1 hy
        have := hc _ _ hadj; rw [ca z hz] at this
        clear hk ih
        revert this; generalize c y = q; cases q <;> cases κ <;> simp
    have h0 : Nat.beq (Nat.land a b) 0 = true := by
      rw [Nat.beq_eq]
      by_contra hne
      obtain ⟨y, hy⟩ := Nat.exists_testBit_of_ne_zero hne
      rw [nl, Nat.testBit_and, Bool.and_eq_true] at hy
      have e1 := ca y hy.1; have e2 := cb y hy.2
      rw [e1] at e2; cases κ <;> simp at e2
    rw [h0, cond_true, ih a b ha1 hb1 ca cb, hk]
    cases Nat.beq (Nat.lor A B) (Nat.lor a b) <;> rfl
lemma pow_bit {j y : ℕ} (h : (2 ^ j).testBit y = true) : y = j := by
  rw [Nat.testBit_two_pow, decide_eq_true_eq] at h; exact h.symm
lemma nonb_ok {e : ℕ} (he : Eb e) {c : ℕ → Bool} (hc : Pc e c) : ∀ fuel r, nonb e fuel r = false := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro r
    change (Bool.rec (motive := fun _ => Bool) (bfs e 12 (Nat.gcd r 2048) 0 (fun c => nonb e fuel (Nat.sub r (Nat.land r c)))) false (Nat.beq r 0)) = false
    rw [bR]
    have : bfs e 12 (Nat.gcd r 2048) 0 (fun c => nonb e fuel (Nat.sub r (Nat.land r c))) = false := by
      obtain ⟨j, hj, hg⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.gcd r 2048 ∣ 2 ^ 11 from Nat.gcd_dvd_right r 2048)
      rw [hg]
      refine bfs_ok he hc (κ := c j) (fun C => ih _) 12 _ _ (Nat.pow_lt_pow_right (by omega) (by omega)) (by norm_num) ?_ (by simp)
      intro y hy; rw [pow_bit hy]
    rw [this]; cases Nat.beq r 0 <;> rfl
lemma nonbip_ok {e : ℕ} (he : Eb e) {c : ℕ → Bool} (hc : Pc e c) : nonbip e = false := nonb_ok he hc _ _
lemma del_bit {e j p : ℕ} (he : Eb e) (h : (del e (2 ^ j)).testBit p = true) : e.testBit p = true ∧ p % 13 ≠ j ∧ p % 12 ≠ j := by
  have h : ((e ||| tch (2 ^ j)) ^^^ tch (2 ^ j)).testBit p = true := h
  rw [Nat.testBit_xor, Nat.testBit_or] at h
  have hT : (tch (2 ^ j)).testBit p = false := by
    cases hb : (tch (2 ^ j)).testBit p with
    | false => rfl
    | true => rw [hb] at h; simp at h
  rw [hT] at h
  have hep : e.testBit p = true := by simpa using h
  have hp := he p hep
  have hT : (2 ^ j * 302268352895954163081217 ||| 2 ^ j * 4723519685917965029377).testBit p = false := hT
  rw [Nat.testBit_or, Bool.or_eq_false_iff] at hT
  refine ⟨hep, fun hj => ?_, fun hj => ?_⟩
  · have h1 := hT.1
    have hlt : j < 13 := by omega
    rw [← geo13, mul_geo (Nat.pow_lt_pow_right (by omega) hlt) 7 _ (by omega), hj, Nat.testBit_two_pow_self] at h1
    simp at h1
  · have h1 := hT.2
    have hlt : j < 12 := by omega
    rw [← geo12, mul_geo (Nat.pow_lt_pow_right (by omega) hlt) 7 _ (by omega), hj, Nat.testBit_two_pow_self] at h1
    simp at h1
lemma del_Eb {e j : ℕ} (he : Eb e) : Eb (del e (2 ^ j)) := fun p hp => he p (del_bit he hp).1
lemma del_adj {e j x y : ℕ} (he : Eb e) (h : Adj (del e (2 ^ j)) x y) : Adj e x y ∧ x ≠ j ∧ y ≠ j := by
  obtain ⟨p, hp, h⟩ := h
  obtain ⟨h1, h2, h3⟩ := del_bit he hp
  refine ⟨⟨p, h1, h⟩, ?_⟩
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨h2, h3⟩
  · exact ⟨h3, h2⟩
lemma ne0_adj {e : ℕ} (h : ne0 e = true) : ∃ x y, Adj e x y := by
  unfold ne0 at h
  rw [bR] at h
  cases h0 : Nat.beq e 0 with
  | true => rw [h0] at h; simp at h
  | false =>
    have hne : e ≠ 0 := fun e0 => by rw [e0] at h0; simp at h0
    obtain ⟨p, hp⟩ := Nat.exists_testBit_of_ne_zero hne
    exact ⟨_, _, p, hp, Or.inl ⟨rfl, rfl⟩⟩
lemma gcd_bit {M : ℕ} (h0 : M ≠ 0) (h1 : M < 2 ^ 12) : ∃ k, k < 12 ∧ Nat.gcd M 4096 = 2 ^ k ∧ M.testBit k = true := by
  obtain ⟨k, hk, hg⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.gcd M 4096 ∣ 2 ^ 12 from Nat.gcd_dvd_right M 4096)
  have hd : 2 ^ k ∣ M := hg ▸ Nat.gcd_dvd_left M 4096
  have hk12 : k < 12 := by
    by_contra hc
    have : 2 ^ 12 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd
    omega
  refine ⟨k, hk12, hg, ?_⟩
  by_contra hb
  have hb : M.testBit k = false := by simpa using hb
  have h2 : 2 ^ (k + 1) ∣ M := by
    obtain ⟨q, rfl⟩ := hd
    have hq : (2 ^ k * q + 0).testBit k = q.testBit 0 := by
      rw [Nat.testBit_two_pow_mul_add _ (by positivity)]; simp
    rw [Nat.add_zero] at hq
    rw [hq, Nat.testBit_zero] at hb
    have : q % 2 = 0 := by simp at hb; omega
    obtain ⟨r, rfl⟩ := Nat.dvd_of_mod_eq_zero this
    exact ⟨r, by rw [pow_succ]; ring⟩
  have h3 : 2 ^ (k + 1) ∣ Nat.gcd M 4096 := Nat.dvd_gcd h2 (by
    change 2 ^ (k + 1) ∣ 2 ^ 12
    exact pow_dvd_pow 2 (by omega))
  rw [hg] at h3
  have := Nat.le_of_dvd (by positivity) h3
  rw [pow_succ] at this
  have : 0 < 2 ^ k := by positivity
  omega
lemma bRn (c : Bool) (e t : ℕ) : (Bool.rec (motive := fun _ => ℕ) e t c : ℕ) = bif c then t else e := by cases c <;> rfl
lemma tri_ok {e : ℕ} (he : Eb e) : ∀ fuel r, tri e fuel r = 0 ∨ ∃ x y z, Adj e x y ∧ Adj e x z ∧ Adj e y z ∧ tri e fuel r = 2 ^ x ||| 2 ^ y ||| 2 ^ z := by
  intro fuel
  induction fuel with
  | zero => intro r; exact Or.inl rfl
  | succ fuel ih =>
    intro r
    have e0 : tri e (fuel + 1) r = bif Nat.beq r 0 then 0 else tri1 e (Nat.gcd r 2048) (tri e fuel (Nat.sub r (Nat.gcd r 2048))) := by
      change Bool.rec (motive := fun _ => Nat) (tri1 e (Nat.gcd r 2048) (tri e fuel (Nat.sub r (Nat.gcd r 2048)))) 0 (Nat.beq r 0) = _
      rw [bRn]
    rw [e0]
    cases hr : Nat.beq r 0 with
    | true => exact Or.inl rfl
    | false =>
      rw [cond_false]
      obtain ⟨x, hx, hgx⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show Nat.gcd r 2048 ∣ 2 ^ 11 from Nat.gcd_dvd_right r 2048)
      have hrest := ih (Nat.sub r (Nat.gcd r 2048))
      generalize tri e fuel (Nat.sub r (Nat.gcd r 2048)) = rest at hrest ⊢
      rw [hgx]
      have hi : 2 ^ x < 2 ^ 12 := Nat.pow_lt_pow_right (by omega) (by omega)
      simp only [tri1, tri2, tri3, tri4, tri5, bRn]
      cases hM : Nat.beq (Nat.land (nbr e (nbr e (2 ^ x))) (nbr e (2 ^ x))) 0 with
      | true => rw [cond_true]; exact hrest
      | false =>
        rw [cond_false]
        have hM0 : nbr e (nbr e (2 ^ x)) &&& nbr e (2 ^ x) ≠ 0 := fun h => by rw [nl, h] at hM; simp at hM
        obtain ⟨y, hy, hgy, hby⟩ := gcd_bit hM0 (lt_of_le_of_lt Nat.and_le_left nbr_lt)
        rw [Nat.testBit_and, Bool.and_eq_true] at hby
        obtain ⟨_, x', hx', axy⟩ := nbr_adj he hi hby.2
        obtain rfl := pow_bit hx'
        have hgy' : Nat.gcd (Nat.land (nbr e (nbr e (2 ^ x'))) (nbr e (2 ^ x'))) 4096 = 2 ^ y := hgy
        rw [hgy']
        cases hL : Nat.beq (Nat.land (nbr e (2 ^ y)) (nbr e (2 ^ x'))) 0 with
        | true => rw [cond_true]; exact hrest
        | false =>
          rw [cond_false]
          have hz0 : nbr e (2 ^ y) &&& nbr e (2 ^ x') ≠ 0 := fun h => by rw [nl, h] at hL; simp at hL
          obtain ⟨z, hz, hgz, hbz⟩ := gcd_bit hz0 (lt_of_le_of_lt Nat.and_le_left nbr_lt)
          rw [Nat.testBit_and, Bool.and_eq_true] at hbz
          obtain ⟨_, y', hy', azy⟩ := nbr_adj he (Nat.pow_lt_pow_right (by omega) hy) hbz.1
          obtain rfl := pow_bit hy'
          obtain ⟨_, x'', hx'', azx⟩ := nbr_adj he hi hbz.2
          obtain rfl := pow_bit hx''
          have hgz' : Nat.gcd (Nat.land (nbr e (2 ^ y')) (nbr e (2 ^ x''))) 4096 = 2 ^ z := hgz
          exact Or.inr ⟨x'', y', z, axy.symm, azx.symm, azy.symm, by rw [hgz']; rfl⟩
lemma pos_cons {x w : W} {t : List W} {i : ℕ} (h : Pos (x :: t) w i) : (w = x ∧ i = t.length) ∨ Pos t w i := by
  obtain ⟨pre, t', e, rfl⟩ := h
  cases pre with
  | nil => simp only [List.nil_append, List.cons.injEq] at e; exact Or.inl ⟨e.1.symm, by rw [e.2]⟩
  | cons y pre => simp only [List.cons_append, List.cons.injEq] at e; exact Or.inr ⟨pre, t', e.2, rfl⟩
lemma pos_inj {v : List W} (hv : (v.map W.s).Nodup) {a b : W} {i j : ℕ} (ha : Pos v a i) (hb : Pos v b j) (e : a.s = b.s) : i = j := by
  induction v with
  | nil => obtain ⟨p, t, h, _⟩ := ha; simp at h
  | cons x t ih =>
    rw [List.map_cons, List.nodup_cons] at hv
    rcases pos_cons ha with ⟨rfl, rfl⟩ | ha' <;> rcases pos_cons hb with ⟨rfl, rfl⟩ | hb'
    · rfl
    · exact absurd (List.mem_map.2 ⟨b, hb'.mem, e.symm⟩) hv.1
    · exact absurd (List.mem_map.2 ⟨a, ha'.mem, e⟩) hv.1
    · exact ih hv.2 ha' hb'
lemma pos_ex {v : List W} {w : W} (h : w ∈ v) : ∃ i, Pos v w i := by
  obtain ⟨p, t, rfl⟩ := List.append_of_mem h
  exact ⟨_, p, t, rfl, rfl⟩
lemma Eb_edg {l o : ℕ} (hl : ∀ i, l.testBit i = true → AA.testBit i = true) (ho : ∀ i, o.testBit i = true → l.testBit i = true)
    {d : Bool} {v : List W} : Eb (edg d l o v) := fun p hp => by
  obtain ⟨h1, h2, _⟩ := edg_spec hl ho hp; exact ⟨h1, h2⟩
lemma he' (t : ℕ) : pos' t = true ∨ t = 0 := by
  rcases Nat.eq_zero_or_pos t with h | h
  · exact Or.inr h
  · exact Or.inl (by simp [pos', h])
section keep
variable {m T : ℕ}
lemma keep_col {d : Bool} {a b k0 t : ℕ} {S S1 : Finset ℕ} (hb : Bi R d a b S S1) (hl : Live R m T k0 t S1) (hm : Min R m T (k0 + 1) t S) (ha : a ∈ S1) (hbn : b ∉ S1) :
    ∃ (x : ℕ) (g : ℕ → ℕ), S.card + t + x = k0 + 1 ∧ (∀ p ∈ S, p ≠ a → g p ≤ x) ∧
      ∀ p ∈ S, ∀ q ∈ S, p ≠ a → q ≠ a → p ≠ q → Ht NN m T (pos' t) S p q → g p ≠ g q := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := id hb
  have hfS : op d a b ∉ insert a (insert b U) := fun h => hb.fresh hl hm.2 (sub_C _ _ (by simpa using h))
  have hf : op d a b ∉ U := fun h => hfS (by simp [h])
  have haU : a ∈ U := by
    rcases Finset.mem_insert.1 ha with h | h
    · exact absurd (show op d a b ∈ insert a (insert b U) by rw [← h]; simp) hfS
    · exact h
  have hbU : b ∉ U := fun h => hbn (by simp [h])
  have eS : insert a (insert b U) = insert b U := Finset.insert_eq_of_mem (by simp [haU])
  obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := pos' t) hl (hb.min hl hm.2).2 (he' t)
  rw [Finset.card_insert_of_notMem hf] at h1
  refine ⟨x, fun p => f (if p = a ∨ p = b then op d a b else p), ?_, fun p hp _ => h2 _ (phi_mem hp), ?_⟩
  · rw [eS, Finset.card_insert_of_notMem hbU]; exact h1
  · intro p hp q hq hpa hqa hpq hh
    have hh' := ht_bi hab (Or.inr rfl) hl hp hq (fun e => absurd e hpa) (fun _ => hbU) (fun e => absurd e hqa) (fun _ => hbU) hh
    refine h3 _ (phi_mem hp) _ (phi_mem hq) ?_ hh'
    simp only [hpa, hqa, false_or]
    have h1' : p = b ∨ p ∈ U := by simp at hp; grind
    have h2' : q = b ∨ q ∈ U := by simp at hq; grind
    split_ifs with r s s
    · exact absurd (r.trans s.symm) hpq
    · intro e; exact hf (e ▸ h2'.resolve_left s)
    · intro e; exact hf (e ▸ h1'.resolve_left r)
    · exact hpq
lemma keep_col2 {d : Bool} {a b k0 t : ℕ} {S S1 : Finset ℕ} (hb : Bi R d a b S S1) (hl : Live R m T k0 t S1) (hm : Min R m T (k0 + 1) t S) (ha : a ∈ S1) (hbn : b ∈ S1) :
    ∃ (x : ℕ) (g : ℕ → ℕ), S.card + t + x + 1 = k0 + 1 ∧ (∀ p ∈ S, p ≠ a → p ≠ b → g p ≤ x) ∧
      ∀ p ∈ S, ∀ q ∈ S, p ≠ a → p ≠ b → q ≠ a → q ≠ b → p ≠ q → Ht NN m T (pos' t) S p q → g p ≠ g q := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := id hb
  have hfS : op d a b ∉ insert a (insert b U) := fun h => hb.fresh hl hm.2 (sub_C _ _ (by simpa using h))
  have hf : op d a b ∉ U := fun h => hfS (by simp [h])
  have haU : a ∈ U := by
    rcases Finset.mem_insert.1 ha with h | h
    · exact absurd (show op d a b ∈ insert a (insert b U) by rw [← h]; simp) hfS
    · exact h
  have hbU : b ∈ U := by
    rcases Finset.mem_insert.1 hbn with h | h
    · exact absurd (show op d a b ∈ insert a (insert b U) by rw [← h]; simp) hfS
    · exact h
  have eS : insert a (insert b U) = U := by
    rw [Finset.insert_eq_of_mem (by simp [haU]), Finset.insert_eq_of_mem hbU]
  obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := pos' t) hl (hb.min hl hm.2).2 (he' t)
  rw [Finset.card_insert_of_notMem hf] at h1
  refine ⟨x, f, by rw [eS]; omega, ?_, ?_⟩
  · intro p hp hpa hpb
    have := h2 _ (phi_mem (g := op d a b) hp)
    simpa [hpa, hpb] using this
  · intro p hp q hq hpa hpb hqa hqb hpq hh
    have hh' := ht_bi hab (Or.inr rfl) hl hp hq (fun e => absurd e hpa) (fun e => absurd e hpb) (fun e => absurd e hqa) (fun e => absurd e hqb) hh
    have m1 := phi_mem (g := op d a b) hp
    have m2 := phi_mem (g := op d a b) hq
    simp only [hpa, hpb, hqa, hqb, or_self, if_false] at hh' m1 m2
    exact h3 _ m1 _ m2 hpq hh'
end keep
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma Hq_ht {v : List W} {S : Finset ℕ} {d : Bool} (hr : Rep v S) (hgd : ∀ w ∈ v, Good l w.s) {a b : W} (ha : a ∈ v) (hb : b ∈ v)
    (h : Hq false l (wst d l v) a.s b.s) : Ht NN m T d S a.s b.s := by
  obtain ⟨⟨s, hs1, i1, i2, a1, a2, b1, b2, a3, b3⟩, ⟨s', hs2, j1, j2, c1, c2, d1, d2, c3, d3⟩⟩ := h
  have uq : ∀ {w : W} {i : ℕ}, w ∈ v → (Nat.land (sp false l w.s) (wst d l v)).testBit i = true →
      l.testBit i = true ∧ Uq NN d S w.s i ∧ w.s.testBit i = true := by
    intro w i hw hi
    have hi2 := hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi2
    obtain ⟨⟨hl, hs⟩, ho⟩ := hi2
    have hsd : sepb NN d w.s i = true := by
      cases d
      · exact hs
      · exact sepb_weak _ hs
    obtain ⟨q1, q2⟩ := uq_of hr hw (d := d) (l := l) (i := i) (by
      simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true]; exact ⟨⟨hl, hsd⟩, ho⟩)
    refine ⟨q1, q2, ?_⟩
    revert hs; simp only [sepb, cond_false]; cases w.s.testBit i <;> simp
  obtain ⟨l1, u1, p1⟩ := uq ha a3
  obtain ⟨l2, u2, p2⟩ := uq hb b3
  obtain ⟨l3, u3, p3⟩ := uq ha c3
  obtain ⟨l4, u4, p4⟩ := uq hb d3
  refine ⟨i1, i2, j1, j2, (X.lg _ l1).1, (X.lg _ l2).1, (X.lg _ l3).1, (X.lg _ l4).1, ?_, ?_, u1, u2, u3, u4, by rw [p1, p3], by rw [p2, p4]⟩
  · intro w hw; obtain ⟨w', hw', rfl⟩ := hr.mem.1 hw
    exact (hgd w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
  · intro w hw; obtain ⟨w', hw', rfl⟩ := hr.mem.1 hw
    exact (hgd w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
lemma Hq_rect {v : List W} {S : Finset ℕ} {t k k' : ℕ} (hr : Rep v S) (hgd : ∀ w ∈ v, Good l w.s) (hm : Min R m T k' t S) (hk : k' ≤ k)
    (hn : v.length + t = k + 1) {a b : W} (ha : a ∈ v) (hb : b ∈ v) (hab : a.s ≠ b.s) (h : Hq (pos' t) l (wst (pos' t) l v) a.s b.s) : False := by
  obtain ⟨⟨s, hs1, i1, i2, a1, a2, b1, b2, a3, b3⟩, ⟨s', hs2, j1, j2, c1, c2, d1, d2, c3, d3⟩⟩ := h
  have hs := hm.size
  have hcard := hr.card
  have hpos : 0 < S.card := hm.1.pos
  have htight : S.card + t = k' + 1 := by omega
  obtain ⟨l1, u1⟩ := uq_of hr ha a3
  obtain ⟨l2, u2⟩ := uq_of hr hb b3
  obtain ⟨l3, u3⟩ := uq_of hr ha c3
  obtain ⟨l4, u4⟩ := uq_of hr hb d3
  have g1 : ∀ w ∈ S, w.testBit i1 = w.testBit i2 := by
    intro w hw; obtain ⟨w', hw', rfl⟩ := hr.mem.1 hw
    exact (hgd w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
  have g2 : ∀ w ∈ S, w.testBit (NN + j1) = w.testBit (NN + j2) := by
    intro w hw; obtain ⟨w', hw', rfl⟩ := hr.mem.1 hw
    exact (hgd w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
  have ma := hr.mem.2 ⟨a, ha, rfl⟩
  have mb := hr.mem.2 ⟨b, hb, rfl⟩
  rcases Nat.eq_zero_or_pos t with rfl | htp
  · have hd' : pos' 0 = false := by simp [pos']
    rw [hd'] at u1 u2 u3 u4
    exact rect0 hm.1 hm.2 (by simpa using htight) (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
      ma mb hab g1 g2 u1 u2 u3 u4
  · have hd' : pos' t = true := by simp [pos', htp]
    rw [hd'] at u1 u2 u3 u4
    exact rect1 hm.1 hm.2 htight (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
      ma mb hab g1 g2 u1 u2 u3 u4
lemma adj_ht {v : List W} {S : Finset ℕ} {d : Bool} (hr : Rep v S) (hgd : ∀ w ∈ v, Good l w.s) {x y : ℕ} (h : Adj (edg false l (wst d l v) v) x y) :
    ∃ a b, Pos v a x ∧ Pos v b y ∧ a.s ≠ b.s ∧ Ht NN m T d S a.s b.s := by
  have hl : ∀ i, l.testBit i = true → AA.testBit i = true := fun i hi => (X.lg i hi).2
  have hadj := h.ne (Eb_edg hl (fun i hi => wst_sub hi))
  obtain ⟨p, hp, hxy⟩ := h
  obtain ⟨_, _, a, b, pa, pb, hq⟩ := edg_spec hl (fun i hi => wst_sub hi) hp
  have hh := Hq_ht X hr hgd pa.mem pb.mem hq
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨a, b, pa, pb, fun e => hadj (pos_inj hr.1 pa pb e), hh⟩
  · exact ⟨b, a, pb, pa, fun e => hadj (pos_inj hr.1 pb pa e), hh.symm⟩
omit X in
open Classical in
lemma pc_of {v : List W} {A : ℕ → ℕ → Prop} {Q : W → Prop} (f : ℕ → ℕ) (h1 : ∀ w ∈ v, Q w → f w.s ≤ 1)
    (h2 : ∀ x y, A x y → ∃ a b, Pos v a x ∧ Pos v b y ∧ Q a ∧ Q b ∧ f a.s ≠ f b.s) :
    ∀ x y, A x y → decide (∃ w, Pos v w x ∧ f w.s = 1) ≠ decide (∃ w, Pos v w y ∧ f w.s = 1) := by
  intro x y hxy
  obtain ⟨a, b, pa, pb, qa, qb, hf⟩ := h2 x y hxy
  have val : ∀ {w i}, Pos v w i → ((∃ w, Pos v w i ∧ f w.s = 1) ↔ f w.s = 1) := by
    intro w i hw
    constructor
    · rintro ⟨w', hw', h⟩; rwa [hw.uniq hw']
    · intro h; exact ⟨w, hw, h⟩
  have e1 := h1 a pa.mem qa; have e2 := h1 b pb.mem qb
  simp only [val pa, val pb]
  intro hc
  have hc' : (f a.s = 1) ↔ (f b.s = 1) := by simpa using hc
  omega
end sound
section kp
variable {m T k k' t : ℕ} {v : List W} {S : Finset ℕ}
lemma tst1_kp {h : ℕ} (hEb : Eb h) (hr : Rep v S) (hm : Min R m T k' t S) (hk : k' ≤ k) (hn : v.length + t = k)
    (hadj : ∀ x y, Adj h x y → ∃ a b, Pos v a x ∧ Pos v b y ∧ a.s ≠ b.s ∧ Ht NN m T (pos' t) S a.s b.s) :
    ∃ (κ : ℕ → Bool) (κ2 : ℕ → ℕ → Bool), (∀ F, tst1 h F = F κ κ2) ∧ KP R m T k' t S v κ κ2 := by
  classical
  have hcard := hr.card
  have mem : ∀ {w i}, Pos v w i → w.s ∈ S := fun hw => hr.mem.2 ⟨_, hw.mem, rfl⟩
  have pne : ∀ {a b i j}, Pos v a i → Pos v b j → i ≠ j → a.s ≠ b.s := fun ha hb hij e => hij (pos_inj hr.1 ha hb e)
  have hb : nonbip h = false := by
    obtain ⟨x, f, q1, q2, q3⟩ := chrom (N := NN) (e := pos' t) hm.1 hm.2 (he' t)
    refine nonbip_ok hEb (c := fun i => decide (∃ w, Pos v w i ∧ f w.s = 1)) (pc_of (v := v) (Q := fun _ => True) f (fun w hw _ => ?_) fun x y hxy => ?_)
    · have := q2 w.s (hr.mem.2 ⟨w, hw, rfl⟩); omega
    · obtain ⟨a, b, pa, pb, hne, hht⟩ := hadj x y hxy
      exact ⟨a, b, pa, pb, trivial, trivial, q3 _ (mem pa) _ (mem pb) hne hht⟩
  refine ⟨fun i => ne0 (del h i), kT2, fun F => ?_, ?_, ?_⟩
  · unfold tst1; rw [hb]
  · rintro d a b S1 k0 rfl hbi hlv ha hbn w i hw rfl
    by_contra hc
    obtain ⟨x, y, hxy⟩ := ne0_adj (by simpa using hc)
    obtain ⟨hxy, hx, hy⟩ := del_adj hEb hxy
    obtain ⟨a', b', pa, pb, hne, hht⟩ := hadj x y hxy
    obtain ⟨x0, g, g1, g2, g3⟩ := keep_col hbi hlv hm ha hbn
    have e1 := g2 _ (mem pa) (pne pa hw hx)
    have e2 := g2 _ (mem pb) (pne pb hw hy)
    have := g3 _ (mem pa) _ (mem pb) (pne pa hw hx) (pne pb hw hy) hne hht
    omega
  · rintro d a b S1 k0 rfl hbi hlv ha hbn
    obtain ⟨x0, g, g1, _⟩ := keep_col2 hbi hlv hm ha hbn
    omega
lemma tst2_kp {h : ℕ} (hEb : Eb h) (hr : Rep v S) (hm : Min R m T k' t S) (hk : k' ≤ k) (hn : v.length + t + 1 = k)
    (hadj : ∀ x y, Adj h x y → ∃ a b, Pos v a x ∧ Pos v b y ∧ a.s ≠ b.s ∧ Ht NN m T (pos' t) S a.s b.s) :
    ∃ (κ : ℕ → Bool) (κ2 : ℕ → ℕ → Bool), (∀ F, tst2 h F = F κ κ2) ∧ KP R m T k' t S v κ κ2 := by
  classical
  have hcard := hr.card
  have mem : ∀ {w i}, Pos v w i → w.s ∈ S := fun hw => hr.mem.2 ⟨_, hw.mem, rfl⟩
  have pne : ∀ {a b i j}, Pos v a i → Pos v b j → i ≠ j → a.s ≠ b.s := fun ha hb hij e => hij (pos_inj hr.1 ha hb e)
  have c1 : ∀ {d : Bool} {a b : ℕ} {S1 : Finset ℕ} {k0 : ℕ}, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → a ∈ S1 → b ∉ S1 →
      ∀ w i, Pos v w i → w.s = a → ∃ c : ℕ → Bool, ∀ x y, (Adj h x y ∧ x ≠ i ∧ y ≠ i) → c x ≠ c y := by
    rintro d a b S1 k0 rfl hbi hlv ha hbn w i hw rfl
    obtain ⟨x0, g, g1, g2, g3⟩ := keep_col hbi hlv hm ha hbn
    refine ⟨fun i => decide (∃ w, Pos v w i ∧ g w.s = 1), pc_of (v := v) (Q := fun x => x.s ≠ w.s) g (fun x hx hq => ?_) fun x y hxy => ?_⟩
    · have := g2 x.s (hr.mem.2 ⟨x, hx, rfl⟩) hq; omega
    · obtain ⟨hxy, hx, hy⟩ := hxy
      obtain ⟨a', b', pa, pb, hne, hht⟩ := hadj x y hxy
      exact ⟨a', b', pa, pb, pne pa hw hx, pne pb hw hy, g3 _ (mem pa) _ (mem pb) (pne pa hw hx) (pne pb hw hy) hne hht⟩
  have c2 : ∀ {d : Bool} {a b : ℕ} {S1 : Finset ℕ} {k0 : ℕ}, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → a ∈ S1 → b ∈ S1 →
      ∀ wa i wb j, Pos v wa i → wa.s = a → Pos v wb j → wb.s = b → ∀ x y, Adj h x y → x ≠ i → x ≠ j → y ≠ i → y ≠ j → False := by
    rintro d a b S1 k0 rfl hbi hlv ha hbn wa i wb j hwa rfl hwb rfl x y hxy xi xj yi yj
    obtain ⟨x0, g, g1, g2, g3⟩ := keep_col2 hbi hlv hm ha hbn
    obtain ⟨a', b', pa, pb, hne, hht⟩ := hadj x y hxy
    have e1 := g2 _ (mem pa) (pne pa hwa xi) (pne pa hwb xj)
    have e2 := g2 _ (mem pb) (pne pb hwa yi) (pne pb hwb yj)
    have := g3 _ (mem pa) _ (mem pb) (pne pa hwa xi) (pne pa hwb xj) (pne pb hwa yi) (pne pb hwb yj) hne hht
    omega
  have k1ok : ∀ {i}, (∃ c : ℕ → Bool, ∀ x y, (Adj h x y ∧ x ≠ i ∧ y ≠ i) → c x ≠ c y) → nonbip (del h (2 ^ i)) = false :=
    fun ⟨c, hc⟩ => nonbip_ok (del_Eb hEb) (c := c) fun x y hxy => hc x y (del_adj hEb hxy)
  have k2ok : ∀ {i j}, (∀ x y, Adj h x y → x ≠ i → x ≠ j → y ≠ i → y ≠ j → False) → ne0 (del (del h (2 ^ i)) (2 ^ j)) = false := by
    intro i j hn
    by_contra hc
    obtain ⟨x, y, hxy⟩ := ne0_adj (by simpa using hc)
    obtain ⟨hxy, xj, yj⟩ := del_adj (del_Eb hEb) hxy
    obtain ⟨hxy, xi, yi⟩ := del_adj hEb hxy
    exact hn x y hxy xi xj yi yj
  rcases tri_ok hEb 12 (f12 h) with hT | ⟨x, y, z, axy, axz, ayz, hT⟩
  · refine ⟨k1 h, k2 h, fun F => ?_, ?_, ?_⟩
    · unfold tst2; rw [st_eq, hT]; rfl
    · intro d a b S1 k0 q1 q2 q3 q4 q5 w i q6 q7
      exact k1ok (c1 q1 q2 q3 q4 q5 w i q6 q7)
    · intro d a b S1 k0 q1 q2 q3 q4 q5 wa i wb j q6 q7 q8 q9
      exact k2ok (c2 q1 q2 q3 q4 q5 wa i wb j q6 q7 q8 q9)
  · generalize hTm : tri h 12 (f12 h) = Tm at hT
    have hT0 : Nat.beq Tm 0 = false := by
      rw [hT]
      refine Bool.eq_false_iff.2 fun hc => ?_
      have hc := Nat.eq_of_beq_eq_true hc
      have : (2 ^ x ||| 2 ^ y ||| 2 ^ z).testBit x = true := by simp [Nat.testBit_or, Nat.testBit_two_pow_self]
      rw [hc] at this; simp at this
    have bT : ∀ i, Tm.testBit i = true ↔ (i = x ∨ i = y ∨ i = z) := by
      intro i
      rw [hT]
      simp only [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro ((q | q) | q)
        · exact Or.inl q.symm
        · exact Or.inr (Or.inl q.symm)
        · exact Or.inr (Or.inr q.symm)
      · rintro (q | q | q)
        · exact Or.inl (Or.inl q.symm)
        · exact Or.inl (Or.inr q.symm)
        · exact Or.inr q.symm
    have nxy := axy.ne hEb; have nxz := axz.ne hEb; have nyz := ayz.ne hEb
    refine ⟨k3 h Tm, k4 h Tm, fun F => ?_, ?_, ?_⟩
    · unfold tst2; rw [st_eq]; beta_reduce; rw [hTm, bR, hT0]; rfl
    · intro d a b S1 k0 q1 q2 q3 q4 q5 w i q6 q7
      obtain ⟨c, hc⟩ := c1 q1 q2 q3 q4 q5 w i q6 q7
      unfold k3
      rw [bR, k1ok ⟨c, hc⟩]
      cases h0 : Nat.beq (Nat.land (2 ^ i) Tm) 0 with
      | false => rfl
      | true =>
        exfalso
        have h0 : 2 ^ i &&& Tm = 0 := Nat.eq_of_beq_eq_true h0
        have hi : ¬ (i = x ∨ i = y ∨ i = z) := fun hi => by
          have : (2 ^ i &&& Tm).testBit i = true := by rw [Nat.testBit_and, Nat.testBit_two_pow_self, (bT i).2 hi]; rfl
          rw [h0] at this; simp at this
        push Not at hi
        have key : ∀ {p q}, Adj h p q → p ≠ i → q ≠ i → c p ≠ c q := fun hpq hp hq => hc _ _ ⟨hpq, hp, hq⟩
        have e1 := key axy hi.1.symm hi.2.1.symm
        have e2 := key axz hi.1.symm hi.2.2.symm
        have e3 := key ayz hi.2.1.symm hi.2.2.symm
        exact (by decide : ∀ a b d : Bool, a ≠ b → a ≠ d → b ≠ d → False) _ _ _ e1 e2 e3
    · intro d a b S1 k0 q1 q2 q3 q4 q5 wa i wb j q6 q7 q8 q9
      have hn := c2 q1 q2 q3 q4 q5 wa i wb j q6 q7 q8 q9
      unfold k4
      rw [bR, k2ok hn]
      cases h0 : Nat.beq (Nat.land (Nat.lor (2 ^ i) (2 ^ j)) Tm) (Nat.lor (2 ^ i) (2 ^ j)) with
      | true => rfl
      | false =>
        exfalso
        have : ¬ ((i = x ∨ i = y ∨ i = z) ∧ (j = x ∨ j = y ∨ j = z)) := by
          rintro ⟨hi, hj⟩
          have : (2 ^ i ||| 2 ^ j) &&& Tm = 2 ^ i ||| 2 ^ j := by
            apply Nat.eq_of_testBit_eq; intro r
            rw [Nat.testBit_and]
            cases hr : (2 ^ i ||| 2 ^ j).testBit r with
            | false => rfl
            | true =>
              rw [Nat.testBit_or, Bool.or_eq_true] at hr
              rcases hr with hr | hr
              · rw [pow_bit hr, (bT i).2 hi]; rfl
              · rw [pow_bit hr, (bT j).2 hj]; rfl
          have h0 : Nat.beq ((2 ^ i ||| 2 ^ j) &&& Tm) (2 ^ i ||| 2 ^ j) = false := h0
          rw [this, Nat.beq_refl] at h0; simp at h0
        have tr := hn x y axy; have tr2 := hn x z axz; have tr3 := hn y z ayz
        by_cases hi : i = x ∨ i = y ∨ i = z
        · have hj : ¬ (j = x ∨ j = y ∨ j = z) := fun hj => this ⟨hi, hj⟩
          push Not at hj
          rcases hi with rfl | rfl | rfl
          · exact tr3 nxy.symm hj.2.1.symm nxz.symm hj.2.2.symm
          · exact tr2 nxy hj.1.symm nyz.symm hj.2.2.symm
          · exact tr nxz hj.1.symm nyz hj.2.1.symm
        · push Not at hi
          by_cases hjx : x = j
          · subst hjx; exact tr3 hi.2.1.symm nxy.symm hi.2.2.symm nxz.symm
          · by_cases hjy : y = j
            · subst hjy; exact tr2 hi.1.symm nxy hi.2.2.symm nyz.symm
            · exact tr hi.1.symm hjx hi.2.1.symm hjy
end kp
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma tsn_eq (d : Bool) (l e : ℕ) (v : List W) (F : (ℕ → Bool) → (ℕ → ℕ → Bool) → Bool) :
    tsn d l e v F = bif Nat.beq v.length e then (bif Nat.beq (edg d l (wst d l v) v) 0 then F kF kF2 else false) else
      (bif Nat.beq (v.length + 1) e then tst1 (edg false l (wst d l v) v) F else
        (bif Nat.beq (v.length + 2) e then tst2 (edg false l (wst d l v) v) F else F kF kF2)) := by
  unfold tsn
  beta_reduce
  rw [bR, bR, bR, bR, st_eq, st_eq, len_eq]
lemma rect0_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) (hn : v.length + t = k + 1) :
    Nat.beq (edg (pos' t) l (wst (pos' t) l v) v) 0 = true := by
  have hl : ∀ i, l.testBit i = true → AA.testBit i = true := fun i hi => (X.lg i hi).2
  have key : ∀ p < 84, 12 ≤ p → p % 13 ≠ p % 12 := by decide
  rw [Nat.beq_eq]
  by_contra hne
  obtain ⟨p, hp⟩ := Nat.exists_testBit_of_ne_zero hne
  obtain ⟨q1, q2, a, b, pa, pb, hq⟩ := edg_spec hl (fun i hi => wst_sub hi) hp
  exact Hq_rect X hs.rep hs.good hm hk hn pa.mem pb.mem (fun e => key p q2 q1 (pos_inj hs.rep.1 pa pb e)) hq
lemma tsn_gen (d : Bool) (l e : ℕ) (v : List W) (F : (ℕ → Bool) → (ℕ → ℕ → Bool) → Bool) {h0 h : ℕ}
    (e0 : edg d l (wst d l v) v = h0) (e1 : edg false l (wst d l v) v = h) :
    tsn d l e v F = bif Nat.beq v.length e then (bif Nat.beq h0 0 then F kF kF2 else false) else
      (bif Nat.beq (v.length + 1) e then tst1 h F else (bif Nat.beq (v.length + 2) e then tst2 h F else F kF kF2)) := by
  subst e0 e1
  exact tsn_eq X d l e v F
lemma tsn_sound {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    ∃ (κ : ℕ → Bool) (κ2 : ℕ → ℕ → Bool), (∀ F, tsn (pos' t) l (k + 1 - t) v F = F κ κ2) ∧ KP R m T k' t S v κ κ2 := by
  have hl : ∀ i, l.testBit i = true → AA.testBit i = true := fun i hi => (X.lg i hi).2
  have hsz := hm.size
  have hcard := hs.rep.card
  have kp0 : KP R m T k' t S v kF kF2 := ⟨fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  obtain ⟨h0, e0⟩ : ∃ h0, edg (pos' t) l (wst (pos' t) l v) v = h0 := ⟨_, rfl⟩
  obtain ⟨h, e1⟩ : ∃ h, edg false l (wst (pos' t) l v) v = h := ⟨_, rfl⟩
  have E := fun F => tsn_gen X (pos' t) l (k + 1 - t) v F e0 e1
  have hz : v.length + t = k + 1 → Nat.beq h0 0 = true := fun hn => by
    have := rect0_ok X hs hm hk hn
    rwa [e0] at this
  have hEb : Eb h := by
    have : Eb (edg false l (wst (pos' t) l v) v) := Eb_edg hl (fun i hi => wst_sub hi)
    rwa [e1] at this
  have hadj : ∀ x y, Adj h x y → ∃ a b, Pos v a x ∧ Pos v b y ∧ a.s ≠ b.s ∧ Ht NN m T (pos' t) S a.s b.s := by
    intro x y hxy
    rw [← e1] at hxy
    exact adj_ht X hs.rep hs.good hxy
  clear e0 e1
  generalize tsn (pos' t) l (k + 1 - t) v = G at E ⊢
  cases h1 : Nat.beq v.length (k + 1 - t) with
  | true =>
    have h1' := Nat.eq_of_beq_eq_true h1
    have h0' := hz (by omega)
    exact ⟨kF, kF2, fun F => by rw [E, h1, h0', cond_true, cond_true], kp0⟩
  | false =>
    cases h2 : Nat.beq (v.length + 1) (k + 1 - t) with
    | true =>
      have h2' := Nat.eq_of_beq_eq_true h2
      obtain ⟨κ, κ2, q1, q2⟩ := tst1_kp hEb hs.rep hm hk (by omega) hadj
      exact ⟨κ, κ2, fun F => by rw [E, h1, h2, cond_false, cond_true, q1], q2⟩
    | false =>
      cases h3 : Nat.beq (v.length + 2) (k + 1 - t) with
      | false => exact ⟨kF, kF2, fun F => by rw [E, h1, h2, h3, cond_false, cond_false, cond_false], kp0⟩
      | true =>
        have h3' := Nat.eq_of_beq_eq_true h3
        obtain ⟨κ, κ2, q1, q2⟩ := tst2_kp hEb hs.rep hm hk (by omega) hadj
        exact ⟨κ, κ2, fun F => by rw [E, h1, h2, h3, cond_false, cond_false, cond_true, q1], q2⟩
end sound
lemma Live.rel {R' : ℕ → ℕ} {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Live R' m T k t S := by
  induction h with
  | stop => exact .stop
  | un _ ih => exact .un ih
  | bi hab hal _ ih => exact .bi hab (hR _ _ _ hal) ih
lemma Bi.rel {R' : ℕ → ℕ} {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hR : ∀ d a b, Al R d a b → Al R' d a b) : Bi R' d a b S S' := by
  obtain ⟨hab, U, e1, e2, hal⟩ := h; exact ⟨hab, U, e1, e2, hR _ _ _ hal⟩
lemma scan_false {p : X → Bool} {xs : List X} (h : scan p xs = false) : ∀ c ∈ xs, p c = false := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (scan p r) true (p a) : Bool) = false at h
    rw [bR] at h
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · revert h; cases p c <;> simp
    · refine ih ?_ c hc
      revert h; cases scan p r <;> simp
lemma pairs_false {h : X → X → Bool} {xs : List X} (hp : pairs h xs = false) : xs.Pairwise (fun a c => h a c = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairs h r) true (scan (h a) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · apply scan_false; revert hp; cases scan (h a) r <;> simp
    · apply ih; revert hp; cases pairs h r <;> simp
lemma pairsP_false {h : X → X → Bool} {xs : List X} {q : ℕ} {a c : X} (hp : pairsP q h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s ≠ q) : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [beq_f hcq, Bool.cond_false] at h2
lemma pairsQ_false {h : X → X → Bool} {xs : List X} {q q' : ℕ} {a c : X} (hp : pairsQ q q' h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s = q') : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [hcq, Nat.beq_refl, Bool.cond_true] at h2
lemma pos_eq (t : ℕ) : pos t = pos' t := by cases t <;> simp [pos, pos']
lemma fr_mem {xs : List X} {a : X} (ha : a ∈ xs) (h : a.w.r = 0) : a ∈ fr xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List X) (fr xs) (x :: fr xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [h]; simp
    · cases Nat.beq x.w.r 0
      · exact ih ha
      · exact List.mem_cons_of_mem _ (ih ha)
lemma fs_mem {xs : List X} {a : X} (ha : a ∈ xs) (h : a.w.r ≠ 0) : a ∈ fs xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List X) (x :: fs xs) (fs xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [beq_f h]; simp
    · cases Nat.beq x.w.r 0
      · exact List.mem_cons_of_mem _ (ih ha)
      · exact ih ha
lemma pairs_any {h : X → X → Bool} {xs : List X} (hp : pairs h xs = false) {a c : X} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c) :
    h a c = false ∨ h c a = false := by
  have hpw := pairs_false hp
  have : Std.Symm (fun a c : X => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
  exact (hpw.imp (S := fun a c => h a c = false ∨ h c a = false) fun h => Or.inl h).forall ha hc hne
lemma pairsN_false {h : X → X → Bool} {xs : List X} (hp : pairsN h xs = false) {a c : X} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c)
    (hr : a.w.r = 0 ∨ c.w.r = 0) : h a c = false ∨ h c a = false := by
  simp only [pairsN, bR] at hp
  cases h1 : pairs h (fr xs) with
  | true => rw [h1] at hp; simp at hp
  | false =>
    rw [h1, cond_false] at hp
    by_cases hra : a.w.r = 0
    · by_cases hrc : c.w.r = 0
      · exact pairs_any h1 (fr_mem ha hra) (fr_mem hc hrc) hne
      · exact Or.inl (scan_false (scan_false hp a (fr_mem ha hra)) c (fs_mem hc hrc))
    · have hrc := hr.resolve_left hra
      exact Or.inr (scan_false (scan_false hp c (fr_mem hc hrc)) a (fs_mem ha hra))
lemma mkX_of {d : Bool} {l o : ℕ} {v : List W} {w : W} {i : ℕ} (h : Pos v w i) : xof d l o w i ∈ mkX d l o v := by
  obtain ⟨pre, t, rfl, rfl⟩ := h
  induction pre with
  | nil =>
    change _ ∈ (⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o, Nat.shiftLeft 1 (len t)⟩ : X) :: mkX d l o t
    rw [len_eq]
    have : Nat.shiftLeft 1 t.length = 2 ^ t.length := by change 1 <<< _ = _; rw [Nat.shiftLeft_eq, one_mul]
    rw [this]; exact List.mem_cons_self
  | cons x pre ih => exact List.mem_cons_of_mem _ ih
lemma mkX_mem {d : Bool} {l o : ℕ} {v : List W} {p : X} (h : p ∈ mkX d l o v) : ∃ w i, Pos v w i ∧ p = xof d l o w i := by
  induction v with
  | nil => simp [mkX] at h
  | cons x v ih =>
    change p ∈ (⟨x, x.s, Nat.shiftRight x.s NN, Nat.land (sp d l x.s) o, Nat.shiftLeft 1 (len v)⟩ : X) :: mkX d l o v at h
    rw [len_eq] at h
    have e : Nat.shiftLeft 1 v.length = 2 ^ v.length := by change 1 <<< _ = _; rw [Nat.shiftLeft_eq, one_mul]
    rw [e] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨x, v.length, ⟨[], v, rfl, rfl⟩, rfl⟩
    · obtain ⟨w, i, ⟨pre, t, e1, e2⟩, e3⟩ := ih h
      exact ⟨w, i, ⟨x :: pre, t, by rw [e1]; rfl, e2⟩, e3⟩
lemma Pos.ex {v : List W} {w : W} (h : w ∈ v) : ∃ i, Pos v w i := by
  obtain ⟨pre, t, rfl⟩ := List.append_of_mem h; exact ⟨t.length, pre, t, rfl, rfl⟩
lemma nodeH_eq (h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool) (d : Bool) (l e n : ℕ) (v : List W) (κ : ℕ → Bool) (κ2 : ℕ → ℕ → Bool)
    (go : (X → X → Bool) → List X → Bool) : nodeH h d l e n v κ κ2 go = go (pair (modeH h n e κ κ2)) (mkX d l (wst d l v) v) := by
  unfold nodeH modeH
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ (Nat.succ n)) e <;> rfl
lemma pair_false {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {d : Bool} {l o i j : ℕ} {a c : W}
    (hp : pair h (xof d l o a i) (xof d l o c j) = false) (d' : Bool) :
    h a c (2 ^ i) (2 ^ j) (dfc d d' l o a c) (dfc d d' l o c a) (opW d' a c).s (opW d' a c).a (opW d' a c).b = false := by
  simp only [pair, xof, bR] at hp
  rw [Bool.cond_eq_ite] at hp
  split_ifs at hp with h1
  · cases d'
    · rw [Bool.not_eq_true] at h1; exact h1
    · exact hp
lemma modeH_false {h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool} {n e : ℕ} {κ : ℕ → Bool} {κ2 : ℕ → ℕ → Bool} {a c : W} {ia ic da dc s x y : ℕ}
    {A C : Prop} (hf : modeH h n e κ κ2 a c ia ic da dc s x y = false) (hA : ¬ A → da = 0) (hC : ¬ C → dc = 0)
    (h0 : ¬ n ≤ e → ¬ A ∧ ¬ C) (k1 : A → ¬ C → κ ia = false) (k2 : C → ¬ A → κ ic = false) (k3 : A → C → κ2 ia ic = false) :
    ∃ oa oc ka kc kb, (¬ A → oa = true) ∧ (¬ C → oc = true) ∧ (A → ¬ C → ka = false) ∧ (C → ¬ A → kc = false) ∧ (A → C → kb = false) ∧
      h a c oa oc ka kc kb s x y = false := by
  unfold modeH at hf
  cases b1 : Nat.ble n e with
  | false =>
    have hne : ¬ n ≤ e := fun h => by rw [Nat.ble_eq_true_of_le h] at b1; simp at b1
    obtain ⟨nA, nC⟩ := h0 hne
    rw [b1] at hf
    simp only [Bool.cond_false, f0, hA nA, hC nC] at hf
    exact ⟨true, true, true, true, true, fun _ => rfl, fun _ => rfl, fun h _ => absurd h nA, fun h _ => absurd h nC, fun h _ => absurd h nA, hf⟩
  | true =>
    rw [b1, Bool.cond_true] at hf
    have bz : ∀ {z : ℕ}, Nat.beq z 0 = false → z ≠ 0 := fun hz e => by rw [e] at hz; simp at hz
    cases b2 : Nat.ble (Nat.succ (Nat.succ n)) e with
    | true =>
      rw [b2, Bool.cond_true] at hf
      refine ⟨Nat.beq da 0, Nat.beq dc 0, false, false, false, fun hn => by rw [hA hn]; rfl, fun hn => by rw [hC hn]; rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, hf⟩
    | false =>
      rw [b2, Bool.cond_false] at hf
      simp only [f1, bR] at hf
      cases z1 : Nat.beq da 0 with
      | true =>
        rw [z1, Bool.cond_true] at hf
        cases z2 : Nat.beq dc 0 with
        | true =>
          rw [z2, Bool.cond_true] at hf
          exact ⟨true, true, κ ia, κ ic, κ2 ia ic, fun _ => rfl, fun _ => rfl, k1, k2, k3, hf⟩
        | false =>
          have hCt : C := by by_contra hn; exact bz z2 (hC hn)
          rw [z2, Bool.cond_false] at hf
          cases z3 : κ ic with
          | false =>
            rw [z3, Bool.cond_false] at hf
            exact ⟨true, false, true, false, κ2 ia ic, fun _ => rfl, fun h => absurd hCt h, fun _ h => absurd hCt h, fun _ _ => rfl, k3, hf⟩
          | true =>
            have hAt : A := by by_contra hn; rw [k2 hCt hn] at z3; simp at z3
            rw [z3, Bool.cond_true, k3 hAt hCt, Bool.cond_false] at hf
            exact ⟨false, false, true, true, false, fun h => absurd hAt h, fun h => absurd hCt h, fun _ h => absurd hCt h, fun _ h => absurd hAt h, fun _ _ => rfl, hf⟩
      | false =>
        have hAt : A := by by_contra hn; exact bz z1 (hA hn)
        rw [z1, Bool.cond_false] at hf
        cases z2 : Nat.beq dc 0 with
        | true =>
          rw [z2, Bool.cond_true] at hf
          cases z3 : κ ia with
          | false =>
            rw [z3, Bool.cond_false] at hf
            exact ⟨false, true, false, true, κ2 ia ic, fun h => absurd hAt h, fun _ => rfl, fun _ _ => rfl, fun _ h => absurd hAt h, k3, hf⟩
          | true =>
            have hCt : C := by by_contra hn; rw [k1 hAt hn] at z3; simp at z3
            rw [z3, Bool.cond_true, k3 hAt hCt, Bool.cond_false] at hf
            exact ⟨false, false, true, true, false, fun h => absurd hAt h, fun h => absurd hCt h, fun _ h => absurd hCt h, fun _ h => absurd hAt h, fun _ _ => rfl, hf⟩
        | false =>
          have hCt : C := by by_contra hn; exact bz z2 (hC hn)
          rw [z2, Bool.cond_false, k3 hAt hCt, Bool.cond_false] at hf
          exact ⟨false, false, true, true, false, fun h => absurd hAt h, fun h => absurd hCt h, fun _ h => absurd hCt h, fun _ h => absurd hAt h, fun _ _ => rfl, hf⟩
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma cv_ok {t k k' z : ℕ} {v : List W} {S : Finset ℕ} {b : Bool} (hs : StOk P T l k z v S) (hl : Live R m T k' t S)
    (h : cv (pos' t) l v b = false) : b = false := by
  have hcov : Nat.beq (cov (pos' t) l v) l = true := by
    rw [Nat.beq_eq]
    apply Nat.eq_of_testBit_eq; intro i
    cases hli : l.testBit i with
    | false =>
      by_contra hc
      obtain ⟨w, _, hw⟩ := (cov_bit _ _ _ _).1 (by simpa using hc)
      rw [sp_bit, hli] at hw; simp at hw
    | true =>
      rw [cov_bit]
      obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
      obtain ⟨w, hw, hs1⟩ := hl.cov m1 m2 t1 t2
      obtain ⟨w', hw', rfl⟩ := hs.rep.mem.1 hw
      exact ⟨w', hw', by rw [sp_bit, hli, hs1]; rfl⟩
  simp only [cv, bR, hcov, cond_true] at h
  cases hp : pos' t <;> rw [hp] at h <;> simpa using h
lemma nodeH_bi {f : ℕ → List W → Bool} {h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {κ : ℕ → Bool} {κ2 : ℕ → ℕ → Bool} {go : (L_meta_17357.X → L_meta_17357.X → Bool) → List L_meta_17357.X → Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' x y S S') (hl : Live R m T k' t S') (hKP : KP R m T (k' + 1) t S v κ κ2)
    (hh : ∀ (a c : W) (oa oc ka kc kb : Bool) (x1 y1 : ℕ), op d' a.s c.s = op d' x y → h a c oa oc ka kc kb (op d' a.s c.s) x1 y1 = false →
      mid f m g np e (Nat.pred n) z v a c oa oc ka kc kb (op d' a.s c.s) x1 y1 = false)
    (hgo : ∀ h xs, go h xs = false → xs = mkX d l (wst d l v) v → ∀ a c : L_meta_17357.X, a ∈ xs → c ∈ xs → a.w ∈ v → c.w ∈ v → a.s = a.w.s → c.s = c.w.s → a.s = x → c.s = y →
      h a c = false ∨ h c a = false)
    (hp : nodeH h d l e n v κ κ2 go = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ ∃ w' ∈ v, w'.s = w.s ∧ w'.r = w.r := by
  rw [nodeH_eq] at hp
  have one : ∀ {a c : W} {i j : ℕ}, Pos v a i → Pos v c j → Bi R d' a.s c.s S S' → op d' a.s c.s = op d' x y →
      pair (modeH h n e κ κ2) (xof d l (wst d l v) a i) (xof d l (wst d l v) c j) = false →
      ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ ∃ w' ∈ v, w'.s = w.s ∧ w'.r = w.r := by
    intro a c i j ha hc hb1 hop hpp
    have hpp := pair_false hpp d'
    have filt : ∀ {x y : W}, (∀ i, (Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (NN + i) = false else y.s.testBit i = true) →
        dfc (pos' t) d' l (wst (pos' t) l v) x y = 0 := by
      intro x y hu
      unfold dfc
      generalize Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v) = u at *
      cases d'
      · simp only [Bool.cond_false, nl, nx] at hu ⊢
        apply Nat.eq_of_testBit_eq; intro i
        have := hu i
        rw [Nat.testBit_xor, Nat.testBit_and]
        cases h1 : u.testBit i with
        | false => simp
        | true => simp [this h1]
      · simp only [Bool.cond_true, nl, nsr] at hu ⊢
        apply Nat.eq_of_testBit_eq; intro i
        have := hu i
        rw [Nat.testBit_and, Nat.testBit_shiftRight]
        cases h1 : u.testBit i with
        | false => simp
        | true => simp [this h1]
    have fa : a.s ∉ S' → dfc d d' l (wst d l v) a c = 0 := fun h => by
      subst hd; exact filt fun i hi => drop_ok X hs.rep hb1 hl ha.mem h hi
    have fc : c.s ∉ S' → dfc d d' l (wst d l v) c a = 0 := fun h => by
      subst hd; exact filt fun i hi => drop_ok X hs.rep hb1.symm hl hc.mem h hi
    have hfS : op d' a.s c.s ∉ S := fun h => hb1.fresh hl hm.2 (sub_C _ _ (by simpa using h))
    have hcards : (a.s ∈ S' ∨ c.s ∈ S') → v.length ≤ S'.card := by
      intro hor
      rw [← hs.rep.card]
      obtain ⟨hac, U, e1, e2, _⟩ := hb1
      have hf : op d' a.s c.s ∉ U := fun h => hfS (by rw [e1]; simp [h])
      have nga : a.s ≠ op d' a.s c.s := fun h => hfS (by rw [← h, e1]; simp)
      have ngc : c.s ≠ op d' a.s c.s := fun h => hfS (by rw [← h, e1]; simp)
      have hU : a.s ∈ U ∨ c.s ∈ U := by
        rcases hor with h | h
        · left; rw [e2, Finset.mem_insert] at h; exact h.resolve_left nga
        · right; rw [e2, Finset.mem_insert] at h; exact h.resolve_left ngc
      rw [e2, Finset.card_insert_of_notMem hf, e1]
      rcases hU with h | h
      · rw [Finset.insert_eq_of_mem (by simp [h])]; exact Finset.card_insert_le _ _
      · rw [Finset.insert_eq_of_mem h]; exact Finset.card_insert_le _ _
    have hmo := modeH_false (A := a.s ∈ S') (C := c.s ∈ S') hpp fa fc (fun hne => by
        constructor
        · intro h; have := hcards (Or.inl h); omega
        · intro h; have := hcards (Or.inr h); omega)
      (fun hA hC => hKP.g1 rfl hb1 hl hA hC a i ha rfl) (fun hC hA => hKP.g1 rfl hb1.symm hl hC hA c j hc rfl)
      (fun hA hC => hKP.g2 rfl hb1 hl hA hC a i c j ha rfl hc rfl)
    obtain ⟨oa, oc, ka, kc, kb, q1, q2, q3, q4, q5, q6⟩ := hmo
    have hmid := hh a c oa oc ka kc kb (opW d' a c).a (opW d' a c).b hop (by rw [← opW_s]; exact q6)
    obtain ⟨z', r, r1, r2, r3⟩ := gate_sound X hs hm hk hn hSe hb1 hl ha.mem hc.mem q1 q2 q3 q4 q5 (by rw [opW_s]; exact hmid)
    exact ⟨z', r, r1, r2, fun w hw => by rw [← hop]; exact r3 w hw⟩
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  obtain ⟨i, hi⟩ := Pos.ex ha
  obtain ⟨j, hj⟩ := Pos.ex hc
  rcases hgo _ _ hp rfl (xof d l (wst d l v) a i) (xof d l (wst d l v) c j) (mkX_of hi) (mkX_of hj) ha hc rfl rfl rfl rfl with q | q
  · exact one hi hj hb rfl q
  · exact one hj hi hb.symm (op_comm _ _ _) q
lemma mv_false (F : ℕ → ℕ → ℕ → List W → Bool) (l m g np k t z : ℕ) (v : List W) (κ : ℕ → Bool) (κ2 : ℕ → ℕ → Bool) (h : mv F l m g np k t z v κ κ2 = false) :
    node (F (k - 1) t) (pos' t) l m g np (k - t) v.length z v κ κ2 pairsN = false ∧
    ∀ s, t = s + 1 → nots (fun q z v => cv (pos' s) l v (tsn (pos' s) l (k - s) v (fun κ κ2 =>
      bif node (F (k - 2) s) (pos' s) l m g np (k - 1 - s) v.length z v κ κ2 (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => cv (pos' s) l v (tsn (pos' s) l (k - 1 - s) v (fun κ κ2 =>
        node (F (k - 3) s) (pos' s) l m g np (k - 2 - s) v.length z v κ κ2 (pairsQ q q'))))
        m g (k - 1 - s) v.length z (q + 1) v v)))) m g (k - s) v.length z 0 v v = false := by
  clear X
  simp only [mv, st_eq, len_eq, bR, pos_eq] at h
  have key : ∀ {p q : Bool}, (bif p then true else q) = false → p = false ∧ q = false := fun {p q} h => by cases p <;> simp_all
  obtain ⟨h1, h2⟩ := key h
  refine ⟨h1, ?_⟩
  rintro s rfl
  exact h2
end sound
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma node_bi {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {κ : ℕ → Bool} {κ2 : ℕ → ℕ → Bool} {go : (L_meta_17357.X → L_meta_17357.X → Bool) → List L_meta_17357.X → Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' x y S S') (hl : Live R m T k' t S') (hKP : KP R m T (k' + 1) t S v κ κ2)
    (hgo : ∀ h xs, go h xs = false → xs = mkX d l (wst d l v) v → ∀ a c : L_meta_17357.X, a ∈ xs → c ∈ xs → a.w ∈ v → c.w ∈ v → a.s = a.w.s → c.s = c.w.s → a.s = x → c.s = y →
      h a c = false ∨ h c a = false)
    (hp : node f d l m g np e n z v κ κ2 go = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ ∃ w' ∈ v, w'.s = w.s ∧ w'.r = w.r :=
  nodeH_bi X hs hm hk hd hn hSe hb hl hKP (fun _ _ _ _ _ _ _ _ _ _ h => h) hgo hp
lemma mv_sound (hR : RR R) {F : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), F k t z v = false → StOk P T l k z v S → Cod R v → ∀ k' ≤ k, ¬ Min R m T k' t S)
    {k t z : ℕ} {v : List W} {S : Finset ℕ} {κ : ℕ → Bool} {κ2 : ℕ → ℕ → Bool} (hs : StOk P T l k z v S) (hcod : Cod R v) (hlen : 2 ≤ v.length)
    (h : mv F l m g np k t z v κ κ2 = false) : ∀ k' ≤ k, Min R m T k' t S → KP R m T k' t S v κ κ2 → False := by
  intro k' hk hm hKP
  obtain ⟨hA, hN⟩ := mv_false X F l m g np k t z v κ κ2 h
  have hcard := hs.rep.card
  have codB : ∀ {v r : List W} {o : ℕ}, Cod R v → (∀ w ∈ r, (w.s = o ∧ w.r = 0) ∨ ∃ w' ∈ v, w'.s = w.s ∧ w'.r = w.r) → Cod R r := by
    intro v r o hv hr w hw
    rcases hr w hw with ⟨_, h⟩ | ⟨w', h1, h2, h3⟩
    · exact Or.inl h
    · rw [← h2, ← h3]; exact hv w' h1
  have sizeB : ∀ {k k' t : ℕ} {S S1 : Finset ℕ} {d : Bool} {a b : ℕ}, Min R m T (k' + 1) t S → k' + 1 ≤ k → Bi R d a b S S1 → Live R m T k' t S1 → S1.card ≤ k - t := by
    intro k k' t S S1 d a b hm hk hb hl
    have hs := (hb.min hl hm.2).size.1; omega
  have sizeU : ∀ {k k' t : ℕ} {S S1 : Finset ℕ} {a : ℕ}, Min R m T (k' + 1) (t + 1) S → k' + 1 ≤ k → Un m a S S1 → Live R m T k' t S1 → S1.card ≤ k - t := by
    intro k k' t S S1 a hm hk hb hl
    have hs := (hb.min hl hm.2).size.1; omega
  rcases first_move k' t S hm (by omega) with
    ⟨k0, d, a, b, S1, rfl, hb, hl⟩ | ⟨k0, t0, a, d, c, S1, S2, rfl, rfl, hu, hb, hl⟩ |
    ⟨k0, t0, a, a', d, S1, S2, S3, rfl, rfl, hu, hne, hu', hb, hl⟩
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hs hm (by omega) rfl rfl (sizeB hm hk hb hl) hb hl hKP (fun h xs hp hxs a c ha hc hav hcv eas ecs hax hcy => by
      refine pairsN_false hp ha hc ?_ ?_
      · rintro rfl
        exact hb.1 (by rw [← hax, ← hcy])
      · by_contra hc'
        push Not at hc'
        obtain ⟨_, U, _, _, hal⟩ := hb
        have h1 : a.w.r = R a.w.s := (hcod _ hav).resolve_left hc'.1
        have h2 : c.w.r = R c.w.s := (hcod _ hcv).resolve_left hc'.2
        rw [← hax, ← hcy, eas, ecs] at hal
        exact hR _ _ _ (by rw [← h1]; exact hc'.1) (by rw [← h2]; exact hc'.2) hal) hA
    exact hF _ _ _ _ _ hf hst (codB hcod hmem) k0 (by simpa using hk) (hb.min hl hm.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hl1 := hb.live hl
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN t0 rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 1) hs hm (by omega) rfl (sizeU hm hk hu hl1) hu hl1 hwa (by omega) hwa h2
    have hm1 := hu.min hl1 hm.2
    have hf1 := cv_ok X hst1 hl1 hf1
    obtain ⟨κ', κ2', hF1, hKP1⟩ := tsn_sound X hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    rw [Bool.not_eq_true] at hf2
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst1 hm1 (by omega) rfl rfl (sizeB (k := k + 1) hm1 (by omega) hb hl) hb hl hKP1 (fun h xs hp hxs a c ha hc hav hcv eas ecs hax hcy => by
      refine Or.inl (pairsP_false hp ha hax hc fun e => hb.1 ?_)
      rw [← hcy, e]) hf2
    exact hF _ _ _ _ _ hf hst (codB (codB hcod hmem1) hmem) k0 (by simpa using hk) (hb.min hl hm1.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hl1 := hb.live hl
    have hl2 := hu'.live hl1
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN (t0 + 1) rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 2) hs hm (by omega) rfl (sizeU hm hk hu hl2) hu hl2 hwa (by omega) hwa h2
    have hm1 := hu.min hl2 hm.2
    have hf1 := cv_ok X hst1 hl2 hf1
    obtain ⟨κ', κ2', hF1, hKP1⟩ := tsn_sound X hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    obtain ⟨wa', hwa', rfl⟩ := hst1.rep.mem.1 hu'.sub.1
    obtain ⟨z2, r2, hf3, hst2, hmem2⟩ := nots_sound X (k := k + 1) hst1 hm1 (by omega) rfl (sizeU (k := k + 2) hm1 (by omega) hu' hl1) hu' hl1 hwa' (by omega) hwa' hf1
    have hm2 := hu'.min hl1 hm1.2
    have hf3 := cv_ok X hst2 hl1 hf3
    obtain ⟨κ3, κ23, hF3, hKP3⟩ := tsn_sound X hst2 hm2 (by omega)
    have hf3 := (hF3 _).symm.trans hf3
    beta_reduce at hf3
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst2 hm2 (by omega) rfl rfl (sizeB (k := k + 1) hm2 (by omega) hb hl) hb hl hKP3 (fun h xs hp hxs a c ha hc hav hcv eas ecs hax hcy =>
      Or.inl (pairsQ_false hp ha hax hc hcy)) hf3
    exact hF _ _ _ _ _ hf hst (codB (codB (codB hcod hmem1) hmem2) hmem) k0 (by simpa using hk) (hb.min hl hm2.2)
theorem look_sound (hR : RR R) : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g np fuel k t z v = false → StOk P T l k z v S → Cod R v →
    ∀ k' ≤ k, ¬ Min R m T k' t S := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hm
    change (Bool.rec (motive := fun _ => Bool) (tsn (pos t) l (k + 1 - t) v (fun κ κ2 => mv (look l m g np fuel) l m g np k t z v κ κ2)) true (Nat.ble (len v) 1) : Bool) = false at h
    rw [bR, pos_eq, len_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      obtain ⟨κ, κ2, hFy, hKP⟩ := tsn_sound X hs hm hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      exact mv_sound X hR ih hs hcod hlen hy k' hk hm hKP
end sound
lemma lz_lg (Z i : ℕ) (h : (lz Z).testBit i = true) : Lg NN (mz Z) (tz Z) i ∧ AA.testBit i = true := by
  have hA : AA.testBit i = true := by
    simp only [lz, nl, Nat.testBit_and, Bool.and_eq_true] at h; exact h.1
  have hT : TG.testBit i = true := by
    have := congrArg (fun x => x.testBit i) AA_TG
    simp [hA] at this; exact this
  have m1 : (mz Z).testBit i = true := by simp [mz, no, h]
  have m2 : (mz Z).testBit (NN + i) = true := by
    simp only [mz, no, Nat.testBit_or, Nat.shiftLeft_eq, Bool.or_eq_true]
    right
    change (lz Z <<< NN).testBit (NN + i) = true
    rw [Nat.testBit_shiftLeft]; simp [h]
  refine ⟨⟨m1, m2, ?_, ?_⟩, hA⟩
  · simp only [tz, nl, Nat.testBit_and, hT, m1]; rfl
  · simp only [tz, nl, Nat.testBit_and]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le TG_lt (Nat.pow_le_pow_right (by omega) (by omega)))]; rfl
lemma segGood_eq {w o : ℕ} {s : ℕ × ℕ} (h : segGood w o s = true) {i j : ℕ} (h1 : s.1 < i) (h2 : i < s.2) (h3 : s.1 < j) (h4 : j < s.2) :
    w.testBit (o + i) = w.testBit (o + j) := by
  have key : ∀ i, s.1 < i → i < s.2 → w.testBit (o + i) = ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)).testBit (i - s.1 - 1) := by
    intro i h1 h2
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, show o + s.1 + 1 + (i - s.1 - 1) = o + i by omega]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega]
  rw [key i h1 h2, key j h3 h4]
  simp only [segGood, Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with h | h <;> rw [h]
  · simp
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega, show j - s.1 - 1 < s.2 - s.1 - 1 by omega]
lemma raw_wire_good {w : ℕ} (hw : w ∈ rawP) (Z : ℕ) : Good (lz Z) (w &&& mz Z) := by
  have h := List.all_eq_true.1 raw_good w hw
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun i j hij h1 h2 => ?_, fun i j hij h1 h2 => ?_⟩ <;> obtain ⟨s, hs, a1, a2, a3, a4⟩ := hij
  · have := segGood_eq (h.1 s hs) a1 a2 a3 a4
    simp only [Nat.zero_add] at this
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.1, (lz_lg Z j h2).1.1]
  · have := segGood_eq (h.2 s hs) a1 a2 a3 a4
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.2.1, (lz_lg Z j h2).1.2.1]
lemma raw_get (v : ℕ) : rawP.getD v 0 = 0 ∨ rawP.getD v 0 ∈ rawP := by
  rw [List.getD_eq_getElem?_getD]
  cases h : rawP[v]? with
  | none => exact Or.inl rfl
  | some x => exact Or.inr (List.mem_of_getElem? h)
lemma raw_get_good (v Z : ℕ) : Good (lz Z) (rawP.getD v 0 &&& mz Z) := by
  rcases raw_get v with h | h
  · rw [h, Nat.zero_and]; exact ⟨fun i j _ _ _ => by simp, fun i j _ _ _ => by simp⟩
  · exact raw_wire_good h Z
lemma shl_lt {a N : ℕ} (h : a < 2 ^ N) : a <<< N < 2 ^ (2 * N) := by
  rw [Nat.shiftLeft_eq, two_mul, pow_add]; exact Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos _)
lemma mz_lt (Z : ℕ) : mz Z < 2 ^ (2 * NN) := by
  have h1 : lz Z < 2 ^ NN := lt_of_le_of_lt Nat.and_le_left AA_lt
  have h2 : fz Z < 2 ^ NN := lt_of_le_of_lt Nat.and_le_left (by
    unfold FPM; exact lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos 64) (by norm_num)) (Nat.pow_le_pow_right (by norm_num) (by unfold NN; norm_num)))
  have h3 : lz Z <<< NN < 2 ^ (2 * NN) := shl_lt h1
  have h4 : (2 : ℕ) ^ NN ≤ 2 ^ (2 * NN) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (lt_of_lt_of_le h1 h4) (lt_of_lt_of_le h2 h4)) h3
lemma mz_mask (Z : ℕ) : mz Z &&& MASKN = mz Z := by
  unfold MASKN; rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_eq_of_lt (mz_lt Z)
lemma tw_not {e : Bool × ℕ × ℕ} (h : Nat.beq e.2.2 9 = true) (Z : ℕ) : tw e &&& mz Z = (rawP.getD e.2.1 0 &&& mz Z) ^^^ mz Z := by
  rw [tw, h, cond_true]; exact and_neg (mz_mask Z) _
lemma tw_op {e : Bool × ℕ × ℕ} (h : Nat.beq e.2.2 9 = false) : tw e = op e.1 (rawP.getD e.2.1 0) (rawP.getD e.2.2 0) := by
  rw [tw, h, cond_false]
lemma wire_good {E : List (Bool × ℕ × ℕ)} {w : ℕ} (hw : w ∈ rawL E) (Z : ℕ) : Good (lz Z) (w &&& mz Z) := by
  simp only [rawL, List.mem_append, List.mem_map] at hw
  rcases hw with h | ⟨e, _, rfl⟩
  · exact raw_wire_good h Z
  · cases h9 : Nat.beq e.2.2 9 with
    | false => rw [tw_op h9, and_op]; exact op_good _ (raw_get_good _ Z) (raw_get_good _ Z)
    | true =>
      rw [tw_not h9]
      have hg := raw_get_good e.2.1 Z
      refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
      · rw [Nat.testBit_xor, Nat.testBit_xor, hg.1 i j h h1 h2, (lz_lg Z i h1).1.1, (lz_lg Z j h2).1.1]
      · rw [Nat.testBit_xor, Nat.testBit_xor, hg.2 i j h h1 h2, (lz_lg Z i h1).1.2.1, (lz_lg Z j h2).1.2.1]
lemma raw_avail (E : List (Bool × ℕ × ℕ)) (v Z : ℕ) : rawP.getD v 0 &&& mz Z ∈ C (mz Z) (WZ E Z) := by
  rcases raw_get v with h | h
  · rw [h, Nat.zero_and]; exact Or.inr (by simp)
  · exact Or.inl ⟨_, by simp only [rawL, List.mem_append]; exact Or.inl h, rfl⟩
lemma WZ_nil_sub (E : List (Bool × ℕ × ℕ)) (Z : ℕ) : WZ [] Z ⊆ WZ E Z := by
  rintro x ⟨w, hw, rfl⟩
  refine ⟨w, ?_, rfl⟩
  simp only [rawL, List.map_nil, List.append_nil, List.mem_append] at hw ⊢
  exact Or.inl hw
lemma impA {e : Bool × ℕ × ℕ} {Z L : ℕ} (h : trivE e Z = true) (hI : Imp [] Z L) : Imp [e] Z L := by
  intro q hq hs
  refine hI q hq (hs.mono le_rfl ?_)
  rintro x (⟨w, hw, rfl⟩ | hx)
  · simp only [rawL, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact Or.inl ⟨w, by simp only [rawL, List.map_nil, List.append_nil]; exact hw, rfl⟩
    · simp only [trivE, Bool.or_eq_true, List.any_eq_true, nl] at h
      rcases h with (h | h) | ⟨w, hw, h⟩
      · rw [Nat.eq_of_beq_eq_true h]; exact Or.inr (by simp)
      · rw [Nat.eq_of_beq_eq_true h]; exact Or.inr (by simp)
      · rw [← Nat.eq_of_beq_eq_true h]; exact Or.inl ⟨w, by simp only [rawL, List.map_nil, List.append_nil]; exact hw, rfl⟩
  · exact Or.inr hx
lemma sol_add {e : Bool × ℕ × ℕ} {E : List (Bool × ℕ × ℕ)} {Z q : ℕ} {S : Set ℕ} (hS : S ⊆ C (mz Z) (WZ E Z))
    (hs : Sol Z0 (mz Z) (tz Z) q (insert (tw e &&& mz Z) S)) : Sol Z0 (mz Z) (tz Z) (q + 1) (C (mz Z) (WZ E Z)) := by
  cases h9 : Nat.beq e.2.2 9 with
  | false =>
    refine .bi (d := e.1) (raw_avail E e.2.1 Z) (raw_avail E e.2.2 Z) (al0 _ _ _) (hs.mono le_rfl ?_)
    rw [← and_op, ← tw_op h9]
    exact Set.insert_subset_insert hS
  | true =>
    refine .un (a := rawP.getD e.2.1 0 &&& mz Z) (raw_avail E e.2.1 Z) (hs.mono le_rfl ?_)
    rw [← tw_not h9]
    exact Set.insert_subset_insert hS
lemma impB {e : Bool × ℕ × ℕ} {Z L : ℕ} (hI : Imp [] Z L) : Imp [e] Z (L - 1) := by
  intro q hq hs
  refine hI (q + 1) (by omega) (sol_add (e := e) (S := C (mz Z) (WZ [] Z)) subset_rfl (hs.mono le_rfl ?_))
  rintro x (⟨w, hw, rfl⟩ | hx)
  · simp only [rawL, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact Or.inr (Or.inl ⟨w, by simp only [rawL, List.map_nil, List.append_nil]; exact hw, rfl⟩)
    · exact Or.inl rfl
  · exact Or.inr (Or.inr hx)
lemma forb_ok {E : List (Bool × ℕ × ℕ)} {f : Bool × ℕ × ℕ} {Z L : ℕ} (hE : E.length ≤ 1) (hf : Imp [f] Z (L + E.length)) :
    ∀ q < L, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (insert (tw f &&& mz Z) (WZ E Z))) := by
  intro q hq hs
  have hsub : C (mz Z) (insert (tw f &&& mz Z) (WZ [] Z)) ⊆ C (mz Z) (WZ [f] Z) := by
    rintro x ((rfl | hx) | hx)
    · exact Or.inl ⟨tw f, by simp [rawL], rfl⟩
    · exact Or.inl (WZ_nil_sub _ _ hx)
    · exact Or.inr hx
  match E, hE, hf, hs with
  | [], _, hf, hs => exact hf q (by simpa using hq) (hs.mono le_rfl hsub)
  | [e], _, hf, hs =>
    refine hf (q + 1) (by simpa using hq) (sol_add (e := e) (S := C (mz Z) (insert (tw f &&& mz Z) (WZ [] Z))) hsub (hs.mono le_rfl ?_))
    rintro x ((rfl | ⟨w, hw, rfl⟩) | hx)
    · exact Or.inr (Or.inl (Or.inl rfl))
    · simp only [rawL, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inr (Or.inl (Or.inr ⟨w, by simp only [rawL, List.map_nil, List.append_nil]; exact hw, rfl⟩))
      · exact Or.inl rfl
    · exact Or.inr (Or.inr hx)
lemma Imp.mono {E : List (Bool × ℕ × ℕ)} {Z L L' : ℕ} (h : Imp E Z L) (hL : L' ≤ L) : Imp E Z L' := fun q hq => h q (by omega)
lemma tabE_ok {e : Bool × ℕ × ℕ} {own : List ℕ} {raw : List (ℕ × ℕ)} (hr : ∀ x ∈ raw, Imp [] x.1 x.2)
    (ho : ∀ x ∈ raw, x.1 ∈ own → Imp [e] x.1 x.2) : ∀ y ∈ tabE e own raw, Imp [e] y.1 y.2 := by
  intro y hy
  simp only [tabE, List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  change Imp [e] x.1 (tabV e own x)
  unfold tabV
  cases h : own.any (fun c => Nat.beq c x.1) with
  | true =>
    rw [List.any_eq_true] at h
    obtain ⟨c, hc, h⟩ := h
    rw [Nat.eq_of_beq_eq_true h] at hc
    exact ho x hx hc
  | false =>
    cases h2 : trivE e x.1 with
    | true => exact impA h2 (hr x hx)
    | false => exact impB (hr x hx)
lemma tz_sub {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') : tz Z &&& mz Z' = tz Z' := by
  simp only [tz, nl, Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]
lemma Im_WZ {E : List (Bool × ℕ × ℕ)} {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ WZ E Z) : Im (mz Z') S ⊆ WZ E Z' := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hS hy
  exact ⟨w, hw, by simp only [Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]⟩
lemma npOf_eq (P : List ℕ) : npOf P = lane (WL NN) 16 (fun j => P.getD j 0) := by
  rw [npOf, laneL_eq, List.length_map, List.length_range]
  refine lane_congr fun j hj => ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]; rfl
lemma PZ_lt (Q : List (ℕ × ℕ)) (j : ℕ) : (PZ Q).getD j 0 < 2 ^ (2 * NN) := by
  rw [PZ, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases Q[j]? with
  | none => exact Nat.two_pow_pos _
  | some x => exact mz_lt _
noncomputable section
end
lemma pL_cons (d : ℕ) (L : List ℕ) : pL (d :: L) = 2 ^ 5 * pL L + d := by
  change (pL L <<< 5) + d = _; rw [Nat.shiftLeft_eq]; ring
lemma pL_pk (L : List ℕ) : pL L = pk L.length (fun j => L.getD j 0) := by
  induction L with
  | nil => simp [pL, pk]
  | cons d L ih =>
    rw [pL_cons, ih, pk, pk, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.mul_zero, pow_zero, mul_one, List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 5 * (j + 1) = 5 * j + 5 by ring, pow_add]; ring
lemma pL_bit {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : ∀ i, (pL L).testBit i = true ↔ (i % 5 = 0 ∧ i / 5 < L.length ∧ L.getD (i / 5) 0 = 1) := by
  induction L with
  | nil => intro i; simp [pL]
  | cons d L ih =>
    intro i
    have hd := h d (by simp)
    have ih := ih fun x hx => h x (by simp [hx])
    rw [pL_cons, Nat.testBit_two_pow_mul_add _ (by omega)]
    split_ifs with hi
    · have : i / 5 = 0 := by omega
      rw [this]
      rcases Nat.eq_zero_or_pos i with rfl | hp
      · interval_cases d <;> simp
      · constructor
        · intro hb
          have : d.testBit i = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hd (Nat.one_lt_two_pow (by omega)))
          rw [this] at hb; simp at hb
        · intro hb; omega
    · rw [ih, show i / 5 = (i - 5) / 5 + 1 by omega]
      simp only [List.length_cons, List.getD_cons_succ]
      constructor
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
lemma pL_isPk {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : isPk L.length (pL L) := fun i hi => by
  have := (pL_bit h i).1 hi; exact ⟨this.1, this.2.1⟩
noncomputable section
end
lemma fl0_eq (s : ℕ) (P : List ℕ) : fl0 s P = pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0)) := by
  induction P with
  | nil => rfl
  | cons n P ih => rw [List.map_cons, pL_cons, ← ih]; change (fl0 s P) <<< 5 + _ = _; rw [Nat.shiftLeft_eq]; ring
lemma fl1_eq (s : ℕ) (P : List ℕ) : fl1 s P = pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)) := by
  induction P with
  | nil => rfl
  | cons n P ih => rw [List.map_cons, pL_cons, ← ih]; change (fl1 s P) <<< 5 + _ = _; rw [Nat.shiftLeft_eq]; ring
lemma mkW_ok (P : List ℕ) (s : ℕ) : WOk P (mkW P s) := by
  have h01 : ∀ f : ℕ → Bool, ∀ d ∈ P.map (fun n => bit01 (f n)), d ≤ 1 := by
    intro f d hd; simp only [List.mem_map] at hd
    obtain ⟨n, _, rfl⟩ := hd; cases f n <;> simp [bit01]
  have bt : ∀ f : ℕ → Bool, ∀ j < P.length, (pL (P.map fun n => bit01 (f n))).testBit (5 * j) = true → f (P.getD j 0) = true := by
    intro f j hj h
    have h := ((pL_bit (h01 f) _).1 h).2.2
    rw [show 5 * j / 5 = j by omega, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp at h ⊢
    cases hf : f P[j] <;> simp [bit01, hf] at h ⊢
  refine ⟨?_, ?_, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) 0)
    rw [List.length_map, ← fl0_eq] at this; exact this
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) n)
    rw [List.length_map, ← fl1_eq] at this; exact this
  · change (fl0 s P).testBit (5 * j) = true at h
    rw [fl0_eq] at h
    exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) 0) j hj h)
  · change (fl1 s P).testBit (5 * j) = true at h
    rw [fl1_eq] at h
    exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) n) j hj h)
noncomputable section
end
lemma mkA_eq (P L : List ℕ) : ∀ h, mkA P L h = h (L.map (mkW P)) := by
  induction L with
  | nil => intro h; rfl
  | cons s L ih =>
    intro h
    change st s (fun s => st (fl0 s P) fun a => st (fl1 s P) fun b => st (Nat.lor a b) fun c => mkA P L fun r => h (⟨s, a, b, c, 3, 0⟩ :: r)) = _
    simp only [st_eq]; rw [ih]; rfl
lemma frcP_eq (L : List ℕ) : ∀ h, frcP L h = h L := by
  induction L with
  | nil => intro h; rfl
  | cons s L ih =>
    intro h
    change st s (fun s => frcP L fun r => h (s :: r)) = _
    simp only [st_eq]; rw [ih]
lemma anySub_false {d : Bool} {l : ℕ} {v : List W} : ∀ {c : ℕ} {h : List W → Bool}, (∀ i, c.testBit i = true → l.testBit i = true) → anySub d l v c h = false →
    ∀ r, r.Sublist v → (∀ i, l.testBit i = true → c.testBit i = true ∨ (cov d l r).testBit i = true) → h r = false := by
  induction v with
  | nil => intro c h _ hh r hr _; rw [List.sublist_nil.1 hr]; exact hh
  | cons w v ih =>
    intro c h hcl hh r hr hcov
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (anySub d l v c h) (Nat.beq (Nat.lor c (cov d l v)) l)) true
      (st (Nat.lor c (sp d l w.s)) fun c => anySub d l v c fun r => h (w :: r)) : Bool) = false at hh
    rw [bR, bR, st_eq] at hh
    cases h1 : anySub d l v (Nat.lor c (sp d l w.s)) (fun r => h (w :: r)) with
    | true => rw [h1] at hh; simp at hh
    | false =>
      rw [h1, Bool.cond_false] at hh
      have hc2 : ∀ i, (cov d l v).testBit i = true → l.testBit i = true := by
        intro i hi
        obtain ⟨w', _, hw'⟩ := (cov_bit _ _ _ _).1 hi
        rw [sp_bit, Bool.and_eq_true] at hw'; exact hw'.1
      cases hr with
      | cons _ hr =>
        have : Nat.beq (Nat.lor c (cov d l v)) l = true := by
          rw [Nat.beq_eq]
          apply Nat.eq_of_testBit_eq; intro i
          rw [no, Nat.testBit_or]
          cases hli : l.testBit i with
          | false =>
            by_contra hc
            rw [Bool.not_eq_false, Bool.or_eq_true] at hc
            rcases hc with h | h
            · rw [hcl i h] at hli; simp at hli
            · rw [hc2 i h] at hli; simp at hli
          | true =>
            rcases hcov i hli with h | h
            · rw [h]; rfl
            · obtain ⟨w', hw', h2⟩ := (cov_bit _ _ _ _).1 h
              rw [(cov_bit d l i v).2 ⟨w', hr.subset hw', h2⟩]; simp
        rw [this, Bool.cond_true] at hh
        exact ih hcl hh r hr hcov
      | cons_cons _ hr =>
        rename_i r'
        refine ih (c := Nat.lor c (sp d l w.s)) ?_ h1 r' hr ?_
        · intro i hi
          rw [no, Nat.testBit_or, Bool.or_eq_true] at hi
          rcases hi with h | h
          · exact hcl i h
          · rw [sp_bit, Bool.and_eq_true] at h; exact h.1
        · intro i hi
          rw [no, Nat.testBit_or, Bool.or_eq_true]
          rcases hcov i hi with h | h
          · exact Or.inl (Or.inl h)
          · change (Nat.lor (sp d l w.s) (cov d l r')).testBit i = true at h
            rw [no, Nat.testBit_or, Bool.or_eq_true] at h
            rcases h with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
lemma addN_cons (o w : ℕ) (t : List ℕ) : addN o (w :: t) = bif Nat.ble w o then (bif Nat.beq o w then w :: t else o :: w :: t) else w :: addN o t := by
  change Bool.rec (motive := fun _ => List ℕ) (w :: addN o t) (Bool.rec (motive := fun _ => List ℕ) (o :: w :: t) (w :: t) (Nat.beq o w)) (Nat.ble w o) = _
  cases Nat.ble w o <;> cases Nat.beq o w <;> rfl
lemma addN_spec {o : ℕ} {v : List ℕ} (hv : Srt v) : Srt (addN o v) ∧ ∀ w, w ∈ addN o v ↔ w = o ∨ w ∈ v := by
  induction v with
  | nil => exact ⟨List.pairwise_singleton _ _, by simp [addN]⟩
  | cons x t ih =>
    have hp := List.pairwise_cons.1 hv
    obtain ⟨i1, i2⟩ := ih hp.2
    rw [addN_cons]
    cases h1 : Nat.ble x o with
    | true =>
      have hle := Nat.le_of_ble_eq_true h1
      cases h2 : Nat.beq o x with
      | true =>
        have e := Nat.eq_of_beq_eq_true h2
        refine ⟨hv, fun w => ?_⟩
        simp only [Bool.cond_true, List.mem_cons]; constructor
        · intro h; exact Or.inr h
        · rintro (rfl | h)
          · exact Or.inl e
          · exact h
      | false =>
        have hne : o ≠ x := fun e => by rw [e, Nat.beq_refl] at h2; simp at h2
        refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, hv⟩, fun w => by simp⟩
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · omega
        · have := hp.1 w hw; omega
    | false =>
      have hlt : o < x := by
        by_contra hc; rw [Nat.ble_eq_true_of_le (by omega)] at h1; simp at h1
      refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, i1⟩, fun w => ?_⟩
      · rcases (i2 w).1 hw with rfl | h
        · exact hlt
        · exact hp.1 w h
      · simp only [Bool.cond_false, List.mem_cons, i2]; grind
lemma avl_spec (m : ℕ) (L : List ℕ) : Srt (avl m L) ∧ ∀ w, w ∈ avl m L ↔ w ≠ 0 ∧ w ≠ m ∧ ∃ x ∈ L, w = x &&& m := by
  induction L with
  | nil => exact ⟨List.Pairwise.nil, by simp [avl]⟩
  | cons y L ih =>
    obtain ⟨i1, i2⟩ := ih
    have e : avl m (y :: L) = bif Nat.beq (Nat.land y m) 0 then avl m L else bif Nat.beq (Nat.land y m) m then avl m L else addN (Nat.land y m) (avl m L) := by
      change Bool.rec (motive := fun _ => List ℕ) (Bool.rec (motive := fun _ => List ℕ) (addN (Nat.land y m) (avl m L)) (avl m L) (Nat.beq (Nat.land y m) m)) (avl m L) (Nat.beq (Nat.land y m) 0) = _
      cases Nat.beq (Nat.land y m) 0 <;> cases Nat.beq (Nat.land y m) m <;> rfl
    rw [e]
    cases h1 : Nat.beq (Nat.land y m) 0 with
    | true =>
      have h0 : y &&& m = 0 := Nat.eq_of_beq_eq_true h1
      refine ⟨i1, fun w => ?_⟩
      simp only [Bool.cond_true, i2, List.mem_cons]
      constructor
      · rintro ⟨a, b, x, hx, e⟩; exact ⟨a, b, x, Or.inr hx, e⟩
      · rintro ⟨a, b, x, rfl | hx, e'⟩
        · exact absurd (e'.trans h0) a
        · exact ⟨a, b, x, hx, e'⟩
    | false =>
      cases h1' : Nat.beq (Nat.land y m) m with
      | true =>
        have h0 : y &&& m = m := Nat.eq_of_beq_eq_true h1'
        refine ⟨i1, fun w => ?_⟩
        simp only [Bool.cond_true, Bool.cond_false, i2, List.mem_cons]
        constructor
        · rintro ⟨a, b, x, hx, e⟩; exact ⟨a, b, x, Or.inr hx, e⟩
        · rintro ⟨a, b, x, rfl | hx, e'⟩
          · exact absurd (e'.trans h0) b
          · exact ⟨a, b, x, hx, e'⟩
      | false =>
        have n1 : y &&& m ≠ 0 := fun e => by
          have : Nat.beq (Nat.land y m) 0 = true := by rw [nl, e]; rfl
          rw [this] at h1; simp at h1
        have n2 : y &&& m ≠ m := fun e => by
          have : Nat.beq (Nat.land y m) m = true := by rw [nl, e]; exact Nat.beq_refl m
          rw [this] at h1'; simp at h1'
        obtain ⟨j1, j2⟩ := addN_spec (o := Nat.land y m) i1
        refine ⟨j1, fun w => ?_⟩
        rw [Bool.cond_false, Bool.cond_false, j2, i2]
        constructor
        · rintro (rfl | ⟨a, b, x, hx, e'⟩)
          · exact ⟨n1, n2, y, by simp, rfl⟩
          · exact ⟨a, b, x, by simp [hx], e'⟩
        · rintro ⟨a, b, x, hx, e'⟩
          rcases List.mem_cons.1 hx with rfl | hx
          · exact Or.inl e'
          · exact Or.inr ⟨a, b, x, hx, e'⟩
lemma hb_mod (H x : ℕ) : hb H x = hb H (x % MM) := by
  unfold hb
  change Nat.beq ((H >>> (x % MM)) &&& 1) 1 = Nat.beq ((H >>> (x % MM % MM)) &&& 1) 1
  rw [Nat.mod_mod]
lemma fbOk_spec {E F : List (Bool × ℕ × ℕ)} {fb : ℕ × ℕ} (h : fbOk E F fb = true) {x y : ℕ} (hx : x ∈ WZ E 0) (hy : y ∈ WZ E 0) (hxy : x ≠ y) {d : Bool}
    (hb : fbit fb.1 fb.2 (op d x y) = true) : ∃ f ∈ F, op d x y = tw f &&& mz 0 := by
  obtain ⟨wx, hwx, rfl⟩ := hx
  obtain ⟨wy, hwy, rfl⟩ := hy
  simp only [fbOk, List.all_eq_true, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_true, exists_exists_and_eq_and] at h
  have h := (h wx hwx wy hwy).resolve_left fun e => hxy (Nat.eq_of_beq_eq_true e)
  simp only [nl, no] at h
  cases d with
  | false =>
    rcases h.1 with h | ⟨f, hf, h⟩
    · change fbit fb.1 fb.2 (wx &&& mz 0 &&& (wy &&& mz 0)) = true at hb
      rw [h] at hb; simp at hb
    · exact ⟨f, hf, Nat.eq_of_beq_eq_true h⟩
  | true =>
    rcases h.2 with h | ⟨f, hf, h⟩
    · change fbit fb.1 fb.2 (wx &&& mz 0 ||| (wy &&& mz 0)) = true at hb
      rw [h] at hb; simp at hb
    · exact ⟨f, hf, Nat.eq_of_beq_eq_true h⟩
lemma fbit_triv (s : ℕ) : fbit 1 0 s = false := by
  unfold fbit
  change Nat.beq ((0 >>> (s % 1)) &&& 1) 1 = false
  rw [Nat.zero_shiftRight]; rfl
lemma sumc_eq {P : List ℕ} {v : List W} (hw : ∀ w ∈ v, WOk P w) : sumc v = pk P.length (cnt v) := by
  induction v with
  | nil => simp [sumc, pk, cnt]
  | cons w v ih =>
    change w.c + sumc v = _
    rw [ih fun x hx => hw x (by simp [hx]), fl_pk (hw w (by simp)), pk_add]
    exact pk_congr fun j _ => by rw [cnt_cons]
lemma pk16 (Q : List (ℕ × ℕ)) (K : ℕ) : pL (Q.map fun e => 16 + (K - e.2)) = pk (PZ Q).length (fun j => 16 + (K - (Q.getD j (0, K)).2)) := by
  rw [pL_pk, PZ, List.length_map, List.length_map]
  refine pk_congr fun j hj => ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
lemma RZ_set (E : List (Bool × ℕ × ℕ)) (Z : ℕ) : {x | RZ E Z x ≠ 0} = WZ E Z := by
  ext x; simp only [RZ, Set.mem_ofPred_eq]; split_ifs with h <;> simp [h]
lemma RZ_mem {E : List (Bool × ℕ × ℕ)} {Z x : ℕ} (h : RZ E Z x ≠ 0) : x ∈ WZ E Z := by
  have : x ∈ {x | RZ E Z x ≠ 0} := h
  rwa [RZ_set] at this
lemma RZ_R2 (E : List (Bool × ℕ × ℕ)) (Z : ℕ) : ∀ d a b, (RZ E Z a = 0 ∨ RZ E Z b = 0) → Al (RZ E Z) d a b := by
  intro d a b h
  unfold Al
  rcases h with h | h <;> rw [h] <;> simp
lemma hasP_ok {p : ℕ} {v : List W} (h : p = 0 ∨ ∃ w ∈ v, w.s = p) : hasP p v = true := by
  unfold hasP
  rw [bR]
  rcases h with rfl | ⟨w, hw, rfl⟩
  · rfl
  · have : (List.rec (motive := fun _ => Bool) false (fun w' _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w'.s w.s)) v : Bool) = true := by
      induction v with
      | nil => simp at hw
      | cons x v ih =>
        change (Bool.rec (motive := fun _ => Bool) (List.rec (motive := fun _ => Bool) false (fun w' _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w'.s w.s)) v : Bool) true (Nat.beq x.s w.s) : Bool) = true
        rw [bR]
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · rw [Nat.beq_refl]; rfl
        · rw [ih hw]; cases Nat.beq x.s w.s <;> rfl
    rw [this]; cases Nat.beq w.s 0 <;> rfl
noncomputable section
end
lemma frcQ_eq (Q : List (ℕ × ℕ)) : ∀ h, frcQ Q h = h Q := by
  induction Q with
  | nil => intro h; rfl
  | cons x Q ih =>
    intro h
    change st x.1 (fun c => st x.2 fun L => frcQ Q fun r => h ((c, L) :: r)) = _
    simp only [st_eq]; rw [ih]
lemma lnW_eq (v : List W) : lnW v = v.length := by
  induction v with
  | nil => rfl
  | cons w v ih => change Nat.succ (lnW v) = _; rw [ih]; rfl
lemma anyN_false {h : ℕ → Bool} {L : List ℕ} (hh : anyN h L = false) : ∀ t ∈ L, h t = false := by
  induction L with
  | nil => simp
  | cons a L ih =>
    change (Bool.rec (motive := fun _ => Bool) (anyN h L) true (h a) : Bool) = false at hh
    rw [bR] at hh
    intro t ht
    cases ha : h a with
    | true => rw [ha] at hh; simp at hh
    | false =>
      rw [ha, Bool.cond_false] at hh
      rcases List.mem_cons.1 ht with rfl | ht
      · exact ha
      · exact ih hh t ht
lemma pre_eq (E : List (Bool × ℕ × ℕ)) (Q : List (ℕ × ℕ)) (Z K : ℕ) (h : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) :
    pre E Q Z K h = h (lz Z) (mz Z) (npOf (PZ Q)) (pL (Q.map fun _ => 16)) (pL (Q.map fun e => 16 + (K - e.2))) (pwr E Z) ((avl (mz Z) (rawL E)).map (mkW (PZ Q))) := by
  simp only [pre, frcQ_eq, frcP_eq, st_eq, mkA_eq]
lemma chkT_chk {top : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool} {E : List (Bool × ℕ × ℕ)} {Q : List (ℕ × ℕ)} {fb : ℕ × ℕ} {Z K : ℕ} {ts : List ℕ} {H ph : ℕ}
    (h : chkT top E Q fb Z K ts H ph = false) : ∀ t ∈ ts, chkG top E Q fb Z K t H ph = false := by
  intro t ht
  simp only [chkT, chkG, st_eq, pre_eq] at h ⊢
  exact anyN_false h t ht
lemma RZ_RR (E : List (Bool × ℕ × ℕ)) (Z : ℕ) : ∀ d a b, RZ E Z a ≠ 0 → RZ E Z b ≠ 0 → ¬ Al (RZ E Z) d a b := by
  intro d a b ha hb h
  have h3 : ∀ x, RZ E Z x ≠ 0 → RZ E Z x = 3 := by
    intro x hx; unfold RZ at hx ⊢; split_ifs at hx ⊢ with h
    · rfl
    · simp at hx
  unfold Al at h
  rw [h3 a ha, h3 b hb] at h
  cases d <;> simp at h
theorem imp_FK {top : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool} (htop : TopOk top)
    {E F : List (Bool × ℕ × ℕ)} {Q : List (ℕ × ℕ)} {fb : ℕ × ℕ} {Z L K : ℕ} (hLK : L ≤ K + 1) (hK : K ≤ 15) (hE : E = [] ∨ ∃ e, E = [e] ∧ e.2.1 < 10 ∧ e.2.2 < 10 ∧ Imp [] Z L)
    (hp : pOk Z Q = true) (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hfb : fb = (1, 0) ∨ (Z = 0 ∧ fbOk E F fb = true)) (hF : ∀ e ∈ F, Imp [e] 0 (L - 1 + E.length))
    (hb : (∃ e ∈ Q, L ≤ e.2) ∨ ∀ t < L, ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chkG top E Q fb Z K t p.1 p.2 = false) : Imp E Z L := by
  intro q hq hsol
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE1 : E.length ≤ 1 := by rcases hE with rfl | ⟨e, rfl, _⟩ <;> simp
  classical
  have hex : ∃ q, Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)) := ⟨q, hsol⟩
  have hqL : Nat.find hex < L := lt_of_le_of_lt (Nat.find_min' hex hsol) hq
  obtain ⟨k, hk, t, S, hS, hl⟩ := (Nat.find_spec hex).live
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hkeq : k = Nat.find hex := le_antisymm hk (Nat.find_min' hex (hl.sol.mono le_rfl hS))
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => Nat.find_min hex (by omega) (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno e he q' (by omega) hs'
  have hpw : pwr E Z = 0 ∨ pwr E Z ∈ S := by
    rcases hE with rfl | ⟨e, rfl, _, _, hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k (by omega) (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      simp only [rawL, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w, by simp only [rawL, List.map_nil, List.append_nil]; exact hw, rfl⟩
      · have hx : tw e &&& mz Z ∈ S := by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨M, hMf, hchk⟩ := hb t (by omega)
  obtain ⟨a1, a2⟩ := avl_spec (mz Z) (rawL E)
  set v := ((avl (mz Z) (rawL E)).filter (fun s => decide (s ∈ S))).map (mkW (PZ Q)) with hv
  have hsub : v.Sublist ((avl (mz Z) (rawL E)).map (mkW (PZ Q))) := List.filter_sublist.map _
  have hvs : v.map W.s = (avl (mz Z) (rawL E)).filter (fun s => decide (s ∈ S)) := by
    rw [hv, List.map_map]; exact List.map_id _
  have hnd : (v.map W.s).Nodup := by
    rw [hvs]
    exact (a1.sublist List.filter_sublist).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, hvs, List.mem_filter, a2]
    constructor
    · rintro ⟨_, hx⟩; simpa using hx
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      exact ⟨⟨fun e => h0 (e ▸ hx), fun e => h1 (e ▸ hx), w, hw, rfl⟩, by simpa using hx⟩
  have hvm : ∀ w ∈ v, ∃ x ∈ rawL E, w = mkW (PZ Q) (x &&& mz Z) := by
    intro w hw
    rw [hv, List.mem_map] at hw
    obtain ⟨s, hs, rfl⟩ := hw
    obtain ⟨_, _, x, hx, rfl⟩ := (a2 s).1 (List.mem_of_mem_filter hs)
    exact ⟨x, hx, rfl⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := hvm w hw; exact mkW_ok _ _
  have hcod : ∀ w ∈ v, w.r = RZ E Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hvm w hw
    have : x &&& mz Z ∈ WZ E Z := ⟨x, hx, rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ, if_pos this]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hvm w hw; exact wire_good hx Z
  have hd0 : ∀ w ∈ v, w.d = 0 := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hvm w hw; rfl
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, K)).1 ∧ Q.getD j (0, K) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (npOf (PZ Q)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_, ⟨fun j => (PZ Q).getD j 0, fun j _ => PZ_lt Q j, npOf_eq _, fun j _ _ => Nat.and_self _⟩⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hA : ∀ j < (PZ Q).length, Acc ((PZ Q).getD j 0) (tz Z) K (K - (Q.getD j (0, K)).2) (fun _ => 0) S := by
    intro j hj
    obtain ⟨e1, e2⟩ := hPget j hj
    rw [e1]
    exact Acc.start (L := (Q.getD j (0, K)).2) (hno _ e2) subset_rfl (by omega)
  have hle := cnt_le X (D := fun _ _ => 0) hrep hwok hA hm (by omega)
  have hz : pL (Q.map fun e => 16 + (K - e.2)) - sumc v = pk (PZ Q).length (fun j => 16 + (K - (Q.getD j (0, K)).2) - cnt v j) := by
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hst : StOk (PZ Q) (tz Z) (lz Z) K (pL (Q.map fun e => 16 + (K - e.2)) - sumc v) v S := by
    rw [hz]
    exact StOk.start hrep hwok hgood (by omega) (fun j _ => by omega) hd0 hA
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, show pos t = pos' t by cases t <;> simp [pos, pos'], hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble (lnW v) (Nat.sub (Nat.succ K) t) = true := Nat.ble_eq_true_of_le (by
    rw [lnW_eq]; change v.length ≤ K + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, top (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (npOf (PZ Q)) fb.1 fb.2 K p.1 p.2 K t (pL (Q.map fun e => 16 + (K - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chkG, st_eq, pre_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startG, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => top (lz Z) (mz Z) _ (npOf (PZ Q)) fb.1 fb.2 K p.1 p.2 K t z r) (fun h => rfl) rfl hst hm (by omega) h3
  have hW : {x | RZ E Z x ≠ 0} ∪ (S : Set ℕ) = WZ E Z := by rw [RZ_set]; exact Set.union_eq_self_of_subset_right hSW
  refine htop X (RZ_RR E Z) (RZ_R2 E Z) (Fs := {s | ∃ f ∈ F, s = tw f &&& mz Z ∧ Z = 0}) hMf all hst hcod (by omega) hl ?_ ?_ ?_
  · intro q hq hs
    rw [hW] at hs
    exact Nat.find_min hex (show q < Nat.find hex by omega) hs
  · intro d x y hxy hx hy hbit
    rcases hfb with rfl | ⟨rfl, hfb⟩
    · rw [fbit_triv] at hbit; simp at hbit
    · obtain ⟨f, hf, e⟩ := fbOk_spec hfb (RZ_mem hx) (RZ_mem hy) hxy hbit
      exact ⟨f, hf, e, rfl⟩
  · rintro s ⟨f, hf, rfl, rfl⟩ q hq hs
    rw [hW] at hs
    exact forb_ok hE1 (hF f hf) q (by omega) hs
lemma Live.W {m T k t : ℕ} {S : Finset ℕ} {Q : Set ℕ} (hl : Live R m T k t S) (hQ : (S : Set ℕ) ⊆ Q) : Sol Z0 m T k Q := hl.sol.mono le_rfl hQ
lemma front {m T : ℕ} (hR : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {k t : ℕ} {S : Finset ℕ} (hl : Live Z0 m T k t S)
    (hm : ∀ q < k, ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) :
    Live R m T k t S ∨ ∃ k0 d a b S1, k = k0 + 1 ∧ R a ≠ 0 ∧ R b ≠ 0 ∧ Bi Z0 d a b S S1 ∧ Live Z0 m T k0 t S1 := by
  induction hl with
  | stop => exact Or.inl .stop
  | @un k t a U hl ih =>
    set Q : Set ℕ := {x | R x ≠ 0} with hQ
    have hfr : a ^^^ m ∉ C m (Q ∪ ((insert a U : Finset ℕ) : Set ℕ)) := by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU : a ^^^ m ∉ U := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR : R (a ^^^ m) = 0 := by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm' : ∀ q < k, ¬ Sol Z0 m T q (C m (Q ∪ ((insert (a ^^^ m) U : Finset ℕ) : Set ℕ))) := by
      intro q hq hs
      refine hm (q + 1) (by omega) (.un (a := a) (Or.inl (Or.inr (by simp))) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0, d, x, y, S1, rfl, hx, hy, ⟨hxy, V, e1, rfl, hal⟩, hl1⟩
    · exact Or.inl (.un h)
    · have nx : x ≠ a ^^^ m := fun e => hx (e ▸ hfR)
      have ny : y ≠ a ^^^ m := fun e => hy (e ▸ hfR)
      have hmV : a ^^^ m ∈ V := by
        have : a ^^^ m ∈ insert x (insert y V) := by rw [← e1]; simp
        simp at this
        rcases this with h | h | h
        · exact absurd h.symm nx
        · exact absurd h.symm ny
        · exact h
      have eU : U = insert x (insert y (V.erase (a ^^^ m))) := by
        ext z
        by_cases hz : z = a ^^^ m
        · subst hz
          simp [hfU, Ne.symm nx, Ne.symm ny]
        · have : z ∈ insert (a ^^^ m) U ↔ z ∈ insert x (insert y V) := by rw [e1]
          simp only [Finset.mem_insert, hz, false_or, Finset.mem_erase, ne_eq, not_false_eq_true, true_and] at this ⊢
          exact this
      refine Or.inr ⟨k0 + 1, d, x, y, insert a (insert (op d x y) (V.erase (a ^^^ m))), rfl, hx, hy,
        ⟨hxy, insert a (V.erase (a ^^^ m)), ?_, ?_, hal⟩, ?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]; grind
      · ext z; simp only [Finset.mem_insert]; grind
      · refine .un ?_
        have : insert (a ^^^ m) (insert (op d x y) (V.erase (a ^^^ m))) = insert (op d x y) V := by
          rw [Finset.insert_comm, Finset.insert_erase hmV]
        rw [this]; exact hl1
  | @bi k t d0 a b U hab hal0 hl ih =>
    set Q : Set ℕ := {x | R x ≠ 0} with hQ
    have hb0 : Bi Z0 d0 a b (insert a (insert b U)) (insert (op d0 a b) U) := ⟨hab, U, rfl, rfl, hal0⟩
    by_cases hW : R a ≠ 0 ∧ R b ≠ 0
    · exact Or.inr ⟨k, d0, a, b, _, rfl, hW.1, hW.2, hb0, hl⟩
    have hal : Al R d0 a b := hR _ _ _ (by
      by_contra hc; push Not at hc; exact hW hc)
    have hfr : op d0 a b ∉ C m (Q ∪ ((insert a (insert b U) : Finset ℕ) : Set ℕ)) := by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU : op d0 a b ∉ U := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfa : op d0 a b ≠ a := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfb : op d0 a b ≠ b := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR : R (op d0 a b) = 0 := by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm' : ∀ q < k, ¬ Sol Z0 m T q (C m (Q ∪ ((insert (op d0 a b) U : Finset ℕ) : Set ℕ))) := by
      intro q hq hs
      refine hm (q + 1) (by omega) (.bi (d := d0) (a := a) (b := b) (Or.inl (Or.inr (by simp))) (Or.inl (Or.inr (by simp))) (al0 _ _ _) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0, d, x, y, S1, rfl, hx, hy, ⟨hxy, V, e1, rfl, hal'⟩, hl1⟩
    · exact Or.inl (.bi hab hal h)
    · set o := op d0 a b with ho
      have nx : x ≠ o := fun e => hx (e ▸ hfR)
      have ny : y ≠ o := fun e => hy (e ▸ hfR)
      have hmV : o ∈ V := by
        have : o ∈ insert x (insert y V) := by rw [← e1]; simp
        simp at this
        rcases this with h | h | h
        · exact absurd h.symm nx
        · exact absurd h.symm ny
        · exact h
      have eU : U = insert x (insert y (V.erase o)) := by
        ext z
        by_cases hz : z = o
        · subst hz
          simp [hfU, Ne.symm nx, Ne.symm ny]
        · have : z ∈ insert o U ↔ z ∈ insert x (insert y V) := by rw [e1]
          simp only [Finset.mem_insert, hz, false_or, Finset.mem_erase, ne_eq, not_false_eq_true, true_and] at this ⊢
          exact this
      refine Or.inr ⟨k0 + 1, d, x, y, insert a (insert b (insert (op d x y) (V.erase o))), rfl, hx, hy,
        ⟨hxy, insert a (insert b (V.erase o)), ?_, ?_, hal'⟩, ?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h | h) <;> simp only [h, true_or, or_true])
      · ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h) <;> simp only [h, true_or, or_true])
      · refine .bi hab hal0 ?_
        have : insert (op d0 a b) (insert (op d x y) (V.erase o)) = insert (op d x y) V := by
          rw [Finset.insert_comm, ← ho, Finset.insert_erase hmV]
        rw [this]; exact hl1
lemma MW.min {m T k t : ℕ} {S : Finset ℕ} (h : MW R m T k S) (hl : Live Z0 m T k t S) : Min Z0 m T k t S :=
  ⟨hl, fun q hq hs => h q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
lemma step_sub {m : ℕ} {A : Set ℕ} {S S1 : Finset ℕ} {g : ℕ} (h : S1 ⊆ insert g S) :
    C m (A ∪ (S1 : Set ℕ)) ⊆ insert g (C m (A ∪ (S : Set ℕ))) := by
  rintro x ((hx | hx) | hx)
  · exact Or.inr (Or.inl (Or.inl hx))
  · have hx' := h hx
    simp only [Finset.mem_insert] at hx'
    rcases hx' with rfl | hx'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (Or.inr hx'))
  · exact Or.inr (Or.inr hx)
lemma MW.bi {m T k a b : ℕ} {d : Bool} {S S1 : Finset ℕ} (h : MW R m T (k + 1) S) (hb : Bi Z0 d a b S S1) : MW R m T k S1 := by
  intro q hq hs
  exact h (q + 1) (by omega) (.bi (d := d) (a := a) (b := b) (Or.inl (Or.inr hb.sub.1)) (Or.inl (Or.inr hb.sub.2.1)) (al0 _ _ _) (hs.mono le_rfl (step_sub hb.sub.2.2)))
lemma MF.bi {m T k a b : ℕ} {Fs : Set ℕ} {d : Bool} {S S1 : Finset ℕ} (h : MF R m T (k + 1) Fs S) (hb : Bi Z0 d a b S S1) : MF R m T k Fs S1 := by
  intro s hsF q hq hs
  refine h s hsF (q + 1) (by omega) (.bi (d := d) (a := a) (b := b) (Or.inl (Or.inr (Or.inr hb.sub.1))) (Or.inl (Or.inr (Or.inr hb.sub.2.1))) (al0 _ _ _) (hs.mono le_rfl ?_))
  rw [← Set.insert_union, ← Set.insert_union]
  exact step_sub hb.sub.2.2
lemma MF.gate {m T k t a b : ℕ} {Fs : Set ℕ} {d : Bool} {S S1 : Finset ℕ} (h : MF R m T (k + 1) Fs S) (hb : Bi Z0 d a b S S1) (hl : Live Z0 m T k t S1)
    (hg : op d a b ∈ Fs) : False := by
  refine h _ hg k (by omega) (hl.sol.mono le_rfl fun x hx => ?_)
  have hx' := hb.sub.2.2 hx
  simp only [Finset.mem_insert] at hx'
  rcases hx' with rfl | hx'
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr (Or.inr hx'))
theorem phase_step (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {P : List ℕ} {m T l k k' t : ℕ} {f : ℕ → List W → Bool} {v : List W} {S : Finset ℕ} {fm fh : ℕ} {Fs : Set ℕ}
    (hrep : Rep v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : MW R m T k' S) (hFb : MF R m T k' Fs S)
    (hfb : ∀ d x y, x ≠ y → R x ≠ 0 → R y ≠ 0 → fbit fm fh (op d x y) = true → op d x y ∈ Fs)
    (hA : ¬ Min R m T k' t S)
    (hB : ∀ (d : Bool) (a c : W) (S1 : Finset ℕ) (k0 : ℕ), a ∈ v → c ∈ v → a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → k' = k0 + 1 → Bi Z0 d a.s c.s S S1 → Live Z0 m T k0 t S1 →
      fbit fm fh (op d a.s c.s) = false → ∃ z' r, f z' r = false ∧ StOk P T l (k - 1) z' r S1 ∧ ∀ w ∈ r, (w.s = op d a.s c.s ∧ w.r = 0) ∨ ∃ w' ∈ v, w'.s = w.s ∧ w'.r = w.r)
    (hF : ∀ (z' : ℕ) (r : List W) (S1 : Finset ℕ), f z' r = false → StOk P T l (k - 1) z' r S1 → (∀ w ∈ r, w.r = R w.s) → ∀ k0 ≤ k - 1, Live Z0 m T k0 t S1 →
      MW R m T k0 S1 → MF R m T k0 Fs S1 → False) : False := by
  rcases front hR2 hl hmW with hlR | ⟨k0, d, a, b, S1, rfl, ha, hb', hb, hl1⟩
  · exact hA ⟨hlR, (hmW.min hl).2⟩
  · obtain ⟨wa, hwa, rfl⟩ := hrep.mem.1 hb.sub.1
    obtain ⟨wb, hwb, rfl⟩ := hrep.mem.1 hb.sub.2.1
    have hnf : fbit fm fh (op d wa.s wb.s) = false := by
      by_contra hc
      exact hFb.gate hb hl1 (hfb d wa.s wb.s hb.1 ha hb' (by simpa using hc))
    obtain ⟨z', r, hf, hst, hmem⟩ := hB d wa wb S1 k0 hwa hwb hb.1 (by rw [hcod wa hwa]; exact ha) (by rw [hcod wb hwb]; exact hb') rfl hb hl1 hnf
    have hfr : R (op d wa.s wb.s) = 0 := by
      by_contra hne
      refine hmW k0 (by omega) (hl1.sol.mono le_rfl fun x hx => ?_)
      have hx' := hb.sub.2.2 hx
      simp only [Finset.mem_insert] at hx'
      rcases hx' with rfl | hx'
      · exact Or.inl (Or.inl hne)
      · exact Or.inl (Or.inr hx')
    refine hF z' r S1 hf hst ?_ k0 (by omega) hl1 (hmW.bi hb) (hFb.bi hb)
    intro w hw
    rcases hmem w hw with ⟨e1, e2⟩ | ⟨w', hw', e1, e2⟩
    · rw [e1, e2, hfr]
    · rw [← e1, ← e2]; exact hcod w' hw'
noncomputable section
end
lemma pairsC_false {H : ℕ} {h : X → X → Bool} {xs : List X} (hp : pairsC H h xs = false) :
    xs.Pairwise (fun a b => hb H (a.s + b.s) = true → h a b = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairsC H h r) true
      (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · intro b hbm hi
      have h1 : scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r = false := by
        revert hp
        cases scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r <;> simp
      have h2 := scan_false h1 b hbm
      beta_reduce at h2
      rw [bR] at h2
      have h3 : hb H (Nat.add a.s b.s) = true := hi
      rwa [h3, Bool.cond_true] at h2
    · apply ih; revert hp; cases pairsC H h r <;> simp
lemma pairsC_any {H : ℕ} {h : X → X → Bool} {xs : List X} (hp : pairsC H h xs = false) {a c : X} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c) (hb' : hb H (a.s + c.s) = true) :
    h a c = false ∨ h c a = false := by
  have : Std.Symm (fun a b : X => hb H (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
    ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
  exact ((pairsC_false hp).imp (S := fun a b => hb H (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall ha hc hne hb'
lemma or_f {a b : Bool} (h : (Bool.rec (motive := fun _ => Bool) b true a : Bool) = false) : a = false ∧ b = false := by
  cases a <;> simp_all
lemma KP.toR {m T k' t : ℕ} {S : Finset ℕ} {v : List W} {κ : ℕ → Bool} {κ2 : ℕ → ℕ → Bool} (h : KP Z0 m T k' t S v κ κ2) : KP R m T k' t S v κ κ2 :=
  ⟨fun e hb hl ha hb' => h.g1 e (hb.rel fun d a b _ => al0 d a b) (hl.rel fun d a b _ => al0 d a b) ha hb',
    fun e hb hl ha hb' => h.g2 e (hb.rel fun d a b _ => al0 d a b) (hl.rel fun d a b _ => al0 d a b) ha hb'⟩
lemma mid1_false {fm fh : ℕ} {h : W → W → Bool → Bool → Bool → Bool → Bool → Nat → Nat → Nat → Bool} {a c : W} {oa oc ka kc kb : Bool} {s x y : ℕ}
    (hf : fbit fm fh s = false) (hh : mid1 fm fh h a c oa oc ka kc kb s x y = false) : h a c oa oc ka kc kb s x y = false := by
  have e : forb fm fh s = fbit fm fh s := rfl
  simp only [mid1, e, hf] at hh
  exact hh
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T)
include X
lemma one_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {fm fh fu : ℕ} {Fs : Set ℕ} {f : ℕ → ℕ → ℕ → List W → Bool}
    (hfb : ∀ d x y, x ≠ y → R x ≠ 0 → R y ≠ 0 → fbit fm fh (op d x y) = true → op d x y ∈ Fs)
    (hF : P1 R P l m T Fs f) {k t z : ℕ} {v : List W} {S : Finset ℕ} {κ : ℕ → Bool} {κ2 : ℕ → ℕ → Bool} (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hlen : 2 ≤ v.length)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : MW R m T k' S) (hFb : MF R m T k' Fs S) (hKP : KP Z0 m T k' t S v κ κ2)
    (h2 : mv (look l m g np fu) l m g np k t z v κ κ2 = false)
    (h1 : ∀ x y, x ∈ S → y ∈ S → x ≠ y → R x ≠ 0 → R y ≠ 0 → ∃ go : (L_meta_17357.X → L_meta_17357.X → Bool) → List L_meta_17357.X → Bool,
      node1 (f (k - 1) t) (pos' t) l m g np fm fh (k - t) v.length z v κ κ2 go = false ∧
      ∀ h xs, go h xs = false → ∀ a c : L_meta_17357.X, a ∈ xs → c ∈ xs → a.w.r ≠ 0 → c.w.r ≠ 0 → a.s = x → c.s = y → h a c = false ∨ h c a = false) : False := by
  refine phase_step hR2 (P := P) (l := l) (f := f (k - 1) t) (fm := fm) (fh := fh) (Fs := Fs) hs.rep hcod hk hl hmW hFb hfb ?_ ?_ ?_
  · intro hm
    exact mv_sound X hR (look_sound X hR fu) hs (fun w hw => Or.inr (hcod w hw)) hlen h2 k' hk hm hKP.toR
  · intro d a c S1 k0 ha hc hne har hcr e hb hl1 hnf
    subst e
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hm := hmW.min hl
    obtain ⟨go, hg1, hg2⟩ := h1 a.s c.s (hs.rep.mem.2 ⟨a, ha, rfl⟩) (hs.rep.mem.2 ⟨c, hc, rfl⟩) hne (by rw [← hcod a ha]; exact har) (by rw [← hcod c hc]; exact hcr)
    have hsz := (hb.min hl1 hm.2).size
    refine nodeH_bi X hs hm (by omega) rfl rfl (by omega) hb hl1 hKP ?_ ?_ hg1
    · intro a' c' oa oc ka kc kb x1 y1 e hh
      rw [e] at hh ⊢
      exact mid1_false hnf hh
    · intro h xs hgo hxs a' c' ha' hc' hav hcv ea ec eax ecy
      refine hg2 h xs hgo a' c' ha' hc' ?_ ?_ eax ecy
      · have : a'.w = a := hs.rep.inj hav ha (by rw [← ea, eax])
        rw [this]; exact har
      · have : c'.w = c := hs.rep.inj hcv hc (by rw [← ec, ecy])
        rw [this]; exact hcr
  · intro z' r S1 hf hst hcod' k0 hk0 hl1 hmW1 hFb1
    exact hF _ _ _ _ _ hf hst hcod' k0 hk0 hl1 hmW1 hFb1
theorem look1_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {fm fh K : ℕ} {Fs : Set ℕ}
    (hfb : ∀ d x y, x ≠ y → R x ≠ 0 → R y ≠ 0 → fbit fm fh (op d x y) = true → op d x y ∈ Fs) : ∀ fuel : ℕ, P1 R P l m T Fs (look1 l m g np fm fh K fuel) := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look1] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hl hmW hFb
    change (Bool.rec (motive := fun _ => Bool) (tsn (pos t) l (k + 1 - t) v (fun κ κ2 => Bool.rec (motive := fun _ => Bool) (mv (look l m g np k) l m g np k t z v κ κ2) true
        (st (k - 1) fun k1 => node1 (look1 l m g np fm fh K fuel k1 t) (pos t) l m g np fm fh (k - t) (len v) z v κ κ2 pairsS))) true (Nat.ble (len v) 1) : Bool) = false at h
    rw [bR, pos_eq, len_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      have hmin := hmW.min hl
      obtain ⟨κ, κ2, hFy, hKP⟩ := tsn_sound X hs hmin hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      obtain ⟨hy1, hy2⟩ := or_f hy
      rw [st_eq] at hy1
      refine one_sound X hR hR2 hfb ih hs hcod hlen hk hl hmW hFb hKP hy2 fun x y hx hy hne hxr hyr => ⟨pairsS, hy1, fun h xs hp a c ha hc har hcr ea ec => ?_⟩
      exact pairs_any hp (fs_mem ha har) (fs_mem hc hcr) (fun e => hne (by rw [← ea, ← ec, e]))
theorem topC_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {fm fh K k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)} {Fs : Set ℕ}
    (hM : mFull M = true) (h : ∀ p ∈ M, topC l m g np fm fh K p.1 p.2 k t z v = false) (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : MW R m T k' S)
    (hfb : ∀ d x y, x ≠ y → R x ≠ 0 → R y ≠ 0 → fbit fm fh (op d x y) = true → op d x y ∈ Fs) (hFb : MF R m T k' Fs S) : False := by
  simp only [mFull, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_eq_true] at hM
  obtain ⟨hM1, p0, hp0, hp1⟩ := hM
  have hmin := hmW.min hl
  obtain ⟨κ, κ2, hFy, hKP⟩ := tsn_sound X hs hmin hk
  have un : ∀ p ∈ M, 2 ≤ v.length ∧ (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g np k) l m g np k t z v κ κ2) (Nat.beq p.2 1)) true
      (st (k - 1) fun k1 => node1 (look1 l m g np fm fh K K k1 t) (pos' t) l m g np fm fh (k - t) v.length z v κ κ2 (fun h xs => pairsC p.1 h (fs xs))) : Bool) = false := by
    intro p hp
    have h := h p hp
    change (Bool.rec (motive := fun _ => Bool) (tsn (pos t) l (k + 1 - t) v (fun κ κ2 =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g np k) l m g np k t z v κ κ2) (Nat.beq p.2 1)) true
      (st (k - 1) fun k1 => node1 (look1 l m g np fm fh K K k1 t) (pos t) l m g np fm fh (k - t) (len v) z v κ κ2 (fun h xs => pairsC p.1 h (fs xs))))) true (Nat.ble (len v) 1) : Bool) = false at h
    rw [bR, pos_eq, len_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      refine ⟨?_, (hFy _).symm.trans h⟩
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
  refine one_sound X hR hR2 hfb (look1_sound X hR hR2 (K := K) hfb K) hs hcod (un p0 hp0).1 hk hl hmW hFb hKP (fu := k) ?_ ?_
  · have := (or_f (un p0 hp0).2).2
    rw [bR, hp1, cond_true] at this; exact this
  · intro x y hx hy hne hxr hyr
    obtain ⟨p, hpM, hpb⟩ := hM1 ((x + y) % MM) (Nat.mod_lt _ (by decide))
    rw [← hb_mod] at hpb
    have h3 := (or_f (un p hpM).2).1
    rw [st_eq] at h3
    refine ⟨_, h3, fun h xs hp a c ha hc har hcr ea ec => ?_⟩
    exact pairsC_any hp (fs_mem ha har) (fs_mem hc hcr) (fun e => hne (by rw [← ea, ← ec, e])) (by rw [ea, ec]; exact hpb)
end sound
theorem topC_ok : TopOk topC := by
  intro P l m g np T X R hR hR2 fm fh K k t z v S M Fs hM h hs hcod k' hk hl hmW hfb hFb
  exact topC_sound X hR hR2 hM h hs hcod hk hl hmW hfb hFb
lemma pick_sub {T : List (ℕ × ℕ)} {cs : List ℕ} : ∀ x ∈ pick T cs, x ∈ T := by
  intro x hx
  simp only [pick, List.mem_filterMap] at hx
  obtain ⟨c, _, h⟩ := hx
  exact List.mem_of_find?_eq_some h
section
variable {top : TopT} (htop : TopOk top)
include htop
lemma okR_imp {E : List (Bool × ℕ × ℕ)} {Q : List (ℕ × ℕ)} {x : ℕ × ℕ} (hE : E = [] ∨ ∃ e, E = [e] ∧ e.2.1 < 10 ∧ e.2.2 < 10 ∧ Imp [] x.1 x.2)
    (h : okR top E Q x = true) (hI : ∀ y ∈ Q, Imp E y.1 y.2) : Imp E x.1 x.2 := by
  simp only [okR, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, Bool.not_eq_true'] at h
  have hx15 := Nat.le_of_ble_eq_true h.1.2
  refine imp_FK htop (F := []) (fb := (1, 0)) (K := x.2 - 1) (by omega) (by omega) hE h.1.1 hI (Or.inl rfl) (by simp) (h.2.imp (fun ⟨y, hy, hy2⟩ => ⟨y, hy, Nat.le_of_ble_eq_true hy2⟩) fun h t ht =>
    ⟨[(FF, 1)], ffull, fun p hp => ?_⟩)
  simp only [List.mem_singleton] at hp; subst hp
  exact chkT_chk h t (List.mem_range.2 ht)
lemma okAll {T U : List (ℕ × ℕ)} (h : U.all (fun x => okR top [] (pr T x.1) x) = true) (hT : ∀ x ∈ T, Imp [] x.1 x.2) : ∀ x ∈ U, Imp [] x.1 x.2 := fun x hx =>
  okR_imp htop (Or.inl rfl) (List.all_eq_true.1 h x hx) (fun y hy => hT y (List.mem_of_mem_filter hy))
lemma ownAll {e : Bool × ℕ × ℕ} (he : e.2.1 < 10 ∧ e.2.2 < 10) {raw : List (ℕ × ℕ)} (hr : ∀ x ∈ raw, Imp [] x.1 x.2) {own cs : List ℕ}
    (ho : ∀ x ∈ raw, x.1 ∈ own → Imp [e] x.1 x.2)
    (h : (raw.filter (inC cs)).all (fun x => okR top [e] (pr (tabE e own raw) x.1) x) = true) : ∀ x ∈ raw, x.1 ∈ cs ++ own → Imp [e] x.1 x.2 := by
  intro x hx hc
  rcases List.mem_append.1 hc with hc | hc
  · have hx' : x ∈ raw.filter (inC cs) := by
      rw [List.mem_filter]
      exact ⟨hx, by simp only [inC, List.any_eq_true]; exact ⟨x.1, hc, Nat.beq_refl _⟩⟩
    exact okR_imp htop (Or.inr ⟨e, rfl, he.1, he.2, hr x hx⟩) (List.all_eq_true.1 h x hx') (fun y hy => tabE_ok hr ho y (List.mem_of_mem_filter hy))
  · exact ho x hx hc
lemma okAllP {T : List (ℕ × ℕ)} {rs : List ((ℕ × ℕ) × List ℕ)} (h : rs.all (okU top T) = true) (hT : ∀ x ∈ T, Imp [] x.1 x.2) : ∀ x ∈ rs.map Prod.fst, Imp [] x.1 x.2 := by
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
  exact okR_imp htop (Or.inl rfl) (List.all_eq_true.1 h r hr) (fun y hy => hT y (pick_sub y hy))
lemma ownAllP {e : Bool × ℕ × ℕ} (he : e.2.1 < 10 ∧ e.2.2 < 10) {raw : List (ℕ × ℕ)} (hr : ∀ x ∈ raw, Imp [] x.1 x.2) {own : List ℕ}
    (ho : ∀ x ∈ raw, x.1 ∈ own → Imp [e] x.1 x.2) {rs : List ((ℕ × ℕ) × List ℕ)} (h : rs.all (okO top e own raw) = true) :
    ∀ x ∈ raw, x.1 ∈ rs.map (fun r => r.1.1) ++ own → Imp [e] x.1 x.2 := by
  intro x hx hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨r, hr', e1⟩ := List.mem_map.1 hc
    have h := List.all_eq_true.1 h r hr'
    simp only [okO, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    have e2 : x.2 = r.1.2 := by
      rcases h.1 x hx with h | h
      · rw [e1, Nat.beq_refl] at h; simp at h
      · exact Nat.eq_of_beq_eq_true h
    have e3 : x = r.1 := Prod.ext e1.symm e2
    subst e3
    exact okR_imp htop (Or.inr ⟨e, rfl, he.1, he.2, hr _ hx⟩) h.2 (tabE_ok (fun y hy => hr y (pick_sub y hy)) (fun y hy => ho y (pick_sub y hy)))
  · exact ho x hx hc
lemma cov_t {E : List (Bool × ℕ × ℕ)} {Q : List (ℕ × ℕ)} {fb : ℕ × ℕ} {K : ℕ} {Ms : List (ℕ × List (ℕ × ℕ))} {tt : List (List ℕ)}
    (hMs : ∀ x ∈ Ms, mFull x.2 = true ∧ ∀ p ∈ x.2, chkG top E Q fb 0 K x.1 p.1 p.2 = false) (hts : ∀ ts ∈ tt, chkT top E Q fb 0 K ts FF 1 = false)
    (hcov : (List.range (K + 1)).all (fun t => tt.any (fun ts => ts.any (Nat.beq t)) || Ms.any (fun x => Nat.beq t x.1)) = true) :
    ∀ t < K + 1, ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chkG top E Q fb 0 K t p.1 p.2 = false := by
  clear htop
  intro t ht
  have h := List.all_eq_true.1 hcov t (List.mem_range.2 ht)
  simp only [Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨ts, hs, s, hs', h⟩ | ⟨x, hx, h⟩
  · obtain rfl := Nat.eq_of_beq_eq_true h
    exact ⟨[(FF, 1)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact chkT_chk (hts ts hs) t hs'⟩
  · obtain rfl := Nat.eq_of_beq_eq_true h
    exact ⟨x.2, hMs x hx⟩
lemma rootT {e : Bool × ℕ × ℕ} {F : List (Bool × ℕ × ℕ)} {Q : List (ℕ × ℕ)} {fb : ℕ × ℕ} {L K : ℕ} (hLK : L ≤ K + 1) (hK : K ≤ 15) (he : e.2.1 < 10 ∧ e.2.2 < 10) (h0 : Imp [] 0 L)
    (hI : ∀ y ∈ Q, Imp [e] y.1 y.2) (hp : pOk 0 Q = true) (hfb : fbOk [e] F fb = true) (hF : ∀ f ∈ F, Imp [f] 0 L)
    {Ms : List (ℕ × List (ℕ × ℕ))} {tt : List (List ℕ)} (hMs : ∀ x ∈ Ms, mFull x.2 = true ∧ ∀ p ∈ x.2, chkG top [e] Q fb 0 K x.1 p.1 p.2 = false)
    (hts : ∀ ts ∈ tt, chkT top [e] Q fb 0 K ts FF 1 = false)
    (hcov : (List.range (K + 1)).all (fun t => tt.any (fun ts => ts.any (Nat.beq t)) || Ms.any (fun x => Nat.beq t x.1)) = true) : Imp [e] 0 L := by
  rcases Nat.eq_zero_or_pos L with rfl | hpos
  · intro q hq; exact absurd hq (Nat.not_lt_zero _)
  · have hc := cov_t htop hMs hts hcov
    refine imp_FK htop hLK hK (Or.inr ⟨e, rfl, he.1, he.2, h0⟩) hp hI (Or.inr ⟨rfl, hfb⟩) (fun f hf => ?_) (Or.inr fun t ht => hc t (by omega))
    have e1 : L - 1 + [e].length = L := by simp only [List.length_cons, List.length_nil]; omega
    rw [e1]; exact hF f hf
lemma rootL {F : List (Bool × ℕ × ℕ)} {Q : List (ℕ × ℕ)} {fb : ℕ × ℕ} {L K : ℕ} (hLK : L ≤ K) (hK : K ≤ 15)
    (hI : ∀ y ∈ Q, Imp [] y.1 y.2) (hp : pOk 0 Q = true) (hfb : fbOk [] F fb = true) (hF : ∀ f ∈ F, Imp [f] 0 L)
    {Ms : List (ℕ × List (ℕ × ℕ))} {tt : List (List ℕ)} (hMs : ∀ x ∈ Ms, mFull x.2 = true ∧ ∀ p ∈ x.2, chkG top [] Q fb 0 K x.1 p.1 p.2 = false)
    (hts : ∀ ts ∈ tt, chkT top [] Q fb 0 K ts FF 1 = false)
    (hcov : (List.range (K + 1)).all (fun t => tt.any (fun ts => ts.any (Nat.beq t)) || Ms.any (fun x => Nat.beq t x.1)) = true) : Imp [] 0 (L + 1) := by
  have hc := cov_t htop hMs hts hcov
  exact imp_FK htop (by omega) hK (Or.inl rfl) hp hI (Or.inr ⟨rfl, hfb⟩) (fun f hf => hF f hf) (Or.inr fun t ht => hc t (by omega))
end
lemma apI {E : List (Bool × ℕ × ℕ)} {A B : List (ℕ × ℕ)} (ha : ∀ x ∈ A, Imp E x.1 x.2) (hb : ∀ x ∈ B, Imp E x.1 x.2) : ∀ x ∈ A ++ B, Imp E x.1 x.2 := fun x hx =>
  (List.mem_append.1 hx).elim (ha x) (hb x)
lemma own0 {e : Bool × ℕ × ℕ} {raw : List (ℕ × ℕ)} : ∀ x ∈ raw, x.1 ∈ ([] : List ℕ) → Imp [e] x.1 x.2 := fun _ _ h => by simp at h
lemma rootQ {e : Bool × ℕ × ℕ} {own : List ℕ} {raw : List (ℕ × ℕ)} {cs : List ℕ} (hr : ∀ x ∈ raw, Imp [] x.1 x.2) (ho : ∀ x ∈ raw, x.1 ∈ own → Imp [e] x.1 x.2) :
    ∀ y ∈ tabE e own (pick raw cs), Imp [e] y.1 y.2 := tabE_ok (fun y hy => hr y (pick_sub y hy)) (fun y hy => ho y (pick_sub y hy))
lemma pickI {E : List (Bool × ℕ × ℕ)} {T : List (ℕ × ℕ)} {cs : List ℕ} (h : ∀ x ∈ T, Imp E x.1 x.2) : ∀ x ∈ pick T cs, Imp E x.1 x.2 := fun x hx => h x (pick_sub x hx)
lemma ownOne {e : Bool × ℕ × ℕ} {raw : List (ℕ × ℕ)} {own : List ℕ} {c L : ℕ} (h : Imp [e] c L) (hu : raw.all (fun x => !Nat.beq x.1 c || Nat.beq x.2 L) = true)
    (ho : ∀ x ∈ raw, x.1 ∈ own → Imp [e] x.1 x.2) : ∀ x ∈ raw, x.1 ∈ c :: own → Imp [e] x.1 x.2 := by
  intro x hx hc
  rcases List.mem_cons.1 hc with hc | hc
  · have hu := List.all_eq_true.1 hu x hx
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at hu
    rcases hu with hu | hu
    · rw [hc, Nat.beq_refl] at hu; simp at hu
    · rw [hc, Nat.eq_of_beq_eq_true hu]; exact h
  · exact ho x hx hc
lemma subI {E : List (Bool × ℕ × ℕ)} {A : List (ℕ × ℕ)} {p : ℕ × ℕ → Bool} (ha : ∀ x ∈ A, Imp E x.1 x.2) : ∀ x ∈ A.filter p, Imp E x.1 x.2 := fun x hx =>
  ha x (List.mem_of_mem_filter hx)
theorem prep {E : List (Bool × ℕ × ℕ)} {Q : List (ℕ × ℕ)} {Z L K : ℕ} (hLK : L ≤ K + 1) (hK : K ≤ 15) (hE : E = [] ∨ ∃ e, E = [e] ∧ e.2.1 < 10 ∧ e.2.2 < 10 ∧ Imp [] Z L)
    (hp : pOk Z Q = true) (hI : ∀ e ∈ Q, Imp E e.1 e.2) {k t : ℕ} {S : Finset ℕ} (hl : Live Z0 (mz Z) (tz Z) k t S) (hS : (S : Set ℕ) ⊆ C (mz Z) (WZ E Z))
    (hmn : ∀ q < k, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z))) (hkL : k < L) :
    t < L ∧ (S : Set ℕ) ⊆ WZ E Z ∧ ∃ (g np z : ℕ) (P : List ℕ) (v : List W), Ctx P (lz Z) (mz Z) g np (tz Z) ∧ StOk P (tz Z) (lz Z) K z v S ∧ (∀ w ∈ v, w.r = RZ E Z w.s) ∧
      ∀ fm fh H ph, chkG topC E Q (fm, fh) Z K t H ph = false → topC (lz Z) (mz Z) g np fm fh K H ph K t z v = false := by
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => hmn q' hq' (hs.mono le_rfl hCS)⟩
  have htk := hm.size.2
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have hpw : pwr E Z = 0 ∨ pwr E Z ∈ S := by
    rcases hE with rfl | ⟨e, rfl, _, _, hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k hkL (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      simp only [rawL, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w, by simp only [rawL, List.map_nil, List.append_nil]; exact hw, rfl⟩
      · have hx : tw e &&& mz Z ∈ S := by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨a1, a2⟩ := avl_spec (mz Z) (rawL E)
  set v := ((avl (mz Z) (rawL E)).filter (fun s => decide (s ∈ S))).map (mkW (PZ Q)) with hv
  have hsub : v.Sublist ((avl (mz Z) (rawL E)).map (mkW (PZ Q))) := List.filter_sublist.map _
  have hvs : v.map W.s = (avl (mz Z) (rawL E)).filter (fun s => decide (s ∈ S)) := by
    rw [hv, List.map_map]; exact List.map_id _
  have hnd : (v.map W.s).Nodup := by
    rw [hvs]
    exact (a1.sublist List.filter_sublist).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, hvs, List.mem_filter, a2]
    constructor
    · rintro ⟨_, hx⟩; simpa using hx
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      exact ⟨⟨fun e => h0 (e ▸ hx), fun e => h1 (e ▸ hx), w, hw, rfl⟩, by simpa using hx⟩
  have hvm : ∀ w ∈ v, ∃ x ∈ rawL E, w = mkW (PZ Q) (x &&& mz Z) := by
    intro w hw
    rw [hv, List.mem_map] at hw
    obtain ⟨s, hs, rfl⟩ := hw
    obtain ⟨_, _, x, hx, rfl⟩ := (a2 s).1 (List.mem_of_mem_filter hs)
    exact ⟨x, hx, rfl⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := hvm w hw; exact mkW_ok _ _
  have hcod : ∀ w ∈ v, w.r = RZ E Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hvm w hw
    have : x &&& mz Z ∈ WZ E Z := ⟨x, hx, rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ, if_pos this]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hvm w hw; exact wire_good hx Z
  have hd0 : ∀ w ∈ v, w.d = 0 := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := hvm w hw; rfl
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, K)).1 ∧ Q.getD j (0, K) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (npOf (PZ Q)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_, ⟨fun j => (PZ Q).getD j 0, fun j _ => PZ_lt Q j, npOf_eq _, fun j _ _ => Nat.and_self _⟩⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hA : ∀ j < (PZ Q).length, Acc ((PZ Q).getD j 0) (tz Z) K (K - (Q.getD j (0, K)).2) (fun _ => 0) S := by
    intro j hj
    obtain ⟨e1, e2⟩ := hPget j hj
    rw [e1]
    exact Acc.start (L := (Q.getD j (0, K)).2) (hno _ e2) subset_rfl (by omega)
  have hle := cnt_le X (D := fun _ _ => 0) hrep hwok hA hm (by omega)
  have hz : pL (Q.map fun e => 16 + (K - e.2)) - sumc v = pk (PZ Q).length (fun j => 16 + (K - (Q.getD j (0, K)).2) - cnt v j) := by
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hst : StOk (PZ Q) (tz Z) (lz Z) K (pL (Q.map fun e => 16 + (K - e.2)) - sumc v) v S := by
    rw [hz]
    exact StOk.start hrep hwok hgood (by omega) (fun j _ => by omega) hd0 hA
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, show pos t = pos' t by cases t <;> simp [pos, pos'], hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble (lnW v) (Nat.sub (Nat.succ K) t) = true := Nat.ble_eq_true_of_le (by
    rw [lnW_eq]; change v.length ≤ K + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  refine ⟨by omega, hSW, _, _, _, PZ Q, v, X, hst, hcod, fun fm fh H ph h2 => ?_⟩
  simp only [chkG, st_eq, pre_eq] at h2
  have h3 := anySub_false (by simp) h2 v hsub hcov
  simp only [startG, bR, hhas, hble, Bool.cond_true] at h3
  exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (npOf (PZ Q)) fm fh K H ph K t z r) (fun h => rfl) rfl hst hm (by omega) h3
section sound
variable {P : List ℕ} {l m g np T : ℕ} (X : Ctx P l m g np T) {R : ℕ → ℕ}
include X
lemma one_first (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {fm fh : ℕ} {Fs : Set ℕ} {f : ℕ → ℕ → ℕ → List W → Bool}
    (hfb : ∀ d x y, x ≠ y → R x ≠ 0 → R y ≠ 0 → fbit fm fh (op d x y) = true → op d x y ∈ Fs)
    (hF : P1 R P l m T Fs f) {k t z : ℕ} {v : List W} {S S1 : Finset ℕ} {κ : ℕ → Bool} {κ2 : ℕ → ℕ → Bool} (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
    {k0 : ℕ} (hk : k0 + 1 ≤ k) (hmW : MW R m T (k0 + 1) S) (hFb : MF R m T (k0 + 1) Fs S) (hKP : KP Z0 m T (k0 + 1) t S v κ κ2)
    {d : Bool} {a b : ℕ} (ha : R a ≠ 0) (hb' : R b ≠ 0) (hb : Bi Z0 d a b S S1) (hl1 : Live Z0 m T k0 t S1)
    {go : (L_meta_17357.X → L_meta_17357.X → Bool) → List L_meta_17357.X → Bool}
    (hg1 : node1 (f (k - 1) t) (pos' t) l m g np fm fh (k - t) v.length z v κ κ2 go = false)
    (hg2 : ∀ h xs, go h xs = false → ∀ a' c : L_meta_17357.X, a' ∈ xs → c ∈ xs → a'.w.r ≠ 0 → c.w.r ≠ 0 → a'.s = a → c.s = b → h a' c = false ∨ h c a' = false) : False := by
  have hrep := hs.rep
  obtain ⟨wa, hwa, rfl⟩ := hrep.mem.1 hb.sub.1
  obtain ⟨wb, hwb, rfl⟩ := hrep.mem.1 hb.sub.2.1
  have hnf : fbit fm fh (op d wa.s wb.s) = false := by
    by_contra hc
    exact hFb.gate hb hl1 (hfb d wa.s wb.s hb.1 ha hb' (by simpa using hc))
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hm : Min Z0 m T (k0 + 1) t S := hmW.min (hb.live hl1)
  have hsz := (hb.min hl1 hm.2).size
  obtain ⟨z', r, hf, hst, hmem⟩ : ∃ z' r, f k t z' r = false ∧ StOk P T l k z' r S1 ∧ ∀ w ∈ r, (w.s = op d wa.s wb.s ∧ w.r = 0) ∨ ∃ w' ∈ v, w'.s = w.s ∧ w'.r = w.r := by
    refine nodeH_bi X hs hm (by omega) rfl rfl (by omega) hb hl1 hKP ?_ ?_ hg1
    · intro a' c' oa oc ka kc kb x1 y1 e hh
      rw [e] at hh ⊢
      exact mid1_false hnf hh
    · intro h xs hgo hxs a' c' ha' hc' hav hcv ea ec eax ecy
      refine hg2 h xs hgo a' c' ha' hc' ?_ ?_ eax ecy
      · have : a'.w = wa := hrep.inj hav hwa (by rw [← ea, eax])
        rw [this, hcod wa hwa]; exact ha
      · have : c'.w = wb := hrep.inj hcv hwb (by rw [← ec, ecy])
        rw [this, hcod wb hwb]; exact hb'
  have hfr : R (op d wa.s wb.s) = 0 := by
    by_contra hne
    refine hmW k0 (by omega) (hl1.sol.mono le_rfl fun x hx => ?_)
    have hx' := hb.sub.2.2 hx
    simp only [Finset.mem_insert] at hx'
    rcases hx' with rfl | hx'
    · exact Or.inl (Or.inl hne)
    · exact Or.inl (Or.inr hx')
  refine hF _ _ _ _ _ hf hst ?_ k0 (by omega) hl1 (hmW.bi hb) (hFb.bi hb)
  intro w hw
  rcases hmem w hw with ⟨e1, e2⟩ | ⟨w', hw', e1, e2⟩
  · rw [e1, e2, hfr]
  · rw [← e1, ← e2]; exact hcod w' hw'
lemma topC_un {fm fh K H ph k t z : ℕ} {v : List W} {S : Finset ℕ} (h : topC l m g np fm fh K H ph k t z v = false) (hs : StOk P T l k z v S)
    {k' : ℕ} (hk : k' ≤ k) (hmin : Min Z0 m T k' t S) : ∃ (κ : ℕ → Bool) (κ2 : ℕ → ℕ → Bool), KP Z0 m T k' t S v κ κ2 ∧ 2 ≤ v.length ∧
      (Nat.beq ph 1 = true → mv (look l m g np k) l m g np k t z v κ κ2 = false) ∧
      node1 (look1 l m g np fm fh K K (k - 1) t) (pos' t) l m g np fm fh (k - t) v.length z v κ κ2 (fun h xs => pairsC H h (fs xs)) = false := by
  obtain ⟨κ, κ2, hFy, hKP⟩ := tsn_sound X hs hmin hk
  change (Bool.rec (motive := fun _ => Bool) (tsn (pos t) l (k + 1 - t) v (fun κ κ2 =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g np k) l m g np k t z v κ κ2) (Nat.beq ph 1)) true
    (st (k - 1) fun k1 => node1 (look1 l m g np fm fh K K k1 t) (pos t) l m g np fm fh (k - t) (len v) z v κ κ2 (fun h xs => pairsC H h (fs xs))))) true (Nat.ble (len v) 1) : Bool) = false at h
  rw [bR, pos_eq, len_eq] at h
  cases h0 : Nat.ble v.length 1 with
  | true => rw [h0] at h; simp at h
  | false =>
    rw [h0, cond_false] at h
    have h1 := (hFy _).symm.trans h
    beta_reduce at h1
    obtain ⟨h2, h3⟩ := or_f h1
    rw [st_eq] at h2
    refine ⟨κ, κ2, hKP, ?_, fun hp => ?_, h2⟩
    · by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
    · rw [bR, hp, cond_true] at h3; exact h3
theorem topC_first (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {fm fh K H ph k t z : ℕ} {v : List W} {S S1 : Finset ℕ} {Fs : Set ℕ}
    (h : topC l m g np fm fh K H ph k t z v = false) (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s) {k0 : ℕ} (hk : k0 + 1 ≤ k) (hmW : MW R m T (k0 + 1) S)
    (hfb : ∀ d x y, x ≠ y → R x ≠ 0 → R y ≠ 0 → fbit fm fh (op d x y) = true → op d x y ∈ Fs) (hFb : MF R m T (k0 + 1) Fs S)
    {d : Bool} {a b : ℕ} (ha : R a ≠ 0) (hb' : R b ≠ 0) (hH : hb H (a + b) = true) (hbi : Bi Z0 d a b S S1) (hl1 : Live Z0 m T k0 t S1) : False := by
  have hmin : Min Z0 m T (k0 + 1) t S := hmW.min (hbi.live hl1)
  obtain ⟨κ, κ2, hKP, _, _, h2⟩ := topC_un X h hs hk hmin
  refine one_first X hR2 hfb (look1_sound X hR hR2 (K := K) hfb K) hs hcod hk hmW hFb hKP ha hb' hbi hl1 h2 fun h xs hp a' c ha' hc har hcr ea ec => ?_
  exact pairsC_any hp (fs_mem ha' har) (fs_mem hc hcr) (fun e => hbi.1 (by rw [← ea, ← ec, e])) (by rw [ea, ec]; exact hH)
theorem topC_two (hR : RR R) {fm fh K H ph k t z : ℕ} {v : List W} {S : Finset ℕ} (h : topC l m g np fm fh K H ph k t z v = false) (hp : Nat.beq ph 1 = true)
    (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s) {k' : ℕ} (hk : k' ≤ k) (hmW : MW R m T k' S) (hl : Live Z0 m T k' t S) (hlR : Live R m T k' t S) : False := by
  have hmin : Min Z0 m T k' t S := hmW.min hl
  obtain ⟨κ, κ2, hKP, hlen, h3, _⟩ := topC_un X h hs hk hmin
  exact mv_sound X hR (look_sound X hR k) hs (fun w hw => Or.inr (hcod w hw)) hlen (h3 hp) k' hk ⟨hlR, hmin.2⟩ hKP.toR
end sound
lemma fbOkH_spec {Z : ℕ} {E F : List (Bool × ℕ × ℕ)} {pv : List ℕ} {fb : ℕ × ℕ} (h : fbOkH Z E F pv fb = true) {x y : ℕ} (hx : x ∈ WZ E Z) (hy : y ∈ WZ E Z) (hxy : x ≠ y) {d : Bool}
    (hbt : fbit fb.1 fb.2 (op d x y) = true) : op d x y ∈ FsH Z E F pv := by
  obtain ⟨wx, hwx, rfl⟩ := hx
  obtain ⟨wy, hwy, rfl⟩ := hy
  have hx0 : wx &&& mz Z ∈ WZ E Z := ⟨wx, hwx, rfl⟩
  have hy0 : wy &&& mz Z ∈ WZ E Z := ⟨wy, hwy, rfl⟩
  simp only [fbOkH, List.all_eq_true, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_true, exists_exists_and_eq_and] at h
  have h := h wx hwx wy hwy
  simp only [nl, no] at h
  rcases h with (h | ⟨H, hH, h⟩) | h
  · exact absurd (Nat.eq_of_beq_eq_true h) hxy
  · exact Or.inr ⟨d, _, _, H, hx0, hy0, hxy, hH, h, rfl⟩
  · cases d with
    | false =>
      rcases h.1 with h | ⟨f, hf, h⟩
      · change fbit fb.1 fb.2 (wx &&& mz Z &&& (wy &&& mz Z)) = true at hbt
        rw [h] at hbt; simp at hbt
      · exact Or.inl ⟨f, hf, Nat.eq_of_beq_eq_true h⟩
    | true =>
      rcases h.2 with h | ⟨f, hf, h⟩
      · change fbit fb.1 fb.2 (wx &&& mz Z ||| (wy &&& mz Z)) = true at hbt
        rw [h] at hbt; simp at hbt
      · exact Or.inl ⟨f, hf, Nat.eq_of_beq_eq_true h⟩
lemma hbFF (x : ℕ) : hb FF x = true := by
  have h := ffull
  simp only [mFull, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_cons, List.any_nil, Bool.or_false] at h
  rw [hb_mod]; exact h.1 _ (Nat.mod_lt _ (by decide))
theorem imp_seq {fb0 : ℕ × ℕ} {E F : List (Bool × ℕ × ℕ)} {Q : List (ℕ × ℕ)} {Z L K : ℕ} (hLK : L ≤ K + 1) (hK : K ≤ 15) (hE : E = [] ∨ ∃ e, E = [e] ∧ e.2.1 < 10 ∧ e.2.2 < 10 ∧ Imp [] Z L)
    (hp : pOk Z Q = true) (hI : ∀ e ∈ Q, Imp E e.1 e.2) (hF : ∀ e ∈ F, Imp [e] Z (L - 1 + E.length)) {M : List (ℕ × ℕ × ℕ × ℕ)} (hM : seqOk Z E F [] M = true)
    (hfull : ((List.range MM).all (fun r => M.any (fun p => hb p.1 r)) && M.any (fun p => Nat.beq p.2.1 1)) = true)
    (hfb0 : fbOkH Z E F [] fb0 = true) (hrun : ∀ t < L, chkG topC E Q fb0 Z K t FF 1 = false ∨ ∀ p ∈ M, chkG topC E Q p.2.2 Z K t p.1 p.2.1 = false) : Imp E Z L := by
  intro q hq hsol
  classical
  have hE1 : E.length ≤ 1 := by rcases hE with rfl | ⟨e, rfl, _⟩ <;> simp
  have hex : ∃ q, Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)) := ⟨q, hsol⟩
  obtain ⟨n0, hn0⟩ : ∃ n, n = Nat.find hex := ⟨_, rfl⟩
  have hqL : n0 < L := by rw [hn0]; exact lt_of_le_of_lt (Nat.find_min' hex hsol) hq
  have hmn : ∀ q < n0, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)) := fun q hq hs => Nat.find_min hex (by omega) hs
  have hge : ∀ q, Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)) → n0 ≤ q := fun q hs => by rw [hn0]; exact Nat.find_min' hex hs
  have hWS : ∀ {S : Finset ℕ}, (S : Set ℕ) ⊆ WZ E Z → {x | RZ E Z x ≠ 0} ∪ (S : Set ℕ) = WZ E Z := fun h => by rw [RZ_set]; exact Set.union_eq_self_of_subset_right h
  have hRZ : ∀ {x : ℕ}, x ∈ WZ E Z → RZ E Z x ≠ 0 := fun {x} h => by
    have : x ∈ {x | RZ E Z x ≠ 0} := by rw [RZ_set]; exact h
    exact this
  have claim : ∀ (N : List (ℕ × ℕ × ℕ × ℕ)) (pv : List ℕ), (∀ p ∈ N, p ∈ M) → seqOk Z E F pv N = true →
      (∀ s ∈ FsH Z E F pv, ∀ q < n0, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (insert s (WZ E Z)))) →
      (∀ p ∈ N, ∀ (d : Bool) (x y : ℕ), x ∈ WZ E Z → y ∈ WZ E Z → x ≠ y → hb p.1 (x + y) = true → ∀ q < n0, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (insert (op d x y) (WZ E Z)))) := by
    intro N
    induction N with
    | nil => intro pv _ _ _ p hp; simp at hp
    | cons p0 N ih =>
      intro pv hN hsq hpv
      rw [seqOk, Bool.and_eq_true] at hsq
      have st0 : ∀ (d : Bool) (x y : ℕ), x ∈ WZ E Z → y ∈ WZ E Z → x ≠ y → hb p0.1 (x + y) = true → ∀ q < n0, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (insert (op d x y) (WZ E Z))) := by
        intro d x y hx hy hxy hH q hq hs
        obtain ⟨k1, hk1, t, S0, hS0, hl⟩ := hs.live
        by_cases hmem : op d x y ∈ S0
        · have hbi : Bi Z0 d x y (insert x (insert y (S0.erase (op d x y)))) S0 := ⟨hxy, S0.erase (op d x y), rfl, (Finset.insert_erase hmem).symm, al0 _ _ _⟩
          have hS : ((insert x (insert y (S0.erase (op d x y))) : Finset ℕ) : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
            intro u hu
            simp only [Finset.coe_insert, Finset.coe_erase, Set.mem_insert_iff, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at hu
            rcases hu with rfl | rfl | ⟨hu, hne⟩
            · exact Or.inl hx
            · exact Or.inl hy
            · rcases hS0 hu with (h | h) | h
              · exact absurd h hne
              · exact Or.inl h
              · exact Or.inr h
          have hlS := hbi.live hl
          have hk : k1 + 1 = n0 := by
            have := hge _ (hlS.sol.mono le_rfl hS); omega
          subst hk
          obtain ⟨htL, hSW, g, np, z, P, v, X, hst, hcod, hrn⟩ := prep hLK hK hE hp hI hlS hS hmn hqL
          have hmW : MW (RZ E Z) (mz Z) (tz Z) (k1 + 1) (insert x (insert y (S0.erase (op d x y)))) := fun q hq hs => by
            rw [hWS hSW] at hs
            exact hmn q hq hs
          rcases hrun t htL with h2 | h2
          · refine topC_first X (R := RZ E Z) (RZ_RR E Z) (RZ_R2 E Z) (Fs := FsH Z E F []) (hrn fb0.1 fb0.2 FF 1 h2) hst hcod (by omega) hmW ?_ ?_ (hRZ hx) (hRZ hy) (hbFF _) hbi hl
            · intro d x y hxy hx hy hbit
              exact fbOkH_spec hfb0 (RZ_mem hx) (RZ_mem hy) hxy hbit
            · rintro s hs q hq hs'
              rw [hWS hSW] at hs'
              rcases hs with ⟨f, hf, rfl⟩ | ⟨_, _, _, H, _, _, _, hH, _⟩
              · exact hpv _ (Or.inl ⟨f, hf, rfl⟩) q hq hs'
              · simp at hH
          · have h2 := hrn p0.2.2.1 p0.2.2.2 p0.1 p0.2.1 (h2 p0 (hN p0 List.mem_cons_self))
            refine topC_first X (R := RZ E Z) (RZ_RR E Z) (RZ_R2 E Z) (Fs := FsH Z E F pv) h2 hst hcod (by omega) hmW ?_ ?_ (hRZ hx) (hRZ hy) hH hbi hl
            · intro d x y hxy hx hy hbit
              exact fbOkH_spec hsq.1 (RZ_mem hx) (RZ_mem hy) hxy hbit
            · intro s hs q hq hs'
              rw [hWS hSW] at hs'
              exact hpv s hs q hq hs'
        · refine hmn k1 (by omega) (hl.sol.mono le_rfl fun u hu => ?_)
          rcases hS0 hu with (h | h) | h
          · exact absurd (h ▸ hu) hmem
          · exact Or.inl h
          · exact Or.inr h
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact st0
      · refine ih (p0.1 :: pv) (fun p hp => hN p (List.mem_cons_of_mem _ hp)) hsq.2 ?_ p hp
        rintro s (⟨f, hf, rfl⟩ | ⟨d, x, y, H, hx, hy, hxy, hH, hh, rfl⟩)
        · exact hpv _ (Or.inl ⟨f, hf, rfl⟩)
        · rcases List.mem_cons.1 hH with rfl | hH
          · exact st0 d x y hx hy hxy hh
          · exact hpv _ (Or.inr ⟨d, x, y, H, hx, hy, hxy, hH, hh, rfl⟩)
  have hF0 : ∀ s ∈ FsH Z E F [], ∀ q < n0, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (insert s (WZ E Z))) := by
    rintro s (⟨f, hf, rfl⟩ | ⟨d, x, y, H, _, _, _, hH, _⟩) q hq hs
    · exact forb_ok hE1 (hF f hf) q (by omega) hs
    · simp at hH
  have hall := claim M [] (fun p hp => hp) hM hF0
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_eq_true] at hfull
  obtain ⟨hf1, p1, hp1, hp2⟩ := hfull
  obtain ⟨k, hk, t, S, hS, hl⟩ := (Nat.find_spec hex).live
  have hkeq : k = n0 := le_antisymm (by omega) (hge _ (hl.sol.mono le_rfl hS))
  subst hkeq
  obtain ⟨htL, hSW, g, np, z, P, v, X, hst, hcod, hrn⟩ := prep hLK hK hE hp hI hl hS hmn hqL
  have hmW : MW (RZ E Z) (mz Z) (tz Z) k S := fun q hq hs => by
    rw [hWS hSW] at hs
    exact hmn q hq hs
  rcases front (RZ_R2 E Z) hl hmW with hlR | ⟨k0, d, a, b, S1, rfl, ha, hb', hbi, hl1⟩
  · rcases hrun t htL with h2 | h2
    · exact topC_two X (RZ_RR E Z) (hrn fb0.1 fb0.2 FF 1 h2) rfl hst hcod (by omega) hmW hl hlR
    · exact topC_two X (RZ_RR E Z) (hrn _ _ _ _ (h2 p1 hp1)) hp2 hst hcod (by omega) hmW hl hlR
  · obtain ⟨p, hpM, hpb⟩ := hf1 ((a + b) % MM) (Nat.mod_lt _ (by decide))
    rw [← hb_mod] at hpb
    refine hall p hpM d a b (RZ_mem ha) (RZ_mem hb') hbi.1 hpb k0 (by omega) (hl1.sol.mono le_rfl fun x hx => ?_)
    have hx' := hbi.sub.2.2 hx
    simp only [Finset.mem_insert] at hx'
    rcases hx' with rfl | hx'
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr (hSW hx'))
lemma sq_run {E : List (Bool × ℕ × ℕ)} {Q : List (ℕ × ℕ)} {Z K L : ℕ} {fb0 : ℕ × ℕ} {M : List Sq} {tt : List (List ℕ)} {R : List (ℕ × List ℕ)}
    (hc : covSq M L tt R = true) (h1 : tt.all (okSw E Q Z K fb0) = true) (h2 : R.all (okSq E Q Z K M) = true) :
    ∀ t < L, chkG topC E Q fb0 Z K t FF 1 = false ∨ ∀ p ∈ M, chkG topC E Q p.2.2 Z K t p.1 p.2.1 = false := by
  intro t ht
  simp only [covSq, List.all_eq_true, List.mem_range, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at hc
  rcases hc t ht with ⟨ts, hts, u, hu, e⟩ | h
  · left
    obtain rfl := Nat.eq_of_beq_eq_true e
    have h3 := List.all_eq_true.1 h1 ts hts
    simp only [okSw, Bool.not_eq_true'] at h3
    exact chkT_chk h3 t hu
  · right
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hp
    obtain ⟨r, hr, e1, u, hu, e2⟩ := h j hj
    obtain rfl := Nat.eq_of_beq_eq_true e2
    have e1 := Nat.eq_of_beq_eq_true e1
    have h3 := List.all_eq_true.1 h2 r hr
    have e3 : M.getD r.1 (0, 0, 1, 0) = M[j] := by
      rw [e1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    simp only [okSq, st_eq, Bool.not_eq_true', e3] at h3
    exact chkT_chk h3 t hu
lemma imp_seqR {T : List (ℕ × ℕ)} {Z L : ℕ} (M : List Sq) (tt : List (List ℕ)) (R : List (ℕ × List ℕ)) (hT : ∀ e ∈ T, Imp [] e.1 e.2)
    (hp : (pOk Z (pr T Z) && (Nat.ble 1 L && (Nat.ble L 16 && sqOk Z [] [] (1, 0) M L tt R))) = true)
    (h1 : tt.all (okSw [] (pr T Z) Z (L - 1) (1, 0)) = true) (h2 : R.all (okSq [] (pr T Z) Z (L - 1) M) = true) : Imp [] Z L := by
  simp only [sqOk, Bool.and_eq_true] at hp
  obtain ⟨a1, a2, a3, b1, b2, b3, b4⟩ := hp
  have hL := Nat.le_of_ble_eq_true a2
  have hL2 := Nat.le_of_ble_eq_true a3
  refine imp_seq (fb0 := (1, 0)) (F := []) (K := L - 1) (by omega) (by omega) (Or.inl rfl) a1 (fun e he => hT e (List.mem_of_mem_filter he)) (by simp) b2 ?_ b1 (sq_run b4 h1 h2)
  rw [Bool.and_eq_true]; exact b3
lemma ty_impS {gs : List (Bool × ℕ × ℕ)} {raw : List (ℕ × ℕ)} {K i : ℕ} {e : Bool × ℕ × ℕ} {own cs : List ℕ} {fb : ℕ × ℕ} {tt : List (List ℕ)} {M : List Sq} {R : List (ℕ × List ℕ)}
    (hr : ∀ x ∈ raw, Imp [] x.1 x.2) (ho : ∀ x ∈ raw, x.1 ∈ own → Imp [e] x.1 x.2) (h1 : okTyS gs raw K i e own cs fb tt M R = true)
    (h2 : tt.all (okSw [e] (tabE e own (pick raw cs)) 0 K fb) = true) (h3 : R.all (okSq [e] (tabE e own (pick raw cs)) 0 K M) = true)
    {L : ℕ} (hL : L ≤ K + 1) (h0 : Imp [] 0 L) (hF : ∀ f ∈ gs.take i, Imp [f] 0 L) : Imp [e] 0 L := by
  rcases Nat.eq_zero_or_pos L with rfl | hpos
  · intro q hq; exact absurd hq (Nat.not_lt_zero _)
  simp only [okTyS, sqOk, Bool.and_eq_true] at h1
  obtain ⟨a1, a2, a3, a4, b1, b2, b3, b4⟩ := h1
  refine imp_seq (fb0 := fb) (F := gs.take i) hL (Nat.le_of_ble_eq_true a3) (Or.inr ⟨e, rfl, Nat.le_of_ble_eq_true a1, Nat.le_of_ble_eq_true a2, h0⟩) a4 (rootQ hr ho)
    (fun f hf => ?_) b2 ?_ b1 (fun t ht => sq_run b4 h2 h3 t (by omega))
  · have e1 : L - 1 + [e].length = L := by simp only [List.length_cons, List.length_nil]; omega
    rw [e1]; exact hF f hf
  · rw [Bool.and_eq_true]; exact b3
lemma imp_run {T : List (ℕ × ℕ)} {Z L : ℕ} (tt : List (List ℕ)) (hT : ∀ e ∈ T, Imp [] e.1 e.2)
    (hp : (pOk Z (pr T Z) && Nat.ble L 16 && (List.range L).all (fun t => tt.any (fun ts => ts.any (Nat.beq t)))) = true)
    (h : ∀ ts ∈ tt, chkT topC [] (pr T Z) (1, 0) Z (L - 1) ts FF 1 = false) : Imp [] Z L := by
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_eq_true] at hp
  have h16 := Nat.le_of_ble_eq_true hp.1.2
  refine imp_FK topC_ok (F := []) (fb := (1, 0)) (K := L - 1) (by omega) (by omega) (Or.inl rfl) hp.1.1 (fun e he => hT e (List.mem_of_mem_filter he)) (Or.inl rfl) (by simp) (Or.inr fun t ht => ?_)
  obtain ⟨ts, hts, s, hs, e⟩ := hp.2 t ht
  obtain rfl := Nat.eq_of_beq_eq_true e
  exact ⟨[(FF, 1)], ffull, fun p hq => by simp only [List.mem_singleton] at hq; subst hq; exact chkT_chk (h ts hts) t hs⟩
lemma ctn {T : List (ℕ × ℕ)} {Z K : ℕ} : ∀ ts ∈ ([] : List (List ℕ)), chkT topC [] (pr T Z) (1, 0) Z K ts FF 1 = false := by simp
lemma ctc {T : List (ℕ × ℕ)} {Z K : ℕ} {a : List ℕ} {tt : List (List ℕ)} (h : chkT topC [] (pr T Z) (1, 0) Z K a FF 1 = false)
    (hh : ∀ ts ∈ tt, chkT topC [] (pr T Z) (1, 0) Z K ts FF 1 = false) : ∀ ts ∈ a :: tt, chkT topC [] (pr T Z) (1, 0) Z K ts FF 1 = false := by
  intro ts hts
  rcases List.mem_cons.1 hts with rfl | hts
  · exact h
  · exact hh ts hts
lemma ty_imp {gs : List Gt} {raw : List (ℕ × ℕ)} {K i : ℕ} {e : Gt} {own cs : List ℕ} {fb : ℕ × ℕ} {tt : List (List ℕ)}
    (hr : ∀ x ∈ raw, Imp [] x.1 x.2) (ho : ∀ x ∈ raw, x.1 ∈ own → Imp [e] x.1 x.2) (h1 : okTy gs raw K i e own cs fb tt = true)
    (h2 : tt.all (okTs raw K e own cs fb) = true) {L : ℕ} (hL : L ≤ K + 1) (h0 : Imp [] 0 L) (hF : ∀ f ∈ gs.take i, Imp [f] 0 L) : Imp [e] 0 L := by
  simp only [okTy, Bool.and_eq_true] at h1
  obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h1
  refine rootT topC_ok (Ms := []) (tt := tt) (K := K) hL (Nat.le_of_ble_eq_true a3) ⟨Nat.le_of_ble_eq_true a1, Nat.le_of_ble_eq_true a2⟩ h0 (rootQ hr ho) a4 a5 hF (by simp) (fun ts hts => ?_) ?_
  · have := List.all_eq_true.1 h2 ts hts
    simpa only [okTs, Bool.not_eq_true'] using this
  · rw [List.all_eq_true] at a6 ⊢
    intro t ht
    simp only [a6 t ht, Bool.true_or]
lemma chainT {gs : List Gt} {L : ℕ} (H : ∀ i (hi : i < gs.length), (∀ f ∈ gs.take i, Imp [f] 0 L) → Imp [gs[i]] 0 L) : ∀ f ∈ gs, Imp [f] 0 L := by
  have P : ∀ n, ∀ i (hi : i < gs.length), i < n → Imp [gs[i]] 0 L := by
    intro n
    induction n with
    | zero => intro i _ h; omega
    | succ n ih =>
      intro i hi _
      refine H i hi fun f hf => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.1 hf
      exact ih j (by omega) (by omega)
  intro f hf
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hf
  exact P (i + 1) i hi (by omega)
theorem iroot_min {N : ℕ} (H : ∀ L ≤ N, Imp [] 0 L → Imp [] 0 (L + 1)) : Imp [] 0 (N + 1) := by
  intro q hq hs
  classical
  have hex : ∃ q, Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [] 0)) := ⟨q, hs⟩
  have h1 : Nat.find hex ≤ q := Nat.find_min' hex hs
  exact H (Nat.find hex) (by omega) (fun q' hq' hs' => Nat.find_min hex hq' hs') _ (Nat.lt_succ_self _) (Nat.find_spec hex)
lemma last_imp {gs : List Gt} {raw : List (ℕ × ℕ)} {K : ℕ} {cs : List ℕ} {fb : ℕ × ℕ} {tt : List (List ℕ)} (hr : ∀ x ∈ raw, Imp [] x.1 x.2)
    (h1 : (Nat.ble K 15 && pOk 0 (pick raw cs) && fbOk [] gs fb && (List.range (K + 1)).all (fun t => tt.any (fun ts => ts.any (Nat.beq t)))) = true)
    (h2 : tt.all (okLs (pick raw cs) K fb) = true) {L : ℕ} (hL : L ≤ K) (hF : ∀ f ∈ gs, Imp [f] 0 L) : Imp [] 0 (L + 1) := by
  simp only [Bool.and_eq_true] at h1
  obtain ⟨⟨⟨a3, a4⟩, a5⟩, a6⟩ := h1
  refine rootL topC_ok (Ms := []) (tt := tt) hL (Nat.le_of_ble_eq_true a3) (pickI hr) a4 a5 hF (by simp) (fun ts hts => ?_) ?_
  · have := List.all_eq_true.1 h2 ts hts
    simpa only [okLs, Bool.not_eq_true'] using this
  · rw [List.all_eq_true] at a6 ⊢
    intro t ht
    simp only [a6 t ht, Bool.true_or]
lemma all_app {α : Type} {p : α → Bool} {A B : List α} (ha : A.all p = true) (hb : B.all p = true) : (A ++ B).all p = true := by
  rw [List.all_append, ha, hb]; rfl
lemma one1 {Z L : ℕ} (h : Imp [] Z L) : ∀ e ∈ [(Z, L)], Imp [] e.1 e.2 := fun e he => by
  simp only [List.mem_singleton] at he; subst he; exact h
lemma ai0 : ∀ e ∈ ac0, Imp [] e.1 e.2 := by simp [ac0]
lemma j4_0 : ∀ e ∈ g4_0, Imp [] e.1 e.2 := okAll topC_ok k4_0 ai0
lemma ai1 : ∀ e ∈ ac1, Imp [] e.1 e.2 := apI (j4_0) (ai0)
lemma j3_0 : ∀ e ∈ g3_0, Imp [] e.1 e.2 := okAll topC_ok k3_0 ai1
lemma ai2 : ∀ e ∈ ac2, Imp [] e.1 e.2 := apI (j3_0) (ai1)
lemma j2_0 : ∀ e ∈ g2_0, Imp [] e.1 e.2 := okAll topC_ok k2_0 ai2
lemma j2_1 : ∀ e ∈ g2_1, Imp [] e.1 e.2 := okAll topC_ok k2_1 ai2
lemma ai3 : ∀ e ∈ ac3, Imp [] e.1 e.2 := apI (j2_0) (apI (j2_1) (ai2))
lemma j1_0 : ∀ e ∈ g1_0, Imp [] e.1 e.2 := okAll topC_ok k1_0 ai3
lemma j1_1 : ∀ e ∈ g1_1, Imp [] e.1 e.2 := okAll topC_ok k1_1 ai3
lemma ai4 : ∀ e ∈ ac4, Imp [] e.1 e.2 := apI (j1_0) (apI (j1_1) (ai3))
lemma base : Imp [] 0 15 := okR_imp topC_ok (x := (0, 15)) (Or.inl rfl) base_k (pickI ai4)
lemma w0_3_0_h : ∀ x ∈ rawT, x.1 ∈ w0_3_0.map (fun r => r.1.1) ++ ([] : List ℕ) → Imp [(false, 7, 8)] x.1 x.2 := ownAllP topC_ok (by decide) ai4 own0 w0_3_0_r
lemma w0_2_0_h : ∀ x ∈ rawT, x.1 ∈ w0_2_0.map (fun r => r.1.1) ++ (w0_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)) → Imp [(false, 7, 8)] x.1 x.2 := ownAllP topC_ok (by decide) ai4 w0_3_0_h w0_2_0_r
lemma w0_1_0_h : ∀ x ∈ rawT, x.1 ∈ w0_1_0.map (fun r => r.1.1) ++ (w0_2_0.map (fun r => r.1.1) ++ (w0_3_0.map (fun r => r.1.1) ++ ([] : List ℕ))) → Imp [(false, 7, 8)] x.1 x.2 := ownAllP topC_ok (by decide) ai4 w0_2_0_h w0_1_0_r
lemma w1_3_0_h : ∀ x ∈ rawT, x.1 ∈ w1_3_0.map (fun r => r.1.1) ++ ([] : List ℕ) → Imp [(true, 7, 8)] x.1 x.2 := ownAllP topC_ok (by decide) ai4 own0 w1_3_0_r
lemma w1_2_0_h : ∀ x ∈ rawT, x.1 ∈ w1_2_0.map (fun r => r.1.1) ++ (w1_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)) → Imp [(true, 7, 8)] x.1 x.2 := ownAllP topC_ok (by decide) ai4 w1_3_0_h w1_2_0_r
lemma w1_1_0_h : ∀ x ∈ rawT, x.1 ∈ w1_1_0.map (fun r => r.1.1) ++ (w1_2_0.map (fun r => r.1.1) ++ (w1_3_0.map (fun r => r.1.1) ++ ([] : List ℕ))) → Imp [(true, 7, 8)] x.1 x.2 := ownAllP topC_ok (by decide) ai4 w1_2_0_h w1_1_0_r
lemma w2_3_0_h : ∀ x ∈ rawT, x.1 ∈ w2_3_0.map (fun r => r.1.1) ++ ([] : List ℕ) → Imp [(false, 7, 9)] x.1 x.2 := ownAllP topC_ok (by decide) ai4 own0 w2_3_0_r
lemma w2_2_0_h : ∀ x ∈ rawT, x.1 ∈ w2_2_0.map (fun r => r.1.1) ++ (w2_3_0.map (fun r => r.1.1) ++ ([] : List ℕ)) → Imp [(false, 7, 9)] x.1 x.2 := ownAllP topC_ok (by decide) ai4 w2_3_0_h w2_2_0_r
lemma w2_1_0_h : ∀ x ∈ rawT, x.1 ∈ w2_1_0.map (fun r => r.1.1) ++ (w2_2_0.map (fun r => r.1.1) ++ (w2_3_0.map (fun r => r.1.1) ++ ([] : List ℕ))) → Imp [(false, 7, 9)] x.1 x.2 := ownAllP topC_ok (by decide) ai4 w2_2_0_h w2_1_0_r
lemma ty0 {L : ℕ} (hL : L ≤ 15) (h0 : Imp [] 0 L) : (∀ f ∈ gtypes.take 0, Imp [f] 0 L) → Imp [(false, 7, 8)] 0 L :=
  ty_imp (tt := ([[0], [1], [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]] : List (List ℕ))) ai4 w0_1_0_h qqk0.1 (by simp only [List.all_cons, List.all_nil, qqk0.2, qqk1, qqk2.1, Bool.and_true]) hL h0
lemma ty1 {L : ℕ} (hL : L ≤ 15) (h0 : Imp [] 0 L) : (∀ f ∈ gtypes.take 1, Imp [f] 0 L) → Imp [(true, 7, 8)] 0 L :=
  ty_impS (tt := ([[2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]] : List (List ℕ))) (R := rt1_0 ++ (rt1_1 ++ (rt1_2 ++ (rt1_3 ++ (rt1_4))))) ai4 w1_1_0_h qqk2.2 (by simp only [List.all_cons, List.all_nil, qqk8, Bool.and_true]) (all_app qqk3 (all_app qqk4 (all_app qqk5 (all_app qqk6 (qqk7))))) hL h0
lemma ty2 {L : ℕ} (hL : L ≤ 15) (h0 : Imp [] 0 L) : (∀ f ∈ gtypes.take 2, Imp [f] 0 L) → Imp [(false, 7, 9)] 0 L :=
  ty_impS (tt := ([[0], [2, 3, 4, 5, 6], [7, 8, 9, 10, 11, 12, 13, 14]] : List (List ℕ))) (R := rt2_0 ++ (rt2_1 ++ (rt2_2))) ai4 w2_1_0_h qqk9.1 (by simp only [List.all_cons, List.all_nil, qqk11.2, qqk12, qqk13, Bool.and_true]) (all_app qqk9.2 (all_app qqk10 (qqk11.1))) hL h0
lemma allT {L : ℕ} (hL : L ≤ 15) (h0 : Imp [] 0 L) : ∀ f ∈ gtypes, Imp [f] 0 L := chainT (fun i hi => by
  have hi : i < 3 := hi
  interval_cases i
  · exact ty0 hL h0
  · exact ty1 hL h0
  · exact ty2 hL h0)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
section circuit
variable (m : ℕ)
lemma getD_mem {S : Set ℕ} {w : List ℕ} (hw : ∀ x ∈ w, x ∈ S) (h0 : 0 ∈ S) (i : ℕ) : w.getD i 0 ∈ S := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · rw [List.getElem?_eq_getElem h]; exact hw _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none (by omega)]; exact h0
lemma ex_sol {T : ℕ} (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ), (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) → Sol Z0 m T gs.length S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact .done (getD_mem hw h0 i)
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → Sol Z0 m T (g :: gs).length S := fun h =>
      (ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT).mono (by simp) subset_rfl
    have go : Sol Z0 m T gs.length (insert (gv m w g) S) := ih (w ++ [gv m w g]) _ (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := false) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := true) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay hm
      | i :: _ => exact .un (rd i) go
lemma gv_sub {w : List ℕ} (hw : ∀ x ∈ w, x &&& m = x) (g : Gate) : gv m w g &&& m = gv m w g := by
  have rd : ∀ i, w.getD i 0 &&& m = w.getD i 0 := fun i => getD_mem (S := {x | x &&& m = x}) hw (by simp) i
  unfold gv
  split
  · simp
  · exact rd _
  · rw [Nat.and_assoc, rd]
  · simp
  · exact rd _
  · rw [Nat.and_or_distrib_right, rd, rd]
  · simp
  · rw [and_neg (Nat.and_self m), rd]
  · simp
lemma ex_sub {gs : List Gate} : ∀ {w : List ℕ}, (∀ x ∈ w, x &&& m = x) → ∀ x ∈ ex m gs w, x &&& m = x := by
  induction gs with
  | nil => intro w hw; exact hw
  | cons g gs ih =>
    intro w hw
    refine ih (w := w ++ [gv m w g]) fun x hx => ?_
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hw x hx
    · exact gv_sub m hw g
lemma getD_map (w : List ℕ) (b i : ℕ) : (w.map (fun x => x.testBit b)).getD i false = (w.getD i 0).testBit b := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp
lemma gv_bit {b : ℕ} (hb : m.testBit b = true) (w : List ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (gv m w g).testBit b = g.op.eval (g.inputs.map fun i => (w.map (fun x => x.testBit b)).getD i false) := by
  have e1 : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
  have e2 : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
  have e3 : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  obtain ⟨o, l⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_map]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  rcases hop with rfl | rfl | rfl
  · match l, hlen with
    | [], _ => simp [gv, e1, hb]
    | [i], _ => simp [gv, e1]
    | [i, j], _ => simp [gv, e1]
  · match l, hlen with
    | [], _ => simp [gv, e2]
    | [i], _ => simp [gv, e2]
    | [i, j], _ => simp [gv, e2]
  · match l, hlen with
    | [], _ => simp [gv, e3, hb]
    | [i], _ => simp [gv, e3, hb]
    | [i, j], _ => simp [gv, e3, hb]
lemma ex_bit {b : ℕ} (hb : m.testBit b = true) (gs : List Gate) : ∀ (w : List ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (ex m gs w).map (fun x => x.testBit b) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.map (fun x => x.testBit b)) := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hg
    rw [List.foldl_cons, ← gv_bit m hb w g (hg g List.mem_cons_self)]
    have := ih (w ++ [gv m w g]) (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    rw [List.map_append] at this
    exact this
end circuit
lemma rawP_len : rawP.length = 9 := rfl
lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 9 => (rawP.getD v.val 0).testBit b) = rawP.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len]
  · intro i h1 h2
    have : i < rawP.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl
lemma f_bit (k : ℕ) : EF.testBit k = f (fun v : Fin 9 => (rawP.getD v.val 0).testBit k) := by
  simp only [f, EF, Nat.testBit_or, Nat.testBit_and]
  rfl
lemma fold_pre (h : List Bool → Gate → Bool) (gs : List Gate) : ∀ w : List Bool, ∃ v, gs.foldl (fun w g => w ++ [h w g]) w = w ++ v := by
  induction gs with
  | nil => exact fun w => ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨v, hv⟩ := ih (w ++ [h w g])
    exact ⟨h w g :: v, by rw [List.foldl_cons, hv, List.append_assoc]; rfl⟩
lemma getD9 (l v : List Bool) (b : Bool) (hl : l.length = 9) : (l ++ [b] ++ v).getD 9 false = b := by
  rw [List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hl]
  rfl
theorem bridge1 (D : PEqualNP.CircuitLowerBounds.Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D)
    (hf : ∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = f y) (e : Bool × ℕ × ℕ) (F : (Fin 9 → Bool) → Bool)
    (hF : ∀ y : Fin 9 → Bool, (D.wires (List.ofFn y)).getD 9 false = F y) (y0 : Fin 9 → Bool) (hy0 : F y0 = true)
    (he : ∀ k, (mz 0).testBit k = true → (tw e).testBit k = F (fun v : Fin 9 => (rawP.getD v.val 0).testBit k)) :
    ∃ q, q + 1 = D.size ∧ Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [e] 0)) := by
  obtain ⟨gates, out⟩ := D
  cases gates with
  | nil =>
    exfalso
    have h := hF y0
    rw [hy0] at h
    change (List.ofFn y0).getD 9 false = true at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp)] at h
    simp at h
  | cons g gs =>
    refine ⟨gs.length, rfl, ?_⟩
    let row : ℕ → Fin 9 → Bool := fun k v => (rawP.getD v.val 0).testBit k
    let init : List ℕ := rawP.map (· &&& mz 0)
    have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by
      intro x hx
      simp only [init, List.mem_map] at hx
      obtain ⟨w, _, rfl⟩ := hx
      rw [Nat.and_assoc, Nat.and_self]
    have hinit_bits : ∀ k, (mz 0).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by
      intro k hk
      simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]
      rw [row_list]
    have hg : gv (mz 0) init g = tw e &&& mz 0 := by
      have hs : gv (mz 0) init g &&& mz 0 = gv (mz 0) init g := gv_sub (mz 0) hinit_sub g
      apply Nat.eq_of_testBit_eq; intro k
      rw [← hs, Nat.testBit_and, Nat.testBit_and]
      cases hk : (mz 0).testBit k with
      | false => simp
      | true =>
        simp only [Bool.and_true]
        rw [gv_bit (mz 0) hk init g (hD g List.mem_cons_self), hinit_bits k hk, he k hk]
        have h := hF (row k)
        obtain ⟨v, hv⟩ := fold_pre (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) gs
          (List.ofFn (row k) ++ [g.op.eval (g.inputs.map fun i => (List.ofFn (row k)).getD i false)])
        change ((g :: gs).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (row k))).getD 9 false = F (row k) at h
        rw [List.foldl_cons] at h
        have h2 := (congrArg (fun l : List Bool => l.getD 9 false) hv).symm.trans h
        exact (getD9 (List.ofFn (row k)) v _ (by simp)).symm.trans h2
    have hout : (ex (mz 0) (g :: gs) init).getD out 0 = tz 0 := by
      rw [← EF_ok]
      have hsub : ∀ x ∈ ex (mz 0) (g :: gs) init, x &&& mz 0 = x := ex_sub (mz 0) hinit_sub
      have hsub' := getD_mem (S := {x | x &&& mz 0 = x}) hsub (by simp) out
      apply Nat.eq_of_testBit_eq; intro k
      have e1 := congrArg (fun x => x.testBit k) hsub'
      simp only [Nat.testBit_and] at e1
      rw [← e1, Nat.testBit_and]
      cases hk : (mz 0).testBit k with
      | false => simp
      | true =>
        simp only [Bool.and_true]
        rw [← getD_map, ex_bit (mz 0) hk (g :: gs) init hD, hinit_bits k hk]
        have h := hf (row k)
        change ((g :: gs).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn (row k))).getD out false = f (row k) at h
        rw [h]
        exact (f_bit k).symm
    refine ex_sol (mz 0) gs (init ++ [gv (mz 0) init g]) (C (mz 0) (WZ [e] 0)) ?_ (Or.inr (Set.mem_insert _ _))
      (Or.inr (Set.mem_insert_of_mem _ rfl)) (fun x hx => hD x (List.mem_cons_of_mem _ hx)) ⟨out, hout⟩
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · simp only [init, List.mem_map] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
    · rw [List.mem_singleton.1 hx, hg]
      exact Or.inl ⟨tw e, by simp [rawL], rfl⟩
lemma tw_and (j : Fin 9) (k : ℕ) : (tw (false, 7, j.val)).testBit k = ((rawP.getD (7 : Fin 9).val 0).testBit k && (rawP.getD j.val 0).testBit k) := by
  have h : Nat.beq j.val 9 = false := by revert j; decide
  rw [tw_op (e := (false, 7, j.val)) h, op_bit]; rfl
lemma tw_or (j : Fin 9) (k : ℕ) : (tw (true, 7, j.val)).testBit k = ((rawP.getD (7 : Fin 9).val 0).testBit k || (rawP.getD j.val 0).testBit k) := by
  have h : Nat.beq j.val 9 = false := by revert j; decide
  rw [tw_op (e := (true, 7, j.val)) h, op_bit]; rfl
lemma tw_neg (k : ℕ) (hk : (mz 0).testBit k = true) : (tw (false, 7, 9)).testBit k = !((rawP.getD (7 : Fin 9).val 0).testBit k) := by
  have h := congrArg (fun x => x.testBit k) (tw_not (e := (false, 7, 9)) rfl 0)
  simp only [Nat.testBit_and, Nat.testBit_xor, hk, Bool.and_true, Bool.xor_true] at h
  exact h
theorem final : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 7)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 && y j)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size := by
  intro D hD h1 hf
  by_contra hlt
  have hf' : ∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = f y := fun y => congrFun hf y
  have go : ∀ e ∈ gtypes, ∀ F : (Fin 9 → Bool) → Bool, (∀ y : Fin 9 → Bool, (D.wires (List.ofFn y)).getD 9 false = F y) → ∀ y0, F y0 = true →
      (∀ k, (mz 0).testBit k = true → (tw e).testBit k = F (fun v : Fin 9 => (rawP.getD v.val 0).testBit k)) → False := by
    intro e he F hF y0 hy0 hb
    obtain ⟨q, hq, hs⟩ := bridge1 D hD hf' e F hF y0 hy0 hb
    exact allT le_rfl base e he q (by omega) hs
  rcases h1 with h | ⟨j, hj, h⟩ | ⟨j, hj, h⟩
  · exact go _ memN (fun y => !(y 7)) h (fun _ => false) rfl tw_neg
  · exact go _ (memA j hj) (fun y => y 7 && y j) h (fun _ => true) rfl (fun k _ => tw_and j k)
  · exact go _ (memO j hj) (fun y => y 7 || y j) h (fun _ => true) rfl (fun k _ => tw_or j k)
end PEqualNP.Outside.L_meta_17357

theorem PEqualNP.Outside.L_meta_17357 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 7)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 && y j)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size :=
  PEqualNP.Outside.L_meta_17357.final
