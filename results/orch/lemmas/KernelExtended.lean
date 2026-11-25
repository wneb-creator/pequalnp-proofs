import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

noncomputable section Code
namespace PEqualNP.Outside.L_meta_10760_aux
open Finset
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

def Lg (N m T i : ℕ) : Prop := m.testBit i = true ∧ m.testBit (N + i) = true ∧ T.testBit i = true ∧ T.testBit (N + i) = false

def Ht (N m T : ℕ) (e : Bool) (S : Finset ℕ) (a b : ℕ) : Prop := ∃ i1 i2 j1 j2, Lg N m T i1 ∧ Lg N m T i2 ∧ Lg N m T j1 ∧ Lg N m T j2 ∧
  (∀ w ∈ S, w.testBit i1 = w.testBit i2) ∧ (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) ∧
  Uq N e S a i1 ∧ Uq N e S b i2 ∧ Uq N e S a j1 ∧ Uq N e S b j2 ∧ a.testBit i1 = a.testBit j1 ∧ b.testBit i2 = b.testBit j2

structure W where
  s : Nat
  a : Nat
  b : Nat
  c : Nat
  r : Nat

structure X where
  w : W
  s : Nat
  q : Nat
  u : Nat

structure Cm where
  a : List Nat
  b : List Nat

def NN : Nat := 501

def AA : Nat := (show {n : Nat // n = (0x0 + 2 ^ 60 * (0xfbffdb6fff6fff0 + 2 ^ 60 * (0xbffdffed6bffd7f + 2 ^ 60 * (0xffdbffdb56bffda + 2 ^ 60 * (0xfb57ffb5aabffdb + 2 ^ 60 * (0xeffffbbfffeef7f + 2 ^ 60 * (0xbfffeeffffbfffe + 2 ^ 60 * (0xfffef7fffdffff7 + 2 ^ 60 * 0xffffb))))))))} from ⟨_, by norm_num; rfl⟩).val

def HX : Nat := (show {n : Nat // n = (0x0 + 2 ^ 60 * (0x40024900090000 + 2 ^ 60 * (0x400200129400280 + 2 ^ 60 * (0x240024a940025 + 2 ^ 60 * 0x4a8004a5540024))))} from ⟨_, by norm_num; rfl⟩).val

def HY : Nat := (show {n : Nat // n = (0x0 + 2 ^ 60 * (0x0 + 2 ^ 60 * (0x0 + 2 ^ 60 * (0x0 + 2 ^ 60 * (0x0 + 2 ^ 60 * (0x100004400011080 + 2 ^ 60 * (0x400011000040001 + 2 ^ 60 * (0x108000200008 + 2 ^ 60 * 0x100004))))))))} from ⟨_, by norm_num; rfl⟩).val

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

def mkX (d : Bool) (l o : Nat) (v : List W) : List X :=
  List.rec (motive := fun _ => List X) [] (fun w _ ih => ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩ :: ih) v

def rm (x y : Nat) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (ih h) (Nat.beq w.s y)) (ih h) (Nat.beq w.s x)) v

def ins (o : W) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [o]) (fun w t ih h => Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive := fun _ => Bool) (h (o :: w :: t)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v

def child (f : Nat → List W → Bool) (g : Nat) (mk : (List W → Bool) → Bool) (z : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (st z (fun z => mk (f z))) (Nat.beq (Nat.land z g) g)

def put (m s x y : Nat) (v : List W) (h : List W → Bool) : Bool :=
  (st (s) (fun s => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((st (x) (fun x1 => (st (y) (fun y1 => (st (Nat.lor x y) (fun w => ins ⟨s, x1, y1, w, 0⟩ v h))))))) (false) (Nat.beq s m))) (false) (Nat.beq s 0))))

def kids (c : ((List W → Bool) → Bool) → Nat → Bool) (e n z x y a c' : Nat) (oa oc : Bool) (mk : (List W → Bool) → Bool) : Bool :=
  (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c mk (Nat.sub (Nat.sub z x) y)) (Nat.ble (Nat.succ (Nat.succ n)) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm a a r h)) (Nat.sub z y)) (oa))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm c' c' r h)) (Nat.sub z x)) (oc))))) (Nat.ble (Nat.succ n) e))))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm a c' r h)) z) (oc))) (oa))))

def mid (f : Nat → List W → Bool) (m g e n z : Nat) (v : List W) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) ((st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) (fun z => kids (child f g) e n z a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v)))) (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g))

def f0 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.lor da dc) 0))

def f1 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.mul da dc) 0))

def f2 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool := h a c da dc s x y

def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : X) : Bool :=
  X.rec (motive := fun _ => Bool) (fun a s q u => X.rec (motive := fun _ => Bool) (fun c s' q' u' => (Bool.rec (motive := fun _ => Bool) (h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)) (true) (h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b)))) c) a

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

def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) ((Bool.rec (motive := fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st (Nat.sub z a.c) (fun z => ins ⟨s, a.b, a.a, a.c, 0⟩ v (fun v => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))

def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t

def wst (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twice d l v)

def node (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (X → X → Bool) → List X → Bool) : Bool :=
  (fun h => (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive := fun _ => Bool) (go (pair (f1 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkX d l (wst d l v) v))
  (mid f m g e (Nat.pred n) z v)

def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t

def cv (d : Bool) (l : Nat) (v : List W) (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false b (Nat.beq (cov d l v) l)) b d

def tst (d : Bool) (l e : Nat) (v : List W) (F : Nat → Bool) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flk l (wst d l v) v star)) false (bip l (wst d l v) v []))
      (Nat.beq (Nat.succ n) e))
    (Bool.rec (motive := fun _ => Bool) (F 0) false (rect d l (wst d l v) v [])) (Nat.beq n e)) v.length

def mv (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          node (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (node (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v v)) true
    (node (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length

def look (l m g : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mv ih l m g k t z v y)) true (Nat.ble v.length 1)) fuel

def look1 (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) fuel

def Rep (v : List W) (S : Finset ℕ) : Prop := (v.map W.s).Nodup ∧ (v.map W.s).toFinset = S

def segsX : List (ℕ × ℕ) := [(63, 76), (76, 79), (79, 92), (92, 95), (95, 98), (98, 101), (101, 114), (114, 127), (127, 129), (129, 142), (142, 144), (144, 147), (147, 149), (149, 152), (152, 165), (165, 178), (178, 180), (180, 182), (182, 185), (185, 198), (198, 200), (200, 203), (203, 205), (205, 207), (207, 210), (210, 213), (213, 226), (226, 229), (229, 242), (242, 245), (245, 258), (258, 260), (260, 262), (262, 264), (264, 266), (266, 269), (269, 271), (271, 274), (274, 287), (287, 289), (289, 291), (291, 294)]

def segsY : List (ℕ × ℕ) := [(294, 307), (307, 312), (312, 316), (316, 334), (334, 338), (338, 356), (356, 360), (360, 378), (378, 396), (396, 400), (400, 418), (418, 423), (423, 441), (441, 459), (459, 464), (464, 482), (482, 500)]

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

def Cl (P : List ℕ) (T k : ℕ) (b : ℕ → ℕ) (S : Finset ℕ) : Prop := ∀ j < P.length, ∀ q, q + b j < k →
  ¬ Sol Z0 (P.getD j 0) (T &&& P.getD j 0) q (C (P.getD j 0) (Im (P.getD j 0) S))

structure StOk (P : List ℕ) (T l k z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  bud : ∃ b : ℕ → ℕ, (∀ j < P.length, b j ≤ 15) ∧ Cl P T k b S ∧ z = pk P.length (fun j => 16 + b j - cnt v j)

structure Ctx (P : List ℕ) (l m g T : ℕ) : Prop where
  lg : ∀ i, l.testBit i = true → Lg NN m T i ∧ AA.testBit i = true
  hP : ∀ j < P.length, P.getD j 0 &&& m = P.getD j 0 ∧ T &&& P.getD j 0 ≠ 0 ∧ T &&& P.getD j 0 ≠ P.getD j 0
  hg : g = pk P.length (fun _ => 16)

inductive Shape (o a c : W) (v : List W) : Bool → Bool → List W → Prop
  | ff {r} : (a :: c :: r).Perm (o :: v) → Shape o a c v false false r
  | tf {r} : (c :: r).Perm (o :: v) → Shape o a c v true false r
  | ft {r} : (a :: r).Perm (o :: v) → Shape o a c v false true r
  | tt {r} : r.Perm (o :: v) → Shape o a c v true true r

def opW (d : Bool) (a c : W) : W := bif d then ⟨a.s ||| c.s, a.a &&& c.a, a.b ||| c.b, (a.a &&& c.a) ||| (a.b ||| c.b), 0⟩
  else ⟨a.s &&& c.s, a.a ||| c.a, a.b &&& c.b, (a.a ||| c.a) ||| (a.b &&& c.b), 0⟩

def mkx (d : Bool) (l o : ℕ) (w : W) : X := ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩

def modeF (n e : ℕ) : (W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ n) e then f2 else f1) else f0

def dfc (d d' : Bool) (l o : ℕ) (a c : W) : ℕ := bif d' then Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s NN)
  else Nat.xor (Nat.land (Nat.land (sp d l a.s) o) c.s) (Nat.land (sp d l a.s) o)

def CmOk (F : W → ℕ) (r : List W) (col : ℕ → ℕ) (c : Cm) : Prop := ∃ κ ≤ 1, (∀ e ∈ c.a, ∃ w ∈ r, F w = e ∧ col w.s = κ) ∧
  ∀ e ∈ c.b, ∃ w ∈ r, F w = e ∧ col w.s = 1 - κ

def NK (R : ℕ → ℕ) (m T k' t : ℕ) (S : Finset ℕ) : Prop :=
  (∀ d a b S1 k0, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → S1.card < S.card) ∧
  ∀ a S1 k0 t0, k' = k0 + 1 → t = t0 + 1 → Un m a S S1 → Live R m T k0 t0 S1 → S1.card ≤ S.card

def notW (m : ℕ) (a : W) : W := ⟨a.s ^^^ m, a.b, a.a, a.c, 0⟩

def Cod (R : ℕ → ℕ) (v : List W) : Prop := ∀ w ∈ v, w.r = 0 ∨ w.r = R w.s

def RR (R : ℕ → ℕ) : Prop := ∀ d a b, R a ≠ 0 → R b ≠ 0 → ¬ Al R d a b

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
def rawP : List ℕ := (show {ns : List Nat // ns = [(0xf4351b55eebe6af + 2 ^ 60 * (0x3ffc360006ffff + 2 ^ 60 * (0x8001ffe06000100 + 2 ^ 60 * (0x1bffc01080002 + 2 ^ 60 * (0x280000002080000 + 2 ^ 60 * (0x889886ab60f09 + 2 ^ 60 * (0x8224a2088a9333a + 2 ^ 60 * (0x64a10449410a50 + 2 ^ 60 * (0x4928 + 2 ^ 60 * (0x2c048404c000000 + 2 ^ 60 * (0x5804009201400b0 + 2 ^ 60 * (0xb00010090100a00 + 2 ^ 60 * (0xa00010090009100 + 2 ^ 60 * (0x7fffc1e0000000 + 2 ^ 60 * 0x7fffc00000)))))))))))))), (0xe79a5deea977b69 + 2 ^ 60 * (0xf800186fff60003 + 2 ^ 60 * (0xbffc0001080017f + 2 ^ 60 * (0x1800004000018 + 2 ^ 60 * (0x501000018200018 + 2 ^ 60 * (0x22357004cdce002 + 2 ^ 60 * (0x494401150044c + 2 ^ 60 * (0xd494000928014a1 + 2 ^ 60 * (0x8252 + 2 ^ 60 * (0x481cc828000000 + 2 ^ 60 * (0x3001205240e2061 + 2 ^ 60 * (0x600002031120710 + 2 ^ 60 * (0x601042033205320 + 2 ^ 60 * (0x7fffdc00000240 + 2 ^ 60 * (0x1ffff + 2 ^ 60 * (0x0 + 2 ^ 60 * 0x7fffc0)))))))))))))))), (0xe7f7f8fb9aac5ec + 2 ^ 60 * (0x1b00006fff4 + 2 ^ 60 * (0xc0bffc00 + 2 ^ 60 * (0xffc00003060001a + 2 ^ 60 * (0x88400004080001b + 2 ^ 60 * (0x3265b881060110 + 2 ^ 60 * (0x41228546684092 + 2 ^ 60 * (0x18222090452d910 + 2 ^ 60 * (0x11088 + 2 ^ 60 * (0x4029082b0000000 + 2 ^ 60 * (0xa08109601280943 + 2 ^ 60 * (0x4020c0923409404 + 2 ^ 60 * (0x400100521056005 + 2 ^ 60 * (0x700000000000809 + 2 ^ 60 * (0x1ffff000001ffff + 2 ^ 60 * 0x3fffe000000))))))))))))))), (0xfabfac7f34f3e5a + 2 ^ 60 * (0x1b6fff0000b + 2 ^ 60 * (0xd6000000 + 2 ^ 60 * (0x1806bffc0 + 2 ^ 60 * (0x100000300abffc0 + 2 ^ 60 * (0xe44060110182024 + 2 ^ 60 * (0x199c4066471991c + 2 ^ 60 * (0x610441220846022 + 2 ^ 60 * (0x22410 + 2 ^ 60 * (0x681e001c0000000 + 2 ^ 60 * (0xc1ac05800b00582 + 2 ^ 60 * (0x8100503c0003801 + 2 ^ 60 * (0x8201103c0038003 + 2 ^ 60 * (0x3 + 2 ^ 60 * (0x1ffff7fffdc0000 + 2 ^ 60 * 0x7fffc))))))))))))))), (0x35f9c678b9af3d7 + 2 ^ 60 * (0xfbffc0000000009 + 2 ^ 60 * (0xd6bffd7f + 2 ^ 60 * (0x1b5000000 + 2 ^ 60 * (0xe3000035a000000 + 2 ^ 60 * (0x781001e04200 + 2 ^ 60 * (0x111f8e0078001e0 + 2 ^ 60 * (0x8038043c70081c0 + 2 ^ 60 * (0xbc0e0 + 2 ^ 60 * (0x15001500000000 + 2 ^ 60 * (0x1285600ac05600 + 2 ^ 60 * (0x34a05200052029 + 2 ^ 60 * (0x6a404a004a004a + 2 ^ 60 * (0x6092 + 2 ^ 60 * (0xc00000000000000 + 2 ^ 60 * (0xffff8000007fffd + 2 ^ 60 * 0x1ffff000000)))))))))))))))), (0xfd7afd45d43fff + 2 ^ 60 * (0xe + 2 ^ 60 * (0xbffdffe00000000 + 2 ^ 60 * (0x1b56bffda + 2 ^ 60 * (0x357ff800000000 + 2 ^ 60 * (0x48780021e008447 + 2 ^ 60 * (0xa1e000878021e00 + 2 ^ 60 * (0x1c0863f818fe07 + 2 ^ 60 * (0xc0703 + 2 ^ 60 * (0x6000600000000 + 2 ^ 60 * (0x18003001800 + 2 ^ 60 * (0x26a81c0241c00e + 2 ^ 60 * (0xc000c000c + 2 ^ 60 * (0x281c + 2 ^ 60 * (0x0 + 2 ^ 60 * 0xffffbfffef00000))))))))))))))), (0x9bfd7ba75f77035 + 2 ^ 60 * (0xd + 2 ^ 60 * (0x0 + 2 ^ 60 * (0xffdbffc00000000 + 2 ^ 60 * (0x357ffb5aabffdb + 2 ^ 60 * (0x8f80023e0000878 + 2 ^ 60 * (0x3e0000f8003e000 + 2 ^ 60 * (0xfe00f7c001f0004 + 2 ^ 60 * (0xff803 + 2 ^ 60 * (0x18001800000000 + 2 ^ 60 * (0x6000c006000 + 2 ^ 60 * (0x6000060030 + 2 ^ 60 * (0x4b447002700270 + 2 ^ 60 * (0x42e0 + 2 ^ 60 * (0x0 + 2 ^ 60 * (0x0 + 2 ^ 60 * 0x1ffff7fffde))))))))))))))))]} from ⟨_, by norm_num; rfl⟩).val

def xw (e : ℕ × ℕ) : ℕ := rawP.getD e.1 0 ||| rawP.getD e.2 0

def rawL (E : List (ℕ × ℕ)) : List ℕ := rawP ++ E.map xw

def six : List (ℕ × ℕ) := []

def rawG : List ℕ := rawL six

def FPM : ℕ := 2 ^ 64 - 1

def FULL : ℕ := 2 ^ NN - 1

def TG : ℕ := (show {n : Nat // n = (0xfffffffffffffff + 2 ^ 60 * (0xfbffdb6fff6ffff + 2 ^ 60 * (0xbffdffed6bffd7f + 2 ^ 60 * (0xffdbffdb56bffda + 2 ^ 60 * (0xfb57ffb5aabffdb + 2 ^ 60 * (0xeffffbbfffeef7f + 2 ^ 60 * (0xbfffeeffffbfffe + 2 ^ 60 * (0xfffef7fffdffff7 + 2 ^ 60 * 0xffffb))))))))} from ⟨_, by norm_num; rfl⟩).val

def kz (Z : ℕ) : ℕ := (List.range 7).foldr (fun i x => bif Nat.testBit Z i then Nat.lor x (Nat.land (Nat.lor (rawP.getD i 0) (Nat.shiftRight (rawP.getD i 0) NN)) FULL) else
  (bif Nat.testBit Z (i + 9) then Nat.lor x (Nat.xor FULL (Nat.land (rawP.getD i 0) (Nat.lor (Nat.shiftRight (rawP.getD i 0) NN) FPM))) else x)) 0

def lz (Z : ℕ) : ℕ := Nat.land AA (Nat.xor (kz Z) FULL)

def fz (Z : ℕ) : ℕ := Nat.land FPM (Nat.xor (kz Z) FULL)

def mz (Z : ℕ) : ℕ := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) NN)

def tz (Z : ℕ) : ℕ := Nat.land TG (mz Z)

def segGood (w o : ℕ) (s : ℕ × ℕ) : Bool :=
  Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) 0 || Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) (2 ^ (s.2 - s.1 - 1) - 1)

def pL (L : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih 5) d) L

def bit01 (b : Bool) : ℕ := bif b then 1 else 0

def mkW (P : List ℕ) (s : ℕ) : W := ⟨s, pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0)), pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)),
  Nat.lor (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0))) (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n))), 3⟩

def addS (o : W) (v : List W) : List W := List.rec (motive := fun _ => List W) [o]
  (fun w t ih => Bool.rec (motive := fun _ => List W) (w :: ih) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v

def avl (P : List ℕ) (m : ℕ) (L : List ℕ) : List W := List.rec (motive := fun _ => List W) []
  (fun w _ ih => Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land w m)) ih) ih (Nat.beq (Nat.land w m) m)) ih (Nat.beq (Nat.land w m) 0)) L

def frc (v : List W) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => st w.s fun s => st w.a fun a => st w.b fun b => st w.c fun c => ih fun r => h (⟨s, a, b, c, w.r⟩ :: r)) v

def anySub (d : Bool) (l : ℕ) (v : List W) : ℕ → (List W → Bool) → Bool := List.rec (motive := fun _ => ℕ → (List W → Bool) → Bool) (fun _ h => h [])
  (fun w t ih c h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (ih c h) (Nat.beq (Nat.lor c (cov d l t)) l)) true
    (st (Nat.lor c (sp d l w.s)) fun c => ih c fun r => h (w :: r))) v

def sumc (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add w.c ih) v

def MM : ℕ := 214

def hb (H x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1

def pairsC (H : ℕ) (h : X → X → Bool) (xs : List X) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a r ih => Bool.rec (motive := fun _ => Bool) ih true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r)) xs

def topC (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (node (look1 l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)

def hasP (p : ℕ) (v : List W) : Bool := Bool.rec (motive := fun _ => Bool)
  (List.rec (motive := fun _ => Bool) false (fun w _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w.s p)) v) true (Nat.beq p 0)

def startv (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topC l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)

def Srt (v : List W) : Prop := v.Pairwise (fun a b => b.s < a.s)

def mFull (M : List (ℕ × ℕ)) : Bool := (List.range MM).all (fun r => M.any (fun p => hb p.1 r)) && M.any (fun p => Nat.beq p.2 1)

def WZ (E : List (ℕ × ℕ)) (Z : ℕ) : Set ℕ := {x | ∃ w ∈ rawL E, x = w &&& mz Z}

def Imp (E : List (ℕ × ℕ)) (Z L : ℕ) : Prop := ∀ q < L, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z))

def PZ (Q : List (ℕ × ℕ)) : List ℕ := Q.map (fun e => mz e.1)

def pOk (Z : ℕ) (Q : List (ℕ × ℕ)) : Bool := !Nat.beq (tz Z) 0 && !Nat.beq (tz Z) (mz Z) && Q.all (fun e => Nat.beq (Nat.land (mz e.1) (mz Z)) (mz e.1) &&
  !Nat.beq (tz e.1) 0 && !Nat.beq (tz e.1) (mz e.1))

def pwr (E : List (ℕ × ℕ)) (Z : ℕ) : ℕ := (E.map fun e => Nat.land (xw e) (mz Z)).headD 0

noncomputable def chk (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startv l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)

open Classical in
noncomputable def RZ (E : List (ℕ × ℕ)) (Z : ℕ) : ℕ → ℕ := fun s => if s ∈ WZ E Z then 3 else 0

def FF : ℕ := 2 ^ MM - 1

noncomputable def okT (E Q : List (ℕ × ℕ)) (Z L : ℕ) (ts : List ℕ) : Bool := ts.all (fun t => !chk E Q Z (L - 1) t FF 1)

noncomputable def okE (E Q : List (ℕ × ℕ)) (e : ℕ × ℕ) : Bool := pOk e.1 Q && Nat.ble e.2 15 && (Q.any (fun x => Nat.ble e.2 x.2) || okT E Q e.1 e.2 (List.range e.2))

def pr (T : List (ℕ × ℕ)) (Z : ℕ) : List (ℕ × ℕ) := T.filter (fun e => Nat.beq (Nat.land Z e.1) Z && !Nat.beq Z e.1)

noncomputable def okS (T : List (ℕ × ℕ)) (Z K : ℕ) (p : ℕ × ℕ × ℕ) : Bool := !chk [] (pr T Z) Z K p.1 p.2.1 p.2.2

def selT (M : List (ℕ × ℕ × ℕ)) (t : ℕ) : List (ℕ × ℕ) := (M.filter (fun p => Nat.beq p.1 t)).map Prod.snd

def okP (T : List (ℕ × ℕ)) (Z L : ℕ) (M : List (ℕ × ℕ × ℕ)) : Bool := pOk Z (pr T Z) && Nat.ble L 15 && (List.range L).all (fun t => mFull (selT M t))

def grp3 : List (Nat × Nat) := [(15, 1), (23, 4), (27, 2), (29, 2), (30, 4), (39, 1), (43, 2), (45, 1), (46, 2), (51, 2), (53, 2), (54, 2), (57, 1), (58, 4), (60, 1), (71, 1), (75, 1), (77, 2), (78, 2), (83, 1), (85, 4), (86, 2), (89, 1), (90, 2), (92, 2), (99, 1), (101, 2), (102, 1), (105, 2), (106, 4), (108, 2), (113, 1), (114, 1), (116, 1), (120, 1)]

def ac3 : List (Nat × Nat) := []

def grp4 : List (Nat × Nat) := [(7, 4), (11, 4), (13, 4), (14, 5), (19, 5), (21, 5), (22, 5), (25, 4), (26, 5), (28, 5), (35, 4), (37, 4), (38, 4), (41, 4), (42, 5), (44, 4), (49, 4), (50, 5), (52, 4), (56, 4), (67, 3), (69, 5), (70, 4), (73, 4), (74, 5), (76, 3), (81, 4), (82, 4), (84, 5), (88, 4), (97, 4), (98, 4), (100, 4), (104, 5), (112, 3)]

def ac4 : List (Nat × Nat) := grp3

def grp5 : List (Nat × Nat) := [(3, 7), (5, 7), (6, 7), (9, 7), (10, 7), (12, 6), (17, 7), (18, 7), (20, 7), (24, 7), (33, 7), (34, 7), (36, 7), (40, 7), (48, 7), (65, 7), (66, 7), (68, 6), (72, 6), (80, 7), (96, 7)]

def ac5 : List (Nat × Nat) := grp3 ++ grp4

def allSeeds : List (Nat × Nat) := grp3 ++ grp4 ++ grp5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma seed3 : grp3.all (fun e => okE [] (pr ac3 e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma seed4 : grp4.all (fun e => okE [] (pr ac4 e.1) e) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma seed5 : grp5.all (fun e => okE [] (pr ac5 e.1) e) = true := by decide +kernel
def tg4 : List (Nat × Nat) := [(628, 1), (16459, 1), (32813, 1)]
def ta4 : List (Nat × Nat) := allSeeds
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tcheck4 : tg4.all (fun e => okE [] (pr ta4 e.1) e) = true := by decide +kernel
def tg3 : List (Nat × Nat) := [(564, 2), (596, 2), (612, 2), (624, 2), (1080, 4), (2129, 4), (4194, 4), (8199, 4), (16395, 2), (16451, 2), (16457, 2), (16458, 2), (32781, 2), (32805, 2), (32809, 2), (32812, 2)]
def ta3 : List (Nat × Nat) := allSeeds ++ tg4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tcheck3 : tg3.all (fun e => okE [] (pr ta3 e.1) e) = true := by decide +kernel
def tg2 : List (Nat × Nat) := [(532, 3), (548, 3), (560, 3), (580, 3), (592, 3), (608, 3), (1048, 5), (1064, 5), (1072, 5), (2065, 5), (2113, 5), (2128, 5), (4130, 5), (4162, 5), (4192, 5), (8195, 5), (8197, 5), (8198, 5), (16387, 3), (16393, 3), (16394, 3), (16449, 3), (16450, 3), (16456, 3), (32773, 3), (32777, 3), (32780, 3), (32801, 3), (32804, 3), (32808, 3)]
def ta2 : List (Nat × Nat) := allSeeds ++ tg4 ++ tg3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tcheck2 : tg2.all (fun e => okE [] (pr ta2 e.1) e) = true := by decide +kernel
def tg1 : List (Nat × Nat) := [(514, 3), (516, 4), (520, 3), (528, 4), (544, 4), (576, 4), (1025, 4), (1028, 4), (1032, 6), (1040, 6), (1056, 6), (1088, 4), (2049, 6), (2050, 4), (2056, 4), (2064, 6), (2080, 4), (2112, 6), (4097, 4), (4098, 6), (4100, 4), (4112, 4), (4128, 6), (4160, 6), (8193, 6), (8194, 6), (8196, 6), (8200, 4), (8224, 4), (8256, 4), (16385, 4), (16386, 4), (16388, 3), (16392, 4), (16400, 3), (16448, 4), (32769, 4), (32770, 3), (32772, 4), (32776, 4), (32784, 3), (32800, 4)]
def ta1 : List (Nat × Nat) := allSeeds ++ tg4 ++ tg3 ++ tg2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tcheck1 : tg1.all (fun e => okE [] (pr ta1 e.1) e) = true := by decide +kernel
def tg0 : List (Nat × Nat) := [(512, 5), (1024, 7), (2048, 7), (4096, 7), (8192, 7), (16384, 5), (32768, 5)]
def ta0 : List (Nat × Nat) := allSeeds ++ tg4 ++ tg3 ++ tg2 ++ tg1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma tcheck0 : tg0.all (fun e => okE [] (pr ta0 e.1) e) = true := by decide +kernel
def extendedSeeds : List (Nat × Nat) := allSeeds ++ tg4 ++ tg3 ++ tg2 ++ tg1 ++ tg0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma six1 : okE [] (pr extendedSeeds 1) (1, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma six2 : okE [] (pr extendedSeeds 2) (2, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma six4 : okE [] (pr extendedSeeds 4) (4, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma six8 : okE [] (pr extendedSeeds 8) (8, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma six16 : okE [] (pr extendedSeeds 16) (16, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma six32 : okE [] (pr extendedSeeds 32) (32, 10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma six64 : okE [] (pr extendedSeeds 64) (64, 9) = true := by decide +kernel
end PEqualNP.Outside.L_meta_10760_aux
end Code
