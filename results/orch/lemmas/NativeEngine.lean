import Std

namespace Engine

def listRec {α : Type u} {motive : List α → Sort v}
    (nil : motive []) (cons : (a : α) → (as : List α) → motive as → motive (a :: as))
    (xs : List α) : motive xs :=
  match xs with
  | [] => nil
  | a :: as => cons a as (listRec nil cons as)

def natRec {motive : Nat → Sort u} (zero : motive 0)
    (succ : (n : Nat) → motive n → motive (n+1)) (n : Nat) : motive n :=
  match n with
  | 0 => zero
  | n + 1 => succ n (natRec zero succ n)


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

def xRec {motive : X → Sort u}
    (mk : (w : W) → (s q n : Nat) → motive ⟨w,s,q,n⟩) (x : X) : motive x :=
  match x with
  | ⟨w,s,q,n⟩ => mk w s q n

structure Cm where
  a : List Nat
  b : List Nat

def NN : Nat := 501

def AA : Nat := 0xffffbfffef7fffdffff7bfffeeffffbfffeeffffbbfffeef7ffb57ffb5aabffdbffdbffdb56bffdabffdffed6bffd7ffbffdb6fff6fff0000000000000000

def HX : Nat := 0x4a8004a554002400240024a940025400200129400280040024900090000000000000000000

def HY : Nat := 0x100004000108000200008400011000040001100004400011080000000000000000000000000000000000000000000000000000000000000000000000000000

def st (n : Nat) (f : Nat → Bool) : Bool := f n

def sp (d : Bool) (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) ((bif d then l else (Nat.land s l)))

def cov (d : Bool) (l : Nat) (v : List W) : Nat :=
  listRec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor (sp d l w.s) ih) v

def twice (d : Bool) (l : Nat) (v : List W) : Nat :=
  listRec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (sp d l w.s) (cov d l t)) ih) v

def hit (f e : Nat) : Bool := ((bif (Nat.beq (Nat.land (Nat.land f e) HX) 0) then (false) else (((bif (Nat.beq (Nat.land (Nat.land f e) HY) 0) then (false) else (true))))))

def hits (f : Nat) (m : List Nat) : Bool := (listRec (motive := fun _ => Bool) (false) (fun e _ ih => ((bif (hit f e) then (true) else (ih)))) (m))

def flag (d : Bool) (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (sp d l w.s) o) AA

def rect (d : Bool) (l o : Nat) (v : List W) : List Nat → Bool :=
  listRec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => ((bif (hits (flag d l o w) m) then (true) else (ih (flag d l o w :: m))))) v

def app (x y : List Nat) : List Nat := listRec (motive := fun _ => List Nat) y (fun e _ ih => e :: ih) x

def join (k : List Cm → Bool) (f : Nat) (cs : List Cm) : List Nat → List Nat → List Cm → Bool :=
  listRec (motive := fun _ => List Nat → List Nat → List Cm → Bool) (fun S O R => k (⟨S, O⟩ :: R))
    (fun c _ ih S O R => (bif (hits f c.a) then ((bif (hits f c.b) then true else (ih (app c.b S) (app c.a O) R))) else ((bif (hits f c.b) then (ih (app c.a S) (app c.b O) R) else (ih S O (c :: R)))))) cs

def bip (l o : Nat) (v : List W) : List Cm → Bool :=
  listRec (motive := fun _ => List Cm → Bool) (fun _ => false)
    (fun w _ ih cs => (fun f => join ih f cs [f] [] []) (flag false l o w)) v

def anyE (m : List Nat) : Bool := listRec (motive := fun _ => Bool) false (fun f t ih => (bif (hits f t) then true else ih)) m

def rmF (f : Nat) (m : List Nat) : List Nat :=
  listRec (motive := fun _ => List Nat) [] (fun e t ih => (bif (hit f e) then t else (e :: ih))) m

def star (m : List Nat) : Bool := listRec (motive := fun _ => Bool) true (fun f t ih => (bif (hits f t) then ((bif (anyE t) then ((bif (hits f (rmF f t)) then false else ((bif (anyE (rmF f t)) then false else true)))) else true)) else ih)) m

def flk (l o : Nat) (v : List W) : (List Nat → Bool) → Bool :=
  listRec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k []) (fun w _ ih k => (fun f => ih (fun r => k (f :: r))) (flag false l o w)) v

def mkX (d : Bool) (l o : Nat) (v : List W) : List X :=
  listRec (motive := fun _ => List X) [] (fun w _ ih => ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩ :: ih) v

def rm (x y : Nat) (v : List W) : (List W → Bool) → Bool :=
  listRec (motive := fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => (bif (Nat.beq w.s x) then (ih h) else ((bif (Nat.beq w.s y) then (ih h) else (ih (fun r => h (w :: r))))))) v

def ins (o : W) (v : List W) : (List W → Bool) → Bool :=
  listRec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [o]) (fun w t ih h => (bif (Nat.ble w.s o.s) then ((bif (Nat.beq o.s w.s) then false else (h (o :: w :: t)))) else (ih (fun r => h (w :: r))))) v

def child (f : Nat → List W → Bool) (g : Nat) (mk : (List W → Bool) → Bool) (z : Nat) : Bool :=
  (bif (Nat.beq (Nat.land z g) g) then (st z (fun z => mk (f z))) else false)

def put (m s x y : Nat) (v : List W) (h : List W → Bool) : Bool :=
  (st (s) (fun s => ((bif (Nat.beq s 0) then (false) else (((bif (Nat.beq s m) then (false) else ((st (x) (fun x1 => (st (y) (fun y1 => (st (Nat.lor x y) (fun w => ins ⟨s, x1, y1, w, 0⟩ v h))))))))))))))

def kids (c : ((List W → Bool) → Bool) → Nat → Bool) (e n z x y a c' : Nat) (oa oc : Bool) (mk : (List W → Bool) → Bool) : Bool :=
  ((bif (((bif (oa) then (((bif (oc) then (c (fun h => mk (fun r => rm a c' r h)) z) else (false)))) else (false)))) then (true) else (((bif (((bif (Nat.ble (Nat.succ n) e) then (((bif (((bif (oc) then (c (fun h => mk (fun r => rm c' c' r h)) (Nat.sub z x)) else (false)))) then (true) else (((bif (oa) then (c (fun h => mk (fun r => rm a a r h)) (Nat.sub z y)) else (false))))))) else (false)))) then (true) else (((bif (Nat.ble (Nat.succ (Nat.succ n)) e) then (c mk (Nat.sub (Nat.sub z x) y)) else (false)))))))))

def mid (f : Nat → List W → Bool) (m g e n z : Nat) (v : List W) (a c : W) (da dc s x y : Nat) : Bool :=
  ((bif (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g) then ((st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) (fun z => kids (child f g) e n z a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v)))) else (false)))

def f0 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  ((bif (Nat.beq (Nat.lor da dc) 0) then (h a c da dc s x y) else (false)))

def f1 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  ((bif (Nat.beq (Nat.mul da dc) 0) then (h a c da dc s x y) else (false)))

def f2 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool := h a c da dc s x y

def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : X) : Bool :=
  xRec (motive := fun _ => Bool) (fun a s q u => xRec (motive := fun _ => Bool) (fun c s' q' u' => ((bif (h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b)) then (true) else (h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b))))) c) a

def scan (p : X → Bool) (xs : List X) : Bool := (listRec (motive := fun _ => Bool) (false) (fun c _ jh => ((bif (p c) then (true) else (jh)))) (xs))

def pairs (h : X → X → Bool) (xs : List X) : Bool :=
  (listRec (motive := fun _ => Bool) (false) (fun a r ih => ((bif (scan (h a) r) then (true) else (ih)))) (xs))

def pairsP (q : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => ((bif (Nat.beq a.s q) then (scan (fun c => ((bif (Nat.beq c.s q) then (false) else (h a c)))) xs) else (false)))) xs

def pairsQ (q q' : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => ((bif (Nat.beq a.s q) then (scan (fun c => ((bif (Nat.beq c.s q') then (h a c) else (false)))) xs) else (false)))) xs

def fr (xs : List X) : List X := listRec (motive := fun _ => List X) [] (fun a _ ih => (bif (Nat.beq a.w.r 0) then (a :: ih) else ih)) xs

def fs (xs : List X) : List X := listRec (motive := fun _ => List X) [] (fun a _ ih => (bif (Nat.beq a.w.r 0) then ih else (a :: ih))) xs

def pairsN (h : X → X → Bool) (xs : List X) : Bool :=
  (bif (pairs h (fr xs)) then true else (scan (fun a => scan (h a) (fs xs)) (fr xs)))

def pairsS (h : X → X → Bool) (xs : List X) : Bool := pairs h (fs xs)

def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  (listRec (motive := fun _ => Bool) (false) (fun a _ ih => ((bif (((bif (Nat.beq (Nat.succ a.s) q) then (false) else ((st (Nat.xor a.s m) (fun s => (st (Nat.sub z a.c) (fun z => ins ⟨s, a.b, a.a, a.c, 0⟩ v (fun v => ((bif (((bif (Nat.ble n e) then (child (f s) g (rm a.s a.s v) z) else (false)))) then (true) else (((bif (Nat.ble (Nat.succ n) e) then (child (f s) g (fun h => h v) (Nat.sub z a.c)) else (false))))))))))))))) then (true) else (ih)))) (r))

def pos (t : Nat) : Bool := natRec (motive := fun _ => Bool) false (fun _ _ => true) t

def wst (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twice d l v)

def node (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (X → X → Bool) → List X → Bool) : Bool :=
  (fun h => (fun xs => (bif (Nat.ble n e) then ((bif (Nat.ble (Nat.succ n) e) then (go (pair (f2 h)) xs) else (go (pair (f1 h)) xs))) else (go (pair (f0 h)) xs)))
    (mkX d l (wst d l v) v))
  (mid f m g e (Nat.pred n) z v)

def prd (t : Nat) (h : Nat → Bool) : Bool := natRec (motive := fun _ => Bool) false (fun s _ => h s) t

def cv (d : Bool) (l : Nat) (v : List W) (b : Bool) : Bool :=
  (bif d then b else ((bif (Nat.beq (cov d l v) l) then b else false)))

def tst (d : Bool) (l e : Nat) (v : List W) (F : Nat → Bool) : Bool :=
  (fun n => (bif (Nat.beq n e) then ((bif (rect d l (wst d l v) v []) then false else (F 0))) else ((bif (Nat.beq (Nat.succ n) e) then ((bif (bip l (wst d l v) v []) then false else ((bif (flk l (wst d l v) v star) then (F 0) else (F 1))))) else (F 0))))) v.length

def mv (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => (bif (node (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN) then true else (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (Nat.sub k s) v (fun y =>
      (bif (node (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)) then true else (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          node (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v))))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v v)))) v.length

def look (l m g : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  natRec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => (bif (Nat.ble v.length 1) then true else (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mv ih l m g k t z v y)))) fuel

def look1 (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  natRec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => (bif (Nat.ble v.length 1) then true else (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      (bif (node (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS) then true else (mv (look l m g K) l m g k t z v y)))))) fuel

def rawP : List Nat := [0x7fffc0000007fffc1e0000000a00010090009100b00010090100a005804009201400b02c048404c000000000000000004928064a10449410a508224a2088a9333a00889886ab60f09280000002080000001bffc010800028001ffe0600010003ffc360006fff7f6bf47fcec2a3d2, 0x7fffc000000000000000000000000001ffff07fffdc000002406010420332053206000020311207103001205240e20610481cc828000000000000000008252d494000928014a100494401150044c22357004cdce002501000018200018001800004000018bffc0001080017ff800186fff6000bcf76632d02fbf6d, 0x3fffe0000001ffff000001ffff7000000000008094001005210560054020c0923409404a081096012809434029082b000000000000000001108818222090452d91004122854668409203265b88106011088400004080001bffc00003060001a0000000c0bffc0000001b00006fffedc2c8d9ffd9f67f, 0x7fffc1ffff7fffdc00000000000000000038201103c00380038100503c0003801c1ac05800b00582681e001c0000000000000000022410610441220846022199c4066471991ce44060110182024100000300abffc00000001806bffc00000000d600000000001b6fff00007cbed5b267770fbf, 0x1ffff000000ffff8000007fffdc0000000000000000000000000609206a404a004a004a034a0520005202901285600ac056000150015000000000000000000bc0e08038043c70081c0111f8e0078001e0000781001e04200e3000035a0000000000001b50000000000000d6bffd7ffbffc000000000e7507fee214fdedb, 0xffffbfffef0000000000000000000000000000000281c000000c000c000c026a81c0241c00e0000180030018000060006000000000000000000c070301c0863f818fe07a1e000878021e0048780021e0084470357ff8000000000000001b56bffdabffdffe0000000000000000000000b8cd6f3dbf741d8e, 0x1ffff7fffde0000000000000000000000000000000000000000042e004b44700270027000000600006003000006000c0060000180018000000000000000000ff803fe00f7c001f00043e0000f8003e0008f80023e00008780357ffb5aabffdbffdbffc0000000000000000000000000000000000000d2fddbfff2dce621]

def xw (e : Nat × Nat) : Nat := rawP.getD e.1 0 ||| rawP.getD e.2 0

def rawL (E : List (Nat × Nat)) : List Nat := rawP ++ E.map xw

def FPM : Nat := 2 ^ 64 - 1

def FULL : Nat := 2 ^ NN - 1

def TG : Nat := 0xffffbfffef7fffdffff7bfffeeffffbfffeeffffbbfffeef7ffb57ffb5aabffdbffdbffdb56bffdabffdffed6bffd7ffbffdb6fff6fffffffffffffffffff

def kz (Z : Nat) : Nat := (List.range 7).foldr (fun i x => bif Nat.testBit Z i then Nat.lor x (Nat.land (Nat.lor (rawP.getD i 0) (Nat.shiftRight (rawP.getD i 0) NN)) FULL) else x) 0

def lz (Z : Nat) : Nat := Nat.land AA (Nat.xor (kz Z) FULL)

def fz (Z : Nat) : Nat := Nat.land FPM (Nat.xor (kz Z) FULL)

def mz (Z : Nat) : Nat := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) NN)

def tz (Z : Nat) : Nat := Nat.land TG (mz Z)

def pL (L : List Nat) : Nat := listRec (motive := fun _ => Nat) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih 5) d) L

def bit01 (b : Bool) : Nat := bif b then 1 else 0

def mkW (P : List Nat) (s : Nat) : W := ⟨s, pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0)), pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)),
  Nat.lor (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0))) (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n))), 3⟩

def addS (o : W) (v : List W) : List W := listRec (motive := fun _ => List W) [o]
  (fun w t ih => (bif (Nat.ble w.s o.s) then ((bif (Nat.beq o.s w.s) then (w :: t) else (o :: w :: t))) else (w :: ih))) v

def avl (P : List Nat) (m : Nat) (L : List Nat) : List W := listRec (motive := fun _ => List W) []
  (fun w _ ih => (bif (Nat.beq (Nat.land w m) 0) then ih else ((bif (Nat.beq (Nat.land w m) m) then ih else (addS (mkW P (Nat.land w m)) ih))))) L

def frc (v : List W) : (List W → Bool) → Bool := listRec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => st w.s fun s => st w.a fun a => st w.b fun b => st w.c fun c => ih fun r => h (⟨s, a, b, c, w.r⟩ :: r)) v

def anySub (d : Bool) (l : Nat) (v : List W) : Nat → (List W → Bool) → Bool := listRec (motive := fun _ => Nat → (List W → Bool) → Bool) (fun _ h => h [])
  (fun w t ih c h => (bif (st (Nat.lor c (sp d l w.s)) fun c => ih c fun r => h (w :: r)) then true else ((bif (Nat.beq (Nat.lor c (cov d l t)) l) then (ih c h) else false)))) v

def sumc (v : List W) : Nat := listRec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.add w.c ih) v

def MM : Nat := 214

def hb (H x : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1

def pairsC (H : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  listRec (motive := fun _ => Bool) false (fun a r ih => (bif (scan (fun x => (bif (hb H (Nat.add a.s x.s)) then (h a x) else false)) r) then true else ih)) xs

def topC (l m g K H ph k t z : Nat) (v : List W) : Bool :=
  (bif (Nat.ble v.length 1) then true else (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    (bif (node (look1 l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))) then true else ((bif (Nat.beq ph 1) then (mv (look l m g K) l m g k t z v y) else false))))))

def hasP (p : Nat) (v : List W) : Bool := (bif (Nat.beq p 0) then true else (listRec (motive := fun _ => Bool) false (fun w _ ih => (bif (Nat.beq w.s p) then true else ih)) v))

def startv (l m g B K t p H ph : Nat) (v : List W) : Bool :=
  (bif (hasP p v) then ((bif (Nat.ble v.length (Nat.sub (Nat.succ K) t)) then (child (fun z r => topC l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v))) else false)) else false)

def mFull (M : List (Nat × Nat)) : Bool := (List.range MM).all (fun r => M.any (fun p => hb p.1 r)) && M.any (fun p => Nat.beq p.2 1)

def PZ (Q : List (Nat × Nat)) : List Nat := Q.map (fun e => mz e.1)

def pOk (Z : Nat) (Q : List (Nat × Nat)) : Bool := !Nat.beq (tz Z) 0 && !Nat.beq (tz Z) (mz Z) && Q.all (fun e => Nat.beq (Nat.land (mz e.1) (mz Z)) (mz e.1) &&
  !Nat.beq (tz e.1) 0 && !Nat.beq (tz e.1) (mz e.1))

def pwr (E : List (Nat × Nat)) (Z : Nat) : Nat := (E.map fun e => Nat.land (xw e) (mz Z)).headD 0

def chk (E Q : List (Nat × Nat)) (Z K t H ph : Nat) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startv l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)

def FF : Nat := 2 ^ MM - 1

def okT (E Q : List (Nat × Nat)) (Z L : Nat) (ts : List Nat) : Bool := ts.all (fun t => !chk E Q Z (L - 1) t FF 1)

def okE (E Q : List (Nat × Nat)) (e : Nat × Nat) : Bool := pOk e.1 Q && Nat.ble e.2 15 && (Q.any (fun x => Nat.ble e.2 x.2) || okT E Q e.1 e.2 (List.range e.2))

def pr (T : List (Nat × Nat)) (Z : Nat) : List (Nat × Nat) := T.filter (fun e => Nat.beq (Nat.land Z e.1) Z && !Nat.beq Z e.1)

def okS (T : List (Nat × Nat)) (Z K : Nat) (p : Nat × Nat × Nat) : Bool := !chk [] (pr T Z) Z K p.1 p.2.1 p.2.2

def selT (M : List (Nat × Nat × Nat)) (t : Nat) : List (Nat × Nat) := (M.filter (fun p => Nat.beq p.1 t)).map Prod.snd

def okP (T : List (Nat × Nat)) (Z L : Nat) (M : List (Nat × Nat × Nat)) : Bool := pOk Z (pr T Z) && Nat.ble L 15 && (List.range L).all (fun t => mFull (selT M t))

end Engine
