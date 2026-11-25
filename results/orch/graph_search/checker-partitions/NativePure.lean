import Std

namespace NativeEngine

def lazyListRec {α β : Type} (z : β)
    (step : α → List α → (Unit → β) → β) : List α → β
  | [] => z
  | x :: xs => step x xs (fun _ => lazyListRec z step xs)

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

def AA : Nat := (0x0 + 2 ^ 60 * (0xfbffdb6fff6fff0 + 2 ^ 60 * (0xbffdffed6bffd7f + 2 ^ 60 * (0xffdbffdb56bffda + 2 ^ 60 * (0xfb57ffb5aabffdb + 2 ^ 60 * (0xeffffbbfffeef7f + 2 ^ 60 * (0xbfffeeffffbfffe + 2 ^ 60 * (0xfffef7fffdffff7 + 2 ^ 60 * 0xffffb))))))))

def HX : Nat := (0x0 + 2 ^ 60 * (0x40024900090000 + 2 ^ 60 * (0x400200129400280 + 2 ^ 60 * (0x240024a940025 + 2 ^ 60 * 0x4a8004a5540024))))

def HY : Nat := (0x0 + 2 ^ 60 * (0x0 + 2 ^ 60 * (0x0 + 2 ^ 60 * (0x0 + 2 ^ 60 * (0x0 + 2 ^ 60 * (0x100004400011080 + 2 ^ 60 * (0x400011000040001 + 2 ^ 60 * (0x108000200008 + 2 ^ 60 * 0x100004))))))))

def st (n : Nat) (f : Nat → Bool) : Bool := f n

def sp (d : Bool) (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) ((if d then l else (Nat.land s l)))

def cov (d : Bool) (l : Nat) (v : List W) : Nat :=
  (lazyListRec 0 (fun w _ lazyIH26  => Nat.lor (sp d l w.s) (lazyIH26 ())) v)

def twice (d : Bool) (l : Nat) (v : List W) : Nat :=
  (lazyListRec 0 (fun w t lazyIH25  => Nat.lor (Nat.land (sp d l w.s) (cov d l t)) (lazyIH25 ())) v)

def hit (f e : Nat) : Bool := ((if (Nat.beq (Nat.land (Nat.land f e) HX) 0) then (false) else (((if (Nat.beq (Nat.land (Nat.land f e) HY) 0) then (false) else (true))))))

def hits (f : Nat) (m : List Nat) : Bool := ((lazyListRec (false) (fun e _ lazyIH24  => ((if (hit f e) then (true) else ((lazyIH24 ()))))) (m)))

def flag (d : Bool) (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (sp d l w.s) o) AA

def rect (d : Bool) (l o : Nat) (v : List W) : List Nat → Bool :=
  (lazyListRec (fun _ => false) (fun w _ lazyIH23 m  => ((if (hits (flag d l o w) m) then (true) else ((lazyIH23 ()) (flag d l o w :: m))))) v)

def app (x y : List Nat) : List Nat := (lazyListRec y (fun e _ lazyIH22  => e :: (lazyIH22 ())) x)

def join (k : List Cm → Bool) (f : Nat) (cs : List Cm) : List Nat → List Nat → List Cm → Bool :=
  (lazyListRec (fun S O R => k (⟨S, O⟩ :: R)) (fun c _ lazyIH21 S O R  => (if (hits f c.a) then ((if (hits f c.b) then true else ((lazyIH21 ()) (app c.b S) (app c.a O) R))) else ((if (hits f c.b) then ((lazyIH21 ()) (app c.a S) (app c.b O) R) else ((lazyIH21 ()) S O (c :: R)))))) cs)

def bip (l o : Nat) (v : List W) : List Cm → Bool :=
  (lazyListRec (fun _ => false) (fun w _ lazyIH20 cs  => (fun f => join (lazyIH20 ()) f cs [f] [] []) (flag false l o w)) v)

def anyE (m : List Nat) : Bool := (lazyListRec false (fun f t lazyIH19  => (if (hits f t) then true else (lazyIH19 ()))) m)

def rmF (f : Nat) (m : List Nat) : List Nat :=
  (lazyListRec [] (fun e t lazyIH18  => (if (hit f e) then t else (e :: (lazyIH18 ())))) m)

def star (m : List Nat) : Bool := (lazyListRec true (fun f t lazyIH17  => (if (hits f t) then ((if (anyE t) then ((if (hits f (rmF f t)) then false else ((if (anyE (rmF f t)) then false else true)))) else true)) else (lazyIH17 ()))) m)

def flk (l o : Nat) (v : List W) : (List Nat → Bool) → Bool :=
  (lazyListRec (fun k => k []) (fun w _ lazyIH16 k  => (fun f => (lazyIH16 ()) (fun r => k (f :: r))) (flag false l o w)) v)

def mkX (d : Bool) (l o : Nat) (v : List W) : List X :=
  (lazyListRec [] (fun w _ lazyIH15  => ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩ :: (lazyIH15 ())) v)

def rm (x y : Nat) (v : List W) : (List W → Bool) → Bool :=
  (lazyListRec (fun h => h []) (fun w _ lazyIH14 h  => (if (Nat.beq w.s x) then ((lazyIH14 ()) h) else ((if (Nat.beq w.s y) then ((lazyIH14 ()) h) else ((lazyIH14 ()) (fun r => h (w :: r))))))) v)

def ins (o : W) (v : List W) : (List W → Bool) → Bool :=
  (lazyListRec (fun h => h [o]) (fun w t lazyIH13 h  => (if (Nat.ble w.s o.s) then ((if (Nat.beq o.s w.s) then false else (h (o :: w :: t)))) else ((lazyIH13 ()) (fun r => h (w :: r))))) v)

def child (f : Nat → List W → Bool) (g : Nat) (mk : (List W → Bool) → Bool) (z : Nat) : Bool :=
  (if (Nat.beq (Nat.land z g) g) then (st z (fun z => mk (f z))) else false)

def put (m s x y : Nat) (v : List W) (h : List W → Bool) : Bool :=
  (st (s) (fun s => ((if (Nat.beq s 0) then (false) else (((if (Nat.beq s m) then (false) else ((st (x) (fun x1 => (st (y) (fun y1 => (st (Nat.lor x y) (fun w => ins ⟨s, x1, y1, w, 0⟩ v h))))))))))))))

def kids (c : ((List W → Bool) → Bool) → Nat → Bool) (e n z x y a c' : Nat) (oa oc : Bool) (mk : (List W → Bool) → Bool) : Bool :=
  ((if (((if (oa) then (((if (oc) then (c (fun h => mk (fun r => rm a c' r h)) z) else (false)))) else (false)))) then (true) else (((if (((if (Nat.ble (Nat.succ n) e) then (((if (((if (oc) then (c (fun h => mk (fun r => rm c' c' r h)) (Nat.sub z x)) else (false)))) then (true) else (((if (oa) then (c (fun h => mk (fun r => rm a a r h)) (Nat.sub z y)) else (false))))))) else (false)))) then (true) else (((if (Nat.ble (Nat.succ (Nat.succ n)) e) then (c mk (Nat.sub (Nat.sub z x) y)) else (false)))))))))

def mid (f : Nat → List W → Bool) (m g e n z : Nat) (v : List W) (a c : W) (da dc s x y : Nat) : Bool :=
  ((if (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g) then ((st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) (fun z => kids (child f g) e n z a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v)))) else (false)))

def f0 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  ((if (Nat.beq (Nat.lor da dc) 0) then (h a c da dc s x y) else (false)))

def f1 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  ((if (Nat.beq (Nat.mul da dc) 0) then (h a c da dc s x y) else (false)))

def f2 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool := h a c da dc s x y

def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : X) : Bool :=
  h a.w c.w (Nat.xor (Nat.land a.u c.s) a.u) (Nat.xor (Nat.land c.u a.s) c.u) (Nat.land a.s c.s) (Nat.lor a.w.a c.w.a) (Nat.land a.w.b c.w.b) ||
  h a.w c.w (Nat.land a.u c.q) (Nat.land c.u a.q) (Nat.lor a.s c.s) (Nat.land a.w.a c.w.a) (Nat.lor a.w.b c.w.b)

def scan (p : X → Bool) (xs : List X) : Bool := ((lazyListRec (false) (fun c _ lazyIH12  => ((if (p c) then (true) else ((lazyIH12 ()))))) (xs)))

def pairs (h : X → X → Bool) (xs : List X) : Bool :=
  ((lazyListRec (false) (fun a r lazyIH11  => ((if (scan (h a) r) then (true) else ((lazyIH11 ()))))) (xs)))

def pairsP (q : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => ((if (Nat.beq a.s q) then (scan (fun c => ((if (Nat.beq c.s q) then (false) else (h a c)))) xs) else (false)))) xs

def pairsQ (q q' : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => ((if (Nat.beq a.s q) then (scan (fun c => ((if (Nat.beq c.s q') then (h a c) else (false)))) xs) else (false)))) xs

def fr (xs : List X) : List X := (lazyListRec [] (fun a _ lazyIH10  => (if (Nat.beq a.w.r 0) then (a :: (lazyIH10 ())) else (lazyIH10 ()))) xs)

def fs (xs : List X) : List X := (lazyListRec [] (fun a _ lazyIH9  => (if (Nat.beq a.w.r 0) then (lazyIH9 ()) else (a :: (lazyIH9 ())))) xs)

def pairsN (h : X → X → Bool) (xs : List X) : Bool :=
  (if (pairs h (fr xs)) then true else (scan (fun a => scan (h a) (fs xs)) (fr xs)))

def pairsS (h : X → X → Bool) (xs : List X) : Bool := pairs h (fs xs)

def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  ((lazyListRec (false) (fun a _ lazyIH8  => ((if (((if (Nat.beq (Nat.succ a.s) q) then (false) else ((st (Nat.xor a.s m) (fun s => (st (Nat.sub z a.c) (fun z => ins ⟨s, a.b, a.a, a.c, 0⟩ v (fun v => ((if (((if (Nat.ble n e) then (child (f s) g (rm a.s a.s v) z) else (false)))) then (true) else (((if (Nat.ble (Nat.succ n) e) then (child (f s) g (fun h => h v) (Nat.sub z a.c)) else (false))))))))))))))) then (true) else ((lazyIH8 ()))))) (r)))

def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t

def wst (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twice d l v)

def node (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (X → X → Bool) → List X → Bool) : Bool :=
  (fun h => (fun xs => (if (Nat.ble n e) then ((if (Nat.ble (Nat.succ n) e) then (go (pair (f2 h)) xs) else (go (pair (f1 h)) xs))) else (go (pair (f0 h)) xs)))
    (mkX d l (wst d l v) v))
  (mid f m g e (Nat.pred n) z v)

def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t

def cv (d : Bool) (l : Nat) (v : List W) (b : Unit → Bool) : Bool :=
  (if d then (b ()) else ((if (Nat.beq (cov d l v) l) then (b ()) else false)))

def tst (d : Bool) (l e : Nat) (v : List W) (F : Nat → Bool) : Bool :=
  (fun n => (if (Nat.beq n e) then ((if (rect d l (wst d l v) v []) then false else (F 0))) else ((if (Nat.beq (Nat.succ n) e) then ((if (bip l (wst d l v) v []) then false else ((if (flk l (wst d l v) v star) then (F 0) else (F 1))))) else (F 0))))) v.length

def mv (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => (if (node (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN) then true else (prd t (fun s => nots (fun q z v => (cv (pos s) l v (fun _ => (tst (pos s) l (Nat.sub k s) v (fun y =>
      (if (node (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)) then true else (prd s (fun s => nots (fun q' z v => (cv (pos s) l v (fun _ => (tst (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          node (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v))))))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v v)))) v.length

def look (l m g : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => (if (Nat.ble v.length 1) then true else (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mv ih l m g k t z v y)))) fuel

def look1 (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => (if (Nat.ble v.length 1) then true else (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      (if (node (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS) then true else (mv (look l m g K) l m g k t z v y)))))) fuel

def rawP : List Nat := [(0xf4351b55eebe6af + 2 ^ 60 * (0x3ffc360006ffff + 2 ^ 60 * (0x8001ffe06000100 + 2 ^ 60 * (0x1bffc01080002 + 2 ^ 60 * (0x280000002080000 + 2 ^ 60 * (0x889886ab60f09 + 2 ^ 60 * (0x8224a2088a9333a + 2 ^ 60 * (0x64a10449410a50 + 2 ^ 60 * (0x4928 + 2 ^ 60 * (0x2c048404c000000 + 2 ^ 60 * (0x5804009201400b0 + 2 ^ 60 * (0xb00010090100a00 + 2 ^ 60 * (0xa00010090009100 + 2 ^ 60 * (0x7fffc1e0000000 + 2 ^ 60 * 0x7fffc00000)))))))))))))), (0xe79a5deea977b69 + 2 ^ 60 * (0xf800186fff60003 + 2 ^ 60 * (0xbffc0001080017f + 2 ^ 60 * (0x1800004000018 + 2 ^ 60 * (0x501000018200018 + 2 ^ 60 * (0x22357004cdce002 + 2 ^ 60 * (0x494401150044c + 2 ^ 60 * (0xd494000928014a1 + 2 ^ 60 * (0x8252 + 2 ^ 60 * (0x481cc828000000 + 2 ^ 60 * (0x3001205240e2061 + 2 ^ 60 * (0x600002031120710 + 2 ^ 60 * (0x601042033205320 + 2 ^ 60 * (0x7fffdc00000240 + 2 ^ 60 * (0x1ffff + 2 ^ 60 * (0x0 + 2 ^ 60 * 0x7fffc0)))))))))))))))), (0xe7f7f8fb9aac5ec + 2 ^ 60 * (0x1b00006fff4 + 2 ^ 60 * (0xc0bffc00 + 2 ^ 60 * (0xffc00003060001a + 2 ^ 60 * (0x88400004080001b + 2 ^ 60 * (0x3265b881060110 + 2 ^ 60 * (0x41228546684092 + 2 ^ 60 * (0x18222090452d910 + 2 ^ 60 * (0x11088 + 2 ^ 60 * (0x4029082b0000000 + 2 ^ 60 * (0xa08109601280943 + 2 ^ 60 * (0x4020c0923409404 + 2 ^ 60 * (0x400100521056005 + 2 ^ 60 * (0x700000000000809 + 2 ^ 60 * (0x1ffff000001ffff + 2 ^ 60 * 0x3fffe000000))))))))))))))), (0xfabfac7f34f3e5a + 2 ^ 60 * (0x1b6fff0000b + 2 ^ 60 * (0xd6000000 + 2 ^ 60 * (0x1806bffc0 + 2 ^ 60 * (0x100000300abffc0 + 2 ^ 60 * (0xe44060110182024 + 2 ^ 60 * (0x199c4066471991c + 2 ^ 60 * (0x610441220846022 + 2 ^ 60 * (0x22410 + 2 ^ 60 * (0x681e001c0000000 + 2 ^ 60 * (0xc1ac05800b00582 + 2 ^ 60 * (0x8100503c0003801 + 2 ^ 60 * (0x8201103c0038003 + 2 ^ 60 * (0x3 + 2 ^ 60 * (0x1ffff7fffdc0000 + 2 ^ 60 * 0x7fffc))))))))))))))), (0x35f9c678b9af3d7 + 2 ^ 60 * (0xfbffc0000000009 + 2 ^ 60 * (0xd6bffd7f + 2 ^ 60 * (0x1b5000000 + 2 ^ 60 * (0xe3000035a000000 + 2 ^ 60 * (0x781001e04200 + 2 ^ 60 * (0x111f8e0078001e0 + 2 ^ 60 * (0x8038043c70081c0 + 2 ^ 60 * (0xbc0e0 + 2 ^ 60 * (0x15001500000000 + 2 ^ 60 * (0x1285600ac05600 + 2 ^ 60 * (0x34a05200052029 + 2 ^ 60 * (0x6a404a004a004a + 2 ^ 60 * (0x6092 + 2 ^ 60 * (0xc00000000000000 + 2 ^ 60 * (0xffff8000007fffd + 2 ^ 60 * 0x1ffff000000)))))))))))))))), (0xfd7afd45d43fff + 2 ^ 60 * (0xe + 2 ^ 60 * (0xbffdffe00000000 + 2 ^ 60 * (0x1b56bffda + 2 ^ 60 * (0x357ff800000000 + 2 ^ 60 * (0x48780021e008447 + 2 ^ 60 * (0xa1e000878021e00 + 2 ^ 60 * (0x1c0863f818fe07 + 2 ^ 60 * (0xc0703 + 2 ^ 60 * (0x6000600000000 + 2 ^ 60 * (0x18003001800 + 2 ^ 60 * (0x26a81c0241c00e + 2 ^ 60 * (0xc000c000c + 2 ^ 60 * (0x281c + 2 ^ 60 * (0x0 + 2 ^ 60 * 0xffffbfffef00000))))))))))))))), (0x9bfd7ba75f77035 + 2 ^ 60 * (0xd + 2 ^ 60 * (0x0 + 2 ^ 60 * (0xffdbffc00000000 + 2 ^ 60 * (0x357ffb5aabffdb + 2 ^ 60 * (0x8f80023e0000878 + 2 ^ 60 * (0x3e0000f8003e000 + 2 ^ 60 * (0xfe00f7c001f0004 + 2 ^ 60 * (0xff803 + 2 ^ 60 * (0x18001800000000 + 2 ^ 60 * (0x6000c006000 + 2 ^ 60 * (0x6000060030 + 2 ^ 60 * (0x4b447002700270 + 2 ^ 60 * (0x42e0 + 2 ^ 60 * (0x0 + 2 ^ 60 * (0x0 + 2 ^ 60 * 0x1ffff7fffde))))))))))))))))]

def xw (e : Nat × Nat) : Nat := rawP.getD e.1 0 ||| rawP.getD e.2 0

def rawL (E : List (Nat × Nat)) : List Nat := rawP ++ E.map xw

def FPM : Nat := 2 ^ 64 - 1

def FULL : Nat := 2 ^ NN - 1

def TG : Nat := (0xfffffffffffffff + 2 ^ 60 * (0xfbffdb6fff6ffff + 2 ^ 60 * (0xbffdffed6bffd7f + 2 ^ 60 * (0xffdbffdb56bffda + 2 ^ 60 * (0xfb57ffb5aabffdb + 2 ^ 60 * (0xeffffbbfffeef7f + 2 ^ 60 * (0xbfffeeffffbfffe + 2 ^ 60 * (0xfffef7fffdffff7 + 2 ^ 60 * 0xffffb))))))))

def kz (Z : Nat) : Nat := (List.range 7).foldr (fun i x => bif Nat.testBit Z i then Nat.lor x (Nat.land (Nat.lor (rawP.getD i 0) (Nat.shiftRight (rawP.getD i 0) NN)) FULL) else
  (bif Nat.testBit Z (i + 9) then Nat.lor x (Nat.xor FULL (Nat.land (rawP.getD i 0) (Nat.lor (Nat.shiftRight (rawP.getD i 0) NN) FPM))) else x)) 0

def lz (Z : Nat) : Nat := Nat.land AA (Nat.xor (kz Z) FULL)

def fz (Z : Nat) : Nat := Nat.land FPM (Nat.xor (kz Z) FULL)

def mz (Z : Nat) : Nat := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) NN)

def tz (Z : Nat) : Nat := Nat.land TG (mz Z)

def pL (L : List Nat) : Nat := (lazyListRec 0 (fun d _ lazyIH7  => Nat.add (Nat.shiftLeft (lazyIH7 ()) 5) d) L)

def bit01 (b : Bool) : Nat := bif b then 1 else 0

def mkW (P : List Nat) (s : Nat) : W := ⟨s, pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0)), pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)),
  Nat.lor (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0))) (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n))), 3⟩

def addS (o : W) (v : List W) : List W := (lazyListRec [o] (fun w t lazyIH6  => (if (Nat.ble w.s o.s) then ((if (Nat.beq o.s w.s) then (w :: t) else (o :: w :: t))) else (w :: (lazyIH6 ())))) v)

def avl (P : List Nat) (m : Nat) (L : List Nat) : List W := (lazyListRec [] (fun w _ lazyIH5  => (if (Nat.beq (Nat.land w m) 0) then (lazyIH5 ()) else ((if (Nat.beq (Nat.land w m) m) then (lazyIH5 ()) else (addS (mkW P (Nat.land w m)) (lazyIH5 ())))))) L)

def frc (v : List W) : (List W → Bool) → Bool := (lazyListRec (fun h => h []) (fun w _ lazyIH4 h  => st w.s fun s => st w.a fun a => st w.b fun b => st w.c fun c => (lazyIH4 ()) fun r => h (⟨s, a, b, c, w.r⟩ :: r)) v)

def anySub (d : Bool) (l : Nat) (v : List W) : Nat → (List W → Bool) → Bool := (lazyListRec (fun _ h => h []) (fun w t lazyIH3 c h  => (if (st (Nat.lor c (sp d l w.s)) fun c => (lazyIH3 ()) c fun r => h (w :: r)) then true else ((if (Nat.beq (Nat.lor c (cov d l t)) l) then ((lazyIH3 ()) c h) else false)))) v)

def sumc (v : List W) : Nat := (lazyListRec 0 (fun w _ lazyIH2  => Nat.add w.c (lazyIH2 ())) v)

def MM : Nat := 214

def hb (H x : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1

def pairsC (H : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  (lazyListRec false (fun a r lazyIH1  => (if (scan (fun x => (if (hb H (Nat.add a.s x.s)) then (h a x) else false)) r) then true else (lazyIH1 ()))) xs)

def topC (l m g K H ph k t z : Nat) (v : List W) : Bool :=
  (if (Nat.ble v.length 1) then true else (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    (if (node (look1 l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))) then true else ((if (Nat.beq ph 1) then (mv (look l m g K) l m g k t z v y) else false))))))

def hasP (p : Nat) (v : List W) : Bool := (if (Nat.beq p 0) then true else ((lazyListRec false (fun w _ lazyIH0  => (if (Nat.beq w.s p) then true else (lazyIH0 ()))) v)))

def startv (l m g B K t p H ph : Nat) (v : List W) : Bool :=
  (if (hasP p v) then ((if (Nat.ble v.length (Nat.sub (Nat.succ K) t)) then (child (fun z r => topC l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v))) else false)) else false)

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

def grp3 : List (Nat × Nat) := [(15, 1), (23, 4), (27, 2), (29, 2), (30, 4), (39, 1), (43, 2), (45, 1), (46, 2), (51, 2), (53, 2), (54, 2), (57, 1), (58, 4), (60, 1), (71, 1), (75, 1), (77, 2), (78, 2), (83, 1), (85, 4), (86, 2), (89, 1), (90, 2), (92, 2), (99, 1), (101, 2), (102, 1), (105, 2), (106, 4), (108, 2), (113, 1), (114, 1), (116, 1), (120, 1)]

def grp4 : List (Nat × Nat) := [(7, 4), (11, 4), (13, 4), (14, 5), (19, 5), (21, 5), (22, 5), (25, 4), (26, 5), (28, 5), (35, 4), (37, 4), (38, 4), (41, 4), (42, 5), (44, 4), (49, 4), (50, 5), (52, 4), (56, 4), (67, 3), (69, 5), (70, 4), (73, 4), (74, 5), (76, 3), (81, 4), (82, 4), (84, 5), (88, 4), (97, 4), (98, 4), (100, 4), (104, 5), (112, 3)]

def grp5 : List (Nat × Nat) := [(3, 7), (5, 7), (6, 7), (9, 7), (10, 7), (12, 6), (17, 7), (18, 7), (20, 7), (24, 7), (33, 7), (34, 7), (36, 7), (40, 7), (48, 7), (65, 7), (66, 7), (68, 6), (72, 6), (80, 7), (96, 7)]

def allSeeds : List (Nat × Nat) := grp3 ++ grp4 ++ grp5

def tg4 : List (Nat × Nat) := [(628, 1), (16459, 1), (32813, 1)]

def tg3 : List (Nat × Nat) := [(564, 2), (596, 2), (612, 2), (624, 2), (1080, 4), (2129, 4), (4194, 4), (8199, 4), (16395, 2), (16451, 2), (16457, 2), (16458, 2), (32781, 2), (32805, 2), (32809, 2), (32812, 2)]

def tg2 : List (Nat × Nat) := [(532, 3), (548, 3), (560, 3), (580, 3), (592, 3), (608, 3), (1048, 5), (1064, 5), (1072, 5), (2065, 5), (2113, 5), (2128, 5), (4130, 5), (4162, 5), (4192, 5), (8195, 5), (8197, 5), (8198, 5), (16387, 3), (16393, 3), (16394, 3), (16449, 3), (16450, 3), (16456, 3), (32773, 3), (32777, 3), (32780, 3), (32801, 3), (32804, 3), (32808, 3)]

def tg1 : List (Nat × Nat) := [(514, 3), (516, 4), (520, 3), (528, 4), (544, 4), (576, 4), (1025, 4), (1028, 4), (1032, 6), (1040, 6), (1056, 6), (1088, 4), (2049, 6), (2050, 4), (2056, 4), (2064, 6), (2080, 4), (2112, 6), (4097, 4), (4098, 6), (4100, 4), (4112, 4), (4128, 6), (4160, 6), (8193, 6), (8194, 6), (8196, 6), (8200, 4), (8224, 4), (8256, 4), (16385, 4), (16386, 4), (16388, 3), (16392, 4), (16400, 3), (16448, 4), (32769, 4), (32770, 3), (32772, 4), (32776, 4), (32784, 3), (32800, 4)]

def tg0 : List (Nat × Nat) := [(512, 5), (1024, 7), (2048, 7), (4096, 7), (8192, 7), (16384, 5), (32768, 5)]

def extendedSeeds : List (Nat × Nat) := allSeeds ++ tg4 ++ tg3 ++ tg2 ++ tg1 ++ tg0

def grpSix : List (Nat × Nat) := [(1,10),(2,10),(4,10),(8,10),(16,10),(32,10),(64,9)]

end NativeEngine

open NativeEngine

def main (args : List String) : IO Unit := do
  let projections := if args.contains "all" then grpSix ++ extendedSeeds
    else if args.contains "pair" then grpSix ++ tg0 ++ grp5
    else grpSix ++ tg0
  let before ← IO.monoMsNow
  IO.println s!"START {args} projections={projections.length}"
  (← IO.getStdout).flush
  if args.contains "regress" then
    for e in [(15,1),(23,4),(15,2),(23,5),(64,10)] do
      let result := okE [] (pr extendedSeeds e.1) e
      IO.println s!"REGRESSION {e} {result}"
      (← IO.getStdout).flush
  else
    let result := if args.contains "root13" then okE [] projections (0,13)
      else if args.contains "root14" then okE [] projections (0,14)
      else !chk [] projections 0 13 1 FF 1
    let after ← IO.monoMsNow
    IO.println s!"RESULT {args} {result} elapsed_ms={after-before}"
    (← IO.getStdout).flush

