def lookMarked (pick : Nat → Nat → Nat → List W → Bool) (l m g : Nat) (depth : Nat) :
    Nat → Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → List W → Bool)
    (fun fuel k t z v => Bool.rec (motive := fun _ => Bool) false
      (look l m g fuel k t z v) (pick k t z v))
    (fun _ prev => Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool)
      (fun _ _ _ _ => true)
      (fun fuel _ k t z v => Bool.rec (motive := fun _ => Bool)
        (tst (pos t) l (Nat.sub (Nat.succ k) t) v
          (fun y => mv (prev fuel) l m g k t z v y)) true (Nat.ble v.length 1))) depth

def look1Marked (pick : Nat → Nat → Nat → List W → Bool) (l m g K : Nat) (depth : Nat) :
    Nat → Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → List W → Bool)
    (fun fuel k t z v => Bool.rec (motive := fun _ => Bool) false
      (look1 l m g K fuel k t z v) (pick k t z v))
    (fun depth prev => Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool)
      (fun _ _ _ _ => true)
      (fun fuel _ k t z v => Bool.rec (motive := fun _ => Bool)
        (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
          Bool.rec (motive := fun _ => Bool)
            (mv (lookMarked pick l m g depth K) l m g k t z v y) true
            (node (prev fuel (Nat.sub k 1) t) (pos t) l m g
              (Nat.sub (Nat.sub k t) y) v.length z v pairsS)))
        true (Nat.ble v.length 1))) depth
