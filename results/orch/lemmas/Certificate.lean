import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

namespace CoverCheck

abbrev M := BitVec 8

def raw : List M := [130, 132, 8, 16, 32, 64]
def profiles : List M := [154, 198, 180, 104]
def cells : List (M × M) :=
  [(154, 1), (198, 8), (180, 2), (104, 16), (154, 4), (154, 32), (154, 64), (198, 1), (198, 16), (198, 32), (180, 1), (180, 8), (180, 64), (104, 1), (104, 2), (104, 4), (104, 128)]

def hit (cell : M × M) (z : M) : Bool :=
  (cell.1 &&& z) == 0 && (cell.2 &&& z) != 0

def key (z : M) : M := if z.toNat ≤ (~~~z).toNat then z else ~~~z

lemma key_flip (z : M) : key (~~~z) = key z := by
  exact (show ∀ a : M, key (~~~a) = key a by decide +kernel) z

def seeds : List M := raw.map key
def lits (xs : List M) := xs ++ xs.map (fun z => ~~~z)
def products (xs : List M) := (lits xs).flatMap fun a =>
  (lits xs).map fun b => key (a &&& b)

def Builds : List M → List M → Prop
  | _, [] => True
  | xs, a :: tail => a ∈ products xs ∧ Builds (a :: xs) tail

def kNat (n : Nat) : Nat :=
  let nx := Nat.xor n 255
  bif Nat.ble n nx then n else nx

def seedsMask : Nat := (4295033088 ||| (2882303761517117441 <<< 64))

def bits128Aux : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | k + 1, m, acc =>
    bits128Aux k m (bif m.testBit k then k :: acc else acc)

def bits128 (m : Nat) : List Nat := bits128Aux 128 m []

def pair4 (a b : Nat) : Nat :=
  let na := Nat.xor a 255
  let nb := Nat.xor b 255
  let p1 := 1 <<< kNat (Nat.land a b)
  let p2 := 1 <<< kNat (Nat.land a nb)
  let p3 := 1 <<< kNat (Nat.land na b)
  let p4 := 1 <<< kNat (Nat.land na nb)
  Nat.lor (Nat.lor p1 p2) (Nat.lor p3 p4)

def prodPairs (a : Nat) : List Nat → Nat → Nat
  | [], pm => pm
  | b :: bs, pm => prodPairs a bs (Nat.lor pm (pair4 a b))

def prodAll : List Nat → List Nat → Nat → Nat
  | [], _, pm => pm
  | a :: as, allB, pm => prodAll as allB (prodPairs a allB pm)

def prodMask (m : Nat) : Nat :=
  let bs := bits128 m
  prodAll bs bs 0

def cachedProdMask (m : Nat) : Nat :=
  bif Nat.beq m seedsMask then (2882586340317266197 ||| (12261093970947408129 <<< 64)) else prodMask m

def fastWeCan (wanted : List Nat) : Nat → Nat → Bool
  | 0, m => (wanted.filter (fun q => !(m.testBit q))).isEmpty
  | k + 1, m =>
    let need := wanted.filter (fun q => !(m.testBit q))
    bif need.isEmpty then true
    else bif Nat.blt (k + 1) need.length then false
    else
      let pm := cachedProdMask m
      let cands := bif Nat.beq need.length (k + 1) then
        need.filter (fun q => pm.testBit q)
      else
        (bits128 pm).filter (fun q => !(m.testBit q))
      cands.any (fun q => fastWeCan wanted k (Nat.lor m (1 <<< q)))

def covMaskOf (z : Nat) : Nat :=
  bif Nat.ble 256 z then 0 else (bif Nat.blt z 128 then (bif Nat.blt z 64 then (bif Nat.blt z 32 then (bif Nat.blt z 16 then (bif Nat.blt z 8 then (bif Nat.blt z 4 then (bif Nat.blt z 2 then (bif Nat.blt z 1 then 0 else 9345) else (bif Nat.blt z 3 then 16388 else 25604)) else (bif Nat.blt z 6 then (bif Nat.blt z 5 then 32784 else 40977) else (bif Nat.blt z 7 then 49152 else 57344))) else (bif Nat.blt z 12 then (bif Nat.blt z 10 then (bif Nat.blt z 9 then 2050 else 3202) else (bif Nat.blt z 11 then 2052 else 3076)) else 0)) else (bif Nat.blt z 24 then (bif Nat.blt z 20 then (bif Nat.blt z 18 then (bif Nat.blt z 17 then 264 else 8584) else (bif Nat.blt z 19 then 16392 else 24584)) else (bif Nat.blt z 22 then (bif Nat.blt z 21 then 32776 else 40968) else (bif Nat.blt z 23 then 49160 else 57352))) else (bif Nat.blt z 28 then (bif Nat.blt z 26 then (bif Nat.blt z 25 then 258 else 386) else 0) else 0))) else (bif Nat.blt z 48 then (bif Nat.blt z 40 then (bif Nat.blt z 36 then (bif Nat.blt z 34 then (bif Nat.blt z 33 then 544 else 673) else 0) else (bif Nat.blt z 38 then (bif Nat.blt z 37 then 48 else 49) else 0)) else (bif Nat.blt z 44 then (bif Nat.blt z 42 then (bif Nat.blt z 41 then 514 else 642) else 0) else 0)) else (bif Nat.blt z 56 then (bif Nat.blt z 52 then (bif Nat.blt z 50 then (bif Nat.blt z 49 then 768 else 896) else 0) else 0) else (bif Nat.blt z 60 then (bif Nat.blt z 58 then (bif Nat.blt z 57 then 770 else 898) else 0) else 0)))) else (bif Nat.blt z 96 then (bif Nat.blt z 80 then (bif Nat.blt z 72 then (bif Nat.blt z 68 then (bif Nat.blt z 66 then (bif Nat.blt z 65 then 4160 else 5185) else (bif Nat.blt z 67 then 4100 else 5124)) else (bif Nat.blt z 70 then (bif Nat.blt z 69 then 80 else 81) else 0)) else (bif Nat.blt z 76 then (bif Nat.blt z 74 then (bif Nat.blt z 73 then 6144 else 7168) else (bif Nat.blt z 75 then 6148 else 7172)) else 0)) else 0) else (bif Nat.blt z 112 then (bif Nat.blt z 104 then (bif Nat.blt z 100 then (bif Nat.blt z 98 then (bif Nat.blt z 97 then 96 else 97) else 0) else (bif Nat.blt z 102 then (bif Nat.blt z 101 then 112 else 113) else 0)) else 0) else 0))) else (bif Nat.blt z 192 then (bif Nat.blt z 160 then (bif Nat.blt z 144 then (bif Nat.blt z 136 then (bif Nat.blt z 132 then (bif Nat.blt z 130 then (bif Nat.blt z 129 then 65536 else 73728) else (bif Nat.blt z 131 then 81920 else 90112)) else (bif Nat.blt z 134 then (bif Nat.blt z 133 then 98304 else 106496) else (bif Nat.blt z 135 then 114688 else 122880))) else 0) else (bif Nat.blt z 152 then (bif Nat.blt z 148 then (bif Nat.blt z 146 then (bif Nat.blt z 145 then 65544 else 73736) else (bif Nat.blt z 147 then 81928 else 90120)) else (bif Nat.blt z 150 then (bif Nat.blt z 149 then 98312 else 106504) else (bif Nat.blt z 151 then 114696 else 122888))) else 0)) else 0) else 0))

-- Canonical product key and the cells covered by a candidate block.
def coverOptions : Nat → List (Nat × Nat)
  | 0 => [(1, 9345), (5, 40977), (33, 673), (37, 49), (65, 5185), (69, 81), (97, 97), (101, 113)]
  | 1 => [(8, 2050), (9, 3202), (24, 258), (25, 386), (40, 514), (41, 642), (56, 770), (57, 898)]
  | 2 => [(2, 16388), (3, 25604), (10, 2052), (11, 3076), (66, 4100), (67, 5124), (74, 6148), (75, 7172)]
  | 3 => [(16, 264), (17, 8584), (18, 16392), (19, 24584), (20, 32776), (21, 40968), (22, 49160), (23, 57352), (111, 65544), (110, 73736), (109, 81928), (108, 90120), (107, 98312), (106, 106504), (105, 114696), (104, 122888)]
  | 4 => [(4, 32784), (5, 40977), (36, 48), (37, 49), (68, 80), (69, 81), (100, 112), (101, 113)]
  | 5 => [(32, 544), (33, 673), (36, 48), (37, 49), (96, 96), (97, 97), (100, 112), (101, 113)]
  | 6 => [(64, 4160), (65, 5185), (68, 80), (69, 81), (96, 96), (97, 97), (100, 112), (101, 113)]
  | 7 => [(1, 9345), (9, 3202), (17, 8584), (25, 386), (33, 673), (41, 642), (49, 896), (57, 898)]
  | 8 => [(16, 264), (17, 8584), (24, 258), (25, 386), (48, 768), (49, 896), (56, 770), (57, 898)]
  | 9 => [(32, 544), (33, 673), (40, 514), (41, 642), (48, 768), (49, 896), (56, 770), (57, 898)]
  | 10 => [(1, 9345), (3, 25604), (9, 3202), (11, 3076), (65, 5185), (67, 5124), (73, 7168), (75, 7172)]
  | 11 => [(8, 2050), (9, 3202), (10, 2052), (11, 3076), (72, 6144), (73, 7168), (74, 6148), (75, 7172)]
  | 12 => [(64, 4160), (65, 5185), (66, 4100), (67, 5124), (72, 6144), (73, 7168), (74, 6148), (75, 7172)]
  | 13 => [(1, 9345), (3, 25604), (5, 40977), (7, 57344), (17, 8584), (19, 24584), (21, 40968), (23, 57352), (126, 73728), (124, 90112), (122, 106496), (120, 122880), (110, 73736), (108, 90120), (106, 106504), (104, 122888)]
  | 14 => [(2, 16388), (3, 25604), (6, 49152), (7, 57344), (18, 16392), (19, 24584), (22, 49160), (23, 57352), (125, 81920), (124, 90112), (121, 114688), (120, 122880), (109, 81928), (108, 90120), (105, 114696), (104, 122888)]
  | 15 => [(4, 32784), (5, 40977), (6, 49152), (7, 57344), (20, 32776), (21, 40968), (22, 49160), (23, 57352), (123, 98304), (122, 106496), (121, 114688), (120, 122880), (107, 98312), (106, 106504), (105, 114696), (104, 122888)]
  | 16 => [(127, 65536), (126, 73728), (125, 81920), (124, 90112), (123, 98304), (122, 106496), (121, 114688), (120, 122880), (111, 65544), (110, 73736), (109, 81928), (108, 90120), (107, 98312), (106, 106504), (105, 114696), (104, 122888)]
  | _ => []

def firstUncovAux : Nat → Nat → Nat → Nat
  | 0, _, i => i
  | r + 1, cov, i => bif cov.testBit i then firstUncovAux r cov (i + 1) else i

def preferUncovered (cov : Nat) : List (Fin 17) → Nat
  | [] => firstUncovAux 17 cov 0
  | i :: rest => bif cov.testBit i.val then preferUncovered cov rest else i.val

def firstUncov (cov : Nat) : Nat :=
  preferUncovered cov [0, 1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 3, 13, 14, 15, 16]

def remLb4 (cov : Nat) : Nat :=
  (bif cov.testBit 0 then 0 else 1) +
  (bif cov.testBit 1 then 0 else 1) +
  (bif cov.testBit 2 then 0 else 1) +
  (bif cov.testBit 3 then 0 else 1)

def remLb (cov : Nat) : Nat :=
  let s := remLb4 cov
  bif Nat.beq s 0 then (bif Nat.beq cov 131071 then 0 else 1) else s

-- Pass a computed coverage mask to each recursive call.
def forceMask (n : Nat) (f : Nat → Bool) : Bool :=
  match n with
  | 0 => f 0
  | k + 1 => f (k + 1)

lemma forceMask_eq (n : Nat) (f : Nat → Bool) : forceMask n f = f n := by
  cases n <;> rfl

def forceWanted (xs : List Nat) (f : List Nat → Bool) : Bool :=
  match xs with
  | [] => f []
  | x :: rest => f (x :: rest)

lemma forceWanted_eq (xs : List Nat) (f : List Nat → Bool) :
    forceWanted xs f = f xs := by
  cases xs <;> rfl

def fastSolve : Nat → Nat → Nat → List Nat → Bool
  | 0, chLen, cov, wanted =>
    !(Nat.blt 11 (chLen + wanted.length)) &&
      Nat.beq cov 131071 && fastWeCan wanted (11 - chLen) seedsMask
  | k + 1, chLen, cov, wanted =>
    bif Nat.blt 11 (chLen + remLb cov + wanted.length) then false
    else bif Nat.beq cov 131071 then fastWeCan wanted (11 - chLen) seedsMask
    else
      let idx := firstUncov cov
      (coverOptions idx).any fun (kz, covered) =>
        let w2 := bif seedsMask.testBit kz || wanted.contains kz then wanted else kz :: wanted
        forceMask (Nat.lor cov covered) (fun c => forceWanted w2 (fastSolve k (chLen + 1) c))

lemma nat_blt_false {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  rw [Bool.eq_false_iff]
  intro ht
  rw [Nat.blt_eq] at ht
  omega

lemma nat_beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  rw [Bool.eq_false_iff]
  intro ht
  exact h (Nat.beq_eq.mp ht)

lemma nat_beq_false_ne {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  rintro rfl
  simp at h

lemma key_spec : ∀ z : M,
    (key z).toNat = kNat z.toNat ∧ (key z).toNat < 128 ∧ (~~~z).toNat = Nat.xor z.toNat 255 := by
  decide +kernel

lemma seeds_spec : ∀ a ∈ seeds, a.toNat < 128 ∧ seedsMask.testBit a.toNat = true := by decide +kernel

lemma covMaskOf_lt : ∀ z : M, covMaskOf z.toNat < 2 ^ 17 := by decide +kernel

lemma covMaskOf_spec : ∀ (z : M) (i : Fin 17),
    (covMaskOf z.toNat).testBit i.val = hit (cells.getD i.val (0, 0)) z := by decide +kernel

lemma coverOptions_spec : ∀ (i : Fin 17) (z : M),
    hit (cells.getD i.val (0, 0)) z = true →
    (kNat z.toNat, covMaskOf z.toNat) ∈ coverOptions i.val := by decide +kernel

lemma disj4_spec : ∀ (z : M) (i j : Fin 4),
    hit (cells.getD i.val (0, 0)) z = true →
    hit (cells.getD j.val (0, 0)) z = true → i = j := by decide +kernel

lemma testBit_one_shift_self (q : Nat) : (1 <<< q).testBit q = true := by
  simp

lemma pair4_spec (u v : M) :
    (pair4 u.toNat v.toNat).testBit (key (u &&& v)).toNat = true ∧
    (pair4 u.toNat v.toNat).testBit (key (u &&& ~~~v)).toNat = true ∧
    (pair4 u.toNat v.toNat).testBit (key (~~~u &&& v)).toNat = true ∧
    (pair4 u.toNat v.toNat).testBit (key (~~~u &&& ~~~v)).toNat = true := by
  have e1 : (key (u &&& v)).toNat = kNat (Nat.land u.toNat v.toNat) := by
    rw [(key_spec (u &&& v)).1, BitVec.toNat_and, Nat.land_eq]
  have e2 : (key (u &&& ~~~v)).toNat = kNat (Nat.land u.toNat (Nat.xor v.toNat 255)) := by
    rw [(key_spec (u &&& ~~~v)).1, BitVec.toNat_and, (key_spec v).2.2, Nat.land_eq]
  have e3 : (key (~~~u &&& v)).toNat = kNat (Nat.land (Nat.xor u.toNat 255) v.toNat) := by
    rw [(key_spec (~~~u &&& v)).1, BitVec.toNat_and, (key_spec u).2.2, Nat.land_eq]
  have e4 : (key (~~~u &&& ~~~v)).toNat = kNat (Nat.land (Nat.xor u.toNat 255) (Nat.xor v.toNat 255)) := by
    rw [(key_spec (~~~u &&& ~~~v)).1, BitVec.toNat_and, (key_spec u).2.2, (key_spec v).2.2, Nat.land_eq]
  unfold pair4
  simp only [Nat.lor_eq, Nat.testBit_or, e1, e2, e3, e4, testBit_one_shift_self,
    Bool.true_or, Bool.or_true, and_self]

lemma mem_bits128Aux (n m : Nat) (acc : List Nat) (q : Nat) :
    q ∈ bits128Aux n m acc ↔ q ∈ acc ∨ (q < n ∧ m.testBit q = true) := by
  induction n generalizing acc with
  | zero => simp [bits128Aux]
  | succ k ih =>
    rw [bits128Aux, ih]
    cases h : m.testBit k
    · simp only [Bool.cond_false]
      constructor
      · rintro (hq | ⟨hq1, hq2⟩)
        · exact Or.inl hq
        · exact Or.inr ⟨by omega, hq2⟩
      · rintro (hq | ⟨hq1, hq2⟩)
        · exact Or.inl hq
        · have hne : q ≠ k := fun e => by rw [e, h] at hq2; cases hq2
          exact Or.inr ⟨by omega, hq2⟩
    · simp only [Bool.cond_true, List.mem_cons]
      constructor
      · rintro ((rfl | hq) | ⟨hq1, hq2⟩)
        · exact Or.inr ⟨by omega, h⟩
        · exact Or.inl hq
        · exact Or.inr ⟨by omega, hq2⟩
      · rintro (hq | ⟨hq1, hq2⟩)
        · exact Or.inl (Or.inr hq)
        · by_cases he : q = k
          · exact Or.inl (Or.inl he)
          · exact Or.inr ⟨by omega, hq2⟩

lemma mem_bits128 (m q : Nat) : q ∈ bits128 m ↔ q < 128 ∧ m.testBit q = true := by
  simpa [bits128] using mem_bits128Aux 128 m [] q

lemma prodPairs_mono (a : Nat) (bs : List Nat) (pm q : Nat) (h : pm.testBit q = true) :
    (prodPairs a bs pm).testBit q = true := by
  induction bs generalizing pm with
  | nil => exact h
  | cons b bs ih =>
    apply ih
    simp [Nat.lor_eq, h]

lemma prodPairs_mem (a b : Nat) (bs : List Nat) (hb : b ∈ bs) (pm q : Nat)
    (h : (pair4 a b).testBit q = true) : (prodPairs a bs pm).testBit q = true := by
  induction bs generalizing pm with
  | nil => cases hb
  | cons x bs ih =>
    simp only [prodPairs]
    rcases List.mem_cons.mp hb with rfl | hmem
    · apply prodPairs_mono
      simp [Nat.lor_eq, h]
    · exact ih hmem _

lemma prodAll_mono (as allB : List Nat) (pm q : Nat) (h : pm.testBit q = true) :
    (prodAll as allB pm).testBit q = true := by
  induction as generalizing pm with
  | nil => exact h
  | cons a as ih => exact ih _ (prodPairs_mono a allB pm q h)

lemma prodAll_mem (a b : Nat) (as allB : List Nat) (ha : a ∈ as) (hb : b ∈ allB) (pm q : Nat)
    (h : (pair4 a b).testBit q = true) : (prodAll as allB pm).testBit q = true := by
  induction as generalizing pm with
  | nil => cases ha
  | cons x as ih =>
    simp only [prodAll]
    rcases List.mem_cons.mp ha with rfl | hmem
    · exact prodAll_mono as allB _ q (prodPairs_mem a b allB hb pm q h)
    · exact ih hmem _

lemma prodMask_of_products {xs : List M} {m : Nat}
    (hxs : ∀ x ∈ xs, x.toNat < 128 ∧ m.testBit x.toNat = true)
    {a : M} (ha : a ∈ products xs) :
    a.toNat < 128 ∧ (prodMask m).testBit a.toNat = true := by
  unfold products at ha
  rw [List.mem_flatMap] at ha
  obtain ⟨x, hx, hy⟩ := ha
  rw [List.mem_map] at hy
  obtain ⟨y, hy, rfl⟩ := hy
  refine ⟨(key_spec (x &&& y)).2.1, ?_⟩
  unfold lits at hx hy
  rw [List.mem_append, List.mem_map] at hx hy
  have memB (u : M) (hu : u ∈ xs) : u.toNat ∈ bits128 m :=
    (mem_bits128 m u.toNat).mpr (hxs u hu)
  rcases hx with ux | ⟨u, ux, rfl⟩ <;> rcases hy with vy | ⟨v, vy, rfl⟩
  · exact prodAll_mem _ _ _ _ (memB x ux) (memB y vy) 0 _ (pair4_spec x y).1
  · exact prodAll_mem _ _ _ _ (memB x ux) (memB v vy) 0 _ (pair4_spec x v).2.1
  · exact prodAll_mem _ _ _ _ (memB u ux) (memB y vy) 0 _ (pair4_spec u y).2.2.1
  · exact prodAll_mem _ _ _ _ (memB u ux) (memB v vy) 0 _ (pair4_spec u v).2.2.2

lemma cachedProdMask_eq (m : Nat) : cachedProdMask m = prodMask m := by
  by_cases h : m = seedsMask
  · subst m
    decide +kernel
  · simp only [cachedProdMask, nat_beq_false h, Bool.cond_false]

lemma need_len_le {wanted : List Nat} {m : Nat} {tail : List M}
    (hnd : wanted.Nodup)
    (hall : ∀ q ∈ wanted, m.testBit q = true ∨ q ∈ tail.map BitVec.toNat) :
    (wanted.filter (fun q => !(m.testBit q))).length ≤ tail.length := by
  let need := wanted.filter (fun q => !(m.testBit q))
  have nd_need : need.Nodup := hnd.filter _
  have sub : need.toFinset ⊆ (tail.map BitVec.toNat).toFinset := by
    intro q hq
    have hm := List.mem_filter.mp (List.mem_toFinset.mp hq)
    have hmf : m.testBit q = false := by simpa using hm.2
    exact List.mem_toFinset.mpr ((hall q hm.1).resolve_left (by simp [hmf]))
  calc need.length
    _ = need.toFinset.card := (List.toFinset_card_of_nodup nd_need).symm
    _ ≤ (tail.map BitVec.toNat).toFinset.card := Finset.card_le_card sub
    _ ≤ (tail.map BitVec.toNat).length := List.toFinset_card_le _
    _ = tail.length := List.length_map _

lemma fastWeCan_ok {wanted : List Nat} (hnd : wanted.Nodup) {xs tail : List M} {fuel m : Nat}
    (hrun : Builds xs tail)
    (hxs : ∀ x ∈ xs, x.toNat < 128 ∧ m.testBit x.toNat = true)
    (hsmall : tail.length ≤ fuel)
    (hall : ∀ q ∈ wanted, m.testBit q = true ∨ q ∈ tail.map BitVec.toNat) :
    fastWeCan wanted fuel m = true := by
  induction tail generalizing fuel xs m with
  | nil =>
    have hemp : (wanted.filter (fun q => !(m.testBit q))).isEmpty = true := by
      rw [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
      intro q hq
      have hm := List.mem_filter.mp hq
      have h1 := hall q hm.1
      simp at h1
      simp [h1] at hm
    cases fuel with
    | zero => simp [fastWeCan, hemp]
    | succ k => simp [fastWeCan, hemp]
  | cons a rest ih =>
    obtain ⟨hprod, hrest⟩ := hrun
    obtain ⟨halt64, hpm⟩ := prodMask_of_products hxs hprod
    by_cases halr : m.testBit a.toNat = true
    · apply ih (xs := a :: xs) hrest
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨halt64, halr⟩
        · exact hxs x hx
      · exact Nat.le_trans (Nat.le_succ _) hsmall
      · intro q hq
        rcases hall q hq with h | h
        · exact Or.inl h
        · simp only [List.map_cons, List.mem_cons] at h
          rcases h with rfl | h
          · exact Or.inl halr
          · exact Or.inr h
    · have halrf : m.testBit a.toNat = false := Bool.eq_false_iff.mpr halr
      cases fuel with
      | zero => simp at hsmall
      | succ k =>
        have hlen : (wanted.filter (fun q => !(m.testBit q))).length ≤ k + 1 :=
          (need_len_le hnd hall).trans hsmall
        rw [fastWeCan, cachedProdMask_eq]
        cases hemp : (wanted.filter (fun q => !(m.testBit q))).isEmpty
        · simp only [Bool.cond_false]
          have hblt : Nat.blt (k + 1) (wanted.filter (fun q => !(m.testBit q))).length = false :=
            nat_blt_false hlen
          rw [hblt]; simp only [Bool.cond_false]
          let m2 := Nat.lor m (1 <<< a.toNat)
          have hm2_self : m2.testBit a.toNat = true := by
            simp [m2, Nat.lor_eq]
          have hm2_mono : ∀ r, m.testBit r = true → m2.testBit r = true := by
            intro r hr; simp [m2, Nat.lor_eq, hr]
          have hrec : fastWeCan wanted k m2 = true := by
            apply ih (xs := a :: xs) hrest
            · intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact ⟨halt64, hm2_self⟩
              · exact ⟨(hxs x hx).1, hm2_mono _ (hxs x hx).2⟩
            · simp only [List.length_cons] at hsmall; omega
            · intro q hq
              rcases hall q hq with h | h
              · exact Or.inl (hm2_mono q h)
              · simp only [List.map_cons, List.mem_cons] at h
                rcases h with rfl | h
                · exact Or.inl hm2_self
                · exact Or.inr h
          apply List.any_eq_true.mpr
          refine ⟨a.toNat, ?_, hrec⟩
          cases hbeq : Nat.beq (wanted.filter (fun q => !(m.testBit q))).length (k + 1)
          · simp only [Bool.cond_false, List.mem_filter, mem_bits128]
            exact ⟨⟨halt64, hpm⟩, by simp [halrf]⟩
          · simp only [Bool.cond_true, List.mem_filter]
            have heq_len : (wanted.filter (fun q => !(m.testBit q))).length = k + 1 :=
              Nat.beq_eq.mp hbeq
            refine ⟨?_, hpm⟩
            by_contra hnot_need
            have hnot_w : a.toNat ∉ wanted := by
              intro hw
              exact hnot_need ⟨hw, by simp [halrf]⟩
            have hle_rest : (wanted.filter (fun q => !(m.testBit q))).length ≤ rest.length := by
              apply need_len_le hnd
              intro q hq
              rcases hall q hq with h | h
              · exact Or.inl h
              · simp only [List.map_cons, List.mem_cons] at h
                rcases h with rfl | h
                · exact False.elim (hnot_w hq)
                · exact Or.inr h
            simp only [List.length_cons] at hsmall
            omega
        · rfl

lemma firstUncovAux_spec (r cov i : Nat)
    (hprev : ∀ j < i, cov.testBit j = true) :
    (firstUncovAux r cov i < i + r ∧ cov.testBit (firstUncovAux r cov i) = false) ∨
      (firstUncovAux r cov i = i + r ∧ ∀ j < i + r, cov.testBit j = true) := by
  induction r generalizing i with
  | zero =>
    exact Or.inr ⟨by simp [firstUncovAux], by simpa using hprev⟩
  | succ r ih =>
    rw [firstUncovAux]
    cases h : cov.testBit i
    · simp only [Bool.cond_false]
      exact Or.inl ⟨by omega, h⟩
    · simp only [Bool.cond_true]
      have hprev' : ∀ j < i + 1, cov.testBit j = true := by
        intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
        · exact hprev j hlt
        · exact h
      rcases ih (i + 1) hprev' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by omega, h2⟩
      · exact Or.inr ⟨by omega, fun j hj => h2 j (by omega)⟩

lemma all_bits_15_eq {cov : Nat} (hlt : cov < 2 ^ 17)
    (hall : ∀ j < 17, cov.testBit j = true) : cov = 131071 := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 17
  · rw [hall j hj]
    have h32 : (131071 : Nat) = 2 ^ 17 - 1 := rfl
    rw [h32, Nat.testBit_two_pow_sub_one]
    simp [hj]
  · have hge : 17 ≤ j := by omega
    have h1 : cov.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hge))
    have h32lt : (131071 : Nat) < 2 ^ 17 := by decide
    have h2 : (131071 : Nat).testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h32lt (Nat.pow_le_pow_right (by omega) hge))
    rw [h1, h2]

lemma firstUncov_spec {cov : Nat} (hlt : cov < 2 ^ 17) (hne : cov ≠ 131071) :
    firstUncov cov < 17 ∧ cov.testBit (firstUncov cov) = false := by
  suffices ∀ order : List (Fin 17),
      preferUncovered cov order < 17 ∧ cov.testBit (preferUncovered cov order) = false from this _
  intro order
  induction order with
  | nil =>
    change firstUncovAux 17 cov 0 < 17 ∧ cov.testBit (firstUncovAux 17 cov 0) = false
    rcases firstUncovAux_spec 17 cov 0 (fun _ hj => by omega) with ⟨h1, h2⟩ | ⟨_, h2⟩
    · simp only [Nat.zero_add] at h1
      exact ⟨h1, h2⟩
    · simp only [Nat.zero_add] at h2
      exact False.elim (hne (all_bits_15_eq hlt h2))
  | cons i rest ih =>
    cases hi : cov.testBit i.val
    · simpa only [preferUncovered, hi, Bool.cond_false] using And.intro i.isLt hi
    · simpa only [preferUncovered, hi, Bool.cond_true] using ih

lemma remLb4_le_sdiff {blocks chosen : List M} {cov : Nat}
    (hcov : ∀ i : Fin 17, cov.testBit i.val = chosen.any (hit (cells.getD i.val (0, 0))))
    (hcover : ∀ c ∈ cells, ∃ z ∈ blocks, hit c z = true) :
    remLb4 cov ≤ (blocks.toFinset \ chosen.toFinset).card := by
  classical
  let U : Finset (Fin 4) := Finset.univ.filter (fun j : Fin 4 => !(cov.testBit j.val))
  have hU_card : U.card = remLb4 cov := by
    have heq : U.card = ∑ j : Fin 4, if !(cov.testBit j.val) then 1 else 0 := by
      rw [Finset.card_filter]
    rw [heq, Fin.sum_univ_four]
    have v0 : ((0 : Fin 4) : Nat) = 0 := rfl
    have v1 : ((1 : Fin 4) : Nat) = 1 := rfl
    have v2 : ((2 : Fin 4) : Nat) = 2 := rfl
    have v3 : ((3 : Fin 4) : Nat) = 3 := rfl
    rw [v0, v1, v2, v3]
    unfold remLb4
    cases cov.testBit 0 <;> cases cov.testBit 1 <;> cases cov.testBit 2 <;> cases cov.testBit 3 <;> simp
  have hex : ∀ j : Fin 4,
      ∃ z : M, j ∈ U → z ∈ blocks.toFinset \ chosen.toFinset ∧ hit (cells.getD j.val (0, 0)) z = true := by
    intro j
    by_cases hj : j ∈ U
    · have hbit : cov.testBit j.val = false := by
        have hm := (Finset.mem_filter.mp hj).2
        simpa using hm
      have hc_mem : cells.getD j.val (0, 0) ∈ cells := by
        have hlt : j.val < cells.length := by have := j.isLt; simp [cells]; omega
        rw [List.getD_eq_getElem _ _ hlt]
        exact List.getElem_mem hlt
      obtain ⟨z, hzB, hhit⟩ := hcover _ hc_mem
      have hzNotC : z ∉ chosen := by
        intro hzC
        have hany : chosen.any (hit (cells.getD j.val (0, 0))) = true :=
          List.any_eq_true.mpr ⟨z, hzC, hhit⟩
        have hcv := hcov ⟨j.val, by omega⟩
        change cov.testBit j.val = chosen.any (hit (cells.getD j.val (0, 0))) at hcv
        rw [hbit, hany] at hcv
        cases hcv
      exact ⟨z, fun _ => ⟨Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hzB, by simpa using hzNotC⟩, hhit⟩⟩
    · exact ⟨0, fun h => (hj h).elim⟩
  choose f hf using hex
  rw [← hU_card]
  exact Finset.card_le_card_of_injOn f
    (fun j hj => Finset.mem_coe.mpr (hf j (Finset.mem_coe.mp hj)).1)
    (fun j1 hj1 j2 hj2 heq => by
      have h1 := (hf j1 (Finset.mem_coe.mp hj1)).2
      have h2 := (hf j2 (Finset.mem_coe.mp hj2)).2
      rw [← heq] at h2
      exact disj4_spec (f j1) j1 j2 h1 h2)

lemma remLb_bound {blocks chosen : List M} {cov : Nat}
    (hnd : chosen.Nodup)
    (hsub : ∀ z ∈ chosen, z ∈ blocks)
    (hlt : cov < 2 ^ 17)
    (hcov : ∀ i : Fin 17, cov.testBit i.val = chosen.any (hit (cells.getD i.val (0, 0))))
    (hcover : ∀ c ∈ cells, ∃ z ∈ blocks, hit c z = true) :
    chosen.length + remLb cov ≤ blocks.length := by
  classical
  have hsubF : chosen.toFinset ⊆ blocks.toFinset := by
    intro z hz; exact List.mem_toFinset.mpr (hsub z (List.mem_toFinset.mp hz))
  have hcardC : chosen.toFinset.card = chosen.length := List.toFinset_card_of_nodup hnd
  have hcardB : blocks.toFinset.card ≤ blocks.length := List.toFinset_card_le blocks
  have hsplit : (blocks.toFinset \ chosen.toFinset).card + chosen.toFinset.card = blocks.toFinset.card :=
    Finset.card_sdiff_add_card_eq_card hsubF
  unfold remLb
  dsimp only
  cases hs : Nat.beq (remLb4 cov) 0
  · change chosen.length + remLb4 cov ≤ blocks.length
    have h4 := remLb4_le_sdiff hcov hcover
    omega
  · cases hc : Nat.beq cov 131071
    · change chosen.length + 1 ≤ blocks.length
      have hne : cov ≠ 131071 := nat_beq_false_ne hc
      obtain ⟨idx_lt, hbit⟩ := firstUncov_spec hlt hne
      let i15 : Fin 17 := ⟨firstUncov cov, idx_lt⟩
      have hc_mem : cells.getD i15.val (0, 0) ∈ cells := by
        have hltC : i15.val < cells.length := by simp [cells, i15, idx_lt]
        rw [List.getD_eq_getElem _ _ hltC]
        exact List.getElem_mem hltC
      obtain ⟨z, hzB, hhit⟩ := hcover _ hc_mem
      have hzNotC : z ∉ chosen := by
        intro hzC
        have hany : chosen.any (hit (cells.getD i15.val (0, 0))) = true :=
          List.any_eq_true.mpr ⟨z, hzC, hhit⟩
        have hcv := hcov i15
        change cov.testBit (firstUncov cov) = chosen.any (hit (cells.getD i15.val (0, 0))) at hcv
        rw [hbit, hany] at hcv
        cases hcv
      have hpos : 1 ≤ (blocks.toFinset \ chosen.toFinset).card :=
        Finset.card_pos.mpr ⟨z, Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr hzB, by simpa using hzNotC⟩⟩
      omega
    · change chosen.length + 0 ≤ blocks.length
      omega

lemma fastSolve_ok {tail blocks : List M}
    (hrun : Builds seeds tail)
    (hbound : tail.length + blocks.length ≤ 11)
    (hattain : ∀ z ∈ blocks, key z ∈ seeds ∨ key z ∈ tail)
    (hcover : ∀ c ∈ cells, ∃ z ∈ blocks, hit c z = true) :
    ∀ (fuel : Nat) (chosen : List M) (cov : Nat) (wanted : List Nat),
      chosen.Nodup →
      (∀ z ∈ chosen, z ∈ blocks) →
      cov < 2 ^ 17 →
      (∀ i : Fin 17, cov.testBit i.val = chosen.any (hit (cells.getD i.val (0, 0)))) →
      wanted.Nodup →
      (∀ q ∈ wanted, seedsMask.testBit q = false ∧ q ∈ tail.map BitVec.toNat) →
      blocks.length ≤ fuel + chosen.length →
      fastSolve fuel chosen.length cov wanted = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro chosen cov wanted hndC hsubC hltC hcov hndW hwSpec henough
    have hrem := remLb_bound hndC hsubC hltC hcov hcover
    have hrem0 : remLb cov = 0 := by omega
    have hcov_eq : cov = 131071 := by
      by_contra hne
      unfold remLb at hrem0
      dsimp only at hrem0
      cases hs : Nat.beq (remLb4 cov) 0
      · rw [hs] at hrem0
        change remLb4 cov = 0 at hrem0
        exact nat_beq_false_ne hs hrem0
      · have hc : Nat.beq cov 131071 = false := nat_beq_false hne
        rw [hs, hc] at hrem0
        cases hrem0
    have hw_len : wanted.length ≤ tail.length := by
      have := need_len_le hndW (m := seedsMask) (tail := tail) (fun q hq => Or.inr (hwSpec q hq).2)
      have heq_f : wanted.filter (fun q => !(seedsMask.testBit q)) = wanted :=
        List.filter_eq_self.mpr (fun q hq => by simp [(hwSpec q hq).1])
      rwa [heq_f] at this
    have hwe : fastWeCan wanted (11 - chosen.length) seedsMask = true :=
      fastWeCan_ok hndW hrun seeds_spec (by omega) (fun q hq => Or.inr (hwSpec q hq).2)
    have hblt : Nat.blt 11 (chosen.length + wanted.length) = false :=
      nat_blt_false (by omega)
    simp [fastSolve, hblt, hcov_eq, hwe]
  | succ k ih =>
    intro chosen cov wanted hndC hsubC hltC hcov hndW hwSpec henough
    have hrem := remLb_bound hndC hsubC hltC hcov hcover
    have hw_len : wanted.length ≤ tail.length := by
      have := need_len_le hndW (m := seedsMask) (tail := tail) (fun q hq => Or.inr (hwSpec q hq).2)
      have heq_f : wanted.filter (fun q => !(seedsMask.testBit q)) = wanted :=
        List.filter_eq_self.mpr (fun q hq => by simp [(hwSpec q hq).1])
      rwa [heq_f] at this
    have hblt : Nat.blt 11 (chosen.length + remLb cov + wanted.length) = false :=
      nat_blt_false (by omega)
    rw [fastSolve, hblt]
    simp only [forceMask_eq, forceWanted_eq]
    simp only [Bool.cond_false]
    by_cases hcov_eq : cov = 131071
    · subst hcov_eq
      simp only [Nat.beq_refl, Bool.cond_true]
      exact fastWeCan_ok hndW hrun seeds_spec (by omega) (fun q hq => Or.inr (hwSpec q hq).2)
    · have hc : Nat.beq cov 131071 = false := nat_beq_false hcov_eq
      rw [hc]
      simp only [Bool.cond_false]
      obtain ⟨idx_lt, hbit⟩ := firstUncov_spec hltC hcov_eq
      let i15 : Fin 17 := ⟨firstUncov cov, idx_lt⟩
      have hc_mem : cells.getD i15.val (0, 0) ∈ cells := by
        have hltL : i15.val < cells.length := by simp [cells, i15, idx_lt]
        rw [List.getD_eq_getElem _ _ hltL]
        exact List.getElem_mem hltL
      obtain ⟨z, hzB, hhit⟩ := hcover _ hc_mem
      have hzNotC : z ∉ chosen := by
        intro hzC
        have hany : chosen.any (hit (cells.getD i15.val (0, 0))) = true :=
          List.any_eq_true.mpr ⟨z, hzC, hhit⟩
        have hcv := hcov i15
        change cov.testBit (firstUncov cov) = chosen.any (hit (cells.getD i15.val (0, 0))) at hcv
        rw [hbit, hany] at hcv
        cases hcv
      apply List.any_eq_true.mpr
      refine ⟨(kNat z.toNat, covMaskOf z.toNat), coverOptions_spec i15 z hhit, ?_⟩
      let kz := kNat z.toNat
      have hkz_eq : (key z).toNat = kz := (key_spec z).1
      let w2 := bif seedsMask.testBit kz || wanted.contains kz then wanted else kz :: wanted
      have hw2_nd : w2.Nodup := by
        dsimp only [w2]
        cases hb : (seedsMask.testBit kz || wanted.contains kz)
        · simp only [Bool.cond_false]
          have hnotW : kz ∉ wanted := by
            intro hm
            have hc1 : wanted.contains kz = true := List.contains_iff_mem.mpr hm
            rw [hc1, Bool.or_true] at hb
            cases hb
          exact List.nodup_cons.mpr ⟨hnotW, hndW⟩
        · simp only [Bool.cond_true]; exact hndW
      have hw2_spec : ∀ q ∈ w2, seedsMask.testBit q = false ∧ q ∈ tail.map BitVec.toNat := by
        dsimp only [w2]
        cases hb : (seedsMask.testBit kz || wanted.contains kz)
        · simp only [Bool.cond_false, List.mem_cons]
          have hsF : seedsMask.testBit kz = false := by
            cases h1 : seedsMask.testBit kz
            · rfl
            · rw [h1, Bool.true_or] at hb; cases hb
          have hinT : kz ∈ tail.map BitVec.toNat := by
            rcases hattain z hzB with hseed | htail
            · have hsT := (seeds_spec (key z) hseed).2
              rw [hkz_eq, hsF] at hsT; cases hsT
            · rw [← hkz_eq]
              exact List.mem_map_of_mem htail
          rintro q (rfl | hq)
          · exact ⟨hsF, hinT⟩
          · exact hwSpec q hq
        · simp only [Bool.cond_true]; exact hwSpec
      have hcov2_lt : Nat.lor cov (covMaskOf z.toNat) < 2 ^ 17 := by
        rw [Nat.lor_eq]
        exact Nat.or_lt_two_pow hltC (covMaskOf_lt z)
      have hcov2_spec : ∀ i : Fin 17,
          (Nat.lor cov (covMaskOf z.toNat)).testBit i.val =
            (z :: chosen).any (hit (cells.getD i.val (0, 0))) := by
        intro i
        rw [Nat.lor_eq, Nat.testBit_or, hcov i, covMaskOf_spec z i, List.any_cons, Bool.or_comm]
      have hrec := ih (z :: chosen) (Nat.lor cov (covMaskOf z.toNat)) w2
        (List.nodup_cons.mpr ⟨hzNotC, hndC⟩)
        (fun x hx => (List.mem_cons.mp hx).elim (fun e => e ▸ hzB) (hsubC x))
        hcov2_lt hcov2_spec hw2_nd hw2_spec (by simp; omega)
      simpa only [List.length_cons] using hrec

set_option maxRecDepth 50000 in
set_option maxHeartbeats 4000000 in
lemma fastSolve_checked : fastSolve 11 0 0 [] = false := by decide +kernel

theorem no_cover_build (tail blocks : List M)
    (hrun : Builds seeds tail)
    (hbound : tail.length + blocks.length ≤ 11)
    (hattain : ∀ z ∈ blocks, key z ∈ seeds ∨ key z ∈ tail)
    (hcover : ∀ c ∈ cells, ∃ z ∈ blocks, hit c z = true) : False := by
  have h0lt : (0 : Nat) < 2 ^ 17 := by decide
  have h1 : fastSolve 11 ([] : List M).length 0 [] = true :=
    fastSolve_ok hrun hbound hattain hcover 11 [] 0 []
      List.nodup_nil (fun _ h => by cases h) h0lt
      (fun _ => by simp) List.nodup_nil (fun _ h => by cases h) (by simp; omega)
  exact Bool.false_ne_true (fastSolve_checked.symm.trans h1)

end CoverCheck

end PEqualNP.Outside.L_meta_2592_aux
